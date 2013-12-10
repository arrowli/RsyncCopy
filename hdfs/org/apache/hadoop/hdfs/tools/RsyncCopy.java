/**
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.hadoop.hdfs.tools;

import java.io.BufferedOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OutputStream;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.concurrent.*;

import javax.net.SocketFactory;
import javax.security.auth.login.LoginException;

import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.conf.Configured;
import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.hdfs.DFSUtil;
import org.apache.hadoop.hdfs.LeaseRenewal;
import org.apache.hadoop.hdfs.protocol.AlreadyBeingCreatedException;
import org.apache.hadoop.hdfs.protocol.Block;
import org.apache.hadoop.hdfs.protocol.ClientProtocol;
import org.apache.hadoop.hdfs.protocol.BlockChecksumListHeader;
import org.apache.hadoop.hdfs.protocol.DataTransferProtocol;
import org.apache.hadoop.hdfs.protocol.DatanodeInfo;
import org.apache.hadoop.hdfs.protocol.FSConstants;
import org.apache.hadoop.hdfs.protocol.LocatedBlock;
import org.apache.hadoop.hdfs.protocol.LocatedBlocks;
import org.apache.hadoop.hdfs.protocol.LocatedBlocksWithMetaInfo;
import org.apache.hadoop.hdfs.protocol.ProtocolCompatible;
import org.apache.hadoop.hdfs.server.common.HdfsConstants;
import org.apache.hadoop.hdfs.server.datanode.DataNode;
import org.apache.hadoop.hdfs.server.namenode.NameNode;
import org.apache.hadoop.io.DataOutputBuffer;
import org.apache.hadoop.io.IOUtils;
import org.apache.hadoop.io.retry.RetryPolicies;
import org.apache.hadoop.io.retry.RetryPolicy;
import org.apache.hadoop.io.retry.RetryProxy;
import org.apache.hadoop.ipc.ProtocolProxy;
import org.apache.hadoop.ipc.RPC;
import org.apache.hadoop.ipc.RemoteException;
import org.apache.hadoop.net.NetUtils;
import org.apache.hadoop.security.AccessControlException;
import org.apache.hadoop.security.UserGroupInformation;
import org.apache.hadoop.util.Daemon;
import org.apache.hadoop.util.StringUtils;

/* new added */
import org.apache.hadoop.hdfs.DistributedFileSystem;

/**
 * There is a need to perform fast file copy on HDFS (primarily for the purpose
 * of HBase Snapshot). The fast copy mechanism for a file works as follows :
 * 
 * 1) Query metadata for all blocks of the source file.
 * 
 * 2) For each block 'b' of the file, find out its datanode locations.
 * 
 * 3) For each block of the file, add an empty block to the namesystem for the
 * destination file.
 * 
 * 4) For each location of the block, instruct the datanode to make a local copy
 * of that block.
 * 
 * 5) Once each datanode has copied over the its respective blocks, they report
 * to the namenode about it.
 * 
 * 6) Wait for all blocks to be copied and exit.
 * 
 * This would speed up the copying process considerably by removing top of the
 * rack data transfers.
 **/

public class RsyncCopy {

	public static final Log LOG = LogFactory.getLog(RsyncCopy.class);
	public ClientProtocol namenode;
	// Namenode proxy that supports method-based compatibility
	public ProtocolProxy<ClientProtocol> namenodeProtocolProxy = null;
	static Random r = new Random();
	final String clientName;
	final LeaseChecker leasechecker;
	Configuration conf;
	SocketFactory socketFactory;
	final FileSystem.Statistics stats;

	private long namenodeVersion = ClientProtocol.versionID;
	protected Integer dataTransferVersion = -1;
	protected volatile int namespaceId = 0;

	final InetAddress localHost;
	InetSocketAddress nameNodeAddr;

	int ipTosValue = NetUtils.NOT_SET_IP_TOS;

	volatile boolean clientRunning = true;
	private ClientProtocol rpcNamenode;
	int socketTimeout;
	int namenodeRPCSocketTimeout;

	public Object namenodeProxySyncObj = new Object();
	private final Path testPath = new Path("/test");
	private final DistributedFileSystem dfs;

	/**
	 * Create a new DFSClient connected to the given nameNodeAddr or
	 * rpcNamenode. Exactly one of nameNodeAddr or rpcNamenode must be null.
	 */
	RsyncCopy(InetSocketAddress nameNodeAddr, ClientProtocol rpcNamenode,
			Configuration conf, FileSystem.Statistics stats, long uniqueId,
			DistributedFileSystem dfs) throws IOException {
		this.conf = conf;
		this.stats = stats;
		this.socketFactory = NetUtils.getSocketFactory(conf,
				ClientProtocol.class);
		this.localHost = InetAddress.getLocalHost();
		this.dfs=DFSUtil.convertToDFS(testPath.getFileSystem(conf));
		String taskId = conf.get("mapred.task.id");
		if (taskId != null) {
			this.clientName = "RsyncCopy_" + taskId + "_" + r.nextInt() + "_"
					+ Thread.currentThread().getId();
		} else {
			this.clientName = "RsyncCopy_" + r.nextInt()
					+ ((uniqueId == 0) ? "" : "_" + uniqueId);
		}

		if (nameNodeAddr != null && rpcNamenode == null) {
			this.nameNodeAddr = nameNodeAddr;
			getNameNode();
		} else {
			throw new IllegalArgumentException(
					"Expecting exactly one of nameNodeAddr and rpcNamenode being null: "
							+ "nameNodeAddr=" + nameNodeAddr + ", rpcNamenode="
							+ rpcNamenode);
		}

		this.leasechecker = new LeaseChecker(this.clientName, this.conf);

		this.socketTimeout = conf.getInt("dfs.socket.timeout",
                HdfsConstants.READ_TIMEOUT);
		this.namenodeRPCSocketTimeout = conf.getInt(
				org.apache.hadoop.hdfs.protocol.FSConstants.DFS_CLIENT_NAMENODE_SOCKET_TIMEOUT, 0);
	}

	/**
	 * Get the checksum of a file.
	 * 
	 * @param src
	 *            The file path
	 * @return The checksum
	 * @see DistributedFileSystem#getFileChecksum(Path)
	 */
	void getFileChecksum(String src) throws IOException {
		checkOpen();
		getFileChecksum(dataTransferVersion, src, namenode,
				namenodeProtocolProxy, socketFactory, socketTimeout);
	}

	/**
	 * Get the checksum of a file.
	 * 
	 * @param src
	 *            The file path
	 * @return The checksum
	 */
	public static void getFileChecksum(int dataTransferVersion, String src,
			ClientProtocol namenode,
			ProtocolProxy<ClientProtocol> namenodeProxy,
			SocketFactory socketFactory, int socketTimeout) throws IOException {
		// get all block locations
		final LocatedBlocks locatedBlocks = callGetBlockLocations(namenode,
				src, 0, Long.MAX_VALUE, isMetaInfoSuppoted(namenodeProxy));
		if (locatedBlocks == null) {
			throw new IOException(
					"Null block locations, mostly because non-existent file "
							+ src);
		}
		int namespaceId = 0;
		if (locatedBlocks instanceof LocatedBlocksWithMetaInfo) {
			LocatedBlocksWithMetaInfo lBlocks = (LocatedBlocksWithMetaInfo) locatedBlocks;
			dataTransferVersion = lBlocks.getDataProtocolVersion();
			namespaceId = lBlocks.getNamespaceID();
		} else if (dataTransferVersion == -1) {
			dataTransferVersion = namenode.getDataTransferProtocolVersion();
		}
		final List<LocatedBlock> locatedblocks = locatedBlocks
				.getLocatedBlocks();

		// get block checksum for each block
		for (int i = 0; i < locatedblocks.size(); i++) {
			LocatedBlock lb = locatedblocks.get(i);
			final Block block = lb.getBlock();
			final DatanodeInfo[] datanodes = lb.getLocations();

			// try each datanode location of the block
			final int timeout = (socketTimeout > 0) ? (socketTimeout + HdfsConstants.READ_TIMEOUT_EXTENSION
					* datanodes.length)
					: 0;

			boolean done = false;
			for (int j = 0; !done && j < datanodes.length; j++) {
				final Socket sock = socketFactory.createSocket();
				DataOutputStream out = null;
				DataInputStream in = null;

				try {
					// connect to a datanode
					NetUtils.connect(sock,
							NetUtils.createSocketAddr(datanodes[j].getName()),
							timeout);
					sock.setSoTimeout(timeout);

					out = new DataOutputStream(new BufferedOutputStream(
							NetUtils.getOutputStream(sock),
							FSConstants.SMALL_BUFFER_SIZE));
					in = new DataInputStream(NetUtils.getInputStream(sock));

					// get block MD5
					if (LOG.isDebugEnabled()) {
						LOG.debug("write to " + datanodes[j].getName() + ": "
								+ DataTransferProtocol.OP_BLOCK_CHECKSUM
								+ ", block=" + block);
					}

					/* Write the header */
					BlockChecksumListHeader blockChecksumListHeader = new BlockChecksumListHeader(
							dataTransferVersion, namespaceId,
							block.getBlockId(), block.getGenerationStamp());
					blockChecksumListHeader.writeVersionAndOpCode(out);
					blockChecksumListHeader.write(out);
					out.flush();

					final short reply = in.readShort();
					if (reply != DataTransferProtocol.OP_STATUS_SUCCESS) {
						throw new IOException("Bad response " + reply
								+ " for block " + block + " from datanode "
								+ datanodes[j].getName());
					}

					// read data
					final long data = in.readLong();
					LOG.info("Rsynccopy received " + data);

				} catch (IOException ie) {
					LOG.warn("src=" + src + ", datanodes[" + j + "].getName()="
							+ datanodes[j].getName(), ie);
				} finally {
					IOUtils.closeStream(in);
					IOUtils.closeStream(out);
					IOUtils.closeSocket(sock);
				}
			}
		}
	}

	private static LocatedBlocks callGetBlockLocations(ClientProtocol namenode,
			String src, long start, long length, boolean supportMetaInfo)
			throws IOException {
		try {
			if (supportMetaInfo) {
				return namenode.openAndFetchMetaInfo(src, start, length);
			}
			return namenode.getBlockLocations(src, start, length);
		} catch (RemoteException re) {
			throw re.unwrapRemoteException(AccessControlException.class,
					FileNotFoundException.class);
		}
	}

	public static boolean isMetaInfoSuppoted(ProtocolProxy<ClientProtocol> proxy)
			throws IOException {
		return proxy != null
				&& proxy.isMethodSupported("openAndFetchMetaInfo",
						String.class, long.class, long.class);
	}

	private void getNameNode() throws IOException {
		if (nameNodeAddr != null) {
			// The lock is to make sure namenode, namenodeProtocolProxy
			// and rpcNamenode are consistent ultimately. There is still
			// a small window where another thread can see inconsistent
			// version of namenodeProtocolProxy and namenode. But it will
			// only happen during the transit time when name-node upgrade
			// and the exception will likely to be resolved after a retry.
			//
			synchronized (namenodeProxySyncObj) {
				this.namenode = dfs.getClient().getNameNodeRPC();
			}
		}
		if (LOG.isDebugEnabled()) {
			LOG.debug("Name node signature is refreshed. Fingerprint: "
					+ namenodeProtocolProxy.getMethodsFingerprint());
		}
	}

	/**
	 * Create a NameNode proxy for the client if the client and NameNode are
	 * compatible
	 * 
	 * @param nameNodeAddr
	 *            NameNode address
	 * @param conf
	 *            configuration
	 * @param ugi
	 *            ticket
	 * @return a NameNode proxy that's compatible with the client
	 */
	private void createRPCNamenodeIfCompatible(InetSocketAddress nameNodeAddr,
			Configuration conf, UserGroupInformation ugi) throws IOException {
		try {
			this.namenodeProtocolProxy = createRPCNamenode(nameNodeAddr, conf,
					ugi, namenodeRPCSocketTimeout);
			this.rpcNamenode = namenodeProtocolProxy.getProxy();
		} catch (RPC.VersionMismatch e) {
			long clientVersion = e.getClientVersion();
			namenodeVersion = e.getServerVersion();
			if (clientVersion > namenodeVersion
					&& !ProtocolCompatible.isCompatibleClientProtocol(
							clientVersion, namenodeVersion)) {
				throw new RPC.VersionIncompatible(
						ClientProtocol.class.getName(), clientVersion,
						namenodeVersion);
			}
			this.rpcNamenode = (ClientProtocol) e.getProxy();
		}
	}

	public static ProtocolProxy<ClientProtocol> createRPCNamenode(
			InetSocketAddress nameNodeAddr, Configuration conf,
			UserGroupInformation ugi, int rpcTimeout) throws IOException {
		return RPC.getProtocolProxy(ClientProtocol.class,
				ClientProtocol.versionID, nameNodeAddr, ugi, conf,
				NetUtils.getSocketFactory(conf, ClientProtocol.class),
				rpcTimeout);
	}

	static ClientProtocol createNamenode(ClientProtocol rpcNamenode,
			Configuration conf) throws IOException {
		long sleepTime = conf.getLong("dfs.client.rpc.retry.sleep",
				org.apache.hadoop.hdfs.protocol.FSConstants.LEASE_SOFTLIMIT_PERIOD);
		RetryPolicy createPolicy = RetryPolicies
				.retryUpToMaximumCountWithFixedSleep(5, sleepTime,
						TimeUnit.MILLISECONDS);

		Map<Class<? extends Exception>, RetryPolicy> remoteExceptionToPolicyMap = new HashMap<Class<? extends Exception>, RetryPolicy>();
		remoteExceptionToPolicyMap.put(AlreadyBeingCreatedException.class,
				createPolicy);

		Map<Class<? extends Exception>, RetryPolicy> exceptionToPolicyMap = new HashMap<Class<? extends Exception>, RetryPolicy>();
		exceptionToPolicyMap.put(RemoteException.class, RetryPolicies
				.retryByRemoteException(RetryPolicies.TRY_ONCE_THEN_FAIL,
						remoteExceptionToPolicyMap));
		RetryPolicy methodPolicy = RetryPolicies.retryByException(
				RetryPolicies.TRY_ONCE_THEN_FAIL, exceptionToPolicyMap);
		Map<String, RetryPolicy> methodNameToPolicyMap = new HashMap<String, RetryPolicy>();

		methodNameToPolicyMap.put("create", methodPolicy);

		return (ClientProtocol) RetryProxy.create(ClientProtocol.class,
				rpcNamenode, methodNameToPolicyMap);
	}

	private static void printUsage() {
		HelpFormatter formatter = new HelpFormatter();
		formatter.printHelp("Usage : FastCopy [options] <srcs....> <dst>", null);
	}

	/** Lease management */
	class LeaseChecker extends LeaseRenewal {
		/**
		 * A map from src -> DFSOutputStream of files that are currently being
		 * written by this client.
		 */
		private final SortedMap<String, OutputStream> pendingCreates = new TreeMap<String, OutputStream>();

		private Daemon daemon = null;

		public LeaseChecker(String clientName, Configuration conf) {
			super(clientName, conf);
		}

		synchronized void put(String src, OutputStream out) {
			if (clientRunning) {
				if (daemon == null) {
					daemon = new Daemon(this);
					daemon.start();
				}
				pendingCreates.put(src, out);
			}
		}

		synchronized void remove(String src) {
			pendingCreates.remove(src);
		}

		void interruptAndJoin() throws InterruptedException {
			Daemon daemonCopy = null;
			synchronized (this) {
				if (daemon != null) {
					daemon.interrupt();
					daemonCopy = daemon;
				}
			}

			if (daemonCopy != null) {
				LOG.debug("Wait for lease checker to terminate");
				daemonCopy.join();
			}
		}

		synchronized void close() {
			while (!pendingCreates.isEmpty()) {
				String src = pendingCreates.firstKey();
				OutputStream out = pendingCreates.remove(src);
				if (out != null) {
					try {
						out.close();
					} catch (IOException ie) {
						LOG.error("Exception closing file " + src + " : " + ie,
								ie);
					}
				}
			}
		}

		/**
		 * Abort all open files. Release resources held. Ignore all errors.
		 */
		@Override
		protected synchronized void abort() {
			super.closeRenewal();
			clientRunning = false;
			while (!pendingCreates.isEmpty()) {
				String src = pendingCreates.firstKey();
			}
			RPC.stopProxy(rpcNamenode); // close connections to the namenode
		}

		@Override
		protected void renew() throws IOException {
			synchronized (this) {
				if (pendingCreates.isEmpty()) {
					return;
				}
			}
			namenode.renewLease(clientName);
		}

		/** {@inheritDoc} */
		@Override
		public String toString() {
			String s = getClass().getSimpleName();
			if (LOG.isTraceEnabled()) {
				return s
						+ "@"
						+ RsyncCopy.this
						+ ": "
						+ StringUtils.stringifyException(new Throwable(
								"for testing"));
			}
			return s;
		}
	}

	protected void checkOpen() throws IOException {
		if (!clientRunning) {
			IOException result = new IOException("Filesystem closed");
			throw result;
		}
	}
	
	public static void main(String args[]) throws Exception {
		if(args.length < 2){
			printUsage();
		}
		Configuration conf = new Configuration();
		InetSocketAddress nameNodeAddr = NameNode
				.getClientProtocolAddress(conf);
		ClientProtocol rpcNamenode = null;
		FileSystem.Statistics stats = null;
		long uniqueId = 0;
		DistributedFileSystem dfs = null;
		RsyncCopy rc = new RsyncCopy(nameNodeAddr, rpcNamenode, conf, stats,
				uniqueId, dfs);
		String src = "/test";
		rc.getFileChecksum(src);
		System.exit(0);
	}
}
