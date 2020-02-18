package ricm.distsys.nio.babystep3;

import java.io.IOException;
import java.io.PrintStream;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.nio.ByteBuffer;
import java.nio.channels.SelectionKey;
import java.nio.channels.Selector;
import java.nio.channels.SocketChannel;
import java.nio.channels.spi.SelectorProvider;
import java.nio.charset.Charset;
import java.security.MessageDigest;
import java.util.Iterator;
import java.util.Random;

/**
 * NIO elementary client RICM4 TP F. Boyer
 */

public class NioClient {

	// The channel used to communicate with the server
	private SocketChannel sc;
	private SelectionKey scKey;

	// Java NIO selector
	private Selector selector;

	// ByteBuffer for outgoing messages
	ByteBuffer outBuffer = ByteBuffer.allocate(128);
	// ByteBuffer for ingoing messages
	ByteBuffer inBuffer = ByteBuffer.allocate(128);

	// The message to send to the server
	byte[] first;
	byte[] digest;
	int nloops;

	// Automata
	private Writer writer;
	private Reader reader;
	
	/**
	 * NIO client initialization
	 * 
	 * @param serverName: the server name
	 * @param port: the server port
	 * @param msg: the message to send to the server
	 * @throws IOException
	 */
	public NioClient(String serverName, int port, byte[] payload) throws IOException {
		this.first = payload;

		// create a new selector
		selector = SelectorProvider.provider().openSelector();

		// create a new non-blocking server socket channel
		sc = SocketChannel.open();
		sc.configureBlocking(false);

		// register an connect interested in order to get a
		// connect event, when the connection will be established
		scKey = sc.register(selector, SelectionKey.OP_CONNECT);

		// request a connection to the given server and port
		InetAddress addr;
		addr = InetAddress.getByName(serverName);
		sc.connect(new InetSocketAddress(addr, port));
	}

	/**
	 * The client forever-loop on the NIO selector - wait for events on registered
	 * channels - possible events are ACCEPT, CONNECT, READ, WRITE
	 */
	public void loop() throws IOException {
		System.out.println("NioClient running");
		while (true) {
			selector.select();

			// get the keys for which an event occurred
			Iterator<?> selectedKeys = this.selector.selectedKeys().iterator();
			while (selectedKeys.hasNext()) {
				SelectionKey key = (SelectionKey) selectedKeys.next();
				// process key's events
				if (key.isValid() && key.isAcceptable())
					handleAccept(key);
				if (key.isValid() && key.isReadable())
					handleRead(key);
				if (key.isValid() && key.isWritable())
					handleWrite(key);
				if (key.isValid() && key.isConnectable())
					handleConnect(key);
				// remove the key from the selected-key set
				selectedKeys.remove();
			}
		}
	}

	/**
	 * Accept a connection and make it non-blocking
	 * 
	 * @param the key of the channel on which a connection is requested
	 */
	private void handleAccept(SelectionKey key) throws IOException {
		throw new Error("Unexpected accept");
	}

	/**
	 * Finish to establish a connection
	 * 
	 * @param the key of the channel on which a connection is requested
	 */
	private void handleConnect(SelectionKey key) throws IOException {
		assert (this.scKey == key);
		assert (sc == key.channel());
		sc.finishConnect();
		key.interestOps(SelectionKey.OP_READ);

		// create new automata
		writer = new Writer(key);
		reader = new Reader(key);
		
		// when connected, send a message to the server
		digest = md5(first);
		writer.send(first);
	}

	/**
	 * Handle incoming data event
	 * 
	 * @param the key of the channel on which the incoming data waits to be received
	 */
	private void handleRead(SelectionKey key) throws IOException {
		assert (this.scKey == key);
		assert (sc == key.channel());

		// Let's read the message
		String data = reader.nextState();
		nloops++;

		if (data != null) {
			// Let's make sure we read the message we sent to the server
			byte[] md5 = md5(data.getBytes(Charset.forName("UTF-8")));
			if (!md5check(digest, md5))
				System.out.println("Checksum Error!");

			// prints message
			System.out.println("NioClient3 " + sc.hashCode() + " received msg["+nloops+"]: " + data);
		
			// send back the received message
			writer.send(first);
		}
	}

	/**
	 * Handle outgoing data event
	 * 
	 * @param the key of the channel on which data can be sent
	 */
	private void handleWrite(SelectionKey key) throws IOException {
		assert (this.scKey == key);
		assert (sc == key.channel());

		// write the output buffer to the socket channel
		writer.nextState();
	}

	public static void main(String args[]) throws IOException {
		int serverPort = NioServer.DEFAULT_SERVER_PORT;
		String serverAddress = "localhost";
		String[] msgs = {"Hey", "How are you?", "It's cloudy out there", "Funky duck", "This is a really long message to send..."};
		Random r = new Random();
		String msg = msgs[r.nextInt(msgs.length)];
		String arg;

		for (int i = 0; i < args.length; i++) {
			arg = args[i];

			if (arg.equals("-m")) {
				msg = args[++i];
			} else if (arg.equals("-p")) {
				serverPort = Integer.valueOf(args[++i]).intValue();
			} else if (arg.equals("-a")) {
				serverAddress = args[++i];
			}
		}
		byte[] bytes = msg.getBytes(Charset.forName("UTF-8"));
		NioClient nc;
		nc = new NioClient(serverAddress, serverPort, bytes);
		nc.loop();
	}

	/*
	 * Wikipedia: The MD5 message-digest algorithm is a widely used hash function
	 * producing a 128-bit hash value. Although MD5 was initially designed to be
	 * used as a cryptographic hash function, it has been found to suffer from
	 * extensive vulnerabilities. It can still be used as a checksum to verify data
	 * integrity, but only against unintentional corruption. It remains suitable for
	 * other non-cryptographic purposes, for example for determining the partition
	 * for a particular key in a partitioned database.
	 */
	public static byte[] md5(byte[] bytes) throws IOException {
		byte[] digest = null;
		try {
			MessageDigest md = MessageDigest.getInstance("MD5");
			md.update(bytes, 0, bytes.length);
			digest = md.digest();
		} catch (Exception ex) {
			throw new IOException(ex);
		}
		return digest;
	}

	public static boolean md5check(byte[] d1, byte[] d2) {
		if (d1.length != d2.length)
			return false;
		for (int i = 0; i < d1.length; i++)
			if (d1[i] != d2[i])
				return false;
		return true;
	}

	public static void echo(PrintStream ps, byte[] digest) {
		for (int i = 0; i < digest.length; i++)
			ps.print(digest[i] + ", ");
		ps.println();
	}

}