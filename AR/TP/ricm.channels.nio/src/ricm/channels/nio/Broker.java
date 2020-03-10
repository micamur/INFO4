package ricm.channels.nio;

import java.io.IOException;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.nio.channels.SelectionKey;
import java.nio.channels.Selector;
import java.nio.channels.ServerSocketChannel;
import java.nio.channels.SocketChannel;
import java.nio.channels.spi.SelectorProvider;
import java.util.Iterator;

import ricm.channels.IBroker;
import ricm.channels.IBrokerListener;

public class Broker implements IBroker {

	// The channel used to communicate with the server
	private SocketChannel sc; // client
	private SelectionKey scKey; // client
	private ServerSocketChannel ssc; // serveur
	private SelectionKey sscKey; // serveur

	// Java NIO selector
	private Selector selector;

	private IBrokerListener brokerListener;

	public Broker() throws IOException {
		// create a new selector
		selector = SelectorProvider.provider().openSelector();
	}

	@Override
	public void setListener(IBrokerListener l) {
		brokerListener = l;
	}

	@Override
	public boolean connect(String host, int port) {
		// PARTIE CLIENT

		try {
			// create a new non-blocking socket channel
			sc = SocketChannel.open();
			sc.configureBlocking(false);

			// register an connect interested in order to get a
			// connect event, when the connection will be established
			scKey = sc.register(selector, SelectionKey.OP_CONNECT);

			// request a connection to the given server and port
			InetAddress addr;
			addr = InetAddress.getByName(host);
			sc.connect(new InetSocketAddress(addr, port));
			return true;
		} catch (IOException e) {
			e.printStackTrace();
			brokerListener.refused(host, port);
			return false;
		}
	}

	@Override
	public boolean accept(int port) {
		// PARTIE SERVEUR

		try {
			// create a new non-blocking server socket channel
			ssc = ServerSocketChannel.open();
			ssc.configureBlocking(false);

			// bind the server socket to the given address and port
			InetSocketAddress isa = new InetSocketAddress(port);
			ssc.socket().bind(isa);

			// be notified when connection requests arrive
			sscKey = ssc.register(selector, SelectionKey.OP_ACCEPT);

			return true;
		} catch (Exception e) {
			e.printStackTrace();
			return false;
		}
	}

	/**
	 * Accept a connection and make it non-blocking
	 * 
	 * @param the key of the channel on which a connection is requested
	 */
	private void handleAccept(SelectionKey key) throws IOException {
		// SERVEUR

		assert (this.sscKey == key);
		assert (ssc == key.channel());

		// get the socket channel for the client who sent something
		SocketChannel sc;

		// do the actual accept on the server-socket channel
		sc = ssc.accept();
		sc.configureBlocking(false);

		// register the read interest for the new socket channel
		// in order to know when there are bytes to read
		SelectionKey keyAccept = sc.register(this.selector, SelectionKey.OP_READ);

		// attach channel to the key
		Channel channelAccept = new Channel(keyAccept);
		keyAccept.attach(channelAccept);

		// send to the listener end of accept
		brokerListener.accepted(channelAccept);
	}

	/**
	 * Finish to establish a connection
	 * 
	 * @param the key of the channel on which a connection is requested
	 */
	private void handleConnect(SelectionKey key) throws IOException {
		// CLIENT

		assert (this.scKey == key);
		assert (sc == key.channel());
		sc.finishConnect();
		key.interestOps(SelectionKey.OP_READ);

		// attach channel to the key
		Channel channelConnect = new Channel(scKey);
		scKey.attach(channelConnect);

		// send to the listener end of connect
		brokerListener.connected(channelConnect);
	}

	/**
	 * Handle outgoing data event
	 * 
	 * @param the key of the channel on which data can be sent
	 */
	private void handleWrite(SelectionKey key) throws IOException {
		// write the output buffer to the socket channel
		((Channel) key.attachment()).handleWrite();
	}

	/**
	 * Handle incoming data event
	 * 
	 * @param the key of the channel on which the incoming data waits to be received
	 */
	private void handleRead(SelectionKey key) throws IOException {
		// Read the message
		byte[] data = ((Channel) key.attachment()).handleRead();

		// Print the message
		if (data != null) {
//			System.out.println("Server Broker received: " + data.length);
		}
	}

	public void run() throws IOException {
		System.out.println("Broker running");
		try {
			while (true) {
				selector.select();
				Iterator<?> selectedKeys = this.selector.selectedKeys().iterator();

				// Goes through all I/O ready clients
				while (selectedKeys.hasNext()) {
					SelectionKey key = (SelectionKey) selectedKeys.next();
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
		} catch (Exception e) {
			e.printStackTrace();
		}

	}

}
