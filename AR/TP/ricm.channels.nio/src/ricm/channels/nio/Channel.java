package ricm.channels.nio;

import java.io.IOException;
import java.nio.channels.SelectionKey;
import java.util.Arrays;

import ricm.channels.IChannel;
import ricm.channels.IChannelListener;

public class Channel implements IChannel {

	// Automata
	public Writer writer;
	public Reader reader;

	// Listener
	private IChannelListener channelListener;

	// Closed state
	private boolean isClosed;

	// Key of the channel
	private SelectionKey key;

	public Channel(SelectionKey key) {
		// create new automata
		writer = new Writer(key);
		reader = new Reader(key);
		// set the channel to open
		isClosed = false;
		// set key
		this.key = key;
	}

	@Override
	public void setListener(IChannelListener l) {
		channelListener = l;
	}

	@Override
	public void send(byte[] bytes, int offset, int count) {
		writer.send(Arrays.copyOfRange(bytes, offset, offset + count));
	}

	@Override
	public void send(byte[] bytes) {
		send(bytes, 0, bytes.length);
	}

	@Override
	public void close() {
		key.cancel();
		isClosed = true;
	}

	@Override
	public boolean closed() {
		return isClosed;
	}

	public void handleWrite() {
		try {
			writer.nextState();
		} catch (IOException e) {
			e.printStackTrace();
			close();
			channelListener.closed(this, e);
		}
	}

	public byte[] handleRead() {
		try {
			byte[] data = reader.nextState();
			if (data != null) {
				channelListener.received(this, data);
			}
			return data;
		} catch (IOException e) {
			e.printStackTrace();
			close();
			channelListener.closed(this, e);
			return null;
		}
	}

}
