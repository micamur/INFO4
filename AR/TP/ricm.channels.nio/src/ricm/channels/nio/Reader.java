package ricm.channels.nio;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.SelectionKey;
import java.nio.channels.SocketChannel;

public class Reader {
	private enum State {
		IDLE, WAIT_LEN, WAIT_MSG
	};

	private State current;
	private ByteBuffer msgBuffer;
	private ByteBuffer msgLenBuffer;
	private SocketChannel sc;
	private int msgLen;
	private SelectionKey key;

	public Reader(SelectionKey key) {
		this.key = key;
		this.current = State.IDLE;
		this.sc = (SocketChannel) key.channel();
		this.msgLenBuffer = ByteBuffer.allocate(4);
	}

	public byte[] nextState() throws IOException {
		switch (current) {
		case IDLE:
			current = State.WAIT_LEN;
		case WAIT_LEN:
			msgLenBuffer.rewind();
			if (sc.read(msgLenBuffer) == -1) {
				// Can't read so finish
				key.cancel();
				sc.close();
				return null;
			}
			if (!msgLenBuffer.hasRemaining()) {
				current = State.WAIT_MSG;

				msgLenBuffer.rewind();
				msgLen = msgLenBuffer.getInt();
				msgLenBuffer.rewind();

				msgBuffer = ByteBuffer.allocate(msgLen);
			}
		case WAIT_MSG:
			if (sc.read(msgBuffer) == -1) {
				// Can't read so finish
				key.cancel();
				sc.close();
				return null;
			}
			if (!msgBuffer.hasRemaining()) {
				current = State.IDLE;

				msgBuffer.rewind();
				byte[] msgByte = new byte[msgBuffer.remaining()];
				msgBuffer.get(msgByte);

				return msgByte;
			}
			return null;
		default:
			return null;
		}
	}
}
