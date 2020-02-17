package ricm.distsys.nio.babystep2;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.SelectionKey;
import java.nio.channels.SocketChannel;

public class Reader {
	private enum State {IDLE, WAIT_LEN, WAIT_MSG};
	private State current;
	private ByteBuffer msgBuffer;
	private ByteBuffer msgLenBuffer;
	private SocketChannel sc;
	private int msgLen;
//	private SelectionKey key;
	
	public Reader(SelectionKey key) {
//		this.key = key;
		this.current = State.IDLE;
		this.sc = (SocketChannel) key.channel();
		this.msgLenBuffer = ByteBuffer.allocate(4);
	}
	
	public String nextState() throws IOException {
		switch (current) {
		case IDLE:
			current = State.WAIT_LEN;
		case WAIT_LEN:
			msgLenBuffer.rewind();
			sc.read(msgLenBuffer);
			if (msgLenBuffer.remaining() == 0) {
				current = State.WAIT_MSG;
				msgLenBuffer.rewind();
				msgLen = msgLenBuffer.getInt();
				msgBuffer = ByteBuffer.allocate(msgLen);
			}
		case WAIT_MSG:
			sc.read(msgBuffer);
			if (msgBuffer.remaining() == 0) {
				current = State.IDLE;
				msgBuffer.rewind();
				byte[] msgByte = new byte[msgBuffer.remaining()];
				msgBuffer.get(msgByte);
				String msg = new String(msgByte, "UTF-8");
				System.out.println("Read: " + msg.length());
				return msg;
			}
			return null;
		default:
			return null;
		}
	}
}
