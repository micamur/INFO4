package ricm.channels.nio;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.SelectionKey;
import java.nio.channels.SocketChannel;
import java.util.LinkedList;

public class Writer {
	private enum State {IDLE, WAIT_LEN, WAIT_MSG};
	private State currentState;
	private ByteBuffer msgBuffer;
	private ByteBuffer msgLenBuffer;
	private SocketChannel sc;
	private int msgLen;
	private LinkedList<ByteBuffer> msgWaiting;
	private SelectionKey key;
	
	public Writer(SelectionKey key) {
		this.key = key;
		this.currentState = State.IDLE;
		this.sc = (SocketChannel) key.channel();
		this.msgLenBuffer = ByteBuffer.allocate(4);
		this.msgWaiting = new LinkedList<ByteBuffer>();
	}
	
	public void nextState() throws IOException {
		switch (currentState) {
		case IDLE:
			currentState = State.WAIT_LEN;
			msgBuffer = msgWaiting.removeFirst();
			msgLen = msgBuffer.remaining();
			msgLenBuffer.rewind();
			msgLenBuffer.putInt(msgLen);
			msgLenBuffer.rewind();
		case WAIT_LEN:
			sc.write(msgLenBuffer);
			if (msgLenBuffer.remaining() == 0) {
				currentState = State.WAIT_MSG;
			}
		case WAIT_MSG:
			sc.write(msgBuffer);
			if (msgBuffer.remaining() == 0) {
				currentState = State.IDLE;
				String msg = new String(msgBuffer.array(), "UTF-8");
				System.out.println("Write: " + msg.length());
				key.interestOps(SelectionKey.OP_READ);
			}
			break;
		default:
			break;
		}
	}
	
	/**
	 * Send the given data
	 * 
	 * @param data: the byte array that should be sent
	 */
	public void send(byte[] newMsg) {
		if (newMsg.length == 0)
			return;
		
		msgWaiting.add(ByteBuffer.wrap(newMsg));
		
		// register a write interests to know when there is room to write
		// in the socket channel.
		key.interestOps(SelectionKey.OP_WRITE | SelectionKey.OP_READ);
	}
}
