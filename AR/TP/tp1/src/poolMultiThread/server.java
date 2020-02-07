package poolMultiThread_;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.concurrent.ArrayBlockingQueue;

public class server {

	int port;
	String dir;
	ServerSocket server;
	public ArrayBlockingQueue<Socket> arraySocketClient;

	public server(int port, String dir) throws IOException {
		this.port = port;
		this.dir = dir;
		this.server = new ServerSocket(port);

		arraySocketClient = new ArrayBlockingQueue<Socket>(16);

		for (int i = 0; i < 16; i++) {
			new workerThread(dir, arraySocketClient);
		}
	}

	public void run() throws IOException, InterruptedException {
		// End-less loop
		while (true) {
			// when the server receive a connection
			// he put the client socket into the buffer
			arraySocketClient.put(server.accept());
		}
	}

	public static void main(String[] args) throws IOException, InterruptedException {
		server s = new server(1234, "tmp");
		s.run();
	}

}
