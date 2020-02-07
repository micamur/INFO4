package basicMultiThread_;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

public class server {

	int port;
	String dir;
	ServerSocket server;

	public server(int port, String dir) throws IOException {
		this.port = port;
		this.dir = dir;
		this.server = new ServerSocket(port);
	}

	public void run() throws IOException {
		// End-less loop
		while (true) {
			// Server waits for a connection
			Socket client = server.accept();
			// A client connected
			System.out.println("Client " + client.getInetAddress() + "connected.");
			workerThread thread = new workerThread(client, dir);
			thread.start();
		}
	}

	public static void main(String[] args) throws IOException {
		server s = new server(1234, "tmp");
		s.run();
	}

}