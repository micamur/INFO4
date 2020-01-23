package babyStep;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.ServerSocket;
import java.net.Socket;

public class server {
	
	int port;
	ServerSocket server;
	
	public server(int port) throws IOException {
		this.port = port;
		this.server = new ServerSocket(port);
	}
	
	public void run() throws IOException {
		// End-less loop
		while (true) {
			// Server waits for a connection
			Socket client = server.accept();
			// A client connected
			System.out.println("Client " + client.getInetAddress() + "connected.");
			
			// Get the server's input stream
			InputStream is = client.getInputStream();
			DataInputStream dis = new DataInputStream(is);
			// Server receives bytes from client (name)
			String req = dis.readUTF();
			System.out.println("Recieved: " + req);
			
			// Get the server's output stream
			OutputStream os = client.getOutputStream();
			DataOutputStream dos = new DataOutputStream(os);
			// Server sends bytes to the client ("Hello " + name)
			String rep = "Hello " + req; 
			dos.writeUTF(rep);
			dos.flush();
		}
	}
	
	public static void main(String[] args) throws IOException {
		server s = new server(10000);
		s.run();
	}
	
}
