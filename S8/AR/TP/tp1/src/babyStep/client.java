package babyStep;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;

public class client {
	
	public static void main(String[] args) throws IOException {
		String name = "Claire";
	
		// Client connects to server
		String serverHost = "localhost";
		int serverPort = 10000;
		Socket server = new Socket(serverHost, serverPort);
		
		// Client connected
		System.out.println("Connected to " + server.getInetAddress());
		
		// Get the server's output stream
		OutputStream os = server.getOutputStream();
		DataOutputStream dos = new DataOutputStream(os);
		// Server sends bytes to the client (name) 
		dos.writeUTF(name);
		dos.flush();
		
		// Get the server's input stream
		InputStream is = server.getInputStream();
		DataInputStream dis = new DataInputStream(is);
		// Client receives bytes from server ("Hello " + name)
		String req = dis.readUTF();
		System.out.println("Recieved: " + req);
	}
	
}
