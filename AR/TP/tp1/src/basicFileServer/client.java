package basicFileServer;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.net.UnknownHostException;

public class client {
	
	String fileName;
	String serverHost;
	int serverPort;
	
	public client(String serverHost, int serverPort, String fileName) {
		this.fileName = fileName;
		this.serverHost = serverHost;
		this.serverPort = serverPort;
	}
	
	public void run() throws UnknownHostException, IOException {
		// Client connects to server
		Socket server = new Socket(serverHost, serverPort);
		
		// Client connected
		System.out.println("Connected to " + server.getInetAddress());
		
		// Get the server's output stream
		OutputStream os = server.getOutputStream();
		
		// Client sends bytes to the server 
		DataOutputStream dos = new DataOutputStream(os);
		dos.writeUTF(fileName);
		dos.flush();
		
		// Get the server's input stream
		InputStream is = server.getInputStream();
		
		// Client reads bytes from the server
		DataInputStream dis = new DataInputStream(is);
		int req = dis.readInt();
		System.out.println("File size: " + req);
		
		if (req > -1) {			
			// Loop to read file content
			byte[] fContent = new byte[req];
			int i = 0;
			while (i < req) {	
				byte[] tmp = new byte[req - i];
				int res = dis.read(tmp);
				System.arraycopy(tmp, 0, fContent, i, tmp.length);
				i += res;
				System.out.println(i*100.0/req + "%");
			}
			
			// Write to file
			FileOutputStream fos = new FileOutputStream(fileName);
			fos.write(fContent);
			fos.close();
		} else {
			System.out.println("File not found");
		}
		
		// Close
		os.close();
		is.close();
		server.close();
	}
	
	public static void main(String[] args) throws IOException {
		client c = new client("localhost", 10000, "img.xcf");
		c.run();
	}
	
}
