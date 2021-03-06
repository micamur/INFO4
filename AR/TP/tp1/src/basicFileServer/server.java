package basicFileServer;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
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
			
			// Get the server's input stream
			InputStream is = client.getInputStream();
			DataInputStream dis = new DataInputStream(is);
			// Server receives bytes from client (file name)
			String req = dis.readUTF();
			System.out.println("Recieved: " + req);

			// Open file
			File f = null;
			int fSize = -1;
			byte[] fContent = null;
			try {
				f = new File(dir + "/" + req);
				FileInputStream fis = new FileInputStream(f);
				fContent = new byte[(int) f.length()];
				fis.read(fContent);
				fis.close();
				fSize = (fContent == null) ? -1 : fContent.length;
				System.out.println("File found");
			} catch (Exception e) {
				System.out.println("File not found: " + dir + "/" + req);
				e.printStackTrace();
			}
			
			// Get the client's output stream
			OutputStream os = client.getOutputStream();
			
			// Server sends bytes to the client (file size)
			DataOutputStream dos = new DataOutputStream(os); 
			dos.writeInt(fSize);
			dos.flush();
			
			if (fSize > -1) {
				// Server sends bytes to the client (file)				
				dos.write(fContent);
				dos.flush();
			}

			// Close
			os.close();
			is.close();
		}
	}
	
	public static void main(String[] args) throws IOException {
		server s = new server(10000, "tmp");
		s.run();
	}
	
}