package basicMultiThread_;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;

public class workerThread extends Thread {

	Socket client;
	String dir;

	public workerThread(Socket client, String dir) {
		this.client = client;
		this.dir = dir;
	}

	public void run() {
		try {
			// Get the server's input stream
			InputStream is = client.getInputStream();
			DataInputStream dis = new DataInputStream(is);
			// Server receives bytes from client (file name)
			String req = dis.readUTF();
			System.out.println("Recieved: " + req + " on thread " + Thread.currentThread().getId());

			// Open file
			File f = null;
			int fSize = -1;
			byte[] fContent = null;
			try {
				// open the file to send
				f = new File(dir + "/" + req);
				// read the file
				FileInputStream fis = new FileInputStream(f);
				// creat an array of byte with the length of f
				fContent = new byte[(int) f.length()];
				// read the file and put what it read in fContent
				fis.read(fContent);
				fis.close();
				fSize = fContent.length;
				System.out.println("File found");
			} catch (Exception e) {
				System.out.println("File not found");
			}

			// Get the client's output stream
			OutputStream os = client.getOutputStream();

			// Server sends bytes to the client (file size)
			DataOutputStream dos = new DataOutputStream(os);
			dos.writeInt(fSize);
			dos.flush();

			if (fSize >= -1) {
				// Server sends bytes to the client (file)
				dos.write(fContent);
				dos.flush();
			}

			os.close();
			is.close();

		} catch (Exception e) {
			System.out.println("Error occured with the thread " + Thread.currentThread().getId());
		}
	}

}
