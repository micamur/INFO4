package downloader.fc;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLConnection;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import javafx.beans.property.ReadOnlyDoubleWrapper;
import javafx.concurrent.Task;
import javafx.scene.control.Button;

public class Downloader extends Task<String> {
	public static final int CHUNK_SIZE = 1024;

	URL url;
	int content_length;
	BufferedInputStream in;

	String filename;
	File temp;
	FileOutputStream out;

	ReadOnlyDoubleWrapper progress = new ReadOnlyDoubleWrapper(this, "progress", 0);

	int size = 0;
	int count = 0;

	Lock l;
	boolean isPaused;

	public Downloader(String uri) {
		try {
			url = new URL(uri);

			URLConnection connection = url.openConnection();
			content_length = connection.getContentLength();

			in = new BufferedInputStream(connection.getInputStream());

			String[] path = url.getFile().split("/");
			filename = path[path.length - 1];
			temp = File.createTempFile(filename, ".part");
			out = new FileOutputStream(temp);

			l = new ReentrantLock();
			isPaused = false;
		} catch (MalformedURLException e) {
			throw new RuntimeException(e);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public String toString() {
		return url.toString();
	}

	protected String download() throws InterruptedException {
		byte buffer[] = new byte[CHUNK_SIZE];

		l.lock();
		while (count >= 0 && !isCancelled()) {
			try {
				out.write(buffer, 0, count);
				size += count;
				updateProgress(size, content_length);
			} catch (IOException e) {
				continue;
			}

			l.unlock();
			Thread.sleep(1000);
			l.lock();

			try {
				count = in.read(buffer, 0, CHUNK_SIZE);
			} catch (IOException e) {
				continue;
			}
		}
		l.unlock();

		if (size < content_length) {
			temp.delete();
			throw new InterruptedException();
		}

		temp.renameTo(new File(filename));
		System.out.println(url + " finished.");
		return filename;
	}

	@Override
	protected String call() throws Exception {
		return download();
	}

	public void playPause(Button b) {
		if (isPaused) {
			resume(b);
		} else {
			pause(b);
		}
	}

	public void resume(Button b) {
		if (isPaused) {
			l.unlock();
			isPaused = false;
			b.setText("||");
			System.out.println(url + " resumed.");
		}
	}

	public void pause(Button b) {
		if (!isPaused) {
			l.lock();
			isPaused = true;
			b.setText(">");
			System.out.println(url + " paused.");
		}
	}

	public void delete() {
		cancel();
		System.out.println(url + " cancelled.");
	}

}
