package downloader.ui;

import downloader.fc.Downloader;
import javafx.application.Platform;
import javafx.scene.control.ProgressBar;
import javafx.scene.layout.VBox;

public class DownloaderView {
	ProgressBar pb;
	Downloader downloader;

	public DownloaderView(String url, VBox vb) {
		try {
			downloader = new Downloader(url);

			pb = new ProgressBar(0);
			pb.setPrefWidth(Double.MAX_VALUE);
			downloader.progressProperty().addListener((obs, o, n) -> {
				System.out.print(".");
				System.out.flush();
				Platform.runLater(() -> pb.setProgress(downloader.progressProperty().get()));
			});
			vb.getChildren().add(pb);

			new Thread(downloader).start();
		} catch (RuntimeException e) {
			System.err.format("skipping %s %s\n", url, e);
		}
		System.out.format("Downloading %s:", downloader);

	}
}
