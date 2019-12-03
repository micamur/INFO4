package downloader.ui;

import downloader.fc.Downloader;
import javafx.application.Platform;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;

public class DownloaderView {
	ProgressBar pb;
	Downloader downloader;

	public DownloaderView(String url, VBox vb) {
		try {
			HBox hb = new HBox();
			
			Button playPause = new Button(">");
			Button delete = new Button("X");
			playPause.setPrefWidth(50);
			delete.setPrefWidth(50);
			
			downloader = new Downloader(url);

			// TODO : la barre de progression n'apparaît pas
			
			pb = new ProgressBar(0);
			pb.setMinWidth(vb.getWidth() - 100);
			pb.setMaxWidth(vb.getWidth() - 100);
			pb.setPrefWidth(Double.MAX_VALUE);
			
			downloader.progressProperty().addListener((obs, o, n) -> {
				System.out.print(".");
				System.out.flush();
				Platform.runLater(() -> pb.setProgress(downloader.progressProperty().get()));
			});
			
			vb.getChildren().add(new Label(downloader.toString()));
			
			hb.getChildren().add(pb);
			hb.getChildren().add(playPause);
			hb.getChildren().add(delete);
			
			vb.getChildren().add(hb);

			new Thread(downloader).start();
		} catch (RuntimeException e) {
			System.err.format("skipping %s %s\n", url, e);
		}
		System.out.format("Downloading %s:", downloader);

	}
}
