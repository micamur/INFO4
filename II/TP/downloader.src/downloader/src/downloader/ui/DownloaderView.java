package downloader.ui;

import downloader.fc.Downloader;
import javafx.application.Platform;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;

public class DownloaderView extends BorderPane {
	private ProgressBar progressBar;
	public Downloader downloader;
	private Button playPause, delete;

	public DownloaderView(String url, VBox vb) {
		try {
			// Boîte contenant les deux boutons
			HBox hb = new HBox();

			// Création des deux boutons
			playPause = new Button("||");
			delete = new Button("X");
			playPause.setPrefWidth(50);
			delete.setPrefWidth(50);

			// Création du processus de téléchargement
			downloader = new Downloader(url);

			// Configuration de la progress bar
			progressBar = new ProgressBar(0);
			progressBar.setPrefWidth(Double.MAX_VALUE);

			// Affichage des points dans la console
			downloader.progressProperty().addListener((obs, o, n) -> {
				System.out.print(".");
				System.out.flush();
				Platform.runLater(() -> progressBar.setProgress(downloader.progressProperty().get()));
			});

			// Ajout des boutons dans la HBox
			playPause.setOnAction(new EventHandler<ActionEvent>() {
				@Override
				public void handle(ActionEvent arg0) {
					downloader.playPause(playPause);
				}
			});
			delete.setOnAction(new EventHandler<ActionEvent>() {
				@Override
				public void handle(ActionEvent arg0) {
					downloader.delete();
					vb.getChildren().remove(DownloaderView.this);
				}
			});
			hb.getChildren().add(playPause);
			hb.getChildren().add(delete);

			// Ajout des éléments dans le BorderPane
			this.setCenter(progressBar);
			this.setTop(new Label(downloader.toString()));
			this.setRight(hb);

			// Ajout de la boîte du téléchargement dans la liste des téléchargements
			vb.getChildren().add(this);

			// Lancement du téléchargement
			new Thread(downloader).start();
		} catch (RuntimeException e) {
			System.err.format("skipping %s %s\n", url, e);
		}
		System.out.format("Downloading %s:", downloader);
	}

}
