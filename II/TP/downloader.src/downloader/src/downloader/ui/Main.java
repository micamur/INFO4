package downloader.ui;

import downloader.fc.Downloader;
import javafx.application.Application;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.ScrollPane;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;

public class Main extends Application {
	protected ObservableList<Downloader> downloaders;

	public void start(Stage stage) {
//		downloaders = FXCollections.observableArrayList();
//		for (String uri : getParameters().getRaw()) {
//			Downloader d = new Downloader(uri);
//			downloaders.add(d);
//			new Thread(d).start();
//		}

		BorderPane bp = new BorderPane();
		VBox vb = new VBox();
		ScrollPane sp = new ScrollPane();

		for (String url : getParameters().getRaw()) {
			new DownloaderView(url, vb);
		}

		vb.setPadding(new Insets(5));
		sp.setFitToWidth(true);
		sp.setContent(vb);
		bp.setCenter(sp);
		stage.setHeight(500);
		stage.setWidth(500);
		stage.setTitle("downloader");
		stage.setScene(new Scene(bp));
		stage.show();
	}

	public static void main(String[] args) {
		launch(args);
	}
}