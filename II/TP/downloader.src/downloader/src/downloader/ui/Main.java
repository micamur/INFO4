package downloader.ui;

import downloader.fc.Downloader;
import javafx.application.Application;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
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
		HBox hb = new HBox();
		Button b = new Button("Add");
		TextArea ta = new TextArea();

		for (String url : getParameters().getRaw()) {
			new DownloaderView(url, vb);
		}

		b.setOnAction(new EventHandler<ActionEvent>() {
			@Override
			public void handle(ActionEvent e) {
				new DownloaderView(ta.getText(), vb);
			}
		});
		ta.setMaxHeight(26);
		ta.setMinHeight(26);
		b.setMinWidth(60);
		hb.getChildren().add(ta);
		hb.getChildren().add(b);
		vb.setPadding(new Insets(5));
		sp.setFitToWidth(true);
		sp.setContent(vb);
		bp.setCenter(sp);
		bp.setBottom(hb);
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