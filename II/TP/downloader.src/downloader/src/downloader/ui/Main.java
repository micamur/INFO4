package downloader.ui;

import java.util.Iterator;

import downloader.fc.Downloader;
import javafx.application.Application;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.geometry.Insets;
import javafx.scene.Node;
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

		// BorderPane qui contient tout
		BorderPane bp = new BorderPane();
		// VBox la liste qui contient les différents téléchargements 
		VBox vb = new VBox();
		// TODO : utile ?
		ScrollPane sp;
		// HBox qui tontient la partie du bas : champ texte et bouton Add
		HBox hb = new HBox();
		Button b = new Button("Add");
		TextArea ta = new TextArea();

		// On lit les URLs en paramètre
		for (String url : getParameters().getRaw()) {
			new DownloaderView(url, vb);
		}

		// On définit l'action du bouton Add
		b.setOnAction(new EventHandler<ActionEvent>() {
			@Override
			public void handle(ActionEvent e) {
				new DownloaderView(ta.getText(), vb);
			}
		});
		
		// Configuration de la zone du bas
		ta.setMaxHeight(26);
		ta.setMinHeight(26);
//		TODO TextArea not resizable bigger
		b.setMinWidth(60);
		hb.getChildren().add(ta);
		hb.getChildren().add(b);
		
		// Configuration de la liste et du scrollPane
		vb.setPadding(new Insets(5));
		sp = new ScrollPane(vb);
		sp.setFitToWidth(true);
		sp.setContent(vb);
		sp.setHbarPolicy(null);
		
		// Configuration du BorderPane principal
		bp.setCenter(sp);
//		bp.setCenter(vb);
		bp.setBottom(hb);
		
		// Configuration de la fenêtre
		stage.setOnCloseRequest(new EventHandler<javafx.stage.WindowEvent>() {
			@Override
			public void handle(javafx.stage.WindowEvent arg0) {
				for (Iterator<Node> iter = vb.getChildren().iterator(); iter.hasNext();) {
					DownloaderView child = (DownloaderView) iter.next();
					child.deleteDownloaderView();
					iter.remove();
				}
			}
		});
		stage.setHeight(300);
		stage.setWidth(500);
		stage.setTitle("downloader");
		stage.setScene(new Scene(bp));
		stage.show();
	}

	public static void main(String[] args) {
		launch(args);
	}
}