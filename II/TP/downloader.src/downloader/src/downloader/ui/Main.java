package downloader.ui;

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
import javafx.scene.layout.VBox;
import javafx.stage.Stage;
import javafx.stage.WindowEvent;

public class Main extends Application {
	protected ObservableList<Downloader> downloaders;

	public void start(Stage stage) {
		// BorderPane qui contient tout
		BorderPane bpMain = new BorderPane();
		// VBox la liste qui contient la liste des différents téléchargements
		VBox vbList = new VBox();
		// ScrollPane qui permet d'avoir une barre de scroll pour la liste
		ScrollPane spList;
		// BorderPane qui contient la partie du bas (champ texte et bouton Add)
		BorderPane bpBottom = new BorderPane();
		Button bAdd = new Button("Add");
		TextArea taInput = new TextArea();

		int bottomHeight = 32;
		int buttonWidth = 64;

		// On lit les URLs en paramètre
		for (String url : getParameters().getRaw()) {
			new DownloaderView(url, vbList);
		}

		// On définit l'action du bouton Add
		bAdd.setOnAction(new EventHandler<ActionEvent>() {
			@Override
			public void handle(ActionEvent e) {
				new DownloaderView(taInput.getText(), vbList);
			}
		});

		// Configuration de la zone du bas
		taInput.setMaxHeight(bottomHeight);
		taInput.setMinHeight(bottomHeight);
		bAdd.setMaxHeight(bottomHeight);
		bAdd.setMinHeight(bottomHeight);
		bAdd.setMinWidth(buttonWidth);
		bAdd.setMaxWidth(buttonWidth);
		bpBottom.setCenter(taInput);
		bpBottom.setRight(bAdd);

		// Configuration de la liste et du scrollPane
		vbList.setPadding(new Insets(5));
		spList = new ScrollPane(vbList);
		spList.setFitToWidth(true);
		spList.setContent(vbList);
		spList.setHbarPolicy(null);

		// Configuration du BorderPane principal
		bpMain.setCenter(spList);
		bpMain.setBottom(bpBottom);

		// Configuration de la fenêtre
		stage.setOnCloseRequest(new EventHandler<WindowEvent>() {
			// Lorsqu'on la ferme, on annule tous les téléchargements en cours
			@Override
			public void handle(WindowEvent event) {
				for (Node node : vbList.getChildren()) {
					if (node instanceof DownloaderView) {
						DownloaderView dvChild = (DownloaderView) node;
						dvChild.downloader.cancel();
						System.out.println("Cancelling download of " + dvChild.downloader.toString());
					}
				}
			}
		});
		stage.setHeight(300);
		stage.setWidth(500);
		stage.setTitle("downloader");
		stage.setScene(new Scene(bpMain));
		stage.show();
	}

	public static void main(String[] args) {
		launch(args);
	}

}