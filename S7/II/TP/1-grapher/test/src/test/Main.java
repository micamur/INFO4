package test;

import javafx.application.Application;
import javafx.stage.Stage;
import javafx.scene.Scene;
import javafx.scene.layout.BorderPane;
import javafx.scene.control.Label;
import javafx.geometry.Insets;


public class Main extends Application {
	public void start(Stage stage) {
		stage.setTitle("test");
		stage.setScene(new Scene(new BorderPane() {{
			setCenter(
				new Label("Ça marche") {{
					setPadding(new Insets(10));
				}}
			);
		}}));
		stage.show();
	}
	public static void main(String[] args) {
		launch(args);
	}
}