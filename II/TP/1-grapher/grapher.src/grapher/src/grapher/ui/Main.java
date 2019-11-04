package grapher.ui;

import grapher.fc.Function;
import javafx.application.Application;
import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.Scene;
import javafx.scene.control.ListView;
import javafx.scene.control.SelectionMode;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

public class Main extends Application {
	public void start(Stage stage) {
		GrapherCanvas c = new GrapherCanvas(getParameters());
		SplitPane sp = new SplitPane();

		ObservableList<Function> fobservable = FXCollections.observableArrayList();
		fobservable.addAll(c.functions);

		ListView<Function> lv = new ListView<Function>(fobservable);
		lv.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);

		ObservableList<Function> selection = lv.getSelectionModel().getSelectedItems();
		selection.addListener(new InvalidationListener() {
			@Override
			public void invalidated(Observable f) {
				System.out.println("Invalidated");
				c.selection = selection;
				c.redraw();
			}
		});
		c.selection = selection;		
		
		BorderPane root = new BorderPane(lv);
		root.setCenter(lv);

		sp.getItems().add(root);
		sp.getItems().add(c);

		stage.setTitle("grapher");
		stage.setScene(new Scene(sp));
		stage.show();
	}

	public static void main(String[] args) {
		launch(args);
	}
}