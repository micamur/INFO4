package grapher.ui;

import java.util.Optional;

import grapher.fc.Function;
import grapher.fc.FunctionFactory;
import javafx.application.Application;
import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.Button;
import javafx.scene.control.ListView;
import javafx.scene.control.SelectionMode;
import javafx.scene.control.Separator;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextInputDialog;
import javafx.scene.control.ToolBar;
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

		// Create toolbar with + and -
		Button plus = new Button("+");
		plus.setOnAction(new EventHandler<ActionEvent>() {
			@Override
			public void handle(ActionEvent e) {
				System.out.println("+ selected");

				// Create dialog to enter new expression
				TextInputDialog dialog = new TextInputDialog();
				dialog.setTitle("Expression");
				dialog.setHeaderText("Expression");
				dialog.setContentText("Nouvelle expression : ");

				// Add new expression in lists
				Optional<String> result = dialog.showAndWait();
				if (result.isPresent()) {
					try {
						Function f = FunctionFactory.createFunction(result.get());
						// TODO Warning : "Cette fonction existe déjà, êtes-vous sûr de vouloir l'ajouter ?"
						c.functions.add(f);
						fobservable.add(f);
						c.redraw();
					} catch (Exception exception) {
						System.out.println(result.get() + " n'est pas une fonction.");

						Alert alert = new Alert(AlertType.ERROR);
						alert.setTitle("Erreur");
						alert.setHeaderText("Erreur");
						alert.setContentText("Ooops, " + result.get() + " n'est pas une fonction !");
						alert.showAndWait();

					}
				}
			}
		});
		Button minus = new Button(" - ");
		minus.setOnAction(new EventHandler<ActionEvent>() {
			@Override
			public void handle(ActionEvent e) {
				System.out.println("- selected");

				// Delete selected functions
				c.functions.removeAll(selection);
				fobservable.removeAll(selection);
				c.redraw();
				
				// TODO Warning : "Êtes-vous sûr de vouloir supprimer toutes les fonctions ?"
				// TODO Warning : "Aucune fonction n'est sélectionnée"
			}
		});
		ToolBar toolBar = new ToolBar(plus, new Separator(), minus);
		root.setBottom(toolBar);

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