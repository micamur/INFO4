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
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.control.Button;
import javafx.scene.control.ListView;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;
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
		BorderPane bp = new BorderPane();
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

		BorderPane rootList = new BorderPane(lv);
		rootList.setCenter(lv);

		// Create toolbar with + and -
		Button plus = new Button("+");
		EventHandler<ActionEvent> plusEH = new EventHandler<ActionEvent>() {
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
		};
		plus.setOnAction(plusEH);
		Button minus = new Button(" - ");
		EventHandler<ActionEvent> minusEH = new EventHandler<ActionEvent>() {
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
		};
		minus.setOnAction(minusEH);
		ToolBar toolBar = new ToolBar(plus, new Separator(), minus);
		rootList.setBottom(toolBar);

		MenuBar rootMenu = new MenuBar();
		final Menu menu1 = new Menu("Expression");
		
		MenuItem menuItemAdd = new MenuItem("Add");
		menuItemAdd.setOnAction(plusEH);
		menuItemAdd.setAccelerator(new KeyCodeCombination(KeyCode.N, KeyCombination.SHORTCUT_DOWN));
		menu1.getItems().add(menuItemAdd);
		MenuItem menuItemRemove = new MenuItem("Remove");
		menuItemRemove.setOnAction(minusEH);
		menuItemRemove.setAccelerator(new KeyCodeCombination(KeyCode.BACK_SPACE, KeyCombination.SHORTCUT_DOWN));
		menu1.getItems().add(menuItemRemove);
		
		rootMenu.getMenus().addAll(menu1);
		
		sp.getItems().add(rootList);
		sp.getItems().add(c);
		bp.setTop(rootMenu);
		bp.setCenter(sp);
		
		stage.setTitle("grapher");
		stage.setScene(new Scene(bp));
		stage.show();
	}

	public static void main(String[] args) {
		launch(args);
	}
}