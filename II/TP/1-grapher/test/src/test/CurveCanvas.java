package curve;

import javafx.geometry.Point2D;
import javafx.geometry.Rectangle2D;

import javafx.scene.paint.Color;
import javafx.scene.canvas.GraphicsContext;
import javafx.scene.canvas.Canvas;


public class CurveCanvas extends Canvas {
	static final double WIDTH = 400;
	static final double HEIGHT = 300;

	protected double W = WIDTH;
	protected double H = HEIGHT;
	
	public CurveCanvas() {
		super(WIDTH, HEIGHT);
	}
	
	public double minHeight(double width) { return HEIGHT;}
	public double maxHeight(double width) { return Double.MAX_VALUE; }
	public double minWidth(double height) { return WIDTH;}
	public double maxWidth(double height) { return Double.MAX_VALUE; }

	public boolean isResizable() { return true; }
	public void resize(double width, double height) {
		super.setWidth(width);
		super.setHeight(height);
		redraw();
	}	
	
	private void redraw() {
		GraphicsContext gc = getGraphicsContext2D();

		// background
		gc.clearRect(0, 0, W, H);
		
		gc.setFill(Color.BLACK);
		gc.setStroke(Color.BLACK);
	}
}
