package grapher.ui;

import javafx.event.EventHandler;
import javafx.geometry.Point2D;
import javafx.scene.canvas.GraphicsContext;
import javafx.scene.input.MouseButton;
import javafx.scene.input.MouseEvent;

class Interaction implements EventHandler<MouseEvent> {

	enum State {
		IDLE, L_CLIC_OR_DRAG, L_DRAG, R_CLIC_OR_DRAG, R_DRAG
	}

	private static final double D_DRAG = 5;

	State state = State.IDLE;
	Point2D p0 = new Point2D(0, 0);
	Point2D p1 = new Point2D(0, 0);
	GrapherCanvas grapher = null;

	Interaction(GrapherCanvas g) {
		this.grapher = g;
	}

	@Override
	public void handle(MouseEvent e) {
		switch (state) {
		case IDLE:
			System.out.println("IDLE");
			if (is_pressed(e)) {
				save_pos(e);
				if (is_left_button(e))
					state = State.L_CLIC_OR_DRAG;
				else if (is_right_button(e))
					state = State.R_CLIC_OR_DRAG;
			}
			break;
		case L_CLIC_OR_DRAG:
			System.out.println("L_CLIC_OR_DRAG");
			if (is_dragged(e)) {
				l_drag(e);
				state = State.L_DRAG;
			} else if (is_released(e)) {
				l_click(e);
				state = State.IDLE;
			}
			break;
		case L_DRAG:
			System.out.println("L_DRAG");
			if (is_dragged(e)) {
				l_drag(e);
			} else if (is_released(e)) {
				state = State.IDLE;
			}
			break;
		case R_CLIC_OR_DRAG:
			System.out.println("R_CLIC_OR_DRAG");
			if (is_dragged(e)) {
				r_drag(e);
				state = State.R_DRAG;
			} else if (is_released(e)) {
				r_click(e);
				state = State.IDLE;
			}
			break;
		case R_DRAG:
			System.out.println("R_DRAG");
			if (is_dragged(e)) {
				r_drag(e);
			} else if (is_released(e)) {
				state = State.IDLE;
				grapher.zoom(p0, p1);
			}
			break;
		default:
			assert (false);
		}
	}

	public void draw(GraphicsContext gc) {
		double x, y, w, h;

		if (state != State.R_DRAG)
			return;

		if (p1.getX() < p0.getX() && p1.getY() < p0.getY()) {
			System.out.println("R_DRAG upper left");
			x = p1.getX();
			y = p1.getY();
			w = p0.getX() - p1.getX();
			h = p0.getY() - p1.getY();
		} else if (p1.getX() < p0.getX() && p1.getY() > p0.getY()) {
			System.out.println("R_DRAG lower left");
			x = p1.getX();
			y = p0.getY();
			w = p0.getX() - p1.getX();
			h = p1.getY() - p0.getY();
		} else if (p1.getX() > p0.getX() && p1.getY() > p0.getY()) {
			System.out.println("R_DRAG lower right");
			x = p0.getX();
			y = p0.getY();
			w = p1.getX() - p0.getX();
			h = p1.getY() - p0.getY();
		} else {
			System.out.println("R_DRAG upper right");
			x = p0.getX();
			y = p1.getY();
			w = p1.getX() - p0.getX();
			h = p0.getY() - p1.getY();
		}

		gc.strokeRect(x, y, w, h);
	}

	private boolean is_pressed(MouseEvent e) {
//		System.out.println("MOUSE_PRESSED");
//		System.out.println(e.getEventType() == MouseEvent.MOUSE_PRESSED);
		return e.getEventType() == MouseEvent.MOUSE_PRESSED;
	}

	private boolean is_released(MouseEvent e) {
//		System.out.println("MOUSE_RELEASED");
//		System.out.println(e.getEventType() == MouseEvent.MOUSE_RELEASED);
		return e.getEventType() == MouseEvent.MOUSE_RELEASED;
	}

	private boolean is_dragged(MouseEvent e) {
		return e.getEventType() == MouseEvent.MOUSE_DRAGGED;
	}

	private boolean is_left_button(MouseEvent e) {
		return e.getButton() == MouseButton.PRIMARY;
	}

	private boolean is_right_button(MouseEvent e) {
		return e.getButton() == MouseButton.SECONDARY;
	}

	private void save_pos(MouseEvent e) {
		p0 = new Point2D(e.getX(), e.getY());
	}

	private void new_pos(MouseEvent e) {
		p1 = new Point2D(e.getX(), e.getY());
	}

	private void l_click(MouseEvent e) {
		save_pos(e);
		grapher.zoom(p0, 5);
	}

	private void r_click(MouseEvent e) {
		save_pos(e);
		grapher.zoom(p0, -5);
	}

	private void l_drag(MouseEvent e) {
		new_pos(e);
		if (p1.distance(p0) < D_DRAG)
			return;
		grapher.translate(p1.getX() - p0.getX(), p1.getY() - p0.getY());
		save_pos(e);
	}

	private void r_drag(MouseEvent e) {
		new_pos(e);
		if (p1.distance(p0) < D_DRAG)
			return;
		grapher.redraw();
	}

}
