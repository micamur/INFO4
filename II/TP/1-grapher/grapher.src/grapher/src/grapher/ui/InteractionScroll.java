package grapher.ui;

import javafx.event.EventHandler;
import javafx.geometry.Point2D;
import javafx.scene.input.ScrollEvent;

class InteractionScroll implements EventHandler<ScrollEvent> {

	enum State {
		IDLE, W_UP, W_DOWN
	}

	State state = State.IDLE;
	Point2D p0 = new Point2D(0, 0);
	GrapherCanvas grapher = null;

	InteractionScroll(GrapherCanvas g) {
		this.grapher = g;
	}

	@Override
	public void handle(ScrollEvent e) {
		switch (state) {
		case IDLE:
			System.out.println("IDLE");
			save_pos(e);
			if (is_scrolling_up(e))
				state = State.W_UP;
			else if (is_scrolling_down(e))
				state = State.W_DOWN;
			break;
		case W_UP:
			System.out.println("W_UP");
			if (is_scrolling_up(e))
				w_up(e);
			else
				state = State.IDLE;
			break;
		case W_DOWN:
			System.out.println("W_DOWN");
			if (is_scrolling_down(e))
				w_down(e);
			else
				state = State.IDLE;
			break;
		default:
			assert (false);
		}
	}

	private boolean is_scrolling_up(ScrollEvent e) {
		return e.getDeltaY() > 0;
	}

	private boolean is_scrolling_down(ScrollEvent e) {
		return e.getDeltaY() < 0;
	}

	private void w_down(ScrollEvent e) {
		save_pos(e);
		grapher.zoom(p0, 5);
	}

	private void w_up(ScrollEvent e) {
		save_pos(e);
		grapher.zoom(p0, -5);
	}

	private void save_pos(ScrollEvent e) {
		p0 = new Point2D(e.getX(), e.getY());
	}

}
