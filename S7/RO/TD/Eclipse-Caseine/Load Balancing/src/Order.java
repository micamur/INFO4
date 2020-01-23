/**
 * 
 * PLEASE DO NOT CHANGE THIS CLASS
 * 
 * @author nicolas et hadrien
 */
public class Order {

	/**
	 * Index of the order
	 */
	private int idx;

	/**
	 * Duration of the order
	 */
	private int duration;

	/**
	 * @return indice of the order
	 */
	public int getIdx() {
		return idx;
	}

	/**
	 * @return duration of the order
	 */
	public int getDuration() {
		return duration;
	}

	/**
	 * Builds an order.
	 * 
	 * @param idx
	 * @param duration
	 */
	public Order(int idx, int duration) {
		this.idx = idx;
		this.duration = duration;
	}
	
	public String toString() {
        return idx + "";
    }
	
}