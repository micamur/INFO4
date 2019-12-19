import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Scanner;

/**
 * Class representing a data set
 * 
 * PLEASE DO NOT CHANGE THIS CLASS
 * 
 * @author nicolas et hadrien
 */
public class BalancingData {

	/**
	 * Number of orders
	 */
	private int N;

	/**
	 * List of orders
	 */
	private Order[] orders;

	/**
	 * Load capacity
	 */
	private int C;

	/**
	 * Build a data set directly from a table of integers
	 *
	 * @param file
	 */
	public BalancingData(int[] duration, int Capacity) {
		this.C = Capacity;
		this.N = duration.length;
		this.orders = new Order[this.N];
		for (int i = 0; i < orders.length; i++) {
			orders[i] = new Order(i + 1, duration[i]);
		}
	}

	/**
	 * Build a data set directly from a table of integers (durations)
	 * 
	 * @param duration: the durations of the orders
	 */
	public BalancingData(int[] duration) {
		this(duration, halfSum(duration));
	}

	// to help chaining constructors
	private static int halfSum(int[] duration) {
		int s = 0;
		for (int i = 0; i < duration.length; i++) {
			s += duration[i];
		}
		return s / 2;
	}

	/**
	 * Build a data set from a file
	 *
	 * @param file
	 */
	public BalancingData(String file) {
		try {
			BufferedReader br = new BufferedReader(new FileReader(new File(file)));
			C = Integer.parseInt(br.readLine());
			N = Integer.parseInt(br.readLine());
			orders = new Order[N];
			Scanner scan = new Scanner(br.readLine());
			for (int i = 0; i < orders.length; i++) {
				int duration = scan.nextInt();
				orders[i] = new Order(i + 1, duration);
			}
			scan.close();
			br.close();
		} catch (IOException e) {
			e.printStackTrace();
		}

	}

	// ***********************************************//
	// ************* Accessors ***********************//
	// ***********************************************//

	/**
	 * @return the number of orders
	 **/
	public int getN() {
		return N;
	}

	/**
	 * @return the capacity of the line
	 **/
	public int getC() {
		return C;
	}

	/**
	 * @param i: index of the order starting from 1 (like in the subject)
	 * @return the i-th order WARNING: i is not the JAVA index that would start from
	 *         0 but the index of the order as defined in the subject So the i-th
	 *         order is stored at index i-1 in the array of BalancingData
	 **/
	public Order getOrder(int i) {
		return orders[i - 1];
	}

}
