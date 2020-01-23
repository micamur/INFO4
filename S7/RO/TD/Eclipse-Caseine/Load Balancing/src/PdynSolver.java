/**
 * A class to implement the DP solver
 * 
 * @author nicolas et hadrien
 */
public class PdynSolver {

	/**
	 * Reference to the data
	 */
	private BalancingData data;

	/**
	 * Value of an optimal solution
	 */
	private int optVal;

	/**
	 * f[w][i]: the value of maximum load with orders 1..i and a capacity of w
	 * f[w][i]: la valeur de la charge maximum possible avec les commandes 1..i et
	 * une capacité de w
	 */
	private int[][] f;

	/**
	 * p[w][i] = w' gives the value w' which led to f[w][i] using f[w'][i-1].
	 * p[w][i] = w' donne la valeur w' qui a permis de calculer f[w][i] (à partir de
	 * f[w'][i-1])
	 */
	private int[][] p;

	/**
	 * Build a Pdyn solver
	 * 
	 * @param data
	 */
	public PdynSolver(BalancingData data) {
		this.data = data;
	}

	/**
	 * @return the optimal value
	 */
	public int getOptVal() {
		return optVal;
	}

	/**
	 * Initialize the data structures needed for the maximum load computation
	 */
	private void init() {
		int n = data.getN();
		int C = data.getC();
		this.f = new int[C + 1][n + 1];
		this.p = new int[C + 1][n + 1];
	}

	/**
	 * Solve the maximum load problem:
	 */
	public void solve() {
		int n = data.getN();
		int C = data.getC();
		this.init();

		// Première ligne à 0
		for (int i = 0; i < n + 1; i++) {
			f[0][i] = 0;
		}

		// Première colonne à 0
		for (int i = 0; i < C + 1; i++) {
			f[i][0] = 0;
		}

		// Remplissage du tableau
		for (int i = 1; i <= n; i++) {
			int ti = data.getOrder(i).getDuration();
			for (int w = 1; w <= C; w++) {
				f[w][i] = Math.max(f[w][i - 1], (w >= ti) ? f[w - ti][i - 1] + ti : 0);
			}
		}

		// Valeur optimale
		this.optVal = f[C][n];
	}

	/**
	 * Print one optimal solution as a String by giving the indexes of the orders on
	 * the machine. So for orders of sizes {4,10,7,5,3} and capa 14, an optimal
	 * solution is made of the first two orders and given as a String: "[ 1 2 ]"
	 * Another optimal solution could be orders number one, three and five: "[ 1 3
	 * 5]"
	 **/
	public String solutionToString() {
		String solution = "Solution: {";
		int currentw = data.getC();
		for (int j = data.getN(); j > 0; j--) {
			int prevw = p[currentw][j];
			if (prevw != currentw) {
				solution += " " + data.getOrder(j - 1).toString() + " ";
			}
			currentw = prevw;
		}
		solution += "}";
		System.out.println(solution);
		return solution;
	}

}
