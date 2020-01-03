/**
 * A class providing static methods for frequent algorithmic problems.
 */
public class Tools {

	/**
	 * Given a set of integers X and an integer E, is there a non-empty subset that
	 * sums to E ? With E = 20 et X = {8,12,5,3,6,9}, the sets : {12,8}, {12,5,3},
	 * {8, 3, 9} are examples of solutions.
	 * 
	 * @param X: a set of integer values (coins)
	 * @param E: a value
	 * @return true if there exists a subset of X that sums to E, false otherwise
	 */
	public static boolean subsetSum(int[] X, int E) {
		if (E == 0) {
			return true;
		}

		boolean[][] objetsPris = new boolean[X.length][E + 1];

		// Initialisation de la première colonne à true
		for (int nbObj = 0; nbObj < X.length; nbObj++) {
			objetsPris[nbObj][0] = true;
		}

		// Initialisation de la première ligne
		for (int value = 0; value <= E; value++) {
			objetsPris[0][value] = (value == X[0]);
		}

		// Remplissage du tableau
		for (int nbObj = 1; nbObj < X.length; nbObj++) {
			for (int value = 1; value <= E; value++) {
				int y = value - X[nbObj] >= 0 ? value - X[nbObj] : 0;
				objetsPris[nbObj][value] = objetsPris[nbObj - 1][value] || objetsPris[nbObj - 1][y];
				if (value == E && objetsPris[nbObj][value] == true) {
					return true;
				}
			}
		}

		return false;
	}

}
