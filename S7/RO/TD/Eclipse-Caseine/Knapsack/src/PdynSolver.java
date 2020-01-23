/**
 * A class to implement the DynamicProgramming solver.
 * The attributes of this class (its state) are defined as the state of the DP algorithm.
 * So your dynamic programming solver can provide access afterwards to intermediate values in the table 
 * (e.g to provide the optimal value for other value of W without doing the complete computation again).
 * 
 * @author nicolas et hadrien
 */
public class PdynSolver {

    /**
     * Reference to the data
     */
    private KnapsackData data;

    /**
     * Value (dollar) of an optimal solution
     */
    private double optVal;

    /**
     * f[w][i]: the maximum value (dollars) achievable with items 1..i and a capacity of w
     */
    private double[][] f;

    /**
     * p[w][i] = w' gives the value w' which led to f[w][i] using f[w'][i-1].
     */
    private int[][] p;

    /**
     * Build a Pdyn solver
     * @param data
     */
    public PdynSolver(KnapsackData data) {
        this.data = data;
    }

    /**
     * @return the optimal value
     */
    public double getOptVal() {
        return optVal;
    }

    /**
     * Initialize the data structures needed for the DP
     * (TODO by the student in other activities)
     */
    private void init() {
        int n = data.getN();
        int W = data.getW();
        this.f = new double[W+1][n+1];
        this.p = new int[W+1][n+1];
    }

    /**
     * Solve the knapsack problem:
     * (TODO by the student in other activities)
     */
    public void solve() {
        int n = data.getN();
        int W = data.getW();
        this.init();
        for (int j = 1; j <= n; j++) {
            double vj = data.getItem(j-1).getValue(); // WARNING: the j-th item is indexed j-1 since indices start at 0 in java 
            int wj    = data.getItem(j-1).getWeight();
            for (int w = 0; w <= W; w++) {
                if (wj > w) {
                    f[w][j] = f[w][j-1];
                    p[w][j] = w;
                } else {
                    double oldvalue = f[w][j-1];
                    double newvalue = f[w-wj][j-1] + vj;
                    if (newvalue > oldvalue) {
                        f[w][j] = newvalue;
                        p[w][j] = w-wj;
                    } else {
                        f[w][j] = oldvalue;
                        p[w][j] = w;
                    }
                }
            }
        }
        //(TODO by the student in other activities): store the optimal value
        this.optVal = f[W][n];
    }
    
    /**
     * Print one optimal solution on the screen
     * (TODO by the student in other activities)
     **/
    public void printSolution() {
        String solution = "Solution: {";
        int currentw    = data.getW();
        for(int j=data.getN(); j>0; j--) {
            int prevw = p[currentw][j];
            if (prevw != currentw) {
                solution += " " + data.getItem(j-1).toString() + " ";
            }
            currentw = prevw;
        }
        solution += "}";
        System.out.println(solution);
    }

}
