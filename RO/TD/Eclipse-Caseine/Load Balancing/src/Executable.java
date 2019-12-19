/**
 * @author nicolas et hadrien
 */
public class Executable {


    /**
     * An example of how to use the program.
     * It is up to you to create your own tests for the various instances.
     * @param args
     */
    public static void main(String[] args) {
        BalancingData exemple = new BalancingData(new int[]{4,10,7,5,3},14);

        long time = System.currentTimeMillis();
        PdynSolver solver = new PdynSolver(exemple);
        solver.solve();
        System.out.println(solver.solutionToString());
        time = (System.currentTimeMillis()-time);

        System.out.println(String.format("OPT: %d CPUTime: %.3f s", solver.getOptVal(),  (time/1000d)));
    }
}