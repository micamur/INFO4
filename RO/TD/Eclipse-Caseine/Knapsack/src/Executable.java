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
        KnapsackData exemple = new KnapsackData(new int[]{6,3,4,2},new double[]{30,14,16,9},10);
        
        long time = System.currentTimeMillis();
        PdynSolver solver = new PdynSolver(exemple);
        solver.solve();
        solver.printSolution();
        time = (System.currentTimeMillis()-time);

        System.out.println(String.format("OPT: %.3f CPUTime: %.3f s", solver.getOptVal(),  (time/1000d)));
    }
}