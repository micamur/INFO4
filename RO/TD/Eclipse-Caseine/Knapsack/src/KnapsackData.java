/**
 * Class representing a data set.
 * 
 * PLEASE DO NOT CHANGE THIS CLASS
 * @author nicolas et hadrien
 */
public class KnapsackData {

    /**
     * Number of items of the loot
     */
    private int n;

    /**
     * Set of items of the loot
     */
    private Item[] items;

    /**
     * Bag/Knapsack capacity
     */
    private int W;

    /**
     * Build a data set directly from a table of integers
     *
     * @param file
     */
    public KnapsackData(int[] weight, double[] values, int bagCapacity) {
        this.W = bagCapacity;
        this.n = weight.length;
        this.items = new Item[this.n];
        for (int i = 0; i < items.length; i++) {
            items[i] = new Item(i+1, weight[i], values[i]);
        }
    }

    //***********************************************//
    //************* Accessors ***********************//
    //***********************************************//
    
    public int getN() {
        return this.n;
    }
    
    public int getW() {
        return this.W;
    }
    
    public Item getItem(int i) {
        return items[i];
    }

}
