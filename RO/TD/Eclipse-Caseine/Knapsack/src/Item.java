/**
 * A class representing an item of the loot.
 * PLEASE DO NOT CHANGE THIS CLASS
 * @author nicolas et hadrien
 */
public class Item {

    /**
     * Index of the item
     */
    private int idx;

    /**
     * Weight of the item
     */
    private int weight;

    /**
     * Value of the item
     */
    private double value;

    /**
     * Builds an item of the loot.
     * @param idx: index of the item
     * @param weight: weight of the item
     * @param value: value (in dollars) in the item
     */
    public Item(int idx, int weight, double value) {
        this.idx = idx;
        this.weight = weight;
        this.value = value;
    }
    
    /**
     * @return index of the item
     */
    public int getIdx() {
        return idx;
    }

    /**
     * @return weight of the item
     */
    public int getWeight() {
        return weight;
    }
    
    /**
     * @return monetary value (dollars) of the item
     */
    public double getValue() {
        return value;
    }

    public String toString() {
        return "("+idx+","+weight+","+value+")";
    }
   
}
