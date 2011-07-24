package pck;
/**
 * Pair class for setting/retrieving/managing a tuple of arity 2 of type string.
 * @author Cory M. Lee
 *
 */
public class Pair {
	String x;
	String y;
	
	
	/**
	 * constructor which constructs a pair, containing two strings.
	 * @param x - name of x param.
	 * @param y - name of y param.
	 */
	public Pair(String x, String y){
	this.x = x;
	this.y = y;
	}

	public void setPair(String inpx, String inpy){
		this.x = inpx;
		this.y = inpy;
	}

	public String getX() {
		return x;
	}

	public String getY() {
		return y;
	}





}
