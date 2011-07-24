package pck;

import java.util.ArrayList;

public class SubGraph extends Graph{

	//label is the string that describes what this graph stands for, and will replace in the final solution.
	private String label = new String();
	// start_loop isnt needed because it'll always be the start node of the subgraph.
	// end_loop is the node right after the end of the loop. in the case of a forloop, its where you end up if the for-loop never executes.
	private String end_loop   = new String();






/**
 * this method removes the nodes connecting the start_loop(aka start) and the end_loop node(NOT THE FINISH NODE) then solves the graph like normal.
 * this allows this normal solve method to check for further inner loops, and then solve them.
 */
	public void solveSubgraph(){
		// TODO remove loop connectors!!!!!!
		//<<remove the nodes that connect the start node, and the end_loop node. (end loop is a construct that only exists within a subgraph).
		
		
		
		
		// then just solve like normal.
		this.solveGraph();

	}








	public String getLabel() {
		return label;
	}








	public void setLabel(String label) {
		this.label = label;
	}








	public String getEnd_loop() {
		return end_loop;
	}








	public void setEnd_loop(String end_loop) {
		this.end_loop = end_loop;
	}
















}
