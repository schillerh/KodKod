package pck;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Scanner;

/**
 * Graph class which contains definition of a control flow graph and methods for reading-in a comma separated
 * control flow graph from a file
 * @author Cory M. Lee
 *
 */
public class Graph {
	
	private ArrayList<String> Nodes;
	private ArrayList<String> Edge;
	private ArrayList<Pair> begin;
	private ArrayList<Pair> end;
	
	
	/**
	 * Consructor for graph class.
	 * @param Nodes - ArrayList of Strings, these are the names of the nodes.
	 * @param Edge  - ArrayList of Edges, these are names of the Edges.
	 * @param begin - ArrayList of Pairs, these are the tuples of type Edge, Node. Pairs an edge with the node it begins on.
	 * @param end   - ArrayList of Pairs, these are the tuples of type Edge, Node. Pairs an edge with the node it ends on.
	 * @param numVisits - Number of steps(in edges) you want to complete pathing through this graph.
	 * @param StartPt   - the node where you want your path to start from. Must be contained in the ArrayList of Nodes or an exception will be thrown.
	 * @param endPt     - the node where you want your path to end. Must be contained in the ArrayList of Nodes or an exception will be thrown.
	 * @throws Exception - Exception is thrown when StartPt or Endpt are not contained within the ArrayList of Nodes.
	 */
	public Graph(ArrayList<String> Nodes, ArrayList<String> Edge, ArrayList<Pair> begin, ArrayList<Pair> end, Integer numVisits, String StartPt, String endPt) throws Exception{
		assert Nodes != null;
		assert Edge != null;
		assert numVisits != 0;
		if(! Nodes.contains(StartPt)){
			throw new Exception("Start Node is not in the set of nodes");
		}
		
		if(! Nodes.contains(endPt)){
			throw new Exception("End node is not in the set of nodes");
		}

		this.Nodes= Nodes;
		this.Edge = Edge;
		this.StartPt = StartPt;
		this.endPt = endPt;
		this.numVisits = numVisits;
	}
	
	
	
	
	/**
	 * reads an input file and sets up the graph in question. format is as follows:
	 * Line# line-text. no trailing commas, no spaces.
	 * 
	 * 0 Node1,Node2,Node3,Node4
	 * 1 Edge1,Edge2,Edge3
	 * 2
	 * 
	 * 
	 * 
	 * 
	 * @param inputFileName
	 */
	public void readFile(String inputFileName){
		try {
			Scanner scan = new Scanner(new File(inputFileName));
			
			
			
			
		} catch (FileNotFoundException e) {
			System.out.println( e.getMessage() );
		}
		
		
		
		
	}
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	/**
	 * returns the nodes.
	 * @return returns ArrayList of node names in graph.
	 */
	public ArrayList<String> getNodes() {
		return Nodes;
	}

/**
 * takes in an ArrayList, and sets node content of the current graph to the content of that ArrayList.
 * @param nodes
 */
	public void setNodes(ArrayList<String> nodes) {
		Nodes = nodes;
	}


	public ArrayList<String> getEdge() {
		return Edge;
	}


	public void setEdge(ArrayList<String> edge) {
		Edge = edge;
	}


	public Integer getNumVisits() {
		return numVisits;
	}


	public void setNumVisits(Integer numVisits) {
		this.numVisits = numVisits;
	}


	public String getStartPt() {
		return StartPt;
	}


	public void setStartPt(String startPt) {
		StartPt = startPt;
	}


	public String getEndPt() {
		return endPt;
	}


	public void setEndPt(String endPt) {
		this.endPt = endPt;
	}


	private Integer numVisits;
	String StartPt, endPt;

	
	
	
	
	
	
	
	
	
	
	

}
