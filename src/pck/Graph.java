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


	private ArrayList<String> Nodes = new ArrayList<String>();
	private ArrayList<String> Edge = new ArrayList<String>();
	private ArrayList<Pair> begin = new ArrayList<Pair>();
	private ArrayList<Pair> end = new ArrayList<Pair>();
	private Integer numVisits = new Integer(0);
	String StartPt, endPt = new String();
	private ArrayList<SubGraph> subs = new ArrayList<SubGraph>();
	private String path = new String();

	public ArrayList<SubGraph> getSubs() {
		return subs;
	}

	public void setSubs(ArrayList<SubGraph> subs) {
		this.subs = subs;
	}

	public String getPath() {
		return path;
	}

	public void setPath(String path) {
		this.path = path;
	}

	public Integer getNumVisits() {
		return numVisits;
	}

	public void setNumVisits(Integer numVisits) {
		this.numVisits = numVisits;
	}


	/**
	 * blank constructor for graph class, just creates a blank graph.
	 */
	public Graph(){

		Nodes = new ArrayList<String>();
		Edge = new ArrayList<String>();
		begin = new ArrayList<Pair>();
		end = new ArrayList<Pair>();
		numVisits = new Integer(0);
		StartPt= endPt = new String();

	}

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
		assert numVisits > 0;
		assert numVisits <= 100;
		assert begin.size() == Nodes.size();
		assert end.size() ==   Nodes.size();

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
		this.begin = begin;
		this.end   = end;
	}




	/**
	 * reads an input file and sets up the graph in question. format is as follows:
	 * Line# line-text. no trailing commas, no spaces.
	 * 
	 * 0 Node1,Node2,Node3,Node4  // comma separated list of node names.
	 * 1 Edge1,Edge2,Edge3        // comma separated list of edge names
	 * 2 Node1                    // name of start node.
	 * 3 Node4                    // name of end node.
	 * 4 3                        // number of steps you want to complete the path in.... in terms of edges.
	 * 5 Edge1,Node1/Edge2,Node2                         // begin tupples
	 * 6 Edge1,Node1/Edge2,Node2
	 * 
	 * 
	 * 
	 * @param inputFileName
	 */
	public void readFile(String inputFileName){
		try {
			Scanner scan = new Scanner(new File(inputFileName));
			// collect node names.
			String temp = scan.next();
			String[] nodeinp = temp.split(",");
			for(Integer i = 0; i < nodeinp.length; i++){
				Nodes.add(nodeinp[i]);
			}





			// collect edges
			temp = scan.next();
			String[] edgeinp = temp.split(",");
			for(Integer i = 0; i < edgeinp.length; i++){
				Edge.add(edgeinp[i]);
			}





			// collect start point.
			temp = scan.next();
			StartPt = temp;

			// collect end point.
			temp = scan.next();
			endPt = temp;

			// collect number of visits.
			temp = scan.next();
			numVisits = Integer.valueOf(temp);

			temp = scan.next();
			String[] compHolder = temp.split("/");

			for(Integer i = 0; i < compHolder.length; i++){
				//temp is now just a tuple of format "Edge1,Node1
				temp = compHolder[i];
				begin.add(this.CreatePair(temp.split(",")[0], temp.split(",")[1]) );
			}

			temp = scan.next();
			compHolder = temp.split("/");
			for(Integer i = 0; i < compHolder.length; i++){
				//temp is now just a tuple of format "Edge1,Node1
				temp = compHolder[i];
				end.add(this.CreatePair(temp.split(",")[0], temp.split(",")[1]) );
			}








		} catch (FileNotFoundException e) {
			System.out.println( e.getMessage() );
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}




	}

	/**
	 * creates a pair for use as either a begin or end tuple.
	 * @param x - string. should refer to an existing edge.
	 * @param y - string. should refer to an existing node.
	 * @return -  returns pair composed of x and y.
	 * @throws Exception - throws an exception if X is not in the set of edges, or Y is not in the set of nodes.
	 */
	private Pair CreatePair(String x, String y) throws Exception{
		if(!Edge.contains(x)){
			throw new Exception("tried to connect an edge" +  x + " that doesn't exist");
		}
		if(!Nodes.contains(y)){
			throw new Exception("tryed to add a valid edge that connects to a node " +  y + " that doesn't exist.");
		}
		return new Pair(x,y);
	}














	/**
	 * returns a java.util.ArrayList of pairs in the format of (Edge,Node) such that Edge is an edge in the universe, and Node is the node that edge ends on.
	 * @return - ArrayList of pairs of format (Edge,Node) such that edge is an edge in the universe, and node is a node on which that edge ends upon.
	 */
	public ArrayList<Pair> getBegin() {
		return begin;
	}



	/**
	 * Sets the begin of all edges in the universe.
	 * @param begin - Accepts Pairs of type (Edge,Node) where an edge is the edge in question and the node is the node that edge begins on.
	 */
	public void setBegin(ArrayList<Pair> begin) {
		this.begin = begin;
	}



	/**
	 * returns a listing of all edge end points in the universe.
	 * @return - returns a pair in the format of (Edge,Node) where the edge is an edge that exists in the universe, and a node is the node where that edge ends.
	 */
	public ArrayList<Pair> getEnd() {
		return end;
	}



	/**
	 * Sets the end ofall edges in the universe.
	 * @param end - Accepts Pairs of type (Edge,Node) where an edge is the edge in question and the node is the node taht edge ends on.
	 */
	public void setEnd(ArrayList<Pair> end) {
		this.end = end;
	}



	public Integer getNumNodes(){
		return Nodes.size();
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

	/**
	 * Returns a list of all edges that currently exist in the universe.
	 * @return - returns java.util.ArrayList<String> containing all edges in the universe.
	 */
	public ArrayList<String> getEdge() {
		return Edge;
	}

	/**
	 * Sets names of all edges that exist in the universe.
	 * @param edge - takes java.util.ArrayList<String> which contains all edges that will later exist in the universe.
	 */
	public void setEdge(ArrayList<String> edge) {
		Edge = edge;
	}


	/**
	 * returns number of edges you want in your traversed path.
	 * @return - Integer.
	 */
	public Integer getnumVisits() {
		return numVisits;
	}

	/**
	 * sets the current number of steps you want to complete the path in. This is counted in terms of edges.
	 * @param numVisits - number of edges you want to traverse in your finished path.
	 */
	public void setnumVisits(Integer numVisits) {
		this.numVisits = numVisits;
	}

	/**
	 * retrieves current start of path
	 * @return  - String name of node.
	 */
	public String getStartPt() {
		return StartPt;
	}

	/**
	 * sets name of start node of path. must exist within the set of nodes.
	 * @param startPt - String name of start node of path, must exist within set of nodes.
	 */
	public void setStartPt(String startPt) {
		StartPt = startPt;
	}

	/**
	 * retrieves string name of endpoint
	 * @return - String, name of current end of path node.
	 */
	public String getEndPt() {
		return endPt;
	}




	/**
	 * sets internal endpoint to the endpoint specified, end point being the node at the end of the path.
	 * @param endPt - String name of node to be set. this must exist within the set of nodes or you'll run into problems later.
	 */
	public void setEndPt(String endPt) {
		this.endPt = endPt;
	}

	/**
	 * Outputs the content of this graph to console.
	 */
	public void printMe(){
		System.out.println("==================================================");
		System.out.println("Current Graph Contains:");
		System.out.println("");
		System.out.println("Nodes: ");
		System.out.println(Nodes.toString());
		System.out.println("");
		System.out.println("Edges: ");
		System.out.println(Edge.toString());

		System.out.println("");

		System.out.println("StartNode: " + StartPt.toString());
		System.out.println("");
		System.out.println("EndNode: " + endPt.toString());
		System.out.println("");

		System.out.println("Begin Pairs :" + begin.size());
		for(int i = 0; i < begin.size(); i++){
			System.out.println("( " + begin.get(i).getX() + ", " + begin.get(i).getY() + " )");
		}
		System.out.println("");
		System.out.println("End Pairs : ");
		for(int i = 0; i < end.size(); i++){
			System.out.println("( " + end.get(i).getX() + ", " + end.get(i).getY() + " )");
		}

		System.out.println();
		System.out.println("Num Visits == " + numVisits);

		System.out.println("");
		System.out.println("Proper Edges: ");
		for(int i = 0; i < begin.size(); i++){
			System.out.println("( " + begin.get(i).getY() + " , " + end.get(i).getY() + " )");
		}

		System.out.println();
		System.out.println("==================================================");

	}

	/**
	 * This private method solves all the subgraphs in this graph, by calling solveSubGraph on all of them.
	 */
	protected void solveAllSubgraphs(){
		for(int i = 0; i < subs.size(); i++){
			subs.get(i).solveSubgraph();
		}
	}

	/**
	 * this method solves the current graph, and sets it's path string.
	 */
	public void solveGraph(){
		// TODO if loops exist....
		// TODO remove loops from graph.... and create subgraphs. then solve subgraphs. <-- magic function.

		this.createSubGraphs();



		this.solveAllSubgraphs();
		// TODO then solve this graph <using normal methods in the pathfinder.. simply solve graph, and convert solutions into the pathstring>
		// TODO then replace subgraph labels in path string with subgraph solutions. <this one should be pretty easy>
		// finally set path string in THIS graph to final solution.

		this.solvePath();


	}

	protected void solvePath(){
		//TODO this runs the path solver on the current graph, does not change anything. simply runs it, interprets the output, and sets the path string.
		//uses path string from the subgraphs to generate the pathstring, so make sure you create and solve them first. 
		// this is intended to only be run on graphs that DO NOT CONTAIN LOOPS. Otherwise, it will take a long time to complete.
		this.setPath(PathFinder.find_path(this));
		System.out.println("path found == " + this.getPath());
		
	}








	/**
	 * this private method finds all loops contained within the current graph, and eliminates them, generating a set of subgraphs now contained within this graph.
	 * These subgraphs can then be solved by the solveAllSubGraphs() method.
	 */
	protected void createSubGraphs() {
		// TODO this function removes all the loops from a graph and replaces them with singular nodes. named LOOP[INDEX] eg LOOP1
		// TODO all edges that point to the start node now point to the LOOP node.
		// TODO all edges that begin on the node AFTER the end node now begin with the LOOP node.

		//since these are saved locally it's okay to re-use the indexes for each graph and it's respective subgraphs.

	}

	/**
	 * short test for the graph.java class.
	 * @param argc - ignore.
	 */
	public static void main(String[] argc){
		Graph test  = new Graph();
		Graph test2 = new Graph();
		Graph test3 = new Graph();
		//test.readFile("src/graphs/forloop.txt");
		//test.printMe();
		test2.readFile("src/graphs/parallelloops.txt");
		test2.solvePath();
		test3.readFile("src/graphs/linearinput.txt");
		test3.solvePath();
		System.out.println("test complete");
	}









}
