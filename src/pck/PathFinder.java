package pck;
/*
 * 
 * This is the path finder, it should only ever be run on the main graph. After the main graph has been processed it will contain no loops, therefore the maximum length of the path
 * is equal to the number of edges in the graph.
 * TODO strip out the loop locating functionality.
 */
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.Iterator;
import kodkod.ast.*;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.ExprOperator;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;

public class PathFinder {

	private final Relation Node, Start, Finish;

	private final Relation Edge, begin, end;

	private final Relation Visit, ref, next;

	public PathFinder() {														/* Path */
		Node = Relation.unary("Node");
		Edge = Relation.unary("Edge");
		Visit = Relation.unary("Visit");


		begin = Relation.binary("begin");
		end = Relation.binary("end");
		ref = Relation.binary("ref");
		next = Relation.binary("next");


		Start = Relation.unary("Start");
		Finish = Relation.unary("Finish");
	}

	public Formula declarations() {
		final Formula f0 = begin.function(Edge, Node);
		final Formula f1 = end.function(Edge, Node);
		final Formula f2 = ref.function(Visit, Edge);	/* Node */
		final Formula f3 = next.partialFunction(Visit, Visit);
		return f0.and(f1).and(f2).and(f3);
	}

	public final Formula facts() {
		final Variable v = Variable.unary("v");
		final Variable w = Variable.unary("w");
		final Variable e = Variable.unary("e");								/* n */
		final Variable d = Variable.unary("d");								/* d */
		final Variable n = Variable.unary("n");
		final Variable st = Variable.unary("st");
		final Variable en = Variable.unary("en");
		final Variable x = Variable.unary("x");
		final Variable x2 = Variable.unary("x2");
		//	final Variable end = Variable.unary("end");
		/*	final Variable e = Variable.unary("e");	*/

		/* CONFORMITY: The structure of the path conforms to the structure of the graph. */
		final Formula f0 = v.join(next).eq(w);
		final Formula f1 = v.join(ref).eq(e);								/* n */
		final Formula f2 = w.join(ref).eq(d);								/* m */
		final Formula f3 = d.join(begin).eq(e.join(end));					/* e	n */
		/*	final Formula f4 = e.join(end).eq(m);	*/
		final Formula f4 = f0.and(f1).and(f2).implies(f3);
		final Formula f5 = f4.forAll(v.oneOf(Visit).and(w.oneOf(Visit)).and(e.oneOf(Edge)).and(d.oneOf(Edge)));

		/* ACYCLICITY: The path is an acyclic sequence of Visits. */
		final Formula f6 = v.in(w.join(next.reflexiveClosure()));
		final Formula f7 = w.in(v.join(next.closure())).not();
		final Formula f8 = f6.iff(f7).forAll(v.oneOf(Visit).and(w.oneOf(Visit)));

		/* There is a Visit before all other Visits, which references an Edge that Begins at the Start Node. */
		final Formula f9 = v.join(ref.join(begin)).eq(Start);
		final Formula f10 = w.in(v.join(next.reflexiveClosure()));
		final Formula f11 = f9.and(f10);
		final Formula f12 = f11.forSome(v.oneOf(Visit)).forAll(w.oneOf(Visit));

		/* There is a Visit after all other Visits, which references an Edge that Ends at the Finish Node. */
		final Formula f13 = v.join(ref.join(end)).eq(Finish);
		final Formula f14 = v.in(w.join(next.reflexiveClosure()));
		final Formula f15 = f13.and(f14);
		final Formula f16 = f15.forSome(v.oneOf(Visit)).forAll(w.oneOf(Visit));


		return f5.and(f8).and(f12).and(f16);

		//and f26
		//.and(f21).and(f27).and(f31);
	}

	public final Formula empty() {
		return declarations().and(facts());
	}
	/* this is the old bounds function that was provided. */ 
	public final Bounds buildpathGraph(Graph jpx, Integer bound) {



		Integer scope = jpx.getnumVisits();
		assert scope > 0;

		final List<String> atoms = new ArrayList<String>(40);
		atoms.addAll(jpx.getNodes());
		Integer numNodes = jpx.getNodes().size();

		atoms.addAll(jpx.getEdge());






		Integer temp = jpx.getnumVisits();
		for (int i = 0; i < temp; i++){
			atoms.add("Visit" + i);
		}


		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		final int max = scope - 1;




		/* Java will not instantiate new Nodes. */
		b.bound(Node, f.range(f.tuple(jpx.getNodes().get(0)), f.tuple( jpx.getNodes().get(jpx.getNodes().size()-1))));
		b.bound(Edge, f.range(f.tuple(jpx.getEdge().get(0)), f.tuple( jpx.getEdge().get(jpx.getEdge().size()-1))));				/* Java will not instantiate new Edges. */
		b.bound(Visit, f.range(f.tuple("Visit0"), f.tuple("Visit" + String.valueOf( bound - 1))));

		b.bound(ref, b.upperBound(Visit).product(b.upperBound(Edge)));		/* Node */
		b.bound(next, b.upperBound(Visit).product(b.upperBound(Visit)));



		final TupleSet Next = f.noneOf(2);
		for(Integer i = 0; i < bound - 1; i++){
			Integer plusone = i + 1;
			Next.add(f.tuple("Visit"+i, "Visit"+plusone));
		}
		b.boundExactly(next, Next);

		final TupleSet Begins = f.noneOf(2);
		for(Integer i = 0; i < jpx.getBegin().size(); i++){
			Begins.add(f.tuple(jpx.getBegin().get(i).getX(), jpx.getBegin().get(i).getY()));
		}
		b.boundExactly(begin , Begins);


		final TupleSet Ends = f.noneOf(2);
		for(Integer i = 0; i < jpx.getEnd().size(); i++){
			Ends.add(f.tuple(jpx.getEnd().get(i).getX(), jpx.getEnd().get(i).getY()));
		}
		b.boundExactly(end , Ends);

		final TupleSet start = f.noneOf(1);		
		start.add(f.tuple(jpx.getStartPt()));										/* Node1 */
		b.boundExactly(Start , start);										/* Node1 */

		final TupleSet en = f.noneOf(1);									/* Node4 */
		en.add(f.tuple(jpx.getEndPt()));										/* Node4 */
		b.boundExactly(Finish , en);										/* Node4 */

		return b;
	}


	@SuppressWarnings("rawtypes")
	public static void find_path(Graph jpx) {
		try {

			FileWriter outFile = new FileWriter("./temp");
			PrintWriter out = new PrintWriter(outFile);

			final PathFinder model = new PathFinder();							/* Path		Path */
			final Solver solver = new Solver();

			final Formula f = model.empty();
			System.out.println(f);
			solver.options().setSolver(SATFactory.DefaultSAT4J);


			assert jpx.getNumNodes() > 0;
			for(int i = 1; i <= jpx.getNumNodes() - 1; i ++){
				out.println("Finding paths for Bounds == " + i);
				final Bounds b = model.buildpathGraph(jpx, i);
				Iterator iterSols = solver.solveAll(f , b);
				while(iterSols.hasNext()){
					Solution s = (Solution)iterSols.next();
					if(s.outcome() == Solution.Outcome.SATISFIABLE || s.outcome() == Solution.Outcome.TRIVIALLY_SATISFIABLE){
						System.out.println(s);
						out.print(s);
						String[] temp  = s.toString().split("ref=");
						System.out.println("");
						System.out.println("");
						temp = temp[1].split(", next=");
						temp = temp[0].split(", ");
						ArrayList<String> ee = new ArrayList<String>();
						for(int x = 0; x < temp.length; x++)
						{
							if(x % 2 == 1){
								ee.add(temp[x].split("]")[0].trim());
							}
						}



						// at this point ee contains a list of the edges traversed in a path. we want to convert this to nodes.

						temp = s.toString().split("end=");
						temp = temp[1].split(", Start=");
						temp = temp[0].split(", ");
						ArrayList<String> en = new ArrayList<String>();
						String temp2 = new String();

						for(int x = 0; x< temp.length; x++){
							if(x == 0){
								en.add(temp[0].substring(2, temp[0].length()).trim());
							}
							else if(x == temp.length - 1 ){
								en.add(temp[temp.length - 1].substring(0, temp[temp.length - 1].length() - 2).trim());
							}

							else if(x % 2 == 1){
								en.add(temp[x].substring(0, temp[x].length() - 1).trim());

							}
							else{
								en.add(temp[x].substring(1, temp[x].length()).trim());
							}

						}

						//finally we solve the bloody path.
						StringBuffer pathtemp = new StringBuffer();

						pathtemp.append("(" + jpx.getStartPt() + ",");
						for(int x = 0; x < ee.size(); x++){
							Integer index = en.indexOf(ee.get(x)) + 1;
							pathtemp.append( en.get(index));
							if(x != ee.size() - 1){
								pathtemp.append(",");
							}
							else{
								pathtemp.append(")");
							}

						}




						String fin = pathtemp.toString();
						System.out.println("path == " + fin);
					}
				}

			}
			outFile.close();
			out.close();

		}	catch (NumberFormatException nfe) {}
		catch (IOException e) {}
	}

	public static void main(String[] argc){
		Graph jpx = new Graph();
		jpx.readFile("src/graphs/linearinput.txt");
		PathFinder.find_path(jpx);
	}
}
