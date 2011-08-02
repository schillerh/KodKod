package pck;
/*
 * 
 * This is the path finder, it should only ever be run on the main graph. After the main graph has been processed it will contain no loops, therefore the maximum length of the path
 * is equal to the number of edges in the graph.
 * TODO strip out the loop locating functionality.
 */
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
	public final Bounds buildpathGraph(String filename) {
		
		Graph jpx = new Graph();
		jpx.readFile(filename);

		Integer scope = jpx.getnumVisits();
		assert scope > 0;
		
		final List<String> atoms = new ArrayList<String>(40);
		atoms.addAll(jpx.getNodes());
		Integer numNodes = jpx.getNodes().size();
		
		atoms.addAll(jpx.getEdge());
		


		


		Integer temp = jpx.getnumVisits();
		System.out.println("maxvis = "+ temp);
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
		b.bound(Visit, f.range(f.tuple("Visit0"), f.tuple("Visit" + String.valueOf( Integer.valueOf( jpx.getnumVisits()) - 1 ))));
			
		b.bound(ref, b.upperBound(Visit).product(b.upperBound(Edge)));		/* Node */
		b.bound(next, b.upperBound(Visit).product(b.upperBound(Visit)));
		
		
		
		final TupleSet Next = f.noneOf(2);
		for(Integer i = 0; i < scope - 1; i++){
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
	public static void main(String[] args) {
		try {
			final PathFinder model = new PathFinder();							/* Path		Path */
			final Solver solver = new Solver();
			final Bounds b = model.buildpathGraph("src/graphs/forloop.txt");
			final Formula f = model.empty();
			System.out.println(f);
			solver.options().setSolver(SATFactory.DefaultSAT4J);
			System.out.println(System.currentTimeMillis());
			Iterator iterSols = solver.solveAll(f , b);
			System.out.println(System.currentTimeMillis());
			while(iterSols.hasNext()) {
				final Solution s = (Solution) iterSols.next();
				if(s.outcome() == Solution.Outcome.SATISFIABLE || s.outcome() == Solution.Outcome.TRIVIALLY_SATISFIABLE){
					System.out.println(s);	
				}
			}


		}	catch (NumberFormatException nfe) {}
	}
}
