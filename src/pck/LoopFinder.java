package pck;
/*
 * 
 * This is the loop finder. it is supposed to find start and end-loop points in a graph.
 * TODO remove pathing component from this set of rules.
 * 
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

public class LoopFinder {

	private final Relation Node, Start, Finish;

	private final Relation Edge, begin, end, corresp;

	private final Relation start_loop, end_loop, loop_set, node_after;

	public LoopFinder() {														/* Path */
		Node = Relation.unary("Node");
		Edge = Relation.unary("Edge");
		start_loop = Relation.unary("start_loop");
		end_loop = Relation.unary("end_loop");
		loop_set = Relation.unary("loop_set");
		node_after = Relation.unary("node_after");


		begin = Relation.binary("begin");
		end = Relation.binary("end");
		corresp = Relation.binary("corresp");

		Start = Relation.unary("Start");
		Finish = Relation.unary("Finish");
	}

	public Formula declarations() {
		final Formula f0 = begin.function(Edge, Node);
		final Formula f1 = end.function(Edge, Node);
		final Formula f4 = corresp.function(start_loop, end_loop);
		return f0.and(f1).and(f4);
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
		final Formula f3 = d.join(begin).eq(e.join(end));					/* e	n */
		/*	final Formula f4 = e.join(end).eq(m);	*/
		final Formula f5 = f3.forSome(e.oneOf(Edge).and(d.oneOf(Edge)));


		/* There is a Visit before all other Visits, which references an Edge that Begins at the Start Node. */
		/* There is a Visit after all other Visits, which references an Edge that Ends at the Finish Node. */
		// rechablefromN = set of nodes reachable from N.
		// nodeb4N = going from beginning to end... set ofnodes that come before the node N

		// start loop nodes are nodes such that their transitive closure contains the node itself, but the node that comes before
		// is not contained within the transitive closure.
		final Expression reachableFromN = (n.join(((begin.transpose()).join(end)).closure()));
		final Expression backreachableFromN = (n.join(((end.transpose()).join(begin)).closure()));
		final Expression nodeb4N       = (n.join(end.transpose() )).join(begin);
		final Expression begEnd = ((begin.transpose()).join(end)).closure(); // nodes reachable from node in question.
		final Expression nextNodeN = (((n.join(begin.transpose())).join(end)));
		final Expression Endbeg = ((end.transpose()).join(begin)).closure(); // nodes reachable from node in question going backwards.
		final Expression NodeAfter = (n.join(begin.transpose() )).join(end);



		final Formula f17 = n.in(reachableFromN);
		final Formula f18 = (nodeb4N.in(reachableFromN)).not();
		final Formula f19 = n.in(start_loop);
		final Formula f20 = (f18.and(f17)  ).iff(f19);
		final Formula f21 = f20.forAll((n.oneOf(Node)));


		final Formula f100 = n.in(reachableFromN);
		final Formula f101 = (NodeAfter.in(backreachableFromN)).not();
		final Formula f105 = n.in(start_loop).not();
		final Formula f102 = n.in(end_loop);
		final Formula f103 = (f100.and(f101).and(f105)).iff(f102);
		final Formula f104 = f103.forAll((n.oneOf(Node)));


		// SCHILLER's END SOLUTION
		/*  final Formula f22 = x.in(nextNodeN);
        final Formula f23 = n.in(n.join(begEnd));
        //final Formula f24 =     (x.join(begEnd).compare(ExprCompOperator.EQUALS, n.join(begEnd)));
        final Formula f24 = n.in(x.join(begEnd));
        final Formula f25 = n.in(end_loop);
        final Formula f26 = (f22.and(f23).and(f24).not()).iff(f25);
        final Formula f27 = f26.forAll(x.oneOf(Node).and(n.oneOf(Node)));

		 */



		// TODO THIS IS BREAKING IT.
		//        final Formula f22 = st.in(n.join(end.transpose()).join(end));








		// 2nd attempt.
		/*
        final Formula f22 = n.in((st.join(end.transpose())).join(begin));
        final Formula f23 = n.in(st.join(begEnd));
        final Formula f24 = n.in(end_loop);
        final Formula f25 = f24.implies(f22.and(f23));
        final Formula f26 = f25.forAll(n.oneOf(Node).and(st.oneOf(start_loop)));
		 */


		/*final Formula f22 = n.in(st.join(begEnd)); // an end node is any node that has an immediate pointer to a start node.
        final Formula f23 = n.in(end_loop);  // and is reachable from said start node.
        final Formula f24 = st.in(nextNodeN);
        final Formula f25 = (f24.and(f22)).iff(f23);
        final Formula f26 = f25.forAll(n.oneOf(Node).and(st.oneOf(start_loop)));
		 */





		final Formula f27 = n.in(n.join(begEnd));
		final Formula f28 = n.in(loop_set);
		final Formula f29 = f27.iff(f28);
		final Formula f30 = f29.forAll(n.oneOf(Node));

		final Formula f31 = x.in(start_loop);
		final Formula f32 = n.in(end_loop);
		final Formula f33 = x.in(nextNodeN);
		final Formula f34 = x.product(n).in(corresp);
		final Formula f35 = f34.iff(f33.and(f32).and(f31));
		final Formula f36 = f35.forAll(n.oneOf(Node).and(x.oneOf(Node)));

		/*
        final Formula f37 = n.in(end_loop);
        final Formula f38 = x.in(NodeAfter);
        final Formula f39 = x.in(node_after);
        final Formula f40 = (f37.and(f38)).implies(f39);
        final Formula f41 = f40.forAll(x.oneOf(Node).and(n.oneOf(Node)));
		 */




		/*
        final Formula f37 = x.in(  ( (n.join(end.transpose())).join(begin) ));
        final Formula f38 = x.in(n.join(begEnd));
        final Formula f42 = n.in(start_loop);
        final Formula f39 = x.in(end_loop);
        final Formula f43 = f37.and(f38).and(f42);
        final Formula f40 = f39.iff(f43);
        final Formula f41 = f40.forAll(x.oneOf(Node).and(n.oneOf(Node)));
		 */

		//   final Formula f37 =  (n.in( (st.join(end.transpose() )).join(begin))).not();  // n is not a node that came before st.

		/* another failed end loop form.
       final Formula f38 = n.in( st.join(end.transpose()).join(begin) );
       final Formula f40 = n.in(end_loop);
       final Formula f39 = st.in(start_loop);
       final Formula f41 = f40.iff(f38.and(f39));
       final Formula f42 = f41.forAll(n.oneOf(Node).and(st.oneOf(Node)));
		 */ 


















		//OLD END LOOP FORMULAS
		/*  final Formula f122 = n.in((st.join(begEnd))); // node in question reachable from start node in question.
		final Formula f123 = st.in(       nextNodeN.join(begEnd)          ).not();   // start node is not reachable from the NEXT node after n.
		final Formula f124 = n.in(end_loop);
		final Formula f125 = (n.in(Finish)).not(); // keep the bloody SAT solver from using a finishing nodes empty transitive closure to break my rules.
		final Formula f126 = f122.and(f123).iff(f124);
		final Formula f127 = f126.forAll(n.oneOf(Node).and(st.oneOf(start_loop)));
		 */


		//OLD LOOP_SET FORMULA
		// nodes in the loop set is the nodes reachable from the start node, minus the nodes reachable from the node after the end node.. so long as that NEXT node is not the start node.
		// expression is the node after the end node. so long as it's not the start node.
		/*final Expression afterEnd = (((en.join(begin.transpose())).join(end))).difference(st);
		final Expression reachableFromStart = st.join(begEnd);
		final Formula f28 = n.in(loop_set);
		final Formula f29 = n.in((reachableFromStart.difference(afterEnd.join(begEnd))).difference(afterEnd));
		final Formula f30 = f28.iff(f29);
		final Formula f31 = f30.forAll(n.oneOf(Node).and(st.oneOf(start_loop)).and(en.oneOf(end_loop)));

		 */
		/*  Formula f100 = x.in(nextNodeN);
        Formula f101 = st.in(nextNodeN);
        Formula f102 = st.in(n.join(begEnd));
        Formula f103 = (st.in(x.join(begEnd))).not();  // start node is not reachable from node after end node.
        Formula f104 = n.in(end_loop);
        Formula f105 = f104.implies(f103.and(f102).and(f101).and(f100));
        Formula f106 = f105.forAll(n.oneOf(Node).and(st.oneOf(start_loop).and(x.oneOf(Node))));
		 */




		return f5.and(f21).and(f30).and(f36).and(f104);

		//and f26
		//.and(f21).and(f27).and(f31);
	}

	public final Formula empty() {
		return declarations().and(facts());
	}
	/* this is the old bounds function that was provided. */ 
	public final Bounds buildGraph(Graph jpx) {



		Integer scope = jpx.getnumVisits();
		assert scope > 0;

		final List<String> atoms = new ArrayList<String>(40);
		atoms.addAll(jpx.getNodes());
		Integer numNodes = jpx.getNodes().size();

		atoms.addAll(jpx.getEdge());








		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		final int max = scope - 1;




		/* Java will not instantiate new Nodes. */
		b.bound(Node, f.range(f.tuple(jpx.getNodes().get(0)), f.tuple( jpx.getNodes().get(jpx.getNodes().size()-1))));
		b.bound(Edge, f.range(f.tuple(jpx.getEdge().get(0)), f.tuple( jpx.getEdge().get(jpx.getEdge().size()-1))));				/* Java will not instantiate new Edges. */
		b.bound(start_loop, f.range(f.tuple(jpx.getNodes().get(0)), f.tuple( jpx.getNodes().get(jpx.getNodes().size()-1))));
		b.bound(end_loop, f.range(f.tuple(jpx.getNodes().get(0)), f.tuple( jpx.getNodes().get(jpx.getNodes().size()-1))));
		b.bound(loop_set, f.range(f.tuple(jpx.getNodes().get(0)), f.tuple( jpx.getNodes().get(jpx.getNodes().size()-1))));
		b.bound(node_after, f.range(f.tuple(jpx.getNodes().get(0)), f.tuple( jpx.getNodes().get(jpx.getNodes().size()-1))));

		b.bound(corresp, b.upperBound(start_loop).product(b.upperBound(end_loop)));



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
	public static void find_loops(Graph jpx){
		try{
			FileWriter outFile = new FileWriter("./temp");
			PrintWriter out = new PrintWriter(outFile);

			final LoopFinder model = new LoopFinder();							/* Path		Path */
			final Solver solver = new Solver();
			final Bounds b = model.buildGraph(jpx);
			final Formula f = model.empty();
			System.out.println(f);
			solver.options().setSolver(SATFactory.DefaultSAT4J);
			System.out.println(System.currentTimeMillis());
			Iterator iterSols = solver.solveAll(f , b);
			System.out.println(System.currentTimeMillis());
			while(iterSols.hasNext()) {
				final Solution s = (Solution) iterSols.next();
				if(s.outcome() == Solution.Outcome.SATISFIABLE || s.outcome() == Solution.Outcome.TRIVIALLY_SATISFIABLE){
					out.print(s);
				}
			}





			//output goes here.
			//out.print(" ///// ");			

			outFile.close();
			out.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}


	public static void main(String[] argc){
		Graph jpx = new Graph();
		jpx.readFile("src/graphs/forloop.txt");
		LoopFinder.find_loops(jpx);
	}


}


