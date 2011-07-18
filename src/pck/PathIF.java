package pck;

import java.util.ArrayList;
import java.util.List;
import java.util.Iterator;
import kodkod.ast.*;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.ExprOperator;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;

public class PathIF {

	private final Relation Node, Start, Finish;

	private final Relation Edge, begin, end, corresp;

	private final Relation Visit, ref, next, start_loop, end_loop, loop_set;

	public PathIF() {														/* Path */
		Node = Relation.unary("Node");
		Edge = Relation.unary("Edge");
		Visit = Relation.unary("Visit");
		start_loop = Relation.unary("start_loop");
		end_loop = Relation.unary("end_loop");
		loop_set = Relation.unary("loop_set");


		begin = Relation.binary("begin");
		end = Relation.binary("end");
		ref = Relation.binary("ref");
		next = Relation.binary("next");
		corresp = Relation.binary("corresp");

		Start = Relation.unary("Start");
		Finish = Relation.unary("Finish");
	}

	public Formula declarations() {
		final Formula f0 = begin.function(Edge, Node);
		final Formula f1 = end.function(Edge, Node);
		final Formula f2 = ref.function(Visit, Edge);	/* Node */
		final Formula f3 = next.partialFunction(Visit, Visit);
		final Formula f4 = corresp.function(start_loop, end_loop);
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
		// rechablefromN = set of nodes reachable from N.
		// nodeb4N = going from beginning to end... set ofnodes that come before the node N
		
		// start loop nodes are nodes such that their transitive closure contains the node itself, but the node that comes before
		// is not contained within the transitive closure.
		final Expression reachableFromN = (n.join(((begin.transpose()).join(end)).closure()));
		final Expression nodeb4N       = (n.join(end.transpose() )).join(begin);
		final Formula f17 = n.in(reachableFromN);
		final Formula f18 = (nodeb4N.in(reachableFromN)).not();
		final Formula f19 = n.in(start_loop);
		final Formula f20 = (f18.and(f17)  ).iff(f19);
		final Formula f21 = f20.forAll((n.oneOf(Node)));
		
		final Expression begEnd = ((begin.transpose()).join(end)).closure(); // nodes reachable from node in question.
        final Expression nextNodeN = (((n.join(begin.transpose())).join(end)));
        
        
        
        // SCHILLER's END SOLUTION
      /*  final Formula f22 = x.in(nextNodeN);
        final Formula f23 = n.in(n.join(begEnd));
        //final Formula f24 =     (x.join(begEnd).compare(ExprCompOperator.EQUALS, n.join(begEnd)));
        final Formula f24 = n.in(x.join(begEnd));
        final Formula f25 = n.in(end_loop);
        final Formula f26 = (f22.and(f23).and(f24).not()).iff(f25);
        final Formula f27 = f26.forAll(x.oneOf(Node).and(n.oneOf(Node)));
        
        */
        
        
        
		// THIS IS BREAKING IT.
        final Formula f22 = st.in(nextNodeN); // an end node is any node that has an immediate pointer to a start node.
        final Formula f23 = n.in(end_loop);  // and is reachable from said start node.
        final Formula f24 = n.in(st.join(begEnd));
        final Formula f25 = (f22.and(f24)).iff(f23);
        final Formula f26 = f25.forAll(n.oneOf(Node).and(st.oneOf(start_loop)));
        
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
        
        
        
        //OLD END LOOP FORMULAS
        /*final Formula f22 = n.in((st.join(begEnd))); // node in question reachable from start node in question.
		final Formula f23 = st.in(       nextNode.join(begEnd)          ).not();   // start node is not reachable from the NEXT node after n.
		final Formula f24 = n.in(end_loop);
		final Formula f25 = (n.in(Finish)).not(); // keep the bloody SAT solver from using a finishing nodes empty transitive closure to break my rules.
		final Formula f26 = f22.and(f23).and(f25).iff(f24);
		final Formula f27 = f26.forAll(n.oneOf(Node).and(st.oneOf(start_loop)));
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
		
		
		
		
	
		return f5.and(f8).and(f12).and(f16).and(f21).and(f30).and(f36);
		//and f26
//.and(f21).and(f27).and(f31);
	}

	public final Formula empty() {
		return declarations().and(facts());
	}
/* this is the old bounds function that was provided. */ 
	public final Bounds buildGraph(String filename) {
		
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
		b.bound(start_loop, f.range(f.tuple(jpx.getNodes().get(0)), f.tuple( jpx.getNodes().get(jpx.getNodes().size()-1))));
		b.bound(end_loop, f.range(f.tuple(jpx.getNodes().get(0)), f.tuple( jpx.getNodes().get(jpx.getNodes().size()-1))));
		b.bound(loop_set, f.range(f.tuple(jpx.getNodes().get(0)), f.tuple( jpx.getNodes().get(jpx.getNodes().size()-1))));
		
		b.bound(ref, b.upperBound(Visit).product(b.upperBound(Edge)));		/* Node */
		b.bound(next, b.upperBound(Visit).product(b.upperBound(Visit)));
		
		b.bound(corresp, b.upperBound(start_loop).product(b.upperBound(end_loop)));
		
		
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
			final PathIF model = new PathIF();							/* Path		Path */
			final Solver solver = new Solver();
			final Bounds b = model.buildGraph("src/graphs/input2.txt");
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
