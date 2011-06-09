package pck;

import java.util.ArrayList;
import java.util.List;
import java.util.Iterator;
import kodkod.ast.*;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;

import kodkod.ast.Relation;

public class SchillerCoryIF{
	
	private final Relation Node, Start, Finish;
	
	private final Relation Edge, begin, end;
	
	private final Relation Visit, ref, next;
	
	
public SchillerCoryIF(){
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
	final Formula f2 = ref.function(Visit, Edge);						/* Node */
	final Formula f3 = next.partialFunction(Visit, Visit);
	
	return f0.and(f1).and(f2).and(f3);
}


public final Formula facts() {
	/* CONFORMITY: The structure of the path conforms to the structure of the graph. */
	/* ACYCLICITY: The path is an acyclic sequence of Visits. */
	/* There is a Visit before all other Visits, which references an Edge that Begins at the Start Node. */
	/* There is a Visit after all other Visits, which references an Edge that Ends at the Finish Node. */
	
	
	
	
	
	return null;
}


public final Formula empty() {
		return declarations().and(facts());
	}


public final Bounds getbounds(int scope) {
	assert scope > 0;
	final int n = scope + 13;
	final List<String> atoms = new ArrayList<String>(n);
	for (int i = 1; i <= 6; i++)
		atoms.add("Node" + i);
	for (int i = 1; i <= 6; i++)
		atoms.add("Edge" + i);
	for (int i = 0; i < scope; i++)
		atoms.add("Visit" + i);

	final Universe u = new Universe(atoms);
	final TupleFactory f = u.factory();
	final Bounds b = new Bounds(u);
	
	final int max = scope - 1;
	
	b.bound(Node, f.range(f.tuple("Node1"), f.tuple("Node6")));				/* Java will not instantiate new Nodes. */
	b.bound(Edge, f.range(f.tuple("Edge1"), f.tuple("Edge7")));				/* Java will not instantiate new Edges. */
	b.bound(Visit, f.range(f.tuple("Visit0"), f.tuple("Visit" + max)));
	
	b.bound(ref, b.upperBound(Visit).product(b.upperBound(Edge)));		/* Node */
	b.bound(next, b.upperBound(Visit).product(b.upperBound(Visit)));

	final TupleSet Begins = f.noneOf(2);
	Begins.add(f.tuple("Edge1", "Node1"));
	Begins.add(f.tuple("Edge2", "Node2"));
	Begins.add(f.tuple("Edge3", "Node2"));
	Begins.add(f.tuple("Edge4", "Node3"));
	Begins.add(f.tuple("Edge5", "Node4"));
	Begins.add(f.tuple("Edge6", "Node5"));
	b.boundExactly(begin , Begins);

	final TupleSet Ends = f.noneOf(2);
	Ends.add(f.tuple("Edge1", "Node2"));
	Ends.add(f.tuple("Edge2", "Node3"));
	Ends.add(f.tuple("Edge3", "Node4"));
	Ends.add(f.tuple("Edge4", "Node5"));
	Ends.add(f.tuple("Edge5", "Node5"));
	Ends.add(f.tuple("Edge6", "Node6"));
	b.boundExactly(end , Ends);

	final TupleSet Node1 = f.noneOf(1);									/* Node1 */
	Node1.add(f.tuple("Node1"));										/* Node1 */
	b.boundExactly(Start , Node1);										/* Node1 */

	final TupleSet Node6 = f.noneOf(1);									/* Node4 */
	Node6.add(f.tuple("Node6"));										/* Node4 */
	b.boundExactly(Finish , Node6);										/* Node4 */

	return b;
}

@SuppressWarnings("rawtypes")
public static void main(String[] args) {
	try {
		final PathIF model = new PathIF();							/* Path		Path */
		final Solver solver = new Solver();
		final Bounds b = model.bounds(10);
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
