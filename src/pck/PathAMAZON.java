package pck;

import java.util.ArrayList;
import java.util.List;
import java.util.Iterator;
import kodkod.ast.*;
import kodkod.instance.*;
import kodkod.engine.*;
import kodkod.engine.satlab.SATFactory;

public class PathAMAZON {

	private final Relation Node, Start, Finish;
	
	private final Relation Edge, begin, end;
	
	private final Relation Visit, ref, next;
	
	public PathAMAZON() {														/* Path */
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
		final Variable v = Variable.unary("v");
		final Variable w = Variable.unary("w");
		final Variable e = Variable.unary("e");								/* n */
		final Variable d = Variable.unary("d");								/* d */
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
		final Formula f8 = f6.implies(f7).forAll(v.oneOf(Visit).and(w.oneOf(Visit)));

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
	}
	
	public final Formula empty() {
 		return declarations().and(facts());
 	}

	public final Bounds bounds1(int scope) {
		assert scope > 0;
		final int n = scope + 14;
		final List<String> atoms = new ArrayList<String>(n);
		for (int i = 1; i <= 7; i++)
			atoms.add("Node" + i);
		for (int i = 1; i <= 7; i++)
			atoms.add("Edge" + i);
		for (int i = 0; i < scope; i++)
			atoms.add("Visit" + i);

		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final int max = scope - 1;
		
		b.bound(Node, f.range(f.tuple("Node1"), f.tuple("Node7")));				
		b.bound(Edge, f.range(f.tuple("Edge1"), f.tuple("Edge7")));				
		b.bound(Visit, f.range(f.tuple("Visit0"), f.tuple("Visit" + max)));
		
		b.bound(ref, b.upperBound(Visit).product(b.upperBound(Edge)));		
		b.bound(next, b.upperBound(Visit).product(b.upperBound(Visit)));

		final TupleSet Begins = f.noneOf(2);
		Begins.add(f.tuple("Edge1", "Node1"));
		Begins.add(f.tuple("Edge2", "Node2"));
		Begins.add(f.tuple("Edge3", "Node2"));
		Begins.add(f.tuple("Edge4", "Node3"));
		Begins.add(f.tuple("Edge5", "Node4"));
		Begins.add(f.tuple("Edge6", "Node5"));
		Begins.add(f.tuple("Edge7", "Node5"));
		b.boundExactly(begin , Begins);

		final TupleSet Ends = f.noneOf(2);
		Ends.add(f.tuple("Edge1", "Node2"));
		Ends.add(f.tuple("Edge2", "Node3"));
		Ends.add(f.tuple("Edge3", "Node4"));
		Ends.add(f.tuple("Edge4", "Node5"));
		Ends.add(f.tuple("Edge5", "Node5"));
		Ends.add(f.tuple("Edge6", "Node6"));
		Ends.add(f.tuple("Edge7", "Node7"));
		b.boundExactly(end , Ends);

		final TupleSet Node1 = f.noneOf(1);									
		Node1.add(f.tuple("Node1"));										
		b.boundExactly(Start , Node1);										

		final TupleSet Node7 = f.noneOf(1);									
		Node7.add(f.tuple("Node7"));										
		b.boundExactly(Finish , Node7);										
	
		return b;
	}

	public final Bounds bounds2(int scope) {
		assert scope > 0;
		final int n = scope + 12;
		final List<String> atoms = new ArrayList<String>(n);
		for (int i = 1; i <= 5; i++)
			atoms.add("Node" + i);
		for (int i = 1; i <= 7; i++)
			atoms.add("Edge" + i);
		for (int i = 0; i < scope; i++)
			atoms.add("Visit" + i);

		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final int max = scope - 1;
		
		b.bound(Node, f.range(f.tuple("Node1"), f.tuple("Node5")));				
		b.bound(Edge, f.range(f.tuple("Edge1"), f.tuple("Edge7")));				
		b.bound(Visit, f.range(f.tuple("Visit0"), f.tuple("Visit" + max)));
		
		b.bound(ref, b.upperBound(Visit).product(b.upperBound(Edge)));		
		b.bound(next, b.upperBound(Visit).product(b.upperBound(Visit)));

		final TupleSet Begins = f.noneOf(2);
		Begins.add(f.tuple("Edge1", "Node1"));
		Begins.add(f.tuple("Edge2", "Node1"));
		Begins.add(f.tuple("Edge3", "Node1"));
		Begins.add(f.tuple("Edge4", "Node2"));
		Begins.add(f.tuple("Edge5", "Node3"));
		Begins.add(f.tuple("Edge6", "Node4"));
		Begins.add(f.tuple("Edge7", "Node5"));
		b.boundExactly(begin , Begins);

		final TupleSet Ends = f.noneOf(2);
		Ends.add(f.tuple("Edge1", "Node2"));
		Ends.add(f.tuple("Edge2", "Node3"));
		Ends.add(f.tuple("Edge3", "Node4"));
		Ends.add(f.tuple("Edge4", "Node5"));
		Ends.add(f.tuple("Edge5", "Node5"));
		Ends.add(f.tuple("Edge6", "Node5"));
		Ends.add(f.tuple("Edge7", "Node1"));
		b.boundExactly(end , Ends);

		final TupleSet StartNode = f.noneOf(1);									
		StartNode.add(f.tuple("Node1"));										
		b.boundExactly(Start , StartNode);
		
		final TupleSet FinishNode = f.noneOf(1);									
		FinishNode.add(f.tuple("Node1"));										
		b.boundExactly(Finish , FinishNode);										
	
		return b;
	}

	public final Bounds bounds3(int scope) {
		assert scope > 0;
		final int n = scope + 3;
		final List<String> atoms = new ArrayList<String>(n);
		for (int i = 1; i <= 2; i++)
			atoms.add("Node" + i);
		for (int i = 1; i <= 1; i++)
			atoms.add("Edge" + i);
		for (int i = 0; i < scope; i++)
			atoms.add("Visit" + i);

		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);
		
		final int max = scope - 1;
		
		b.bound(Node, f.range(f.tuple("Node1"), f.tuple("Node2")));				
		b.bound(Edge, f.range(f.tuple("Edge1"), f.tuple("Edge1")));				
		b.bound(Visit, f.range(f.tuple("Visit0"), f.tuple("Visit" + max)));
		
		b.bound(ref, b.upperBound(Visit).product(b.upperBound(Edge)));		
		b.bound(next, b.upperBound(Visit).product(b.upperBound(Visit)));

		final TupleSet Begins = f.noneOf(2);
		Begins.add(f.tuple("Edge1", "Node1"));
		b.boundExactly(begin , Begins);

		final TupleSet Ends = f.noneOf(2);
		Ends.add(f.tuple("Edge1", "Node2"));
		b.boundExactly(end , Ends);

		final TupleSet Node1 = f.noneOf(1);									
		Node1.add(f.tuple("Node1"));										
		b.boundExactly(Start , Node1);

		final TupleSet Node2 = f.noneOf(1);									
		Node2.add(f.tuple("Node2"));		
		b.boundExactly(Finish , Node2);
	
		return b;
	}

	@SuppressWarnings("rawtypes")
	public static void main(String[] args) {
		try {
			final PathAMAZON model = new PathAMAZON();							/* Path		Path */
			final Solver solver = new Solver();

			final Bounds b1 = model.bounds1(7);
 			final Bounds b2 = model.bounds2(3);
 			final Bounds b3 = model.bounds3(1);
 
			final Formula f = model.empty();
			System.out.println(f);
			solver.options().setSolver(SATFactory.DefaultSAT4J);
			
			System.out.println(System.currentTimeMillis());
			Iterator iterSols1 = solver.solveAll(f , b1);
			Iterator iterSols2 = solver.solveAll(f , b2);
			Iterator iterSols3 = solver.solveAll(f , b3);
			System.out.println(System.currentTimeMillis());
			
			while(iterSols1.hasNext()) {
				final Solution s1 = (Solution) iterSols1.next();
				System.out.println(s1);	
			}
			while(iterSols2.hasNext()) {
				final Solution s2 = (Solution) iterSols2.next();
				System.out.println(s2);	
			}
			while(iterSols3.hasNext()) {
				final Solution s3 = (Solution) iterSols3.next();
				System.out.println(s3);	
			}
 
		}	catch (NumberFormatException nfe) {}
	}
}
