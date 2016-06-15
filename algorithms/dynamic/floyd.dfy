/**
 * Floyd-Warshall algorithm (1959)
 *
 * Minimum path cost in a negative cycle free directed graph.
 *
 * The absence of negative cycles is set as a precondition.
 * However it can be modified to detect the presence of
 * negative cycles.
 *
 * Taken from:
 * https://en.wikipedia.org/wiki/Floyd–Warshall_algorithm&oldid=710345047
 */


/**
 * A special cost value (infinity) is used to point out that there is no
 * connection between two nodes. Dafny doesn't support "extended real numbers"
 * or something similar so an algebraic datatype is used.
 *
 * Floyd-Warshall algorithm let edge costs be negative, then using negative
 * numbers as infinity is not a choice.
 *
 * A real implementation could use floating point arithmetic according to the
 * IEEE 754 standard which provides special values for infinities.
 */

// Extended real numbers with (positive) infinity
datatype xreal = Real(value : real) | Infty

// Type synonym for a graph (a nxn matrix of xreals)
type xgraph = array2<xreal>

// Less or equal on xreals
predicate method Leq(x : xreal, y : xreal)
{
	match y
	{
		case Infty => true

		case Real(yv) => match x
			{
				case Infty => false

				case Real(xv) => xv <= yv
			}
	}
}

function method Add(x : xreal, y : xreal) : xreal
{
	if x.Infty? || y.Infty?
	then Infty
	else Real(x.value + y.value)
}


/**
 * Path formalization.
 *
 *
 * The key definition is "path". Paths are represented as sequences of vertex
 * indices (non negative integers) and intermediate nodes cannot appear twice
 * (while ends may agree).
 *
 * Due to way the Floyd-Warshall algorithm works, a upper bound for
 * intermediate vertices has has been added to the definition.
 */

predicate Walk(w : seq<int>, bound : nat)
{
	// At least two vertices (an edge)
	|w| >= 2
	&&
	// Intermediate nodes are valid and not higher than bound
	forall i | 0 < i < |w|-1 :: 0 <= w[i] < bound
}

predicate WalkIn(w : seq<int>, bound : nat, edges : xgraph)
	reads edges
	requires ValidGraph(edges)
{
	bound <= Size(edges)
	&&
	Walk(w, bound)
	&&
	0 <= Start(w) < Size(edges)
	&&
	0 <= End(w) < Size(edges)
}


predicate AnyPath(s : seq<int>, bound : nat)
{
	// It is a walk
	Walk(s, bound)
	&&
	// And it doesn't contain inner loops
	forall i, j | 0 <= i < |s| && 0 < j < |s|-1 ::
		i != j ==> s[i] != s[j]
}

function Start(w : seq<int>) : int
	requires w != []
{
	w[0]
}

function End(w : seq<int>) : int
	requires w != []
{
	w[|w|-1]
}

predicate Path(s : seq<int>, from : nat, to : nat, bound : nat)
{
	AnyPath(s, bound) && Start(s) == from && End(s) == to
}

function Size(graph : xgraph) : nat
	reads graph
	requires graph != null
{
	graph.Length0
}


// The cost of travel thought a path
// (it does not require that the path is actually a path)
function Cost(s : seq<int>, edges : xgraph) : xreal
	reads edges
	requires edges != null
	requires edges.Length0 == edges.Length1

	requires forall i | 0 <= i < |s| :: 0 <= s[i] < Size(edges)
{
	if |s| < 2 then Real(0.0) else Add(edges[s[0], s[1]],
		Cost(s[1..], edges))
}

/*
 * Graph are represented as square matrices of costs (xreal
 * numbers) with no negative cycles.
 */
predicate ValidGraph(edges : xgraph)
	reads edges
{
	edges != null
	&&
	edges.Length0 == edges.Length1
	&&
	(forall node | 0 <= node < Size(edges) ::
		edges[node, node] == Real(0.0))
	&&
	// No negative cycles
	(forall path, bound : nat |
		AnyPath(path, bound)
		&&
		bound <= Size(edges)
		&&
		Start(path) == End(path)
		&&
		0 <= Start(path) < Size(edges)
	::
		Leq(Real(0.0), Cost(path, edges))
	)
}

/*
 * 'cost' is the minimum cost of any path in 'graph' from 'from' to 'to'
 * using nodes whose index is lower than 'bound'
 */
predicate MinCost(from : nat, to : nat, graph : xgraph,
		bound : nat, cost : xreal)

	reads graph
	requires ValidGraph(graph)

	requires bound <= Size(graph)
	requires from < Size(graph) && to < Size(graph)
{
	(forall path | Path(path, from, to, bound) ::
		Leq(cost, Cost(path, graph)))
	&&
	exists path | Path(path, from, to, bound) :: cost == Cost(path, graph)
}


method Floyd(edges : xgraph) returns (dist : xgraph)
	requires ValidGraph(edges)

	requires Size(edges) > 0

	ensures dist != null
	ensures dist.Length0 == Size(edges)
	ensures dist.Length1 == Size(edges)

	ensures forall i, j | 0 <= i < edges.Length0 && 0 <= j < edges.Length0 ::
		MinCost(i, j, edges, edges.Length0, dist[i, j])
{

	// Initialization
	var n := edges.Length0;

	dist := new xreal[n, n];

	var i : nat, j : nat, k : nat;

	j := 0;

	while j < n
		invariant 0 <= j <= n

		invariant forall r, s | 0 <= r < n && 0 <= s < j ::
			dist[r, s] == edges[r, s]
	{
		i := 0;

		while i < n
			invariant 0 <= i <= n
			invariant 0 <= j <= n

			invariant forall r, s | 0 <= r < n && 0 <= s < j ::
				dist[r, s] == edges[r, s]

			invariant forall r | 0 <= r < i ::
				dist[r, j] == edges[r, j]
		{
			dist[i, j] := edges[i, j];

			i := i + 1;
		}

		j := j + 1;
	}

	// The algorithm itself: iterative refinement of upper bounds

	k := 0;

	// Lemma to prove that initial values are correct
	Initialization(edges);

	while k < n
		invariant 0 <= k <= n

		invariant forall r, s | 0 <= r < n && 0 <= s < n ::
			MinCost(r, s, edges, k, dist[r, s])
	{
		j := 0;

		while j < n
			invariant 0 <= j <= n

			// Preserve
			invariant forall r, s | 0 <= r < n && j <= s < n ::
				MinCost(r, s, edges, k, dist[r, s])

			// Advance
			invariant forall r, s | 0 <= r < n && 0 <= s < j ::
				MinCost(r, s, edges, k+1, dist[r, s])
		{
			i := 0;

			while i < n
				invariant 0 <= j < n
				invariant 0 <= i <= n

				// Preserve
				invariant forall r, s | 0 <= r < n && j+1 <= s < n ::
					MinCost(r, s, edges, k, dist[r, s])

				invariant forall r | i <= r < n ::
					MinCost(r, j, edges, k, dist[r, j])

				invariant forall r, s | 0 <= r < n && 0 <= s < j ::
					MinCost(r, s, edges, k+1, dist[r, s])

				// Advance
				invariant forall r | 0 <= r < i ::
					MinCost(r, j, edges, k+1, dist[r, j])

			{
				/*
				 * dist contains at the same time minimum costs
				 * with bound k and k+1. Still and all, where k
				 * is an end those minimums coincide.
				 */

				MinPathBound(i, k, j, edges);

				assert MinCost(i, k, edges, k, dist[i, k]);
				assert MinCost(k, j, edges, k, dist[k, j]);
				assert MinCost(i, j, edges, k, dist[i, j]);


				var through_k := Add(dist[i, k], dist[k, j]);

				// It worth taking the path through k
				if !Leq(dist[i, j], through_k)
				{
					UpdateBetter(i, k, j, dist[i, k], dist[k, j],
						dist[i, j], edges);

					dist[i, j] := through_k;
				}
				else {
					UpdateSame(i, k, j, dist[i, k], dist[k, j],
						dist[i, j], edges);
				}

				assert MinCost(i, j, edges, k+1, dist[i, j]);

				// (!!) The following seems to be unavoidable. Why?

				assert forall r | r == i :: dist[i, j] == dist[r, j];

				i := i + 1;
			}

			j := j + 1;
		}

		k := k + 1;
	}
}



/*
 * Auxiliary lemmas
 */

lemma Initialization(edges : xgraph)
	requires ValidGraph(edges)

	ensures forall i, j | 0 <= i < edges.Length0 && 0 <= j < edges.Length0 ::
		MinCost(i, j, edges, 0, edges[i, j])
{
	// In this case is not even necessary to invoke the absence
	// of negative cycles

	forall i, j | 0 <= i < edges.Length0 && 0 <= j < edges.Length0
		ensures MinCost(i, j, edges, 0, edges[i, j])
	{
		// There is a path whose cost is edges[i, j]

		var thePath := [i, j];

		assert Path(thePath, i, j, 0);
		assert Cost(thePath, edges) == edges[i, j];


		// And is the only one

		forall path | Path(path, i, j, 0)
			ensures path == thePath
		{
			if |path| > 2 {
				var med := path[1];

				assert 0 <= path[1] < 0;
			}
		}
	}
}


/*
 * A stretch of a path is a path itself.
 */
lemma PathSplitArePath(path : seq<int>, start : nat, end : nat,
	i : nat, bound : nat)

	requires Path(path, start, end, bound)

	requires 0 < i < |path|-1

	ensures Path(path[..i+1], start, path[i], bound)
	ensures Path(path[i..], path[i], end, bound)
{

}

/*
 * The total cost of a path can be summed by sections.
 *
 * We don't really require that 'path' is a path, taking
 * advantage of the lack of this restriction in PathCost.
 */
lemma PathSplitCost(path : seq<int>, i : nat, edges : xgraph)
	requires ValidGraph(edges)
	requires 0 <= i < |path|

	requires forall k | 0 <= k < |path| :: 0 <= path[k] < edges.Length0

	ensures Add(Cost(path[..i+1], edges), Cost(path[i..], edges))
		== Cost(path, edges)

	decreases i
{
	if i == 0 {
		// Base case
		return;
	}
	else if i == |path|-1
	{
		assert path[..i+1] == path;
		assert Cost(path[i..], edges) == Real(0.0);

		return;
	}

	calc {
		Cost(path, edges);

		Add(edges[path[0], path[1]], Cost(path[1..], edges));
		{ PathSplitCost(path[1..], i-1, edges); }

		Add(edges[path[0], path[1]], Add(Cost(path[1..][..i], edges),
			Cost(path[1..][i-1..], edges)));
		{
			assert path[1..][i-1..] == path[i..];
			assert path[1..][..i] == path[1..i+1];
		}
		Add(edges[path[0], path[1]], Add(Cost(path[1..i+1], edges),
			Cost(path[i..], edges)));

		Add(Add(edges[path[0], path[1]], Cost(path[1..i+1], edges)),
			Cost(path[i..], edges));

		Add(Add(edges[path[0], path[1]], Cost(path[..i+1][1..], edges)),
			Cost(path[i..], edges));

		Add(Cost(path[..i+1], edges), Cost(path[i..], edges));
	}

}

/*
 * The sum of the two previous lemmas.
 */
lemma PathSplit(path : seq<int>, start : nat, end : nat,
	i : nat, bound : nat, edges : xgraph)

	requires ValidGraph(edges)
	requires Path(path, start, end, bound)

	requires 0 < i < |path|-1
	requires bound <= edges.Length0
	requires start < edges.Length0
	requires end < edges.Length0

	ensures Path(path[..i+1], start, path[i], bound)
	ensures Path(path[i..], path[i], end, bound)

	ensures Add(Cost(path[..i+1], edges), Cost(path[i..], edges))
		== Cost(path, edges)
{
	PathSplitArePath(path, start, end, i, bound);
	PathSplitCost(path, i, edges);
}

/*
 * A concatenation of two path is a path under certain conditions:
 *  1. Ends where they join match.
 *  2. Both are optimal paths.
 *  3. The optimal cost between the start and end (avoiding the contact
 *     vertex) exceeds the sum of the costs of the two paths.
 *
 * A easy handwritten proof can be done by reductio ad absurdum, finding
 * a path which, avoiding k, has a cost lower than cij, against (3).
 * However, a "easier" proof has been applied instead.
 */

lemma WalkLoop(walk : seq<int>, edges : xgraph, k : nat, r : nat, s : nat,
	loop : seq<int>, cutoff : seq<int>)

	requires ValidGraph(edges)
	requires WalkIn(walk, k, edges)

	// There are two stops in the walk that
	// share the same vertex
	requires s < |walk|
	requires r < s
	requires !(r == 0 && s == |walk|-1)

	requires walk[r] == walk[s]

	requires loop == walk[r..s+1]
	requires cutoff == walk[..r] + walk[s..]

	ensures Cost(walk, edges) == Add(Cost(loop, edges), Cost(cutoff, edges))
{
	/*
	 * A tedious calculation.
	 * Dafny alone can deal with the two first postconditions.
	 */
	calc {
		Cost(walk, edges);

		// First split
		{ PathSplitCost(walk, r, edges); }
		Add(Cost(walk[..r+1], edges), Cost(walk[r..], edges));

		// Second split, we have 3 sections
		{ PathSplitCost(walk[r..], s-r, edges); }
		Add(Cost(walk[..r+1], edges), Add(Cost(walk[r..][..s-r+1], edges),
			Cost(walk[r..][s-r..], edges)));

		// Slice simplification and loop == walk[r..s+1]
		{
			assert walk[r..][..s-r+1] == walk[r..s+1];
			assert walk[r..][s-r..] == walk[s..];
		}
		Add(Cost(walk[..r+1], edges), Add(Cost(loop, edges),
			Cost(walk[s..], edges)));

		// Add is associative and commutative
		Add(Cost(loop, edges), Add(Cost(walk[..r+1], edges),
			Cost(walk[s..], edges)));

		// That's cutoff
		{
			// Reduces verification time a lot (~4s)
			assert walk[r] == walk[s];

			assert cutoff[..r+1] == walk[..r+1];
			assert cutoff[r..] == walk[s..];

			PathSplitCost(cutoff, r, edges);
		}
		Add(Cost(loop, edges), Cost(cutoff, edges));
	}

}

/*
 * Given a walk between two vertices there is a path between those vertices
 * whose cost is lower than that of the walk.
 */
lemma WalkReduce(walk : seq<int>, k : nat, edges : xgraph)
	requires ValidGraph(edges)

	requires WalkIn(walk, k, edges)

	ensures exists path :: Path(path, Start(walk), End(walk), k)
		&& Leq(Cost(path, edges), Cost(walk, edges))

	decreases |walk|
{
	// If walk is a path there is nothing to do
	if AnyPath(walk, k) {
		assert Path(walk, Start(walk), End(walk), k);

		return;
	}

	// When walk is not a path...

	var r, s :| 0 <= r < |walk| && 0 < s < |walk|-1 && r != s &&
		walk[r] == walk[s];

	// Without loss of generality, suppose r < s 
	if s < r { r, s := s, r; }

	// There is at least a loop. Lets remove it.

	// At least one of {r, s} is an inner index
	assert 0 < s < |walk|-1 || 0 < r < |walk|-1;

	// Breaks the walk
	var loop := walk[r..s+1];
	var cutoff := walk[..r] + walk[s..];

	assert Start(loop) == End(loop);
	assert WalkIn(loop, k, edges);

	assert Start(walk) == Start(cutoff);

	var cutoff_cost := Cost(cutoff, edges);
	//var loop_cost := Cost(loop, edges);
	var walk_cost := Cost(walk, edges);

	WalkLoop(walk, edges, k, r, s, loop, cutoff);

	// Loop has non negative cost so Cost(cutoff) <= Cost(walk)
	LoopCosts(loop, k, edges);

	assert Leq(cutoff_cost, walk_cost);

	// Induction (as cutoff is strictly smaller)
	WalkReduce(cutoff, k, edges);

	var path :| Path(path, Start(cutoff), End(cutoff), k)
		&& Leq(Cost(path, edges), cutoff_cost);

	assert End(walk) == End(cutoff);
	assert Start(walk) == Start(cutoff);
}


/*
 * The minimum cost of a path which starts or ends in k using 0..k vertices
 * coincides with that of a path whose vertices are vertices in 0..k-1.
 * (because k cannot appear as an intermediate vertex).
 */
lemma MinPathBound(i : nat, k : nat, j : nat, edges : xgraph)
	requires ValidGraph(edges)

	requires i < edges.Length0
	requires j < edges.Length0
	requires k < edges.Length0

	ensures forall cik :: MinCost(i, k, edges, k+1, cik) ==>
		MinCost(i, k, edges, k, cik)
	ensures forall ckj :: MinCost(k, j, edges, k+1, ckj) ==>
		MinCost(k, j, edges, k, ckj)
{
}


/*
 * Two lemmas to help proving that the update (or the lack of it) in the
 * innermost loop is correct.
 */

lemma UpdateBetter(i : nat, k : nat, j : nat, cik : xreal,
	ckj : xreal, cij : xreal, edges : xgraph)

	requires ValidGraph(edges)

	requires i < edges.Length0
	requires j < edges.Length0
	requires k < edges.Length0

	requires MinCost(i, k, edges, k, cik)
	requires MinCost(k, j, edges, k, ckj)
	requires MinCost(i, j, edges, k, cij)

	requires !Leq(cij, Add(cik, ckj))

	ensures MinCost(i, j, edges, k+1, Add(cik, ckj))
{
	// The cost of any path is higher or equal to cik + ckj

	forall path | Path(path, i, j, k+1)
		ensures Leq(Add(cik, ckj), Cost(path, edges))
	{
		MinPathBound(i, k, j, edges);

		if Path(path, i, j, k)
		{
			// Definition of cij and cik + ckj < cij

			assert Leq(cij, Cost(path, edges));
		}
		else {
			// Due to MinPathBound (otherwise Path(path, i, j, k))
			assert i != k && j != k;

			var ind : nat :| 0 < ind < |path|-1 && path[ind] == k;

			/*
			 * The split subpaths costs are higher than cik and ckj
			 * respectively and the total cost is the sum.
			 *
			 * So all paths bounded by k+1 have a cost bounded by
			 * cik + ckj.
			 */
			PathSplit(path, i, j, ind, k+1, edges);
		}
	}

	// There is a path whose cost is cik + ckj

	var pik : seq<int> :| Path(pik, i, k, k) && Cost(pik, edges) == cik;
	var pkj : seq<int> :| Path(pkj, k, j, k) && Cost(pkj, edges) == ckj;

	var wij := pik + pkj[1..];

	WalkReduce(wij, k+1, edges);

	var pij :| Path(pij, i, j, k+1) && Leq(Cost(pij, edges), Cost(wij, edges));

	PathSplitCost(wij, |pik|-1, edges);

//	assert Cost(wij, edges) == Add(cik, ckj);
//	assert Cost(pij, edges) == Add(cik, ckj);
}

lemma UpdateSame(i : nat, k : nat, j : nat, cik : xreal,
	ckj : xreal, cij : xreal, edges : xgraph)

	requires ValidGraph(edges)

	requires i < edges.Length0
	requires j < edges.Length0
	requires k < edges.Length0

	requires MinCost(i, k, edges, k, cik)
	requires MinCost(k, j, edges, k, ckj)
	requires MinCost(i, j, edges, k, cij)

	requires Leq(cij, Add(cik, ckj))

	ensures MinCost(i, j, edges, k+1, cij)
{
	// The cost of any path is higher or equal to cij

	forall path | Path(path, i, j, k+1)
		ensures Leq(cij, Cost(path, edges))
	{
		MinPathBound(i, k, j, edges);

		if Path(path, i, j, k)
		{
			// Definition of 'cij'
			assert Leq(cij, Cost(path, edges));
		}
		else {
			// Due to MinPathBound (otherwise Path(path, i, j, k))
			assert i != k && j != k;

			var ind : nat :| 0 < ind < |path|-1 && path[ind] == k;

			/*
			 * The splitted subpathes costs are higher than cik and ckj
			 * respectively and the total cost is the sum, in the other
			 * hand cij <= cik + ckj.
			 *
			 * So all paths bounded by k+1 have a cost bounded by cij.
			 */
			PathSplit(path, i, j, ind, k+1, edges);
		}
	}
}

// The minimum path cost is also the minimum walk cost
// between two given nodes
lemma MinWalkCost(walk : seq<int>, bound : nat, cost : xreal, edges : xgraph)
	requires ValidGraph(edges)
	requires WalkIn(walk, bound, edges)
	requires MinCost(Start(walk), End(walk), edges, bound, cost)

	ensures Leq(cost, Cost(walk, edges))

	decreases |walk|
{
	if AnyPath(walk, bound)
	{
		// Base case (true by definition of MinCost)
	}
	else
	{
		// If it's not a path, there are repeated nodes
		assert exists r, s | 0 <= r < |walk| && 0 < s < |walk|-1 ::
			r != s && walk[r] == walk[s];

		var r, s :| 0 <= r < |walk| && 0 < s < |walk|-1 && r != s && walk[r] == walk[s];

		// Suppose r <= s without loss of generality
		if s < r
		{
			r, s := s, r;
		}

		// Any of them is an inner index
		assert 0 < r < |walk|-1 || 0 < s < |walk|-1;

		// Split the path in a loop and the rest
		var loop := walk[r..s+1];
		var cutoff := walk[..r] + walk[s..];

		WalkLoop(walk, edges, bound, r, s, loop, cutoff);

		assert Walk(loop, bound);

		// Induction using min cost for a loop is 0
		StaticCost(Start(loop), bound, edges);

		MinWalkCost(loop, bound, Real(0.0), edges);

		// Then Cost(walk) = Cost(loop) + Cost(cutoff)
		// >= Cost(cutoff)

		// Induction again cost <= Cost(cutoff) <= Cost(walk)

		assert Walk(cutoff, bound);
		assert Start(cutoff) == Start(walk);
		assert End(cutoff) == End(walk);

		MinWalkCost(cutoff, bound, cost, edges);
	}
}

// The minimum cost from a vertex to itself is 0
lemma StaticCost(i : nat, bound : nat, edges : xgraph)
	requires ValidGraph(edges)

	requires bound <= Size(edges)

	requires i < Size(edges)

	ensures MinCost(i, i, edges, bound, Real(0.0))
{
	var zeropath := [i, i];

	assert Cost(zeropath, edges) == Real(0.0);
}

// Loops have non negative cost even if they aren't paths
lemma LoopCosts(loop : seq<int>, bound : nat, edges : xgraph)
	requires ValidGraph(edges)
	requires WalkIn(loop, bound, edges)
	requires Start(loop) == End(loop)

	ensures Leq(Real(0.0), Cost(loop, edges))
{
	StaticCost(Start(loop), bound, edges);

	MinWalkCost(loop, bound, Real(0.0), edges);
}
