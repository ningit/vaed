/**
 * A special cost value (infinity) is used to point out that there is no
 * connection between two nodes.
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

/*
 * Functions for walks
 */

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

function Size(graph : xgraph) : nat
	reads graph

	requires graph != null
{
	graph.Length0
}

predicate Walk(walk : seq<int>, edges : xgraph)
	reads edges

	requires edges != null
{
	|walk| >= 2
	&&
	forall i | 0 <= i < |walk| :: 0 <= walk[i] < Size(edges)
}

predicate Bounded(walk : seq<int>, bound : nat)
{
	forall i | 0 < i < |walk|-1 :: walk[i] < bound
}

// The cost of travelling thought a walk
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
	// No walk with negative cost
	(forall walk : seq<int> |
		Walk(walk, edges)
	::
		Leq(Real(0.0), Cost(walk, edges))
	)
}

/**
 * The distances matrix has the same shape as the graph matrix.
 */
predicate ValidDist(dist : xgraph, edges : xgraph)
	reads dist, edges

	requires edges != null
{
	dist != null
	&&
	dist.Length0 == Size(edges)
	&&
	dist.Length1 == Size(edges)
}

/*
 * 'cost' is the minimum cost of any path in 'graph' from 'from' to 'to'
 * using nodes whose index is lower than 'bound'
 */
predicate {:opaque} MinCost(cost : xreal, from : nat, to : nat, graph : xgraph,
		bound : nat)

	reads graph

	requires ValidGraph(graph)
	requires from	 < Size(graph)
	requires to	 < Size(graph)
{
	(forall walk |
		Walk(walk, graph)
		&& Start(walk) == from
		&& End(walk) == to
		&& Bounded(walk, bound)
	::
		Leq(cost, Cost(walk, graph))
	)
	&&
	(exists walk |
		Walk(walk, graph)
		&& Start(walk) == from
		&& End(walk) == to
		&& Bounded(walk, bound)
	::
		cost == Cost(walk, graph)
	)
}
