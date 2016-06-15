/**
 * Dijkstra algorithm (Edsger Dijkstra, 1959)
 */

/*
 * Abstract graph to allow easy implementation as an adjacency list.
 *
 * Count() provides the number of vertices and the Adjacents(nat)
 * function returns a map whose key are the neighbour vertices and
 * its value is the cost of the edge which connect them.
 */
trait Graph
{
	function method Count() : nat

	function method Adjacents(n : nat) : map<int, real>
		reads this
		requires 0 <= n < Count()

		ensures n !in Adjacents(n)

		ensures forall node | node in Adjacents(n) ::
			0 <= node < Count()
			&&
			Adjacents(n)[node] >= 0.0
}

/*
 * Improved priority queue.
 *
 * - Priorities can be updated.
 * - There are a key and a value.
 * - A map is used as its representation.
 */
class PrioQueue
{
	// Creates the empty queue
	constructor()
		ensures Elems == map[]
		modifies this

	// Is the queue empty?
	predicate method Empty()
		reads this
		ensures Empty() <==> Elems == map[]

	// Sets or update a queue value
	method Set(key : nat, value : real)
		ensures Elems == old(Elems)[key := value]
		modifies this

	// Gets the minimum entry in the queue
	method Pop() returns (key : nat, value : real)
		requires !Empty()

		ensures key in old(Elems)
		ensures value == old(Elems)[key]

		ensures forall k | k in old(Elems) :: old(Elems)[k] >= value

		// Removes the the element from the table of elements
		ensures Elems == map k | k in old(Elems) && k != key :: old(Elems)[k]
		modifies this

	// Abstract representation
	ghost var Elems : map<int, real>
}

predicate ValidGraph(graph : Graph)
	reads graph
{
	graph != null
	&&
	graph.Count() > 0
}

/*
 * A walk is a sequence of connected vertices represented by their indices.
 *
 * They must be non-empty. Singleton walks are allowed.
 */
predicate Walk(w : seq<int>, graph : Graph)
	reads graph
	requires ValidGraph(graph)
{
	// At least one element
	w != []
	&&
	// Walk vertices are in bounds
	(forall i | 0 <= i < |w| :: 0 <= w[i] < graph.Count())
	&&
	// The nodes are connected
	(forall i | 0 <= i < |w|-1 :: w[i+1] in graph.Adjacents(w[i]))
}

// It says: is w a walk from 0 to node within graph?
predicate WalkTo(node : nat, w : seq<int>, graph : Graph)
	reads graph

	requires ValidGraph(graph)
	requires 0 <= node < graph.Count()
{
	// A walk from 0 to node
	Walk(w, graph)
	&&
	w[0] == 0
	&&
	w[|w|-1] == node

}

// The cost of a walk is the sum of the cost of its composing edges
function WalkCost(w : seq<int>, graph : Graph) : real
	reads graph

	requires ValidGraph(graph)
	requires Walk(w, graph)
{
	if |w| == 1 then 0.0 else
		graph.Adjacents(w[|w|-2])[w[|w|-1]] + WalkCost(w[..|w|-1], graph)
}


/*
 * About distances.
 */

// It says: dist is the distance to node in graph.
predicate DistanceTo(dist : real, node : nat, graph : Graph)
	reads graph

	requires ValidGraph(graph)
	requires 0 <= node < graph.Count()
{
	// Its a lower bound of the cost of any path
	(forall walk | WalkTo(node, walk, graph) ::
		dist <= WalkCost(walk, graph))
	&&
	// And there is a path with this cost
	(exists walk :: WalkTo(node, walk, graph)
		&& WalkCost(walk, graph) == dist)
}


/*
 * Definitions to ensure the correction of the list of links to previous
 * nodes in the calculated path from the origin.
 *
 * The predicate is enunciated in two steps and it states that there is a
 * prev cell for each node, whose value could be -1 (if the node is not
 * connected with the origin, or not yet) or the index of the previous nodes
 * in an optimal path from the origin.
 *
 * Every non negative cell let return back to the origin and so reconstruct
 * a path from there.
 */

predicate ValidPrev(prev : seq<int>, graph : Graph)
	reads graph
	requires ValidGraph(graph)
{
	BasicValidPrev(prev, graph)
	&&
	forall i | 0 <= i < |prev| :: prev[i] >= 0 ==>
		BackToZero(i, prev, graph, graph.Count())
}

predicate BasicValidPrev(prev : seq<int>, graph : Graph)
	reads graph
	requires ValidGraph(graph)
{
	|prev| == graph.Count()
	&&
	prev[0] < 0
	&&
	(forall i | 1 <= i < |prev| :: prev[i] < 0 || (0 <= prev[i] < graph.Count()
		&& i in graph.Adjacents(prev[i])))
}

// It is possible to go back to zero in a bounded number of steps
predicate BackToZero(i : nat, prev : seq<int>, graph : Graph, steps : nat)
	reads graph

	requires ValidGraph(graph)
	requires BasicValidPrev(prev, graph)
	requires 0 <= i < graph.Count()

	decreases steps
{
	steps > 0 && (i == 0 || (prev[i] >= 0 && 
		BackToZero(prev[i], prev, graph, steps - 1)))
}

/*
 * Function methods to get the path from the origin based on prev.
 *
 * The auxiliary function includes an extra parameter
 * to prove termination.
 */

function method WalkFromPrev(i : nat, prev : seq<int>, graph : Graph) : seq<int>
	reads graph
	requires ValidGraph(graph)
	requires ValidPrev(prev, graph)
	requires 0 <= i < graph.Count()

	requires BackToZero(i, prev, graph, graph.Count())

	ensures WalkTo(i, WalkFromPrev(i, prev, graph), graph)
{
	WalkFromPrevAux(i, prev, graph, graph.Count())
}

function method WalkFromPrevAux(i : nat, prev : seq<int>,
	graph : Graph, ghost bound : nat) : seq<int>

	reads graph
	requires ValidGraph(graph)
	requires ValidPrev(prev, graph)
	requires 0 <= i < graph.Count()

	requires BackToZero(i, prev, graph, bound)

	ensures WalkTo(i, WalkFromPrevAux(i, prev, graph, bound), graph)

	decreases bound
{
	(if prev[i] >= 0
	then WalkFromPrevAux(prev[i], prev, graph, bound-1)
	else []) + [i]
}

/**
 * Computes the minimum path from the origin (numbered as 0) to the rest of
 * vertices.
 *
 * dist and prev will contain the distance from the origin and the previous
 * node in an optimal path from it for each node in the graph. When a node
 * is unconnected to the origin -1 will be written in both cells.
 */
method Dijkstra(graph : Graph) returns (dist : array<real>, prev : array<int>)
	requires ValidGraph(graph)

	ensures dist != null
	ensures dist.Length == graph.Count()

	ensures prev != null
	ensures ValidPrev(prev[..], graph)

	ensures forall id | 0 <= id < graph.Count() :: dist[id] >= 0.0
		==> DistanceTo(dist[id], id, graph)

	ensures forall id | 0 <= id < graph.Count() :: dist[id] >= 0.0
		==> dist[id] ==
			WalkCost(WalkFromPrev(id, prev[..], graph), graph)

	ensures forall id | 0 < id < graph.Count() :: dist[id] < 0.0
		==> !(exists walk :: WalkTo(id, walk, graph))
{
	var queue := new PrioQueue();
	var closed  := new bool[graph.Count()];

	dist := new real[graph.Count()];
	prev := new int[graph.Count()];

	// Initialization

	var i := 0;

	while i < graph.Count()
		invariant 0 <= i <= graph.Count()

		invariant forall j | 0 <= j < i :: dist[j] == -1.0
		invariant forall j | 0 <= j < i :: prev[j] == -1
		invariant forall j | 0 <= j < i :: !closed[j]

		invariant queue.Elems == map[]
	{
		dist[i]	:= -1.0;
		prev[i]	:= -1;
		closed[i] := false;

		i := i + 1;
	}

	queue.Set(0, 0.0);

	dist[0] := 0.0;

	ghost var npend := closed.Length;

	AllFalse(closed[..]);

	Initialization(graph);

	while !queue.Empty()

		invariant npend == CountFalses(closed[..])

		// About the final results

		// The distance is negative iff the node has not been visited yet
		invariant forall id | 0 < id < graph.Count() ::
			dist[id] < 0.0 <==> IsOutside(id, graph, closed[..])

		// Nodes which have been visited but are not yet closed, have the
		// nearest distance from the closed nodes assigned
		invariant forall id | 0 < id < graph.Count() :: dist[id] >= 0.0
			<==>  BestApproach(id, graph, closed[..], dist[..], prev[..])

		// For the closed nodes, the final distance is already calculated
		invariant forall id | 0 <= id < graph.Count() :: closed[id]
			==> DistanceTo(dist[id], id, graph)

		invariant 0 !in queue.Elems ==> closed[0]

		// Prev is valid
		invariant ValidPrev(prev[..], graph)

		// About the queue and its values

		invariant forall id | id in queue.Elems :: 0 <= id < graph.Count()

		invariant forall id | 0 <= id < graph.Count() ::
			dist[id] >= 0.0 && !closed[id] <==> id in queue.Elems

		invariant forall id | id in queue.Elems :: dist[id] == queue.Elems[id]

		invariant forall id, c | id in queue.Elems && 0 <= c < graph.Count()
			&& closed[c] :: dist[c] <= queue.Elems[id]

		decreases npend
	{
		// Keeps a copy of the old close
		ghost var closed0 := closed[..];

		// Gets the nearer node from the queue
		var nearer, nearcost := queue.Pop();

		// Closes the node
		closed[nearer] := true;

		npend := npend - 1;

		// Some proofs for the initialization of invariants

		CancelOne(closed0, nearer);

		var adjacents := set node | node in graph.Adjacents(nearer);

		StillOutside(nearer, graph , closed0, dist[..], adjacents);

		assert forall id | 0 < id < graph.Count() && id !in adjacents ::
			dist[id] < 0.0 <==> IsOutside(id, graph, closed[..]);

		assert nearer !in queue.Elems;

		// Checks every (not closed) adjacent node for a lower
		// distance to it

		while |adjacents| > 0
			invariant npend == CountFalses(closed[..]);

			// About the final results

			invariant forall id | 0 < id < graph.Count() && id !in adjacents ::
				dist[id] < 0.0 <==> IsOutside(id, graph, closed[..])

			invariant forall id | 0 < id < graph.Count() && id in adjacents ::
				dist[id] < 0.0 <==> IsOutside(id, graph, closed0)

			invariant forall id | 0 < id < graph.Count() && id !in adjacents ::
				dist[id] >= 0.0  <==> 
				BestApproach(id, graph, closed[..], dist[..], prev[..])

			invariant forall id | 0 < id < graph.Count() && id in adjacents ::
				dist[id] >= 0.0 <==>
				BestApproach(id, graph, closed0, dist[..], prev[..])

			invariant forall id | 0 <= id < graph.Count() :: closed[id]
				==> DistanceTo(dist[id], id, graph)

			invariant 0 !in queue.Elems ==> closed[0]

			invariant ValidPrev(prev[..], graph)

			// About the queue and its values

			invariant forall id | id in queue.Elems :: 0 <= id < graph.Count()

			invariant forall id | 0 <= id < graph.Count() ::
				dist[id] >= 0.0 && !closed[id] <==> id in queue.Elems

			invariant forall id | id in queue.Elems :: dist[id] == queue.Elems[id]

			invariant forall id, c | id in queue.Elems && 0 <= c < graph.Count() &&
				closed[c] :: dist[c] <= queue.Elems[id]

			decreases |adjacents|
		{
			var next :| next in adjacents;

			var cost := graph.Adjacents(nearer)[next];

			if !closed[next] && dist[next] > nearcost + cost
			{
				// Updates the distance and antecedent

				dist[next] := nearcost + cost;
				prev[next] := nearer;

				queue.Set(next, dist[next]);
			}

			i := i + 1;

			adjacents := adjacents - {next};
		}
	}

	Unreachables(graph, closed[..], dist[..]);
}

/*
 * Functions for readability
 */

// The vertex 'id' is outside, i.e. it is not reachable from a
// closed node
predicate IsOutside(id : nat, graph : Graph, closed : seq<bool>)
	reads graph

	requires ValidGraph(graph)
	requires 0 < id < graph.Count()

	requires |closed| == graph.Count()
{
	forall c | 0 <= c < graph.Count() && closed[c] ::
		id !in graph.Adjacents(c)
}

/*
 * The distance we have assigned to a frontier node is the best possible from
 * the current closed nodes. This is also valid for closed nodes (except for 0).
 */
predicate BestApproach(id : nat, graph : Graph, closed : seq<bool>,
	dist : seq<real>, prev : seq<int>)

	reads graph

	requires ValidGraph(graph)
	requires 0 < id < graph.Count()

	requires |closed| == graph.Count()
	requires |dist| == graph.Count()
	requires |prev| == graph.Count()

	requires ValidPrev(prev, graph)
{
	// The previous exists and is closed
	prev[id] >= 0
	&&
	closed[prev[id]]
	&&
	// The distance is the best from the closed set
	dist[id] == dist[prev[id]] + graph.Adjacents(prev[id])[id]
	&&
	forall c | 0 <= c < graph.Count() && closed[c] && id in graph.Adjacents(c) ::
		dist[id] <= dist[c] + graph.Adjacents(c)[id]
}

/*
 * Auxiliary definitions to prove termination.
 */

function CountFalses(s : seq<bool>) : nat
{
	if s == [] then 0 else (if s[|s|-1] then 0 else 1) + CountFalses(s[..|s|-1])
}

// When all elements are false, the count gives the array length
lemma AllFalse(s : seq<bool>)
	requires forall i | 0 <= i < |s| :: !s[i]

	ensures CountFalses(s) == |s|
{
}

lemma CancelOne(s : seq<bool>, k : nat)
	requires 0 <= k < |s|
	requires !s[k]

	ensures CountFalses(s[k := true]) == CountFalses(s) - 1
{
}

/*
 * Lemmas
 */

// Any walk has have positive costs
lemma AllWalkPositive(walk : seq<int>, graph : Graph)
	requires ValidGraph(graph)
	requires Walk(walk, graph)

	ensures WalkCost(walk, graph) >= 0.0
{
}

// Lemma to prove the invariants at the start of the loop
lemma Initialization(graph : Graph)
	requires ValidGraph(graph)

	ensures DistanceTo(0.0, 0, graph)
{
	var zeropath := [0];

	assert WalkTo(0, zeropath, graph);

	assert WalkCost(zeropath, graph) == 0.0;

	forall walk | WalkTo(0, walk, graph)
		ensures 0.0 <= WalkCost(walk, graph)
	{
		AllWalkPositive(walk, graph);
	}
}

/*
 * If we close a vertex, the outside vertices which are not adjacent to it
 * remains outside.
 */
lemma StillOutside(newcl : nat, graph : Graph, closed : seq<bool>,
	dist : seq<real>, adjacents : set<int>)

	// The preconditions of routine
	requires ValidGraph(graph)
	requires |closed| == graph.Count()
	requires |dist| == graph.Count()
	requires 0 <= newcl < graph.Count()

	// Adjacents to the recently closed nodes
	requires adjacents == set node | node in graph.Adjacents(newcl)

	// The invariant of the main method loop we wanted to preserve
	requires forall id | 0 < id < graph.Count() ::
		dist[id] < 0.0 <==> IsOutside(id, graph, closed)

	ensures forall id | 0 < id < graph.Count() && id !in adjacents ::
		dist[id] < 0.0 <==> IsOutside(id, graph, closed[newcl := true])
{

}

/*
 * When we get the a vertex from the queue, its distance is definitive.
 */
lemma IsTheDistance(id : nat, graph : Graph, closed : seq<bool>,
	dist : seq<real>, prev : seq<int>)

	// The preconditions of routine
	requires ValidGraph(graph)
	requires |closed| == graph.Count()
	requires |dist| == graph.Count()
	requires 0 < id < graph.Count()

	// Prev is valid and id is in the frontier
	requires ValidPrev(prev, graph)

	requires forall id | 0 < id < graph.Count() ::
		(exists c | 0 <= c < graph.Count() :: id in graph.Adjacents(c))
		==> dist[id] >= 0.0

	requires forall i | 0 < i < graph.Count() && dist[i] >= 0.0 :: 
		BestApproach(i, graph, closed, dist, prev)

	requires BestApproach(id, graph, closed, dist, prev)

	requires closed[0]

	// For the closed nodes, the final distance is already calculated
	requires forall id | 0 <= id < graph.Count() :: closed[id]
		==> DistanceTo(dist[id], id, graph)

	// The property that comes from the min-heap 
	// requires forall c | 0 <= c < graph.Count() && closed[c] ::
	//	dist[c] <= dist[id]

	// Consequence of the min-heap extraction
	requires forall jd | 0 <= jd < graph.Count() && !closed[jd] &&
		dist[jd] >= 0.0 :: dist[id] <= dist[jd]

	ensures DistanceTo(dist[id], id, graph)
{
	// The previous node is closed
	assert closed[prev[id]];

	// So its distance is final
	assert DistanceTo(dist[prev[id]], prev[id], graph);

	// (1) We try to prove that there is a walk with dist[id] cost
	// using the optimum walk to prev[id]

	assert exists walk :: WalkTo(prev[id], walk, graph)
		&& WalkCost(walk, graph) == dist[prev[id]];

	var walk :| WalkTo(prev[id], walk, graph)
		&& WalkCost(walk, graph) == dist[prev[id]];

	var walk' := walk + [id];

	assert WalkTo(id, walk', graph);

	// (2) We try to prove that every other walk has higher cost

	forall walk | WalkTo(id, walk, graph)
		ensures dist[id] <= WalkCost(walk, graph)
	{
		// As id != 0, |walk| >= 2
		assert |walk| >= 2;

		// Let's consider some cases depending on the antecedent in the walk
		var pr := walk[|walk|-2];

		/*
		 * The idea is that a path cost is higher than dist[j] for sure
		 * only if j is closed. There is at least a closed node (0) in
		 * the path.
		 */

		if closed[pr]
		{
			/*
			 * The key elements are:
			 * - dist[id] = dist[pr] + edge(pr, id)
			 * - dist[pr] <= WalkCost(walk[..|walk|-1], graph)
			 */

			assert dist[id] <= WalkCost(walk, graph);
		}
		else if |walk| > 2
		{
			var i := |walk| - 2;

			// We find the last closed node in the walk
			while !closed[walk[i]]
				invariant 0 <= i < |walk|
				invariant forall j | i+1 <= j < |walk|-1 :: !closed[walk[j]]

				decreases i
			{
				i := i - 1;
			}

			assert closed[walk[i]];
			assert !closed[walk[i+1]];

			// As walk[i] is closed
			assert DistanceTo(dist[walk[i]], walk[i], graph);

			assert dist[walk[i]] <= WalkCost(walk[..i+1], graph);

			assert dist[walk[i+1]] >= 0.0;

			assert BestApproach(walk[i+1], graph, closed, dist, prev);

			calc <= {
				dist[id];
				dist[walk[i+1]];
				WalkCost(walk[..i+2], graph);
				{ SubWalkCost(walk, graph, i+2); }
				WalkCost(walk, graph);
			}
		}
	}
}

lemma SubWalkCost(walk : seq<int>, graph : Graph, i : nat)
	requires ValidGraph(graph)
	requires Walk(walk, graph)
	requires 0 < i < |walk|

	ensures WalkCost(walk[..i], graph) <= WalkCost(walk, graph)

	decreases |walk| - i
{
	if i < |walk|-1
	{
		calc <= {
			WalkCost(walk[..i], graph);
			// We add a positive number
			WalkCost(walk[..i], graph) + graph.Adjacents(walk[i-1])[walk[i]];
			{ assert walk[..i+1][..i] == walk[..i]; }
			WalkCost(walk[..i+1][..i], graph) + graph.Adjacents(walk[..i+1][i-1])[walk[..i+1][i]];
			WalkCost(walk[..i+1], graph);
			// Induction hypothesis
			{ SubWalkCost(walk, graph, i+1); }
			WalkCost(walk, graph);
		}
	}
}

/*
 * At the end, those nodes which have not been visited by the algorithm
 * are unreachable.
 */
lemma Unreachables(graph : Graph, closed : seq<bool>, dist : seq<real>)
	// The preconditions of routine
	requires ValidGraph(graph)
	requires |closed| == graph.Count()
	requires |dist| == graph.Count()

	requires forall id | 0 < id < graph.Count() ::
		dist[id] < 0.0 <==> IsOutside(id, graph, closed[..])

	requires forall id | 0 < id < graph.Count() ::
		dist[id] < 0.0 <==> !closed[id]

	requires closed[0]

	ensures forall id | 0 < id < graph.Count() && dist[id] < 0.0 ::
		!(exists walk :: WalkTo(id, walk, graph))
{
	forall id | 0 < id < graph.Count() && dist[id] < 0.0
		ensures !(exists walk :: WalkTo(id, walk, graph))
	{
		/*
		 * Reductio ad absurdum.
		 *
		 * Suppose there is a walk to id. As id is outside, no closed
		 * node connect to it. So its antecedent in the walk is not
		 * closed. If it is not closed, it is outside. And we iterate.
		 *
		 * Finally, we arrive to the conclusion that the origin is not
		 * closed, against the hypothesis.
		 */

		if exists walk :: WalkTo(id, walk, graph)
		{
			var walk :| WalkTo(id, walk, graph);

			if |walk| > 2
			{
				var i := |walk| - 1;

				while i > 1
					invariant 1 <= i < |walk|
					invariant !closed[walk[i]]
				{
					assert !closed[walk[i-1]];

					i := i - 1;
				}

				assert walk[1] in graph.Adjacents(0);
			}
		}
	}
}
