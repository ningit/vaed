/**
 * Floyd-Warshall algorithm (1959)
 *
 * Minimum path cost in a negative cycle free directed graph.
 *
 * The absence of negative cycles is set as a precondition.
 * However it can be modified to detect the presence of
 * negative cycles.
 *
 */

include "floydBase.dfy"
include "floydLemma.dfy"

/**
 * Method for copying matrices.
 */
method copyMatrix<T>(m : array2<T>) returns (mcopy : array2<T>)
	requires m != null

	ensures mcopy != null
	ensures fresh(mcopy)

	ensures mcopy.Length0 == m.Length0
	ensures mcopy.Length1 == m.Length1

	ensures forall i, j | 0 <= i < m.Length0 && 0 <= j < m.Length1 ::
		m[i, j] == mcopy[i, j]
{
	var n0, n1 := m.Length0, m.Length1;

	mcopy := new T[n0, n1]((i,j) requires 0 <= i < n0 && 0 <= j < n1 reads m => m[i, j]);
}

// Invariant for the loops of the Floyd algorithm
predicate DistInvariant(dist : xgraph, edges : xgraph, i : nat, j : nat, k : nat)
	reads dist, edges

	requires ValidGraph(edges)
	requires ValidDist(dist, edges)

	requires 0 <= i <= Size(edges)
	requires 0 <= j <= Size(edges)
	requires 0 <= k <= Size(edges)
{
	var n := Size(edges);

	forall r, s | 0 <= r < n && 0 <= s < n ::
		MinCost(dist[r, s], r, s, edges,
			if s < j || (s == j && r < i) then k+1 else k)
}

method Floyd(edges : xgraph) returns (dist : xgraph)
	requires ValidGraph(edges)
	requires Size(edges) > 0

	ensures ValidDist(dist, edges)
	ensures fresh(dist)

	ensures forall i, j | 0 <= i < Size(edges) && 0 <= j < Size(edges) ::
		MinCost(dist[i, j], i, j, edges, Size(edges))
{

	// Initialization
	var n := edges.Length0;

	dist := copyMatrix(edges);

	// The algorithm itself: iterative refinement of upper bounds

	var i : nat, j : nat, k : nat;

	k := 0;

	// Lemma to prove that initial values are correct
	forall r, s | 0 <= r < n && 0 <= s < n
	{
		Initialization(r, s, edges);
	}

	while k < n
		invariant 0 <= k <= n

		invariant DistInvariant(dist, edges, 0, 0, k)
	{
		j := 0;

		while j < n
			invariant 0 <= j <= n

			invariant DistInvariant(dist, edges, 0, j, k)
		{
			i := 0;

			while i < n
				invariant 0 <= i <= n

				invariant DistInvariant(dist, edges, i, j, k)
			{
				var through_k := Add(dist[i, k], dist[k, j]);

				// It worth taking the path through k
				if !Leq(dist[i, j], through_k)
				{
					Shortcut(edges, i, j, k, dist[i, j], dist[i, k], dist[k, j]);

					dist[i, j] := through_k;

				}
				// There is no executable code in this branch 
				else
				{
					NoShortcut(edges, i, j, k, dist[i, j], dist[i, k], dist[k, j]);
				}

				i := i + 1;
			}

			j := j + 1;
		}

		k := k + 1;
	}
}
