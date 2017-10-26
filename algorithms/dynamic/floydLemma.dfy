include "floydBase.dfy"

// Walk costs can be calculted by parts
lemma SplitCost(walk : seq<int>, k : nat, edges : xgraph)
	decreases k

	requires edges != null
	requires edges.Length0 == edges.Length1

	requires Walk(walk, edges)
	requires 0 <= k < |walk|

	ensures Cost(walk, edges) == Add(Cost(walk[..k+1], edges), Cost(walk[k..], edges))
{
	if k > 1
	{
		SplitCost(walk[1..], k-1, edges);

		assert walk[1..][..k] == walk[..k+1][1..];
		assert walk[1..][..k-1] == walk[..k][1..];
	}
}

/*
 * The following two lemmas say that for any walk bounded by k+1 and having k as one of its
 * ends, there exists a walk bounded by k with lower or equal cost.
 *
 * The third lemma then proves that the minimum cost in that case is
 * equivalent whether taken with bound k or k+1.
 */

lemma ReduceBoundStart(walk : seq<int>, edges : xgraph)
	requires ValidGraph(edges)
	requires Walk(walk, edges)
	requires Bounded(walk, Start(walk)+1)

	ensures exists walk' |
		Walk(walk', edges)
		&& Start(walk') == Start(walk) 
		&& End(walk') == End(walk)
	::
		Bounded(walk', Start(walk))
		&& Leq(Cost(walk', edges), Cost(walk, edges))
{
	var val := Start(walk);

	/* If there is not val vertices as intermediates ones,
	 * walk is our walk' (base case). Otherwise
 	 */
	if exists k | 0 < k < |walk|-1 :: walk[k] == val
	{
		var k :| 0 < k < |walk|-1 && walk[k] == val;

		// Removes the loop
		var reduced := walk[k..];

		// The loop cost is positive by the ValidGraph property
		SplitCost(walk, k, edges);
		assert Leq(Real(0.0), Cost(walk[..k+1], edges));
		assert Leq(Cost(reduced, edges), Cost(walk, edges));

		// Apply recursion
		ReduceBoundStart(reduced, edges);
	}
}

lemma ReduceBoundEnd(walk : seq<int>, edges : xgraph)
	requires ValidGraph(edges)
	requires Walk(walk, edges)
	requires Bounded(walk, End(walk)+1)
	//requires End(walk) > 0

	ensures exists walk' |
		Walk(walk', edges)
		&& Start(walk') == Start(walk) 
		&& End(walk') == End(walk)
	::
		Bounded(walk', End(walk))
		&& Leq(Cost(walk', edges), Cost(walk, edges))
{
	var val := End(walk);

	/* If there is not val vertices as intermediates ones,
	 * walk is our walk' (base case). Otherwise
 	 */
	if exists k | 0 < k < |walk|-1 :: walk[k] == val
	{
		var k :| 0 < k < |walk|-1 && walk[k] == val;

		// Removes the loop
		var reduced := walk[..k+1];

		// The loop cost is positive by the ValidGraph property
		SplitCost(walk, k, edges);
		assert Leq(Real(0.0), Cost(walk[..k+1], edges));
		assert Leq(Cost(reduced, edges), Cost(walk, edges));

		// Apply recursion
		assert Bounded(reduced, End(reduced)+1);
		ReduceBoundEnd(reduced, edges);
	}
}

lemma MinWalkBound(i : nat, k : nat, j : nat, cik : xreal, ckj : xreal, edges : xgraph)
	requires ValidGraph(edges)

	requires i < Size(edges)
	requires j < Size(edges)
	requires k < Size(edges)

	ensures MinCost(cik, i, k, edges, k)  ==> MinCost(cik, i, k, edges, k+1)
	ensures MinCost(ckj, k, j, edges, k) ==> MinCost(ckj, k, j, edges, k+1)
{
	// Reveals MinCost definition
	reveal_MinCost();

	if MinCost(cik, i, k, edges, k)
	{
		forall walk |
			Walk(walk, edges)
			&& Start(walk) == i
			&& End(walk) == k
			&& Bounded(walk, k+1)
		ensures
			Leq(cik, Cost(walk, edges))
		{
			ReduceBoundEnd(walk, edges);

			var walk' :| Walk(walk', edges) && Start(walk') == Start(walk) 
				&& End(walk') == End(walk) && Bounded(walk', k)
				&& Leq(Cost(walk', edges), Cost(walk, edges));

			assert Leq(cik, Cost(walk', edges));
		}
	}

	if MinCost(ckj, k, j, edges, k)
	{
		forall walk |
			Walk(walk, edges)
			&& Start(walk) == k
			&& End(walk) == j
			&& Bounded(walk, k+1)
		ensures
			Leq(ckj, Cost(walk, edges))
		{
			ReduceBoundStart(walk, edges);

			var walk' :| Walk(walk', edges) && Start(walk') == Start(walk) 
				&& End(walk') == End(walk) && Bounded(walk', k)
				&& Leq(Cost(walk', edges), Cost(walk, edges));

			assert Leq(ckj, Cost(walk', edges));
		}
	}
}

/*
 * Lemmas to be used within the Floyd algorithm code
 */

lemma Initialization(r : int, s : int, edges : xgraph)
	requires ValidGraph(edges)

	requires 0 <= r < Size(edges)
	requires 0 <= s < Size(edges)

	ensures MinCost(edges[r, s], r, s, edges, 0)
{
	// Reveals the definition of MinCost
	reveal_MinCost();

	// There exists a walk with such cost
	var edgew := [r, s];

	assert Walk(edgew, edges);
	assert Cost(edgew, edges) == edges[r, s];

	// In fact it is the only possible walk
	forall walk
		| Walk(walk, edges) && Start(walk) == r && End(walk) == s && Bounded(walk, 0)
		ensures Leq(edges[r, s], Cost(walk, edges))
	{
		assert |walk| == 2;

		assert walk == [r, s];
	}
}

lemma NoShortcut(edges : xgraph, i : nat, j : nat, k : nat, opt_ij : xreal, opt_ik : xreal, opt_kj : xreal)
	requires ValidGraph(edges)

	requires 0 <= i < Size(edges)
	requires 0 <= j < Size(edges)
	requires 0 <= k < Size(edges)

	requires MinCost(opt_ij, i, j, edges, k)
	requires MinCost(opt_ik, i, k, edges, k) || MinCost(opt_ik, i, k, edges, k+1)
	requires MinCost(opt_kj, k, j, edges, k) || MinCost(opt_kj, k, j, edges, k+1)

	requires Leq(opt_ij, Add(opt_ik, opt_kj))

	ensures MinCost(opt_ij, i, j, edges, k+1)
{
	// Reveals the definition of MinCost
	reveal_MinCost();

	forall walk | Walk(walk, edges)
		&& Start(walk) == i
		&& End(walk) == j
		&& Bounded(walk, k+1)

		ensures Leq(opt_ij, Cost(walk, edges))
	{
		// Suppose it is not bounded by k (otherwise we have it yet)

		if exists m | 0 < m < |walk|-1 :: walk[m] == k
		{
			var m :| 0 < m < |walk|-1 && walk[m] == k;

			var walk1 := walk[..m+1];
			var walk2 := walk[m..];

			SplitCost(walk, m, edges);
			assert Cost(walk, edges) == Add(Cost(walk1, edges), Cost(walk2, edges));

			MinWalkBound(i, k, j, opt_ik, opt_kj, edges);

			// We then apply the MinCost condition on opt_ik
			assert walk1[m] == k;
			assert Walk(walk1, edges) && Start(walk1) == i && End(walk1) == k && Bounded(walk1, k+1);

			assert Leq(opt_ik, Cost(walk1, edges));

			// And opt_kj
			assert walk2[0] == k;
			assert Walk(walk2, edges) && Start(walk2) == k && End(walk2) == j && Bounded(walk2, k+1);
			
			assert Leq(opt_kj, Cost(walk2, edges));

			// And then the the sum is monotonous
			assert Leq(Add(opt_ik, opt_kj), Cost(walk, edges));

			// And the verifier uses opt_ij <= opt_ik + opt_kj
		}
	}

	// (2) Existence of a walk with that cost

	// By the MinCost precondition on opt_ij
	assert exists walk | Walk(walk, edges) && Start(walk) == i && End(walk) == j && Bounded(walk, k) ::
		opt_ij == Cost(walk, edges);
}


lemma Shortcut(edges : xgraph, i : nat, j : nat, k : nat, opt_ij : xreal, opt_ik : xreal, opt_kj : xreal)
	requires ValidGraph(edges)

	requires 0 <= i < Size(edges)
	requires 0 <= j < Size(edges)
	requires 0 <= k < Size(edges)

	requires MinCost(opt_ij, i, j, edges, k)
	requires MinCost(opt_ik, i, k, edges, k) || MinCost(opt_ik, i, k, edges, k+1)
	requires MinCost(opt_kj, k, j, edges, k) || MinCost(opt_kj, k, j, edges, k+1)

	requires !Leq(opt_ij, Add(opt_ik, opt_kj))

	ensures MinCost(Add(opt_ik, opt_kj), i, j, edges, k+1)
{
	// Reveals the definition of MinCost
	reveal_MinCost();

	forall walk | Walk(walk, edges)
		&& Start(walk) == i
		&& End(walk) == j
		&& Bounded(walk, k+1)

		ensures Leq(Add(opt_ik, opt_kj), Cost(walk, edges))
	{
		// Suppose it is not bounded by k (otherwise we have it yet)

		if exists m | 0 < m < |walk|-1 :: walk[m] == k
		{
			var m :| 0 < m < |walk|-1 && walk[m] == k;

			var walk1 := walk[..m+1];
			var walk2 := walk[m..];

			SplitCost(walk, m, edges);
			assert Cost(walk, edges) == Add(Cost(walk1, edges), Cost(walk2, edges));

			MinWalkBound(i, k, j, opt_ik, opt_kj, edges);

			// We then apply the MinCost condition on opt_ik
			assert walk1[m] == k;
			assert Walk(walk1, edges) && Start(walk1) == i && End(walk1) == k && Bounded(walk1, k+1);

			assert Leq(opt_ik, Cost(walk1, edges));

			// And opt_kj
			assert walk2[0] == k;
			assert Walk(walk2, edges) && Start(walk2) == k && End(walk2) == j && Bounded(walk2, k+1);
			
			assert Leq(opt_kj, Cost(walk2, edges));

			// And then the the sum is monotonous
			assert Leq(Add(opt_ik, opt_kj), Cost(walk, edges));
		}
	}

	// (2) Existence of a walk with that cost

	// By the MinCost precondition on opt_ik and opt_kj
	var walk1 :| Walk(walk1, edges) && Start(walk1) == i && End(walk1) == k
		&& Bounded(walk1, k+1) && opt_ik == Cost(walk1, edges);
	var walk2 :| Walk(walk2, edges) && Start(walk2) == k && End(walk2) == j
		&& Bounded(walk2, k+1) && opt_kj == Cost(walk2, edges);

	var walk := walk1 + walk2[1..];

	assert Start(walk) == i;
	assert End(walk) == j;

	SplitCost(walk, |walk1|-1, edges);

	assert walk[..|walk1|] == walk1;
	assert walk[|walk1|-1..] == walk2;

	assert Cost(walk, edges) == Add(Cost(walk1, edges), Cost(walk2, edges));
}
