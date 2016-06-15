/**
 * Generic binary heap (with custom priority).
 */
predicate TotalPreorder<T>(R : (T, T) -> bool)
	reads R.reads
{
	   (forall x, y :: R.requires(x, y))
	// Transitive
	&& (forall x, y, z :: R(x, y) && R(y, z) ==> R(x, z))
	// Total
	&& (forall x, y :: R(x, y) || R(y, x))

	// Reflexive is included in total
}

class {:autocontracts} BinaryHeap<T(==)>
{
	// Greatest or equal priority comparator
	var gep : (T, T) -> bool;

	predicate GoodPredicate(g : (T, T) -> bool)
		reads g.reads
	{
		forall t, s :: this !in g.reads(t, s)
	}

	function Elements() : multiset<T>
		reads this, Repr, gep.reads

		requires Valid()
	{
		multiset(elems[..nelems])
	}

	// Total number of elements in the heap
	function Size() : nat
		reads this, Repr, gep.reads

		requires Valid()
		ensures Size() <= |Elements()|
	{
		nelems
	}

	// Increase the size of the full up internal array
	method Expand()
		requires nelems == elems.Length
		ensures nelems < elems.Length
		ensures Elements() == old(Elements())
	{
		var tmp := new T[2 * elems.Length + 1];

		// Range copy idiom
		forall i | 0 <= i < elems.Length
		{
			tmp[i] := elems[i];
		}

		// tmp is elems with doubled capacity
		assert tmp[..nelems] == elems[..nelems];

		elems := tmp;

	//	assume Valid();
	}

	// Retrives the least element of the priority queue
	method Pull() returns (x : T)
		requires Size() != 0

		ensures forall y | y in old(Elements()) :: gep(x, y)
		ensures Elements() == old(Elements()) - multiset{x}
	{
		// Returns the minimum

		RootIsMin();

		x := elems[0];

		// Removes the minimum

		nelems := nelems - 1;

		// Takes the last element and sinks it to get a new root

		elems[0] := elems[nelems];

		assert TotalPreorder(gep); // este es el punto exacto donde falla

		ghost var Elements0 := multiset(elems[..nelems]);

		var pos := 0;

		assert TotalPreorder(gep);

		while pos < (nelems - 1) / 2 &&
			(!gep(elems[pos], elems[2*pos+1]) || !gep(elems[pos], elems[2*pos+2]))

			invariant 0 <= pos <= nelems

			// Keeps validity
			invariant elems == old(elems)
			invariant Repr == old(Repr)
			invariant elems != null && nelems < elems.Length

			// All children are lower than their parents except pos'
			invariant forall i | 0 < i < nelems && Parent(i) != pos :: gep(elems[Parent(i)], elems[i])

			// But pos's children are lower than their grandparents
			invariant 0 < pos ==> forall chd : nat | 0 < chd < nelems ::
				Parent(chd) == pos ==> gep(elems[Parent(pos)], elems[chd])

			// Elements are only changed by permutations
			invariant Elements0 == multiset(elems[..nelems])

			decreases nelems - pos
		{
			// Choose the lowest child
			var chd := 2 * pos + 2;

			// The first condition is unnecessary but decreases ver. time
			if !gep(elems[pos], elems[2*pos+1]) && gep(elems[2*pos+1], elems[2*pos+2])
			{
				chd := 2*pos + 1;
			}

			elems[pos], elems[chd] := elems[chd], elems[pos];

			pos := chd;
		}

		// If we've arrived to a father with only one child (unique if exists)

		if pos == (nelems - 1) / 2 && nelems % 2 == 0 && !gep(elems[pos], elems[nelems - 1])
		{
			elems[pos], elems[nelems - 1] := elems[nelems -1], elems[pos];
		}
	}

	// Inserts an element to the priority queue
	method Insert(x : T)
		ensures Elements() == old(Elements()) + multiset{x}
	{
		if nelems == elems.Length
		{
			Expand();
		}

		ghost var elems0, Repr0 := elems, Repr;

		elems[nelems] := x;

		nelems := nelems + 1;

		// Floats the number

		var pos : nat := nelems - 1;

		ghost var Elements0 := multiset(elems[..nelems]);

		while pos > 0 && !gep(elems[(pos - 1) / 2], elems[pos])
			invariant 0 <= pos < nelems

			// Keeps validity
			invariant elems == elems0
			invariant Repr == Repr0
			invariant elems != null && nelems <= elems.Length

			// All children are lower than their parents except pos

			invariant forall i | 0 < i < nelems && i != pos :: gep(elems[Parent(i)], elems[i])

			// But pos's children are lower than their grandparent
			invariant 0 < pos ==> forall chd : nat | 0 < chd < nelems ::
				Parent(chd) == pos ==> gep(elems[Parent(pos)], elems[chd])

			// Elements are only changed by permutations
			invariant Elements0 == multiset(elems[..nelems])
		{
			var parent := (pos - 1) / 2;

			elems[parent], elems[pos] := elems[pos], elems[parent];

			pos := parent;
		}
	}

	constructor(gepc : (T, T) -> bool)
		requires GoodPredicate(gepc)
		requires TotalPreorder(gepc)

		ensures Elements() == multiset{}
	{
		elems := new T[31];
		nelems := 0;

		gep := gepc;
	}

	predicate Valid()
		reads gep.reads
	{
		// There is an array with enough capacity
		elems != null && nelems <= elems.Length
		&&
		// gep does not read the binary heap itself
		GoodPredicate(gep)
		&&
		// geq is a total preorder
		TotalPreorder(gep)
		&&
		// Parents have highest priority
		(forall i | 0 < i < nelems :: gep(elems[Parent(i)], elems[i]))
	}

	// The heap root holds the minimum
	lemma RootIsMin()
		ensures forall y | y in Elements() :: gep(elems[0], y)
	{
		// Easy proof with reductio ad absurdum

		if exists y | y in Elements() :: !gep(elems[0], y) {

			// Elements are vector entries
			assert exists pos : nat | pos < nelems :: !gep(elems[0], elems[pos]);

			var pos : nat :| pos < nelems && !gep(elems[0], elems[pos]);

			while pos > 0
				invariant 0 <= pos < nelems

				invariant !gep(elems[0], elems[pos])
			{
				// Uses elems[parent] <= elems[pos]

				var parent := (pos - 1) / 2;

				assert parent == Parent(pos);

				pos := parent;
			}

			assert !gep(elems[0], elems[0]);
		}
	}

	// Index of the parent node
	function Parent(n : nat) : nat
		requires n != 0
	{
		(n - 1) / 2
	}

	// Elements
	var elems	: array<T>;

	// Elements count
	var nelems	: nat;
}
