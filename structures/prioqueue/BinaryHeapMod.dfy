/**
 * Generic binary heap (with custom priority).
 *
 * This code produce internal Boogie errors (related to triggers)
 * in 1.9.7 but that is solved in newer (unstable) versions.
 */
class {:autocontracts} BinaryHeap<T(==)>
{
	// Greatest or equal priority comparator
	predicate method {:opaque} {:verify false} gep(a : T, b : T)
		// Reflexive
		ensures a == b ==> gep(a, b)
		// Transitive
		ensures forall c | gep(a, c) && gep(c, b) :: gep(a, b)
		// Total
		ensures gep(a, b) || gep(b, a)

	function Elements() : multiset<T>
		reads this, Repr

		requires Valid()
	{
		multiset(elems[..nelems])
	}

	// Number of elements in the heap
	function Size() : nat
		reads this
	{
		nelems
	}

	// Increases the size of the full up internal array
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

		ghost var Elements0 := multiset(elems[..nelems]);

		var pos := 0;

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

	constructor()
		ensures Elements() == multiset{}
	{
		elems := new T[31];
		nelems := 0;
	}

	predicate Valid()
	{
		// There is an array with enough capacity
		elems != null && nelems <= elems.Length
		&&
		// Parents have highest priority
		forall i | 0 < i < nelems :: gep(elems[Parent(i)], elems[i])
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
