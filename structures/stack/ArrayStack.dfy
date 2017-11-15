/*
 * Stack implemented by means of an array.
 */
include "Stack.dfy"

// This module is abstract because type T is not defined

abstract module ArrayStack refines Stack
{
	// Default value for T
	// (it is needed to initialize the array)
	function method DefaultValue() : T

class {:autocontracts} Stack
{
	function method Top...
	{
		ReverseLemma(elems[..nelems]);

		elems[nelems - 1]
	}

	method Pop...
	{
		ReverseCorollaryTail(elems[..nelems]);

		assert elems[..nelems][..nelems-1] == elems[..nelems-1];

		nelems	:= nelems - 1;
	}

	method Expand()
		modifies this

		ensures nelems < elems.Length
		ensures Elements() == old(Elements())
	{
		var tmp := new T[elems.Length * 2](_ => DefaultValue());

		assert elems.Length < tmp.Length;

		forall i | 0 <= i < nelems
		{
			tmp[i] := elems[i];
		}

		assert tmp[..nelems] == elems[..nelems];

		Repr := {tmp};
		elems := tmp;
	}

	method Push...
	{
		// Test if space is exhausted
		if nelems == elems.Length
		{
			Expand();

			// Why do we need to set Repr twice to make
			// «fresh(Repr - old(Repr))» hold?
			Repr := {elems};
		}

		ReverseCorollaryCons(elems[..nelems], e);

		// Adds the new element
		elems[nelems]	:= e;

		assert elems[..nelems + 1] == elems[..nelems] + [e];

		nelems		:= nelems + 1;
	}

	predicate method Empty...
	{
		ReverseLemma(elems[..nelems]);

		nelems == 0
	}

	function method Size...
	{
		ReverseLemma(elems[..nelems]);

		nelems
	}

	// Abstract representation

	function Elements...
	{
		Reverse(elems[..nelems])
	}

	predicate Valid() {
		elems != null && nelems <= elems.Length && elems.Length > 0
	}

	// Data representation

	constructor()
	{
		elems	:= new T[16](_ => DefaultValue());
		nelems	:= 0;

		Repr := {elems};
	}

	// Data representation
	var elems	: array<T>;

	// Number of elements (size)
	var nelems	: nat;
}

function Reverse<R>(xs : seq<R>) : seq<R>
{
	ReverseAux(xs, [])
}

function ReverseAux<R>(xs : seq<R>, a : seq<R>) : seq<R>
{
	if xs == []

	then a
	else ReverseAux(xs[1..], [xs[0]] + a)
}

lemma ReverseLemma<R>(xs : seq<R>)
	ensures |xs| == |Reverse(xs)|
	ensures forall i | 0 <= i < |xs| :: xs[i] == Reverse(xs)[|xs| - i - 1]
{
	ReverseLemmaAux(xs, []);
}

lemma {:induction false} ReverseLemmaAux<R>(xs : seq<R>, a : seq<R>)
	ensures |xs| + |a| == |ReverseAux(xs, a)|

	ensures forall i | 0 <= i < |xs| ::
		xs[i] == ReverseAux(xs, a)[|xs| - i - 1]

	ensures forall i | 0 <= i < |a| ::
		a[i] == ReverseAux(xs, a)[|xs| + i]
{
	if xs != [] {
		ReverseLemmaAux(xs[1..], [xs[0]] + a);

		assert ([xs[0]] + a)[0] == ReverseAux(xs, a)[|xs| - 1];

		// Uncommenting the following reduce verificiation time

		// assert forall i | 1 <= i < |xs| ::
		//	xs[i] == ReverseAux(xs, a)[|xs| - i - 1];
	}
}

lemma ReverseCorollaryCons<R>(xs : seq<R>, x : R)
	ensures [x] + Reverse(xs) == Reverse(xs + [x])
{
	ReverseLemma(xs);
	ReverseLemma(xs + [x]);

	var lhs, rhs := [x] + Reverse(xs), Reverse(xs + [x]);

	calc {
		rhs[0];
		(xs + [x])[|xs|];
		x;
		lhs[0];
	}

	forall i | 0 < i < |xs|
		ensures lhs[i] == rhs[i];
	{
		calc {
			rhs[i];
			(xs + [x])[|xs| - i];
			xs[|xs| - i];
			lhs[i];
		}
	}
}

lemma ReverseCorollaryTail<R>(xs : seq<R>)
	requires xs != []

	// needed for the next postcondition to make sense
	ensures |Reverse(xs)| == |xs|
	ensures Reverse(xs)[1..] == Reverse(xs[..|xs|-1])
{
	ReverseCorollaryCons(xs[..|xs|-1], xs[|xs|-1]);

	assert xs == xs[..|xs|-1] + [xs[|xs|-1]];

	ReverseLemma(xs);
}

}
