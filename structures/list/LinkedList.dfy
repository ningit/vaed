/*
 * List implemented using linked nodes.
 */
class LinkedList<T>
{
	/*
	 * Abstract representation
	 */

	function Elements() : seq<T>
		reads Repr()
		requires Valid()

		// Implementation details
		ensures |Nodes| == |Elements()|
		ensures forall i | 0 <= i < |Nodes| :: Nodes[i].value == Elements()[i]
	{
		CollectElements(Nodes)
	}

	function CollectElements(ns : seq<Node<T>>) : seq<T>
		reads (set n | n in ns)

		requires forall i | 0 <= i < |ns| :: ns[i] != null

		// Elements = map (\x -> x.value) Nodes
		ensures |CollectElements(ns)| == |ns|
		ensures forall i | 0 <= i < |ns| :: CollectElements(ns)[i] == ns[i].value
	{
		if ns == [] then [] else

		[ns[0].value] + CollectElements(ns[1..])
	}

	function method CountElements(h : Node<T>, ghost n : nat) : nat
		reads Repr()
		decreases |Nodes| - n

		requires Valid()
		requires h != null ==> 0 <= n < |Nodes|
		requires h != null ==> Nodes[n] == h

		ensures h != null ==> CountElements(h, n) == |CollectElements(Nodes[n..])|
	{
		if h == null then 0 else

		1 + CountElements(h.next, n + 1)
	}

	/*
 	 * Observers
 	 */

	// Tests whether the stack is empty
	predicate method Empty()
		reads Repr()

		requires Valid()
		ensures Empty() <==> Elements() == []
	{
		head == null
	}

	// Gets the list size
	function method Size() : nat
		reads Repr()

		requires Valid()
		ensures Size() == |Elements()|
	{
		CountElements(head, 0)
	}

	// Gets the front of the list
	function method Front() : T
		reads Repr()

		requires Valid()
		requires !Empty()

		ensures Front() == Elements()[0]
	{
		head.value
	}

	// Gets iterator from the beginning
	method Iterator() returns (it : Iter<T>)
	{
		it := new Iter(head);
	}

	// Gets the n-th element of the list
	method Get(n : nat) returns (x : T)
		requires Valid()
		requires 0 <= n < Size()

		ensures Valid()
		ensures x == Elements()[n]
		ensures fresh(Repr() - old(Repr()))
	{
		var m := 0;

		// Current node
		var cnod := head;

		while m < n
			invariant n < |Nodes|
			invariant 0 <= m <= n
			invariant cnod == Nodes[m]
		{
			cnod := cnod.next;

			assert cnod == Nodes[m+1];

			m := m + 1;
		}

		x := cnod.value;
	}

	/*
	 * Modifiers
	 */

	// Sets the n-th element of the list
	method Set(n : nat, x : T)
		modifies (set n | n in Nodes)

		requires Valid()
		requires 0 <= n < Size()

		ensures Valid()
		ensures Elements() == old(Elements())[n := x]
		ensures fresh(Repr() - old(Repr()))
	{
		var m := 0;

		// Current node
		var cnod := head;

		while m < n
			invariant n < |Nodes|
			invariant 0 <= m <= n
			invariant cnod == Nodes[m]
		{
			cnod := cnod.next;

			assert cnod == Nodes[m+1];

			m := m + 1;
		}

		cnod.value := x;

		DistinctNodes();

		// This is unnecessary but decreases verification time
		forall i | 0 <= i < |Nodes|
			ensures i != m ==> Nodes[i].value == old(Nodes[i].value)
			ensures i == m ==> Nodes[i].value == x
		{
			assert Nodes[m] == cnod;
		}
	}

	// Removes the n-th element of the list
	method Remove(n : nat)
		modifies this, (set n | n in Nodes)

		requires Valid()
		requires 0 <= n < Size()

		ensures Valid()
		ensures Elements() == old(Elements())[..n] + old(Elements())[n+1..]
		ensures fresh(Repr() - old(Repr()))
	{
		var m := 0;

		// Current node
		var cnod := head;
		var pnod := null;

		while m < n
			invariant n < |Nodes|
			invariant 0 <= m <= n
			invariant cnod == Nodes[m]
			invariant m > 0 ==> pnod == Nodes[m-1]
		{
			cnod, pnod := cnod.next, cnod;

			assert cnod == Nodes[m+1];

			m := m + 1;
		}

		if m == 0
		{
			// Iff head becomes null, Nodes becomes empty
			assert Nodes[m].next == null ==> (NullIsLast(m); |Nodes| == 1);

			head := cnod.next;

			Nodes := Nodes[1..];

			assert Elements() == old(Elements())[1..];
		}
		else
		{
			DistinctNodes();

			pnod.next := cnod.next;

			Nodes := Nodes[..m] + Nodes[m+1..];


			// Correctness proof

			ghost var elems := Elements();
			ghost var elem0 := old(Elements());

			forall k | 0 <= k < |elems|
				ensures elems[k] == (elem0[..n] + elem0[n+1..])[k]
			{
				if k < m
				{
					calc == {
						elems[k];
						Nodes[k].value;
						old(Nodes)[k].value;
						elem0[k];
						(elem0[..n] + elem0[n+1..])[k];
					}
				}
				else {
					calc == {
						elems[k];
						Nodes[k].value;
						old(Nodes)[k+1].value;
						elem0[k+1];
						elem0[n+1..][k - n];
						(elem0[..n] + elem0[n+1..])[k];
					}
				}
			}
		}
	}

	// Insert at n-th position of the list
	method Insert(n : nat, x : T)
		modifies this, (set n | n in Nodes)

		requires Valid()
		requires 0 <= n <= Size()

		ensures Valid()
		ensures Elements() == old(Elements())[..n] + [x] +  old(Elements())[n..]
		ensures fresh(Repr() - old(Repr()))
	{
		if n == 0
		{
			Cons(x); return;
		}

		var m := 1;

		// Current node
		var fnod := head.next;
		var pnod := head;

		while m < n
			invariant n <= |Nodes|
			invariant 0 <= m <= n
			invariant fnod == Nodes[m-1].next
			invariant pnod == Nodes[m-1]
		{
			assert fnod == Nodes[m];

			fnod, pnod := fnod.next, pnod.next;

			m := m + 1;
		}

		DistinctNodes();

		// Stores the new element in a new node
		var newNode := new Node;

		newNode.next := fnod;
		pnod.next := newNode;

		newNode.value := x;

		// Updates Nodes auxiliary variable
		ghost var nodes0 := Nodes;

		Nodes := nodes0[..n] + [newNode] + nodes0[n..];


		// Postcondition correctness proof

		ghost var elems  := Elements();
		ghost var elem0  := old(Elements());
		ghost var elems' := elem0[..n] + [x] + elem0[n..];

		forall i | 0 <= i < |elems|
			ensures elems[i] == elems'[i]
		{
			if i < n
			{
				calc == {
					elems[i];
					Nodes[i].value;
					old(Nodes)[i].value;
					elem0[i];
					elems'[i];
				}
			}
			else if i > n
			{
				calc == {
					elems[i];
					Nodes[i].value;
					old(Nodes)[i-1].value;
					elem0[i-1];
					elems'[i];
				}
			}
		}
	}

	/**
	 * Constructors
	 */
	constructor()
		modifies this

		ensures Valid()
		ensures Elements() == []
		ensures fresh(Repr() - {this})
	{

		head	:= null;

		Nodes	:= [];
	}

	method Cons(x : T)
		modifies this

		requires Valid()
		ensures Valid()
		ensures Elements() == [x] + old(Elements())
		ensures fresh(Repr() - old(Repr()))
	{
		var head0 := head;

		head := new Node;

		head.value	:= x;
		head.next	:= head0;

		Nodes := [head] + Nodes;
	}

	predicate Valid()
		reads this, (set n | n in Nodes)
	{
		// The sequence is filled with valid nodes
		(forall i | 0 <= i < |Nodes| :: Nodes[i] != null)
		&&
		// Nodes are linked in sequence
		(forall i | 0 <= i < |Nodes|-1 :: Nodes[i].next == Nodes[i+1])
		&&
		// If head is empty, there are not nodes
		(Nodes == [] <==> head == null)
		&&
		// Otherwise, the first one is the head and the last one is empty
		(head != null ==> Nodes[0] == head && Nodes[|Nodes|-1].next == null)
	}

	function Repr() : set<object>
		reads this
	{
		{this} + set n : object | n in Nodes :: n
	}

	// All nodes in Nodes are distinct
	lemma DistinctNodes()
		requires Valid()

		ensures forall i, j | 0 <= i < j < |Nodes| :: Nodes[i] != Nodes[j]
	{
		// Obviously true: suppose Node is not empty
		if Nodes == [] { return; }

		var k := |Nodes| - 1;

		// Proof by induction with reductio ad absurdum

		while k > 0
			invariant 0 <= k < |Nodes|
			invariant forall i, j | k <= i < j < |Nodes| :: Nodes[i] != Nodes[j]
		{
			k := k - 1;

			if exists i, j | k <= i < j < |Nodes| :: Nodes[i] == Nodes[j]
			{
				var i, j :| k <= i < j < |Nodes| && Nodes[i] == Nodes[j];

				if j == |Nodes|-1
				{
					assert Nodes[j].next == null;
					assert Nodes[i].next == Nodes[i+1];
					// and Nodes[i+1]
				}
				else if i == k
				{
					assert Nodes[k].next == Nodes[k+1];
					assert Nodes[j].next == Nodes[j+1];

					// Absurd by hypothesis (invariant)
					assert Nodes[k+1] == Nodes[j+1];
				}

				// Otherwise: the invariant
			}
		}
	}

	// Next pointer is null only in last element
	lemma NullIsLast(m : nat)
		requires Valid()
		requires 0 <= m < |Nodes|
		requires Nodes[m].next == null

		ensures m == |Nodes| - 1 
	{
		// Suppose not: next is a valid node which is not null
		if (m != |Nodes| - 1) {
			assert Nodes[m].next == Nodes[m+1];
		}
	}

	// Data representation
	var head : Node<T>;

	// Sequence of nodes
	ghost var Nodes : seq<Node<T>>;
}


// Iterator on the list
iterator Iter<T>(nod : Node<T>) yields (x : T) {
	var curr := nod;

	while curr != null {
		yield curr.value;

		curr := curr.next;
	}
}


// Single linked nodes
class Node<T> {
	var next : Node<T>;

	var value : T;
}
