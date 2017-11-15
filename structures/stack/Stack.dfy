abstract module Stack {

// Type parameter
type T

// A FIFO data structure
class Stack
{
	// Creates the empty stack
	constructor()
		ensures Valid()
		ensures fresh(Repr)
		ensures Elements() == []

	// Gets the top element of the stack without changing it
	function method Top() : T
		reads this, Repr
		requires Valid()
		requires !Empty()
		ensures Top() == Elements()[0]

	// Removes the top element of the stack
	method Pop()
		modifies this, Repr
		requires Valid()
		requires !Empty()
		ensures Valid()
		ensures fresh(Repr - old(Repr))
		ensures Elements() == old(Elements())[1..]

	// Pushes an element to the top of the stack
	method Push(e : T)
		modifies this, Repr
		requires Valid()
		ensures Valid()
		ensures fresh(Repr - old(Repr))
		ensures Elements() == [e] + old(Elements())

	// Tests whether the stack is empty
	predicate method Empty()
		reads this, Repr
		requires Valid()
		ensures Empty() <==> Elements() == []

	// Number of elements
	function method Size() : nat
		reads this, Repr
		requires Valid()
		ensures Size() == |Elements()|

	// Abstract representation
	function Elements() : seq<T>
		reads this, Repr
		requires Valid()

	// Validity predicate
	predicate Valid()
		reads this, Repr

	// Set of objects under the class representation 
	ghost var Repr : set<object>;
}

}
