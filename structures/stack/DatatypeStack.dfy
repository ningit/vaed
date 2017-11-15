/*
 * Stack implemented by means of an inductive data type.
 */
include "Stack.dfy"

// This module is abstract because type T is not defined

abstract module DatatypeStack refines Stack
{

class {:autocontracts} Stack
{
	function method Top...
	{
		elems.x
	}

	method Pop...
	{
		elems := elems.xs;
	}

	// Pushes an element to the top of the stack
	method Push...
	{
		elems := Cons(e, elems);
	}

	predicate method Empty...
	{
		elems == EmptyStack
	}

	function method Size...
	{
		StackIRSize(elems)
	}

	// Abstract representation

	function Elements...
	{
		IRToSeq(elems)
	}

	constructor ()
	{
		elems := EmptyStack;
		Repr := {this};
	}

	// Data representation
	var elems	: StackIR; 
}

// Inductive data type
datatype StackIR = EmptyStack | Cons(x : T, xs : StackIR)

// The number of elements in the stack
function method StackIRSize(x : StackIR) : nat
	ensures StackIRSize(x) == |IRToSeq(x)|
{
	match x 
		case EmptyStack =>
			0

		case Cons(_, y) =>
			StackIRSize(y) + 1
}

// Converts the inductive data type to a sequence
function IRToSeq(x : StackIR) : seq<T>
{
	match x
		case EmptyStack =>
			[]

		case Cons(e, xs) =>
			[e] + IRToSeq(xs)
}

}
