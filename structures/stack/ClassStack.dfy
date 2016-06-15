/*
 * Stack implemented by means of classes and pointers.
 *
 */
include "Stack.dfy"

// This module is abstract because type T is not defined

abstract module ClassStack refines Stack
{

class Stack
{
	function method Top...
	{
		head.value
	}

	method Pop...
	{
		// Needed in order to prove that the chaine from the
		// new head is still valid
		assert Repr - {head} - {this} == Repr - {this} - {head};

		head := head.next;

		Repr := Repr - {old(head)};
	}

	method Push...
	{
		var newHead := new Node;

		newHead.value := e;
		newHead.next  := head;

		newHead.tailLength := if head == null then 0 else
			1 + head.tailLength;

		head := newHead;

		Repr := Repr + {head};

		assert Repr - {this} - {head} == Repr - {head} - {this};
	}

	predicate method Empty...
	{
		head == null
	}

	function method Size...
	{
		ChainSize(head, Repr - {this})
	}

	// Abstract representation

	function Elements...
	{
		ValueChain(head, Repr - {this})
	}

	predicate Valid()
	{
		(head != null ==> head in Repr) && ValidChain(head, Repr - {this})
	}

	constructor ()
	{
		head := null;

		Repr := {this};
	}

	// Data representation
	var head : Node; 
}

// Node class

class Node
{
	// Node value
	var value : T;

	// Pointer to the next node
	var next : Node;

	// Tail length bound
	ghost var tailLength : nat;
}

predicate ValidLink(node : Node)
	reads node, node.next

	requires node != null
{
	(node.tailLength == 0 ==> node.next == null)
	&&
	(node.next != null ==> node.next.tailLength < node.tailLength)
}

predicate ValidChain(node : Node, nodes : set<object>)
	reads nodes

	requires node == null || node in nodes
{
	node == null ||

	(node.next != null ==> node.next in nodes && ValidLink(node) && ValidChain(node.next, nodes - {node}))
}

function ValueChain(node : Node, nodes : set<object>) : seq<T>
	reads nodes

	requires node == null || node in nodes
	requires ValidChain(node, nodes)
{
	if node == null

	then	[]
	else	[node.value] + ValueChain(node.next, nodes - {node})
}

function method ChainSize(node : Node, ghost nodes : set<object>) : nat
	reads nodes

	requires node == null || node in nodes
	requires ValidChain(node, nodes)

	ensures ChainSize(node, nodes) == |ValueChain(node, nodes)|

	decreases |nodes|
{
	if node == null

	then	0
	else	1 + ChainSize(node.next, nodes - {node})
}

}
