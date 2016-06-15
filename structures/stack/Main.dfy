/*
 * Stacks test.
 *
 * All non-final modules must be defined abstract in order to tell Dafny we
 * don't want to produce code for them. Otherwise an error will we shown:
 *	«Opaque type ('_1_DatatypeStack_Compile.T') cannot be compiled»
 *
 * Answer found in http://dafny.codeplex.com/discussions/541972 and "Programming
 * Language Features for Refinement" [krml248], page 4.
 *
 */

include "ClassStack.dfy"  // or ArrayStack/DatatypeStack

module IntStack refines ClassStack
{
	type T = int
}

method Main()
{
	var m := new IntStack.Stack();

	print m.Empty(), "\n";

	m.Push(3);
	m.Push(7);
	m.Pop();

	print m.Top(), " ", m.Size(), " ", m.Empty(), "\n";
}
