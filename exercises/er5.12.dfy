/*
 * En la versión anterior de este ejercicio Ord se definía como s[i] <= s[i+1]
 * y así sólo funcionaba con la opción /autoTriggers:0.
 *
 * Hay un ejemplo oficial en:
 * http://dafny.codeplex.com/SourceControl/latest#Test/triggers/
 * some-proofs-only-work-without-autoTriggers.dfy
 */

// ¿Está la secuencia ordenada?
predicate Ord(s : seq<int>) {
	forall i, j | 0 <= i <= j < |s| - 1 :: s[i] <= s[j]
}


// Versión recursiva

method busq_binaria(a : array<int>, x : int, c : nat, f : nat) returns
	(b : bool, p : nat)

	requires a != null
	requires Ord(a[..])
	requires 0 <= c <= f <= a.Length-1

	ensures b ==> c <= p < f && a[p] == x
	ensures !b ==> c <= p <= f
		&& (forall j | c <= j < p :: a[j] < x)
		&& (forall j | p <= j < f :: a[j] > x)

	decreases f - c
{
	var m : nat;

	if c == f {
		b, p := false, c;
	}
	else /* c < f */ {
		m := (c + f) / 2;

		if x < a[m] {
			b, p := busq_binaria(a, x, c, m);
		}
		else if x == a[m] {
			b, p := true, m;
		}
		else /* x > a[m] */ {
			b, p := busq_binaria(a, x, m+1, f);
		}
	}
}


// Versión iterativa

method busq_binaria_it(a : array<int>, x : int, c : nat, f : nat) returns 
	(b : bool, p : nat)

	requires a != null
	requires Ord(a[..])
	requires 0 <= c <= f <= a.Length-1

	ensures b ==> c <= p < f && a[p] == x
	ensures !b ==> c <= p <= f
		&& (forall y | y in a[c..p] :: y < x)
		&& (forall y | y in a[p..f] :: y > x)
{
	var m : nat := (c + f) / 2;

	var c', f' := c, f;

	while c' < f' && x != a[m]
		invariant c <= c' <= f' <= f
		invariant m == (c' + f') / 2;

		// Resto de invariantes
		invariant forall y | y in a[c..c'] :: y < x
		invariant forall y | y in a[f'..f] :: y > x
	{
		if x < a[m] {
			f' := m;
		}
		else /* x > a[m] */ {
			c' := m+1;
		}

		m := (c' + f') / 2;
	}

	if c' == f' {
		b, p := false, c';
	}
	else /* x == a[m] */ {
		b, p := true, m; 
	}
}
