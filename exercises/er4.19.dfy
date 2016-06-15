/**
 * En este ejercicio se puede observar que el operador de conjunción lógica
 * de Dafny tiene cortocircuito.
 */

predicate method Par(n : int) {
	n % 2 == 0
}

// «k índice es el índice del primer número par de la secuencia s o en su
// defecto es |s|»
predicate EsPrimerPar(s : seq<int>, k : nat) {
	// Es un índice del vector o es |s| para indicar ausencia
	0 <= k <= |s|

	// Todos los anteriores son impares
	&& forall j | 0 <= j < k :: !Par(s[j])

	// Y si es un índice propio es par
	&& k != |s| ==> Par(s[k])
}

method primer_par(v : array<int>) returns (x : nat)
	requires v != null
	ensures EsPrimerPar(v[..], x)
{
	x := 0;

	while x != v.Length && !Par(v[x])
		invariant 0 <= x <= v.Length
		invariant forall i | 0 <= i < x :: !Par(v[i])
	{
		x := x + 1;
	}
}
