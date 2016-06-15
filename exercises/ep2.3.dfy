// Suma de los k primeros números naturales
function SumaPrim(k : nat) : nat {
	if k == 0 then 0 else k + SumaPrim(k-1)
}

// La función anterior es monótona
lemma Monotonia()
	 ensures forall i : nat , j : nat | i < j :: SumaPrim(i) < SumaPrim(j)
{
}

method es_triangular(n : nat) returns (b : bool)
	requires n > 0
	ensures b == exists k : nat :: n == SumaPrim(k)
{
	var j : nat, s : nat := 1, 1;

	while s < n
		invariant s == SumaPrim(j)
		invariant SumaPrim(j-1) < n
	{
		j := j + 1;
		s := s + j;
	}

	b := (s == n);

	// Es necesario
	Monotonia();

	/*
	 * De la monotonía se deducen los siguientes para-todo:

	assert b <==> n == SumaPrim(j);

	assert forall i : nat | i < j :: n != SumaPrim(i);

	assert forall i : nat | i > j :: n != SumaPrim(i);

	*/
}
