function fob(n : nat, x : nat, y : nat) : nat {
		if n == 0 then 	x
	else 	if n == 1 then 	y
	else 			fob(n - 2, x, y) + fob(n - 1, x, y)
}

lemma Igualdad(n : nat, x : nat, y : nat)
	ensures fob(n, y, x + y) == fob(n+1, x, y)
{
	// Demostración por inducción

	if n > 1 {
		Igualdad(n-2, x, y);
		Igualdad(n-1, x, y);
	}
}


method gfob(n : nat, x : nat, y : nat) returns (r : nat, s : nat)
	ensures r == fob(n, x, y)
	ensures s == fob(n + 1, x, y)
{
	if n == 0 {
		r, s := x, y;
	}
	else {
		r, s := gfob(n - 1, y, x + y);

		Igualdad(n, x, y);
		Igualdad(n-1, x, y);
	}

}
