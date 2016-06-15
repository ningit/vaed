method raiz(n : int, a : int) returns (r : int)
	requires n >= 0 && a >= 0
	requires a * a <= n 
	ensures r * r <= n < (r + 1) * (r + 1)

	decreases n - a * a
{
	if (a + 1) * (a + 1) > n {
		r := a;
	}
	else {
		r := raiz(n, a + 1);
	}
}
