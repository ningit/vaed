function Fibo(n : nat) : nat {
	if 	n == 0	then 0
	else if n == 1	then 1
			else Fibo(n-1) + Fibo(n-2)
}

method gfib(n : nat) returns (f : nat, g : nat)
	ensures f == Fibo(n)
	ensures g == Fibo(n+1)
{
	if n == 0 {
		f, g := 0, 1;
	}
	else if n == 1 {
		f, g := 1, 1;
	}
	else {
		f, g := gfib(n-1);

		f, g := g, f + g;
	}
}
