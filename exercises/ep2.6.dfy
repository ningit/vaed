method maximo(v : array<int>, n : int) returns (m : int)
	requires v != null
	requires 0 <= n < v.Length
	ensures exists k : int | 0 <= k <= n :: v[k] == m
	ensures forall j : int | 0 <= j <= n :: v[j] <= m
{
	if n == 0 {
		m := v[0];
	}
	else {
		m := maximo(v, n-1);

		if (v[n] > m) {
			m := v[n];
		}
	}
}

