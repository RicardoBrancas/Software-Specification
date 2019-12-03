method integerDivision (A: int, B: int) returns (q: int, r: int)
requires A > 0
requires B > 0
ensures A == q * B + r
ensures 0 <= r
ensures r < B
{
    q := 0;
    r := A;
    while r >= B
        invariant A == q * B + r
        invariant 0 <= r
        decreases r
    {
        q := q +1;
        r := r - B;
    }
}

function fact(x: int): int
requires x >= 0
decreases x
{
    if (x == 0) then 1 else x * fact(x-1)
}

method factorial(x: int) returns (y: int)
requires x >= 0
ensures y == fact(x)
{
    y := 1;
    var z := 0;
    while z != x
        invariant y == fact(z)
        invariant z <= x
        decreases x - z
    {
        z := z + 1;
        y := y * z;
    }
}

function gcd(a: nat, b: nat): nat
requires a > 0
requires b > 0
decreases a, b
{
    if (a == b) then a
    else if (a > b) then gcd(a-b, b)
    else gcd(a, b-a)
}

method euclides(M: nat, N: nat) returns (x: nat, y: nat)
requires 0 < M
requires 0 < N
ensures x == y
ensures x == gcd(M, N)
{
    x := M;
    y := N;
    while x != y
        invariant x > 0
        invariant y > 0
        invariant gcd(x, y) == gcd(M, N)
        decreases x + y
    {
        if x < y {
            y := y - x;
        } else {
            x := x - y;
        }
    }
}

function pow(a: int, b: int): int
requires b >= 0
decreases b
{
    if b == 0 then 1 else a * pow(a, b-1)
}

method exponentiation(A: int, B: int) returns (r: int)
requires A >= 0
requires B >= 0
ensures r == pow(A, B)
{
    r := 1;
    var x := 0;
    while x != B
        invariant r == pow(A, x)
        invariant x <= B
        decreases B - x
    {
        r := r * A;
        x := x + 1;
    }
}

method squareRoot(n: nat) returns (r: int)
ensures r*r <= n
ensures (r+1)*(r+1) >= n
{
    r := 0;
    while r*r > n || (r+1)*(r+1) < n
        invariant r*r <= n
        decreases n - r
    {
        r := r + 1;
    }
}

method nth_odd (n: nat) returns (j: int)
ensures j == 1 + 2*n
{
    var k := 0;
    j := 1;
    while k < n
        invariant k <= n
        invariant j == 1 + 2*k
        decreases n - k
    {
        k := k + 1;
        j := j + 2;
    }
}

method nth_even (n: nat) returns (j: int)
ensures j == 2*n
{
    var k := 0;
    j := 0;
    while k < n
        invariant k <= n
        invariant j == 2*k
        decreases n - k
    {
        k := k + 1;
        j := j + 2;
    }
}

method loop(x: int) returns (ret:int)
requires x > 0
ensures ret == x * x
{
    var y := x;
    var z := 0;

    while (y > 0) 
        invariant z == x * (x - y)
        decreases y
    {
        z := z + x;
        y := y - 1;
    }

    return z;
}

method loop2 (n: nat) returns (j : nat)
ensures j == pow(2, n)
{
    var k := 0;
    j := 1;
    while k < n
        invariant k <= n
        invariant j == pow(2, k)
        decreases n - k
    {
        k := k + 1;
        j := 2 * j ;
    }
}