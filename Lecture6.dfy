// Methods and Contracts

method between (p: int, r: int) returns (q: int)
 requires r-p > 1
 ensures p < q && q < r  // We can write this in two separate lines
{
    q := (p+r) / 2;
}

method MultipleReturns(x: int, y: int) 
        returns (more: int, less: int)
 ensures less < x
 ensures x < more
{
    more := x + y;
    less := x - y;
}

// Local variables

/*
method m1() {
    var a := 0;
    a := 1;
    var a := 2;
    var b:int;
    var c;
    var d:int, e:bool := 0;
    var f, g := 0, false;
    var h, i:int;
}
*/

// Methods: Opacity
method Triple(x: int) returns (r: int)
 ensures r == 3*x
{
    var y := Double(x);
    r := y + x;
}

method Double(x:int) returns (r:int)
 ensures r == 2*x

// Exercise: Write a method Max that takes two integer parameters and returns
// their maximum. Add appropriate annotations and make sure your code verifies.

method Max(x: int, y: int) returns (r: int)
ensures r >= x
ensures r >= y
ensures r == x || r == y
{
    if y <= x {
        r := x;
    } else {
        return y;
    }
}

// Assertions
// Exercise: Add v==3 to the end of TestAbs

method Abs(x: int) returns (y: int)
 ensures 0 <= y
{
    if x < 0 {
        return -x;
    } else {
        return x;
    }
}

method TestAbs() {
    var v := Abs(3);
    assert 0 <= v;
}


// Functions

function abs(x: int): int
{
    if x<0 then -x else x
}

method m2()
{
    assert abs(3) == 3;
}

// Exercise: max function


// Exercise: Fibonacci function


// Loop invariants

method m4(n: nat)
{
    var i := 0;
    while i < n
        invariant 0 <= i
    {
        i := i+1;
    }
    assert i==n;
}

// Exercise: exponentiation


// Exercise: iterative fib



