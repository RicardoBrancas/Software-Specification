function method reverse<T>(l: seq<T>): seq<T>
decreases l
{
    if l == [] then [] else reverse(l[1..]) + l[..1]
}

method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
    ensures a[..] == s
{
    a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

function position1<T>(s: seq<T>, b: T): nat
    decreases s
    requires b in s
    ensures position1(s, b) < |s|
    ensures s[position1(s, b)] == b
    ensures forall k :: 0 <= k < position1(s, b) ==> s[k] != b
{
    if (s[0] == b) then 0 else 1 + position1(s[1..], b)
}

function count<T>(s: seq<T>, b: T): nat
    decreases s
    ensures count(s, b) <= |s|
    ensures s == [] ==> count(s, b) == 0
    //TODO
{   
    multiset(s)[b]
}