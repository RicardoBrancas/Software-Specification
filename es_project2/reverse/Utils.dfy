datatype List<T> = Nil | Cons (head: T, tail: List)

function method append<T>(l1: List<T>, l2: List<T>): List<T>
decreases l1
{
    match l1
        case Nil => l2
        case Cons(h, t) => Cons(h, append(t, l2))
}

function method reverse(l: List): List
    decreases l
{
    match l
        case Nil => Nil
        case Cons(h, T) => append(reverse(T), Cons (h, Nil))
}

method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
    ensures a[..] == s
{
    a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

function method concat<T>(s: List<seq<T>>): seq<T>
    decreases s
{
    match s
        case Nil => []
        case Cons(h, T) => h + concat(T)
}

lemma {:induction s} concat_unit<T>(s: List<seq<T>>, elem:seq<T>)
    ensures concat(append(s, Cons(elem, Nil))) == concat(s) + elem
{}

lemma {:induction s} reverse_concat_keeps<T>(s: List<seq<T>>)
    ensures |concat(s)| == |concat(reverse(s))|
{
    match s
        case Nil => {}
        case Cons(h, T) =>
            calc == {
                |concat(Cons(h, T))|;
                |h + concat(T)|;
                |h| + |concat(T)|;
                |h| + |concat(reverse(T))|;
                |concat(reverse(T))| + |h|;
                |concat(reverse(T)) + h|;
                == {concat_unit(reverse(T), h);}
                |concat(append(reverse(T), Cons(h, Nil)))|;
            }
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