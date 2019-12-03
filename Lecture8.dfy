datatype Colour = Red | White | Blue

predicate Below(c1: Colour, c2: Colour)
{
    c1 == Red || c1 == c2 || c2 == Blue
}

method DutchFlag(a: array<Colour>)
    modifies a
    ensures forall k :: 0 <= k < a.Length-1 ==> Below(a[k], a[k+1])
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var r, w, b := 0, 0, a.Length;

    while w != b
        invariant 0 <= r <= w <= b <= a.Length
        invariant forall k :: 0 <= k < r ==> a[k] == Red
        invariant forall k :: r <= k < w ==> a[k] == White
        invariant forall k :: b <= k < a.Length ==> a[k] == Blue
        invariant multiset(a[..]) == multiset(old(a[..]))
        decreases b - w
    {
        match a[w]
            case Red => 
                a[r], a[w] := a[w], a[r];
                r := r + 1;
                w := w + 1;
            case White =>
                w := w + 1;
            case Blue =>
                a[b-1], a[w] := a[w], a[b-1];
                b := b - 1;
    }
}