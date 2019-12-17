predicate matches<T(==)>(a1:seq<T>, i1: nat, a2:seq<T>, i2:nat, n:nat)
{
    0 <= i1 <= |a1| - n &&
    0 <= i2 <= |a2| - n &&
    forall i :: 0 <= i < n ==> a1[i1+i] == a2[i2+i]
}

predicate any_match<T(==)>(t: seq<T>, p:seq<T>, pos:nat)
  decreases t
  requires 0 <= pos <= |t|
{
  exists i :: 0 <= i <= pos - |p| && matches(t, i, p, 0, |p|)
}

predicate lps<T(==)>(S: seq<T>, q:nat, k:nat)
{
    0 <= k < q <= |S|
    && matches(S, q-k, S, 0, k)
    && (forall k' :: k < k' < q ==> !matches(S, q-k', S, 0, k'))
}

method PrefixFunction<T(==)>(P: seq<T>) returns (pi: array<nat>)
    requires |P| > 0

    ensures pi.Length == |P|+1
    ensures forall i :: 0 < i < |P| ==> lps(P, i, pi[i])
{
    pi := new nat[|P|+1];
    pi[1] := 0;
    var q := 1;
    var k := 0;
    while q < |P|
        decreases pi.Length - q, k

        invariant 0 <= k < q <= |P|

        invariant matches(P, q-k, P, 0, k)
        invariant forall i :: 0 < i <= q ==> lps(P, i, pi[i])
    {
        k := pi[q];
        q := q + 1;
        
        assert lps(P, q-1, k);
        
        while k > 0 && P[k] != P[q-1]
            decreases k

            invariant 0 <= k < |P|

            invariant matches(P, q-k-1, P, 0, k)
            invariant forall i :: 0 < i <= q-1 ==> lps(P, i, pi[i])
        {
            k := pi[k];
        }

        if P[k] == P[q-1] {
            k := k + 1;
        }

        pi[q] := k;
    }
}

method Match<Type(==)>(T: seq<Type>, P: seq<Type>) returns (found: bool, pos:nat)
    requires |P| > 0
    requires |T| > 0

    ensures any_match(T, P, |T|) <==> found
    ensures found ==> 0 <= pos < |T|
    ensures !found ==> 0 <= pos <= |T|
    ensures found ==> matches(T, pos, P, 0, |P|)
    ensures forall k :: 0 <= k < pos ==> !matches(T, k, P, 0, |P|)
{
   var pi := PrefixFunction(P);
   var i, q := 0, 0;
    while q < |P| && i < |T|
        decreases |T| - i

        invariant 0 <= q <= |P|
        invariant q <= i <= |T|
        invariant forall k :: 0 < k < |P| ==> lps(P, k, pi[k])
        invariant matches(T, i-q, P, 0, q)
        invariant forall k :: 0 <= k < i - q ==> !matches(T, k, P, 0, |P|)
        invariant q < |P| ==> !any_match(T, P, i)
    {
        i := i + 1;

        while q > 0 && q < |P| && T[i-1] != P[q]
            decreases q

            invariant 0 <= q <= |P|
            invariant q <= i <= |T|
            invariant matches(T, i-q-1, P, 0, q)
            invariant !any_match(T, P, i-1)
            invariant forall k :: 0 < k < |P| ==> lps(P, k, pi[k])
            invariant forall k :: 0 <= k < i - q - 1 ==> !matches(T, k, P, 0, |P|)
        {
            assert forall k :: 0 <= k < i - q - 1 ==> !matches(T, k, P, 0, |P|);
            q := pi[q];
        }

        if T[i-1] == P[q] {
            q := q + 1;
        }
    }
    found := q == |P|;
    pos := i - q;
}