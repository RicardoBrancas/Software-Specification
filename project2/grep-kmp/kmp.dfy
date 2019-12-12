predicate proper_suffix<T(==)>(w:seq<T>, x:seq<T>)
    requires |w| < |x|
    ensures (|w| == 0 && |x| > 0) ==> proper_suffix(w, x)
{
    x[|x|-|w|..] == w
}

lemma proper_suffix_empty<T(==)>(s:seq<T>)
    
{}

/*predicate suffix<T(==)>(w:seq<T>, x:seq<T>)
    requires |w| <= |x|
{
    x[|x|-|w|..] == w
}*/

function method match_at<T(==)>(t: seq<T>, p:seq<T>, t_pos:nat): bool
    requires 0 <= t_pos < |t|
{
    p <= t[t_pos..]
}

predicate lps<T(==)>(S: seq<T>, q:nat, k:nat)
    requires 0 <= k < q <= |S|
{
    (k == 0 && q == 0) || (
    proper_suffix(S[..k], S[..q])
    && (forall k' :: k <= k' < q ==> !proper_suffix(S[..k'], S[..q]))
    )
}

lemma extend_lps<T(==)>(S: seq<T>, q:nat, k:nat)

{}

method PrefixFunction<T(==)>(P: seq<T>) returns (pi: array<int>)
    requires |P| > 1

    ensures pi.Length == |P|+1
    ensures forall i :: 1 <= i < |P| ==> 0 <= pi[i] < i
    ensures forall i :: 1 <= i < |P| ==> lps(P, i, pi[i])
{
    pi := new int[|P|+1];
    pi[1] := 0;
    var q := 1;
    var k := 0;
    while q < |P|
        decreases pi.Length - q

        invariant 0 <= k < q <= |P|

        invariant pi[q] == k
        invariant forall i :: 1 <= i < q ==> 0 <= pi[i] < i
        invariant forall i :: 1 <= i < q ==> lps(P, i, pi[i])
        invariant proper_suffix(P[..k], P[..q])
        //invariant forall k' :: k < k' < q ==> !proper_suffix(P[..k'], P[..q])
    {
        q := q + 1;
        
        while k > 0 && P[k] != P[q-1]
            decreases k

            invariant 0 <= k < |P|

            invariant forall i :: 1 <= i < q ==> 0 <= pi[i] < i
            invariant forall i :: 1 <= i < q-1 ==> lps(P, i, pi[i])
            invariant proper_suffix(P[..k], P[..q-1])
            //invariant forall k' :: k < k' < q-1 ==> !proper_suffix(P[..k'], P[..q-1])
        {
            k := pi[k];
        }

        if P[k] == P[q-1] {
            k := k + 1;
        }

        pi[q] := k;
    }
}

method Match<Type(==)>(T: seq<Type>, P: seq<Type>) returns (m: bool, pos:nat)
    requires |P| > 1
    requires |T| > 0
    requires |T| >= |P|

    ensures m ==> 0 <= pos < |T|
    ensures !m ==> 0 <= pos <= |T|
    ensures m ==> match_at(T, P, pos)
    ensures forall k :: 0 <= k < pos ==> !match_at(T, P, k)
{
   var pi := PrefixFunction(P);
   var i, q := 0, 0;
    while q < |P| && i < |T|
        decreases |T| - i

        invariant 0 <= q <= |P|
        invariant q <= i <= |T|
        invariant T[i-q..i] == P[..q]
        invariant forall k :: 0 <= k < i - q ==> !match_at(T, P, k)
    {
        i := i + 1;

        while q > 0 && q < |P| && T[i-1] != P[q]
            decreases q

            invariant 0 <= q
            invariant q <= |P|
            invariant q <= i <= |T|
            invariant T[i-1-q..i-1] == P[..q]
            invariant forall k :: 0 <= k < i - q -1 ==> !match_at(T, P, k)   
        {
            q := pi[q];
        }

        if T[i-1] == P[q] {
            q := q + 1;
        }
    }
    m := q == |P|;
    pos := i - q;
}