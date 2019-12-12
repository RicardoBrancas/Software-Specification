predicate prefix_suffix<T(==)>(S: seq<T>, k: nat)
    requires 0 <= k <= |S|
{
    S[..k] == S[|S|-k..]
}

function method match_at<T(==)>(t: seq<T>, p:seq<T>, t_pos:nat): bool
    requires 0 <= t_pos < |t|
{
    p <= t[t_pos..]
}

lemma smaller_prefix_suffix<T(==)>(P: seq<T>, k:nat, pik:nat)
    requires 0 <= pik <= k < |P|
    requires prefix_suffix(P, k)
    requires prefix_suffix(P[..k], pik)
    ensures prefix_suffix(P, pik)
{}

lemma subsubseq<T(==)>(S: seq<T>, i:nat, j:nat)
    requires 0 <= i <= j <= |S|
    ensures S[..j][..i] == S[..i]
{}

predicate lps<T(==)>(S: seq<T>, k:nat)
    requires 0 <= k <= |S|
{
    (|S| == 0 || k < |S|) &&
    prefix_suffix(S, k) &&
    forall k' :: k <= k' < |S| ==> !prefix_suffix(S, k')
}

lemma larger_lps<T(==)>(P:seq<T>, k:nat, q:nat)
    requires 0 <= k < q < |P|
    requires lps(P[..q-1], k)
    requires P[q] == P[k]
    ensures lps(P[..q], k+1)
{}

method PrefixFunction<T(==)>(P: seq<T>) returns (pi: array<int>)
    requires |P| > 1

    ensures pi.Length == |P|
    ensures forall i :: 0 <= i < |P| ==> 0 <= pi[i] <= i
    ensures forall i :: 0 <= i < |P| ==> lps(P[..i], pi[i])
{
    pi := new int[|P|];
    pi[0] := 0;
    var q := 1;
    var k := 0;
    while q < pi.Length
        decreases pi.Length - q

        invariant pi.Length == |P|

        invariant 0 < q <= pi.Length
        invariant 0 <= k <= q <= |P|
        invariant forall i :: 0 <= i < q ==> 0 <= pi[i] <= i
        invariant forall i :: 0 <= i < q ==> lps(P[..i], pi[i])
    {
        k := pi[q - 1];

        while k > 0 && P[k] != P[q]
            decreases k
            invariant 0 <= k < q
            invariant k <= q-1
            invariant forall i :: 0 <= i < q ==> 0 <= pi[i] <= i
            invariant forall i :: 0 <= i < q ==> lps(P[..i], pi[i])
            invariant prefix_suffix(P[..q-1], k)
        {
            subsubseq(P, k, q-1);
            smaller_prefix_suffix(P[..q-1], k, pi[k]);
            k := pi[k - 1];
        }

        assert prefix_suffix(P[..q-1], k);

        if P[k] == P[q] {
            larger_lps(P, k, q);
            k := k + 1;
        }

        pi[q] := k;
        q := q + 1;
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
   var lsp := PrefixFunction(P);
   var i, j := 0, 0;
    while j < |P| && i < |T|
        decreases |T| - i

        invariant 0 <= j <= |P|
        invariant j <= i <= |T|
        invariant T[i-j..i] == P[..j]
        invariant forall k :: 0 <= k < i - j ==> !match_at(T, P, k)
    {
        while j > 0 && j < |P| && T[i] != P[j]
            decreases j

            invariant 0 <= j <= |P|
            invariant j <= i <= |T|
            //invariant T[i-j..i] == P[..j]
            //invariant forall k :: 0 <= k < i - j ==> !match_at(T, P, k)   
        {
            j := lsp[j-1];
        }

        if T[i] == P[j] {
            j := j + 1;
        }

        i := i + 1;
    }
    m := j == |T|;
    pos := i - j;
}