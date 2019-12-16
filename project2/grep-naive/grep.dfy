/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the "naive" string matching algorithm.
 *
 */

include "Io.dfy"
include "FileUtils.dfy"

predicate method match_at<T(==)>(t: seq<T>, p:seq<T>, pos:nat)
    requires 0 <= pos < |t|
{
    pos + |p| <= |t| && p == t[pos..pos+|p|]
}

predicate any_match<T(==)>(t: seq<T>, p:seq<T>, pos:nat)
  decreases t
  requires 0 <= pos <= |t|
{
  exists i :: 0 <= i < pos && match_at(t, p, i)
}


method first_match(t: seq<byte>, p:seq<byte>) returns (found: bool, s:nat)
  requires |t| != 0

  ensures any_match(t, p, |t|) <==> found
  ensures found ==> 0 <= s < |t|
  ensures !found ==> 0 <= s <= |t|
  ensures found ==> match_at(t, p, s)
  ensures forall k :: 0 <= k < s ==> !match_at(t, p, k)
{
  s := 0;
  found := false;
  while s < |t|
    decreases |t| - s
    invariant s <= |t|
    invariant forall k :: 0 <= k < s ==> !match_at(t, p, k)
    invariant !any_match(t, p, s)
  {
    if match_at(t, p, s) {
      found := true;
      return;
    }

    s := s + 1;
  }
}

method Grep(file: FileStream, length: int32, pattern: seq<byte>) returns (ok:bool, found: bool, s:nat)
  requires FileOk(file)
  requires length as int == len(file)

  modifies file
  modifies file.env.ok
  modifies file.env.files

  ensures ok ==> FileOk(file)
  ensures ok ==> found ==> 0 <= s < |content(file)|
  ensures ok ==> !found ==> 0 <= s <= |content(file)|
  ensures ok ==> found ==> match_at(content(file), pattern, s)
  ensures ok ==> forall k :: 0 <= k < s ==> !match_at(content(file), pattern, k)
{
  var cont;
  ok, cont := ReadFile(file, length as nat32);
  if (!ok) {
    return;
  }

  if (|cont| == 0) {
    print "NO\n";
    found := false;
    s := 0;
    return;
  }

  found, s := first_match(cont, pattern);
  
}

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  modifies env.ok
  modifies env.files
{
  var num_args := HostConstants.NumCommandLineArgs(env);

  if (num_args != 3) {
    print "Expected usage: grep <file>\n";
    return;
  }

  var pattern := HostConstants.GetCommandLineArg(1, env);
  var source := HostConstants.GetCommandLineArg(2, env);
  var source_exists := FileStream.FileExists(source, env);

  if (!source_exists) {
    print ("Source file does not exist.\n");
    return;
  }

  var ok1, src_file := FileStream.Open(source, env);
  if (!ok1) {
    print "Error while opening source file.\n";
    return;
  }

  var ok2, src_len := FileStream.FileLength(source, env);
  if (!ok2) {
    print "Error while opening source file.\n";
    return;
  }

  var ok, m, n := Grep(src_file, src_len, seqa2seqb(pattern[..]));
}

function method {:verify false} seqa2seqb(s: seq<char>): seq<byte>
  decreases s
{
  if s == [] then [] else [s[0] as byte] + seqa2seqb(s[1..])
}