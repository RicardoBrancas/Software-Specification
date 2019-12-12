/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the "naive" string matching algorithm.
 *
 */

include "Io.dfy"
include "FileUtils.dfy"

function method match_at(t: seq<byte>, p:seq<byte>, t_pos:nat): bool
    requires 0 <= t_pos < |t|
{
    p <= t[t_pos..]
}

method first_match(t: seq<byte>, p:seq<byte>) returns (found: bool, s:nat)
  requires |t| != 0
  ensures found ==> 0 <= s < |t|
  ensures !found ==> 0 <= s <= |t|
  ensures found ==> match_at(t, p, s)
  ensures forall k :: 0 <= k < s ==> !match_at(t, p, k)
{
  s := 0;
  found := false;
  while s < |t| - |p|
    decreases |t| - s
    invariant s <= |t|
    invariant forall k :: 0 <= k < s ==> !match_at(t, p, k)
  {
    if match_at(t, p, s) {
      found := true;
      return;
    }
    s := s + 1;
  }
}

method Grep(file: FileStream, length: int32, pattern: seq<byte>)
  requires FileOk(file)
  requires length as int == len(file)

  modifies file
  modifies file.env.ok
  modifies file.env.files
{
  var ok, cont := ReadFile(file, length as nat32);
  if (!ok) {
    return;
  }

  if (|cont| == 0) {
    print "NO\n";
    return;
  }

  var m, n := first_match(cont, pattern);
  if (m) {
    print "YES: ";
    print n;
    print "\n";
  } else {
    print "NO\n";
  }
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

  Grep(src_file, src_len, seqa2seqb(pattern[..]));
}

function method {:verify false} seqa2seqb(s: seq<char>): seq<byte>
{
  if s == [] then [] else [s[0] as byte] + seqa2seqb(s[1..])
}