/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the Knuth-Morris-Pratt algorithm.
 *
 */

include "Io.dfy"
include "FileUtils.dfy"
include "kmp.dfy"

method Grep(file: FileStream, length: int32, pattern: seq<byte>) returns (ok:bool, found: bool, s:nat)
  requires FileOk(file)
  requires length as int == len(file)

  modifies file
  modifies file.env.ok
  modifies file.env.files

  ensures ok ==> FileOk(file)
  ensures ok ==> found ==> 0 <= s < |content(file)|
  ensures ok ==> !found ==> 0 <= s <= |content(file)|
  ensures ok ==> found ==> matches(content(file), s, pattern, 0, |pattern|)
  ensures ok ==> forall k :: 0 <= k < s ==> !matches(content(file), k, pattern, 0, |pattern|)
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

  if (|pattern| == 0) {
    print "YES: 0\n";
    found := true;
    s := 0;
    return;
  }

  found, s := Match(cont, pattern);
}

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  modifies env.ok
  modifies env.files
{
  var num_args := HostConstants.NumCommandLineArgs(env);
  var ok;

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

  var src_file;
  ok, src_file := FileStream.Open(source, env);
  if (!ok) {
    print "Error while opening source file.\n";
    return;
  }

  var src_len;
  ok, src_len := FileStream.FileLength(source, env);
  if (!ok) {
    print "Error while opening source file.\n";
    return;
  }

  var found, pos;
  ok, found, pos := Grep(src_file, src_len, seqa2seqb(pattern[..]));

  if !ok {
    print("Error while greping.\n");
    return;
  }

  if (found) {
    print "YES: ";
    print pos;
    print "\n";
  } else {
    print "NO\n";
  }
}

function method {:verify false} seqa2seqb(s: seq<char>): seq<byte>
  decreases s
{
  if s == [] then [] else [s[0] as byte] + seqa2seqb(s[1..])
}