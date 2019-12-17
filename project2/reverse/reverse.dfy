/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"
include "FileUtils.dfy"

predicate is_rev_stream(s1: seq<byte>, s2: seq<byte>)
{
  s1 == join(reverse(lines(s2)))
}

function method {:verify false} lines(s: seq<byte>): seq<seq<byte>>
    decreases s
{
  if s == [] then []
  else
    var nextl := next_line(s);
    if nextl == [] then [] else [nextl] + lines(s[|nextl|+1..])
}

function method {:verify false} next_line(s: seq<byte>): seq<byte>
  decreases s
  requires 0 < |s|
  ensures 0 < |next_line(s)|
{
  if s[0] != 10 then [s[0]] + next_line(s[1..]) else []
}

function method {:verify false} join(s: seq<seq<byte>>): seq<byte>
  decreases s
{
  if s == [] then []
  else s[0] + [10] + join(s[1..])
}

lemma {:verify false} join_lines_same_size(s:seq<byte>)
  ensures |s| == |join(reverse(lines(s)))|
{}

function method reverse<T>(s: seq<T>): seq<T>
  decreases s
  ensures |s| == |reverse(s)|
  ensures forall i :: 0 <= i < |s| ==> s[i] == reverse(s)[|s|-1-i]
{
  if s == [] then []
  else [s[|s| - 1]] + reverse(s[..|s|-1])
}

method Reverse(source: FileStream, src_len: int32, dest: FileStream) returns (ok: bool)
  requires FileOk(source)
  requires FileOk(dest)
  requires src_len as int == len(source)
  requires len(dest) == 0
  requires len(source) > 0

  modifies source
  modifies source.env.ok
  modifies source.env.files
  modifies dest
  modifies dest.env.ok
  modifies dest.env.files

  ensures ok ==> FileOk(source)
  ensures ok ==> FileOk(dest)
  ensures ok ==> is_rev_stream(content(dest), content(source))
{
  var f_content;
  ok, f_content := ReadFile(source, src_len as nat32);
  if (!ok) {
    return;
  }

  var ls := lines(f_content);
  var reversed_seq := join(reverse(ls));
  var reversed := ArrayFromSeq(reversed_seq);
  join_lines_same_size(f_content);
  ok := dest.Write(0, reversed, 0, |reversed_seq| as int32);
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  requires |env.constants.CommandLineArgs()| == 3
  requires env.constants.CommandLineArgs()[1] in env.files.state()
  requires env.constants.CommandLineArgs()[2] in env.files.state()
  requires |env.files.state()[env.constants.CommandLineArgs()[1]]| > 0
  requires |env.files.state()[env.constants.CommandLineArgs()[2]]| == 0

  // note assert in the end of the method

  modifies env.ok
  modifies env.files
{
  var source := HostConstants.GetCommandLineArg(1, env);
  var dest := HostConstants.GetCommandLineArg(2, env);

  var src_file, dst_file;
  var src_len;

  var ok;

  ok, src_file := FileStream.Open(source, env);
  if (!ok) {
    print "Error while opening source file.\n";
    return;
  }

  ok, dst_file := FileStream.Open(dest, env);
  if (!ok) {
    print "Error while opening destination file.\n";
    return;
  }

  ok, src_len := FileStream.FileLength(source, env);
  if (!ok) {
    print "Error while getting length of source file.\n";
    return;
  }

  ok := Reverse(src_file, src_len, dst_file);

  assert ok ==> is_rev_stream(content(dst_file), content(src_file));

  if (!ok) {
    print "Error while reversing/writing.\n";
    return;
  }
}

