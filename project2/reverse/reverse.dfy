/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"
include "FileUtils.dfy"

method Reverse(source: FileStream, src_len: int32, dest: FileStream) returns (ok: bool)
  requires FileOk(source)
  requires FileOk(dest)
  requires src_len as int == len(source)
  requires len(dest) == 0

  modifies source
  modifies source.env.ok
  modifies source.env.files
  modifies dest
  modifies dest.env.ok
  modifies dest.env.files

  ensures ok ==> FileOk(source)
  ensures ok ==> FileOk(dest)
  ensures ok ==> lines(content(dest)) == reverse(lines(content(source))) 
{
  var content;
  ok, content := ReadFile(source, src_len as nat32);
  if (!ok) {
    return;
  }

  var lines := lines(content);
  var reversed_seq := concat(reverse(lines));
  var reversed := ArrayFromSeq(reversed_seq);
  reverse_concat_keeps(lines);
  ok := dest.Write(0, reversed, 0, |reversed_seq| as int32);
}

method {:main} Main(ghost env: HostEnvironment?) returns (ok: bool)
  requires env != null && env.Valid() && env.ok.ok()
  requires |env.constants.CommandLineArgs()| == 3
  requires env.constants.CommandLineArgs()[1] in env.files.state()
  requires env.constants.CommandLineArgs()[2] in env.files.state()
  requires |env.files.state()[env.constants.CommandLineArgs()[2]]| == 0

  modifies env.ok
  modifies env.files

  ensures ok ==> env.constants.CommandLineArgs()[1] in env.files.state()
  ensures ok ==> env.constants.CommandLineArgs()[2] in env.files.state()
  ensures ok ==> lines(env.files.state()[env.constants.CommandLineArgs()[2]]) == reverse(lines(env.files.state()[env.constants.CommandLineArgs()[1]]))
{
  var source := HostConstants.GetCommandLineArg(1, env);
  var dest := HostConstants.GetCommandLineArg(2, env);

  var src_file, dst_file;
  var src_len;

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
}

