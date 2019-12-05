/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"
include "FileUtils.dfy"

method Reverse(source: FileStream, src_len: int32, dest: FileStream)
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
{
  var ok, cont := ReadFile(source, src_len as nat32);
  if (!ok) {
    return;
  }

  var lines := ReadLines(cont);
  var reversed := concat(reverse(lines));

  reverse_concat_keeps(lines);

  var ok1 := WriteFile(dest, reversed);
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  modifies env.ok
  modifies env.files
{
  var num_args := HostConstants.NumCommandLineArgs(env);

  if (num_args != 3) {
    print "Expected usage: reverse <source> <destination>\n";
    return;
  }

  var source := HostConstants.GetCommandLineArg(1, env);
  var source_exists := FileStream.FileExists(source, env);

  if (!source_exists) {
    print ("Source file does not exist.\n");
    return;
  }

  var dest := HostConstants.GetCommandLineArg(2, env);
  var dest_exists := FileStream.FileExists(dest, env);

  if(dest_exists) {
    print "Destination file exists! Aborting...\n";
    return;
  }

  var ok1, src_file := FileStream.Open(source, env);
  if (!ok1) {
    print "Error while opening source file.\n";
    return;
  }

  var ok2, dst_file := FileStream.Open(dest, env);
  if (!ok2) {
    print "Error while opening destination file.\n";
    return;
  }

  var ok3, src_len := FileStream.FileLength(source, env);
  if (!ok3) {
    print "Error while opening source file.\n";
    return;
  }

  var ok4, dst_len := FileStream.FileLength(dest, env);
  if (!ok4) {
    print "Error while opening destination file.\n";
    return;
  }

  Reverse(src_file, src_len, dst_file);
}
