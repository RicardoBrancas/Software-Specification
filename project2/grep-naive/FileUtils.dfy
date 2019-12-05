include "Io.dfy"
include "Utils.dfy"

predicate FileOk(f: FileStream)
    reads f
    reads f.env
    reads f.env.ok
    reads f.env.files
{   
    f.env.Valid() &&
    f.env.ok.ok() &&
    f.IsOpen() &&
    f.env.files != null &&
    f.Name() in f.env.files.state()
}

function len(f: FileStream): nat
    requires FileOk(f)
    reads f
    reads f.env
    reads f.env.ok
    reads f.env.files
    ensures FileOk(f)
{
  |content(f)|
}

function content(f: FileStream): seq<byte>
    requires FileOk(f)
    reads f
    reads f.env
    reads f.env.ok
    reads f.env.files
    ensures FileOk(f)
{
  f.env.files.state()[f.Name()]
}

method ReadFile(f: FileStream, length: nat32) returns (ok: bool, result: seq<byte>)
    requires FileOk(f)
    requires length as nat == len(f)

    modifies f
    modifies f.env.ok
    modifies f.env.files

    ensures ok ==> FileOk(f)
    ensures ok ==> result == content(f)
    ensures f.env == old(f.env)
    ensures ok ==> f.env.files.state() == old(f.env.files.state())
    ensures f.Name() == old(f.Name())
{
    var buffer := new byte[length];
    ok := f.Read(0, buffer, 0, length as int32);
    if (!ok) {
        return;
    }

    result := buffer[..];
}

method WriteFile(f: FileStream, s: seq<byte>) returns (ok: bool)
    requires FileOk(f)
    requires -0x80000000 <= |s| < 0x80000000
    requires len(f) == 0

    modifies f
    modifies f.env.ok
    modifies f.env.files

    ensures ok ==> FileOk(f)
    ensures ok ==> len(f) == |s|
{
    var buffer := ArrayFromSeq(s);
    ok := f.Write(0, buffer, 0, |s| as int32);
    if (!ok) {
        return;
    }
}

method ReadLine(f: seq<byte>, start: nat) returns (next: nat, line:seq<byte>)
    requires 0 <= start < |f|

    ensures start < next <= |f|
    ensures next == |f| || f[next-1] == '\n' as byte
    ensures line == f[start..next]
    ensures forall k :: start <= k < next-1 ==> f[k] != '\n' as byte
{
    next := start;
    line := [];
    while (next < |f| && f[next] != '\n' as byte)
        decreases |f| - next
        invariant start <= next <= |f|
        invariant line == f[start..next]
        invariant '\n' as byte !in f[start..next]
    {
        line := line + [f[next]];
        next := next + 1;
    }

    if (next < |f| && f[next] == '\n' as byte) {
        line := line + [f[next]];
        next := next + 1;
    }
}

method ReadLines(f: seq<byte>) returns (lines: List<seq<byte>>)
    ensures concat(lines) == f
    //ensures size(lines) == count(f, '\n' as byte) + 1
{
    lines := Nil;
    var next := 0;
    var line := [];
    while (next != |f|)
        decreases |f| - next
        invariant next <= |f|
        invariant concat(lines) == f[..next]
        //invariant size(lines) == count(f[..next], '\n' as byte)
    {
        next, line := ReadLine(f, next);
        concat_unit(lines, line);
        lines := append(lines, Cons(line, Nil));
    }
}