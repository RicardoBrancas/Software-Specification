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