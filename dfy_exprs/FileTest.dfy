// https://github.com/wilcoxjay/notes

include "Fileio.dfy"

// Useful to convert Dafny strings into arrays of characters.
method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
  a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

method {:main} Main(ghost env: HostEnvironment)
  requires env.ok.ok()
  modifies env.ok
{
    var fname := ArrayFromSeq("foo.txt");
    var f: FileStream;
    var ok: bool;
    ok, f := FileStream.Open(fname, env);

    // Try commenting out the following line to see that you are forced to handle errors!
    if !ok { print "open failed\n"; return; }

    var buffer:array<byte> := new byte[20];
    ok := f.Read(0, buffer, 0, 20);

    // print buffer[0], buffer[1];

    if !ok { print "read failed\n"; return; }

    ok := f.Close();
    // // This is "hello world!" in ascii.
    // // The library requires the data to be an array of bytes, but Dafny has no char->byte conversions :(
    // var data: array<byte> := ArrayFromSeq([104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 33, 10]);

    // ok := f.Write(0, data, 0, data.Length as int32);

    print "done!\n";
}

