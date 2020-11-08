// https://github.com/wilcoxjay/notes

using System;
using System.Numerics;
using System.Diagnostics;
using System.Threading;
using System.Collections.Concurrent;
using System.Collections.Generic;
using FStream = System.IO.FileStream;
using UClient = System.Net.Sockets.UdpClient;
using IEndPoint = System.Net.IPEndPoint;


namespace _module {

public partial class FileStream
{
    internal FStream fstream;
    internal FileStream(FStream fstream) { this.fstream = fstream; }

    public static void Open(char[] name, out bool ok, out FileStream f)
    {
        try
        {
            f = new FileStream(new FStream(new string(name), System.IO.FileMode.OpenOrCreate, System.IO.FileAccess.ReadWrite));
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            f = null;
            ok = false;
        }
    }

    public bool Close()
    {
        try
        {
            fstream.Close();
            return true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            return false;
        }
    }

    public bool Read(int fileOffset, byte[] buffer, int start, int end)
    {
        try
        {
            fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
            fstream.Read(buffer, start, end - start);
            return true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            return false;
        }
    }

    public bool Write(int fileOffset, byte[] buffer, int start, int end)
    {
        try
        {
            fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
            fstream.Write(buffer, start, end - start);
            return true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            return false;
        }
    }

    public void Flush(out bool ok)
    {
        try
        {
            fstream.Flush();
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            ok = false;
        }
    }
}


}
