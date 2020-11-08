// https://github.com/wilcoxjay/notes

using System;
// using FStream = System.IO.FileStream;

namespace _module {

public partial class SystemFFI
{
    public static byte[] GetRandomBV(int length)
    {
        // String s = String.Format("[INPUT]{0}:{1}:", new string(name), length);
        // Console.Write(s);

        byte[] result = new byte[length];
        Random rnd = new Random();

        for (int i = 0; i < length; i++) 
        {
            result[i] = (byte) rnd.Next(0, 2);
            // Console.Write(result[i]);
        }

        // Console.WriteLine();
        return result;
    }

    public static byte GetRandomBit()
    {
        Random rnd = new Random();
        return (byte) rnd.Next(0, 2);
    }

    // public static void Open(char[] name, out bool ok, out FileStream f)
    // {
    //     try
    //     {
    //         f = new FileStream(new FStream(new string(name), System.IO.FileMode.OpenOrCreate, System.IO.FileAccess.ReadWrite));
    //         ok = true;
    //     }
    //     catch (Exception e)
    //     {
    //         System.Console.Error.WriteLine(e);
    //         f = null;
    //         ok = false;
    //     }
    // }

    // public bool Close()
    // {
    //     try
    //     {
    //         fstream.Close();
    //         return true;
    //     }
    //     catch (Exception e)
    //     {
    //         System.Console.Error.WriteLine(e);
    //         return false;
    //     }
    // }

    // public bool Read(int fileOffset, byte[] buffer, int start, int end)
    // {
    //     try
    //     {
    //         fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
    //         fstream.Read(buffer, start, end - start);
    //         return true;
    //     }
    //     catch (Exception e)
    //     {
    //         System.Console.Error.WriteLine(e);
    //         return false;
    //     }
    // }

    // public bool Write(int fileOffset, byte[] buffer, int start, int end)
    // {
    //     try
    //     {
    //         fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
    //         fstream.Write(buffer, start, end - start);
    //         return true;
    //     }
    //     catch (Exception e)
    //     {
    //         System.Console.Error.WriteLine(e);
    //         return false;
    //     }
    // }

    // public void Flush(out bool ok)
    // {
    //     try
    //     {
    //         fstream.Flush();
    //         ok = true;
    //     }
    //     catch (Exception e)
    //     {
    //         System.Console.Error.WriteLine(e);
    //         ok = false;
    //     }
    // }
}


}
