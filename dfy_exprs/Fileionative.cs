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
}


}
