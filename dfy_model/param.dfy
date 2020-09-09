module param {
    function method {:opaque} B() : (r: int)
        ensures r >= 1;
    {
        64
    }

 	type word = i:int | 0 <= i < B()
    type dword = i:int | 0 <= i < B() * B()

    lemma dword_split_lemma(x: dword)
        ensures dword_lh(x) + dword_uh(x) * B() == x;
    {
        assert true;
    }

    function method dword_lh(x: dword) : word 
    {
        x % B()
    }

    function method dword_uh(x: dword) : word
    {
        x / B()
    }

    lemma dword_mul_lemma(a: dword, b: dword)
        ensures 
        
    {
        var a0 := dword_lh(a);
        var a1 := dword_uh(a);

        var b0 := dword_lh(b);
        var b1 := dword_uh(b);

        dword_split_lemma(a);
        dword_split_lemma(b);

        assert a0 * b0 + a1 * b0 * B() + a0 * b1 * B() + a1 * b1 * B() * B() == a * b;
    }
}