module param {
    function method {:opaque} B() : (r: int)
        ensures r >= 1;
    {
        64
    }

 	type word = i:int | 0 <= i < B()
    type dword = i:int | 0 <= i < B() * B()

    function method {:opaque} dword_lh(x: dword) : word 
    {
        x % B()
    }

    function method {:opaque} dword_uh(x: dword) : word
    {
        x / B()
    }

    lemma dword_split_lemma(x: dword)
        ensures dword_lh(x) + dword_uh(x) * B() == x;
    {
        reveal dword_lh();
        reveal dword_uh();
    }

    lemma dword_mul_lemma(a: dword, a0: word, a1: word, b: dword, b0: word, b1: word)
        requires a0 == dword_lh(a);
        requires a1 == dword_uh(a);
        requires b0 == dword_lh(b);
        requires b1 == dword_uh(b);
        ensures a0 * b0 + a1 * b0 * B() + a0 * b1 * B() + a1 * b1 * B() * B() == a * b;
    {
        dword_split_lemma(a);
        dword_split_lemma(b);
    }
}