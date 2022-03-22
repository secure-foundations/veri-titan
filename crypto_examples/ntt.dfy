include "../std_lib/src/NonlinearArithmetic/Power.dfy"
include "../std_lib/src/NonlinearArithmetic/DivMod.dfy"

module ntt {
    import opened Power
    import opened DivMod

    const G: nat := 7 // 256-th root of unity
    const Q: nat := 12289

    type elem = i :nat | i < Q

    // datatype elem = elem(n: nat, pow: nat)

    function method modmul(a: elem, b: elem): elem
    {
        (a * b) % Q
    }

    function method modpow(a: elem, b: nat): elem
    {
        Pow(a, b) % Q
    }

    function method Pow2(e: nat): nat
    {
        LemmaPowPositive(2, e);
        Pow(2, e)
    }

    lemma Pow2Properties1(i: nat)
        ensures i == 0 ==> Pow2(i) == 1;
        ensures i == 1 ==> Pow2(i) == 2;
        ensures i > 1 ==> Pow2(i) % 2 == 0;

    lemma Pow2Properties2(i: nat, j: nat)
        requires j <= i;
        ensures 1 <= Pow(2, j);
        ensures Pow(2, i) % Pow(2, j) == 0;

    method fft(a: seq<elem>, logn: nat, omega: elem) returns (y: seq<elem>)
        requires 1 <= |a| == Pow2(logn)
        requires logn <= 8
        requires |a| == 1 || |a| % 2 == 0
        requires Pow2(8) % |a| == 0
        requires omega == modpow(G, Pow2(8 - logn))
        decreases logn
    {
        var len := |a|;
        if |a| == 1 {
            return a;
        }
        assert logn != 0 by {
            LemmaPow0(2);
        }

        assert Pow(2, logn-1) * 2 == Pow(2, logn) by {
            reveal Pow();
        }
        var len' := len / 2;
        var a_e := seq(len', n requires 0 <= n < len' => a[n * 2]);
        var a_o := seq(len', n requires 0 <= n < len' => a[n * 2 + 1]);

        var omega' := modmul(omega, omega);
        assume omega' == modpow(G, Pow2(8 - logn + 1));

        assert len' % 2 == 0 || len' == 1 by {
            Pow2Properties1(logn - 1);
        }

        assert Pow2(8) % len' == 0 by {
            Pow2Properties2(8, logn - 1);
        }


        var y_e := fft(a_e, logn-1, omega');
        var y_o := fft(a_o, logn-1, omega');
        
        // var omega := 
    }


}

