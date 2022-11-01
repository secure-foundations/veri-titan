include "bvop/bv_op.s.dfy"
include "bvop/bv16_op.s.dfy"
include "bvop/bv32_op.s.dfy"
include "bvop/bv256_op.s.dfy"
// include "crypto/pow2.s.dfy"

abstract module flat_mem_s(BV: bv_op_s) {
    import opened integers
    import BS = BV.BVSEQ

    import Power
    import Mul

    // how many bytes in the word
    const WORD_BYTES: nat

    // how many words in the memory
    const MAX_WORDS: nat

    function MAX_BYTES(): nat 
    {
        Mul.LemmaMulNonnegative(WORD_BYTES, MAX_WORDS);
        WORD_BYTES * MAX_WORDS
    }

    // obligation
    lemma word_size_lemma()
        ensures WORD_BYTES != 0
        ensures Power.Pow(256, WORD_BYTES) == BS.BASE()

    // points to a word with aligment
    predicate ptr_aligned(ptr: nat)
    {
        word_size_lemma();
        && ptr % WORD_BYTES == 0
        && ptr + WORD_BYTES <= MAX_BYTES()
    }

    // aligned adddresses only
    type aptr = i :nat | ptr_aligned(i) witness *

    const STACK_MAX_WORDS: nat

    const STACK_BOT: aptr

    datatype mem_t = mem_cons(
        // the flat memory, 
        flat: map<aptr, BS.uint>,
        // ghost state about memory structure
        ghost split: map<aptr, nat>)
    {
        // single word read/write

        function method read_word(ptr: aptr): BS.uint
        {
            if ptr in flat then flat[ptr] else 0 
        }

        function method write_word(ptr: aptr, value: BS.uint): mem_t
        {
            var flat' := if ptr in flat then flat[ptr := value] else flat;
            mem_cons(flat', split)
        }

        // multi words read/write

        predicate valid_multi_word(ptr: aptr, count: nat)
        {
            ptr + count * WORD_BYTES <= MAX_BYTES()
        }

        // assumptions about the initial memory state

        predicate region_valid(base: nat, len: nat)
        {
            // the addresses are all mapped
            && (forall i | 0 <= i < len :: 
                base + i * WORD_BYTES in flat)
            // the addresses are all bounded
            && base + len * WORD_BYTES < MAX_BYTES()
        }

        predicate inv()
        {
            // stack region
            && STACK_BOT in split
            && split[STACK_BOT] == STACK_MAX_WORDS
            // all the regions are valid
            && (forall base | base in split ::
                region_valid(base, split[base]))
            // regions are disjoint
            && (forall b1, b2 | (b1 in split && b2 in split && b1 != b2) ::
                    (b1 >= b2 + split[b2] || b2 >= b1 + split[b1]))
        }
    }
}


    // datatype regions_t = regions_t(regions:, max: nat)
    // {
    //     predicate region_inv(base: nat)
    //         requires base in regions
    //     {
    //         && var len := |regions[base]|;
    //         && len != 0
    //         && base + len < max
    //         && (forall i | 1 <= i < len ::
    //             (base + i) !in regions)
    //     }

    //     predicate {:opaque} inv()
    //     {
    //         && max != 0
    //         && (forall base | base in regions ::
    //             region_inv(base))
    //     }

    //     function region_as_raw(base: nat): (f: map<nat, uint8>)
    //         requires base in regions
    //     {
    //         map k | base <= k < base + |regions[base]| ::
    //             do_read_(base, k - base)
    //     }

    //     function regions_as_raws_(): set<map<nat, uint8>>
    //     {
    //         set base | base in regions :: region_as_raw(base)
    //     }

    //     lemma region_indices_disjoint_lemma(base1: nat, i: nat, base2: nat, j: nat)
    //         requires inv()
    //         requires region_index_valid(base1, i);
    //         requires region_index_valid(base2, j);
    //         requires base1 != base2
    //         ensures base1 + i != base2 + j
    //     {
    //         assert region_inv(base1) && region_inv(base2) by {
    //             reveal inv();
    //         }

    //         if base1 + i == base2 + j {
    //             var buff1 := regions[base1];
    //             var buff2 := regions[base2];

    //             if base1 > base2 {
    //                 assert region_inv(base2);
    //                 var k := j - i;
    //                 assert base1 == base2 + k;
    //                 assert 0 <= k < |buff2|;
    //                 assert base1 !in regions;
    //                 assert false;
    //             } else {
    //                 assert region_inv(base1);
    //                 var k := i - j;
    //                 assert base2 == base1 + k;
    //                 assert 0 <= k < |buff1|;
    //                 assert base2 !in regions;
    //                 assert false;
    //             }
    //         }
    //     }

    //     predicate disjoint_regions(base1: nat, base2: nat)
    //     {
    //         && base1 in regions
    //         && base2 in regions
    //         && base1 != base2
    //     }

    //     lemma region_properties_lemma()
    //         requires inv()
    //         ensures keysDisjoint(regions_as_raws_())
    //         ensures forall k, m | (m in regions_as_raws_() && k in m) :: k < max
    //     {
    //         reveal keysDisjoint();
    //         forall base1 , base2 | disjoint_regions(base1, base2)
    //             ensures region_as_raw(base1).Keys !! region_as_raw(base2).Keys
    //         {
    //             var m1 := region_as_raw(base1).Keys;
    //             var m2 := region_as_raw(base2).Keys;

    //             if !(m1 !! m2) {
    //                 var k :| k in m1 && k in m2;
    //                 var i :| k == i + base1;
    //                 var j :| k == j + base2;
    //                 region_indices_disjoint_lemma(base1, i, base2, j);
    //             }
    //         }
    //         reveal inv();
    //     }

    //     function regions_as_raws(): (rs: set<map<nat, uint8>>)
    //         requires inv();
    //         ensures keysDisjoint(rs)
    //     {
    //         region_properties_lemma();
    //         regions_as_raws_()
    //     }

    //     function {:opaque} as_flat(): (f: flat_t)
    //         requires inv()
    //         ensures f.inv()
    //         ensures f.max == max
    //     {
    //         var rs := flattenMaps(regions_as_raws());
    //         var f := flat_t(rs, max);
    //         assert f.inv() by {reveal inv(); reveal f.inv();}
    //         f
    //     }

    //     lemma region_index_valid_bound_lemma(base: nat, i: nat)
    //         requires inv()
    //         requires region_index_valid(base, i)
    //         ensures base + i < max
    //     {
    //         reveal inv();
    //     }

    //     lemma do_read_lemma(base: nat, i: nat)
    //         requires inv()
    //         requires region_index_valid(base, i)
    //         ensures do_read_(base, i) == as_flat().do_read(base + i)
    //     {
    //         reveal keysDisjoint();
    //         var raw := as_flat().raw;
    //         var raws := regions_as_raws();
    //         region_index_valid_bound_lemma(base, i);
    //         var rraw := region_as_raw(base);

    //         flattenMapsElemNecLemma(raws, rraw, base + i);
    //         reveal as_flat();
    //     }

    //     function do_read(base: nat, i: nat): (v: uint8)
    //         requires inv()
    //         requires region_index_valid(base, i)
    //         ensures v == as_flat().do_read(base + i)
    //     {
    //         do_read_lemma(base, i);
    //         do_read_(base, i)
    //     }

    //     lemma do_write_lemma(base: nat, i: nat, value: uint8)
    //         requires inv()
    //         requires region_index_valid(base, i)
    //         ensures var that := do_write_(base, i, value);
    //             && that.inv()
    //             && base + i < max
    //             && that.as_flat() == as_flat().do_write(base + i, value)
    //     {
    //         var that := do_write_(base, i, value);

    //         assert that.inv() by {
    //             reveal inv();

    //             forall base1 | base1 in that.regions
    //                 ensures that.region_inv(base)
    //             {
    //                 if base1 != base {
    //                     assert that.regions[base1] == regions[base1];
    //                 } else {
    //                     var region' := regions[base][i := value];
    //                     assert that.regions[base] == region';
    //                 }
    //             }
    //         }

    //         var raws := regions_as_raws();
    //         var raw := flattenMaps(raws);
    //         var raws' := that.regions_as_raws();
    //         var raw' := flattenMaps(raws');
    //         var ptr :nat := base + i;

    //         var rr := region_as_raw(base);
    //         var rr' := that.region_as_raw(base);

    //         assert raws' == raws - {rr} + {rr'} 
    //             && rr in raws 
    //             && rr' in raws' 
    //             && rr' == rr[ptr := value] by {
    //             forall base' | base' in that.regions
    //                 ensures base' in regions;
    //                 ensures base' != base ==>
    //                     that.region_as_raw(base') == region_as_raw(base');
    //                 ensures base' == base ==>
    //                     that.region_as_raw(base) == rr[i + base := value];
    //             {
    //                 var region := regions[base'];
    //                 var region' := that.regions[base'];
    //                 if base' != base {
    //                     assert region' == region;
    //                     assert that.region_as_raw(base') == region_as_raw(base');
    //                 } else {
    //                     assert region' == region[i := value];
    //                     assert rr' == rr[i + base := value];
    //                 }
    //             }
    //         }

    //         assert raw' == raw[ptr := value] by {
    //             flattenMapsUpdateLemma(raws, raws', rr, rr', ptr, value);
    //         }

    //         region_index_valid_bound_lemma(base, i);

    //         assert raw' == that.as_flat().raw by {
    //             reveal that.as_flat();
    //         }

    //         assert raw == as_flat().raw by {
    //             reveal as_flat();
    //         }

    //         assert that.as_flat() == as_flat().do_write(ptr, value);
    //     }
    // }

// module regioned_mem_s(BV: bv_op_s, LM: linear_mem_s(BV)) 
// {
//     type uint = BV.BVSEQ.uint

//     type regions_t =  map<nat, seq<uint>>


//     function do_read_(regions: regions_t, base: nat, i: nat): uint
//         requires region_index_valid(regions, base, i)
//     {
//         regions[base][i]
//     }

//     function do_write_(regions: regions_t, base: nat, i: nat, value: uint): regions_t
//         requires region_index_valid(regions, base, i)
//     {
//         var region' := regions[base][i := value];
//         regions[base := region']
//     }

//     function as_linear(regions: regions_t): LM.mem_t
// }



    // datatype mem_t = mem_cons(heap: ,stack: )



        // lemma regions_disjoint_lemma(base1: nat, base2: nat)
        //     requires inv()
        //     requires disjoint_regions(base1, base2)
        //     ensures region_as_raw(base1).Keys !! region_as_raw(base2).Keys
        // {
        //    var m1 := region_as_raw(base1).Keys;
        //     var m2 := region_as_raw(base2).Keys;

        //     if !(m1 !! m2) {
        //         var k :| k in m1 && k in m2;
        //         var i :| k == i + base1;
        //         var j :| k == j + base2;
        //         region_indices_disjoint_lemma(base1, i, base2, j);
        //     }
        // }

        // lemma address_suf_lemma(addr: nat)
        //     returns (base: nat, i: nat)
        //     requires inv()
        //     requires addr in regions_as_raw()
        //     ensures region_index_valid(base, i)
        //     ensures addr == base + i 
        //     ensures regions_as_raw()[addr] == read_region_index(base, i)
        // {
        //     var rs := regions_as_raws();
        //     var f := flattenMapsElemSufLemma(rs, addr);
        //     base :| (base in regions && region_as_raw(base) == f);
        //     i := read_region_index_lemma(base, addr);
        //     assert addr == i + base;
        //     calc == {
        //         regions[base][i];
        //         f[addr];
        //         regions_as_raw()[addr];
        //     }
        // }

        // lemma do_read_lemma(base: nat, addr: nat)
        //     returns (i: nat)
        //     requires base in regions
        //     requires addr in region_as_raw(base)
        //     ensures addr >= base
        //     ensures region_index_valid(base, addr-base)
        //     ensures addr == i + base
        //     ensures region_as_raw(base)[addr] == regions[base][i]
        // {
        //     assert base <= addr < base + |regions[base]|;
        //     i := addr - base;
        //     assert region_index_valid(base, i) && base + i == addr;
        // }

