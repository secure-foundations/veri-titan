include "bvop/bv_op.s.dfy"
// include "crypto/pow2.s.dfy"

module SetOfMaps {
    predicate {:opaque} keysDisjoint<K, V>(ms: set<map<K, V>>)
    {
        forall m1, m2 | (m1 in ms && m2 in ms && m1 != m2)
            :: m1.Keys !! m2.Keys
    }

    function flattenMaps<K,V>(ms: set<map<K, V>>): map<K, V>
        requires keysDisjoint(ms)
    {
        reveal keysDisjoint();
        map m, k | (m in ms && k in m) :: k := m[k]
    }

    lemma flattenMapsElemSufLemma<K,V>(ms: set<map<K, V>>, k: K)
        returns (m: map<K, V>)
        requires keysDisjoint(ms)
        requires k in flattenMaps(ms)
        ensures m in ms && k in m
        ensures m[k] == flattenMaps(ms)[k]
    {
        reveal keysDisjoint();
        m :| m in ms && k in m;
        assert flattenMaps(ms)[k] == m[k];
    }

    lemma flattenMapsElemNecLemma<K,V>(ms: set<map<K, V>>, m: map<K, V>, k: K)
        requires keysDisjoint(ms)
        requires m in ms && k in m
        ensures k in flattenMaps(ms)
        ensures m[k] == flattenMaps(ms)[k]
    {
    }

    lemma flattenMapsUpdateLemma<K,V>(ms: set<map<K, V>>, ms': set<map<K, V>>,
        n: map<K,V>, n': map<K,V>, k: K, v: V)
        requires keysDisjoint(ms)
        requires keysDisjoint(ms')
        requires n in ms
        requires n' in ms'
        requires ms' == ms - {n} + {n'}
        requires k in n
        requires k in n'
        requires n'[k] == v
        requires n' == n[k := v]
        ensures flattenMaps(ms') == flattenMaps(ms)[k := v]
    {
        reveal keysDisjoint();
        var m := flattenMaps(ms);
        var m' := flattenMaps(ms');

        forall key | key in m'
            ensures key in m
            ensures key != k ==> m[key] == m'[key]
            ensures key == k ==> m[key] == n'[key]
        {
            var _ := flattenMapsElemSufLemma(ms, key);
            var _ := flattenMapsElemSufLemma(ms', key);
        }

        assert m' == m[k := v];
    }
}

module flat {
    import opened integers
    import Power

    import opened SetOfMaps

    datatype flat_t = flat_t(raw: map<nat, uint8>, max: nat)
    {
        predicate {:opaque} inv()
        {
            && max != 0
            && (forall addr | addr in raw :: addr < max)
        }

        function method do_read(ptr: nat): uint8
            requires inv()
        {
            if ptr in raw then raw[ptr] else 0 
        }

        function method do_write(ptr: nat, value: uint8): flat_t
            requires inv()
            requires ptr < max;
            ensures inv()
        {
            reveal inv();
            var raw' := if ptr in raw then raw[ptr := value] else raw;
            this.(raw := raw')
        }
    }

    datatype regions_t = regions_t(regions: map<nat, seq<uint8>>, max: nat)
    {
        predicate valid_region_index(base: nat, i: nat)
        {
            && base in regions
            && 0 <= i < |regions[base]|
        }

        function do_read_(base: nat, i: nat): uint8
            requires valid_region_index(base, i)
        {
            regions[base][i]
        }

        function do_write_(base: nat, i: nat, value: uint8): regions_t
            requires valid_region_index(base, i)
        {
            var region' := regions[base][i := value];
            var regions' := regions[base := region'];
            this.(regions := regions')
        }

        predicate region_inv(base: nat)
            requires base in regions
        {
            && var len := |regions[base]|;
            && len != 0
            && base + len < max
            && (forall i | 1 <= i < len ::
                (base + i) !in regions)
        }

        predicate {:opaque} inv()
        {
            && max != 0
            && (forall base | base in regions ::
                region_inv(base))
        }

        function region_as_raw(base: nat): (f: map<nat, uint8>)
            requires base in regions
        {
            map k | base <= k < base + |regions[base]| ::
                do_read_(base, k - base)
        }

        function regions_as_raws_(): set<map<nat, uint8>>
        {
            set base | base in regions :: region_as_raw(base)
        }

        lemma region_indices_disjoint_lemma(base1: nat, i: nat, base2: nat, j: nat)
            requires inv()
            requires valid_region_index(base1, i);
            requires valid_region_index(base2, j);
            requires base1 != base2
            ensures base1 + i != base2 + j
        {
            assert region_inv(base1) && region_inv(base2) by {
                reveal inv();
            }

            if base1 + i == base2 + j {
                var buff1 := regions[base1];
                var buff2 := regions[base2];

                if base1 > base2 {
                    assert region_inv(base2);
                    var k := j - i;
                    assert base1 == base2 + k;
                    assert 0 <= k < |buff2|;
                    assert base1 !in regions;
                    assert false;
                } else {
                    assert region_inv(base1);
                    var k := i - j;
                    assert base2 == base1 + k;
                    assert 0 <= k < |buff1|;
                    assert base2 !in regions;
                    assert false;
                }
            }
        }

        predicate disjoint_regions(base1: nat, base2: nat)
        {
            && base1 in regions
            && base2 in regions
            && base1 != base2
        }

        lemma region_properties_lemma()
            requires inv()
            ensures keysDisjoint(regions_as_raws_())
            ensures forall k, m | (m in regions_as_raws_() && k in m) :: k < max
        {
            reveal keysDisjoint();
            forall base1 , base2 | disjoint_regions(base1, base2)
                ensures region_as_raw(base1).Keys !! region_as_raw(base2).Keys
            {
                var m1 := region_as_raw(base1).Keys;
                var m2 := region_as_raw(base2).Keys;

                if !(m1 !! m2) {
                    var k :| k in m1 && k in m2;
                    var i :| k == i + base1;
                    var j :| k == j + base2;
                    region_indices_disjoint_lemma(base1, i, base2, j);
                }
            }
            reveal inv();
        }

        function regions_as_raws(): (rs: set<map<nat, uint8>>)
            requires inv();
            ensures keysDisjoint(rs)
        {
            region_properties_lemma();
            regions_as_raws_()
        }

        function {:opaque} as_flat(): (f: flat_t)
            requires inv()
            ensures f.inv()
            ensures f.max == max
        {
            var rs := flattenMaps(regions_as_raws());
            var f := flat_t(rs, max);
            assert f.inv() by {reveal inv(); reveal f.inv();}
            f
        }

        lemma valid_region_index_bound_lemma(base: nat, i: nat)
            requires inv()
            requires valid_region_index(base, i)
            ensures base + i < max
        {
            reveal inv();
        }

        lemma do_read_lemma(base: nat, i: nat)
            requires inv()
            requires valid_region_index(base, i)
            ensures do_read_(base, i) == as_flat().do_read(base + i)
        {
            reveal keysDisjoint();
            var raw := as_flat().raw;
            var raws := regions_as_raws();
            valid_region_index_bound_lemma(base, i);
            var rraw := region_as_raw(base);

            flattenMapsElemNecLemma(raws, rraw, base + i);
            reveal as_flat();
        }

        function do_read(base: nat, i: nat): (v: uint8)
            requires inv()
            requires valid_region_index(base, i)
            ensures v == as_flat().do_read(base + i)
        {
            do_read_lemma(base, i);
            do_read_(base, i)
        }

        lemma do_write_lemma(base: nat, i: nat, value: uint8)
            requires inv()
            requires valid_region_index(base, i)
            ensures var that := do_write_(base, i, value);
                && that.inv()
                && base + i < max
                && that.as_flat() == as_flat().do_write(base + i, value)
        {
            var that := do_write_(base, i, value);

            assert that.inv() by {
                reveal inv();

                forall base1 | base1 in that.regions
                    ensures that.region_inv(base)
                {
                    if base1 != base {
                        assert that.regions[base1] == regions[base1];
                    } else {
                        var region' := regions[base][i := value];
                        assert that.regions[base] == region';
                    }
                }
            }

            var raws := regions_as_raws();
            var raw := flattenMaps(raws);
            var raws' := that.regions_as_raws();
            var raw' := flattenMaps(raws');
            var ptr :nat := base + i;

            var rr := region_as_raw(base);
            var rr' := that.region_as_raw(base);

            assert raws' == raws - {rr} + {rr'} 
                && rr in raws 
                && rr' in raws' 
                && rr' == rr[ptr := value] by {
                forall base' | base' in that.regions
                    ensures base' in regions;
                    ensures base' != base ==>
                        that.region_as_raw(base') == region_as_raw(base');
                    ensures base' == base ==>
                        that.region_as_raw(base) == rr[i + base := value];
                {
                    var region := regions[base'];
                    var region' := that.regions[base'];
                    if base' != base {
                        assert region' == region;
                        assert that.region_as_raw(base') == region_as_raw(base');
                    } else {
                        assert region' == region[i := value];
                        assert rr' == rr[i + base := value];
                    }
                }
            }

            assert raw' == raw[ptr := value] by {
                flattenMapsUpdateLemma(raws, raws', rr, rr', ptr, value);
            }

            valid_region_index_bound_lemma(base, i);

            assert raw' == that.as_flat().raw by {
                reveal that.as_flat();
            }

            assert raw == as_flat().raw by {
                reveal as_flat();
            }

            assert that.as_flat() == as_flat().do_write(ptr, value);
        }
    }
}
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
        //     ensures valid_region_index(base, i)
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
        //     ensures valid_region_index(base, addr-base)
        //     ensures addr == i + base
        //     ensures region_as_raw(base)[addr] == regions[base][i]
        // {
        //     assert base <= addr < base + |regions[base]|;
        //     i := addr - base;
        //     assert valid_region_index(base, i) && base + i == addr;
        // }

