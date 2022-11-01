include "flat.s.dfy"

abstract module regions_mem_i(BV: bv_op_s) {
    import opened integers
    import FM = flat_mem_s(BV)
    import BS = FM.BS

    import Mul

    type regions_t = map<nat, seq<BS.uint>>

    predicate region_index_valid(regions: regions_t, base: nat, i: nat)
    {
        && base in regions
        && 0 <= i < |regions[base]|
    }

    function read_region(regions: regions_t, base: nat, i: nat): BS.uint
        requires region_index_valid(regions, base, i)
    {
        regions[base][i]
    }

    function wrtie_region(regions: regions_t, base: nat, i: nat, v: BS.uint): regions_t
        requires region_index_valid(regions, base, i)
    {
        var region' := regions[base][i := v];
        regions[base := region']
    }

    function as_flat_ptr(base: nat, i: nat): nat
    {
        Mul.LemmaMulNonnegative(i, FM.WORD_BYTES);
        base + i * FM.WORD_BYTES
    }

    function build_stack_region(mem: FM.mem_t, base: nat, len: nat): seq<BS.uint>
        requires mem.region_valid(base, len)
    {
        seq(len, i requires 0 <= i < len =>
            mem.flat[as_flat_ptr(base, i)])
    }

    function build_regions(mem: FM.mem_t): regions_t
        requires mem.inv()
    {
        map base | base in mem.split ::
            build_stack_region(mem, base, mem.split[base])
    }

    predicate refines_flat(regions: regions_t, mem: FM.mem_t)
    {
        && mem.inv()
        && regions == build_regions(mem)
    }

    lemma read_refinement_lemma(regions: regions_t, base: nat, i: nat, mem: FM.mem_t)
        requires refines_flat(regions, mem)
        requires region_index_valid(regions, base, i)
        ensures FM.ptr_aligned(as_flat_ptr(base, i))
        ensures read_region(regions, base, i) ==
            mem.read_word(as_flat_ptr(base, i))
    {
        assume false;
    }

    lemma write_refinement_lemma(regions: regions_t, base: nat, i: nat, v: BS.uint, mem: FM.mem_t)
        requires refines_flat(regions, mem)
        requires region_index_valid(regions, base, i)
        ensures FM.ptr_aligned(as_flat_ptr(base, i))
        ensures refines_flat(wrtie_region(regions, base, i, v),
            mem.write_word(as_flat_ptr(base, i), v))
    {
        assume false;
    }
}

abstract module hyper_mem_i(BV: bv_op_s)
{
    import Mul

    import RM = regions_mem_i(BV)
    import FM = RM.FM
    import BS = FM.BS

    function {:fuel 1} rev_concat(fs: seq<seq<BS.uint>>): seq<BS.uint>
        decreases |fs|
    {
        if |fs| == 0 then
            []
        else
            var index := |fs| - 1;
            fs[index] + rev_concat(fs[..index])
    }

    datatype hyper_t = hyper_cons(
        heap: map<FM.aptr, seq<BS.uint>>,
        fs: seq<seq<BS.uint>>,
        free: seq<BS.uint>)
    {
        function build_stack_region(): seq<BS.uint>
        {
            free + rev_concat(fs)
        }

        function build_regions(): RM.regions_t
        {
            heap[FM.STACK_BOT := build_stack_region()]
        }

        predicate refines_flat(mem: RM.FM.mem_t)
        {
            && mem.inv()
            && FM.STACK_BOT !in heap
            && RM.refines_flat(build_regions(), mem)
        }

        function push_frame_(len: nat): hyper_t
            requires 0 <= len < |free|
        {
            var fs' := fs + [free[len..]];
            hyper_cons(heap, fs', free[..len])
        }

        lemma push_refinement_lemma(len: nat)
            requires 0 <= len < |free|
            ensures build_stack_region() == 
                push_frame_(len).build_stack_region()
        {
            var stack' := push_frame_(len);

            calc == {
                stack'.build_stack_region();
                free[..len] + rev_concat(fs + [free[len..]]);
                free[..len] + free[len..] + rev_concat(fs);
                free + rev_concat(fs);
                build_stack_region();
            }
        }

        function pop_frame_(): hyper_t
            requires |fs| != 0
        {
            var index := |fs| - 1;
            hyper_cons(heap, fs[..index], free + fs[index])
        }

        lemma pop_refinement_lemma()
            requires |fs| != 0
            ensures build_stack_region() == 
                pop_frame_().build_stack_region()
        {
            var stack' := pop_frame_();
            var index := |fs| - 1;

            calc == {
                stack'.build_stack_region();
                free + fs[index] + rev_concat(fs[..index]);
                free + rev_concat(fs[..index] + [fs[index]]);
                free + rev_concat(fs);
                build_stack_region();
            }
        }

        predicate valid_frame_index(i: nat)
        {
            && |fs| != 0
            && i < |fs[|fs| - 1]|
        }

        function write_frame_(i: nat, value: BS.uint): hyper_t
            requires valid_frame_index(i)
        {
            var fi := |fs| - 1;
            hyper_cons(heap, fs[..fi] + [fs[fi][i := value]], free)
        }

        lemma write_frame_refinement_lemma(i: nat, value: BS.uint)
            requires valid_frame_index(i)
            ensures write_frame_(i, value).build_stack_region() ==
                build_stack_region()[|free| + i := value];
        {
            var stack' := write_frame_(i, value);
            var fi := |fs| - 1;
            var fs' := fs[fi][i := value];
            var si := |free| + i;

            calc == {
                build_stack_region()[si:= value];
                (free + rev_concat(fs))[si:= value];
                free + rev_concat(fs)[i := value];
                free + rev_concat(fs[..fi] + [fs[fi]])[i := value];
                free + (fs[fi] + rev_concat(fs[..fi]))[i := value];
                free + fs[fi][i := value] + rev_concat(fs[..fi]);
                free + fs' + rev_concat(fs[..fi]);
                free + rev_concat(fs[..fi] + [fs']);
                stack'.build_stack_region();
            }
        }

        function read_frame_(i: nat): BS.uint
            requires valid_frame_index(i)
        {
            fs[|fs| - 1][i]
        }

        lemma read_frame_refinement_lemma(i: nat)
            requires valid_frame_index(i)
            ensures read_frame_(i) == build_stack_region()[|free| + i];
        {
            var fi := |fs| - 1;
            calc == {
                build_stack_region()[|free| + i];
                (free + rev_concat(fs))[|free| + i];
                rev_concat(fs)[i];
                rev_concat(fs[..fi] + [fs[fi]])[i];
                (fs[fi] + rev_concat(fs[..fi]))[i];
                fs[fi][i];
            }
        }
    }

    datatype iter_t = iter_cons(base_ptr: nat, buff: seq<BS.uint>, index: nat)
    {
        function cur_addr(): nat
        {
            RM.as_flat_ptr(base_ptr, index)
        }
    }

    predicate iter_inv(hyper: hyper_t, iter: iter_t)
    {
        var base_ptr := iter.base_ptr;
        && base_ptr in hyper.heap
        && iter.index <= |iter.buff|
        && hyper.heap[base_ptr] == iter.buff
    }

    predicate iter_safe(hyper: hyper_t, iter: iter_t)
    {
        && iter_inv(hyper, iter)
        && iter.index < |iter.buff|
    }

// iter read

    function read_iter(hyper: hyper_t, iter: iter_t): (v: BS.uint)
        requires iter_safe(hyper, iter)
    {
        iter.buff[iter.index]
    }

    function iter_load_next(iter: iter_t, inc: bool): iter_t
    {
        iter.(index := if inc then iter.index + 1 else iter.index)
    }

    lemma read_iter_refinement_lemma(hyper: hyper_t, iter: iter_t, mem: RM.FM.mem_t)
        requires iter_safe(hyper, iter)
        requires hyper.refines_flat(mem)
        ensures FM.ptr_aligned(iter.cur_addr())
        ensures read_iter(hyper, iter) ==
            mem.read_word(iter.cur_addr())
    {
        var regions := hyper.build_regions();
        assert iter.buff == regions[iter.base_ptr];
        RM.read_refinement_lemma(regions, iter.base_ptr, iter.index, mem);
    }

// iter write

    function write_iter(hyper: hyper_t, iter: iter_t, value: BS.uint):
        (hyper_t)
        requires iter_safe(hyper, iter)
    {
        var buff' := iter.buff[iter.index := value];
        hyper.(heap := hyper.heap[iter.base_ptr := buff'])
    }

    function iter_store_next(iter: iter_t, value: BS.uint, inc: bool): iter_t
        requires iter.index < |iter.buff|
    {
        iter.(index := if inc then iter.index + 1 else iter.index)
            .(buff := iter.buff[iter.index := value])
    }

    lemma write_iter_refinement_lemma(hyper: hyper_t, iter: iter_t, value: BS.uint, mem: RM.FM.mem_t)
        returns (hyper': hyper_t)
        requires iter_safe(hyper, iter)
        requires hyper.refines_flat(mem)
        ensures hyper' == write_iter(hyper, iter, value)
        ensures FM.ptr_aligned(iter.cur_addr())
        ensures hyper'.refines_flat(mem.write_word(iter.cur_addr(), value))
        ensures iter_safe(hyper', iter_store_next(iter, value, false))
    {
        var regions := hyper.build_regions();
        var base := iter.base_ptr;
        var buff := iter.buff;
        var index := iter.index;
        assert buff == regions[base];
        RM.write_refinement_lemma(regions, base, iter.index, value, mem);
        hyper' := write_iter(hyper, iter, value);
        var regions' := hyper'.build_regions();
        assert regions' == regions[base := buff[index := value]];
        assert regions' == RM.wrtie_region(regions, base, index, value);
    }

// stack push

    lemma push_refinement_lemma(hyper: hyper_t, len: nat, mem: RM.FM.mem_t)
        returns (hyper': hyper_t)
        requires 0 <= len < |hyper.free|
        requires hyper.refines_flat(mem)
        ensures hyper' == hyper.push_frame_(len)
        ensures hyper'.refines_flat(mem)
    {
        // var regions := hyper.build_regions();
        hyper' := hyper.push_frame_(len);
        // var regions' := hyper'.build_regions();
        hyper.push_refinement_lemma(len);
    }

// stack pop

    lemma pop_refinement_lemma(hyper: hyper_t, len: nat, mem: RM.FM.mem_t)
        returns (hyper': hyper_t)
        requires |hyper.fs| != 0
        requires hyper.refines_flat(mem)
        ensures hyper' == hyper.pop_frame_()
        ensures hyper'.refines_flat(mem)
    {
        // var regions := hyper.build_regions();
        hyper' := hyper.pop_frame_();
        // var regions' := hyper'.build_regions();
        hyper.pop_refinement_lemma();
    }

// stack read

    lemma read_frame_refinement_lemma(hyper: hyper_t, i: nat, mem: RM.FM.mem_t)
        requires hyper.valid_frame_index(i)
        requires hyper.refines_flat(mem)
        ensures FM.ptr_aligned(RM.as_flat_ptr(FM.STACK_BOT, i + |hyper.free|))
        ensures hyper.read_frame_(i) ==
            mem.read_word(RM.as_flat_ptr(FM.STACK_BOT, i + |hyper.free|))
    {
        var regions := hyper.build_regions();
        var base := FM.STACK_BOT;
        hyper.read_frame_refinement_lemma(i);
        var j := |hyper.free| + i;
        RM.read_refinement_lemma(regions, base, j, mem);
    }

// stack write

    lemma write_frame_refinement_lemma(hyper: hyper_t, i: nat, value: BS.uint, mem: RM.FM.mem_t)
        returns (hyper': hyper_t)
        requires hyper.valid_frame_index(i)
        requires hyper.refines_flat(mem)
        ensures hyper' == hyper.write_frame_(i, value)
        ensures FM.ptr_aligned(RM.as_flat_ptr(FM.STACK_BOT, i + |hyper.free|))
        ensures hyper'.refines_flat(
            mem.write_word(RM.as_flat_ptr(FM.STACK_BOT, i + |hyper.free|), value))
    {
        hyper' := hyper.write_frame_(i, value);
        var regions := hyper.build_regions();
        var regions' := hyper'.build_regions();
        var base := FM.STACK_BOT;
        hyper.write_frame_refinement_lemma(i, value);
        var j := |hyper.free| + i;
        var stack' := regions[base][j := value];
        assert regions' == regions[base := stack'];
        assert regions' == RM.wrtie_region(regions, base, j, value);
        RM.write_refinement_lemma(regions, base, j, value, mem);
    }
}

// abstract module test {
//     import opened integers
//     import BV32 = bv32_op_s
//     import BV256 = bv256_op_s

//     import HM = hyper_mem_i(BV32)
//     import RM = HM.RM
//     import FM = RM.FM

//     // import FM = HM.FM

//     import IT32 = recast_iter_i(BV32, BV32)
//     import IT256 = recast_iter_i(BV32, BV256)

//     function read_iter32(hyper: HM.hyper_t, iter: IT32.iter_t): uint32
//         requires IT32.iter_safe(hyper, iter);
//     {
//         IT32.uint_bound_lemma();
//         IT32.read_iter(hyper, iter)
//     }

//     lemma read_iter32_refinement_lemma(hyper: HM.hyper_t, iter: IT32.iter_t, mem:   FM.mem_t)
//         requires mem.inv()
//         requires hyper.refines_flat(mem)
//         // ensures 

//     function read_iter256(hyper: HM.hyper_t, iter: IT256.iter_t): uint256
//         requires IT256.iter_safe(hyper, iter);
//     {
//         IT256.uint_bound_lemma();
//         IT256.read_iter(hyper, iter)
//     }

// }