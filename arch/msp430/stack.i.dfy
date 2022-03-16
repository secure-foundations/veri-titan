include "flat.s.dfy"

module stack {
  import Mul
  import DivMod

  import opened integers
  import opened flat

  lemma LemmaDivMulNop(a: int, b: int)
    requires b != 0
    requires a % b == 0
    ensures a / b * b == a
  {
    var q := a / b;
    var r := a % b;
    DivMod.LemmaFundamentalDivMod(a, b);
    assert a == q * b + r;
  }

  function STACK_MAX_BYTES(): (n: nat)
    ensures n % 2 == 0
  {
    0x400
  }

  function STACK_MAX_WORDS(): (n: nat)
  {
    STACK_MAX_BYTES() / 2
  }

  function {:extern} STACK_START(): (sp: nat)
    ensures sp > STACK_MAX_BYTES()
    ensures ptr_admissible_16(sp)

  function STACK_END(): (n: nat)
    ensures n % 2 == 0
  {
    STACK_START() - STACK_MAX_BYTES()
  }

  predicate in_stack_addr_range(addr: int)
  {
    && STACK_END() <= addr <= STACK_START()
    && ptr_admissible_16(addr)
  }

  function ptr_to_stack_index(addr: int): nat
    requires in_stack_addr_range(addr)
  {
    (addr - STACK_END()) / 2
  }

  function stack_index_to_ptr(i: nat): nat
  {
    STACK_END() + i * 2
  }

  datatype frame_t = frame_cons(fp: int, content: seq<uint16>)
  {
    function next_fp(): int
    {
      fp - 2 * |content|
    }

    predicate frame_inv(stack: seq<uint16>)
      requires |stack| == STACK_MAX_WORDS()
    {
      && in_stack_addr_range(fp)
      && in_stack_addr_range(next_fp())
      
      && var start := ptr_to_stack_index(next_fp());
      && content == stack[start..ptr_to_stack_index(fp)]
    }
  }

  predicate frames_diff_one(f1: frames_t, f2: frames_t)
  {
    && |f1.fs| + 1 == |f2.fs|
    && f1.fs == f2.fs[..|f1.fs|]
  }

  datatype frames_t = frames_cons(sp: int, fs: seq<frame_t>)
  {
    predicate frames_inv(stack: seq<uint16>)
      requires |stack| == STACK_MAX_WORDS()
    {
      // first one is a place holder
      && |fs| != 0 
      && fs[0].fp == STACK_START()
      && |fs[0].content| == 0
      && var last := |fs| - 1;
      // for adjcent frames, the frame pointers are offseted by the frame length
      && (forall i | 0 <= i < last ::
        fs[i].next_fp() == fs[i + 1].fp)
      && fs[last].next_fp() == sp
      && (forall i | 0 <= i < |fs| :: fs[i].frame_inv(stack))
    }
  
    function depth(): nat 
    {
      |fs|
    }

    function push_batch(content: seq<uint16>): (new_frames: frames_t)
      ensures frames_diff_one(this, new_frames)
    {
      var new_sp := sp - |content| * 2;
      this.(sp := new_sp)
        .(fs := fs + [frame_cons(sp, content)])
    }

    function push(num_bytes: uint16, stack: seq<uint16>): (new_frames: frames_t)
      requires |stack| == STACK_MAX_WORDS()
      requires num_bytes % 2 == 0
      requires frames_inv(stack)
      requires in_stack_addr_range(sp - num_bytes)
      ensures frames_diff_one(this, new_frames)
    {
      var new_sp := sp - num_bytes;
      var start := ptr_to_stack_index(new_sp);
      var end := ptr_to_stack_index(sp);
      push_batch(stack[start..end])
    }

    lemma push_preserves_inv(num_bytes: uint16, stack: seq<uint16>)
      requires push.requires(num_bytes, stack)
      ensures push(num_bytes, stack).frames_inv(stack)
      ensures |top_frame(push(num_bytes, stack)).content| == num_bytes / 2
    {
      var new_frames := push(num_bytes, stack);
      assert new_frames.frames_inv(stack) by {
        var new_sp := sp - num_bytes;
        var start := ptr_to_stack_index(new_sp);
        var end := ptr_to_stack_index(sp);
        var new_f := frame_cons(sp, stack[start..end]);

        var last := |new_frames.fs| - 1;
        assert new_frames.fs[last] == new_f;
        assert new_frames.fs[..last] == fs[..last];

        forall i | 0 <= i < last
          ensures new_frames.fs[i].next_fp() == new_frames.fs[i + 1].fp
        {
          assert fs[i] == new_frames.fs[i];
        }

        calc == {
          (end - start) * 2;
          ptr_to_stack_index(sp) * 2 - ptr_to_stack_index(sp - num_bytes) * 2;
          {
            Mul.LemmaMulIsDistributiveSubAuto();
          }
          (sp - STACK_END()) / 2 * 2 - (sp - num_bytes - STACK_END()) / 2 * 2;
          {
            assert DivMod.IsModEquivalent(sp, STACK_END(), 2);
            LemmaDivMulNop(sp - STACK_END(), 2);
          }
          sp - STACK_END() - (sp - num_bytes - STACK_END()) / 2 * 2;
          {
            assert DivMod.IsModEquivalent(sp, num_bytes, 2);
            assert DivMod.IsModEquivalent(sp - num_bytes, STACK_END(), 2);
            LemmaDivMulNop(sp - num_bytes - STACK_END(), 2);
          }
          num_bytes;
        }
        assert end - start == num_bytes / 2;
        assert |stack[start..end]| == num_bytes / 2;

        forall i | 0 <= i < |new_frames.fs|
          ensures new_frames.fs[i].frame_inv(stack)
        {
          if i < last {
            assert fs[i] == new_frames.fs[i];
            assert fs[i].frame_inv(stack);
          } else {
            assert new_frames.fs[i] == new_f;
          }
        }
      }
      assert new_frames == push(num_bytes, stack);
      assert push(num_bytes, stack).frames_inv(stack);
    }

    function pop(stack: seq<uint16>): frames_t
      requires |stack| == STACK_MAX_WORDS()
      requires frames_inv(stack)
      requires |fs| >= 2
    {
      var last := |fs| - 1;
      var new_sp := fs[last].fp;
      this.(sp := new_sp)
        .(fs := fs[..last])
    }

    lemma pop_preserves_inv(stack: seq<uint16>)
      requires pop.requires(stack)
      ensures pop(stack).frames_inv(stack)
    {
      var new_frames := pop(stack);
      var last := |new_frames.fs| - 1;

      forall i | 0 <= i < last
        ensures new_frames.fs[i].next_fp() == new_frames.fs[i + 1].fp
      {
        assert fs[i] == new_frames.fs[i];
      }

      forall i | 0 <= i < |new_frames.fs|
        ensures new_frames.fs[i].frame_inv(stack)
      {
        assert fs[i] == new_frames.fs[i];
        assert fs[i].frame_inv(stack);
      }
    }

    lemma fp_decreasing(stack: seq<uint16>, i: nat)
      requires |stack| == STACK_MAX_WORDS()
      requires frames_inv(stack)
      requires i < |fs|
      ensures forall j: nat | 0 <= j < i :: fs[i].fp <= fs[j].fp
      ensures forall j: nat | 0 <= j < i :: fs[i].fp + |fs[j].content| * 2 <= fs[j].fp
    {
      if i != 0 {
        // assert fs[i-1].fp <= fs[i].fp;
        fp_decreasing(stack, i - 1);
      }
    }

    lemma sp_as_lower_bound(stack: seq<uint16>, k: nat)
      requires |stack| == STACK_MAX_WORDS()
      requires frames_inv(stack)
      requires k < |fs| - 1
      ensures sp + |fs[|fs| - 1].content| * 2 + |fs[k].content| * 2  <= fs[k].fp 
    {
      var len := |fs| - 1;
      fp_decreasing(stack, len);
      assert forall j: nat | 0 <= j < len :: sp + |fs[len].content| * 2 + |fs[j].content| * 2 <= fs[j].fp;
    }

    function write(index: nat, value: uint16): frames_t
      requires frames_writable(this, index)
    {
      var last := |fs| - 1;
      var top_f := top_frame(this);
      var new_content := top_f.content[index := value];
      var new_top_f := top_f.(content := new_content);
      this.(fs := fs[last := new_top_f])
    }

    function read(index: nat): uint16
      requires frames_writable(this, index)
    {
      var top_f := top_frame(this);
      top_f.content[index]
    }

    lemma none_top_frame_disjoint(stack: seq<uint16>, i: nat, index: nat, value: uint16)
      requires |stack| == STACK_MAX_WORDS()
      requires write.requires(index, value)
      requires i < |fs| - 1
      requires frames_inv(stack)
      ensures ptr_to_stack_index(sp) + index < ptr_to_stack_index(fs[i].next_fp());
    {
      var last := |fs| - 1;
      var j := ptr_to_stack_index(sp) + index;
      var f := fs[i];
      var start := ptr_to_stack_index(f.next_fp());
      var end := ptr_to_stack_index(f.fp);

      calc == {
        j * 2;
        ((sp - STACK_END()) / 2 + index) * 2;
        {
          Mul.LemmaMulIsDistributiveAuto();
        }
        (sp - STACK_END()) / 2 * 2 + index * 2;
        {
          assert DivMod.IsModEquivalent(sp, STACK_END(), 2); // pain
          LemmaDivMulNop(sp - STACK_END(), 2);
        }
        sp - STACK_END() + index * 2;
      }

      calc == {
        start * 2;
        (f.fp - |f.content| * 2 - STACK_END()) / 2 * 2;
        {
          assert DivMod.IsModEquivalent(f.fp, |f.content| * 2, 2); // pain
          assert DivMod.IsModEquivalent(f.fp - |f.content| * 2, STACK_END(), 2); // pain
          LemmaDivMulNop(f.fp - |f.content| * 2 - STACK_END(), 2);
        }
        f.fp - |f.content| * 2 - STACK_END();
      }

      assert j < start by 
      {
        calc {
          (j - start) * 2;
          j * 2 - start * 2;
          sp + index * 2 - f.fp + |f.content| * 2;
          sp + |f.content| * 2 + index * 2 - f.fp;
          <=
          { sp_as_lower_bound(stack, i); }
          index * 2 - |fs[last].content| * 2;
          <
          0;
        }
      }
    }

    lemma write_preserves_inv(stack: seq<uint16>,
      index: nat, value: uint16)
      requires |stack| == STACK_MAX_WORDS()
      requires write.requires(index, value)
      requires frames_inv(stack)
      ensures write(index, value).
        frames_inv(stack[ptr_to_stack_index(sp) + index := value])
    {
      var new_frames := write(index, value);
      assert in_stack_addr_range(sp);

      var j := ptr_to_stack_index(sp) + index;
      var new_stack := stack[j := value];

      var last := |new_frames.fs| - 1;

      forall i | 0 <= i < last
        ensures new_frames.fs[i].next_fp() == new_frames.fs[i + 1].fp
      {
        assert fs[i].fp == new_frames.fs[i].fp;
      }

      forall i | 0 <= i < |new_frames.fs|
        ensures new_frames.fs[i].frame_inv(new_stack)
      {
        var new_f := new_frames.fs[i];
        var start := ptr_to_stack_index(new_f.next_fp());
        var end := ptr_to_stack_index(new_f.fp);

        if i != last {
          none_top_frame_disjoint(stack, i, index, value);
        } else {
          calc == {
            new_f.content;
            fs[i].content[index := value];
            {
              assert fs[i].frame_inv(stack);
            }
            stack[start..end][index := value];
            stack[start + index := value][start..end];
            stack[ptr_to_stack_index(sp) + index := value][start..end];
            stack[j := value][start..end];
          }
        }
      }
    }
  }

  function top_frame(frames: frames_t): frame_t
    requires frames.depth() != 0
  {
    frames.fs[|frames.fs| - 1]
  }

  predicate frames_writable(frames: frames_t, index: nat)
  {
    && frames.depth() != 0
    && index < |top_frame(frames).content|
  }
}