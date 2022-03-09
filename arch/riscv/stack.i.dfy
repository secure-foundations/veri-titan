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
    ensures n % 4 == 0
  {
    0x400
  }

  function STACK_MAX_WORDS(): (n: nat)
  {
    STACK_MAX_BYTES() / 4
  }

  function STACK_START(): (sp: nat)
    ensures sp > STACK_MAX_BYTES()
    ensures ptr_admissible_32(sp)

  function STACK_END(): (n: nat)
    ensures n % 4 == 0
  {
    STACK_START() - STACK_MAX_BYTES()
  }

  predicate in_stack_addr_range(addr: int)
  {
    && STACK_END() <= addr <= STACK_START()
    && ptr_admissible_32(addr)
  }

  function ptr_to_stack_index(addr: int): nat
    requires in_stack_addr_range(addr)
  {
    (addr - STACK_END()) / 4
  }

  function stack_index_to_ptr(i: nat): nat
  {
    STACK_END() + i * 4
  }

  datatype frame_t = frame_cons(fp: int, content: seq<uint32>)
  {
    function next_fp(): int
    {
      fp - 4 * |content|
    }

    predicate frame_inv(stack: seq<uint32>)
      requires |stack| == STACK_MAX_WORDS()
    {
      && in_stack_addr_range(fp)
      && in_stack_addr_range(next_fp())
      
      && var start := ptr_to_stack_index(next_fp());
      && content == stack[start..ptr_to_stack_index(fp)]
    }
  }

  predicate frames_writable(frames: frames_t, index: nat)
  {
    && var fs := frames.fs;
    && |fs| != 0
    && index < |fs[|fs| - 1].content|
  }

  function top_frame(frames: frames_t): frame_t
    requires |frames.fs| != 0 
  {
    frames.fs[|frames.fs| - 1]
  }

  datatype frames_t = frames_cons(sp: int, fs: seq<frame_t>)
  {
    predicate frames_inv(stack: seq<uint32>)
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
  
    function push(num_bytes: uint32, stack: seq<uint32>): frames_t
      requires |stack| == STACK_MAX_WORDS()
      requires num_bytes % 4 == 0
      requires frames_inv(stack)
      requires in_stack_addr_range(sp - num_bytes)
    {
      var new_sp := sp - num_bytes;
      var start := ptr_to_stack_index(new_sp);
      var end := ptr_to_stack_index(sp);
      this.(sp := new_sp)
        .(fs := fs + [frame_cons(sp, stack[start..end])])
    }

    function push_once(content: seq<uint32>, stack: seq<uint32>): frames_t
    {
      var new_sp := sp - |content| * 4;
      this.(sp := new_sp)
        .(fs := fs + [frame_cons(sp, content)])
    }

    lemma push_preserves_inv(num_bytes: uint32, stack: seq<uint32>)
      requires push.requires(num_bytes, stack)
      ensures push(num_bytes, stack).frames_inv(stack)
      ensures |top_frame(push(num_bytes, stack)).content| == num_bytes / 4
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
          (end - start) * 4;
          ptr_to_stack_index(sp) * 4 - ptr_to_stack_index(sp - num_bytes) * 4;
          {
            Mul.LemmaMulIsDistributiveSubAuto();
          }
          (sp - STACK_END()) / 4 * 4 - (sp - num_bytes - STACK_END()) / 4 * 4;
          {
            assert DivMod.IsModEquivalent(sp, STACK_END(), 4);
            LemmaDivMulNop(sp - STACK_END(), 4);
          }
          sp - STACK_END() - (sp - num_bytes - STACK_END()) / 4 * 4;
          {
            assert DivMod.IsModEquivalent(sp, num_bytes, 4);
            assert DivMod.IsModEquivalent(sp - num_bytes, STACK_END(), 4);
            LemmaDivMulNop(sp - num_bytes - STACK_END(), 4);
          }
          num_bytes;
        }
        assert end - start == num_bytes / 4;
        assert |stack[start..end]| == num_bytes / 4;

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

    function pop(stack: seq<uint32>): frames_t
      requires |stack| == STACK_MAX_WORDS()
      requires frames_inv(stack)
      requires |fs| >= 2
    {
      var last := |fs| - 1;
      var new_sp := fs[last].fp;
      this.(sp := new_sp)
        .(fs := fs[..last])
    }

    lemma pop_preserves_inv(stack: seq<uint32>, new_frames: frames_t)
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

    lemma fp_decreasing(stack: seq<uint32>, i: nat)
      requires |stack| == STACK_MAX_WORDS()
      requires frames_inv(stack)
      requires i < |fs|
      ensures forall j: nat | 0 <= j < i :: fs[i].fp <= fs[j].fp
      ensures forall j: nat | 0 <= j < i :: fs[i].fp + |fs[j].content| * 4 <= fs[j].fp
    {
      if i != 0 {
        // assert fs[i-1].fp <= fs[i].fp;
        fp_decreasing(stack, i - 1);
      }
    }

    lemma sp_as_lower_bound(stack: seq<uint32>, k: nat)
      requires |stack| == STACK_MAX_WORDS()
      requires frames_inv(stack)
      requires k < |fs| - 1
      ensures sp + |fs[|fs| - 1].content| * 4 + |fs[k].content| * 4  <= fs[k].fp 
    {
      var len := |fs| - 1;
      fp_decreasing(stack, len);
      assert forall j: nat | 0 <= j < len :: sp + |fs[len].content| * 4 + |fs[j].content| * 4 <= fs[j].fp;
    }

    function write(index: nat, value: uint32): frames_t
      requires frames_writable(this, index)
    {
      var last := |fs| - 1;
      var top_f := top_frame(this);
      var new_content := top_f.content[index := value];
      var new_top_f := top_f.(content := new_content);
      this.(fs := fs[last := new_top_f])
    }

    function read(index: nat): uint32
      requires frames_writable(this, index)
    {
      var top_f := top_frame(this);
      top_f.content[index]
    }

    lemma none_top_frame_disjoint(stack: seq<uint32>, i: nat, index: nat, value: uint32)
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
        j * 4;
        ((sp - STACK_END()) / 4 + index) * 4;
        {
          Mul.LemmaMulIsDistributiveAuto();
        }
        (sp - STACK_END()) / 4 * 4 + index * 4;
        {
          assert DivMod.IsModEquivalent(sp, STACK_END(), 4); // pain
          LemmaDivMulNop(sp - STACK_END(), 4);
        }
        sp - STACK_END() + index * 4;
      }

      calc == {
        start * 4;
        (f.fp - 4 * |f.content| - STACK_END()) / 4 * 4;
        {
          assert DivMod.IsModEquivalent(f.fp, 4 * |f.content|, 4); // pain
          assert DivMod.IsModEquivalent(f.fp - 4 * |f.content|, STACK_END(), 4); // pain
          LemmaDivMulNop(f.fp - 4 * |f.content| - STACK_END(), 4);
        }
        f.fp - 4 * |f.content| - STACK_END();
      }

      assert j < start by 
      {
        calc {
          (j - start) * 4;
          j * 4 - start * 4;
          sp + index * 4 - f.fp + |f.content| * 4;
          sp + |f.content| * 4 + index * 4 - f.fp;
          <=
          { sp_as_lower_bound(stack, i); }
          index * 4 - |fs[last].content| * 4;
          <
          0;
        }
      }
    }

    lemma write_preserves_inv(stack: seq<uint32>,
      index: nat, value: uint32)
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

  function init_frames(stack: seq<uint32>): (frames: frames_t)
    requires |stack| == STACK_MAX_WORDS()
    ensures frames.frames_inv(stack)
  {
    frames_cons(STACK_START(), [frame_cons(STACK_START(), [])])
  }
}