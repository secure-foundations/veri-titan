include "flat_memory.dfy"

module stack {
  import opened integers
  import opened flat_memory
  import Mul
  import DivMod

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

  datatype frame_t = frame_cons(fp: nat, content: seq<uint32>)
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

  datatype frames_t = frames_cons(sp: nat, fs: seq<frame_t>)
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
  
    function push(num_words: uint32, stack: seq<uint32>): frames_t
      requires |stack| == STACK_MAX_WORDS()
      requires frames_inv(stack)
      requires in_stack_addr_range(sp - num_words * 4)
    {
      var new_sp := sp - num_words * 4;
      var start := ptr_to_stack_index(new_sp);
      var end := ptr_to_stack_index(sp);
      this.(sp := new_sp)
        .(fs := fs + [frame_cons(sp, stack[start..end])])
    }

    lemma push_preserves_inv(num_words: uint32, stack: seq<uint32>, new_frames: frames_t)
      requires push.requires(num_words, stack)
      requires new_frames == push(num_words, stack)
      ensures new_frames.frames_inv(stack)
    {
      var new_sp := sp - 4 * num_words;
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

      forall i | 0 <= i < |new_frames.fs|
        ensures new_frames.fs[i].frame_inv(stack)
      {
        if i < last {
          assert fs[i] == new_frames.fs[i];
        } else {
          assert new_frames.fs[i] == new_f;
        }
      }
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
      requires new_frames == pop(stack)
      ensures new_frames.frames_inv(stack)
    {
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

    // lemma (stack: seq<uint32>, i: nat)

    function write(index: nat, value: uint32): frames_t
      requires |fs| >= 1
      requires index < |fs[|fs| - 1].content|
    {
      var last := |fs| - 1;
      var top_f := fs[last];
      var new_content := top_f.content[index := value];
      var new_top_f := top_f.(content := new_content);
      this.(fs := fs[last := new_top_f])
    }

    lemma write_preserves_inv(stack: seq<uint32>,
      index: nat, value: uint32,
      new_frames: frames_t)
      requires |stack| == STACK_MAX_WORDS()
      requires write.requires(index, value)
      requires frames_inv(stack)
      // requires new_frames == write(index, value)
      // requires new_stack == 
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
          calc == {
            new_f.content;
            fs[i].content;
            {
              assert fs[i].frame_inv(stack);
            }
            stack[start..end];
            {
              calc == {
                j * 4;
                ((sp - STACK_END()) / 4 + index) * 4;
                {
                  Mul.LemmaMulIsDistributiveAuto();
                }
                (sp - STACK_END()) / 4 * 4 + index * 4;
                {
                  assume (sp - STACK_END()) / 4 * 4 == sp - STACK_END();
                }
                sp - STACK_END() + index * 4;
              }

              calc == {
                start * 4;
                (fs[i].fp - 4 * |fs[i].content| - STACK_END()) / 4 * 4;
                {
                  assume false;
                }
                fs[i].fp - 4 * |fs[i].content| - STACK_END();
              }

              calc {
                (j - start) * 4;
                j * 4 - start * 4;
                ==
                sp + index * 4 - fs[i].fp + |fs[i].content| * 4;
                ==
                sp + |fs[i].content| * 4 + index * 4 - fs[i].fp ;
                <=
                {
                  sp_as_lower_bound(stack, i);
                }
                index * 4 - |fs[last].content| * 4;
                <
                0;
              }

              assert (j - start) * 4 < 0;
              assert j < start;
            }
            new_stack[start..end];
          }
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

  // function write_frame(frames: frames_t, index: nat, value: uint32): frames_t
  //   requires |frames.fs| >= 1
  //   requires index < |frames.fs[|frames.fs| - 1].content|
  // {
  //   var last := |frames.fs| - 1;
  //   var top_f := frames.fs[last];
  //   var new_content := top_f.content[index := value];
  //   var new_top_f := top_f.(content := new_content);
  //   frames.(fs := frames.fs[last := new_top_f])
  // }

}