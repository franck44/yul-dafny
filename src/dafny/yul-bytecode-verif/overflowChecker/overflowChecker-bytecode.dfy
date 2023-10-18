
/*
 * Copyright 2023 Franck Cassez
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

include "../../../../libs/evm-dafny/src/dafny/state.dfy"
include "../../../../libs/evm-dafny/src/dafny/bytecode.dfy"

/**
  *  
  */
module OverFlowCheckerBytecode {

  import opened Int
  import EvmState
  import opened Bytecode

  /**
    *  The labels (JUMPDEST) in the bytecode.
    */
  const tag_1: u8 := 0x0c
  const tag_2: u8 := 0x0d
  const tag_3: u8 := 0x18
  const tag_4: u8 := 0x17                   //   this one is not a JUMPDEST

  /**
    *  When a JUMP or JUMPI is executed we need to make sure the target location 
    *  is a JUMPDEST.
    *  This axiom enforces it.
    */
  lemma {:axiom} ValidJumpDest(s: EvmState.ExecutingState)
    ensures s.IsJumpDest(tag_1 as u256)
    ensures s.IsJumpDest(tag_2 as u256)
    ensures s.IsJumpDest(tag_3 as u256)
    // ensures s.IsJumpDest(tag_4 as u256)

  /**
    *  Code starting at PC == 0.
    */
  function ExecuteFromZero(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Capacity() >= 4
    requires st.Operands() >= 0
    requires st.PC() == 0 as nat

    ensures s'.EXECUTING?
    ensures s'.PC() == tag_1 as nat
  {
    /*
    00000000: PUSH1 0xa     //  tag_2 
    00000002: PUSH1 0x8
    00000004: PUSH1 0x38
    00000006: SWAP1
    00000007: PUSH1 0xc     //  tag_1 
    00000009: JUMP
    */
    ValidJumpDest(st);
    var s1 := Push1(st, tag_2);
    var s2 := Push1(s1, 0x08);
    var s3 := Push1(s2, 0x38);
    var s4 := Swap(s3, 1);
    assert s4.Peek(2) == tag_2 as u256;
    var s5 := Push1(s4, tag_1);
    assert s5.Peek(3) == tag_2 as u256;
    var s6 := Jump(s5);
    s6
  }

  /**
    * Code staring at tag_2
    */
  function ExecuteFromTag2(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Capacity() >= 0
    requires st.Operands() >= 0
    requires st.PC() == tag_2 as nat

    ensures s'.RETURNS?
    ensures |s'.data| == 0
  {
    /*
    0000000b: STOP
    */
    var s6 := Stop(st);
    s6
  }

  /**
    * Code staring at tag_1
    */
  function ExecuteFromTag1(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Capacity() >= 1
    requires st.Operands() >= 3
    requires st.PC() == tag_1 as nat
    requires st.Peek(2) == tag_3 as u256

    ensures s'.EXECUTING?
    ensures s'.Operands() == st.Operands() - 1
    ensures s'.Peek(0) == st.Peek(2)
    ensures s'.Peek(1) as nat == (st.Peek(0) as nat + st.Peek(1) as nat) % TWO_256
    ensures s'.PC() == if st.Peek(0) > ((st.Peek(0) as nat + st.Peek(1) as nat) % TWO_256) as u256 then tag_3 as nat else tag_4 as nat
  {
    /*
    0000000c: JUMPDEST      //  tag_1
    0000000d: SWAP2
    0000000e: SWAP1
    0000000f: DUP3
    00000010: ADD
    00000011: DUP1
    00000012: SWAP3
    00000013: GT
    00000014: PUSH1 0x18    //  tag_3 
    00000016: JUMPI
    */
    ValidJumpDest(st);
    var s1 := JumpDest(st);             //  x, y, z
    var s2 := Swap(s1, 2);              //  z, y, x
    var s3 := Swap(s2, 1);              //  y, z, x
    var s4 := Dup(s3, 3);               //  x, y, z, x
    var s5 := Add(s4);                  //  x + y, z, x
    var s6 := Dup(s5, 1);               //  x + y, x + y, z, x
    var s7 := Swap(s6, 3);              //  x, x + y, z, x + y
    assert s7.Peek(0) == st.Peek(0);
    var s8 := Bytecode.Gt(s7);          //  x > x + y, z, x + y
    var s9 := Push1(s8, tag_3);         //  tag_3, x > x + y, z, x + y
    var s10 := JumpI(s9);               //  z, x + y
    s10
  }

  /**
    * Code staring at tag_3
    */
  function ExecuteFromTag3(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Operands() >= 0
    requires st.Capacity() >= 2
    requires st.PC() == tag_3 as nat

    ensures s'.ERROR?
  {
    /*
    00000018: JUMPDEST      //  tag_3 
    00000019: PUSH0
    0000001a: DUP1
    0000001b: REVERT
    */
    ValidJumpDest(st);

    var s1 := JumpDest(st);
    var s2 := Push0(s1);
    var s3 := Dup(s2, 1);

    var s4 := Revert(s3);
    s4
  }

  /**
    * Code staring at tag_3
    */
  function ExecuteFromTag4(st: EvmState.ExecutingState): (s': EvmState.State)
    requires st.Operands() >= 1
    requires st.Capacity() >= 0
    requires st.PC() == tag_4 as nat
    requires st.Peek(0) in {tag_1 as u256, tag_2 as u256, tag_3 as u256}

    ensures s'.EXECUTING?
    ensures s'.PC() == st.Peek(0) as nat
    ensures s'.Operands() == st.Operands() - 1
  {
    /*
    00000017: JUMP
    */
    ValidJumpDest(st);
    // assume st.IsJumpDest(st.Peek(0));
    Jump(st)
  }

}