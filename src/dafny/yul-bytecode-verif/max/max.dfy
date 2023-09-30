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
include "../../../../libs/evm-dafny/src/dafny/evm.dfy"

include "../../Yul/Semantics.dfy"

/**
  *  
  */
module MaxBytecodeVerification {

  import opened Int
  import opened Yul
  import opened Opcode
  import opened EvmState
  import Memory
  import EVM
  import opened Bytecode
  import Gas

  /**
    *  The labels (JUMPDEST) in the bytecode.
    */
  const tag_1: u8 := 0x0f
  const tag_2: u8 := 0x0a
  const tag_3: u8 := 0x1b 
  const tag_4: u8 := 0x18

  /**
    *  When a JUMP or JUMPI is executed we need to make sure the target location 
    *  is a JUMPDEST.
    *  This axiom enforces it.
    */
  lemma {:axiom} ValidJumpDest(s: ExecutingState)
    ensures s.IsJumpDest(tag_1 as u256)
    ensures s.IsJumpDest(tag_2 as u256)
    ensures s.IsJumpDest(tag_3 as u256)
    ensures s.IsJumpDest(tag_4 as u256)

  /**
    *  Translation of the of the Yul code in Dafny.
    *   Use Dafny native operators.
    */
  method Max(x: u256, y: u256, m: Memory.T) returns (result: u256, m': Memory.T)
    ensures result == x || result == y
    ensures result >= x && result >= y
    ensures m' == m
  {
    m' := m;
    result := x;
    if lt(x, y) {
      result := y;
    }
  }

  /**
    *  Proof of simmulation.
    *  Prove that bytecode at tag1 returns same as Max.
    *
    *  Shows that every "move" in the bytecode (AtTag ...) can be matched by a move in
    *  in the Yul code.
    *  As a result the bytecode simulates the Yul code and Yul safety properties (ensures)
    *  are enforced on the bytecode.
    *
    *  @example    Executing `ExecuteFromTag1(st)` can be matched by executing 
    *              `result := x`. After that, depending on `x < y` we can go into
    *              two different branches. Both can be matched respectively by `result := y` and 
    *              `skip` (no instruction). 
    */
  method MaxProof(x: u256, y: u256, m: Memory.T, ghost st:ExecutingState) returns (result: u256, m': Memory.T, ghost s': State)
    requires st.Operands() >= 3
    requires st.Peek(0) == x
    requires st.Peek(1) == y
    requires st.Peek(2) == tag_2 as u256
    requires st.IsJumpDest(st.Peek(2))
    requires st.PC() == tag_1 as nat
    requires st.Capacity() >= 2
    requires st.evm.memory == m

    ensures s'.EXECUTING?
    ensures s'.PC() == tag_2 as nat
    ensures s'.Operands() == st.Operands() - 2
    ensures s'.Peek(0) == result
    ensures s'.evm.memory == st.evm.memory
    ensures m' == m
  {
    ghost var s1 := ExecuteFromTag1(st);
    m' := m;                                          //  bytecode move
    result := x;                                      //  matching Yul move
    if lt(x, y) {
      s' := ExecuteFromTag4(ExecuteFromTag3(s1));     //  bytecode move
      result := y;                                    //  matching Yul move
    } else {
      s' := ExecuteFromTag4(s1);                      //  bytecode move
    }                                                 //  matching Yul move: Skip
  }

  /**
    *  Translation of Yul code in Dafny.
    */
  method Main(m: Memory.T) returns (m': Memory.T)
    requires Memory.Size(m) % 32 == 0
    ensures Memory.Size(m') > 0x40 + 31
    ensures Memory.ReadUint256(m', 0x40) == 8
  {
    var x := 8;                     //  let
    var y := 3;                     //  let
    var z, m1 := Max(x, y, m);      //  funcall
    m' := mstore(0x40, z, m1);      //  memory store
  }

  /**
    *  Proof of simulation for Main.
    */
  method MainProof(m: Memory.T, ghost st:ExecutingState) returns (z': u256, m': Memory.T, ghost s': State)
    requires st.Capacity() >= 5
    requires st.Operands() >= 0
    requires st.PC() == 0 as nat
    requires Memory.Size(m) % 32 == 0
    requires st.evm.memory == m

    ensures s'.EXECUTING?
    ensures Memory.Size(m') > 0x40 + 31
    ensures Memory.ReadUint256(m', 0x40) == z'
    ensures s'.evm.memory == m'
  {
    ValidJumpDest(st);
    ghost var s1 := ExecuteFromZero(st);        //  bytecode move
    var x := 8;                                 //  Yul move
    var y := 3;                                 //  Yul move

    var z, m1, s2 := MaxProof(x, y, m, s1);    //  Simulation of call to Max.
    assert z == s2.Peek(0);
    assert m1 == m;

    s' := ExecuteFromTag2(s2);          //  Bytecode move
    z':= z;                             //  Yul move
    m' := mstore(0x40, z, m1);          //  Yul move
  }

  /**
    *  Code starting at PC == 0.
    */
  function ExecuteFromZero(st:ExecutingState): (s': State)
    requires st.Capacity() >= 5
    requires st.Operands() >= 0
    requires st.PC() == 0 as nat

    ensures s'.EXECUTING?
    ensures s'.PC() == tag_1 as nat
  {
    /*
    00000000: PUSH1 0xa     //  tag_2 
    00000002: PUSH1 0x8
    00000004: PUSH1 0x3
    00000006: SWAP1
    00000007: PUSH1 0xf     //  tag_1 
    00000009: JUMP
    */
    ValidJumpDest(st);
    var s1 := Push1(st, tag_2);
    var s2 := Push1(s1, 0x08);
    var s3 := Push1(s2, 0x03);
    var s4 := Swap(s3, 1);
    assert s4.Peek(2) == tag_2 as u256;
    var s5 := Push1(s4, tag_1);
    assert s5.Peek(3) == tag_2 as u256;
    var s6 := Jump(s5);
    s6
  }

  function ExecuteFromTag2(st:ExecutingState): (s': State)
    requires st.Capacity() >= 1
    requires st.Operands() >= 0
    requires st.PC() == tag_2 as nat
  {
    /*
    0000000a: JUMPDEST
    0000000b: PUSH1 0x40
    0000000d: MSTORE
    0000000e: STOP
    */
    var s1 := JumpDest(st);
    var s2 := Push1(s1, 0x40);
    var s3 := MStore(s2);
    s3
  }

  function ExecuteFromTag1(st:ExecutingState): (s': State)
    requires st.Capacity() >= 2
    requires st.Operands() >= 3
    requires st.PC() == tag_1 as nat
    requires st.IsJumpDest(st.Peek(2))
    requires st.Peek(2) == tag_2 as u256

    ensures s'.EXECUTING?
    ensures s'.Operands() == st.Operands()
    ensures s'.Peek(0) == st.Peek(1)
    ensures s'.Peek(1) == st.Peek(2)
    ensures s'.Peek(2) == st.Peek(0)
    ensures s'.PC() == if st.Peek(0) < st.Peek(1) then tag_3 as nat else tag_4 as nat
  {
    /*
    0000000f: JUMPDEST      //  tag_1 
    00000010: SWAP2
    00000011: SWAP1
    00000012: DUP1 
    00000013: DUP4
    00000014: LT
    00000015: PUSH1 0x1b
    00000017: JUMPI
    */
    ValidJumpDest(st);
    var s1 := JumpDest(st); //  r, y, x
    var s2 := Swap(s1, 2);  //  x, y, r
    var s3 := Swap(s2, 1);  //  x, r, y
    var s4 := Dup(s3, 1);   //  x, r, y, y
    var s5 := Dup(s4, 4);   //  x, r, y, y, x
    assert s5.PC() == 0x14;
    var s6 := Lt(s5);       //  x, r, y, x < y
    var s7 := Push1(s6, tag_3); //  x, r, y, x < y, tag_ 3
    var s8 := JumpI(s7);        //  x, r, y
    s8
  }

  function ExecuteFromTag4(st:ExecutingState): (s': State)
    requires st.Operands() >= 3
    requires st.PC() == tag_4 as nat
    requires st.IsJumpDest(st.Peek(1))
    requires st.Peek(1) as nat == tag_2 as nat

    ensures s'.EXECUTING?
    ensures s'.PC() == st.Peek(1) as nat == tag_2 as nat
    ensures s'.Operands() == st.Operands() - 2
    ensures s'.Peek(0) == st.Peek(2)
  {
    /*
    00000018: JUMPDEST      // tag_4 x2, x1, x0 
    00000019: POP           //  x2, x1 
    0000001a: JUMP          //  x2 
    */
    var s9 := JumpDest(st);
    var s10 := Pop(s9);
    assert s10.IsJumpDest(s10.Peek(0));
    var s11 := Jump(s10);
    assert s11.PC() == st.Peek(1) as nat;
    s11
  }

  function ExecuteFromTag3(st:ExecutingState): (s': State)
    requires st.Operands() >= 3
    requires st.Capacity() >= 1
    requires st.PC() == tag_3 as nat
    requires st.IsJumpDest(st.Peek(1))
    requires st.Peek(1) == tag_2 as u256

    ensures s'.EXECUTING?
    ensures s'.PC() == tag_4 as nat
    ensures s'.Operands() == st.Operands()
  {
    /*
    0000001b: JUMPDEST      //  tag_ 3  x2, x1, x0 
    0000001c: SWAP1         //  x2, x0, x1 
    0000001d: SWAP2         //  x1, x0, x2 
    0000001e: POP           //  x1, x0 
    0000001f: SWAP1         //  x0, x1 
    00000020: PUSH0         //  x0, x1, 0 
    00000021: PUSH1 0x18    //  x0, x1, 0, 0x18 
    00000023: JUMP          //  x0, x1, 0
    */
    ValidJumpDest(st);

    var s1 := JumpDest(st);
    var s2 := Swap(s1, 1);
    var s3 := Swap(s2, 2);
    var s4 := Pop(s3);
    var s5 := Swap(s4, 1);
    var s6 := Push0(s5);
    var s7 := Push1(s6, tag_4);

    var s8 := Jump(s7);
    assert s8.Peek(0) == 0; //  x0, x1, 0
    s8
  }

  method {:main} Runner() {
    // emtpy memory
    // var m := Memory.Create();
    // var m' := Main(m);

    print "Main2\n";
  }

}