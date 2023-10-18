
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
  // include "../../Yul/StrictSemantics.dfy"
include "../../Yul/State.dfy"

include "./overflowChecker-bytecode.dfy"

/**
  *  
  */
module OverflowCheckerRefinement {

  import opened Int
  import opened YulSem
  import opened YulState
  import opened OverFlowCheckerBytecode

  /** Necessary and sufficient condition for overflow in Add. */
  lemma NSCOverFlowU256(x: u256, y: u256)
    ensures x as nat + y as nat < TWO_256 <==> !Gt(x, Add(x ,y))
  {    // thanks Dafny
  }

  method checked_add_t_uint256Proof(x: u256, y: u256, s: Executing, ghost st: EvmState.ExecutingState) returns (sum: u256, s': State, ghost st': EvmState.State)

    requires st.Capacity() >= 1
    requires st.Operands() >= 3
    requires st.PC() == tag_1 as nat
    requires st.Peek(2) == tag_3 as u256

    requires st.Peek(0) == x
    requires st.Peek(1) == y

    /** if no overflow we get normal state s'. */
    ensures x as nat + y as nat < TWO_256 <==> s' == s
    /** Sum is the sum of x and y. */
    ensures x as nat + y as nat < TWO_256 <==>
            sum as nat == x as nat + y as nat
    /** If addition overflows we get an error state. */
    ensures x as nat + y as nat >= TWO_256 <==> s'.ERROR?

    ensures s'.ERROR? <==> st'.ERROR?
    ensures s'.EXECUTING? <==> st'.EXECUTING?

    ensures st'.EXECUTING? ==> st'.PC() == st.Peek(2) as nat == tag_3 as nat
    ensures st'.EXECUTING? ==> st'.Operands() >= 1 && st'.Peek(0) == sum
    //  No overflow.
    ensures st'.EXECUTING? ==> st'.Peek(0) == st.Peek(0) + st.Peek(1) 

    ensures st'.ERROR? <==> st.Peek(0) as nat + st.Peek(1) as nat >= TWO_256
  {
    ghost var st1 := ExecuteFromTag1(st);   //  bytecode move
    sum := Add(x, y);                       //  Yul move
    // use our lemma.
    NSCOverFlowU256(x, sum);                //  
    if Gt(x, sum) {
      assert st1.PC() == tag_3 as nat ;
      var st2 := ExecuteFromTag3(st1);     //  bytecode Revert
      //  Overflow, revert
      return sum, Revert(0, 0, s), st2;     // yul move Revert(0, 0, s)
    }
    assert st1.PC() == tag_4 as nat;
    var st3 := ExecuteFromTag4(st1);        //  bytecode move. Jump to top of stack
    assert st3.PC() == tag_3 as nat;        //  Jump to tag_3
    //  no overflow
    return sum, s, st3;                     //  Yul move: skip
  }
}
