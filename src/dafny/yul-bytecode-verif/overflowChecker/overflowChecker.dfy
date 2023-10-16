
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
include "../../Yul/Semantics.dfy"
include "../../Yul/State.dfy"

/**
  *  
  */
module OverflowChecker {

  import opened Int
  import opened YulSem
  import opened YulState

  /** Necessary and sufficient condition for overflow in Add. */
  lemma NSCOverFlowU256(x: u256, y: u256)
    ensures x as nat + y as nat < TWO_256 <==> !Gt(x, Add(x ,y))
  {    // thanks Dafny
  }

    /**
     *  Overfloe checker as generated bh the Solidity compiler.
     *  `clean-up` calls have been removed.
     */
  method checked_add_t_uint256(x: u256, y: u256, s: Executing) returns (sum: u256, s': State)

    /** if no overflow we get normal state s'. */
    ensures x as nat + y as nat < TWO_256 <==> s' == s
    /** Sum is the sum of x and y. */
    ensures x as nat + y as nat < TWO_256 <==>
            sum as nat == x as nat + y as nat
    /** If addition overflows we get an error state. */
    ensures x as nat + y as nat >= TWO_256 <==> s'.ERROR?
  {
    sum := Add(x, y);
    // use our lemma.
    NSCOverFlowU256(x, sum);
    if Gt(x, sum) {
      //  Overflow, revert
      return 0, Revert(0, 0, s);
    }
    //  no overflow
    return sum, s;
  }
}
