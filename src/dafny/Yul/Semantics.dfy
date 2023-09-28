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

include "../../../libs/evm-dafny/src/dafny/util/int.dfy"
include "../../../libs/evm-dafny/src/dafny/core/memory.dfy"


/**
  * Provide Semantics of Yul builtin operators/functions.
  *
  * EVM dialect.
  * @link{https://docs.soliditylang.org/en/latest/yul.html#evm-dialect}
  */
module Yul {

  import opened Int
  import Memory

  //  Arithmetic operators.

  /**
    *   Addition modulo 2^256.
    *   @param      x    
    *   @param      y
    *   @returns    x + y mod 2^256.
    */
  function add(x: u256, y: u256): u256
  {
    ((x as nat + y as nat) % TWO_256) as u256
  }

  /**
    *   Multiplication modulo 2^256.
    *   @param      x    
    *   @param      y
    *   @returns    x * y mod 2^256.
    */
  function mul(x: u256, y: u256): u256
  {
    ((x as nat * y as nat) % TWO_256) as u256
  }

  //  Comparison operators.

  /**
    *   Unsigned lower than.
    *   @param      x   
    *   @param      y 
    *   @returns    1 if x < y and 0 otherwise.
    */
  function lt(x: u256, y: u256): u256
  {
    if x < y then 1 else 0
  }

  //  Memory operators.

  /**
    *   Memory store. Store a u256 into memory.
    *
    *   @param      address The start address.
    *   @param      value   Value to store.
    *   @param      m       The memory before store operation.
    *   @returns    m[address..address + 31] <- value.
    *
    *   @note       Memory is a word-addressable array of bytes. A u256 value
    *               is stored into 32 bytes ranging from address to address + 31.
    *     
    */
  function mstore(address: u256, value: u256, m: Memory.T): (m' :Memory.T)
    requires Memory.Size(m) % 32 == 0
    ensures Memory.Size(m') % 32 == 0
    ensures Memory.Size(m') >= address as nat
  {
    //  Make sure memory is large enough.
    var m' := Memory.ExpandMem(m, address as nat, 32);
    Memory.WriteUint256(m', address as nat, value)
  }


}