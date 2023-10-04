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
include "../../../libs/evm-dafny/src/dafny/bytecode.dfy"
include "./State.dfy"

/**
  * Provide Semantics of Yul builtin operators/functions.
  * Arithmetic operators are not implemented 
  * and must be specified in a refined module.
  * The main reason is that it allows to use a strict version 
  *  of e.g. arithmetic that simplify the reasoning. 
  *
  * EVM dialect.
  * @link{https://docs.soliditylang.org/en/latest/yul.html#evm-dialect}
  */
abstract module CommonSem {

  import opened Int
  import opened YulState
  import Memory
  import Bytecode
  import Word

  /**
    *   Signed Modulo with zero handling.
    *   @param      x    
    *   @param      y
    */
  function Exp(x: u256, y: u256) : u256
  {
    (MathUtils.Pow(x as nat, y as nat) % TWO_256) as u256
  }

  //  Comparison operators.

  /**
    *   Unsigned lower than.
    *   @param      x   
    *   @param      y 
    *   @returns    x < y
    */
  function Lt(x: u256, y: u256): bool
  {
    x < y 
  }

  /**
    *   Unsigned greater than.
    *   @param      x   
    *   @param      y 
    *   @returns    x > y
    */
  function Gt(x: u256, y: u256): bool
  {
    x > y
  }

  /**
    *   Signed lower than.
    *   @param      x   
    *   @param      y 
    *   @returns    x as int < y as int.
    */
  function SLt(x: u256, y: u256): bool
  {
    var lhs := Word.asI256(x);
    var rhs := Word.asI256(y);
    lhs < rhs 
  }

  /**
    *   Signed greater than.
    *   @param      x   
    *   @param      y 
    *   @returns    x as int >  y as int and 0 otherwise.
    */
  function SGt(x: u256, y: u256): bool
  {
    var lhs := Word.asI256(x);
    var rhs := Word.asI256(y);
    lhs > rhs
  }

  /**
    *   Equality.
    *   @param      x   
    *   @param      y 
    *   @returns    x == y
    */
  function Eq(x: u256, y: u256): bool
  {
    x == y
  }

  /**
    *   Is zero.
    *   @param      x   
    *   @returns    x == 0.
    */
  function IsZero(x: u256): bool
  {
    x == 0 
  }

  //    Bitwise operators

  /**
    *   Bitwise not
    *   @param      x    
    *   @returns    not(x), every bit is flipped.
    */
  function Not(x: u256) : u256
  {
    (TWO_256 - 1 - x as nat) as u256
  }

  /**
    *   Bitwise And
    *   @param      x    
    *   @param      y    
    *   @returns    x && y
    */
  function And(x: u256, y: u256) : u256
  {
    x 
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
  function MStore(address: u256, value: u256, s: Executing): (s': State)
    requires s.MemSize() % 32 == 0
    ensures s'.EXECUTING?
    ensures s'.MemSize() % 32 == 0
    ensures s'.MemSize() >= address as nat + 32
    ensures s'.yul.context == s.yul.context
    ensures s'.yul.world == s.yul.world
  {
    //  Make sure memory is large enough.
    var m' := Memory.ExpandMem(s.yul.memory, address as nat, 32);
    EXECUTING(s.yul.(memory := Memory.WriteUint256(m', address as nat, value)))
  }

  // Environment (context) functions
  // function CallValue(c: Context.T )

}