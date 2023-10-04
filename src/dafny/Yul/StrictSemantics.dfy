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
include "../../../libs/evm-dafny/src/dafny/core/context.dfy"
include "../../../libs/evm-dafny/src/dafny/bytecode.dfy"
include "./Semantics.dfy"
include "State.dfy"
include "./CommonSem.dfy"
/**
  * Provide Semantics of Yul builtin operators/functions.
  * This semantics uses Dafny native arithmetic operators when possible
  * enforcing types (u256).
  *
  * As we use Dafny native operators, it is easier for the solver
  * to "reason" about them.
  *
  * EVM dialect.
  * @link{https://docs.soliditylang.org/en/latest/yul.html#evm-dialect}
  */
module YulStrict refines CommonSem {

  import YulSem
  import I256

  //  Arithmetic operators.

  /**
    *   Addition.
    *   @param      x    
    *   @param      y
    *   @returns    x + y
    */
  function Add(x: u256, y: u256): u256
    requires x as nat + y as nat < TWO_256
    ensures Add(x, y) == YulSem.Add(x, y)
  {
    x + y
  }

  /**
    *   Subtraction.
    *   @param      x    
    *   @param      y
    *   @returns    x as int - y as int as u256
    */
  function Sub(x: u256, y: u256): u256
    requires -TWO_255 <= x as int - y as int < TWO_255
    ensures Sub(x, y) == YulSem.Sub(x, y)
  {
    ((x as int - y as int) % TWO_256) as u256
  }

  /**
    *   Multiplication.
    *   @param      x    
    *   @param      y
    *   @returns    x * y
    */
  function Mul(x: u256, y: u256): u256
    requires x as nat * y as nat < TWO_256
    ensures Mul(x, y) == YulSem.Mul(x, y)
  {
    x * y
  }

  /**
    *   Division.
    *   @param      x    
    *   @param      y
    *   @returns    x / y
    */
  function Div(x: u256, y: u256): u256
    requires y != 0
    ensures Div(x, y) == YulSem.Div(x, y)
  {
    x / y
  }

  /**
    *   Signed integer Division modulo 2^256.
    *   @param      x    
    *   @param      y
    *   @returns    if y !=0 then x / y for signed numbers (2-s complement) mod 2^256 else 0.
    *   @note       We assume that the semantics in Yul is the same as in the EVM dialect. 
    *               Use the EVM bytecode helpers.
    */
  function SDiv(x: u256, y: u256): u256
    requires y != 0
    requires (Word.asI256(y) != -1 || Word.asI256(x) != (-TWO_255 as i256))
    ensures SDiv(x, y) == YulSem.SDiv(x, y)
  {
    var lhs := Word.asI256(x);
    var rhs := Word.asI256(y);
    Word.fromI256(I256.Div(lhs,rhs))
  }

  /**
    *   Modulo.
    *   @param      x    
    *   @param      y
    *   @returns    x % y 
    */
  function Mod(x: u256, y: u256) : u256
    requires y != 0
    ensures Mod(x, y) == YulSem.Mod(x, y)
  {
    x % y
  }

  /**
    *   Signed Modulo with zero handling.
    *   @param      x    
    *   @param      y
    *   @returns    if y !=0 then x % y else 0.
    */
  function SModWithZero(x: u256, y: u256) : u256
  {
    YulSem.SModWithZero(x, y)
  }

}