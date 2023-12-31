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
include "./CommonSem.dfy" 

/**
  * Provide Semantics of Yul builtin operators/functions.
  *
  * EVM dialect.
  * @link{https://docs.soliditylang.org/en/latest/yul.html#evm-dialect}
  */
module YulSem refines CommonSem {

  //  Arithmetic operators.

  /**
    *   Addition modulo 2^256.
    *   @param      x    
    *   @param      y
    *   @returns    x + y mod 2^256.
    */
  function Add(x: u256, y: u256): u256
  {
    ((x as nat + y as nat) % TWO_256) as u256
  }

  /**
    *   Subtraction modulo 2^256.
    *   @param      x    
    *   @param      y
    *   @returns    x as int - y as int mod 2^256.
    */
  function Sub(x: u256, y: u256): u256
  {
    ((x as int - y as int) % TWO_256) as u256
  }

  /**
    *   Multiplication modulo 2^256.
    *   @param      x    
    *   @param      y
    *   @returns    x * y mod 2^256.
    */
  function Mul(x: u256, y: u256): u256
    ensures x as nat * y as nat < TWO_256 ==> Mul(x, y) == x * y
  {
    ((x as nat * y as nat) % TWO_256) as u256
  }

  /**
    *   Division modulo 2^256.
    *   @param      x    
    *   @param      y
    *   @returns    if y !=0 then x / y mod 2^256 else 0.
    *   @note       Re-use helpers in the bytecode semantics.
    */
  function Div(x: u256, y: u256): u256
    ensures y != 0  ==> Div(x, y) == x / y
  {
    Bytecode.DivWithZero(x, y)
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
    // ensures y > 0 && x > 0 ==> SDiv(x, y) == x / y
  {
    var lhs := Word.asI256(x);
    var rhs := Word.asI256(y);
    var res := Word.fromI256(Bytecode.SDivWithZero(lhs, rhs));
    res
  }

  /**
    *   Modulo with zero handling.
    *   @param      x    
    *   @param      y
    *   @returns    if y !=0 then x % y else 0.
    */
  function Mod(x: u256, y: u256) : u256
    ensures y != 0 ==> Mod(x, y) == x % y
  {
    if y == 0 then 0 as u256
    else
      (x % y) as u256
  }

  /**
    *   Signed Modulo with zero handling.
    *   @param      x    
    *   @param      y
    *   @returns    if y !=0 then x % y else 0.
    */
  function SModWithZero(x: u256, y: u256) : u256
  {
    var lhs := Word.asI256(x);
    var rhs := Word.asI256(y);
    var res := Word.fromI256(Bytecode.SModWithZero(lhs, rhs));
    res
  }

}