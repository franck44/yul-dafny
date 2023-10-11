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
module CommonSem {

  import opened Int
  import U256
  import opened YulState
  import Memory
  import Bytecode
  import Word

  /**
    *    @link{https://osec.io/blog/2023-07-28-solidity-compilers-memory-safety}
    *    Semantics seems to be important only for optimisation.
    *    For now we use Identyt for memoryguard.
    */
  function MemoryGuard(x: u256): u256 {
    x
  }

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
    var z := (!(x as bv256) as nat) as u256;
    z
  }

  /**
    *   Bitwise And
    *   @param      x    
    *   @param      y    
    *   @returns    x && y
    */
  function And(x: u256, y: u256) : u256
  {
    ((x as bv256) & (y as bv256)) as u256
  }

  /**
    *   Special cases of And at boundaries.
    */
  lemma XAnd1IsX(x: u256, y: u256)
    requires y == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
    ensures And(x, y) == And(y, x) == x
  {
  }

  /**
    *   Bitwise Or
    *   @param      x    
    *   @param      y    
    *   @returns    x || y
    */
  function Or(x: u256, y: u256) : u256
  {
    ((x as bv256) | (y as bv256)) as u256
  }

  /**
    * Right shift operation.
    */
  function Shr(value: u256, shift: u256): u256
    ensures shift == 0 ==> Shr(value, shift) == value
  {
    U256.Shr(value, shift)
  }

  /**
    * Left shift operation.
    */
  function Shl(value: u256, shift: u256): u256
    ensures shift == 0 ==> Shl(value, shift) == value
  {
    U256.Shl(value, shift)
  }

  /**
    *  Sha3. 
    *  @param  loc The start location in memory.
    *  @param  len The number of bytes to hash.
    *
    *   @note       We require that memory size is ;arger than the requested
    *               last memory location. This implies that the state 
    *               is not modified and no memory expansion is needed. 
    */
  function Keccak256(loc: u256, len: u256, s: Executing): u256
    requires len > 0
    /** Enforce constraint on memory size and slice to read. */
    requires loc as nat + len as nat < s.MemSize()
  {
    //  get len bytes from loc and possibly extend memory
    var bytes := Memory.Slice(s.yul.memory, loc as nat, len as nat);
    var hash := s.yul.precompiled.Sha3(bytes);
    hash
  }

  //  Memory operators.

  /**
    *   Memory load. load a u256 into memory.
    *
    *   @param      address The address to read a word from.
    *
    *   @note       Memory is a word-addressable array of bytes. A u256 value
    *               is stored into 32 bytes ranging from address to address + 31.
    *     
    */
  function MLoad(address: u256, s: Executing): (s': (u256, State))
    ensures s'.1.EXECUTING?
    ensures s'.1.MemSize() > address as nat + 31
    ensures s'.1.yul.context == s.yul.context
    ensures s'.1.yul.world == s.yul.world
  {
    //  Make sure memory is large enough.
    var m' := Memory.ExpandMem(s.yul.memory, address as nat, 32);
    (Memory.ReadUint256(m', address as nat) ,EXECUTING(s.yul.(memory := m')))
  }

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
    ensures s'.EXECUTING?
    ensures s'.MemSize() > address as nat + 31
    ensures s'.yul.context == s.yul.context
    ensures s'.yul.world == s.yul.world
  {
    //  Make sure memory is large enough.
    var m' := Memory.ExpandMem(s.yul.memory, address as nat, 32);
    EXECUTING(s.yul.(memory := Memory.WriteUint256(m', address as nat, value)))
  }

  /**
    * Get word from storage.
    */
  function SLoad(loc: u256, s: Executing): u256
  {
    s.Load(loc)
  }

  /**
    * Save word to storage.
    */
  function SStore(loc: u256, val: u256, s: Executing): (s': State)
  {
    s.Store(loc, val)
  }

  // Environment (context) functions

  /**
    *    Extract callvalue from context.
    */
  function CallValue(s: Executing): u256
  {
    s.yul.context.callValue
  }

  /**
    *  Get a word of the calldata.
    *  @param  loc The starting location to read the word from.
    *  
    *  @returns    The section calldata[loc..loc + 31] if loc + 31 <= calldatsize
     8              and 0 otherwise. 
     */
  function CallDataLoad(loc: u256, s: Executing): u256
  {
    if loc >= CallDataSize(s) then 0
    else s.yul.context.CallDataRead(loc)
  }

  /**
    * Get size of calldata in current environment.
    */
  function CallDataSize(s: Executing): u256
  {
    s.yul.context.CallDataSize()
  }

  /**
    *    Revert.
    *    @param  start   Offset of memory slice to be returned.
    *    @param  len     Number of bytes from `start` to be returned.
    */
  function Revert(start: u256, len: u256, s: Executing): (s': State)
    ensures s'.ERROR?
  {
    var data := Memory.Slice(s.yul.memory, start as nat, len as nat);
    ERROR(REVERTS, data:=data)
  }

  /**
    *    Return.
    *    @param  start   Offset of memory slice to be returned.
    *    @param  len     Number of bytes from `start` to be returned.
    */
  function Return(start: u256, len: u256, s: Executing): (s': State)
    ensures s'.RETURNS?
  {
    var data := Memory.Slice(s.yul.memory, start as nat, len as nat);
    RETURNS(data := data, world := s.yul.world)
  }
}