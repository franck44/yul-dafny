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
include "../../../libs/evm-dafny/src/dafny/util/arrays.dfy"
include "../../../libs/evm-dafny/src/dafny/core/memory.dfy"
include "../../../libs/evm-dafny/src/dafny/core/context.dfy"
include "../../../libs/evm-dafny/src/dafny/core/storage.dfy"
include "../../../libs/evm-dafny/src/dafny/core/precompiled.dfy"
include "../../../libs/evm-dafny/src/dafny/core/worldstate.dfy"

/**
  * A Yul state.
  */
module YulState {

  import opened Int
  import opened Arrays
  import Memory
  import Context
  import Storage
  import WorldState
  import Precompiled

  /** 
    *  An executing state of ther Yul machine. 
    *   
    *  @param  context The execution context (callvalue etc)
    *  @param  memory  State of memory
    *  @param  world   Storage state 
    */
  datatype Raw = EState(
    context: Context.T,
    memory: Memory.T,
    world : WorldState.T,
    precompiled: Precompiled.T
  )

  /**
    *   The type for valid states requires that the address
    *   provided in the context is in the Keys of the worldstate 
    *   addresses. This is similar to the Dafny-EVM requirement.
    */
  type T = s: Raw | s.context.address in s.world.accounts
    witness YUL_WITNESS

  datatype Error =
      REVERTS
    | INSUFFICIENT_FUNDS
    | MEMORY_OVERFLOW
    | BALANCE_OVERFLOW
    | RETURNDATA_OVERFLOW
    | ARITHMETIC_OVER_UNDER_FLOW
    | INVALID_PRECONDITION
    | CODESIZE_EXCEEDED
    | CALLDEPTH_EXCEEDED
    | ACCOUNT_COLLISION
    | WRITE_PROTECTION_VIOLATED

  /**
    *    A state of the Yul machine.
    */
  datatype State =
      EXECUTING(yul: T)
    | ERROR(error: Error, data: Array<u8> := [])
    | RETURNS(data: Array<u8> := [], world: WorldState.T)

  {
    //  Memory helpers.

    /**
      *  Get Memory size.
      */
    function MemSize(): nat
      requires this.EXECUTING?
    {
      Memory.Size(this.yul.memory)
    }

    /**
      *  Read a word in memory.
      *
      *  @param  address The first byte to read from.
      */
    function Read(address: nat) : u256
      requires this.EXECUTING?
      requires address + 31 < this.MemSize() {
      Memory.ReadUint256(yul.memory, address)
    }

    //  Storage helpers.

    /**
      * Read word from storage
      */
    function SLoad(address: u256) : u256
      requires this.EXECUTING?
    {
      var account := yul.context.address;
      yul.world.Read(account,address)
    }

    /**
      * Store word in storage
      */
    function SStore(address: u256, val: u256): State
      requires this.EXECUTING?
    {
      var account := yul.context.address;
      EXECUTING(yul.(world:=yul.world.Write(account,address,val)))
    }

  }

  //  Types and constanst

  //  A state witness to ensure that some types are inhabited.
  const YUL_WITNESS: Raw :=
    EState(
      Context.DEFAULT,
      Memory.Create(),
      WorldState.Create(map[0:=WorldState.DefaultAccount()]),
      Precompiled.DEFAULT
    )

  /**
    * The type for executing (normal, or non-error) states.
    */
  type Executing = s:State | s.EXECUTING?
    witness EXECUTING(YUL_WITNESS)

  /**
    * Returns a default executing state.
    */
  function Init(): Executing {
    EXECUTING(YUL_WITNESS)
  }

  /**
    * The type for terminated states.
    */
  type TerminatedState = s:State | (s.RETURNS? || s.ERROR?)
    witness ERROR(INSUFFICIENT_FUNDS)

}