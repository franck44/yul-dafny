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

include "../../../libs/evm-dafny/src/dafny/core/memory.dfy"
include "../../../libs/evm-dafny/src/dafny/core/context.dfy"
include "../../../libs/evm-dafny/src/dafny/core/worldstate.dfy"

/**
  * A Yul state.
  */
module YulState {

  import Memory
  import Context
  import WorldState

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
    world : WorldState.T
  )

  /**
    *    A state of the Yul machine.
    */
  datatype State =
      EXECUTING(yul: Raw)
    | REVERT()

  {
    //  Some useful functions 

    //  Memory 
    
    /**
      *  Get Memory size.
      */
    function MemSize(): nat
      requires this.EXECUTING?
    {
      Memory.Size(this.yul.memory)
    }


  }

  const STATE_WITNESS: Raw :=
    EState(
      Context.DEFAULT,
      Memory.Create(),
      WorldState.Create(map[0:=WorldState.DefaultAccount()])
    )

  /**
    * The type for executing states.
    */
  type Executing = s:State | s.EXECUTING?
    witness EXECUTING(STATE_WITNESS)

  /**
    * The type for terminated states.
    */
  // type TerminatedState = s:State | s.REVERT?
  // witness ERROR(INSUFFICIENT_GAS)



  // | ERROR(error:Error,gas:nat := 0, data: Array<u8> := [])
  // | RETURNS(gas:nat,data: Array<u8>,world: WorldState.T,substate:SubState.T)
  // | CONTINUING(Continuation) {

}