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

include "./erc-20.dfy"

module A {

  import opened Int
  import opened YulStrict
  import opened YulState
  import opened ERC20

  /**
    * A simple example with a sequence and an if statement.
    */
  class KERC20 {

    // ghost var totalSupply: u256

    // var memory: seq<u8>

    //  Arbitry address
    var address: u160

    // var storage: map<u256, u256>

    var world: WorldState.T

    constructor(a: u160)
      requires a > 0
      ensures GInv()
    {
      address := a;
      //   totalSupply := 0 ;
      //  Initial memory is empty
      // memory := [] ;
      //  Storage allocated
      // storage := map[0 := 0];
      world := WorldState.Create(map[0:=WorldState.DefaultAccount(), a := WorldState.DefaultAccount()]);
    }

    predicate GInv()
      reads `address, `world
    {
      && address in world.accounts
      && address > 0
         //   && foo() == 0
         // totalSupply ==
         //  some of balances should be total supply
    }

    function InitContext(callValue:u256,callData:Arrays.Array<u8>) : Context.T
      reads `address
    {
      Context.Context(
        sender := 0,
        origin := 0,
        address:= address,
        callValue:=callValue,
        callData:=callData,
        returnData:=[],
        writePermission:=true,
        gasPrice:= 0,
        block:= Context.Block.Info(0,0,0,0,0,0)
      )
    }

    // A simple witness of the Context datatype.
    // const DEFAULT : T := Create(0,0,0,0,[],true,0,Block.Info(0,0,0,0,0,0))

    method Execute(callValue:u256, callData:Arrays.Array<u8>)
      requires GInv()
      ensures GInv()

      modifies `world
    //   ensures 
    {
      assert address in world.accounts;
      var s0: State :=
        EXECUTING(
          EState(
            // get ABI and add to context
            InitContext(callValue, callData),
            Memory.Create(),
            world,
            Precompiled.DEFAULT
          )
        );

      assert s0.EXECUTING?;
      assert s0.MemSize() % 32 == 0;
      assert address > 0 && s0.yul.context.address == address;

    //   var s':= Main(s0, s0.Load(0), address);
    //   assert s'.RETURNS? || s'.ERROR?;

    //   if |callData| < 4 {
    //     assert s'.ERROR?;
    //     // assert assert s'.world == world;
    //   } else {
    //     match Selector(s0) 
    //         case TotalSupplySelector => 
    //             assert s'.RETURNS?;
    //             assert s'.world.accounts[address] == world.accounts[address];
    //             assert false;
    //         case MintSelector => 
    //             assert true;
    //         case _ => 
    //             assert s'.ERROR?;
    //   }
    }
  }
}
