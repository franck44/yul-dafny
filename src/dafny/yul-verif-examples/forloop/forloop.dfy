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

include "../../Yul/Semantics.dfy"

/**
  * A simple example with a sequence and an if statement.
  */
module forLoopYul {

  import opened Int
  import opened Yul
  import Memory

  /**
    *  Translation of Yul code of main in Dafny.
    */
  method Main(m: Memory.T) returns (m': Memory.T)
    requires Memory.Size(m) % 32 == 0
    ensures Memory.Size(m') > 31
    // ensures Memory.ReadUint256(m', 0x40) == 8
  {
    // var x := 8;                     //  let
    // var y := 3;                     //  let
    // var z, m1 := Max(x, y, m);      //  funcall. Returns result ans new memory.
    // m' := mstore(0x40, z, m1);      //  memory store
    var x: u256 := 0;
    m' := m;
    while lt(x, 10) > 0 
        decreases 10 - x
        invariant x <= 10
        invariant x > 0 ==> Memory.Size(m') >= 32 as nat 
    {
        m' := mstore(x, mul(x, 0x1), m); 
        x := add(x, 1);
    }
    assert Memory.Size(m') >= 32;
  }

  /**
    *  Run the code.
    */
//   method {:main} Test()
//   {
//     var m := Main(Memory.Create());
//     print Memory.ReadUint256(m, 0x40), "\n";
//   }

}