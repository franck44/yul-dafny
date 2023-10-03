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
include "../../Yul/VerifSemantics.dfy"

/**
  * A simple example with a sequence and an if statement.
  */
module forLoopYul {

  import opened Int
  import opened YulStrict
  import Memory

  /**
    *  Translation of Yul code of main in Dafny.
    */ 
  method Main(m: Memory.T) returns (m': Memory.T)
    requires Memory.Size(m) % 32 == 0
    ensures Memory.Size(m') >= 10 * 32 
  {
    var x: u256 := 0;
    m' := m;
    while lt(x, 10)
        decreases 10 - x
        invariant x <= 10 
        invariant Memory.Size(m') % 32 == 0
        invariant x > 0 ==> Memory.Size(m') >= x as nat * 32    
    {
        m' := mstore(Mul(x, 32), Mul(x, 0x01), m'); 
        x := Add(x, 1);
    }
  }

  /**
    *  Run the code.
    */
  method {:main} Runner()
  {
    var m := Memory.Create();
    assert Memory.Size(m) == 0;
    var m' := Main(m);

    assert Memory.Size(m') >= 32 * 10;

    for i := 0 to 10
        invariant Memory.Size(m') >=  32 *10
    {
        print "Memory[", 32 * i, "..", 32 * i + 31 ,"] = ", Memory.ReadUint256(m', i * 32), " (u256)\n";
    }
    
  }

}