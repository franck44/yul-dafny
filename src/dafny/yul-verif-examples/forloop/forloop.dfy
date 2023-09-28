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
    ensures Memory.Size(m') >= 10 * 32 
  {
    var x: u256 := 0;
    m' := m;
    while lt(x, 10) > 0 
        decreases 10 - x
        invariant x <= 10 
        invariant x as nat * 32 < TWO_256
        invariant mul(x, 32) == x * 32 
        invariant Memory.Size(m') % 32 == 0
        invariant x > 0 ==> Memory.Size(m') >= mul(x - 1, 32) as nat + 32    
    {
        m' := mstore(mul(x, 32), mul(x, 0x01), m'); 
        assert Memory.Size(m') >= mul(x, 32) as nat + 32 ;  
        assert Memory.Size(m') % 32 == 0;
        x := add(x, 1);
    }
  }

  /**
    *  Run the code.
    */
  method {:main} Test()
  {
    var m := Memory.Create();
    assert Memory.Size(m) == 0;
    var m' := Main(m);

    assert Memory.Size(m') >= 32 * 10;

    for i := 0 to 10
        invariant Memory.Size(m') >=  32 *10
    {
        print "Memory[", i, "] = ", Memory.ReadUint256(m', i * 32), "\n";
    }
    
  }

}