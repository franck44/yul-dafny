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
include "../../Yul/StrictSemantics.dfy"

/**
  * A simple example with a sequence and an if statement.
  */
module forLoopYul {

  import opened Int
  import opened YulState
  import opened YulSem = YulStrict
  import Memory

  /**
    *  Translation of Yul code of main in Dafny.
    */ 
  method Main(s: Executing) returns (s': State)
    requires s.MemSize() % 32 == 0
    ensures s'.EXECUTING?
    ensures s'.MemSize() >= 10 * 32 
  {
    var x: u256 := 0;
    s' := s;
    while lt(x, 10)
        decreases 10 - x
        invariant x <= 10 
        invariant s'.EXECUTING?
        invariant s'.MemSize() % 32 == 0
        invariant x > 0 ==> s'.MemSize() >= x as nat * 32    
    {
        s' := YulSem.MStore(Mul(x, 32), Mul(x, 0x01), s'); 
        x := Add(x, 1);
    }
  }

  /**
    *  Run the code.
    */
  method {:main} Runner()
  {
    var s := YulState.Init();
    assert s.MemSize() == 0;
    var s' := Main(s);

    assert s'.MemSize() >= 32 * 10;

    for i := 0 to 10
        invariant s'.EXECUTING?
        invariant s'.MemSize() >=  32 *10
    {
        print "Memory[", 32 * i, "..", 32 * i + 31 ,"] = ", s'.Read(i * 32), " (u256)\n"; 
    }
    
  }

}