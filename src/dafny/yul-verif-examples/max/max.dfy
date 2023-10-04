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
module maxYul {

  import opened Int
  import opened YulStrict
  import opened YulState

  /**
    *  Translation of the of the Yul code of max in Dafny.
    */
  method Max(x: u256, y: u256, s: Executing) returns (result: u256, s': State) 
    ensures result == x || result == y
    ensures result >= x && result >= y
    ensures s' == s        //  Memory is not modified
    // ensures Memory.Size(m') == Memory.Siz(m)
  {
    s' := s;
    result := x;
    if lt(x, y) {
      result := y;
    }
  }

  /**
    *  Translation of Yul code of main in Dafny.
    */
  method Main(s: Executing) returns (s': State)  
    requires s.MemSize() % 32 == 0
    ensures s'.MemSize() > 0x40 + 31
    // ensures Memory.ReadUint256(m', 0x40) == 8
  {
    var x := 8;                     //  let
    var y := 3;                     //  let
    // var z, m1 := Max(x, y, m);      //  funcall. Returns result ans new memory.
    // m' := MStore(0x40, z, m1);      //  memory store
  }

  /**
    *  Run the code.
    */
  method {:main} {:verify false} Test()  
  {
    var s := Main(YulState.Init());
    print s.Read(0x40), "\n";
  }

}