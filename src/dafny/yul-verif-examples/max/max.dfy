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
module maxYul {

  import opened Int
  import ByteUtils
  import opened YulStrict
  import opened YulState

  /**
    *  Translation of the of the Yul code of max in Dafny.
    */
  method Max(x: u256, y: u256) returns (result: u256)
    ensures result == maxu256(x, y)
  {
    // s' := s;
    result := x;
    if Lt(x, y) {
      result := y;
    }
  }

  /**
    *  Translation of Yul code of main in Dafny.
    */
  method Main(s: Executing) returns (s': State)
    ensures s'.RETURNS?
    ensures ByteUtils.ReadUint256(s'.data, 0) == 8
  {
    var x := 8;                     //  let
    var y := 3;                     //  let
    var z := Max(x, y);      //  funcall. Returns result ans new memory.
    var s2 := MStore(0x40, z, s);  //  memory store
    return Return(0x40, 32, s2);    //  return result
  }

  /**
    *   A ghost (verification-only) function.
    */
  ghost function maxu256(x: u256, y: u256): (r: u256)
    ensures r == x || r == y
    ensures r >= x && r >= y
  {
    if x <= y then y else x
  }

  /**
    *  Generalisation of Yul code of main in Dafny.
    */
  method Main2(s: Executing, x: u256, y: u256) returns (s': State)
    ensures s'.RETURNS?
    ensures ByteUtils.ReadUint256(s'.data, 0) == maxu256(x, y)
  {
    var z := Max(x, y);      //  funcall. Returns result ans new memory.
    var s2 := MStore(0x40, z, s);  //  memory store
    return Return(0x40, 32, s2);    //  return result
  }

  /**
    *  Run the code. 
    */
  method {:main} {:verify true} Test()
  {
    var s := Main(YulState.Init());
    assert s.RETURNS?;
    print ByteUtils.ReadUint256(s.data, 0), "\n";
  }

}