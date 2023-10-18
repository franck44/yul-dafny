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
  * A simple example to store and retrieve elements
  * in a dynamic-sized array.
  *
  * Assume with have an array `uin256[] a`
  */
module DynArray {

  import opened Int
  import opened YulSem = YulStrict
  import opened YulState

  ghost predicate Inv
  {
    true
  }

  datatype Try<T> = Success(v: T) | Failure(e: State)

  /**
    *   Get an element.
    *   @param  pos     The storage slot number that contains the length of the array.  
    *   @param  index   The index of the element to be retrieved.
    *
    *   @note           We use the scratchpad zone of memory (< 0x20) to
    *                   store the value to be hashed.
    */
  method Get(pos: u256, index: u256, s: Executing) returns (result: Try<u256>)
    requires s.MemSize() % 32 == 0
    /** Index must be within current size of array, stored at `pos`. */
    requires index < SLoad(pos, s)
    requires 0x20 < s.MemSize()
  {
    //  Store the slot number at location 0x00
    var s1 := MStore(0x00, pos, s);
    //  Compute the storage location of the first element of the array.
    var firstElemPos := Keccak256(0x00, 1, s1);
    //  Check that first position + index does not exceed TWO_256
    if firstElemPos < (TWO_256 - 1 - index as nat) as u256 {
      return Success(SLoad(firstElemPos + index, s));
    } else {
      return Failure(Revert(0, 0, s));
    }
  }

  /**
    *   Add an element at the end of the array.
    *   @param  pos     The slot number that contains the length of the array.  
    *   @param  index   The value to be appended at the end.
    */
  //   method Push(pos: u256, val: u256, s: Executing) returns (s': State)
  //     /** Array length is not TWO_256. */
  //     requires SLoad(pos, s) as nat < TWO_256 - 1
  //     /** Decoding the first slot of the array   */
  //     requires pos as nat + 1 < s.MemSize()
  //     requires SLoad(pos, s) as nat + Keccak256(pos, 1, s) as nat + 1 < TWO_256
  //   {
  //     var currentLength := SLoad(pos, s);
  //     var firstElemPos := Keccak256(pos, 1, s);
  //     var s1 := SStore(pos, currentLength + 1, s);
  //     return SStore(firstElemPos + currentLength + 1, val, s1);
  //   }

  /**
    *  Set an index to a given value,
    */
  method Set(x: u256, y: u256, s: Executing) returns (s': State)
    // ensures result == x || result == y
    // ensures result >= x && result >= y
    // ensures s' == s        //  Memory is not modified
    // ensures Memory.Size(m') == Memory.Siz(m)
  {
    return s;
    // s' := s;
    // result := x;
    // if Lt(x, y) {
    //   result := y;
    // }
  }

  /**
    *  Translation of Yul code of main in Dafny.
    */
  //   method Main(s: Executing) returns (s': State)
  //     requires s.MemSize() % 32 == 0
  //     ensures s'.EXECUTING?
  //     ensures s'.MemSize() > 0x40 + 31
  //     // ensures Memory.ReadUint256(m', 0x40) == 8
  //   {
  //     var x := 8;                     //  let
  //     var y := 3;                     //  let
  //     var z, s1 := Max(x, y, s);      //  funcall. Returns result ans new memory.
  //     s' := MStore(0x40, z, s1);      //  memory store
  //   }

  /**
    *  Run the code. 
    */
  //   method {:main} {:verify false} Test()
  //   {
  //     var s := Main(YulState.Init());
  //     print s.Read(0x40), "\n";
  //   }

}