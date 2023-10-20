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

include "./Semantics.dfy"
include "./StrictSemantics.dfy"
include "./State.dfy"

module CommonFunctions {

  import opened Int
  import opened YulStrict
  import opened YulState
  import ByteUtils


  /** Get the free memory pointer. */
  method allocate_unbounded(s: Executing) returns (memPtr: u256, s': State)
    ensures s'.EXECUTING?
    ensures s'.Context() == s.Context()
    ensures s'.World() == s.World()
    ensures s.MemSize() >= 96 ==> memPtr == s.Read(64)
  {
    return MLoad(64, s).0, MLoad(64, s).1;
  }

  // Reverts and Panic

  method revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(s: Executing) returns (s': State)
    ensures s'.ERROR?
  {
    return Revert(0, 0, s);
  }

  method revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(s: Executing) returns (s': State)
    ensures s'.ERROR?
  {
    return Revert(0, 0, s);
  }

  function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db(s: Executing): (s': State) {
    Revert(0, 0, s)
  }

  function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74(s: Executing): (s': State)
  {
    Revert(0, 0, s)
  }

  function panic_error_0x11(s: Executing): (s': State)
  {
    var s1 := MStore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856, s);
    var s2 := MStore(4, 0x11, s1);
    Revert(0, 0x24, s2)
  }

  function panic_error_0x32(s: Executing): (s': State) {
    var s1 := MStore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856, s);
    var s2 := MStore(4, 0x32, s1);
    Revert(0, 0x24, s2)
  }

  //  abi_ functions

  /**
    *   Check interval between two numbers.
    *   @param  headStart   
    *   @param  dataEnd
    *   @param  s          A state.
    *   @returns           `revert` if dataEnd < headStart and `s` otherwise.
    */
  method abi_decode_tuple_(headStart: u256, dataEnd: u256, s: Executing) returns (s': State)
    requires -TWO_255 <= dataEnd as int - headStart as int < TWO_255
    ensures headStart <= dataEnd ==> s' == s
    ensures s'.EXECUTING? ==> s' == s
  {
    if SLt(Sub(dataEnd, headStart), 0) {
      s' := revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(s) ;
    }
    return s;
  }

  /**
    *  Store value at address `pos` in Memory.
    */
  method abi_encode_t_uint256_to_t_uint256_fromStack(value: u256, pos: u256, s: Executing) returns (s': State)
    ensures s'.EXECUTING?
    ensures s'.MemSize() > pos as nat + 31
    ensures s'.Context() == s.Context()
    ensures s'.World() == s.World()
    ensures Memory.ReadUint256(s'.yul.memory, pos as nat) == value
  {
    var k := cleanup_t_uint256(value);
    s' := MStore(pos, k, s);
  }

  /**
    *  Store value0 at address headStart in memory and return the 
    *  next available? memory slot (23-bytes)
    */
  method abi_encode_tuple_t_uint256__to_t_uint256__fromStack(headStart: u256 , value0: u256, s: Executing) returns (tail: u256, s': State)
    requires headStart as nat + 32 < TWO_256
    ensures s'.EXECUTING?
    ensures tail == headStart + 32
    ensures headStart as nat + 31 < s'.MemSize()
    ensures Memory.ReadUint256(s'.yul.memory, headStart as nat) == value0
    ensures s'.World() == s.World()
  {
    tail := Add(headStart, 32);
    s' := abi_encode_t_uint256_to_t_uint256_fromStack(value0,  Add(headStart, 0), s);
  }

  method abi_decode_t_uint256(offset: u256, end: u256, s: Executing) returns (value: u256, s': State)
    ensures s' == s
    ensures offset < CallDataSize(s) ==> value == s.Context().CallDataRead(offset) == ByteUtils.ReadUint256(s.Context().callData, offset as nat)
  {
    value := CallDataLoad(offset, s);
    s' := validator_revert_t_uint256(value, s);
  }

  method abi_decode_tuple_t_uint256(headStart: u256, dataEnd: u256, s: Executing) returns (value0: u256, s': State)
    requires -TWO_255 <= dataEnd as int - headStart as int < TWO_255
    requires headStart <= dataEnd <= CallDataSize(s)
    ensures dataEnd as int - headStart as int >= 32 ==> s'.EXECUTING?
    ensures dataEnd as int - headStart as int < 32 ==> s'.ERROR?
    ensures s'.EXECUTING? ==> s' == s
    ensures s'.EXECUTING? ==> value0 == ByteUtils.ReadUint256(s.Context().callData, headStart as nat)
  {
    if SLt(Sub(dataEnd, headStart), 32) {
      s' := revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(s);
      value0 := 0;
      return;
    }
    {
      var offset := 0;
      value0, s' := abi_decode_t_uint256(Add(headStart, offset), dataEnd, s);
      assert value0 == s.Context().CallDataRead(headStart) == ByteUtils.ReadUint256(s.Context().callData, headStart as nat);
    }
  }

  method abi_decode_tuple_t_uint256t_uint256(headStart: u256, dataEnd: u256, s: Executing) returns (value0: u256, value1: u256, s': State)
    requires -TWO_255 <= dataEnd as int - headStart as int < TWO_255
    requires headStart <= dataEnd <= CallDataSize(s)
    ensures dataEnd as int - headStart as int >= 64 ==> s'.EXECUTING?
    ensures dataEnd as int - headStart as int < 64 ==> s'.ERROR?
    ensures s'.EXECUTING? ==> s' == s
    ensures s'.EXECUTING? ==> value0 == ByteUtils.ReadUint256(s.Context().callData, headStart as nat)
    ensures s'.EXECUTING? ==> value1 == ByteUtils.ReadUint256(s.Context().callData, headStart as nat + 32)
  {
    if SLt(Sub(dataEnd, headStart), 64) {
      s' := revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(s);
      value0, value1 := 0, 0;
      return;
    }
    {
      var offset := 0;
      value0, s' := abi_decode_t_uint256(Add(headStart, offset), dataEnd, s);
      assert value0 == s.Context().CallDataRead(headStart) == ByteUtils.ReadUint256(s.Context().callData, headStart as nat);
    }
    {
      var offset := 32;
      value1, s' := abi_decode_t_uint256(Add(headStart, offset), dataEnd, s);
      assert value1 == s.Context().CallDataRead(headStart + 32) == ByteUtils.ReadUint256(s.Context().callData, headStart as nat + 32);
    }
  }

  function {:opaque} abi_encode_tuple__to__fromStack(headStart: u256): (tail: u256)
    ensures tail == headStart
  {
    Add(headStart, 0)
  }

  //  Shift functions

  /** Get leftmost 4-bytes of a u256. */
  function shift_right_224_unsigned(value: u256): (newValue: u256)
  {
    Shr(value, 224)
  }

  /**
    * Shift right.
    */
  function shift_right_unsigned_dynamic(bits: u256, value: u256): (newValue: u256)
  {
    Shr(value, bits)
  }

  /**
    *  Another function that is the identity.
    */
  function {:opaque} shift_right_0_unsigned(value: u256): (newValue: u256)
    ensures value == newValue
  {
    Shr(value, 0)
  }

  function {:opaque} shift_left_0(value: u256): (newValue: u256)
    ensures newValue == value
  {
    Shl(value, 0)
  }

  //  Cleanup functions

  /**
    *  Another identity function,
    */
  function cleanup_t_uint256(value: u256): (cleaned: u256)
  {
    value
  }

  function identity(value: u256): (ret:u256)
  {
    value
  }

  function convert_t_uint256_to_t_uint256(value: u256): (converted: u256)
    ensures converted == value
  {
    cleanup_t_uint256(identity(cleanup_t_uint256(value)))
  }

  function prepare_store_t_uint256(value: u256): (ret: u256)
  {
    value
  }

  /**
    *   This function does not do anything (provably).
    */
  function validator_revert_t_uint256(value: u256, s: Executing): (s': State)
    ensures s' == s
  {
    if !Eq(value, cleanup_t_uint256(value)) then
      // this test is never true.
      assert false;
      Revert(0, 0, s)
    else s
  }

  /**
    *  In this context cleanup is the identity.
    */
  function cleanup_from_storage_t_uint256(value: u256): (cleaned: u256)
  {
    value
  }

  //    Storage functions

  /**
    *   ??
    */
  function extract_from_storage_value_dynamict_uint256(slot_value: u256, offset: u256) : (value: u256)
    requires offset as nat * 8 < TWO_256
  {
    var k := shift_right_unsigned_dynamic(Mul(offset, 8), slot_value);
    cleanup_from_storage_t_uint256(k)
  }

  /**
    *   ??
    */
  function read_from_storage_split_dynamic_t_uint256(slot: u256, offset: u256, s: Executing): (value: u256)
    requires offset as nat * 8 < TWO_256
    ensures offset == 0 ==> value == s.SLoad(slot)
  {
    extract_from_storage_value_dynamict_uint256(SLoad(slot, s), offset)
  }

  function extract_from_storage_value_offset_0t_uint256(slot_value: u256): (value: u256)
  {
    cleanup_from_storage_t_uint256(shift_right_0_unsigned(slot_value))
  }

  function read_from_storage_split_offset_0_t_uint256(slot: u256, s: Executing): (value: u256)
  {
    extract_from_storage_value_offset_0t_uint256(SLoad(slot, s))
  }

  function update_storage_value_offset_0t_uint256_to_t_uint256(slot: u256, value_0: u256, s: Executing) : (s': State)
    ensures s'.EXECUTING?
    ensures s'.SLoad(slot) == value_0
    ensures s'.MemSize() == s.MemSize()
  {
    var convertedValue_0 := convert_t_uint256_to_t_uint256(value_0);
    SStore(slot, update_byte_slice_32_shift_0(SLoad(slot, s), prepare_store_t_uint256(convertedValue_0)), s)
  }

  //  Misc.

  lemma NSCOverFlowU256(x: u256, y: u256)
    ensures x as nat + y as nat < TWO_256 ==> YulSem.Add(x, y) as nat == x as nat + y as nat
    ensures YulSem.Add(x ,y) >= x ==> x as nat + y as nat < TWO_256
    ensures x as nat + y as nat < TWO_256 <==> YulSem.Add(x ,y) >= x
    ensures x as nat + y as nat < TWO_256 <==> !Gt(x, YulSem.Add(x ,y))
  {
  }

  method checked_add_t_uint256(x: u256, y: u256, s: Executing) returns (sum: u256, s': State)
    ensures x as nat + y as nat < TWO_256 <==> s'.EXECUTING?
    ensures x as nat + y as nat >= TWO_256 <==> s'.ERROR?

    ensures s'.EXECUTING? ==> s' ==  s
    ensures s'.EXECUTING? ==> sum == x + y
  {
    var x1 := cleanup_t_uint256(x);
    var y1 := cleanup_t_uint256(y);
    sum := YulSem.Add(x1, y1);
    NSCOverFlowU256(x1, sum);
    s' := s;
    if Gt(x1, sum) {
      //  Overflow, revert
      assert x as nat + y as nat >= TWO_256;
      return 0, panic_error_0x11(s);
    }
    //  no overflow
    assert x as nat + y as nat < TWO_256;
  }

  function {:opaque} update_byte_slice_32_shift_0(value: u256, toInsert: u256): (result: u256)
    ensures result == toInsert
  {
    // 64 fs => TWO_256 - 1
    var mask := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
    var toInsert_ := shift_left_0(toInsert);
    assert toInsert_ == toInsert;
    var value_ := And(value, Not(mask));
    assert value_ == 0;
    XAnd1IsX(toInsert, mask);
    assert And(toInsert_, mask) == toInsert;
    assert Or(value_, And(toInsert_, mask)) == toInsert;
    Or(value_, And(toInsert_, mask))
  }

}

