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
include "../../Yul/State.dfy"

/**
  * A simple example with a sequence and an if statement.
  */
module ERC20 {

  import opened Int
  import opened YulStrict
  import YulSem
  import opened YulState
  import ByteUtils

  /**
    *   The selector for the two function totalSupply (getter) and mint.
    */
  const TotalSupplySelector: u256 := 0x18160ddd
  const MintSelector: u256 := 0xa0712d68

  /**
    *  Extract selector from calldata.
    *  @param  s   A Yul state.
    *  @returns    The first 4 bytes of the calldataload, as a u256.
    */
  function Selector(s: Executing): u256
    requires CallDataSize(s) >= 4
  {
    shift_right_224_unsigned(CallDataLoad(0, s))
  }

  /**
    *   Dispatch and execute code.
    *   @param  s   A Yul state.
    *   @returns    The state reached after executing the call 
    *               given byt the calldataload.
    */
  method Dispatch(s: Executing) returns (s': State)
    /** Calldataload cannot be two large. */
    requires TWO_255 - 1 > CallDataSize(s) as nat

    /** The returned state is either an RETURN or an ERROR. */
    ensures s'.RETURNS? || s'.ERROR?
    /** If not enough calldata, revert. */
    ensures CallDataSize(s) < 4 ==> s'.ERROR? 

    /** Accounts are not modified. */
    ensures s'.RETURNS? ==> s.yul.world.accounts == s'.world.accounts
    ensures s'.RETURNS? ==> CallDataSize(s) as nat >= 4

    ensures CallDataSize(s) as nat >= 4 && Selector(s) == TotalSupplySelector && CallValue(s) == 0 ==> s'.RETURNS?
    // ensures CallDataSize(s) >= 36 && Selector(s) == MintSelector && (s.Load(0) as nat + ByteUtils.ReadUint256(s.yul.context.callData, 4) as nat) < TWO_256 ==> s'.RETURNS?
    ensures s'.RETURNS? && Selector(s) == TotalSupplySelector ==> Storage.Read(s'.world.accounts[s.yul.context.address].storage, 0) ==  s.SLoad(0)
    ensures s'.RETURNS? && Selector(s) == TotalSupplySelector ==> s'.RETURNS? ==> ByteUtils.ReadUint256(s'.data, 0) == s.SLoad(0)
    // ensures s'.RETURNS? && Selector(s) == MintSelector ==> Storage.Read(s'.world.accounts[account].storage, 0) ==  s.SLoad(0) + ByteUtils.ReadUint256(s.yul.context.callData, 4)
    // ensures (CallDataSize(s) < 4 || (Selector(s) !=  TotalSupplySelector && Selector(s) != MintSelector)) ==> s'.ERROR?
  {

    // var s1 := MStore(64, MemoryGuard(128), s);
    // assert s1.Read(64) == 128;
    // assert CallDataSize(s1) == CallDataSize(s);
    var s1 := s;

    if !Lt(CallDataSize(s1), 4) {
      //  There is enough calldata for a 4-byte selector
      assert CallDataSize(s1) >= 4;
      //  Extract selector
      var selector: u256 := Selector(s1);
      match selector

      case TotalSupplySelector =>
        {
          // totalSupply()
          s' := external_fun_totalSupply_3(s1);
          return;
        }

      case MintSelector =>
        {
          // mint(uint256)
          s':= external_fun_mint_13(s1);
          return;
        }

      case _ =>
        // assert false;
        return Revert(0, 0, s1);

    }
    //  Here we should revert as the calldataload does not have enough bytes.
    assert CallDataSize(s1) < 4;
    return Revert(0, 0, s1);
  }

  /** Get leftmost 4-bytes of a u256. */
  function shift_right_224_unsigned(value: u256): (newValue: u256)
  {
    Shr(value, 224)
  }

  /** Get the free memory pointer. */
  method allocate_unbounded(s: Executing) returns (memPtr: u256, s': State)
    ensures s'.EXECUTING?
    ensures s'.yul.context == s.yul.context
    ensures s'.yul.world == s.yul.world
    ensures s.MemSize() >= 96 ==> memPtr == s.Read(64)
  {
    return MLoad(64, s).0, MLoad(64, s).1;
  }

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
    * Shift right.
    */
  function shift_right_unsigned_dynamic(bits: u256, value: u256): (newValue: u256)
  {
    Shr(value, bits)
  }

  /**
    *  In this context cleanup is the identity.
    */
  function cleanup_from_storage_t_uint256(value: u256): (cleaned: u256)
  {
    value
  }

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

  /**
    *    The auto-generated getter for totoalSupply.
    */
  method getter_fun_totalSupply_3(s: Executing) returns (ret: u256)
    ensures ret == s.SLoad(0)
  {
    var slot := 0;
    var offset := 0;
    ret := read_from_storage_split_dynamic_t_uint256(slot, offset, s);
  }

  /**
    *  Another identity function,
    */
  function cleanup_t_uint256(value: u256): (cleaned: u256)
  {
    value
  }

  /**
    *  Store value at address `pos` in Memory.
    */
  method abi_encode_t_uint256_to_t_uint256_fromStack(value: u256, pos: u256, s: Executing) returns (s': State)
    ensures s'.EXECUTING?
    ensures s'.MemSize() > pos as nat + 31
    ensures s'.yul.context == s.yul.context
    ensures s'.yul.world == s.yul.world
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
    ensures s'.yul.world == s.yul.world
  {
    tail := Add(headStart, 32);
    s' := abi_encode_t_uint256_to_t_uint256_fromStack(value0,  Add(headStart, 0), s);
  }


  method external_fun_totalSupply_3(s: Executing) returns (s': State)
    requires 4 <= CallDataSize(s) as nat < TWO_255 - 1

    ensures CallValue(s) > 0 <==> s'.ERROR?
    ensures s'.ERROR? || s'.RETURNS?
    ensures s'.RETURNS? ==> |s'.data| == 32
    ensures s'.RETURNS? ==> ByteUtils.ReadUint256(s'.data, 0) == s.SLoad(0)
    ensures s'.RETURNS? ==> s.yul.world.accounts == s'.world.accounts
    ensures s'.RETURNS? ==> Storage.Read(s'.world.accounts[s.yul.context.address].storage, 0) == s.SLoad(0)
    // Storage.Read(s'.world.accounts[s.yul.context.address].storage, 0) ==  s.SLoad(0);
    // ensures
  {
    if CallValue(s) > 0 {
      //  Not payable
      var s1 := revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(s);
      return s1;
    }
    assert CallValue(s) == 0;
    var s1 := abi_decode_tuple_(4, CallDataSize(s), s);
    var ret_0 :=  getter_fun_totalSupply_3(s1);
    var memPos, s2 := allocate_unbounded(s1);
    var memEnd, s3 := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0, s2);
    assert Memory.ReadUint256(s3.yul.memory, memPos as nat) == ret_0;
    // var x := RETURNS(data := Memory.Slice(s3.yul.memory, memPos as nat, (memEnd - memPos) as nat));
    var x := Return(memPos, memEnd - memPos, s3);

    assert s.yul.context.address in x.world.accounts;
    assert ByteUtils.ReadUint256(x.data, 0) == Memory.ReadUint256(s3.yul.memory, memPos as nat) == s.SLoad(0);
    assert x.world.accounts == s.yul.world.accounts;
    assert Storage.Read(x.world.accounts[s.yul.context.address].storage, 0) == s.SLoad(0);
    //  Return with data = memory slice between memPos of length memEnd - memPos
    //   return RETURNS(data := Memory.Slice(s2.yul.memory, memPos as nat, (memEnd - memPos) as nat));
    return x;
    // }

  }

  function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db(s: Executing): (s': State) {
    Revert(0, 0, s)
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

  method abi_decode_t_uint256(offset: u256, end: u256, s: Executing) returns (value: u256, s': State)
    ensures s' == s
    ensures offset < CallDataSize(s) ==> value == s.yul.context.CallDataRead(offset) == ByteUtils.ReadUint256(s.yul.context.callData, offset as nat)
  {
    value := CallDataLoad(offset, s);
    s' := validator_revert_t_uint256(value, s);
  }

  method abi_decode_tuple_t_uint256(headStart: u256, dataEnd: u256, s: Executing) returns (value0: u256, s': State)
    requires -TWO_255 <= dataEnd as int - headStart as int < TWO_255
    ensures dataEnd as int - headStart as int >= 32 ==> s'.EXECUTING?
    ensures dataEnd as int - headStart as int < 32 ==> s'.ERROR?
    ensures s'.EXECUTING? ==> s' == s
    ensures s'.EXECUTING? ==> value0 == ByteUtils.ReadUint256(s.yul.context.callData, headStart as nat)
  {
    if SLt(Sub(dataEnd, headStart), 32) {
      s' := revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(s);
      value0 := 0;
      return;
    }
    {
      var offset := 0;
      value0, s' := abi_decode_t_uint256(Add(headStart, offset), dataEnd, s);
      assert value0 == s.yul.context.CallDataRead(headStart) == ByteUtils.ReadUint256(s.yul.context.callData, headStart as nat);
    }

  }

  function {:opaque} abi_encode_tuple__to__fromStack(headStart: u256): (tail: u256)
    ensures tail == headStart
  {
    Add(headStart, 0)
  }

  /**
    *  Increase totalSupply by a given amount if possible.
    */
  method external_fun_mint_13(s: Executing) returns (s': State)
    requires 4 <= CallDataSize(s) as nat < TWO_255 - 1
    ensures CallDataSize(s) < 36 ==> s'.ERROR?
    ensures CallDataSize(s) >= 36 && (s.SLoad(0) as nat + ByteUtils.ReadUint256(s.yul.context.callData, 4) as nat) >= TWO_256 ==> s'.ERROR?
    ensures s'.RETURNS? || s'.ERROR?
    ensures s'.RETURNS? ==> s'.world.accounts.Keys == s.yul.world.accounts.Keys
    ensures  s'.RETURNS? ==> Storage.Read(s'.world.accounts[s.yul.context.address].storage, 0) ==  s.SLoad(0) + ByteUtils.ReadUint256(s.yul.context.callData, 4)
    // ensures s'.EXECUTING? ==> CallDataSize(s) >= 36
    // ensures s'.EXECUTING? ==> (s.SLoad(0) as nat + ByteUtils.ReadUint256(s.yul.context.callData, 4) as nat) < TWO_256
    // ensures s'.EXECUTING? ==> s'.Load(0) == s.SLoad(0) +  ByteUtils.ReadUint256(s.yul.context.callData, 4)
  {
    if CallValue(s) > 0 {
      //  Not payable, revert
      s' := revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(s);
      return;
    }
    var param_0, s1 :=  abi_decode_tuple_t_uint256(4, CallDataSize(s), s);
    if s1.ERROR? {
      s' := s1;
    } else {
      var s2 := fun_mint_13(param_0, s1);
      if !s2.EXECUTING? {
        //  Overflow
        assert s2.ERROR?;
        assert s.SLoad(0) as nat + param_0 as nat >= TWO_256;
        return s2;
      }
      // no Overflow
      assert s1.SLoad(0) as nat + param_0 as nat < TWO_256;
      assert s2.SLoad(0) == s.SLoad(0) + param_0;
      var memPos, s3 := allocate_unbounded(s2);
      var memEnd := abi_encode_tuple__to__fromStack(memPos);

      assert memPos == memEnd;
      s' := Return(memPos, memEnd - memPos, s3);
      //    The data returned is empty.
      assert |s'.data| == 0;
      return;
    }
  }

  function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74(s: Executing): (s': State)
  {
    Revert(0, 0, s)
  }

  /**
    *  Another function that is the identity.
    */
  function {:opaque} shift_right_0_unsigned(value: u256): (newValue: u256)
    ensures value == newValue
  {
    Shr(value, 0)
  }

  function extract_from_storage_value_offset_0t_uint256(slot_value: u256): (value: u256)
  {
    cleanup_from_storage_t_uint256(shift_right_0_unsigned(slot_value))
  }

  function read_from_storage_split_offset_0_t_uint256(slot: u256, s: Executing): (value: u256)
  {
    extract_from_storage_value_offset_0t_uint256(SLoad(slot, s))
  }

  function panic_error_0x11(s: Executing): (s': State)
  {
    var s1 := MStore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856, s);
    var s2 := MStore(4, 0x11, s1);
    Revert(0, 0x24, s2)
  }

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
    ensures x as nat + y as nat < TWO_256 <==> sum as nat == x as nat + y as nat
    ensures s'.EXECUTING? ==> s'.MemSize() == s.MemSize()
    ensures s'.EXECUTING? ==> s'.yul.world.accounts.Keys == s.yul.world.accounts.Keys
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

  function {:opaque} shift_left_0(value: u256): (newValue: u256)
    ensures newValue == value
  {
    Shl(value, 0)

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

  function update_storage_value_offset_0t_uint256_to_t_uint256(slot: u256, value_0: u256, s: Executing) : (s': State)
    ensures s'.EXECUTING?
    ensures s'.SLoad(slot) == value_0
    ensures s'.MemSize() == s.MemSize()
  {
    var convertedValue_0 := convert_t_uint256_to_t_uint256(value_0);
    SStore(slot, update_byte_slice_32_shift_0(SLoad(slot, s), prepare_store_t_uint256(convertedValue_0)), s)
  }

  method fun_mint_13(var_amount_5: u256, s: Executing) returns (s': State)
    ensures s'.EXECUTING? <==> s.SLoad(0) as nat + var_amount_5 as nat < TWO_256
    ensures s'.EXECUTING? ==> s'.SLoad(0) == s.SLoad(0) + var_amount_5
    ensures s'.EXECUTING? ==> s'.yul.world.accounts.Keys == s.yul.world.accounts.Keys
    ensures s'.ERROR? || s'.EXECUTING?
  {
    /// @src 0:1314:1320  "amount"
    var v_1 := var_amount_5;
    var expr_9 := v_1;
    /// @src 0:1299:1320  "totalSupply += amount"
    var v_2 := read_from_storage_split_offset_0_t_uint256(0x00, s);
    assert v_2 == s.SLoad(0x00);
    var expr_10, s1 := checked_add_t_uint256(v_2, expr_9, s);
    if s1.ERROR? {
        return s1;
    }
    s' := update_storage_value_offset_0t_uint256_to_t_uint256(0x00, expr_10, s1);
  }

}

