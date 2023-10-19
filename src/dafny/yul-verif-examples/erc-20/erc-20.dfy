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
include "../../Yul/CommonFunctions.dfy"
/**
  * A simple example with a sequence and an if statement.
  */
module ERC20 {

  import opened Int
  import opened YulStrict
  import YulSem
  import opened YulState
  import ByteUtils
  import opened CommonFunctions 

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

    /** Accounts' keys are not modified. */
    ensures s'.RETURNS? ==> s.yul.world.accounts.Keys == s'.world.accounts.Keys

    /** Conditions under which calls do not revert. */
    ensures (CallDataSize(s) >= 4 && Selector(s) == TotalSupplySelector && CallValue(s) == 0) ==> s'.RETURNS?
    ensures CallDataSize(s) >= 36 && Selector(s) == MintSelector && CallValue(s) == 0 && (s.SLoad(0) as nat + CallDataLoad(4, s) as nat) < TWO_256 ==> s'.RETURNS?

    ensures CallDataSize(s) >= 36 && Selector(s) == MintSelector && CallValue(s) == 0 && (s.SLoad(0) as nat + CallDataLoad(4, s) as nat) < TWO_256 ==> s'.RETURNS?

    /**  Worldstate is not modified by totalSupply. */
    ensures s'.RETURNS? && Selector(s) == TotalSupplySelector ==> s'.world ==  s.yul.world
    // /** The value returned  in the data field is storage at slot 0 in `s`. */
    ensures s'.RETURNS? && Selector(s) == TotalSupplySelector ==> s'.RETURNS? ==> ByteUtils.ReadUint256(s'.data, 0) == s.SLoad(0)

    /** Storage is updated by mint if no overflow. */
    ensures s'.RETURNS? && Selector(s) == MintSelector ==> Storage.Read(s'.world.accounts[s.yul.context.address].storage, 0) as nat ==  s.SLoad(0) as nat + CallDataLoad(4, s) as nat < TWO_256
    //  Overflow result in a revert.
    ensures CallDataSize(s) >= 36 && Selector(s) == MintSelector && CallValue(s) == 0 && (s.SLoad(0) as nat + CallDataLoad(4, s) as nat) >= TWO_256 ==> s'.ERROR?
  {
    var s1 := MStore(64, MemoryGuard(128), s);

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

    }
    //  Here we should revert as the calldataload does not have enough bytes.
    assert CallDataSize(s1) < 4 || (Selector(s1) != TotalSupplySelector && Selector(s1) != MintSelector) ;
    return revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74(s1);
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

  method external_fun_totalSupply_3(s: Executing) returns (s': State)
    requires 4 <= CallDataSize(s) as nat < TWO_255 - 1
    requires s.MemSize() >= 96 && s.Read(64) as nat + 32 < TWO_256
    ensures CallValue(s) > 0 <==> s'.ERROR?
    ensures s'.ERROR? || s'.RETURNS?
    ensures s'.RETURNS? ==> |s'.data| == 32
    ensures s'.RETURNS? ==> ByteUtils.ReadUint256(s'.data, 0) == s.SLoad(0)
    ensures s'.RETURNS? ==> s'.world == s.World()
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
    return Return(memPos, memEnd - memPos, s3);
  }

  /**
    *  Increase totalSupply by a given amount if possible.
    */
  method external_fun_mint_13(s: Executing) returns (s': State)
    requires 4 <= CallDataSize(s) as nat < TWO_255 - 1
    ensures CallDataSize(s) < 36 || CallValue(s) > 0 ==> s'.ERROR?
    ensures CallDataSize(s) >= 36 && (s.SLoad(0) as nat + ByteUtils.ReadUint256(s.Context().callData, 4) as nat) >= TWO_256 ==> s'.ERROR?
    ensures CallDataSize(s) >= 36 && CallValue(s) == 0 && (s.SLoad(0) as nat + ByteUtils.ReadUint256(s.Context().callData, 4) as nat) < TWO_256 ==> s'.RETURNS?
    ensures s'.RETURNS? || s'.ERROR?
    ensures s'.RETURNS? ==> s'.world.accounts.Keys == s.Accounts().Keys
    ensures s'.RETURNS? ==> Storage.Read(s'.world.accounts[s.Context().address].storage, 0) ==  s.SLoad(0) + CallDataLoad(4, s)
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

  method fun_mint_13(var_amount_5: u256, s: Executing) returns (s': State)
    ensures s'.EXECUTING? <==> s.SLoad(0) as nat + var_amount_5 as nat < TWO_256
    ensures s'.EXECUTING? ==> s'.SLoad(0) == s.SLoad(0) + var_amount_5
    ensures s'.EXECUTING? ==> s'.Accounts().Keys == s.Accounts().Keys
    ensures s'.EXECUTING? ==> s'.Context() == s.Context()
    ensures s'.ERROR? || s'.EXECUTING?
  {
    /// @src 0:1314:1320  "amount"
    var v_1 := var_amount_5;
    var expr_9 := v_1;
    /// @src 0:1299:1320  "totalSupply += amount"
    var v_2 := read_from_storage_split_offset_0_t_uint256(0x00, s);
    var expr_10, s1 := checked_add_t_uint256(v_2, expr_9, s);
    if s1.ERROR? {
        return s1;
    }
    s' := update_storage_value_offset_0t_uint256_to_t_uint256(0x00, expr_10, s1);
  }

}

