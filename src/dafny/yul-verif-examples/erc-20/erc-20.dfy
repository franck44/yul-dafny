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
// include "../../../../libs/evm-dafny/src/dafny/util/bytes.dfy"


/**
  * A simple example with a sequence and an if statement.
  */
module ERC20 {

  import opened Int
  import opened YulSem = YulStrict
  import opened YulState
  import ByteUtils

  datatype Either<A, B> = Left(val: A) | Right(error: B)

  predicate GInv(s: Executing)
  {
    true
    // totalSupply ==
    //  some of balances should be total supply
  }


  method Main(s: Executing, ghost totalSupply: u256) returns (s': State)
    requires totalSupply == s.Load(0)
    requires s.MemSize() % 32 == 0
    requires 4 <= CallDataSize(s) as nat < TWO_255 - 4
    ensures CallDataSize(s) < 4 ==> s'.ERROR?
    ensures CallDataSize(s) >= 4 && shift_right_224_unsigned(CallDataLoad(0, s)) == 0x18160ddd ==> ByteUtils.ReadUint256(s'.data, 0) == s.Load(0)
    ensures s'.RETURNS? ==> ByteUtils.ReadUint256(s'.data, 0) == totalSupply
  {

    // var s1 := MStore(64, MemoryGuard(128), s);
    // assert s1.Read(64) == 128;
    // assert CallDataSize(s1) == CallDataSize(s);
    var s1 := s;

    if !Lt(CallDataSize(s1), 4) {
      //  There is enough calldata for a 4-byte selector
      assert CallDataSize(s1) >= 4;
      //  Extract selector
      var selector := shift_right_224_unsigned(CallDataLoad(0, s1));
      match selector

      case 0x18160ddd =>
        {
          // totalSupply()

          var s2 := external_fun_totalSupply_3(s1);
          assert s2.RETURNS? ==> |s2.data| == 32; 
          assert s2.RETURNS? ==> ByteUtils.ReadUint256(s2.data, 0) == s.Load(0);
          return s2;
        }

      case 0xa0712d68 =>
        {
          // mint(uint256)

          // external_fun_mint_13()
          return s1;
        }

      case _ => return Revert(0, 0, s1);

    }
    assert CallDataSize(s1) < 4;
    return Revert(0, 0, s1);
  }

  /** Get leftmost 4-bytes of a u256. */
  function shift_right_224_unsigned(value: u256): (newValue: u256)
  {
    Shr(224, value)
  }

  /** Get the free memory pointer. */
  method allocate_unbounded(s: Executing) returns (memPtr: u256, s': State)
    requires s.MemSize() % 32 == 0
    ensures s'.EXECUTING?
    ensures s'.MemSize() % 32 == 0
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

  function shift_right_unsigned_dynamic(bits: u256, value: u256): (newValue: u256)
    ensures bits == 0 ==> newValue == value
  {
    assume bits == 0 ==> Shr(bits, value) == value;
    Shr(bits, value)
  }

  function cleanup_from_storage_t_uint256(value: u256): (cleaned: u256) 
  {
    value
  }

  function extract_from_storage_value_dynamict_uint256(slot_value: u256, offset: u256) : (value: u256)
    requires offset as nat * 8 < TWO_256
    // ensures value == 
  {
    var k := shift_right_unsigned_dynamic(Mul(offset, 8), slot_value);
    cleanup_from_storage_t_uint256(k)
  }

  function read_from_storage_split_dynamic_t_uint256(slot: u256, offset: u256, s: Executing): (value: u256)
    requires offset as nat * 8 < TWO_256
    ensures offset == 0 ==> value == s.Load(slot)
  {
    extract_from_storage_value_dynamict_uint256(SLoad(slot, s), offset)
  }


  method getter_fun_totalSupply_3(s: Executing) returns (ret: u256)
    ensures ret == s.Load(0)
  {
    var slot := 0;
    var offset := 0;
    ret := read_from_storage_split_dynamic_t_uint256(slot, offset, s);
  }


  method cleanup_t_uint256(value: u256) returns (cleaned: u256)
    ensures cleaned == value
  {
    cleaned := value;
  }

  /**
    *  Store value at address pos in Memory.
    */
  method abi_encode_t_uint256_to_t_uint256_fromStack(value: u256, pos: u256, s: Executing) returns (s': State)
    requires s.MemSize() % 32 == 0
    ensures s'.EXECUTING?
    ensures s'.MemSize() % 32 == 0
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
    requires s.MemSize() % 32 == 0
    requires headStart as nat + 32 < TWO_256
    ensures s'.EXECUTING?
    ensures s'.MemSize() % 32 == 0
    ensures tail == headStart + 32
    ensures headStart as nat + 31 < s'.MemSize()
    ensures Memory.ReadUint256(s'.yul.memory, headStart as nat) == value0
  {
    tail := Add(headStart, 32);
    s' := abi_encode_t_uint256_to_t_uint256_fromStack(value0,  Add(headStart, 0), s);
  }

// lemma foo(s: )

  method external_fun_totalSupply_3(s: Executing) returns (s': State)
    requires 4 <= CallDataSize(s) as nat < TWO_255 - 4
    requires s.MemSize() % 32 == 0
    ensures s'.ERROR? || s'.RETURNS?
    ensures s'.RETURNS? ==> |s'.data| == 32
    ensures s'.RETURNS? ==> ByteUtils.ReadUint256(s'.data, 0) == s.Load(0)
    // ensures
  {
    if CallValue(s) > 0 {
      //  Not payable
      var s1 := revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb(s);
      return s1;
    } else {
      //  CallValue(s) == 0
      assert CallValue(s) == 0;
      var s1 := abi_decode_tuple_(4, CallDataSize(s), s);
      var ret_0 :=  getter_fun_totalSupply_3(s1);
      assert ret_0 == s1.Load(0) == s.Load(0);
      var memPos, s2 := allocate_unbounded(s1);
      assume memPos as nat + 32 < TWO_256;
      //  Store ret_0 in memory at location memPos'
      var memEnd, s3 := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0, s2);
      assert Memory.ReadUint256(s3.yul.memory, memPos as nat) == ret_0;
      var x := RETURNS(data := Memory.Slice(s3.yul.memory, memPos as nat, (memEnd - memPos) as nat));

      assert ByteUtils.ReadUint256(x.data, 0) == Memory.ReadUint256(s3.yul.memory, memPos as nat) == s.Load(0);
      //  Return with data = memory slice between memPos of length memEnd - memPos
    //   return RETURNS(data := Memory.Slice(s2.yul.memory, memPos as nat, (memEnd - memPos) as nat));
      return x;
    }

  }

  /* ---------- calldata decoding functions ----------- */

  /**
    *    Extract the selector, the first four bytes of the calldataload.
    */
  function selector(s: Executing): (r: u256)
    // ensures CallDataSize(s) >= 4 ==>
    //  to prove: if calldatasize >= 4 then the result if the first 4 bytes
    //  of calldataload
  {
    YulSem.Div(
      CallDataLoad(0, s),
      0x100000000000000000000000000000000000000000000000000000000)
  }

  /** test that offset if less than 160 bits */
  function decodeAsAddress(offset: u256, s: Executing): Either<u256, State>
    // requires offset < TWO_160
    requires 4 + (offset as nat + 1) * 0x20 as nat < TWO_256
  {
    var r := decodeAsUint(offset, s);
    match r
    case Left(v) =>
      if v as nat < TWO_160 then Left(v)
      else Right(Revert(0, 0, s))
    case x => x
  }

  /**
    *  Decode the nth word after selector in the calldata parameters.
    *  @param  offset  The index of the word.\*
    *  @note            Interestingly, the Yul specification from 
    *                   @link{https://docs.soliditylang.org/en/latest/yul.html#complete-erc20-example}
    *                   does not account for overflows in multiplication 
    *                   and adddition.
    */
  function decodeAsUint(offset: u256, s: Executing): Either<u256, State>
    requires 4 + (offset as nat + 1) * 0x20 as nat < TWO_256
  {
    if CallDataSize(s) < Add(4, Mul(offset + 1, 0x20)) then
      Right(Revert(0, 0, s))
    else Left(CallDataLoad(Add(4, Mul(offset, 0x20)), s))
  }

  // /* ---------- calldata encoding functions ---------- */
  // function returnUint(v) {
  //     mstore(0, v)
  //     return(0, 0x20)
  // }
  // function returnTrue() {
  //     returnUint(1)
  // }

  /* -------- storage layout ---------- */
  //   function ownerPos(): u256 { 0 }

  //   function totalSupplyPos(): u256  { 1 }

  /**
    *   Storage slot for an account.
    */
  //   function AccountToStorageOffset(account: u256): u256
  //     requires account as nat < TWO_256 - 0x1000
  //   {
  //     Add(0x1000, account)
  //   }

  /**   
    *  Storage slot of allowance for an account.
    */
  //   function AllowanceStorageOffset(account: u256, spender: u256, s: Executing): (r:   (u256, State))
  //     requires account as nat < TWO_256 - 0x1000
  //     requires s.MemSize() % 32 == 0
  //     ensures r.1.EXECUTING?
  //     ensures r.1.MemSize() % 32 == 0
  //   {
  //     var offset := AccountToStorageOffset(account);
  //     var s1 := MStore(0, offset, s);
  //     var s2 := MStore(0x20, spender, s);
  //     Keccak256(0, 0x40, s2)
  //   }

  /* -------- storage access ---------- */
  // function owner() -> o {
  //     o := sload(ownerPos())
  // }
  // function totalSupply() -> supply {
  //     supply := sload(totalSupplyPos())
  // }
  // function mintTokens(amount) {
  //     sstore(totalSupplyPos(), safeAdd(totalSupply(), amount))
  // }
  //   function balanceOf(account: u256, s: Executing): u256
  //     requires account as nat < TWO_256 - 0x1000
  //   {
  //     SLoad(AccountToStorageOffset(account), s)
  //   }
  // function addToBalance(account, amount) {
  //     let offset := accountToStorageOffset(account)
  //     sstore(offset, safeAdd(sload(offset), amount))
  // }
  // function deductFromBalance(account, amount) {
  //     let offset := accountToStorageOffset(account)
  //     let bal := sload(offset)
  //     require(lte(amount, bal))
  //     sstore(offset, sub(bal, amount))
  // }
  // function allowance(account, spender) -> amount {
  //     amount := sload(allowanceStorageOffset(account, spender))
  // }
  // function setAllowance(account, spender, amount) {
  //     sstore(allowanceStorageOffset(account, spender), amount)
  // }
  // function decreaseAllowanceBy(account, spender, amount) {
  //     let offset := allowanceStorageOffset(account, spender)
  //     let currentAllowance := sload(offset)
  //     require(lte(amount, currentAllowance))
  //     sstore(offset, sub(currentAllowance, amount))
  // }

}

