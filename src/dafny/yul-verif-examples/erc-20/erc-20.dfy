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
  import opened YulSem = YulStrict
  import opened YulState

  datatype Either<A, B> = Left(val: A) | Right(error: B)

  predicate GInv(s: Executing)
  {
    true
    //  some of balances should be total supply
  }

  method Main(s: Executing) returns (s': State)
    requires s.MemSize() % 32 == 0

    ensures CallValue(s) != 0 ==> s'.ERROR?
    // ensures Memory.Size(m') > 0x40 + 31
    // ensures Memory.ReadUint256(m', 0x40) == 8
  {
    //  Non payable, callvalue must be zero, otherwise we revert.
    if !IsZero((CallValue(s))) {
      return Revert(0, 0, s);
    }

    s' := s;

    match selector(s)
    case 0x70a08231 /* "balanceOf(address)" */ => {
      // returnUint(balanceOf(decodeAsAddress(0)))
      s' := s;
    }

    // case 0x18160ddd /* "totalSupply()" */ {
    //     returnUint(totalSupply())
    // }
    // case 0xa9059cbb /* "transfer(address,uint256)" */ {
    //     transfer(decodeAsAddress(0), decodeAsUint(1))
    //     returnTrue()
    // }
    // case 0x23b872dd /* "transferFrom(address,address,uint256)" */ {
    //     transferFrom(decodeAsAddress(0), decodeAsAddress(1), decodeAsUint(2))
    //     returnTrue()
    // }
    // case 0x095ea7b3 /* "approve(address,uint256)" */ {
    //     approve(decodeAsAddress(0), decodeAsUint(1))
    //     returnTrue()
    // }
    // case 0xdd62ed3e /* "allowance(address,address)" */ {
    //     returnUint(allowance(decodeAsAddress(0), decodeAsAddress(1)))
    // }
    // case 0x40c10f19 /* "mint(address,uint256)" */ {
    //     mint(decodeAsAddress(0), decodeAsUint(1))
    //     returnTrue()
    // }
    case _ => return Revert(0, 0, s);


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
  function ownerPos(): u256 { 0 }

  function totalSupplyPos(): u256  { 1 }

  /**
    *   Storage slot for an account.
    */
  function AccountToStorageOffset(account: u256): u256
    requires account as nat < TWO_256 - 0x1000
  {
    Add(0x1000, account)
  }

  /**   
    *  Storage slot of allowance for an account.
    */
  function AllowanceStorageOffset(account: u256, spender: u256, s: Executing): (r:   (u256, State))
    requires account as nat < TWO_256 - 0x1000
    requires s.MemSize() % 32 == 0
    ensures r.1.EXECUTING?
    ensures r.1.MemSize() % 32 == 0
  {
    var offset := AccountToStorageOffset(account);
    var s1 := MStore(0, offset, s);
    var s2 := MStore(0x20, spender, s);
    Keccak256(0, 0x40, s2)
  }

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
  function balanceOf(account: u256, s: Executing): u256
    requires account as nat < TWO_256 - 0x1000
  {
    SLoad(AccountToStorageOffset(account), s)
  }
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

