
In this folder, we explain how we encode a simple Yul function,
a sequence of variables declarations and some memory operation.

The Yul code to translate to Dafny is:

```solidity
object "Runtime" {
  code {
    function max(x, y) -> result 
    {
        result := x
        if lt(x, y) {
            result := y 
        } 
    }
    let x := 8
    let y := 3
    let z := max(x, y)
    //  Store z at memory location 0x40
    mstore(0x40, z)
    //  Return the previously stored value
    return(0x40, 32)
  }
}
```

We have to translate (and provide a semantics for) the `let` instructions.
This is a variable declaration, with scope, so we can use Dafny `var` declaration syntax: `let x := 8` is translated into `var x: u256 := 8;`
Note that we have to provide the type in Dafny, and this will be used to detect overflows, or correct conversion from one representation to another.

The [Yul library](../../Yul/CommonSem.dfy) in Dafny provides the instruction `Lt(x: u256, y: u256)`, and we use it to give the meaning to `lt(x, y)` in the Yul code.

The `mstore` instruction updates the memory in the current contract's context.
As a result we need to give a semantics to this effect.
There are several ways that this can be done in Dafny, and we have chosen to _explicitly_ include a _Yul state_ in this kind of side-effect functions.

The semantics of a Yul `mstore(address, value)` is given by the following Dafny function in the library:

```dafny
function MStore(address: u256, value: u256, s: Executing): (s': State)
    ensures s'.EXECUTING?
    ensures s'.MemSize() > address as nat + 31
    ensures s'.yul.context == s.yul.context
    ensures s'.yul.world == s.yul.world
  {
    //  Make sure memory is large enough.
    var m' := Memory.ExpandMem(s.yul.memory, address as nat, 32);
    EXECUTING(s.yul.(memory := Memory.WriteUint256(m', address as nat, value)))
  }
```

The Dafny datatype `Executing` captures states that are not _error_ states (e.g. revert states). 
This Dafny function can only be used with a non-error state as an input.
However it returns a `State` which can be either `Executing` or `Error`.

An executing state comprises of:

-  the current `memory` state, an 32-byte addressable array of bytes), 
- the `storage` state, a 32-byte addressable array of 32-bytes, and 
- some contextual information for the current execution (e.g. the `calldataload`). 

The semantics of `MStore` has the following effects:

1. extend the memory to ensure the size is larger than the requested address to store from;
2. update the memory of state `s` by writing the 32-byte (u256) `value` at address `address` in memory.

As can be readily seen, the semantics of this function guarantees several post-conditions (`ensures`):

1. the returned state is always `Executing`;
2. the memory size of the returned state goes beyond the 32 bytes after `address`;
3. the other components of the state (world, context, etc) are not modified.

The Dafny verification engine checks that the post-conditions hold **for all inputs**.
Of course to do it uses the definitions and (proved) properties of some functions `Memory.ExpandMem` and `Memory.WriteUint256` that are provided the Dafny-EVM library (a separate repository).

The full Dafny code is:

```dafny

/**
 *   A ghost (verification-only) function tha provides a definition of `maximum`.
 */
ghost function maxu256(x: u256, y: u256): (r: u256)
    ensures r == x || r == y
    ensures r >= x && r >= y
{
    if x <= y then y else x
}

/**
 *  Translation of the Yul code of max in Dafny.
 */
method Max(x: u256, y: u256) returns (result: u256) 
    ensures result == maxu256(x, y)
{
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
    var z := Max(x, y);             //  funcall
    var s1:= MStore(0x40, z, s);    //  memory store
    return Return(0x40, 32, s1);    //  return result
}
```

Thanks to this encoding we can reason about the code and prove some properties of `Main` (the top-level function of the Yul code):

1. the resulting Yul state is always `Return`, no error/exception occurs;
2. the result returned in the returned state's data field is 8.

And this is true **for all input state `s`**.

The code for `Max` also provides a proof that it computes the maximum of `x` and `y`: the result is larger than both `x` and `y` and it is either `x` or `y`. 

An easy generalisation is that the same code works with arbitrary inputs for `x` and `y`

```dafny
/**
 *  Generalisation of Yul code of main in Dafny.
 *  @param      x 
 *  @param      y 
 *  @returns    The max of `x` and `y` as defined by `maxu256`.
 */
method Main2(s: Executing, x: u256, y: u256) returns (s': State)
    ensures s'.RETURNS?
    ensures ByteUtils.ReadUint256(s'.data, 0) == maxu256(x, y)
{
    var z := Max(x, y);                //  funcall
    var s2 := MStore(0x40, z, s);      //  memory store
    return Return(0x40, 32, s2);       //  return result
}
```
And this is true **for all inputs `s`, `x`, `y`**.

