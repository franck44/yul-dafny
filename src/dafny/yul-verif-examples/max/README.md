
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
    // Store z at memory location 0x40
    mstore(0x40, z)
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

The Dafny `Executing` captures states that are not _error_ states (e.g. revert states). 
This Dafny function can only be used with a non-error state as an input.
However it returns a `State` which can be either `Executing` or `Error`.

An executing state contains the current `memory` state (an 32-byte addressable array of bytes), `storage` state (a 32-byte addressable array of 32-bytes), and some context information for the current execution (e.g. the `calldataload`). 

The semantics has the following effects:

1. extend the memory to ensure the size is larger than the requested address to store from;
2. update the memory of state `s` by writing the 32-byte (u256) `value` at address `address` in memory.

As can be readily seen, the semantics of this function guarantees several post-conditions:

1. the returned state is always `Executing`;
2. the memory size of the returned state goes beyond the 32 bytes after `address`;
3. the other components of the state (world, context, are not modified.

The Dafny verification engine checks that the post-conditions hold **for all inputs**.
Of course to do it uses the definitions of some functions `Memory.ExpandMem` and `Memory.WriteUint256` that are provided the Dafny-EVM library (a separate repository).

The final Dafny code is:

```dafny
/**
 *  Translation of the of the Yul code of max in Dafny.
 */
  method Max(x: u256, y: u256, s: Executing) returns (result: u256, s': State) 
    ensures result == x || result == y
    ensures result >= x && result >= y
    ensures s' == s     
  {
    s' := s;
    result := x;
    if Lt(x, y) { 
      result := y;
    }
  }

/**
 *  Translation of Yul code of main in Dafny.
 */
method Main(s: Executing) returns (s': State)  
    requires s.MemSize() == 0
    ensures s'.EXECUTING?
    ensures s'.MemSize() > 0x40 + 31
{
    var x := 8;                     //  let
    var y := 3;                     //  let
    var z, s1 := Max(x, y, s);      //  funcall. Returns result ans new memory (in s1).
    s' := MStore(0x40, z, s1);      //  memory store
}
```

Thanks to this encoding we can reason about the code and prove some properties of `Main` (the top-level function of the Yul code):

1. the resulting Yul state is always `Executing`, no error/exception occurs;
2. the memory size of the resulting state `s` is larger than 31 bytes after the memory slot we store the computed value.

And this is true **for all input state `s`** with an initial empty memory (memory size is zero).

The code for `Max` also provides a proof that it computes the maximum of `x` and `y`: the result is larger than both `x` and `y` and it is either `x` or `y`. 

