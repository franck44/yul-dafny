[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![made-for-VSCode](https://img.shields.io/badge/Made%20for-VSCode-1f425f.svg)](https://code.visualstudio.com/)

# Overview

This repository contributes a shallow embedding of [Yul](https://docs.soliditylang.org/en/latest/yul.html) in [Dafny](https://github.com/dafny-lang/dafny).
It defines the semantics of the source language, Yul, using a host language, Dafny, by translating Yul structures into Dafny structures.

## What is Yul?

Yul can be seen as structured EVM bytecode: it has control flow structures (`if`, `for`, `block`, etc) and functions.
It does not provide a _stack_ as in the EVM, but rather _variables_ and _scopes_.
As a result, it easier to read than EVM bytecode.

The following example defines a function `max` and uses it to store (in memory) the largest of two values. 

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
        //  Main code
        let x := 8
        let y := 3
        let z := max(x, y)
        mstore(0x40, z)
    }
}
```

The builtin functions `lt`, `mstore` are part of the _EVM dialect_ of Yul.
This dialect has a single variable/literal type which is `u256` (unsigned integers over 256 bits), so the type of all variables (`x`, `y`, `result`) is `u256`.
Yul has been designed to be easy to translate into EVM bytecode (with a stack instead of variables, and jumps instead to implement control structures).
It is also a good target for formal verification.

## Semantics of Yul

An informal semantics is defined in the [Yul documentation](https://docs.soliditylang.org/en/latest/yul.html#formal-specification).
There are several _formal semantics_ of Yul (see resources below), all them being _deep embeddings_ in the sense that the formalisation provides:
- the syntax of Yul, and
- an operational or denotational semantics of the language.

In this project we propose a _shallow embedding_ a Yul into the (host) verification-friendly language Dafny.
A shallow embedding re-uses the host language features (control structures, variables declaration, scopes) to equip the source language (Yul) with a formal 
semantics that is inherited from the host (Dafny).

For instance, the `max` function above can be translated into Dafny as:

```dafny
method Max(x: u256, y: u256, m: Memory.T) returns (result: u256, m': Memory.T)
    ensures result == x || result == y
    ensures result >= x && result >= y
    ensures m' == m
{
    m' := m;            //  memory is not modified
    result := x;        
    if lt(x, y) > 0 {
        result := y;
    }
}
```
The semantics of assignment, function declarations, `if` and variables' scopes is inherited from the Dafny semantics.
The advantage of a shallow embedding is that it is usually easier to implement, and in our case, we can directly use the extra verification features of Dafny to provide some guarantees about the code (e.g. `ensures`).  

## From Solidity to Yul

Yul is an intermediate representation (IR) that can be compiled to EVM bytecode.
The solidity compiler can generate Yul as an intermediate representation of Solidity code:

```zsh
> solc --ir file.sol >file.yul
```

The Yul code in 'file.yul' can be compiled into EVM bytecode:
```zsh
> solc --yul file.yul >file.txt
```

## Formal verification of Yul and EVM bytecode

With a shallow embedding of Yul, we get the ability to prove some properties of Yul programs.
We can leverage this feature to prove properties of EVM bytecode generated from Yul.


An example is provided in [this folder](src/dafny/yul-bytecode-verif/max).
The verification works as follow:

- some properties are verified on the Yul code
- we then compile the Yul code into EVM bytecode
- we prove that the bytecode for each function (e.g. `max`) _simulates_ the Yul code.

# Examples

The [examples folder](src/dafny/yul-verif-examples) contains examples of Yul to Dafny translation and verification.
# Resources

- [What is Yul?](https://www.quicknode.com/guides/ethereum-development/smart-contracts/what-is-yul)
- [Yul specification in Lean](https://github.com/NethermindEth/Yul-Specification)
- [Yul specification in K](https://github.com/ethereum/Yul-K/tree/master)
- [Yul specification in Isabelle](https://github.com/mmalvarez/Yul-Isabelle)
- [An EVM in Dafny (Dafny-EVM)](Consensys/evm-dafny.git)