
include "../../../libs/evm-dafny/src/dafny/util/int.dfy"
include "../../../libs/evm-dafny/src/dafny/core/memory.dfy"
include "../../../libs/evm-dafny/src/dafny/bytecode.dfy"

module MathProofs {

    import opened Int

    // lemma NotLem(x: u256, y: bv256)
    //     requires x as bv256 == y 
    //     requires x == 0 
    //     ensures !y == (TWO_256 - 1 - x as nat) as bv256 
    // {

    // }

}

