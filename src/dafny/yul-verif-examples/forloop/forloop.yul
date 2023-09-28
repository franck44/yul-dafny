
object "Runtime" {
        code {
            for { let x := 0 } lt(x, 10) { x := add(x, 1) } {
                mstore(x, mul(x, 0x1))
            }
        }
    }

    
