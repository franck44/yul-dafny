
object "Runtime" {
    code {
        function checked_add_t_uint256(x, y) -> sum {
            sum := add(x, y)
            if gt(x, sum) { revert(0, 0) }
        }

        let x := 8
        let y := 56
        let z := checked_add_t_uint256(x, y)

    }
  }
  