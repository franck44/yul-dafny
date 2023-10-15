Optimized IR:
/// @use-src 0:"src/dafny/yul-verif-examples/erc-20/erc-20.sol"
object "ERC20_14" {
    code {
        {
            /// @src 0:54:1580  "contract ERC20 {..."
            mstore(64, memoryguard(0x80))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := allocate_unbounded()
            codecopy(_1, dataoffset("ERC20_14_deployed"), datasize("ERC20_14_deployed"))
            return(_1, datasize("ERC20_14_deployed"))
        }
        function allocate_unbounded() -> memPtr
        { memPtr := mload(64) }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"src/dafny/yul-verif-examples/erc-20/erc-20.sol"
    object "ERC20_14_deployed" {
        code {
            {
                /// @src 0:54:1580  "contract ERC20 {..."
                mstore(64, memoryguard(0x80))
                if iszero(lt(calldatasize(), 4))
                {
                    let selector := shift_right_unsigned(calldataload(0))
                    switch selector
                    case 0x18160ddd { external_fun_totalSupply() }
                    case 0xa0712d68 { external_fun_mint() }
                    default { }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function shift_right_unsigned(value) -> newValue
            { newValue := shr(224, value) }
            function allocate_unbounded() -> memPtr
            { memPtr := mload(64) }
            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function shift_right_unsigned_dynamic(bits, value) -> newValue
            { newValue := shr(bits, value) }
            function cleanup_from_storage_uint256(value) -> cleaned
            { cleaned := value }
            function extract_from_storage_value_dynamict_uint256(slot_value, offset) -> value
            {
                value := cleanup_from_storage_uint256(shift_right_unsigned_dynamic(mul(offset, 8), slot_value))
            }
            function read_from_storage_split_dynamic_uint256(slot, offset) -> value
            {
                value := extract_from_storage_value_dynamict_uint256(sload(slot), offset)
            }
            /// @ast-id 3 @src 0:75:98  "uint public totalSupply"
            function getter_fun_totalSupply() -> ret
            {
                let slot := 0
                let offset := 0
                ret := read_from_storage_split_dynamic_uint256(slot, offset)
            }
            /// @src 0:54:1580  "contract ERC20 {..."
            function cleanup_uint256(value) -> cleaned
            { cleaned := value }
            function abi_encode_uint256_to_uint256(value, pos)
            {
                mstore(pos, cleanup_uint256(value))
            }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, add(headStart, 0))
            }
            function external_fun_totalSupply()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := getter_fun_totalSupply()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_uint256(memPos, ret)
                return(memPos, sub(memEnd, memPos))
            }
            function validator_revert_uint256(value)
            {
                if iszero(eq(value, cleanup_uint256(value))) { revert(0, 0) }
            }
            function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                let offset := 0
                value0 := abi_decode_uint256(add(headStart, offset), dataEnd)
            }
            function abi_encode_tuple(headStart) -> tail
            { tail := add(headStart, 0) }
            function external_fun_mint()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let param := abi_decode_tuple_uint256(4, calldatasize())
                fun_mint(param)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple(memPos)
                return(memPos, sub(memEnd, memPos))
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            function shift_right_0_unsigned(value) -> newValue
            { newValue := shr(0, value) }
            function extract_from_storage_value_offsett_uint256(slot_value) -> value
            {
                value := cleanup_from_storage_uint256(shift_right_0_unsigned(slot_value))
            }
            function read_from_storage_split_offset_uint256(slot) -> value
            {
                value := extract_from_storage_value_offsett_uint256(sload(slot))
            }
            function panic_error_0x11()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x11)
                revert(0, 0x24)
            }
            function checked_add_uint256(x, y) -> sum
            {
                x := cleanup_uint256(x)
                y := cleanup_uint256(y)
                sum := add(x, y)
                if gt(x, sum) { panic_error_0x11() }
            }
            function shift_left(value) -> newValue
            { newValue := shl(0, value) }
            function update_byte_slice_shift(value, toInsert) -> result
            {
                let mask := not(0)
                toInsert := shift_left(toInsert)
                value := and(value, not(mask))
                result := or(value, and(toInsert, mask))
            }
            function identity(value) -> ret
            { ret := value }
            function convert_uint256_to_uint256(value) -> converted
            {
                converted := cleanup_uint256(identity(cleanup_uint256(value)))
            }
            function prepare_store_uint256(value) -> ret
            { ret := value }
            function update_storage_value_offsett_uint256_to_uint256(slot, value)
            {
                let convertedValue := convert_uint256_to_uint256(value)
                sstore(slot, update_byte_slice_shift(sload(slot), prepare_store_uint256(convertedValue)))
            }
            /// @ast-id 13 @src 0:1211:1387  "function mint(uint amount) external {..."
            function fun_mint(var_amount)
            {
                /// @src 0:1316:1322  "amount"
                let _1 := var_amount
                let expr := _1
                /// @src 0:1301:1322  "totalSupply += amount"
                let _2 := read_from_storage_split_offset_uint256(0x00)
                let expr_1 := checked_add_uint256(_2, expr)
                update_storage_value_offsett_uint256_to_uint256(0x00, expr_1)
            }
        }
        data ".metadata" hex"a264697066735822122015789cef51a4aba55cf90c71238232e663c54e72c0da29076a12e9bdda4cdc0964736f6c63430008150033"
    }
}

