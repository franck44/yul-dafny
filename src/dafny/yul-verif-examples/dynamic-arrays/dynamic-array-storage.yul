IR:

/// @use-src 0:"src/dafny/yul-verif-examples/dynamic-arrays/dynamic-array-storage.sol"
object "DynArray_19" {
    code {
        /// @src 0:54:185  "contract DynArray {..."
        mstore(64, memoryguard(128))
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        constructor_DynArray_19()

        let _1 := allocate_unbounded()
        codecopy(_1, dataoffset("DynArray_19_deployed"), datasize("DynArray_19_deployed"))

        return(_1, datasize("DynArray_19_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        /// @src 0:54:185  "contract DynArray {..."
        function constructor_DynArray_19() {

            /// @src 0:54:185  "contract DynArray {..."

        }
        /// @src 0:54:185  "contract DynArray {..."

    }
    /// @use-src 0:"src/dafny/yul-verif-examples/dynamic-arrays/dynamic-array-storage.sol"
    object "DynArray_19_deployed" {
        code {
            /// @src 0:54:185  "contract DynArray {..."
            mstore(64, memoryguard(128))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x1ab06ee5
                {
                    // set(uint256,uint256)

                    external_fun_set_18()
                }

                case 0xcc3e57d9
                {
                    // myArray(uint256)

                    external_fun_myArray_4()
                }

                default {}
            }

            revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()

            function shift_right_224_unsigned(value) -> newValue {
                newValue :=

                shr(224, value)

            }

            function allocate_unbounded() -> memPtr {
                memPtr := mload(64)
            }

            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
                revert(0, 0)
            }

            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() {
                revert(0, 0)
            }

            function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() {
                revert(0, 0)
            }

            function cleanup_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function validator_revert_t_uint256(value) {
                if iszero(eq(value, cleanup_t_uint256(value))) { revert(0, 0) }
            }

            function abi_decode_t_uint256(offset, end) -> value {
                value := calldataload(offset)
                validator_revert_t_uint256(value)
            }

            function abi_decode_tuple_t_uint256t_uint256(headStart, dataEnd) -> value0, value1 {
                if slt(sub(dataEnd, headStart), 64) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

                {

                    let offset := 32

                    value1 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

            }

            function abi_encode_tuple__to__fromStack(headStart ) -> tail {
                tail := add(headStart, 0)

            }

            function external_fun_set_18() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1 :=  abi_decode_tuple_t_uint256t_uint256(4, calldatasize())
                fun_set_18(param_0, param_1)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple__to__fromStack(memPos  )
                return(memPos, sub(memEnd, memPos))

            }

            function abi_decode_tuple_t_uint256(headStart, dataEnd) -> value0 {
                if slt(sub(dataEnd, headStart), 32) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

            }

            function panic_error_0x32() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x32)
                revert(0, 0x24)
            }

            function array_length_t_array$_t_uint256_$dyn_storage(value) -> length {

                length := sload(value)

            }

            function array_dataslot_t_array$_t_uint256_$dyn_storage(ptr) -> data {
                data := ptr

                mstore(0, ptr)
                data := keccak256(0, 0x20)

            }

            function array_dataslot_t_bytes_storage_ptr(ptr) -> data {
                data := ptr

                mstore(0, ptr)
                data := keccak256(0, 0x20)

            }

            function long_byte_array_index_access_no_checks(array, index) -> slot, offset {

                offset := sub(31, mod(index, 0x20))
                let dataArea := array_dataslot_t_bytes_storage_ptr(array)
                slot := add(dataArea, div(index, 0x20))

            }

            function storage_array_index_access_t_array$_t_uint256_$dyn_storage(array, index) -> slot, offset {
                let arrayLength := array_length_t_array$_t_uint256_$dyn_storage(array)
                if iszero(lt(index, arrayLength)) { panic_error_0x32() }

                let dataArea := array_dataslot_t_array$_t_uint256_$dyn_storage(array)
                slot := add(dataArea, mul(index, 1))
                offset := 0

            }

            function shift_right_unsigned_dynamic(bits, value) -> newValue {
                newValue :=

                shr(bits, value)

            }

            function cleanup_from_storage_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function extract_from_storage_value_dynamict_uint256(slot_value, offset) -> value {
                value := cleanup_from_storage_t_uint256(shift_right_unsigned_dynamic(mul(offset, 8), slot_value))
            }

            function read_from_storage_split_dynamic_t_uint256(slot, offset) -> value {
                value := extract_from_storage_value_dynamict_uint256(sload(slot), offset)

            }

            /// @ast-id 4
            /// @src 0:78:99  "uint[] public myArray"
            function getter_fun_myArray_4(key_0) -> ret {

                let slot := 0
                let offset := 0

                if iszero(lt(key_0, array_length_t_array$_t_uint256_$dyn_storage(slot))) { revert(0, 0) }

                slot, offset := storage_array_index_access_t_array$_t_uint256_$dyn_storage(slot, key_0)

                ret := read_from_storage_split_dynamic_t_uint256(slot, offset)

            }
            /// @src 0:54:185  "contract DynArray {..."

            function abi_encode_t_uint256_to_t_uint256_fromStack(value, pos) {
                mstore(pos, cleanup_t_uint256(value))
            }

            function abi_encode_tuple_t_uint256__to_t_uint256__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_myArray_4() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0 :=  abi_decode_tuple_t_uint256(4, calldatasize())
                let ret_0 :=  getter_fun_myArray_4(param_0)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
                revert(0, 0)
            }

            function shift_left_dynamic(bits, value) -> newValue {
                newValue :=

                shl(bits, value)

            }

            function update_byte_slice_dynamic32(value, shiftBytes, toInsert) -> result {
                let shiftBits := mul(shiftBytes, 8)
                let mask := shift_left_dynamic(shiftBits, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
                toInsert := shift_left_dynamic(shiftBits, toInsert)
                value := and(value, not(mask))
                result := or(value, and(toInsert, mask))
            }

            function identity(value) -> ret {
                ret := value
            }

            function convert_t_uint256_to_t_uint256(value) -> converted {
                converted := cleanup_t_uint256(identity(cleanup_t_uint256(value)))
            }

            function prepare_store_t_uint256(value) -> ret {
                ret := value
            }

            function update_storage_value_t_uint256_to_t_uint256(slot, offset, value_0) {
                let convertedValue_0 := convert_t_uint256_to_t_uint256(value_0)
                sstore(slot, update_byte_slice_dynamic32(sload(slot), offset, prepare_store_t_uint256(convertedValue_0)))
            }

            /// @ast-id 18
            /// @src 0:106:183  "function set(uint v, uint index) external {..."
            function fun_set_18(var_v_6, var_index_8) {

                /// @src 0:175:176  "v"
                let _1 := var_v_6
                let expr_14 := _1
                /// @src 0:158:165  "myArray"
                let _2_slot := 0x00
                let expr_11_slot := _2_slot
                /// @src 0:166:171  "index"
                let _3 := var_index_8
                let expr_12 := _3
                /// @src 0:158:172  "myArray[index]"

                let _4, _5 := storage_array_index_access_t_array$_t_uint256_$dyn_storage(expr_11_slot, expr_12)
                /// @src 0:158:176  "myArray[index] = v"
                update_storage_value_t_uint256_to_t_uint256(_4, _5, expr_14)
                let expr_15 := expr_14

            }
            /// @src 0:54:185  "contract DynArray {..."

        }

        data ".metadata" hex"a2646970667358221220e0276b336087434029b9c065a8843424011acd12245b40fb691c94f67277fd2b64736f6c63430008150033"
    }

}


