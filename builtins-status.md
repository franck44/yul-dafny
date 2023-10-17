

The following table of builtins is available for the  [EVM dialect](https://docs.soliditylang.org/en/latest/yul.html#evm-dialect) of Yul.


| Supported       | Instruction           | Description |
|-----------------| ----------------------| ----------- |
| :red_circle: | `stop()`      |   stop execution, identical to return(0, 0)    |
| :white_check_mark: | `add(x, y)` | x + y |
| :white_check_mark: | `sub(x, y)` | x - y |
| :white_check_mark: | `mul(x, y)` | x * y |
| :white_check_mark: | `div(x, y)` | x / y or 0 if y == 0 |
| :white_check_mark: | `sdiv(x, y)` | x / y, for signed numbers in two’s complement, 0 if y == 0 |
| :white_check_mark: | `mod(x, y)` | x % y, 0 if y == 0 |
| :white_check_mark: | `smod(x, y)` | x % y, for signed numbers in two’s complement, 0 if y == 0 |
| :white_check_mark: | `exp(x, y)` | x to the power of y |
| :white_check_mark: | `not(x)` | bitwise “not” of x (every bit of x is negated) |
| :white_check_mark: | `lt(x, y)` | 1 if x &lt; y, 0 otherwise |
| :white_check_mark: | `gt(x, y)` | 1 if x &gt; y, 0 otherwise |
| :white_check_mark: | `slt(x, y)` | 1 if x &lt; y, 0 otherwise, for signed numbers in two’s complement |
| :white_check_mark: | `sgt(x, y)` | 1 if x &gt; y, 0 otherwise, for signed numbers in two’s complement |
| :white_check_mark: | `eq(x, y)` | 1 if x == y, 0 otherwise |
| :white_check_mark: | `iszero(x)` | 1 if x == 0, 0 otherwise |
| :white_check_mark: | `and(x, y)` | bitwise “and” of x and y |
| :white_check_mark: | `or(x, y)` | bitwise “or” of x and y |
| :white_check_mark: | `xor(x, y)` | bitwise “xor” of x and y |
| :red_circle: | `byte(n, x)` | nth byte of x, where the most significant byte is the 0th byte| 
| :red_circle: | `stop()` | stop execution, identical to return(0, 0) |
| :white_check_mark: | `shl(x, y)` | logical shift left y by x bits |
| :white_check_mark: | `shr(x, y)` | logical shift right y by x bits |
| :red_circle: | `sar(x, y)` | signed arithmetic shift right y by x bits |
| :red_circle: | `addmod(x, y, m)` | (x + y) % m with arbitrary precision arithmetic, 0 if m == 0 |
| :red_circle: | `mulmod(x, y, m)` | (x * y) % m with arbitrary precision arithmetic, 0 if m == 0 |
| :red_circle: | `signextend(i, x)` | sign extend from (i*8+7)th bit counting from least significant |
| :red_circle: | `keccak256(p, n)` | keccak(mem[p…(p+n))) |
| :red_circle: | `pc()` | current position in code |
| :red_circle: | `pop(x)` | discard value x |
| :white_check_mark: | `mload(p)` | mem[p…(p+32)) |
| :white_check_mark: | `mstore(p, v)` | mem[p…(p+32)) := v |
| :red_circle: | `mstore8(p, v)` | mem[p] := v &amp; 0xff (only modifies a single byte) |
| :white_check_mark: | `sload(p)` | storage[p] |
| :white_check_mark: | `sstore(p, v)` | storage[p] := v |
| :red_circle: | `msize()` | size of memory, i.e. largest accessed memory index |
| :red_circle: | `gas()` | gas still available to execution |
| :red_circle: | `address()` | address of the current contract / execution context |
| :red_circle: | `balance(a)` | wei balance at address a |
| :red_circle: | `selfbalance()` | equivalent to balance(address()), but cheaper |
| :red_circle: | `caller()` | call sender | :white_check_mark: |
| :white_check_mark: | `callvalue()` | wei sent together with the current call |
| :white_check_mark: | `calldataload(p)` | call data starting from position p (32 bytes) |
| :white_check_mark: | `calldatasize()` | size of call data in bytes |
| :red_circle: | `calldatacopy(t, f, s)` | copy s bytes from calldata at position f to mem at position t |
| :red_circle: | `codesize()` | size of the code of the current contract / execution context |
| :red_circle: | `codecopy(t, f, s)` | copy s bytes from code at position f to mem at position t |
| :red_circle: | `extcodesize(a)` | size of the code at address a |
| :red_circle: | `extcodecopy(a, t, f, s)` | like codecopy(t, f, s) but take code at address a |
| :red_circle: | `returndatasize | size of the last returndata |
| :red_circle: | `returndatacopy(t, f, s)` | copy s bytes from returndata at position f to mem at position t |
| :red_circle: | `extcodehash(a)` | code hash of address a |
| :red_circle: | `create(v, p, n)` | create new contract with code mem[p…(p+n)) and send v wei and return the new address;| returns 0 on error |
| :red_circle: | `create2(v, p, n, s)` | create new contract with code mem[p…(p+n)) at address `keccak256(0xff . this . s . | keccak256(mem[p…(p+n)))` and send v wei and return the new address |
| :red_circle: | `call(g, a, v, in, insize, out, outsize)` | call contract at address a with input mem[in…(in+insize)| providing g gas and v wei and output area mem[out…(out+outsize)) returning 0 on error (eg. out of gas) and 1 | on success |
| :red_circle: | `callcode(g, a, v, in, insize, out, outsize)` | identical to <code class="docutils literal | notranslate"><span class="pre">call</span></code> but only use the code from a and stay in the context of the | current contract otherwise |
| :red_circle: | `delegatecall(g, a, in, insize, out, outsize)` | Similar to `callcode` |
| :red_circle: | `staticcall(g, a, in, insize, out, outsize)` | Similar to `call` | 
| :white_check_mark: | `return(p, s)` | end execution, return data mem[p…(p+s)) |
| :white_check_mark: | `revert(p, s)` | end execution, revert state changes, return data mem[p…(p+s)) |
| :red_circle: | `selfdestruct(a)` | end execution, destroy current contract and send funds to a (deprecated) |
| :red_circle: | `invalid()` | end execution with invalid instruction |
| :red_circle: | `log0(p, s)` | log data mem[p…(p+s)) |
| :red_circle: | `log1(p, s, t1)` | log data mem[p…(p+s)) with topic t1 |
| :red_circle: | `log2(p, s, t1, t2)` | log data mem[p…(p+s)) with topics t1, t2 |
| :red_circle: | `log3(p, s, t1, t2, t3)` | log data mem[p…(p+s)) with topics t1, t2, t3 |
| :red_circle: | `log4(p, s, t1, t2, t3, t4)` | log data mem[p…(p+s)) with topics t1, t2, t3, t4 |
| :red_circle: | `chainid()` | ID of the executing chain (EIP-1344) |
| :red_circle: | `basefee()` | current block’s base fee (EIP-3198 and EIP-1559) |
| :red_circle: | `origin()` | transaction sender |
| :red_circle: | `gasprice()` | gas price of the transaction |
| :red_circle: | `blockhash(b)` | hash of block nr b - only for last 256 blocks excluding current |
| :red_circle: | `coinbase()` | current mining beneficiary |
| :red_circle: | `timestamp()` | timestamp of the current block in seconds since the epoch |
| :red_circle: | `number()` | current block number |
| :red_circle: | `difficulty()` | difficulty of the current block (see note below) |
| :red_circle: | `prevrandao()` | randomness provided by the beacon chain (see note below) |
| :red_circle: | `gaslimit()` | block gas limit of the current block |
