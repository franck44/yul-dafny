pragma solidity ^0.8.20;
 
// import "./IERC20.sol";

contract DynArray {
    uint[] public myArray;

    function set(uint v, uint index) external {
        myArray[index] = v;
    }
}