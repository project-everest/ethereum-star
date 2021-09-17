
contract A {
  address owner;

  uint32[] blah;
  mapping (address => uint32) balances;


  event ModifiedBalance(address a, uint32 change);

  struct User {
    address adr;
    uint32 bal;
    uint32 start_block;
  }

  function test(address t) returns (uint32 output) {

  }

}

contract B {

}


