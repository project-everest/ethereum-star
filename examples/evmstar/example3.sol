contract MyBank {
  mapping (address => uint) balances;

  function Deposit() {
    balances[msg.sender] += msg.value;
  }

  function Withdraw() {
    msg.sender.send(balances[msg.sender]);
    balances[msg.sender] = 0;
  }

  function GetBalance() constant returns(uint) {
    return balances[msg.sender];
  }
}