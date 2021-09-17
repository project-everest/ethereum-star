contract MyContract {
  uint balance;

  function MyContract() {
    Mint(1000000);
  }

  function Mint(uint amount) internal {
    balance = amount;
  }

  function Withdraw(uint n) {
    if (balance <= n) {
        msg.sender.send(n);
        balance -= n;
    }
  }

  function GetBalance() constant returns(uint) {
    return balance;
  }
}