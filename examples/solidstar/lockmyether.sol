contract LockMyEther {
	
	//Author: General_Illus
	//Date: 3/6/2016
	//Version: LockMyEther v1.0

	address owner;
	
	mapping (address => uint) fees;
	
	struct User
    {
        uint bal; // user balance
        uint expiration_block;  // block ether is unlocked
        bool trickle; // turn trickle on/off
        uint trickle_block;   // last block user attempted trickle witdrawal
    }
	
	mapping (address => User) user;
	
    // Constructor
    function LockMyEther(){
        owner = msg.sender;
		fees[owner] = 0;
    }
	

    // Deposit funds. User cannot alter expiration block once set. Can deposit more Ether though
    function main() {
		
		// Pay half of a percent fee to depost funds
		uint fee = msg.value / 200;
		fees[owner] += fee;
		
		// Deposit Funds
		uint deposit = msg.value - fee;
		user[msg.sender].bal += deposit;
		if (user[msg.sender].expiration_block > 0)
			return;
		user[msg.sender].expiration_block = 0;
    
	}

    // Withdraw funds 
    function withdraw() {
		// Trickle is on, so allow withdraw based on variance between expiration block and last withdraw block
		if (user[msg.sender].trickle == true && user[msg.sender].expiration_block > block.number) {
			uint balance_per_block = user[msg.sender].bal / (user[msg.sender].expiration_block - user[msg.sender].trickle_block);
			uint trickle_balance = balance_per_block * (block.number - user[msg.sender].trickle_block);
			msg.sender.send(trickle_balance);
			user[msg.sender].bal = user[msg.sender].bal - trickle_balance;
			user[msg.sender].trickle_block = block.number;
		}
		// Trickle is off, test is current block is greater than expiration block, if true then withdraw
		else {
			if (user[msg.sender].expiration_block > block.number)
				return;
			msg.sender.send(user[msg.sender].bal);
 			user[msg.sender].bal = 0;
			user[msg.sender].expiration_block = 0;
		}
    }
	
	// Withdraw fees
	function withdrawFees() {
		if (msg.sender == owner)
			owner.send(fees[owner]);
			fees[owner] = 0;
    }
	
	// Check balance of account
    function getBalance() constant returns (uint Balance) {
      return user[msg.sender].bal;
    }
	
	// Check balance of fee account
	function getFeeBalance() constant returns (uint FeeBalance) {
		if (msg.sender == owner)
      		return fees[owner];
    }
	
	// Get latest block number
	function getLatestBlock() constant returns (uint BlockNumber) {	
		return block.number;
	}
	
	// Get expiration block
	function getExpirationBlock() constant returns (uint ExpirationBlock) {
		return user[msg.sender].expiration_block;
	}
	
	// Get trickle block
	function getTrickleBlock() constant returns (uint TrickleBlock) {
		return user[msg.sender].trickle_block;
	}
	
	// Get trickle status
	function getTrickle() constant returns (bool Trickle) {
		return user[msg.sender].trickle;
	}
	
	// Set expiration block
	function setExpirationBlock(uint _blocknumber) {
		// Do not allow anyone to set an expiration after one has already been set
		if (user[msg.sender].expiration_block > 0)
			return;
		// Do not allow anyone to set an expiration that is more than 9M blocks into future
		if (_blocknumber > block.number+9000000)
			return;
		user[msg.sender].expiration_block = _blocknumber;
	}

	//Turn trickle on
	function setTrickleOn() {
		user[msg.sender].trickle = true;
		user[msg.sender].trickle_block = block.number;
	}
	
	//Turn trickle off
	function setTrickleOff() {
		user[msg.sender].trickle = false;
	}

    // Default function
    function() {
        main();
    }

}
