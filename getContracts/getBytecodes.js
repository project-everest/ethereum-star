const HTTP = require('http');
const FS = require('fs');

const getBytecode = function(contractId, i) {
	const contract = /verifiedbytecode2(.|\n|\s)*?\<\/div\>/g
	const url = 'http://etherscan.io/address/';
	HTTP.get(`${url}${contractId}#code`, function(res) {
		var body = '';
		res.on('data', function(chunk) {
			body += chunk;
		});
		res.on('end', function() {
			var contracts = body.match(contract);
			contracts.forEach(function(c) {
				c = c.substring(19, c.length - 6);
				FS.writeFileSync(`bytecode/${i}.txt`, c);
				console.log(`Bytecode ${i} fetched.`);
			});
		});
	});
};

const getContractList = function(page) {
	const url = 'http://etherscan.io/contractsVerified/';
	HTTP.get(`${url}${page}`, function(res) {
		const contractId = /0x\w+#code/gm;
		var body = '';
		res.on('data', function(chunk) {
			body += chunk;
		});
		res.on('end', function() {
			var contractIds = body.match(contractId);
			console.log(
				`Page ${page}: ${contractIds.length} contracts found.`
			);
			contractIds.forEach(function(c, i) {
				contractIds[i] = c.substring(0, 42);
				getBytecode(contractIds[i], `${page}_${i}`);
			});
		});
	});
};

var timeout = 0;
for (var p = 1; p < 17; p++) {
	setTimeout(function(page) {
		console.log(`Page ${page} out of 16...`);
		getContractList(page);
	}, timeout, p);
	timeout += 1234;
};
