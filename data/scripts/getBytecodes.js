/*
   Copyright 2016 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
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
