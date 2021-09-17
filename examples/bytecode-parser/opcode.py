class Opcode:
	def __init__ (self, code, operation, bytes):
		self.code = code	
		self.operation = operation
		self.bytes = bytes	

lst = [
Opcode('00','STOP',0),
Opcode('01','ADD',0),
Opcode('02','MUL',0),
Opcode('03','SUB',0),
Opcode('04','DIV',0),
Opcode('05','SDIV',0),
Opcode('06','MOD',0),
Opcode('07','SMOD',0),
Opcode('08','ADDMOD',0),
Opcode('09','MULMOD',0),
Opcode('0a','EXP',0),
Opcode('0b','SIGNEXTEND',0),
Opcode('10','LT',0),
Opcode('11','GT',0),
Opcode('12','SLT',0),
Opcode('13','SGT',0),
Opcode('14','EQ',0),
Opcode('15','ISZERO',0),
Opcode('16','AND',0),
Opcode('17','OR',0),
Opcode('18','XOR',0),
Opcode('19','NOT',0),
Opcode('1a','BYTE',0),
Opcode('20','SHA3',0),
Opcode('30','ADDRESS',0),
Opcode('31','BALANCE',0),
Opcode('32','ORIGIN',0),
Opcode('33','CALLER',0),
Opcode('34','CALLVALUE',0),
Opcode('35','CALLDATALOAD',0),
Opcode('36','CALLDATASIZE',0),
Opcode('37','CALLDATACOPY',0),
Opcode('38','CODESIZE',0),
Opcode('39','CODECOPY',0),
Opcode('3a','GASPRICE',0),
Opcode('3b','EXTCODESIZE',0),
Opcode('3c','EXTCODECOPY',0),
Opcode('40','BLOCKHASH',0),
Opcode('41','COINBASE',0),
Opcode('42','TIMESTAMP',0),
Opcode('43','NUMBER',0),
Opcode('44','DIFFICULTY',0),
Opcode('45','GASLIMIT',0),
Opcode('50','POP',0),
Opcode('51','MLOAD',0),
Opcode('52','MSTORE',0),
Opcode('53','MSTORE8',0),
Opcode('54','SLOAD',0),
Opcode('55','SSTORE',0),
Opcode('56','JUMP',0),
Opcode('57','JUMP1',0),
Opcode('58','PC',0),
Opcode('59','MSIZE',0),
Opcode('5a','GAS',0),
Opcode('5b','JUMPDEST',0),
Opcode('60','PUSH1',1),
Opcode('61','PUSH2',2),
Opcode('62','PUSH3',3),
Opcode('63','PUSH4',4),
Opcode('64','PUSH5',5),
Opcode('65','PUSH6',6),
Opcode('66','PUSH7',7),
Opcode('67','PUSH8',8),
Opcode('68','PUSH9',9),
Opcode('69','PUSH10',10),
Opcode('6a','PUSH11',11),
Opcode('6b','PUSH12',12),
Opcode('6c','PUSH13',13),
Opcode('6d','PUSH14',14),
Opcode('6e','PUSH15',15),
Opcode('6f','PUSH16',16),
Opcode('70','PUSH17',17),
Opcode('71','PUSH18',18),
Opcode('72','PUSH19',19),
Opcode('73','PUSH20',20),
Opcode('74','PUSH21',21),
Opcode('75','PUSH22',22),
Opcode('76','PUSH23',23),
Opcode('77','PUSH24',24),
Opcode('78','PUSH25',25),
Opcode('79','PUSH26',26),
Opcode('7a','PUSH27',27),
Opcode('7b','PUSH28',28),
Opcode('7c','PUSH29',29),
Opcode('7d','PUSH30',30),
Opcode('7e','PUSH31',31),
Opcode('7f','PUSH32',32),
Opcode('80','DUP1',0),
Opcode('81','DUP2',0),
Opcode('82','DUP3',0),
Opcode('83','DUP4',0),
Opcode('84','DUP5',0),
Opcode('85','DUP6',0),
Opcode('86','DUP7',0),
Opcode('87','DUP8',0),
Opcode('88','DUP9',0),
Opcode('89','DUP10',0),
Opcode('8a','DUP11',0),
Opcode('8b','DUP12',0),
Opcode('8c','DUP13',0),
Opcode('8d','DUP14',0),
Opcode('8e','DUP15',0),
Opcode('8f','DUP16',0),
Opcode('90','SWAP1',0),
Opcode('91','SWAP2',0),
Opcode('92','SWAP3',0),
Opcode('93','SWAP4',0),
Opcode('94','SWAP5',0),
Opcode('95','SWAP6',0),
Opcode('96','SWAP7',0),
Opcode('97','SWAP8',0),
Opcode('98','SWAP9',0),
Opcode('99','SWAP10',0),
Opcode('9a','SWAP11',0),
Opcode('9b','SWAP12',0),
Opcode('9c','SWAP13',0),
Opcode('9d','SWAP14',0),
Opcode('9e','SWAP15',0),
Opcode('9f','SWAP16',0),
Opcode('a0','LOG0',0),
Opcode('a1','LOG1',0),
Opcode('a2','LOG2',0),
Opcode('a3','LOG3',0),
Opcode('a4','LOG4',0),
Opcode('f0','CREATE',0),
Opcode('f1','CALL',0),
Opcode('f2','CALLCODE',0),
Opcode('f3','RETURN',0),
Opcode('f4','DELEGATECALL',0),
Opcode('ff','SUICIDE',0),
]

line = '6060'
def ListSearch(lst, opcode):
	for i, val in enumerate(lst):
		if val.code == opcode :
			return val

def WriteToFile (name, line):
	f =  open(name, 'w')
	f.write(line)
	f.close();

def ReadByte(line, counter, length):
	result = ''
	for i in range (0, length*2):
		result = result + line[counter + i];
	return result

def OneOperation(line, counter, f):	
	opcode = ReadByte(line, counter, 1)
	a = ListSearch(lst, opcode)
	counter = counter + 2
	if (a == None):
		f.write(opcode + 'Is not found')
	else:
		f.write(a.operation +' ' + ReadByte(line, counter, a.bytes) + '\n') 
		counter = counter + 2 * a.bytes
	return counter

def Parse (line, address):
	try:
		f = open(address,'w')
		counter = 0
		while counter < len(line):
			counter = OneOperation(line, counter, f)
		f.close()
	except: 
		print("Error while writing to the file " + address)

def main():
	import argparse
	parser = argparse.ArgumentParser(description='Contract parser')
	parser.add_argument('inputAddress', metavar='input', type=str, 
                    help='address from where to read')
	parser.add_argument('outputAddress', metavar = 'output', type = str, help = 'address to where to write')
	args = parser.parse_args()
	inputAddress = args.inputAddress
	outputAddress = args.outputAddress
	line = ''
	try:
		f = open(inputAddress,'r')
		line = f.read()
		line = line[0:len(line)-1]
	except:
		print ("Exception while opening")
	Parse(line,outputAddress)
	
				
main()

