# ethereum-star

A tool to verify solidity contracts via translation to F*. 


# Tools 

There are two tools in this distribution:

## evmstar 

evmstar is a tool that reads in an EVM program and translates it 
to F*. The source for this tool is in 
the `src/evmstar` directory. To build it, install `batteries` via opam, and 
then run `make` in that directory. To run it, type

```
./EvmStar.exe -i path/to/pgm.evm 
```

Type `EvmStar.exe -h` for the tool's annotation functionality. 

## solidstar

solidstar is a tool that translates Solidity contracts to F*.
The source for this tool is in the `src/solidstar` directory. To 
build it, install `menhir`, `PCRE` and `ulex` via opam, and then
run `make` in that directory. To run it, type

```
./soliditystar.native x.sol
``` 



# Examples

Some small examples are given in the /examples directory. 

Larger examples of bytecodes and contracts can be downloaded using the scripts
in data/scripts. You need mkdir data/bytecode and data/contracts the 
directories already. 

# References

For some context, see: 

- Results of recent discussions: https://blog.ethereum.org/2016/06/19/thinking-smart-contract-security/
- Symbolic execution tool (OYENTE) paper - To appear at CCS2016: https://eprint.iacr.org/2016/633.pdf
- Non-formal automated tool: http://hackingdistributed.com/2016/06/16/scanning-live-ethereum-contracts-for-bugs/
- Develop smart contracts using Idris: http://publications.lib.chalmers.se/records/fulltext/234939/234939.pdf
- Solidity developer on Why3 list: http://lists.gforge.inria.fr/pipermail/why3-club/2016-July/001383.html

Other links to attacks:
- http://martin.swende.se/blog/Breaking_the_house.html
- http://vessenes.com/more-ethereum-attacks-race-to-empty-is-the-real-deal/
- http://vessenes.com/deconstructing-thedao-attack-a-brief-code-tour/
- http://hackingdistributed.com/2016/07/13/reentrancy-woes/

EVM tutorial:
- https://github.com/ethereum/wiki/wiki/Ethereum-Development-Tutorial
- SUBTLETIES (!): https://github.com/ethereum/wiki/wiki/Subtleties

Reference:
- [Yellow paper](https://github.com/mitls/ethereum-star/blob/master/docs/yellow-paper.pdf)

Resources:
- [Solidity browser compiler](https://chriseth.github.io/browser-solidity/#version=soljson-latest.js)
- [EVM disassembler](https://github.com/Arachnid/evmdis)
- [Ethereum Block Explorer - Contract accounts](http://etherscan.io/accounts/c)






