Blanc: A Minimal EVM Programming Language for Interactive Verification
======================================================================

Blanc is a minimal EVM programming language optimized for formal verification 
with interactive theorem provers. Blanc's toolchain is implemented in Lean 4.
This repo contains the following files:

- [Basic.lean](Blanc/Basic.lean): generic definitions and lemmas (for Booleans, 
  lists, bit vectors, bytes, etc.) that are useful for but not specific to Blanc.
- [Semantics.lean](Blanc/Semantics.lean): formalized semantics of the EVM and Blanc.
- [Common.lean](Blanc/Common.lean): definitions and lemmas generally useful for writing and 
  verifying Blanc programs, including the correctness proof for the Blanc 
  compiler and tactics for automating Blanc program verification. 
- [Weth.lean](Blanc/Weth.lean): proof-of-concept port of the Wrapped Ether (WETH) contract.
- [Solvent.lean](Blanc/Solvent.lean): proof of solvency preservation for the ported WETH contract.
- [Deployer.lean](Blanc/Deployer.lean): makeshift solution for deploying Blanc program bytecode.
  generates deployer Solidity code for bytecodes compiled from Blanc programs.
- [blanc.pdf](blanc.pdf): an overview of the Blanc language and toolchain (rough draft).


