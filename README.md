# Blanc: A Minimal EVM Programming Language for Interactive Verification

Blanc is an EVM programming language optimized for formal verification 
with interactive theorem provers. Blanc's toolchain is implemented in Lean 4.
This repo contains the following files:

- [Basic.lean](Blanc/Basic.lean): generic definitions and lemmas (for Booleans, 
  lists, bit vectors, bytes, etc.) useful for but not specific to Blanc.
- [Semantics.lean](Blanc/Semantics.lean): formalized semantics of EVM and Blanc.
- [Common.lean](Blanc/Common.lean): definitions and lemmas for writing and 
  verifying Blanc programs, including the Blanc compiler's correctness proof and 
  tactics for automating Blanc program verification. 
- [Weth.lean](Blanc/Weth.lean): proof-of-concept implementation of the Wrapped 
  Ether (WETH) contract in Blanc.
- [Solvent.lean](Blanc/Solvent.lean): proof of solvency for the WETH implementation.


