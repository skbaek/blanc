#!/usr/bin/env python3
"""The finite surface the PRORATA vault differential must execute.

This is the G1/G2 exact ABI surface, in the artifact gate's source order.  The
differential requires every one of these 25 selectors to be executed on both
compiled sides (removal-ledger row K23), so a selector cannot silently drop out
of the boundary matrix.  It is a coverage declaration, not a result oracle: it
carries no expected post-state, return value, allowed mismatch or measurement.

The per-case disposition ledger that used to live here (129 declared case
names, each credited by an executed-ID record) was retired under the evidence
economy directive; see `scripts/GATES.md`, "Evidence economy (standing)".
"""
from __future__ import annotations

SELECTORS = (
    "totalAssets()", "name()", "convertToAssets(uint256)",
    "approve(address,uint256)", "previewWithdraw(uint256)", "totalSupply()",
    "transferFrom(address,address,uint256)", "decimals()", "asset()",
    "maxDeposit(address)", "previewRedeem(uint256)",
    "deposit(uint256,address)", "balanceOf(address)",
    "mint(uint256,address)", "symbol()", "transfer(address,uint256)",
    "previewMint(uint256)", "withdraw(uint256,address,address)",
    "redeem(uint256,address,address)", "maxMint(address)",
    "convertToShares(uint256)", "maxWithdraw(address)", "maxRedeem(address)",
    "allowance(address,address)", "previewDeposit(uint256)",
)
