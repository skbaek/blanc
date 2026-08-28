-- Prorata.lean : PRORATA, the pro-rata share ledger étude
--
-- An ETH-native, non-transferable share ledger, composed from scratch:
-- `deposit()` mints shares at the current ratio, `withdraw(uint256)` burns
-- shares and sends ETH (handing control to untrusted code mid-flight), the
-- two conversion views expose the pricing arithmetic, and plain ETH receipt
-- is accepted without minting — the donation lever. Mint and burn pricing
-- carry the virtual-offset defense in the OpenZeppelin decimal-offset shape:
-- `offset` virtual shares beside one virtual asset, so the share price
-- `(B+1)/(S+offset)` starts at `1/offset` and — the ledger's core invariant —
-- never decreases.
--
-- Deliberately bare by design: no events, no token standard, no
-- transferability, no address argument anywhere on the surface (the share
-- mapping is keyed by CALLER, which is address-shaped by construction, so
-- the WETH-class address-guard route is never even exercised).
--
-- Arithmetic route (goal `prorata-etude-v1`, fixed decision 5): single-word
-- arithmetic under contract-enforced magnitude guards. Every priced product
-- provably stays below 2^256: deposits bound `a ≤ maxValue` and
-- `B₀ ≤ maxBalance` before computing `a·(S+offset)`, withdrawals and views
-- bound `B ≤ maxBalance` (and the supply cap `maxSupply` rides the ledger
-- invariant) before computing `s·(B+1)`. A donation can push `B` above
-- `maxBalance`; that halts withdrawals until balance falls — PRORATA makes
-- no liveness claim. From genesis, the least such credit is
-- `maxBalance + 1 = 2^126` wei; from an arbitrary admissible state the exact
-- threshold is `maxBalance + 1 - B`.

import Blanc.CommonProofs

namespace Blanc

open Jaune


open Jaune.Ninst Ninst

namespace Prorata

-- constants --

-- The virtual-share offset (OZ decimal offset δ = 3). Additive everywhere:
-- it appears in code only as `S + offset`, never as a factor.
def offset : B256 := 1000

-- Largest single deposit: exactly 2^96 − 1 wei.
def maxValue : B256 := Nat.toB256 (2 ^ 96 - 1)

-- Share-supply cap: exactly 2^126 − 1 shares. The invariant
-- `S ≤ offset · B` is a safety statement, not a liveness or capacity claim.
def maxSupply : B256 := Nat.toB256 (2 ^ 126 - 1)

-- Balance ceiling for any operation that multiplies by `B + 1`.
def maxBalance : B256 := Nat.toB256 (2 ^ 126 - 1)

-- Total share supply lives at the all-ones slot, which is never
-- address-shaped, so it cannot collide with any CALLER-keyed balance slot.
-- Pushed as NOT(0): two bytes instead of a 33-byte PUSH32.
def supplySlot : B256 := B256.max

def pushSupplySlot : Line := [pushB256 0, not]

-- deposit() — payable --

-- Mint `m = a·(S+offset) / (B₀+1)` shares to caller, where `a` is the call
-- value and `B₀ = SELFBALANCE − CALLVALUE` is the balance the deposit's
-- pricing sees (the incoming value is already credited mid-call and must
-- not price itself). Returns `m`.
def deposit : Func :=
  callvalue ::: pushB256 maxValue ::: lt ::: -- (maxValue <? a)
  .rev <?> -- [deposit above maxValue: revert]
  callvalue ::: selfbalance ::: sub ::: -- B₀
  dup 0 ::: pushB256 maxBalance ::: lt ::: -- (maxBalance <? B₀) :: B₀
  .rev <?> -- [pre-deposit balance above maxBalance: revert]
           -- B₀
  pushB256 1 ::: add ::: -- (B₀+1)
  pushSupplySlot +++ sload ::: -- S :: (B₀+1)
  dup 0 ::: pushB256 offset ::: add ::: -- (S+offset) :: S :: (B₀+1)
  callvalue ::: mul ::: -- a·(S+offset) :: S :: (B₀+1)
  dup 2 ::: swap 0 ::: div ::: -- m :: S :: (B₀+1)
  dup 1 ::: dup 1 ::: add ::: -- (S+m) :: m :: S :: (B₀+1)
  dup 0 ::: pushB256 maxSupply ::: lt ::: -- (maxSupply <? S+m) :: (S+m) :: m :: S :: (B₀+1)
  .rev <?> -- [post-deposit supply above maxSupply: revert]
           -- (S+m) :: m :: S :: (B₀+1)
  pushSupplySlot +++ sstore ::: -- m :: S :: (B₀+1)
                                -- [total supply is now up to date]
  dup 0 ::: caller ::: sload ::: add ::: -- (bal+m) :: m :: S :: (B₀+1)
  caller ::: sstore ::: -- m :: S :: (B₀+1)
                        -- [caller share balance is now up to date]
  mstoreAt 0 +++ -- S :: (B₀+1) || m
  returnMemoryRange 0 32

-- withdraw(uint256 s) — nonpayable --

-- ( p :: junk -- ) send `p` wei to caller with all remaining gas, empty
-- calldata, no return-data window: the mid-flight hand-off to untrusted
-- code. State is fully settled before this runs (checks-effects-
-- interactions), and the payout leaves the success flag on the stack.
def sendToCaller : Line :=
  pushList [0, 0, 0, 0] ++ -- 0 :: 0 :: 0 :: 0 :: p :: junk
  swap 3 :: caller :: -- caller :: p :: 0 :: 0 :: 0 :: 0 :: junk
  gas :: call :: -- success? :: junk
  []

-- Burn `s` shares from caller, send `p = s·(B+1) / (S+offset)` wei to
-- caller, revert if the send fails. Returns `p`. The payout satisfies
-- `p ≤ B` structurally (`s ≤ S` and the virtual asset make it strictly
-- under `B+1`), so the send cannot fail for insufficient balance.
def withdraw : Func :=
  arg 0 +++ dup 0 ::: caller ::: sload ::: -- bal :: s :: s
  dup 1 ::: dup 1 ::: lt ::: -- (bal <? s) :: bal :: s :: s
  .rev <?> -- [insufficient share balance: revert]
           -- bal :: s :: s
  sub ::: caller ::: sstore ::: -- s
                                -- [caller share balance is now up to date]
  selfbalance ::: dup 0 ::: pushB256 maxBalance ::: lt ::: -- (maxBalance <? B) :: B :: s
  .rev <?> -- [balance above maxBalance: revert]
           -- B :: s
  pushB256 1 ::: add ::: -- (B+1) :: s
  dup 1 ::: mul ::: -- s·(B+1) :: s
  pushSupplySlot +++ sload ::: -- S :: s·(B+1) :: s
  dup 0 ::: pushB256 offset ::: add ::: -- (S+offset) :: S :: s·(B+1) :: s
  swap 1 ::: -- s·(B+1) :: S :: (S+offset) :: s
  dup 2 ::: swap 0 ::: div ::: -- p :: S :: (S+offset) :: s
  dup 3 ::: dup 2 ::: sub ::: -- (S−s) :: p :: S :: (S+offset) :: s
  pushSupplySlot +++ sstore ::: -- p :: S :: (S+offset) :: s
                                -- [total supply is now up to date;
                                --  state fully settled before the send]
  dup 0 ::: -- p :: p :: S :: (S+offset) :: s
  sendToCaller +++ -- success? :: p :: S :: (S+offset) :: s
  (mstoreAt 0 +++ returnMemoryRange 0 32) <?> .rev
  -- [revert if the send failed; otherwise return p]

-- convertToShares(uint256 a) — view --

-- The deposit formula at the current state (`B₀ = SELFBALANCE`: no value in
-- flight), replicating deposit's arithmetic-guard revert region exactly,
-- including the supply-cap check on the hypothetical mint.
def convertToShares : Func :=
  arg 0 +++ dup 0 ::: pushB256 maxValue ::: lt ::: -- (maxValue <? a) :: a
  .rev <?> -- [amount above maxValue: revert]
           -- a
  selfbalance ::: dup 0 ::: pushB256 maxBalance ::: lt ::: -- (maxBalance <? B) :: B :: a
  .rev <?> -- [balance above maxBalance: revert]
           -- B :: a
  pushB256 1 ::: add ::: -- (B+1) :: a
  pushSupplySlot +++ sload ::: -- S :: (B+1) :: a
  dup 0 ::: pushB256 offset ::: add ::: -- (S+offset) :: S :: (B+1) :: a
  dup 3 ::: mul ::: -- a·(S+offset) :: S :: (B+1) :: a
  dup 2 ::: swap 0 ::: div ::: -- m :: S :: (B+1) :: a
  dup 1 ::: dup 1 ::: add ::: -- (S+m) :: m :: S :: (B+1) :: a
  pushB256 maxSupply ::: lt ::: -- (maxSupply <? S+m) :: m :: S :: (B+1) :: a
  .rev <?> -- [hypothetical post-deposit supply above maxSupply: revert]
           -- m :: S :: (B+1) :: a
  mstoreAt 0 +++ returnMemoryRange 0 32

-- convertToAssets(uint256 s) — view --

-- The withdraw formula at the current state, replicating withdraw's
-- arithmetic-guard revert region (the ledger-sufficiency check is not
-- arithmetic and has no view analogue; the supply cap bounds the argument
-- instead, which every share count a real withdraw can burn satisfies).
def convertToAssets : Func :=
  arg 0 +++ dup 0 ::: pushB256 maxSupply ::: lt ::: -- (maxSupply <? s) :: s
  .rev <?> -- [share count above maxSupply: revert]
           -- s
  selfbalance ::: dup 0 ::: pushB256 maxBalance ::: lt ::: -- (maxBalance <? B) :: B :: s
  .rev <?> -- [balance above maxBalance: revert]
           -- B :: s
  pushB256 1 ::: add ::: -- (B+1) :: s
  dup 1 ::: mul ::: -- s·(B+1) :: s
  pushSupplySlot +++ sload ::: -- S :: s·(B+1) :: s
  pushB256 offset ::: add ::: -- (S+offset) :: s·(B+1) :: s
  swap 0 ::: div ::: -- p :: s
  mstoreAt 0 +++ returnMemoryRange 0 32

-- the donation lever --

-- Plain ETH receipt: accept and mint nothing. Reached through the dispatch
-- fallback, so it must separate the two ways a call gets here: empty
-- calldata is a donation and succeeds; any unmatched selector reverts.
def donate : Func :=
  calldatasize ::: .rev <?> Func.stop

-- main --

-- The four dispatched functions in ascending selector order. Everything
-- except `deposit` rejects nonzero call value; the payable surface is
-- exactly `deposit` and the empty-calldata donation path.
def prorataFuncs : List (B256 × Func) :=
  [ (selector "convertToAssets" [.uint256], nonpayable convertToAssets), -- 0x07a2d13a
    (selector "withdraw" [.uint256], nonpayable withdraw),               -- 0x2e1a7d4d
    (selector "convertToShares" [.uint256], nonpayable convertToShares), -- 0xc6e6f592
    (selector "deposit" [], deposit) ]                                   -- 0xd0e30db0

-- `dispatchWith`'s ordering precondition, checked rather than commented
-- (the WETH precedent: a misordered entry would compile to an unreachable
-- function, and this line fails to elaborate instead).
theorem prorataFuncs_sorted : DispatchTree.sorted prorataFuncs = true := by
  decide +kernel

def prorataTree : DispatchTree := .ofSorted prorataFuncs

def prorata : Prog := ⟨Func.mainWith 1 prorataTree, [donate]⟩

end Prorata

end Blanc
