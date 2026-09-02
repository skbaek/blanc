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
-- Materialized as NOT(0): two bytes instead of a 33-byte PUSH32.
def supplySlot : B256 := B256.max

-- The bodies cache the all-ones word: besides naming `supplySlot` for SLOAD /
-- SSTORE, shifting it right by 130 yields the common 2^126 - 1 magnitude cap.
-- Shifting that retained cap right by 30 yields `maxValue = 2^96 - 1`.
def pushMaxWord : Line := [pushB256 0, not]

def pushMaxAndCap : Line :=
  [pushB256 0, not, dup 0, pushB256 130, shr]

def pushSupplySlot : Line := pushMaxWord

-- deposit() — payable --

-- Mint `m = a·(S+offset) / (B₀+1)` shares to caller, where `a` is the call
-- value and `B₀ = SELFBALANCE − CALLVALUE` is the balance the deposit's
-- pricing sees (the incoming value is already credited mid-call and must
-- not price itself). Returns `m`.
def deposit : Func :=
  pushMaxAndCap +++ -- M :: U, where M=maxBalance=maxSupply and U=supplySlot
  callvalue ::: dup 1 ::: pushB256 30 ::: shr ::: lt :::
    -- fₐ :: M :: U, where fₐ=(maxValue <? a)
  callvalue ::: selfbalance ::: sub ::: -- B₀ :: fₐ :: M :: U
  dup 0 ::: dup 3 ::: lt ::: dup 2 ::: add :::
    -- (fₐ+fᴮ) :: B₀ :: fₐ :: M :: U, fᴮ=(M <? B₀)
  .revert <?> -- [either pre-arithmetic magnitude guard failed: revert]
           -- B₀ :: 0 :: M :: U
  pushB256 1 ::: add ::: -- (B₀+1) :: 0 :: M :: U
  dup 3 ::: sload ::: -- S :: (B₀+1) :: 0 :: M :: U
  dup 0 ::: pushB256 offset ::: add :::
    -- (S+offset) :: S :: (B₀+1) :: 0 :: M :: U
  callvalue ::: mul ::: -- a·(S+offset) :: S :: (B₀+1) :: 0 :: M :: U
  dup 2 ::: swap 0 ::: div ::: -- m :: S :: (B₀+1) :: 0 :: M :: U
  dup 1 ::: dup 1 ::: add ::: -- (S+m) :: m :: S :: (B₀+1) :: 0 :: M :: U
  dup 0 ::: dup 6 ::: lt ::: -- (M <? S+m) :: (S+m) :: m :: S :: (B₀+1) :: 0 :: M :: U
  .revert <?> -- [post-deposit supply above maxSupply: revert]
           -- (S+m) :: m :: S :: (B₀+1) :: 0 :: M :: U
  dup 6 ::: sstore ::: -- m :: S :: (B₀+1) :: 0 :: M :: U
                        -- [total supply is now up to date]
  dup 0 ::: caller ::: sload ::: add ::: -- (bal+m) :: m :: S :: (B₀+1) :: 0 :: M :: U
  caller ::: sstore ::: -- m :: S :: (B₀+1) :: 0 :: M :: U
                        -- [caller share balance is now up to date]
  mstoreAt 0 +++ -- S :: (B₀+1) :: 0 :: M :: U || m
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
  pushMaxWord +++ -- U=supplySlot
  arg 0 +++ dup 0 ::: caller ::: sload ::: -- bal :: s :: s :: U
  dup 1 ::: dup 1 ::: lt ::: -- (bal <? s) :: bal :: s :: s
  .revert <?> -- [insufficient share balance: revert]
           -- bal :: s :: s :: U
  sub ::: caller ::: sstore ::: -- s :: U
                                -- [caller share balance is now up to date]
  selfbalance ::: dup 0 ::: dup 3 ::: pushB256 130 ::: shr ::: lt :::
    -- (maxBalance <? B) :: B :: s :: U
  .revert <?> -- [balance above maxBalance: revert]
           -- B :: s :: U
  pushB256 1 ::: add ::: -- (B+1) :: s :: U
  dup 1 ::: mul ::: -- s·(B+1) :: s :: U
  dup 2 ::: sload ::: -- S :: s·(B+1) :: s :: U
  dup 0 ::: pushB256 offset ::: add ::: -- (S+offset) :: S :: s·(B+1) :: s :: U
  swap 1 ::: -- s·(B+1) :: S :: (S+offset) :: s :: U
  dup 2 ::: swap 0 ::: div ::: -- p :: S :: (S+offset) :: s :: U
  dup 3 ::: dup 2 ::: sub ::: -- (S−s) :: p :: S :: (S+offset) :: s :: U
  dup 5 ::: sstore ::: -- p :: S :: (S+offset) :: s :: U
                        -- [total supply is now up to date;
                        --  state fully settled before the send]
  dup 0 ::: -- p :: p :: S :: (S+offset) :: s :: U
  sendToCaller +++ -- success? :: p :: S :: (S+offset) :: s :: U
  (mstoreAt 0 +++ returnMemoryRange 0 32) <?> .revert
  -- [revert if the send failed; otherwise return p]

-- convertToShares(uint256 a) — view --

-- The deposit formula at the current state (`B₀ = SELFBALANCE`: no value in
-- flight), replicating deposit's arithmetic-guard revert region exactly,
-- including the supply-cap check on the hypothetical mint.
def convertToShares : Func :=
  pushMaxAndCap +++ -- M :: U
  arg 0 +++ dup 0 ::: dup 2 ::: pushB256 30 ::: shr ::: lt :::
    -- fₐ :: a :: M :: U, where fₐ=(maxValue <? a)
  selfbalance ::: dup 0 ::: dup 4 ::: lt ::: dup 2 ::: add :::
    -- (fₐ+fᴮ) :: B :: fₐ :: a :: M :: U, fᴮ=(M <? B)
  .revert <?> -- [either pre-arithmetic magnitude guard failed: revert]
           -- B :: 0 :: a :: M :: U
  pushB256 1 ::: add ::: -- (B+1) :: 0 :: a :: M :: U
  dup 4 ::: sload ::: -- S :: (B+1) :: 0 :: a :: M :: U
  dup 0 ::: pushB256 offset ::: add :::
    -- (S+offset) :: S :: (B+1) :: 0 :: a :: M :: U
  dup 4 ::: mul ::: -- a·(S+offset) :: S :: (B+1) :: 0 :: a :: M :: U
  dup 2 ::: swap 0 ::: div ::: -- m :: S :: (B+1) :: 0 :: a :: M :: U
  dup 1 ::: dup 1 ::: add ::: -- (S+m) :: m :: S :: (B+1) :: 0 :: a :: M :: U
  dup 6 ::: lt ::: -- (M <? S+m) :: m :: S :: (B+1) :: 0 :: a :: M :: U
  .revert <?> -- [hypothetical post-deposit supply above maxSupply: revert]
           -- m :: S :: (B+1) :: 0 :: a :: M :: U
  mstoreAt 0 +++ returnMemoryRange 0 32

-- convertToAssets(uint256 s) — view --

-- The withdraw formula at the current state, replicating withdraw's
-- arithmetic-guard revert region (the ledger-sufficiency check is not
-- arithmetic and has no view analogue; the supply cap bounds the argument
-- instead, which every share count a real withdraw can burn satisfies).
def convertToAssets : Func :=
  pushMaxAndCap +++ -- M :: U
  arg 0 +++ dup 0 ::: dup 2 ::: lt :::
    -- fₛ :: s :: M :: U, where fₛ=(maxSupply <? s)
  selfbalance ::: dup 0 ::: dup 4 ::: lt ::: dup 2 ::: add :::
    -- (fₛ+fᴮ) :: B :: fₛ :: s :: M :: U, fᴮ=(M <? B)
  .revert <?> -- [either pre-arithmetic magnitude guard failed: revert]
           -- B :: 0 :: s :: M :: U
  pushB256 1 ::: add ::: -- (B+1) :: 0 :: s :: M :: U
  dup 2 ::: mul ::: -- s·(B+1) :: 0 :: s :: M :: U
  dup 4 ::: sload ::: -- S :: s·(B+1) :: 0 :: s :: M :: U
  pushB256 offset ::: add ::: -- (S+offset) :: s·(B+1) :: 0 :: s :: M :: U
  swap 0 ::: div ::: -- p :: 0 :: s :: M :: U
  mstoreAt 0 +++ returnMemoryRange 0 32

-- the donation lever --

-- Plain ETH receipt: accept and mint nothing. Reached through the dispatch
-- fallback, so it must separate the two ways a call gets here: empty
-- calldata is a donation and succeeds; any unmatched selector reverts.
def donate : Func :=
  calldatasize ::: .revert <?> Func.stop

-- main --

-- The four public selector/body pairs in ascending selector order.  This
-- remains the checked ABI catalogue used by property statements; the runtime
-- below hand-shapes their ingress so the three nonpayable entries share one
-- value split instead of carrying three identical wrappers.
def prorataFuncs : List (B256 × Func) :=
  [ (selector "convertToAssets" [.uint256], convertToAssets), -- 0x07a2d13a
    (selector "withdraw" [.uint256], withdraw),               -- 0x2e1a7d4d
    (selector "convertToShares" [.uint256], convertToShares), -- 0xc6e6f592
    (selector "deposit" [], deposit) ]                        -- 0xd0e30db0

-- The catalogue order is checked rather than commented.  Besides preventing
-- ABI drift, it retains the same machine-checked selector inventory consumed
-- by the generic contract-family tooling.
theorem prorataFuncs_sorted : DispatchTree.sorted prorataFuncs = true := by
  decide +kernel

-- Zero-value calls try the three nonpayable selectors in hot-path order:
-- withdrawal first, then the share preview, then the asset preview.  Failed
-- tests preserve the selector for the next comparison; successful tests POP
-- that preserved word before entering the original body.  The final equality
-- consumes it directly.  An unmatched selector reaches `donate`, whose
-- calldata-size split rejects every nonempty miss and accepts only receive.
def zeroValueDispatch : Func :=
  dup 0 ::: pushB256 (selector "withdraw" [.uint256]) ::: eq :::
  ((pop ::: withdraw) <?>
  dup 0 ::: pushB256 (selector "convertToShares" [.uint256]) ::: eq :::
  ((pop ::: convertToShares) <?>
  pushB256 (selector "convertToAssets" [.uint256]) ::: eq :::
  (convertToAssets <?> donate)))

-- Deposit is tested first because it alone is selector-payable.  On a miss,
-- raw CALLVALUE is the shared nonpayability split: zero proceeds to the three
-- remaining selectors; nonzero discards the selector and reuses `donate`,
-- which accepts precisely empty calldata and otherwise gives the same empty
-- revert as the former per-entry guards.  Empty calldata is therefore payable
-- at either value, while every recognized non-deposit selector remains
-- nonpayable and every nonempty miss still reverts.
def prorataMain : Func :=
  fsig +++
  dup 0 ::: pushB256 (selector "deposit" []) ::: eq :::
  ((pop ::: deposit) <?>
  callvalue ::: ((pop ::: donate) <?> zeroValueDispatch))

def prorata : Prog := ⟨prorataMain, []⟩

end Prorata

end Blanc
