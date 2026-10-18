import Blanc.Composition.UniswapV2PairUsdcWeth9Checkpoint
import Blanc.Composition.UniswapV2PairWeth9CheckJoint
import Blanc.Lift.Usdc.FiniteFootprint

/-!
# A computable checker for the two-token joint checkpoint (C7, U10b)

`checkJoint2 pair usdc weth urows wrows prows base w` decides `JointCheckpoint2` over a finite
description: the predecessor's joint checker on side `.one` (`checkJoint`: the Pair and WETH9
codes, the Pair's storage representation, WETH9's footprint, the Pair's WETH9 rows, the world's
balance sum, the address facts), USDC's checkpoint checker (`checkUsdc`: the three runtimes, the
implementation slot, USDC's footprint over `urows`, the ledger's fixed words), `token0 = usdc`, the
Pair's USDC rows (`checkUsdcHolder`: its balance row listed, unflagged and covering `reserve0`, its
listed allowance rows zero), `pair ≠ usdc`, and neither USDC's nor the Pair's address a precompile
of any covered fork (the Pair's half discharges `usdc_neverSigner_pair`'s `pairNotPrecompile`,
amendment A10). `checkJoint2_sound` is the soundness theorem.

**C7 controls.** `checkJoint2_allowance_control` and `checkJoint2_frozen_control` compose the
statement controls `JointCheckpoint2.allowance_control`/`frozen_control` with soundness: on any
world and rows, a tracked nonzero USDC allowance of the Pair, or a flagged Pair balance word, makes
the checker answer `false`.  `U0` is a concrete synthetic two-token world the checker accepts in the
kernel (`u0_accepts`), so `JointCheckpoint2` is satisfiable (`u0_jointCheckpoint2`); the two
mutants `u0_allowance_rejected` and `u0_frozen_rejected` change exactly one USDC word of `U0` and
are rejected, in the kernel.

Cost: `checkJoint` plus `checkUsdc` plus one pass over USDC's rows.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.Weth9
  Blanc.Composition.UniswapV2PairWeth9Joint Blanc.Lift.FiniteCheckpoint

/-- `checkUsdc` establishes the row facts of its footprint walk (each listed word is its key's slot;
the listed keys are distinct). -/
theorem checkUsdc_rows {P : Adr} {rows : List (Usdc.Key × B256)} {w : Jaune.State}
    (h : Usdc.checkUsdc P rows w = true) :
    RowsSound Usdc.Key.slot Usdc.fixedSlots rows (w.getStor P) := by
  simp only [Usdc.checkUsdc, Bool.and_eq_true] at h
  exact checkRows_sound h.1.1.2

/-- One holder's USDC rows: its balance row is listed, unflagged and holding at least `n` balance
bits, and each of its listed allowance rows reads zero. -/
def checkUsdcHolder (rows : List (Usdc.Key × B256)) (s : Stor) (a : Adr) (n : Nat) : Bool :=
  rows.any (fun r => decide (r.1 = .bal a) && decide (Usdc.frozenBit (s.get r.2) = false) &&
      decide (n ≤ Usdc.balanceBits (s.get r.2))) &&
    rows.all (fun r => match r.1 with
      | .allow o _ => decide (o ≠ a) || decide (s.get r.2 = 0)
      | _ => true)

/-- Holder rows from word facts alone: the weakening of `checkUsdcHolder_sound` the
support-free checker uses (`RowsSound` is unavailable without support; the proof reads only
`word`). -/
theorem checkUsdcHolder_soundW {rows : List (Usdc.Key × B256)} {s : Stor} {a : Adr} {n : Nat}
    (word : ∀ r ∈ rows, Usdc.Key.slot r.1 = r.2)
    (h : checkUsdcHolder rows s a n = true) :
    rowKeys rows (.bal a) ∧ Usdc.frozenBit (s.get (Usdc.balSlot a)) = false ∧
      n ≤ Usdc.balanceBits (s.get (Usdc.balSlot a)) ∧
      ∀ g, rowKeys rows (.allow a g) → s.get (Usdc.allowSlot a g) = 0 := by
  simp only [checkUsdcHolder, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨r, hr, ⟨hkey, hflag⟩, hn⟩, hall⟩ := h
  have hword : Usdc.Key.slot r.1 = r.2 := word r hr
  rw [hkey] at hword
  change Usdc.balSlot a = r.2 at hword
  refine ⟨List.mem_map.mpr ⟨r, hr, hkey⟩, ?_, ?_, ?_⟩
  · rw [hword]
    exact hflag
  · rw [hword]
    exact hn
  · intro g hg
    obtain ⟨r', hr', hkey'⟩ := List.mem_map.mp hg
    have hword' : Usdc.Key.slot r'.1 = r'.2 := word r' hr'
    have hcheck := hall r' hr'
    rw [hkey'] at hword' hcheck
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hcheck
    rcases hcheck with hne | hzero
    · exact absurd rfl hne
    · change Usdc.allowSlot a g = r'.2 at hword'
      rw [hword']
      exact hzero

theorem checkUsdcHolder_sound {rows : List (Usdc.Key × B256)} {s : Stor} {a : Adr} {n : Nat}
    (sound : RowsSound Usdc.Key.slot Usdc.fixedSlots rows s)
    (h : checkUsdcHolder rows s a n = true) :
    rowKeys rows (.bal a) ∧ Usdc.frozenBit (s.get (Usdc.balSlot a)) = false ∧
      n ≤ Usdc.balanceBits (s.get (Usdc.balSlot a)) ∧
      ∀ g, rowKeys rows (.allow a g) → s.get (Usdc.allowSlot a g) = 0 :=
  checkUsdcHolder_soundW sound.word h

/-- **The two-token joint checkpoint checker**: `checkJoint` on side `.one`, `checkUsdc`, and the
Pair's USDC row checks. -/
def checkJoint2 (pair usdc weth : Adr) (urows : List (Usdc.Key × B256))
    (wrows : List (Weth9.Key × B256)) (prows : List PairRow) (base : UniswapV2Pair.State)
    (w : Jaune.State) : Bool :=
  checkJoint pair weth wrows prows base .one w && Usdc.checkUsdc usdc urows w &&
    decide (base.token0 = usdc) &&
    checkUsdcHolder urows (w.getStor usdc) pair base.reserve0.val && decide (pair ≠ usdc) &&
    decide (∀ f ∈ coveredForks, ¬ (Fork.ruleSet f).isPrecomp usdc) &&
    decide (∀ f ∈ coveredForks, ¬ (Fork.ruleSet f).isPrecomp pair)

/-- **Soundness of the two-token joint checkpoint checker.** -/
theorem checkJoint2_sound {pair usdc weth : Adr} {urows : List (Usdc.Key × B256)}
    {wrows : List (Weth9.Key × B256)} {prows : List PairRow} {base : UniswapV2Pair.State}
    {w : Jaune.State} (h : checkJoint2 pair usdc weth urows wrows prows base w = true) :
    JointCheckpoint2 pair usdc weth (rowKeys urows) (rowKeys wrows) (pairKeys prows)
      (rowsState base prows) w := by
  simp only [checkJoint2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hjoint, husdc⟩, htoken0⟩, hholder⟩, hapart⟩, hprecomp⟩, hpairPrecomp⟩ := h
  obtain ⟨installed, foot⟩ := Usdc.checkUsdc_sound husdc
  obtain ⟨tracked, notFrozen, reserve, noAllowance⟩ :=
    checkUsdcHolder_sound (checkUsdc_rows husdc) hholder
  exact
    { weth9 := checkJoint_sound hjoint
      usdcInstalled := installed
      usdcFoot := foot
      token0 := htoken0
      tracked := tracked
      notFrozen := notFrozen
      noAllowance := noAllowance
      reserve := reserve
      apart := hapart
      usdcNotPrecompile := fun s hfork => hprecomp s.fork hfork
      pairNotPrecompile := fun s hfork => hpairPrecomp s.fork hfork }

/-! ## C7 controls -/

/-- **C7 control (any world)**: a tracked nonzero USDC allowance row of the Pair is rejected. -/
theorem checkJoint2_allowance_control {pair usdc weth : Adr} {urows : List (Usdc.Key × B256)}
    {wrows : List (Weth9.Key × B256)} {prows : List PairRow} {base : UniswapV2Pair.State}
    {w : Jaune.State} {g : Adr} (row : rowKeys urows (.allow pair g))
    (granted : (w.getStor usdc).get (Usdc.allowSlot pair g) ≠ 0) :
    checkJoint2 pair usdc weth urows wrows prows base w = false := by
  cases h : checkJoint2 pair usdc weth urows wrows prows base w
  · rfl
  · exact absurd (checkJoint2_sound h) (JointCheckpoint2.allowance_control row granted)

/-- **C7 control (any world)**: a flagged Pair balance word is rejected. -/
theorem checkJoint2_frozen_control {pair usdc weth : Adr} {urows : List (Usdc.Key × B256)}
    {wrows : List (Weth9.Key × B256)} {prows : List PairRow} {base : UniswapV2Pair.State}
    {w : Jaune.State} (flag : Usdc.frozenBit ((w.getStor usdc).get (Usdc.balSlot pair)) = true) :
    checkJoint2 pair usdc weth urows wrows prows base w = false := by
  cases h : checkJoint2 pair usdc weth urows wrows prows base w
  · rfl
  · exact absurd (checkJoint2_sound h) (JointCheckpoint2.frozen_control flag)

/-! ## Non-vacuity: a synthetic two-token world the checker accepts, and the controls on it -/

/-- The Pair of the synthetic world `U0`. -/
def u0Pair : Adr := 0x5555555555555555555555555555555555555555

/-- WETH9's address in `U0`. -/
def u0Weth : Adr := 0x3333333333333333333333333333333333333333

/-- A spender the Pair has (zero) allowance rows for, in both tokens; also USDC's owner and admin
words. -/
def u0Spender : Adr := 0x7777777777777777777777777777777777777777

/-- The Pair's `factory` word. -/
def u0Factory : Adr := 0x4444444444444444444444444444444444444444

/-- The Pair's model state: unlocked, `token0 = USDC`, `token1 = WETH9`, both reserves `10^6`,
total supply `10^6` held at address `0`. -/
def u0Base : UniswapV2Pair.State where
  totalSupply := 1000000
  balanceOf := fun _ => 0
  allowance := fun _ _ => 0
  domainSeparator := 0
  nonces := fun _ => 0
  factory := u0Factory
  token0 := Usdc.usdcProxy
  token1 := u0Weth
  reserve0 := ⟨1000000, by decide⟩
  reserve1 := ⟨1000000, by decide⟩
  blockTimestampLast := 0
  price0CumulativeLast := 0
  price1CumulativeLast := 0
  kLast := 0
  unlocked := 1

/-- The Pair's tracked rows: the supply at address `0`. -/
def u0PairRows : List PairRow := [(.balance 0, mapSlot (0 : Adr).toB256 1, 1000000)]

/-- WETH9's tracked rows (ascending slot words): the Pair's allowance to the spender, the Pair's
balance. -/
def u0WethRows : List (Weth9.Key × B256) :=
  [(.allow u0Pair u0Spender, Weth9.allowSlot u0Pair u0Spender), (.bal u0Pair, Weth9.balSlot u0Pair)]

/-- USDC's tracked rows (ascending slot words): the Pair's balance, the Pair's allowance to the
spender. -/
def u0UsdcRows : List (Usdc.Key × B256) :=
  [(.bal u0Pair, Usdc.balSlot u0Pair), (.allow u0Pair u0Spender, Usdc.allowSlot u0Pair u0Spender)]

/-- The Pair's storage, representing `rowsState u0Base u0PairRows`. -/
def u0PairStor : Stor := Stor.ofList
  [(0, 1000000), (5, u0Factory.toB256), (6, Usdc.usdcProxy.toB256), (7, u0Weth.toB256),
    (8, Nat.toB256 (1000000 + 1000000 * 2 ^ 112)), (12, 1), (mapSlot (0 : Adr).toB256 1, 1000000)]

/-- WETH9's storage: the Pair's balance word (backed by WETH9's ether). -/
def u0WethStor : Stor := Stor.ofList [(Weth9.balSlot u0Pair, 1000000)]

/-- USDC's proxy storage: owner, `initialized`, version 3, the implementation and admin words, and
the Pair's unflagged balance word. -/
def u0UsdcStor : Stor := Stor.ofList
  [(0, u0Spender.toB256), (8, Nat.toB256 (2 ^ 160)), (18, 3), (Usdc.implSlot, Usdc.usdcImpl.toB256),
    (Usdc.adminSlot, u0Spender.toB256), (Usdc.balSlot u0Pair, 1000000)]

/-- **The synthetic world `U0`**, parametric in USDC's proxy storage: the Pair's runtime, WETH9's
runtime, and USDC's proxy, implementation and library runtimes. -/
def u0World (us : Stor) : Jaune.State :=
  (((((.empty : Jaune.State).insert u0Pair
      { nonce := 1, bal := 0, stor := u0PairStor, code := UniswapV2Pair.code }).insert u0Weth
      { nonce := 1, bal := 1000000, stor := u0WethStor, code := Weth9.code }).insert Usdc.usdcProxy
      { Acct.nil with stor := us, code := Usdc.Proxy.code }).insert Usdc.usdcImpl
      { Acct.nil with code := Usdc.Impl.code }).insert Usdc.usdcLib
      { Acct.nil with code := Usdc.Lib.code }

/-- **The checker accepts `U0`** (kernel evaluation). -/
theorem u0_accepts :
    checkJoint2 u0Pair Usdc.usdcProxy u0Weth u0UsdcRows u0WethRows u0PairRows u0Base
      (u0World u0UsdcStor) = true := by
  decide +kernel

/-- **`U0` satisfies the two-token joint checkpoint**: the predicate is satisfiable. -/
theorem u0_jointCheckpoint2 :
    JointCheckpoint2 u0Pair Usdc.usdcProxy u0Weth (rowKeys u0UsdcRows) (rowKeys u0WethRows)
      (pairKeys u0PairRows) (rowsState u0Base u0PairRows) (u0World u0UsdcStor) :=
  checkJoint2_sound u0_accepts

/-- **C7 control 1 (concrete)**: `U0` with the Pair's tracked USDC allowance to the spender set to
`7` is rejected (kernel evaluation). -/
theorem u0_allowance_rejected :
    checkJoint2 u0Pair Usdc.usdcProxy u0Weth u0UsdcRows u0WethRows u0PairRows u0Base
      (u0World (u0UsdcStor.set (Usdc.allowSlot u0Pair u0Spender) 7)) = false := by
  decide +kernel

/-- **C7 control 2 (concrete)**: `U0` with the Pair's USDC balance word flagged (bit 255 set, the
balance bits unchanged) is rejected (kernel evaluation). -/
theorem u0_frozen_rejected :
    checkJoint2 u0Pair Usdc.usdcProxy u0Weth u0UsdcRows u0WethRows u0PairRows u0Base
      (u0World (u0UsdcStor.set (Usdc.balSlot u0Pair) (Nat.toB256 (2 ^ 255 + 1000000)))) = false := by
  decide +kernel

end Blanc.Composition.UniswapV2PairUsdcWeth9
