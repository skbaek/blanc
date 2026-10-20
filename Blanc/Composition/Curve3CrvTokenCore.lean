import Blanc.Lift.Token.Supply
import Blanc.Lift.Curve3Crv.CommittedHistory
import Blanc.Curve3Crv.Properties

/-!
# 3Crv as a token book with a minter/supply facet (U8b)

`c3crvBook` reads the existing pure 3Crv model (`Curve3Crv.State`, `Curve3Crv.step`) through the
deployed dispatcher's own decoder (`decodeCall`) and the canonical owner word (`ownerWordOf`), exactly
as the committed replay does (`ModelStep`, `committedFrameInvocations`): a writer message steps the
model (and is rejected when the model rejects it); any other message leaves the ledger alone (a view
keeps the state, `body_view`).  A ledger is good while it is conserved.

`c3crvSupply` is its `SupplyFacet`: supply is `totalSupply`, the minter is `minter`, a mint or burn
is a decoded `mint`/`burnFrom` (zero amounts included), and the laws are the model's minter rules
(`mint_eq_ok`, `burnFrom_eq_ok`, `supply_change_by_minter`, `minter_change_by_minter`).

`c3crvBook_run_eq` identifies the book's run over the committed writer invocations' messages with
the model fold `runInvocations` of `c3crv_history_committed_derived`.

The U8 control (`control_mutant_no_supplyFacet`): a mutated book whose `mint` skips the caller check
admits no supply facet with 3Crv's own minter and mint classification; one non-minter mint is the
kernel counter-run.
-/

namespace Blanc.Composition.Curve3CrvToken

open Jaune Blanc Blanc.Lift Blanc.Lift.Token Blanc.Lift.Curve3Crv
open Blanc.Curve3Crv (Call)

/-! ## The book -/

/-- One message's effect on the 3Crv ledger: a writer steps the model with the frame's caller, value
and canonical owner word; any other message leaves the ledger alone. -/
def c3crvStep (l : Blanc.Curve3Crv.State) (e : Sevm) : Option Blanc.Curve3Crv.State :=
  if IsWriter (decodeCall e) then
    match Blanc.Curve3Crv.step (c3ctx e (ownerWordOf e)) (decodeCall e) l with
    | .ok o => some o.1
    | .error _ => none
  else some l

/-- What a 3Crv entry frame asks, as far as the token core speaks of it. -/
def c3crvOp (e : Sevm) : Op :=
  match decodeCall e with
  | .balanceOf h => .balanceOf h.toAdr
  | .transfer d v => .transfer d.toAdr v.toNat
  | .transferFrom s d v => .transferFrom s.toAdr d.toAdr v.toNat
  | .approve p v => .approve p.toAdr v.toNat
  | _ => .other

/-- **The 3Crv book**: the existing pure model, read as natural numbers; a ledger is good while its
supply is the sum of its balances. -/
def c3crvBook : Book where
  Ledger := Blanc.Curve3Crv.State
  step := c3crvStep
  op := c3crvOp
  bal l a := (l.balanceOf a).toNat
  allow l o p := (l.allowances o p).toNat
  Good := Blanc.Curve3Crv.Conserved

theorem c3crvStep_writer {l l' : Blanc.Curve3Crv.State} {a : Sevm}
    (hw : IsWriter (decodeCall a)) (h : c3crvStep l a = some l') :
    ∃ o, Blanc.Curve3Crv.step (c3ctx a (ownerWordOf a)) (decodeCall a) l = .ok o ∧ l' = o.1 := by
  unfold c3crvStep at h
  rw [if_pos hw] at h
  cases hs : Blanc.Curve3Crv.step (c3ctx a (ownerWordOf a)) (decodeCall a) l with
  | ok o =>
    rw [hs] at h
    exact ⟨o, rfl, (Option.some.inj h).symm⟩
  | error e =>
    rw [hs] at h
    cases h

theorem c3crvStep_nonwriter {l l' : Blanc.Curve3Crv.State} {a : Sevm}
    (hw : ¬ IsWriter (decodeCall a)) (h : c3crvStep l a = some l') : l' = l := by
  unfold c3crvStep at h
  rw [if_neg hw] at h
  exact (Option.some.inj h).symm

/-- A writer step the model accepts is a book step. -/
theorem c3crvStep_of_ok {l : Blanc.Curve3Crv.State} {a : Sevm} {o : Blanc.Curve3Crv.Out}
    (hw : IsWriter (decodeCall a))
    (h : Blanc.Curve3Crv.step (c3ctx a (ownerWordOf a)) (decodeCall a) l = .ok o) :
    c3crvStep l a = some o.1 := by
  unfold c3crvStep
  rw [if_pos hw, h]

/-! ## The book's run is the committed model fold -/

/-- The messages of a list of invocations. -/
def invMessages (invs : List WriterInvocation) : List Sevm := invs.map (·.sevm)

/-- **The book's run over the committed writer invocations is the model fold** whenever each
invocation records its message's canonical owner word and runs a writer selector (as every committed
invocation does, `mem_committedInvocations`). -/
theorem c3crvBook_run_eq :
    ∀ (l : Blanc.Curve3Crv.State) (invs : List WriterInvocation),
      (∀ inv ∈ invs, inv.ownerWord = ownerWordOf inv.sevm ∧ IsWriter (decodeCall inv.sevm)) →
      c3crvBook.run l (invMessages invs) = runInvocations l invs
  | l, [], _ => rfl
  | l, inv :: rest, h => by
    obtain ⟨hown, hw⟩ := h inv List.mem_cons_self
    change (c3crvStep l inv.sevm).bind (fun l' => c3crvBook.run l' (invMessages rest)) =
      (match Blanc.Curve3Crv.step (c3ctx inv.sevm inv.ownerWord) (decodeCall inv.sevm) l with
        | .ok o => runInvocations o.1 rest
        | .error _ => none)
    unfold c3crvStep
    rw [if_pos hw, hown]
    cases Blanc.Curve3Crv.step (c3ctx inv.sevm (ownerWordOf inv.sevm)) (decodeCall inv.sevm) l with
    | ok o =>
      exact c3crvBook_run_eq o.1 rest fun i hi => h i (List.mem_cons_of_mem inv hi)
    | error e => rfl

/-- Every committed invocation of a history records its canonical owner word and runs a writer. -/
theorem committedInvocations_canonical {cfg : ChainConfig} {checkpoint future : BlockChain}
    {ca : Adr} (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ inv ∈ committedInvocations ca trace,
      inv.ownerWord = ownerWordOf inv.sevm ∧ IsWriter (decodeCall inv.sevm) := by
  intro inv member
  obtain ⟨frame, -, -, -, writer, rfl⟩ := mem_committedInvocations member
  exact ⟨rfl, writer⟩

/-! ## The minter/supply facet -/

/-- A decoded `mint`'s recipient and amount. -/
def callMint : Call → Option (Adr × Nat)
  | .mint d v => some (d.toAdr, v.toNat)
  | _ => none

/-- A decoded `burnFrom`'s source and amount. -/
def callBurn : Call → Option (Adr × Nat)
  | .burnFrom f v => some (f.toAdr, v.toNat)
  | _ => none

/-- The mint a 3Crv message asks for. -/
def c3crvMintOf (e : Sevm) : Option (Adr × Nat) := callMint (decodeCall e)

/-- The burn a 3Crv message asks for. -/
def c3crvBurnOf (e : Sevm) : Option (Adr × Nat) := callBurn (decodeCall e)

theorem callMint_eq {c : Call} {d : Adr} {v : Nat} (h : callMint c = some (d, v)) :
    ∃ d₀ v₀ : B256, c = .mint d₀ v₀ ∧ d = d₀.toAdr ∧ v = v₀.toNat := by
  cases c <;> simp only [callMint, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem callBurn_eq {c : Call} {d : Adr} {v : Nat} (h : callBurn c = some (d, v)) :
    ∃ d₀ v₀ : B256, c = .burnFrom d₀ v₀ ∧ d = d₀.toAdr ∧ v = v₀.toNat := by
  cases c <;> simp only [callBurn, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem c3crv_mint_step {l l' : Blanc.Curve3Crv.State} {a : Sevm} {d : Adr} {v : Nat}
    (h : c3crvStep l a = some l') (hm : c3crvMintOf a = some (d, v)) :
    a.caller = l.minter ∧ l'.totalSupply.toNat = l.totalSupply.toNat + v ∧ l'.minter = l.minter := by
  obtain ⟨d₀, v₀, hc, -, rfl⟩ := callMint_eq hm
  obtain ⟨o, ho, rfl⟩ := c3crvStep_writer (by rw [hc]; trivial) h
  rw [hc] at ho
  obtain ⟨-, ho⟩ := Blanc.Curve3Crv.step_eq_ok.mp ho
  obtain ⟨-, hs, -, hnof, -, rfl⟩ := Blanc.Curve3Crv.mint_eq_ok.mp ho
  exact ⟨hs, B256.toNat_add_eq_of_nof _ _ hnof, rfl⟩

theorem c3crv_burn_step {l l' : Blanc.Curve3Crv.State} {a : Sevm} {d : Adr} {v : Nat}
    (h : c3crvStep l a = some l') (hb : c3crvBurnOf a = some (d, v)) :
    a.caller = l.minter ∧ l'.totalSupply.toNat + v = l.totalSupply.toNat ∧
      l'.minter = l.minter := by
  obtain ⟨d₀, v₀, hc, -, rfl⟩ := callBurn_eq hb
  obtain ⟨o, ho, rfl⟩ := c3crvStep_writer (by rw [hc]; trivial) h
  rw [hc] at ho
  obtain ⟨-, ho⟩ := Blanc.Curve3Crv.step_eq_ok.mp ho
  obtain ⟨-, hs, -, hle, -, rfl⟩ := Blanc.Curve3Crv.burnFrom_eq_ok.mp ho
  have hle' : v₀.toNat ≤ l.totalSupply.toNat := B256.toNat_le_toNat hle
  refine ⟨hs, ?_, rfl⟩
  change (l.totalSupply - v₀).toNat + v₀.toNat = l.totalSupply.toNat
  rw [B256.toNat_sub_eq_of_le _ _ hle]
  omega

theorem c3crv_other_step {l l' : Blanc.Curve3Crv.State} {a : Sevm}
    (h : c3crvStep l a = some l') (hm : c3crvMintOf a = none) (hb : c3crvBurnOf a = none) :
    l'.totalSupply.toNat = l.totalSupply.toNat := by
  by_cases hw : IsWriter (decodeCall a)
  · obtain ⟨o, ho, rfl⟩ := c3crvStep_writer hw h
    have same : o.1.totalSupply = l.totalSupply := by
      apply Classical.byContradiction
      intro hne
      obtain ⟨-, d, v, hc | hc⟩ := Blanc.Curve3Crv.supply_change_by_minter ho hne
      · unfold c3crvMintOf at hm
        rw [hc] at hm
        cases hm
      · unfold c3crvBurnOf at hb
        rw [hc] at hb
        cases hb
    rw [same]
  · rw [c3crvStep_nonwriter hw h]

theorem c3crv_minter_step {l l' : Blanc.Curve3Crv.State} {a : Sevm}
    (h : c3crvStep l a = some l') (hne : l'.minter ≠ l.minter) : a.caller = l.minter := by
  by_cases hw : IsWriter (decodeCall a)
  · obtain ⟨o, ho, rfl⟩ := c3crvStep_writer hw h
    exact Blanc.Curve3Crv.minter_change_by_minter ho hne
  · rw [c3crvStep_nonwriter hw h] at hne
    exact absurd rfl hne

/-- **3Crv's minter/supply facet**: supply `totalSupply`, minter `minter`, decoded `mint`/`burnFrom`
messages (zero amounts included), with the model's minter rules as laws. -/
def c3crvSupply : SupplyFacet c3crvBook where
  supply l := l.totalSupply.toNat
  minter l := l.minter
  mintOf := c3crvMintOf
  burnOf := c3crvBurnOf
  mint_step h hm := c3crv_mint_step h hm
  burn_step h hb := c3crv_burn_step h hb
  other_step h hm hb := c3crv_other_step h hm hb
  minter_step h hne := c3crv_minter_step h hne

/-- Every message but `setMinter` keeps 3Crv's minter. -/
theorem c3crv_keepsMinter {a : Sevm} (h : ∀ m, decodeCall a ≠ .setMinter m) :
    c3crvSupply.KeepsMinter a := by
  intro l l' hs
  change l'.minter = l.minter
  by_cases hw : IsWriter (decodeCall a)
  · obtain ⟨o, ho, rfl⟩ := c3crvStep_writer hw hs
    obtain ⟨-, ho⟩ := Blanc.Curve3Crv.step_eq_ok.mp ho
    revert h ho hw
    generalize decodeCall a = c
    intro h hw ho
    cases c with
    | setMinter m => exact absurd rfl (h m)
    | setName n y => obtain ⟨-, -, -, rfl⟩ := Blanc.Curve3Crv.setName_eq_ok.mp ho; rfl
    | transfer d v => obtain ⟨-, -, -, rfl⟩ := Blanc.Curve3Crv.transfer_eq_ok.mp ho; rfl
    | transferFrom f d v =>
      obtain ⟨-, -, -, -, -, rfl⟩ := Blanc.Curve3Crv.transferFrom_eq_ok.mp ho; rfl
    | approve p v => obtain ⟨-, -, rfl⟩ := Blanc.Curve3Crv.approve_eq_ok.mp ho; rfl
    | mint d v => obtain ⟨-, -, -, -, -, rfl⟩ := Blanc.Curve3Crv.mint_eq_ok.mp ho; rfl
    | burnFrom f v => obtain ⟨-, -, -, -, -, rfl⟩ := Blanc.Curve3Crv.burnFrom_eq_ok.mp ho; rfl
    | totalSupply | allowance _ _ | name | symbol | decimals | balanceOf _ | other =>
      simp only [IsWriter] at hw
  · rw [c3crvStep_nonwriter hw hs]

/-! ## The 3Crv side of the supply identity over a history -/

/-- **3Crv's supply over a configured history.**  From `c3crv_history_committed_derived`'s premises,
if every committed writer invocation the initial minter sends keeps the minter, then the minter
persists and the final supply plus the committed burns equals the initial supply plus the committed
mints (zero amounts included), where the final state is the model fold over exactly the committed
invocations and abstracts the future storage. -/
theorem c3crv_history_supply {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace))
    (keeps : ∀ inv ∈ committedInvocations ca trace, inv.sevm.caller = initial.minter →
      c3crvSupply.KeepsMinter inv.sevm) :
    ∃ s, runInvocations initial (committedInvocations ca trace) = some s ∧
      VyInv (future.state.getStor ca) s
        (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) ∧
      s.minter = initial.minter ∧
      s.totalSupply.toNat + c3crvSupply.burned (invMessages (committedInvocations ca trace)) =
        initial.totalSupply.toNat + c3crvSupply.minted (invMessages (committedInvocations ca trace)) := by
  obtain ⟨-, s, -, fold, final, -⟩ :=
    c3crv_history_committed_derived trace installed invariant fresh
  have book : c3crvBook.run initial (invMessages (committedInvocations ca trace)) = some s := by
    rw [c3crvBook_run_eq _ _ (committedInvocations_canonical trace)]
    exact fold
  obtain ⟨hminter, hsupply⟩ := c3crvSupply.run_supply book fun a member hcaller => by
    obtain ⟨inv, hinv, rfl⟩ := List.mem_map.mp member
    exact keeps inv hinv hcaller
  exact ⟨s, fold, final, hminter, hsupply⟩

/-! ## The U8 control -/

/-- The control's mutation: `mint` without the caller check. -/
def mutantMint (d v : B256) (s : Blanc.Curve3Crv.State) : Option Blanc.Curve3Crv.State :=
  if d.toNat < 2 ^ 160 ∧ d ≠ 0 ∧ s.totalSupply.toNat + v.toNat < 2 ^ 256 ∧
      (s.balanceOf d.toAdr).toNat + v.toNat < 2 ^ 256 then
    some { s with totalSupply := s.totalSupply + v,
                  balanceOf := ledgerCredit s.balanceOf d.toAdr v }
  else none

/-- The mutated book: 3Crv's book whose non-payable `mint` skips the caller check. -/
def mutantStep (l : Blanc.Curve3Crv.State) (e : Sevm) : Option Blanc.Curve3Crv.State :=
  match decodeCall e with
  | .mint d v => if e.value = 0 then mutantMint d v l else none
  | _ => c3crvStep l e

def mutantBook : Book where
  Ledger := Blanc.Curve3Crv.State
  step := mutantStep
  op := c3crvOp
  bal l a := (l.balanceOf a).toNat
  allow l o p := (l.allowances o p).toNat
  Good := Blanc.Curve3Crv.Conserved

/-- The control's ledger: empty, with minter `1`. -/
def mutantLedger : Blanc.Curve3Crv.State :=
  ⟨[], [], 0, fun _ => 0, fun _ _ => 0, 0, 1⟩

/-- The control's message: `mint(1, 1)` sent by address `0` (not the minter). -/
def mutantWitness : Sevm :=
  { (default : Sevm) with
    data := [0x40, 0xc1, 0x0f, 0x19] ++ List.replicate 31 0 ++ [1] ++ List.replicate 31 0 ++ [1] }

theorem mutantWitness_decode : decodeCall mutantWitness = .mint 1 1 := by
  have hlen : ¬ mutantWitness.data.length < 4 := by decide
  have hsel : Sevm.selector mutantWitness = selMint := by decide +kernel
  have ha0 : Sevm.argWord mutantWitness 0 = 1 := by decide +kernel
  have ha1 : Sevm.argWord mutantWitness 1 = 1 := by decide +kernel
  unfold decodeCall
  rw [if_neg hlen]
  simp only [hsel, ha0, ha1]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos trivial]

/-- The mutated book accepts the non-minter `mint(1, 1)`. -/
theorem mutant_accepts : ∃ l', mutantBook.step mutantLedger mutantWitness = some l' := by
  rw [show mutantBook.step = mutantStep from rfl]
  unfold mutantStep
  rw [mutantWitness_decode]
  dsimp only
  rw [if_pos (show mutantWitness.value = 0 from rfl)]
  unfold mutantMint
  rw [if_pos (by decide +kernel)]
  exact ⟨_, rfl⟩

/-- **U8 control.**  A book whose `mint` skips the caller check has no minter/supply facet that reads
3Crv's minter and classifies 3Crv's mints: the non-minter `mint(1, 1)` from address `0` is accepted
(one step), so `mint_step` would make `0` the minter `1`.  (A facet with free projections exists
trivially — constant supply, no mints — so the projections are fixed to 3Crv's.) -/
theorem control_mutant_no_supplyFacet :
    ¬ ∃ F : SupplyFacet mutantBook, F.minter = (·.minter) ∧ F.mintOf = c3crvMintOf := by
  rintro ⟨F, hminter, hmint⟩
  obtain ⟨l', hstep⟩ := mutant_accepts
  have hm : F.mintOf mutantWitness = some ((1 : B256).toAdr, (1 : B256).toNat) := by
    rw [hmint]
    unfold c3crvMintOf
    rw [mutantWitness_decode]
    rfl
  have hcaller := (F.mint_step hstep hm).1
  rw [hminter] at hcaller
  exact absurd hcaller (by decide)

end Blanc.Composition.Curve3CrvToken
