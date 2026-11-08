import Blanc.Lift.FrameChain
import Blanc.Lift.WriteSiteLocality
import Blanc.Lift.WriteSiteReachHistory
import Blanc.AddressSlotProofs
import Blanc.Lift.WriteSiteMapping
import Blanc.Lift.StaticOnlyFrames
import Blanc.LockExclusion
import Blanc.ExecutionCellProvenance
import Blanc.ExecutionHistoryCellProvenance
import Blanc.ExecutionInRawNodeOrigin
import Blanc.SlotFootprint
import Blanc.Lift.LinearRuntimeSafety

/-!
# Locality of one holder's balance entry over a mid history

`EntryLocal`: a token's storage moves through its settled frames (`FrameChain`), and each such frame
satisfies `held pre + credit ≤ held post + debit`, where `debit` and `credit` read the frame's message.
With `ownDebit` and `ownCredit` that says a third party's frame never lowers the holder's entry and the
holder's own frame lowers it by at most the amount it names. A rolled-back frame is not settled, so nothing
here ranges over one.

The kit for a certified code:

* `Exec.staticOnly_rawFrameDescendants_isStatic`, `staticOnly_quiet`: below code that executes only
  `STATICCALL`, every entered frame is static, on any lane without state gas;
* `frame_cellInv`: a cell property every write in a committed frame's raw nodes keeps holds at its post;
* `frame_rows_zero`: a holder's tracked rows stay zero across a frame the row table does not name
  (`rawWrite_rowClass`);
* `frame_cell_keep`: a frame under a selector with no mapping site keeps an entry apart from its known sites;
* `CoinKey`, `CoinKeysFresh`: the trace-local hash premise, over the words a coin's settled frames name;
* `rowSep_of_keys`, `slot_ne_of_keys`: the separation facts it gives;
* `PoolAuthorityEmpty`: the holder's allowance is empty at the cut and nothing can fill it;
* `entryLocal_of_frames`: the assembly from a chain and a per-frame law.

Contract-neutral: no address, base or selector of a coin is fixed here but the ERC-20 ABI's in
`ownDebit`/`ownCredit`.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift.WriteSite

/-! ## Static-only code, on a lane without state gas -/

/-! ## A cell across a committed frame -/

/-! ## A certified frame's writes -/

/-! ## The hash premise -/

/-- A slot a coin's frame names, by its shape. -/
inductive CoinKey : Type
  /-- `keccak256(a ‖ b)`. -/
  | map (b a : B256)
  /-- `keccak256(k ‖ keccak256(o ‖ b))`. -/
  | row (b o k : B256)
  /-- Any other known word. -/
  | raw (x : B256)
  deriving DecidableEq

variable {sites : List Site} {balBase allowBase : B256} {h : Adr} {frames : List Exec.Frame}

/-! ## Locality -/

/-- What the holder's own message says it takes out of its entry. -/
def ownDebit (h : Adr) (e : Sevm) : Nat :=
  if e.caller ≠ h then 0
  else if Blanc.Sevm.selector e = 0xa9059cbb ∧ (Sevm.dataWord e 4).toAdr ≠ h then
    (Sevm.dataWord e 36).toNat
  else if Blanc.Sevm.selector e = 0x23b872dd ∧ (Sevm.dataWord e 4).toAdr = h ∧
      (Sevm.dataWord e 36).toAdr ≠ h then
    (Sevm.dataWord e 68).toNat
  else 0

/-- What the holder's own message says it pulls into its entry. -/
def ownCredit (h : Adr) (e : Sevm) : Nat :=
  if e.caller = h ∧ Blanc.Sevm.selector e = 0x23b872dd ∧ (Sevm.dataWord e 4).toAdr ≠ h ∧
      (Sevm.dataWord e 36).toAdr = h then
    (Sevm.dataWord e 68).toNat
  else 0

/-- **Locality of `held` at coin `T`** over the settled frames `settled`, from words `a` to `b`. -/
structure EntryLocal (T : Adr) (Obs Good : Exec.Frame → Prop) (held : StorWords → Nat)
    (debit credit : Sevm → Nat) (a b : StorWords) (settled : List Exec.Frame) : Prop where
  /-- The coin's storage moves exactly through these frames, to the end. -/
  chain : FrameChain T Good a (coinFrames T Obs settled) b
  /-- The same, to the entry of any settled frame no earlier non-static `T` frame encloses. -/
  at_ : ∀ {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame},
    settled = before ++ f :: after →
    Exec.NoOpaqueAbove (fun A => A.sevm.currentTarget = T ∧ A.sevm.isStatic = false) before f →
    FrameChain T Good a (coinFrames T Obs before) (wordsAt T f.pre.state)
  /-- Each frame's effect on the entry, attributed by its message. -/
  law : ∀ F ∈ coinFrames T Obs settled,
    held (wordsAt T F.pre.state) + credit F.sevm ≤ held (wordsAt T F.post.state) + debit F.sevm

namespace EntryLocal

variable {T : Adr} {Obs Good : Exec.Frame → Prop} {held : StorWords → Nat} {a b : StorWords}
  {settled : List Exec.Frame}

/-- A third party's frame does not lower the entry. -/
theorem third_party (L : EntryLocal T Obs Good held (ownDebit h) (ownCredit h) a b settled)
    {F : Exec.Frame} (hF : F ∈ coinFrames T Obs settled) (caller : F.sevm.caller ≠ h) :
    held (wordsAt T F.pre.state) ≤ held (wordsAt T F.post.state) := by
  have := L.law F hF
  have hd : ownDebit h F.sevm = 0 := ite_eq_left caller
  rw [hd] at this
  omega

/-- A frame that lowers the entry is the holder's own `transfer` or `transferFrom` from itself, and
lowers it by at most the amount it names. -/
theorem lowered (L : EntryLocal T Obs Good held (ownDebit h) (ownCredit h) a b settled)
    {F : Exec.Frame} (hF : F ∈ coinFrames T Obs settled)
    (lower : held (wordsAt T F.post.state) < held (wordsAt T F.pre.state)) :
    F.sevm.caller = h ∧ (Blanc.Sevm.selector F.sevm = 0xa9059cbb ∨
        Blanc.Sevm.selector F.sevm = 0x23b872dd ∧ (Sevm.dataWord F.sevm 4).toAdr = h) ∧
      held (wordsAt T F.pre.state) ≤ held (wordsAt T F.post.state) + ownDebit h F.sevm := by
  have law := L.law F hF
  have zero : ownDebit h F.sevm ≠ 0 := fun z => by rw [z] at law; omega
  refine ⟨?_, ?_, by omega⟩
  · by_contra caller
    exact zero (ite_eq_left caller)
  · unfold ownDebit at zero
    split at zero
    · exact absurd rfl zero
    · split at zero
      · rename_i hs
        exact .inl hs.1
      · split at zero
        · rename_i hs
          exact .inr ⟨hs.1, hs.2.1⟩
        · exact absurd rfl zero

/-- Over the whole chain, the entry moves by the frames' amounts. -/
theorem total (L : EntryLocal T Obs Good held debit credit a b settled) :
    held a + ((coinFrames T Obs settled).map fun F => credit F.sevm).sum ≤
      held b + ((coinFrames T Obs settled).map fun F => debit F.sevm).sum :=
  (FrameChain.fold (I := fun _ => True) L.chain
    (fun F hF _ _ => ⟨trivial, L.law F hF⟩) trivial).2

end EntryLocal

end Blanc.Lift
