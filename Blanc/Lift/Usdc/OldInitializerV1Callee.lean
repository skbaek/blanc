import Blanc.Lift.Usdc.OldInitializerV1Staging
import Blanc.Lift.Usdc.OldInitializerV1Payload
import Blanc.Lift.SolcStorageReturn

/-!
# Actual V1 `initialize` callee `t_16b0_c16`: same-run write classification

Source-bound leaf over `Blanc.Lift.SolcStoragePayload`,
`Blanc.Lift.SolcStorageClear` and `Blanc.Lift.SolcStorageReturn`. The actual
callee (table entry `16`, entered from the wrapper's `callNext 16`) checks the
initialized byte of slot `8` (revert arm), checks four addresses nonzero
(`chk`), stores the three decoded strings through helper `46` at slots
`4`/`5`/`7` (`callFrag`), then packs decimals/master minter/pauser/blacklister
into slots `6`/`8`/`1`/`2` (`setFrag`), the owner into slot `0` (helper `47`)
and the initialized flag into slot `8` (`t_18e8_c16`). The code shapes are
`rfl` equations against the `Cert` trees.

Helper `46` is solc's `string storage = string memory`: a header store at
`slot`, then either the short tail or the payload loop at entry `52` over
`keccak(slot) + i`, and in both cases the shared tail `7` that clears the old
payload through helper `42` (entries `50`/`51`). `helper46_obs` classifies its
stores; `helper46_returned` gives its returned stack and memory, which the
callee needs to stage the next string. `callee_obs` is the callee result. No
fork, gas, hash, zero, length-range or calldata premise; the memory premises
are the staged headers and bounds `Staged3` supplies.
-/

namespace Blanc.Lift.Usdc.OldInitializerV1Callee

open Jaune Blanc Blanc.Lift
open SolcStringAllocation SolcAbiStringStaging OldInitializerV1Staging
open ImplV1 SolcStorageReturn

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- Fixed storage slots the actual V1 initializer writes directly. -/
def fixedSlots : List B256 := [0, 1, 2, 4, 5, 6, 7, 8]

/-- `(slot, head)` of the three actual decoded strings: name, symbol, currency. -/
def stringSlots : List (B256 × B256) := [(4, head1), (5, head2), (7, head3)]

/-- A bounded modular payload key of the actual long decoded string stored at
`slot` from the ABI head `head`. -/
def PayloadKey (sevm : Sevm) (key : B256) : Prop :=
  ∃ slot head, (slot, head) ∈ stringSlots ∧ 31 < (lenAt sevm head).toNat ∧
    ∃ i : Nat, i < ((lenAt sevm head).toNat + 31) / 32 ∧
      key = slot.toBytes.keccak + i.toB256

/-- The actual V1 initializer writes a fixed slot, literal zero, or an indexed
word of an actual long decoded string. Payload-key addition is modular. -/
def V1InitializerWriteClass (sevm : Sevm) (pre : Devm) (n : Ninst) : Prop :=
  n = .reg .sstore → ∀ key value rest,
    pre.stack = key :: value :: rest →
    key ∈ fixedSlots ∨ value = 0 ∨ PayloadKey sevm key

/-- The observed step relation: same `P`, classified stores, no external
instruction. -/
def Obs (P : Sevm → Devm → Ninst → Devm → Prop) (sevm : Sevm) :
    Sevm → Devm → Ninst → Devm → Prop :=
  fun s d n d' => P s d n d' ∧ V1InitializerWriteClass sevm d n ∧ ∀ x, n ≠ .exec x

theorem silentClass {n : Ninst} {d : Devm} (h : n.stateSilent = true) :
    V1InitializerWriteClass sevm d n := by
  intro hn; subst hn; cases h

theorem silentNoExec {n : Ninst} (h : n.stateSilent = true) : ∀ x, n ≠ .exec x := by
  intro x hn; subst hn; cases h

set_option hygiene false in
/-- One state-silent observed step: invert with `t` and rebuild. -/
local macro "qs " t:term : tactic => `(tactic| (
  have step := rpw_next run
  clear run
  obtain ⟨_, w, run⟩ := step
  refine .next ⟨w, silentClass rfl, silentNoExec rfl⟩ ?_
  obtain ⟨_, rfl⟩ := $t (erase w.1)
  clear w
  try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at run ⊢))

set_option hygiene false in
/-- An observed `SLOAD` step. -/
local macro "qsload" : tactic => `(tactic| (
  have step := rpw_next run
  clear run
  obtain ⟨_, w, run⟩ := step
  refine .next ⟨w, silentClass rfl, silentNoExec rfl⟩ ?_
  obtain ⟨_, _, _, rfl⟩ := ri_sload_any (erase w.1)
  clear w))

variable {P : Sevm → Devm → Ninst → Devm → Prop}

/-- The inline clearing head of helper `42` is the legacy template over
entries `50`/`51`. -/
theorem t_2f10_c42_shape : ImplV1.t_2f10_c42 =
    SolcStorageClear.legacyHead [0x2f, 0x10] [0x2f, 0x28] (by decide) (by decide) 50 51 := rfl

/-- Helper `42` returns the clearing end word over the caller's tail. -/
theorem helper42_returned
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {cur e r : B256} {rest : List B256} {D : Devm}
    (run : SFunc.RunP P ImplV1.cert.prog sevm (St b (cur :: e :: r :: rest) M G)
      ImplV1.t_2f0a_c42 (.returned D)) :
    ∃ b' G', D = St b' (e :: rest) M G' := by
  unfold ImplV1.t_2f0a_c42 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push (erase w)
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl (erase w)
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl (erase w)
  rw [t_2f10_c42_shape] at run
  exact legacyRunP_returned erase OldInitializerV1Payload.entry50
    OldInitializerV1Payload.retEntry51 (by decide) run

/-- The shared exit tail `7` (drop three words, clear through helper `42`,
return) returns the slot word over the caller's tail. -/
theorem tail7_returned
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {x y z e slot r : B256} {rest : List B256} {D : Devm}
    (run : SFunc.RunP P ImplV1.cert.prog sevm
      (St b (x :: y :: z :: e :: slot :: r :: rest) M G) ImplV1.t_2ef9_c7 (.returned D)) :
    ∃ b' G', D = St b' (slot :: rest) M G' := by
  unfold ImplV1.t_2ef9_c7 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop (erase w)
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl (erase w)
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop (erase w)
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push (erase w)
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl (erase w)
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl (erase w)
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_push (erase w)
  dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at run
  obtain ⟨G', D', callee, run⟩ := rpw_callRet (show ImplV1.cert.prog[42]? = some ImplV1.t_2f0a_c42 from rfl) run
  obtain ⟨_, _, rfl⟩ := helper42_returned erase callee
  unfold ImplV1.t_2f06_c7 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop (erase w)
  obtain ⟨_, w, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl (erase w)
  dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at run
  exact ⟨_, _, (rpw_ret run).choose_spec⟩

/-- Same `P`, literal-zero stores, no external instruction. -/
def ZeroObs (P : Sevm → Devm → Ninst → Devm → Prop) : Sevm → Devm → Ninst → Devm → Prop :=
  fun s d n d' => P s d n d' ∧
    (n = .reg .sstore → ∀ key value rest, d.stack = key :: value :: rest → value = 0) ∧
    ∀ x, n ≠ .exec x

/-- The shared exit tail `7` stores only literal zeros (through helper `42`)
and executes no external instruction. -/
theorem tail7_zero
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {d : Devm} {o : Outcome}
    (run : SFunc.RunP P ImplV1.cert.prog sevm d ImplV1.t_2ef9_c7 o) :
    SFunc.RunP (ZeroObs P) ImplV1.cert.prog sevm d ImplV1.t_2ef9_c7 o := by
  unfold ImplV1.t_2ef9_c7 at run ⊢
  cases run with
  | dest burn run =>
    refine .dest burn ?_
    iterate 7
      obtain ⟨next, step, run⟩ := rpw_next run
      refine .next ⟨step, (by intro impossible; cases impossible),
        (by intro x impossible; cases impossible)⟩ ?_
    cases run with
    | callHalt dest lookup pop callee =>
      rw [show ImplV1.cert.prog[42]? = some ImplV1.t_2f0a_c42 from rfl] at lookup
      cases lookup
      exact .callHalt dest rfl pop (OldInitializerV1Payload.helper42_zeroStores erase callee)
    | callRet dest lookup pop callee rest =>
      rw [show ImplV1.cert.prog[42]? = some ImplV1.t_2f0a_c42 from rfl] at lookup
      cases lookup
      refine .callRet dest rfl pop (OldInitializerV1Payload.helper42_zeroStores erase callee) ?_
      unfold ImplV1.t_2f06_c7 at rest ⊢
      cases rest with
      | dest burn rest =>
        refine .dest burn ?_
        iterate 2
          obtain ⟨next, step, rest⟩ := rpw_next rest
          refine .next ⟨step, (by intro impossible; cases impossible),
            (by intro x impossible; cases impossible)⟩ ?_
        cases rest with
        | ret dest pop => exact .ret dest pop

/-- A cut run of the payload exit `t_2ef8_c52` never stops at the loop head. -/
theorem tail8_done {d : Devm} {sg : Seg}
    (run : SFunc.RunCutP P ImplV1.cert.prog sevm [52] d ImplV1.t_2ef8_c52 sg) :
    ∃ o, sg = .done o := by
  unfold ImplV1.t_2ef8_c52 ImplV1.t_2ef9_c7 at run
  cases run with
  | dest burn run =>
    cases run with
    | dest burn2 run =>
      iterate 7
        obtain ⟨next, step, run⟩ := ric_nextP run
      cases run with
      | callHalt => exact ⟨_, rfl⟩
      | callRet dest lookup pop callee rest =>
        unfold ImplV1.t_2f06_c7 at rest
        cases rest with
        | dest burn rest =>
          iterate 2
            obtain ⟨next, step, rest⟩ := ric_nextP rest
          cases rest with
          | ret => exact ⟨_, rfl⟩

set_option hygiene false in
/-- One plain run step inverted with `t`. -/
local macro "ps " t:term : tactic => `(tactic| (
  have step := rpw_next run
  clear run
  obtain ⟨_, w, run⟩ := step
  obtain ⟨_, rfl⟩ := $t (erase w)
  clear w
  try dsimp only [List.set, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at run))

/-- The inline first payload head of helper `46` is the loop template at
entry `52`. -/
theorem t_2edd_c46_shape : ImplV1.t_2edd_c46 =
    SolcStoragePayload.head OldInitializerV1Payload.back52 OldInitializerV1Payload.exit52
      (by decide) (by decide) OldInitializerV1Payload.k52 ImplV1.t_2ef8_c52 := rfl

/-- Helper `46` (solc `string storage = string memory`), called with
`L :: D :: slot :: r :: rest`, returns `slot :: rest`; its memory keeps every
byte of the entry memory after the scratch write of `slot` at `0`. -/
theorem helper46_returned
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {L D slot r : B256} {rest : List B256} {Dr : Devm}
    (run : SFunc.RunP P ImplV1.cert.prog sevm (St b (L :: D :: slot :: r :: rest) M G)
      ImplV1.t_2e8a_c46 (.returned Dr)) :
    ∃ b' M' G', Dr = St b' (slot :: rest) M' G' ∧ Keeps (M.write 0 slot.toBytes) M' := by
  unfold ImplV1.t_2e8a_c46 at run
  obtain ⟨_, run⟩ := rpw_dest run
  ps ri_dup rfl
  ps ri_dup rfl
  have step := rpw_next run
  clear run
  obtain ⟨_, w, run⟩ := step
  obtain ⟨_, _, _, rfl⟩ := ri_sload_any (erase w)
  clear w
  ps ri_push
  ps ri_dup rfl
  ps ri_push
  ps ri_and
  ps ri_iszero
  ps ri_push
  ps ri_mul
  ps ri_sub
  ps ri_and
  ps ri_push
  ps ri_swap rfl
  ps ri_div
  ps ri_swap rfl
  ps ri_push
  ps ri_mstore
  ps ri_push
  ps ri_push
  ps ri_keccak
  ps ri_swap rfl
  ps ri_push
  ps ri_add
  ps ri_push
  ps ri_swap rfl
  ps ri_div
  ps ri_dup rfl
  ps ri_add
  ps ri_swap rfl
  ps ri_dup rfl
  ps ri_push
  ps ri_lt
  ps ri_push
  have k0 : Keeps (M.write 0 slot.toBytes)
      ((M.write (Bytes.toB256 [0]).toNat slot.toBytes).read (Bytes.toB256 [0]).toNat
        (Bytes.toB256 [32]).toNat).2 := Keeps.read _ _ _
  generalize ((M.write (Bytes.toB256 [0]).toNat slot.toBytes).read (Bytes.toB256 [0]).toNat
    (Bytes.toB256 [32]).toNat).2 = M1 at run k0
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · -- short string: header store, then the shared tail
    unfold ImplV1.t_2ebb_c46 at run
    ps ri_dup rfl
    ps ri_mload
    ps ri_push
    ps ri_not
    ps ri_and
    ps ri_dup rfl
    ps ri_dup rfl
    ps ri_add
    ps ri_or
    ps ri_dup rfl
    have step := rpw_next run
    clear run
    obtain ⟨_, w, run⟩ := step
    obtain ⟨_, _, rfl⟩ := ri_sstore_any (erase w)
    clear w
    ps ri_push
    obtain ⟨_, _, get, run⟩ := rpw_jump run
    cases Option.some.inj (get.symm.trans (show ImplV1.cert.prog[7]? = some ImplV1.t_2ef9_c7 from rfl))
    obtain ⟨_, _, rfl⟩ := tail7_returned erase run
    exact ⟨_, _, _, rfl, k0.trans (Keeps.read _ _ _)⟩
  · -- long string: header store, payload loop, shared tail
    unfold ImplV1.t_2ecb_c46 at run
    obtain ⟨_, run⟩ := rpw_dest run
    ps ri_dup rfl
    ps ri_dup rfl
    ps ri_add
    ps ri_push
    ps ri_add
    ps ri_dup rfl
    have step := rpw_next run
    clear run
    obtain ⟨_, w, run⟩ := step
    obtain ⟨_, _, rfl⟩ := ri_sstore_any (erase w)
    clear w
    ps ri_dup rfl
    ps ri_iszero
    ps ri_push
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨-, _, _, get, run⟩
    · unfold ImplV1.t_2eda_c46 at run
      ps ri_swap rfl
      ps ri_dup rfl
      ps ri_add
      rw [t_2edd_c46_shape] at run
      obtain ⟨_, _, _, _, M2, _, k2, run⟩ :=
        payload_exit erase OldInitializerV1Payload.entry52 tail8_done run
      unfold ImplV1.t_2ef8_c52 at run
      obtain ⟨_, run⟩ := rpw_dest run
      obtain ⟨_, _, rfl⟩ := tail7_returned erase run
      exact ⟨_, _, _, rfl, k0.trans k2⟩
    · cases Option.some.inj (get.symm.trans (show ImplV1.cert.prog[7]? = some ImplV1.t_2ef9_c7 from rfl))
      obtain ⟨_, _, rfl⟩ := tail7_returned erase run
      exact ⟨_, _, _, rfl, k0⟩

/-- A classified store on an exact stack. -/
theorem storeClass {key v : B256} {rest : List B256}
    (h : key ∈ fixedSlots ∨ v = 0 ∨ PayloadKey sevm key) :
    V1InitializerWriteClass sevm (St b (key :: v :: rest) M G) (.reg .sstore) := by
  intro _ key' v' rest' hs
  simp only [St.stack, List.cons.injEq] at hs
  obtain ⟨rfl, rfl, -⟩ := hs
  exact h

theorem slot_fixed {slot head : B256} (h : (slot, head) ∈ stringSlots) : slot ∈ fixedSlots := by
  simp only [stringSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

theorem zeroObs_obs {Q : Sevm → Devm → Ninst → Devm → Prop} {s d n d'}
    (h : ZeroObs Q s d n d') : Obs Q sevm s d n d' :=
  ⟨h.1, fun hn key value rest hs => Or.inr (Or.inl (h.2.1 hn key value rest hs)), h.2.2⟩

set_option hygiene false in
/-- One observed `SSTORE` step whose class is proved by `t`. -/
local macro "qstore " t:term : tactic => `(tactic| (
  have step := rpw_next run
  clear run
  obtain ⟨_, w, run⟩ := step
  refine .next ⟨w, storeClass $t, fun x h => by cases h⟩ ?_
  obtain ⟨_, _, rfl⟩ := ri_sstore_any (erase w.1)
  clear w))

/-- **Helper `46` classified.** Every store of an actual helper-`46` run for
string `(slot, head)` (length `L` read from the actual header, payload at
`D`, no wrap of `D + L`) writes `slot`, a literal zero, or a bounded modular
payload key of the actual decoded string. Same `PotStep P` run, same
pre-state and outcome. -/
theorem helper46_obs
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {L D slot head : B256} {S : List B256} {o : Outcome}
    (hslot : (slot, head) ∈ stringSlots) (hL : L = lenAt sevm head)
    (hnw : D.toNat + L.toNat < 2 ^ 256)
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b (L :: D :: slot :: S) M G) ImplV1.t_2e8a_c46 o) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm
      (St b (L :: D :: slot :: S) M G) ImplV1.t_2e8a_c46 o := by
  have eraseP : ∀ {s d n d'}, FreePtr.PotStep P s d n d' → Ninst.Run s d n d' :=
    fun h => erase h.1
  have tail7 : ∀ {d o}, SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm d
      ImplV1.t_2ef9_c7 o →
      SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm d ImplV1.t_2ef9_c7 o :=
    fun run => SFunc.RunP.mono zeroObs_obs (tail7_zero eraseP run)
  unfold ImplV1.t_2e8a_c46 at run ⊢
  refine qdest run fun G run => ?_
  qs ri_dup rfl
  qs ri_dup rfl
  qsload
  qs ri_push
  qs ri_dup rfl
  qs ri_push
  qs ri_and
  qs ri_iszero
  qs ri_push
  qs ri_mul
  qs ri_sub
  qs ri_and
  qs ri_push
  qs ri_swap rfl
  qs ri_div
  qs ri_swap rfl
  qs ri_push
  qs ri_mstore
  qs ri_push
  qs ri_push
  qs ri_keccak
  qs ri_swap rfl
  qs ri_push
  qs ri_add
  qs ri_push
  qs ri_swap rfl
  qs ri_div
  qs ri_dup rfl
  qs ri_add
  qs ri_swap rfl
  qs ri_dup rfl
  qs ri_push
  qs ri_lt
  qs ri_push
  have hash : ((M.write (Bytes.toB256 [0]).toNat slot.toBytes).read (Bytes.toB256 [0]).toNat
      (Bytes.toB256 [32]).toNat).1 = slot.toBytes := by
    have h := Mem.read_write_zero M (ys := slot.toBytes) (by
      intro e; have := B256.length_toBytes slot; rw [e] at this; cases this)
    rw [B256.length_toBytes] at h
    exact h
  rw [hash] at run ⊢
  generalize ((M.write (Bytes.toB256 [0]).toNat slot.toBytes).read (Bytes.toB256 [0]).toNat
    (Bytes.toB256 [32]).toNat).2 = M1 at run ⊢
  refine qbranch run (fun G hw run => ?_) (fun G hw run => ?_)
  · -- short string: header store at `slot`, then the shared tail
    unfold ImplV1.t_2ebb_c46 at run ⊢
    qs ri_dup rfl
    qs ri_mload
    qs ri_push
    qs ri_not
    qs ri_and
    qs ri_dup rfl
    qs ri_dup rfl
    qs ri_add
    qs ri_or
    qs ri_dup rfl
    qstore (Or.inl (slot_fixed hslot))
    qs ri_push
    cases run with
    | jump d0 get pop run =>
      cases Option.some.inj (get.symm.trans
        (show ImplV1.cert.prog[7]? = some ImplV1.t_2ef9_c7 from rfl))
      exact .jump d0 get pop (tail7 run)
  · -- long string: header store at `slot`, payload loop, shared tail
    have long : 31 < L.toNat := by
      have h : Bytes.toB256 [31] < L := by
        by_contra hn
        exact hw (by simp only [B256.ltCheck, hn, ↓reduceIte])
      rw [B256.lt_iff_toNat_lt_toNat] at h
      exact h
    generalize (slot.toBytes.keccak +
        (Bytes.toB256 [31] + (Bytes.toB256 [1, 0] * ((Bytes.toB256 [1] &&& _) =? 0) -
          Bytes.toB256 [1] &&& _) / Bytes.toB256 [2]) / Bytes.toB256 [32]) = E at run ⊢
    unfold ImplV1.t_2ecb_c46 at run ⊢
    refine qdest run fun G run => ?_
    qs ri_dup rfl
    qs ri_dup rfl
    qs ri_add
    qs ri_push
    qs ri_add
    qs ri_dup rfl
    qstore (Or.inl (slot_fixed hslot))
    qs ri_dup rfl
    qs ri_iszero
    qs ri_push
    refine qbranchTo run (fun G _ run => ?_) (fun G g _ get run => ?_)
    · unfold ImplV1.t_2eda_c46 at run ⊢
      qs ri_swap rfl
      qs ri_dup rfl
      qs ri_add
      rw [t_2edd_c46_shape] at run ⊢
      have cnt : SolcStoragePayload.count (D + L) D.toNat = (L.toNat + 31) / 32 := by
        unfold SolcStoragePayload.count
        rw [B256.toNat_add_eq_of_nof _ _ hnw]
        congr 1
        omega
      have exitCert : ∀ {d sg}, SFunc.RunCutP (FreePtr.PotStep P) ImplV1.cert.prog sevm
          [OldInitializerV1Payload.k52] d ImplV1.t_2ef8_c52 sg →
          ∃ o, sg = .done o ∧ SFunc.RunP (SolcStoragePayload.Enriched (FreePtr.PotStep P)
            (D + L) slot.toBytes.keccak D.toNat) ImplV1.cert.prog sevm d ImplV1.t_2ef8_c52 o := by
        intro d sg cut
        obtain ⟨o, rfl⟩ := tail8_done cut
        refine ⟨o, rfl, ?_⟩
        have run := runCutP_done cut
        unfold ImplV1.t_2ef8_c52 at run ⊢
        cases run with
        | dest burn run =>
          exact .dest burn (SFunc.RunP.mono
            (fun h => ⟨h.1, fun hn key value rest hs => Or.inl (h.2.1 hn key value rest hs),
              h.2.2⟩) (tail7_zero eraseP run))
      have enriched := SolcStoragePayload.runP_enriched (P := FreePtr.PotStep P) eraseP
        (SolcStoragePayload.readWindow_potStep erase) OldInitializerV1Payload.entry52 exitCert
        (i₀ := 0) (rest := E :: slot :: S)
        ⟨Nat.zero_le _, by omega, by
          have z : (0 : Nat).toB256 = (0 : B256) := rfl
          simp only [St.stack, Nat.mul_zero, Nat.add_zero, toB256_toNat, z, B256.add_zero]⟩ run
      refine SFunc.RunP.mono (fun h => ⟨h.1, fun hn key value rest hs => ?_, h.2.2⟩) enriched
      rcases h.2.1 hn key value rest hs with zero | ⟨j, hj, hk⟩
      · exact Or.inr (Or.inl zero)
      · refine Or.inr (Or.inr ⟨slot, head, hslot, hL ▸ long, j, ?_, hk⟩)
        rw [← hL, ← cnt]
        exact hj
    · cases Option.some.inj (get.symm.trans
        (show ImplV1.cert.prog[7]? = some ImplV1.t_2ef9_c7 from rfl))
      exact tail7 run

/-! ## Callee fragments -/

/-- The 20-byte address mask literal. -/
def m20b : Bytes := [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The shared reverting arm `push 0; dup1; revert`. -/
def revArm : SFunc := .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

/-- One nonzero-address check on stack word `j`, reverting on zero. -/
def chk (j : Fin 16) (tag : Bytes) (htag : tag.length ≤ 32) (k : SFunc) : SFunc :=
  .dest (.next (.push [0x00] (by decide)) (.next (.push m20b (by decide)) (.next (.reg .and)
    (.next (.reg (.dup j)) (.next (.push m20b (by decide)) (.next (.reg .and)
    (.next (.reg .eq) (.next (.reg .iszero) (.next (.reg .iszero) (.next (.reg .iszero)
    (.next (.push tag htag) (.branch revArm k))))))))))))

/-- One packed setter: read-modify-write of `slot` with the masked stack word `j`. -/
def setFrag (j : Fin 16) (slot mask : Bytes) (hs : slot.length ≤ 32) (hm : mask.length ≤ 32)
    (k : SFunc) : SFunc :=
  .next (.reg (.dup j)) (.next (.push slot hs) (.next (.push [0x00] (by decide))
    (.next (.push [0x01, 0x00] (by decide)) (.next (.reg .exp) (.next (.reg (.dup 1))
    (.next (.reg .sload) (.next (.reg (.dup 1)) (.next (.push mask hm) (.next (.reg .mul)
    (.next (.reg .not) (.next (.reg .and) (.next (.reg (.swap 0)) (.next (.reg (.dup 3))
    (.next (.push mask hm) (.next (.reg .and) (.next (.reg .mul) (.next (.reg .or)
    (.next (.reg (.swap 0)) (.next (.reg .sstore) (.next (.reg .pop) k))))))))))))))))))))

/-- Stage string `j` (pointer on the stack) for helper `46` at `slot`, returning
to `tag`. -/
def callFrag (j : Fin 16) (slot tag : Bytes) (hs : slot.length ≤ 32) (ht : tag.length ≤ 32)
    (k : SFunc) : SFunc :=
  .next (.reg (.dup j)) (.next (.push slot hs) (.next (.reg (.swap 0)) (.next (.reg (.dup 0))
    (.next (.reg .mload) (.next (.reg (.swap 0)) (.next (.push [0x20] (by decide))
    (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.push tag ht) (.next (.reg (.swap 2))
    (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.push [0x2e, 0x8a] (by decide))
    (.callNext 46 k))))))))))))))

theorem t_16cc_shape : ImplV1.t_16cc_c16 = chk 4 [0x17, 0x08] (by decide) ImplV1.t_1708_c16 := rfl
theorem t_1708_shape : ImplV1.t_1708_c16 = chk 3 [0x17, 0x44] (by decide) ImplV1.t_1744_c16 := rfl
theorem t_1744_shape : ImplV1.t_1744_c16 = chk 2 [0x17, 0x80] (by decide) ImplV1.t_1780_c16 := rfl
theorem t_1780_shape : ImplV1.t_1780_c16 = chk 1 [0x17, 0xbc] (by decide) ImplV1.t_17bc_c16 := rfl

theorem t_17bc_shape : ImplV1.t_17bc_c16 =
    .dest (callFrag 7 [0x04] [0x17, 0xd2] (by decide) (by decide) ImplV1.t_17d2_c16) := rfl
theorem t_17d2_shape : ImplV1.t_17d2_c16 =
    .dest (.next (.reg .pop) (callFrag 6 [0x05] [0x17, 0xe9] (by decide) (by decide)
      ImplV1.t_17e9_c16)) := rfl
theorem t_17e9_shape : ImplV1.t_17e9_c16 =
    .dest (.next (.reg .pop) (callFrag 5 [0x07] [0x18, 0x00] (by decide) (by decide)
      ImplV1.t_1800_c16)) := rfl
theorem t_1800_shape : ImplV1.t_1800_c16 =
    .dest (.next (.reg .pop)
      (setFrag 4 [0x06] [0xff] (by decide) (by decide)
      (setFrag 3 [0x08] m20b (by decide) (by decide)
      (setFrag 2 [0x01] m20b (by decide) (by decide)
      (setFrag 1 [0x02] m20b (by decide) (by decide)
      (.next (.push [0x18, 0xe8] (by decide)) (.next (.reg (.dup 1))
      (.next (.push [0x2e, 0x47] (by decide)) (.callNext 47 ImplV1.t_18e8_c16))))))))) := rfl

set_option hygiene false in
/-- One observed `DUP` of an unnamed stack word. -/
local macro "qsdup" : tactic => `(tactic| (
  have step := rpw_next run
  clear run
  obtain ⟨_, w, run⟩ := step
  refine .next ⟨w, silentClass rfl, silentNoExec rfl⟩ ?_
  obtain ⟨_, _, _, rfl⟩ := ri_dup_any (erase w.1)
  clear w))

section Frags

variable {fs : List SFunc} {k : SFunc} {o : Outcome}

theorem revArm_false {d : Devm} (run : SFunc.RunP P fs sevm d revArm o) : False := by
  unfold revArm at run
  obtain ⟨_, -, run⟩ := rpw_next run
  obtain ⟨_, -, run⟩ := rpw_next run
  exact rpw_revert run

theorem chk_obs (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {j : Fin 16} {tag : Bytes} {htag : tag.length ≤ 32}
    (run : SFunc.RunP (FreePtr.PotStep P) fs sevm (St b S M G) (chk j tag htag k) o)
    (cont : ∀ G', SFunc.RunP (FreePtr.PotStep P) fs sevm (St b S M G') k o →
      SFunc.RunP (Obs (FreePtr.PotStep P) sevm) fs sevm (St b S M G') k o) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) fs sevm (St b S M G) (chk j tag htag k) o := by
  unfold chk at run ⊢
  refine qdest run fun G run => ?_
  qs ri_push
  qs ri_push
  qs ri_and
  qsdup
  qs ri_push
  qs ri_and
  qs ri_eq
  qs ri_iszero
  qs ri_iszero
  qs ri_iszero
  qs ri_push
  exact qbranch run (fun _ _ run => (revArm_false run).elim) (fun G _ run => cont G run)

theorem setFrag_obs (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {j : Fin 16} {slot mask : Bytes} {hs : slot.length ≤ 32} {hm : mask.length ≤ 32}
    (hfix : Bytes.toB256 slot ∈ fixedSlots)
    (run : SFunc.RunP (FreePtr.PotStep P) fs sevm (St b S M G) (setFrag j slot mask hs hm k) o)
    (cont : ∀ b' G', SFunc.RunP (FreePtr.PotStep P) fs sevm (St b' S M G') k o →
      SFunc.RunP (Obs (FreePtr.PotStep P) sevm) fs sevm (St b' S M G') k o) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) fs sevm (St b S M G)
      (setFrag j slot mask hs hm k) o := by
  unfold setFrag at run ⊢
  qsdup
  qs ri_push
  qs ri_push
  qs ri_push
  qs ri_exp
  qs ri_dup rfl
  qsload
  qs ri_dup rfl
  qs ri_push
  qs ri_mul
  qs ri_not
  qs ri_and
  qs ri_swap rfl
  qs ri_dup rfl
  qs ri_push
  qs ri_and
  qs ri_mul
  qs ri_or
  qs ri_swap rfl
  qstore (Or.inl hfix)
  qs ri_pop
  exact cont _ _ run

end Frags

theorem callFrag_obs (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {j : Fin 16} {slot tag : Bytes} {hs : slot.length ≤ 32} {ht : tag.length ≤ 32}
    {k : SFunc} {o : Outcome} {p head : B256} (hp : S[j.val]? = some p)
    (hslot : (Bytes.toB256 slot, head) ∈ stringSlots)
    (hL : memWord M p.toNat = lenAt sevm head)
    (hnw : (32 + p).toNat + (memWord M p.toNat).toNat < 2 ^ 256)
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm (St b S M G)
      (callFrag j slot tag hs ht k) o)
    (cont : ∀ b' M' G', Keeps (((M.read p.toNat 32).2).write 0 (Bytes.toB256 slot).toBytes) M' →
      SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
        (St b' (Bytes.toB256 slot :: S) M' G') k o →
      SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm
        (St b' (Bytes.toB256 slot :: S) M' G') k o) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm (St b S M G)
      (callFrag j slot tag hs ht k) o := by
  have eraseP : ∀ {s d n d'}, FreePtr.PotStep P s d n d' → Ninst.Run s d n d' :=
    fun h => erase h.1
  unfold callFrag at run ⊢
  qs ri_dup hp
  qs ri_push
  qs ri_swap rfl
  qs ri_dup rfl
  qs ri_mload
  qs ri_swap rfl
  qs ri_push
  qs ri_add
  qs ri_swap rfl
  qs ri_push
  qs ri_swap rfl
  qs ri_swap rfl
  qs ri_swap rfl
  qs ri_push
  have lookup : ImplV1.cert.prog[46]? = some ImplV1.t_2e8a_c46 := rfl
  cases run with
  | callHalt d0 get pop callee =>
    rw [lookup] at get
    cases get
    rw [(St.of_pop1 pop).2] at callee pop
    exact .callHalt d0 lookup pop (helper46_obs erase hslot hL hnw callee)
  | callRet d0 get pop callee rest =>
    rw [lookup] at get
    cases get
    rw [(St.of_pop1 pop).2] at callee pop
    obtain ⟨b', M', G', rfl, keep⟩ := helper46_returned eraseP callee
    exact .callRet d0 lookup pop (helper46_obs erase hslot hL hnw callee)
      (cont b' M' G' keep rest)

set_option hygiene false in
/-- One observed state-silent step whose post-state is no longer needed. -/
local macro "qn" : tactic => `(tactic| (
  have step := rpw_next run
  clear run
  obtain ⟨_, w, run⟩ := step
  refine .next ⟨w, silentClass rfl, silentNoExec rfl⟩ ?_
  clear w))


/-- The registered V1 runtime owner helper is the shared legacy initializer. -/
theorem helper47_shape : ImplV1.t_2e47_c47 = SolcStorageReturn.legacyOwnerInit := rfl

/-- The actual returning V1 owner helper preserves the upper slot bits,
changes only the low address field, and restores the caller's stack tail. -/
theorem helper47_effects {post : Devm} {owner returnPC : B256}
    (run : SFunc.Run ImplV1.cert.prog sevm (St b (owner :: returnPC :: S) M G)
      ImplV1.t_2e47_c47 (.returned post)) :
    post.stack = S ∧ post.memory = M ∧
      post.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set 0
        (addressSlotWriteWord (b.getStorVal sevm.currentTarget 0) owner.toAdr.toB256) ∧
      (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) := by
  rw [helper47_shape] at run
  exact SolcStorageReturn.legacyOwnerInit_effects run

/-- Helper `47` (owner setter) writes only slot `0`. -/
theorem helper47_obs (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {d : Devm} {o : Outcome}
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm d ImplV1.t_2e47_c47 o) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm d ImplV1.t_2e47_c47 o := by
  rw [St.self' d] at run ⊢
  unfold ImplV1.t_2e47_c47 at run ⊢
  refine qdest run fun G run => ?_
  qsdup
  qs ri_push
  qs ri_dup rfl
  qs ri_push
  qs ri_exp
  qs ri_dup rfl
  qsload
  qs ri_dup rfl
  qs ri_push
  qs ri_mul
  qs ri_not
  qs ri_and
  qs ri_swap rfl
  qs ri_dup rfl
  qs ri_push
  qs ri_and
  qs ri_mul
  qs ri_or
  qs ri_swap rfl
  qstore (Or.inl (by decide))
  qn
  qn
  cases run with
  | ret d0 pop => exact .ret d0 pop

/-- The initialized-flag store `t_18e8_c16` writes only slot `8`. -/
theorem t_18e8_obs (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {d : Devm} {o : Outcome}
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm d ImplV1.t_18e8_c16 o) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm d ImplV1.t_18e8_c16 o := by
  rw [St.self' d] at run ⊢
  unfold ImplV1.t_18e8_c16 at run ⊢
  refine qdest run fun G run => ?_
  qs ri_push
  qs ri_push
  qs ri_push
  qs ri_push
  qs ri_exp
  qs ri_dup rfl
  qsload
  qs ri_dup rfl
  qs ri_push
  qs ri_mul
  qs ri_not
  qs ri_and
  qs ri_swap rfl
  qs ri_dup rfl
  qs ri_iszero
  qs ri_iszero
  qs ri_mul
  qs ri_or
  qs ri_swap rfl
  qstore (Or.inl (by decide))
  iterate 9 qn
  cases run with
  | ret d0 pop => exact .ret d0 pop

/-- A word at or above `32` that fits in `Mx` survives a header read, the
scratch word write at `0`, and any kept continuation. -/
theorem memWord_keeps {Mx M' : Mem} {i n o : Nat} {v : B256}
    (keep : Keeps (((Mx.read i n).2).write 0 v.toBytes) M') (h32 : 32 ≤ o)
    (hfit : o + 32 ≤ Mx.size) :
    memWord M' o = memWord Mx o ∧ Mx.size ≤ M'.size := by
  have s1 : Mx.size ≤ (Mx.read i n).2.size := memExtSize_ge _ _ _
  have s2 := (Mem.write_agree (Mx.read i n).2 0 v.toBytes).1
  have hlen : v.toBytes.length = 32 := B256.length_toBytes v
  refine ⟨?_, le_trans s1 (le_trans s2 keep.2)⟩
  have e1 : memWord M' o = memWord (((Mx.read i n).2).write 0 v.toBytes) o :=
    memWord_congr (fun j _ => by rw [keep.1])
  rw [e1]
  have e2 : memWord (((Mx.read i n).2).write 0 v.toBytes) o = memWord (Mx.read i n).2 o := by
    apply memWord_congr
    intro j hj
    exact (Mem.write_agree (Mx.read i n).2 0 v.toBytes).2 _ (by omega) (Or.inr (by omega))
  rw [e2]
  rfl

/-- `32 + p` does not wrap below the header-plus-payload bound. -/
theorem nowrap {p L : B256} (h : p.toNat + 32 + L.toNat < 2 ^ 256) :
    (32 + p).toNat + L.toNat < 2 ^ 256 := by
  rw [B256.toNat_add_eq_of_nof _ _ (by show (32 : B256).toNat + p.toNat < 2 ^ 256; rw [show (32 : B256).toNat = 32 from rfl]; omega)]
  rw [show (32 : B256).toNat = 32 from rfl]
  omega

/-- The setter block `t_1800_c16` (decimals, master minter, pauser,
blacklister, then helper `47` and the initialized flag) writes only fixed
slots. -/
theorem t_1800_obs (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {x : B256} {o : Outcome}
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm (St b (x :: S) M G)
      ImplV1.t_1800_c16 o) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm (St b (x :: S) M G)
      ImplV1.t_1800_c16 o := by
  rw [t_1800_shape] at run ⊢
  refine qdest run fun G run => ?_
  qs ri_pop
  refine setFrag_obs erase (by decide) run fun b G run => ?_
  refine setFrag_obs erase (by decide) run fun b G run => ?_
  refine setFrag_obs erase (by decide) run fun b G run => ?_
  refine setFrag_obs erase (by decide) run fun b G run => ?_
  qs ri_push
  qsdup
  qs ri_push
  have lookup : ImplV1.cert.prog[47]? = some ImplV1.t_2e47_c47 := rfl
  cases run with
  | callHalt d0 get pop callee =>
    rw [lookup] at get
    cases get
    exact .callHalt d0 lookup pop (helper47_obs erase callee)
  | callRet d0 get pop callee rest =>
    rw [lookup] at get
    cases get
    exact .callRet d0 lookup pop (helper47_obs erase callee) (t_18e8_obs erase rest)

/-- **Actual V1 initializer callee, classified (milestone A).** Every run of
the actual callee `t_16b0_c16` from the call-16 entry stack the wrapper
stages (four masked addresses, masked decimals, the three string pointers,
the return tag, the residual `R`) is the same `PotStep P` run with every store
classified: a fixed slot, a literal zero, or a bounded modular payload key of
an actual decoded string. Both outcomes are covered (the statement is about
the run with its own outcome). The memory facts are exactly the staged
headers, their fit in the entry memory and the no-wrap of each
header-plus-payload span; all come from `Staged3`. -/
theorem callee_obs
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {a1 a2 a3 a4 a5 p1 p2 p3 : B256} {R : List B256} {o : Outcome}
    (hdr1 : memWord M p1.toNat = lenAt sevm head1)
    (hdr2 : memWord M p2.toNat = lenAt sevm head2)
    (hdr3 : memWord M p3.toNat = lenAt sevm head3)
    (h32₂ : 32 ≤ p2.toNat) (h32₃ : 32 ≤ p3.toNat)
    (fit2 : p2.toNat + 32 ≤ M.size) (fit3 : p3.toNat + 32 ≤ M.size)
    (nw1 : p1.toNat + 32 + (lenAt sevm head1).toNat < 2 ^ 256)
    (nw2 : p2.toNat + 32 + (lenAt sevm head2).toNat < 2 ^ 256)
    (nw3 : p3.toNat + 32 + (lenAt sevm head3).toNat < 2 ^ 256)
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b (a1 :: a2 :: a3 :: a4 :: a5 :: p3 :: p2 :: p1 :: retTag :: R) M G)
      ImplV1.t_16b0_c16 o) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm
      (St b (a1 :: a2 :: a3 :: a4 :: a5 :: p3 :: p2 :: p1 :: retTag :: R) M G)
      ImplV1.t_16b0_c16 o := by
  unfold ImplV1.t_16b0_c16 at run ⊢
  refine qdest run fun G run => ?_
  qs ri_push
  qs ri_push
  qs ri_swap rfl
  qsload
  qs ri_swap rfl
  qs ri_push
  qs ri_exp
  qs ri_swap rfl
  qs ri_div
  qs ri_push
  qs ri_and
  qs ri_iszero
  qs ri_iszero
  qs ri_iszero
  qs ri_push
  refine qbranch run (fun _ _ run => (revArm_false run).elim) (fun G _ run => ?_)
  rw [t_16cc_shape] at run ⊢
  refine chk_obs erase run fun G run => ?_
  rw [t_1708_shape] at run ⊢
  refine chk_obs erase run fun G run => ?_
  rw [t_1744_shape] at run ⊢
  refine chk_obs erase run fun G run => ?_
  rw [t_1780_shape] at run ⊢
  refine chk_obs erase run fun G run => ?_
  -- name (slot 4)
  rw [t_17bc_shape] at run ⊢
  refine qdest run fun G run => ?_
  refine callFrag_obs erase (p := p1) (head := head1) rfl (by decide) hdr1
    (by rw [hdr1]; exact nowrap nw1) run fun b M1 G keep1 run => ?_
  obtain ⟨m2, s1⟩ := memWord_keeps keep1 h32₂ fit2
  obtain ⟨m3, -⟩ := memWord_keeps keep1 h32₃ fit3
  -- symbol (slot 5)
  rw [t_17d2_shape] at run ⊢
  refine qdest run fun G run => ?_
  qs ri_pop
  refine callFrag_obs erase (p := p2) (head := head2) rfl (by decide) (m2.trans hdr2)
    (by rw [m2, hdr2]; exact nowrap nw2) run fun b M2 G keep2 run => ?_
  obtain ⟨m3', -⟩ := memWord_keeps keep2 h32₃ (le_trans fit3 s1)
  -- currency (slot 7)
  rw [t_17e9_shape] at run ⊢
  refine qdest run fun G run => ?_
  qs ri_pop
  refine callFrag_obs erase (p := p3) (head := head3) rfl (by decide)
    (m3'.trans (m3.trans hdr3)) (by rw [m3', m3, hdr3]; exact nowrap nw3) run
    fun b M3 G _ run => ?_
  exact t_1800_obs erase run

/-- The terminal continuation `t_0584_c60 = dest; stop` has no instruction
step, so every run of it is observed. -/
theorem t_0584_obs {Q : Sevm → Devm → Ninst → Devm → Prop} {d : Devm} {o : Outcome}
    (run : SFunc.RunP P ImplV1.cert.prog sevm d ImplV1.t_0584_c60 o) :
    SFunc.RunP Q ImplV1.cert.prog sevm d ImplV1.t_0584_c60 o := by
  unfold ImplV1.t_0584_c60 at run ⊢
  cases run with
  | dest burn run =>
    cases run with
    | last h => exact .dest burn (.last h)

/-- **Whole V1 `initialize` same-run write classifier (milestone B).** Every
`PotStep P` run of the actual inherited `initialize` entry `t_0410_c60`
(selector `0x3357162b`; entry stack: callvalue word over the dispatcher
residual `R`), from memory whose free pointer is `p1 ≥ 96`, is the same run
(same `P`, pre-state and outcome) with every store classified by
`V1InitializerWriteClass`: fixed slot `0/1/2/4/5/6/7/8`, literal zero, or a
bounded modular payload key `keccak(slot) + i` (`i < (L + 31) / 32`) of an
actual long decoded string at slot `4`/`5`/`7` with `L` its actual decoded
length; and no external instruction executes. The only premises are the
wrapper-entry free-pointer seams. -/
theorem initialize_observed
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {cv p1 : B256} {R : List B256} {M0 : Mem} {G0 : Nat} {out : Outcome}
    (hfp : memWord M0 64 = p1) (hp96 : 96 ≤ p1.toNat)
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b (cv :: R) M0 G0) ImplV1.t_0410_c60 out) :
    SFunc.RunP (Obs (FreePtr.PotStep P) sevm) ImplV1.cert.prog sevm
      (St b (cv :: R) M0 G0) ImplV1.t_0410_c60 out := by
  obtain ⟨p2, p3, M3, G2, -, hS, rest⟩ := wrapper_stage erase hfp hp96 run
  dsimp only at rest
  obtain ⟨L, run⟩ := rest
  refine L _ (fun w hs => ⟨w, silentClass hs, silentNoExec hs⟩) out ?_
  have n1 := hS.next1
  have n2 := hS.next2
  have o12 := hS.ord12
  have o23 := hS.ord23
  have o34 := hS.ord34
  have b4 := hS.below4
  have f2 := hS.fit2
  have f3 := hS.fit3
  have callee := fun {G} {o} (r : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b ([mask20 &&& Sevm.dataWord sevm 228, mask20 &&& Sevm.dataWord sevm 196,
        mask20 &&& Sevm.dataWord sevm 164, mask20 &&& Sevm.dataWord sevm 132,
        mask8 &&& Sevm.dataWord sevm 100, p3, p2, p1, retTag] ++ R) M3 G)
      ImplV1.t_16b0_c16 o) =>
    callee_obs erase hS.hdr1 hS.hdr2 hS.hdr3 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) r
  cases run with
  | callHalt d0 get pop r =>
    rw [show ImplV1.cert.prog[16]? = some ImplV1.t_16b0_c16 from rfl] at get
    cases get
    rw [(St.of_pop1 pop).2] at r pop
    exact .callHalt d0 rfl pop (callee r)
  | callRet d0 get pop r rest =>
    rw [show ImplV1.cert.prog[16]? = some ImplV1.t_16b0_c16 from rfl] at get
    cases get
    rw [(St.of_pop1 pop).2] at r pop
    exact .callRet d0 rfl pop (callee r) (t_0584_obs rest)

/-- The requested write classifier, projected from the same actual run. -/
theorem initialize_writeClass
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {cv p1 : B256} {R : List B256} {M0 : Mem} {G0 : Nat} {out : Outcome}
    (hfp : memWord M0 64 = p1) (hp96 : 96 ≤ p1.toNat)
    (run : SFunc.RunP (FreePtr.PotStep P) ImplV1.cert.prog sevm
      (St b (cv :: R) M0 G0) ImplV1.t_0410_c60 out) :
    SFunc.RunP (fun s d n d' => FreePtr.PotStep P s d n d' ∧ V1InitializerWriteClass sevm d n)
      ImplV1.cert.prog sevm (St b (cv :: R) M0 G0) ImplV1.t_0410_c60 out :=
  SFunc.RunP.mono (fun h => ⟨h.1, h.2.1⟩) (initialize_observed erase hfp hp96 run)

end Blanc.Lift.Usdc.OldInitializerV1Callee
