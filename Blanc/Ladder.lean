import Blanc.LadderBase
import Blanc.LadderSem

namespace Blanc

open Jaune

structure ContractSpec where
  /-- The contract's source program.  The ladder consumes it only through
  `Prog.compile` — code preservation across sub-executions, code
  non-emptiness (`Prog.compile_ne_nil`) and non-delegation
  (`not_delegation_of_compile`), all three of which are already generic in
  the program and therefore need no slot. -/
  prog : Prog
  /-- storage at the contract address → callvalue in flight → the contract's
  ETH balance → Prop. -/
  Inv : Stor → B256 → B256 → Prop
  /-- The global side condition on the world's balance map. -/
  Side : (Adr → B256) → Prop
  /-- Once a frame has terminated there is no callvalue in flight.
  (WETH: `solvent_zero_of_solvent`.) -/
  inv_forget : ∀ {s : Stor} {v b : B256}, Inv s v b → Inv s 0 b
  /-- The invariant survives a rise in the contract's own balance. -/
  inv_mono : ∀ {s : Stor} {v b b' : B256}, Inv s v b → b.toNat ≤ b'.toNat → Inv s v b'
  /-- A callvalue that has already been credited to the contract's balance may
  be taken into flight. -/
  inv_recv : ∀ {s : Stor} {v b b' : B256}, Inv s 0 b → b'.toNat = b.toNat + v.toNat → Inv s v b'
  /-- The side condition survives any change that does not raise the total. -/
  side_le : ∀ {f g : Adr → B256}, Side f → sum g ≤ sum f → Side g
  /-- The side condition survives a value transfer. -/
  side_transfer : ∀ {st st' : Jaune.State} {caller callee : Adr} {wad : B256},
    st.subBal caller wad = some st' → Side st.bal → Side (st'.addBal callee wad).bal
  /-- The side condition survives a credit that stays under the bound.  The
  bound is supplied by the caller's wei-conservation argument, exactly as in
  `State.Inv.addBal`. -/
  side_addBal : ∀ {w : Jaune.State} {a : Adr} {val : B256},
    sum w.bal + val.toNat < 2 ^ 256 → Side w.bal → Side (w.addBal a val).bal
  /-- The invariant survives a value transfer that does not debit the
  contract.  The callee may be the contract itself, in which case its balance
  rises; `Side` is what rules out a wrap. -/
  inv_transfer : ∀ {st st' : Jaune.State} {caller callee ca : Adr} {wad v : B256},
    st.subBal caller wad = some st' → caller ≠ ca → Side st.bal →
    Inv (st.getStor ca) v (st.bal ca) →
    Inv ((st'.addBal callee wad).getStor ca) v ((st'.addBal callee wad).bal ca)
  /-- Entering a frame *at* the contract with callvalue `wad`: the transfer has
  already credited `wad` to the contract's balance, and the child frame carries
  it in flight. -/
  inv_recv_transfer : ∀ {st st' : Jaune.State} {caller ca : Adr} {wad : B256},
    st.subBal caller wad = some st' → caller ≠ ca → Side st.bal →
    Inv (st.getStor ca) 0 (st.bal ca) →
    Inv ((st'.addBal ca wad).getStor ca) wad ((st'.addBal ca wad).bal ca)
  /-- The invariant survives a bare credit under the wei-conservation bound
  (`State.Inv.addBal`: gas refunds, the coinbase fee, withdrawals). -/
  inv_addBal : ∀ {w : Jaune.State} {ca a : Adr} {val v : B256},
    sum w.bal + val.toNat < 2 ^ 256 → Side w.bal →
    Inv (w.getStor ca) v (w.bal ca) →
    Inv ((w.addBal a val).getStor ca) v ((w.addBal a val).bal ca)

namespace ContractSpec

variable (c : ContractSpec)

/-- The frame-entry form of the invariant: the callvalue is in flight exactly
when the current frame is executing the contract itself. -/
def PreInv (devm : Devm) (ca : Adr) (sevm : Sevm) : Prop :=
  (sevm.currentTarget = ca → c.Inv (Devm.getStor devm ca) sevm.value (devm.getBal ca)) ∧
  (sevm.currentTarget ≠ ca → c.Inv (Devm.getStor devm ca) 0 (devm.getBal ca))

/-- The frame-exit form of the invariant. -/
def PostInv (devm : Devm) (ca : Adr) : Prop :=
  c.Inv (Devm.getStor devm ca) 0 (devm.getBal ca)

/-- The generic counterpart of `Blanc.Precond`. -/
structure Pre (ca : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  (code : some (devm.getCode ca).toList = Prog.compile c.prog)
  (side : c.Side devm.getBal)
  (inv : c.PreInv devm ca sevm)

/-- The frame-entry precondition, together with the machine's memory
invariant *when the frame is the contract's own*.

`Mem.Wf` is a genuine machine invariant — `initDevm` starts from `Mem.empty`,
and `Mem.write`/`.extend`/`.extends` preserve it — but nothing in `Pre`
records it, and `Mem.write`'s in-place branch preserves its *negation* just as
faithfully, so a frame handed an ill-formed memory can never recover one.  A
contract obligation that reasons about memory therefore has to be *given* the
invariant at frame entry; it cannot establish it.

Why a separate predicate rather than a fourth field of `Pre`: `Pre.state_eq`
transports `Pre` along `Devm.state` equality alone, and memory is machine
state, not world state.  Roughly fifty call sites depend on that transport.

Why the guard: every rung of the frame-level ladder that has to *re-establish*
this predicate step-by-step does so under `sevm.currentTarget ≠ ca`, where the
conjunct is vacuous.  The two places the content is actually needed — the
contract's own frame at `pc = 0`, and a spawned child frame — are exactly the
places where the `Devm` is `initDevm`, so `Mem.wf_empty` discharges it. -/
structure PreWf (ca : Adr) (sevm : Sevm) (devm : Devm) : Prop where
  (pre : c.Pre ca sevm devm)
  (wf : sevm.currentTarget = ca → Mem.Wf devm.memory)

/-- The generic counterpart of `Blanc.Postcond`. -/
structure Post (ca : Adr) (_sevm : Sevm) (devm : Devm) : Prop where
  (side : c.Side devm.getBal)
  (inv : c.PostInv devm ca)

/-- The generic counterpart of `Blanc.State.Inv`. -/
structure StateInv (ca : Adr) (w : Jaune.State) : Prop where
  (code : some (w.getCode ca).toList = Prog.compile c.prog)
  (side : c.Side w.bal)
  (inv : c.Inv (w.getStor ca) 0 (w.bal ca))

end ContractSpec

/-- The sem-parametric view of an ordinary contract specification. -/
def ContractSpec.toSem (c : ContractSpec) : ContractSpecSem :=
  { sem := c.prog.codeSem
    Inv := c.Inv
    Side := c.Side
    inv_forget := c.inv_forget
    inv_mono := c.inv_mono
    inv_recv := c.inv_recv
    side_le := c.side_le
    side_transfer := c.side_transfer
    side_addBal := c.side_addBal
    inv_transfer := c.inv_transfer
    inv_recv_transfer := c.inv_recv_transfer
    inv_addBal := c.inv_addBal }

namespace ContractSpec

def pre_toSem {c : ContractSpec} {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h : c.Pre ca sevm devm) : (c.toSem).Pre ca sevm devm :=
  ⟨h.code, h.side, h.inv⟩

def pre_ofSem {c : ContractSpec} {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h : (c.toSem).Pre ca sevm devm) : c.Pre ca sevm devm :=
  ⟨h.code, h.side, h.inv⟩

def preWf_toSem {c : ContractSpec} {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h : c.PreWf ca sevm devm) : (c.toSem).PreWf ca sevm devm :=
  ⟨pre_toSem h.pre, h.wf⟩

def preWf_ofSem {c : ContractSpec} {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h : (c.toSem).PreWf ca sevm devm) : c.PreWf ca sevm devm :=
  ⟨pre_ofSem h.pre, h.wf⟩

def post_toSem {c : ContractSpec} {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h : c.Post ca sevm devm) : (c.toSem).Post ca sevm devm :=
  ⟨h.side, h.inv⟩

def post_ofSem {c : ContractSpec} {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h : (c.toSem).Post ca sevm devm) : c.Post ca sevm devm :=
  ⟨h.side, h.inv⟩

def stateInv_toSem {c : ContractSpec} {ca : Adr} {w : Jaune.State}
    (h : c.StateInv ca w) : (c.toSem).StateInv ca w :=
  ⟨h.code, h.side, h.inv⟩

def stateInv_ofSem {c : ContractSpec} {ca : Adr} {w : Jaune.State}
    (h : (c.toSem).StateInv ca w) : c.StateInv ca w :=
  ⟨h.code, h.side, h.inv⟩

end ContractSpec

namespace ContractSpec

variable {c : ContractSpec}

/-- Once the frame has terminated the callvalue is no longer in flight.  This
is the `inv_forget` slot and nothing else. -/
lemma post_of_pre {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h : c.Pre ca sevm devm) : c.Post ca sevm devm := by
  exact post_ofSem (ContractSpecSem.post_of_pre (c := c.toSem) (pre_toSem h))

lemma Post.of_state_eq {ca : Adr} {sevm sevm' : Sevm} {child post : Devm}
    (h : c.Post ca sevm' child) (hstate : post.state = child.state) :
    c.Post ca sevm post := by
  exact post_ofSem (ContractSpecSem.Post.of_state_eq (c := c.toSem) (post_toSem h) hstate)

lemma Pre.state_eq {wa sevm devm devm'}
    (h_pc : c.Pre wa sevm devm) (h_eq : devm'.state = devm.state) :
    c.Pre wa sevm devm' := by
  exact pre_ofSem (ContractSpecSem.Pre.state_eq (c := c.toSem) (pre_toSem h_pc) h_eq)

lemma Pre.of_eqs {wa : Adr} {sevm : Sevm} {pre inter : Devm}
    (h_pc : c.Pre wa sevm pre)
    (h_code : inter.getCode wa = pre.getCode wa)
    (h_bal : inter.getBal = pre.getBal)
    (h_stor : Devm.getStor inter wa = Devm.getStor pre wa) :
    c.Pre wa sevm inter := by
  exact pre_ofSem (ContractSpecSem.Pre.of_eqs (c := c.toSem) (pre_toSem h_pc) h_code h_bal h_stor)

lemma Pre.transfer_state {ca : Adr} {sevm : Sevm} {pre inter : Devm}
    {caller callee : Adr} {wad : B256} {st_mid : Jaune.State}
    (h_pc : c.Pre ca sevm pre)
    (h_ne : caller ≠ ca)
    (h_sub : pre.state.subBal caller wad = some st_mid)
    (h_state : inter.state = st_mid.addBal callee wad) :
    c.Pre ca sevm inter := by
  exact pre_ofSem (ContractSpecSem.Pre.transfer_state (c := c.toSem)
    (pre_toSem h_pc) h_ne h_sub h_state)

lemma GenericCall.none_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp .none (.ok inter))
    (h_ne : stv = true → caller ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  exact pre_ofSem (ContractSpecSem.GenericCall.none_preserves_precond (c := c.toSem) h_run h_ne (pre_toSem h_pc))

lemma GenericCreate.none_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    (h_run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize
      .none (.ok inter))
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  exact pre_ofSem (ContractSpecSem.GenericCreate.none_preserves_precond
    (c := c.toSem) h_run (pre_toSem h_pc))

lemma Xinst.none_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm} {x : Xinst}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : Xinst.Run sevm devm x .none (.ok inter))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  exact pre_ofSem (ContractSpecSem.Xinst.none_preserves_precond (c := c.toSem) hfork h_run h_ne (pre_toSem h_pc))

lemma Ninst.none_preserves_precond
    {wa : Adr} {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst}
    (hfork : CoveredFork sevm.benvStat.fork)
    (run : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (target_ne : sevm.currentTarget ≠ wa)
    (precondition : c.Pre wa sevm pre) :
    c.Pre wa sevm inter := by
  exact pre_ofSem (ContractSpecSem.Ninst.none_preserves_precond
    (c := c.toSem) hfork run target_ne (pre_toSem precondition))

lemma Pre.child_of_transfer {ca : Adr} {sevm sevm' : Sevm} {devm devm' : Devm}
    {st st_mid : Jaune.State} {caller target : Adr} {value : B256}
    (h_pc : c.Pre ca sevm devm)
    (h_ct_ne : sevm.currentTarget ≠ ca)
    (h_ne : caller ≠ ca)
    (h_stor : (st.get ca).stor = (devm.state.get ca).stor)
    (h_code : (st.get ca).code = (devm.state.get ca).code)
    (h_bal : ∀ a, (st.get a).bal = (devm.state.get a).bal)
    (h_sub : st.subBal caller value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct' : sevm'.currentTarget = target)
    (h_val : sevm'.currentTarget = ca → sevm'.value = value) :
    c.Pre ca sevm' devm' := by
  exact pre_ofSem (ContractSpecSem.Pre.child_of_transfer (c := c.toSem)
    (pre_toSem h_pc) h_ct_ne h_ne h_stor h_code h_bal h_sub h_state h_ct' h_val)

lemma Pre.child_of_outbound_transfer
    {ca target : Adr} {sevm' : Sevm} {devm' : Devm}
    {st st_mid : Jaune.State} {value : B256}
    (h_code : some (st.getCode ca).toList = Prog.compile c.prog)
    (h_side : c.Side st.bal)
    (h_inv : c.Inv (st.getStor ca) 0 (st.bal ca - value))
    (h_sub : st.subBal ca value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct : sevm'.currentTarget = target)
    (h_value : sevm'.value = value) :
    c.Pre ca sevm' devm' := by
  exact pre_ofSem (ContractSpecSem.Pre.child_of_outbound_transfer (c := c.toSem)
    (by simpa [ContractSpec.toSem, Prog.codeSem] using h_code)
    h_side h_inv h_sub h_state h_ct h_value)

lemma Pre.child_of_eqs {wa : Adr} {sevm sevm' : Sevm} {devm devm' : Devm}
    (h_pc : c.Pre wa sevm devm)
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_state : devm'.state = devm.state)
    (h_val : sevm'.currentTarget = wa → sevm'.value = 0) :
    c.Pre wa sevm' devm' := by
  exact pre_ofSem (ContractSpecSem.Pre.child_of_eqs (c := c.toSem)
    (pre_toSem h_pc) h_ct_ne h_state h_val)

lemma Pre.of_postcond {wa : Adr} {sevm sevm' : Sevm} {child inter devm' : Devm}
    (h_post : c.Post wa sevm' child)
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_code_pre : some (devm'.getCode wa).toList = Prog.compile c.prog)
    (h_code_eq : child.getCode wa = devm'.getCode wa)
    (h_stor : (inter.state.get wa).stor = (child.state.get wa).stor)
    (h_code : (inter.state.get wa).code = (child.state.get wa).code)
    (h_bal : ∀ a, (inter.state.get a).bal = (child.state.get a).bal) :
    c.Pre wa sevm inter := by
  exact pre_ofSem (ContractSpecSem.Pre.of_postcond (c := c.toSem)
    (post_toSem h_post) h_ct_ne
    (by simpa [ContractSpec.toSem, Prog.codeSem] using h_code_pre)
    h_code_eq h_stor h_code h_bal)

lemma GenericCall.some_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {gas : Nat} {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {evm' : Evm} {exn' : Execution}
    (h_run : GenericCall sevm devm gas value caller target codeAddress stv
      isStatic ii is oi os code dp (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_ne : stv = true → caller ≠ wa)
    (h_tv : stv = false → target = wa → value = 0)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  rcases ContractSpecSem.GenericCall.some_preserves_precond (c := c.toSem)
      h_run ex_sub h_ct_ne h_ne h_tv (pre_toSem h_pc) with ⟨hpre, hpost⟩
  exact ⟨pre_ofSem hpre, fun hp => by
    cases exn' with
    | error e => exact pre_ofSem (hpost trivial)
    | ok out => exact pre_ofSem (hpost (post_toSem hp))⟩


lemma GenericCreate.some_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    {evm' : Evm} {exn' : Execution}
    (h_run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize
      (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ct_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  rcases ContractSpecSem.GenericCreate.some_preserves_precond (c := c.toSem)
      h_run ex_sub h_ct_ne (pre_toSem h_pc) with ⟨hpre, hpost⟩
  exact ⟨pre_ofSem hpre, fun hp => by
    cases exn' with
    | error e => exact pre_ofSem (hpost trivial)
    | ok out => exact pre_ofSem (hpost (post_toSem hp))⟩


lemma Xinst.some_preserves_precond {wa : Adr} {sevm : Sevm} {devm inter : Devm} {x : Xinst}
    {evm' : Evm} {exn' : Execution}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : Xinst.Run sevm devm x (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  rcases ContractSpecSem.Xinst.some_preserves_precond (c := c.toSem)
      hfork h_run ex_sub h_ne (pre_toSem h_pc) with ⟨hpre, hpost⟩
  exact ⟨pre_ofSem hpre, fun hp => by
    cases exn' with
    | error e => exact pre_ofSem (hpost trivial)
    | ok out => exact pre_ofSem (hpost (post_toSem hp))⟩


lemma Post.selfdestruct_delete {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h_ne : sevm.currentTarget ≠ ca) (h_pc : c.Pre ca sevm devm) :
    c.Post ca sevm
      (addAccountToDelete (devm.setBal sevm.currentTarget 0) sevm.currentTarget) := by
  exact post_ofSem (ContractSpecSem.Post.selfdestruct_delete (c := c.toSem) h_ne (pre_toSem h_pc))

lemma Linst.inv_postcond {wa : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : Linst.Run sevm pre l (.ok post))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm pre) :
    c.Post wa sevm post := by
  exact post_ofSem (ContractSpecSem.Linst.inv_postcond (c := c.toSem) hfork h_run h_ne (pre_toSem h_pc))

def Sound (c : ContractSpec) (ca : Adr) : Prop :=
  ∀ {sevm pre post},
    CoveredFork sevm.benvStat.fork →
    Prog.Run sevm pre c.prog post →
    sevm.currentTarget = ca →
    ( ∀ pc' sevm' pre' post',
        Exec pc' sevm' pre' (.ok post') →
        sevm'.depth < sevm.depth →
        Prog.At c.prog ca pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        c.PreWf ca sevm' pre' →
        c.Post ca sevm' post' ) →
    Mem.Wf pre.memory →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- The same obligation for a contract whose targets never consult the memory
invariant: `Sound` without the `Mem.Wf` premise on the entry state.

This is the *stronger* obligation — it has to hold at an arbitrary entry
memory — and it is the one a contract that never reads memory should be
stating, because it is what buys the premise-free frame theorem
`preserves_noMem`.  `SoundNoMem.sound` weakens it back wherever a `Sound`
consumer is what is wanted.

The deeper-frame hypothesis is *not* weakened: it stays phrased at `PreWf`,
because that is what the ladder can deliver, and a re-entrant target consumes
it at a child frame whose memory is `initDevm`'s. -/
def SoundNoMem (c : ContractSpec) (ca : Adr) : Prop :=
  ∀ {sevm pre post},
    CoveredFork sevm.benvStat.fork →
    Prog.Run sevm pre c.prog post →
    sevm.currentTarget = ca →
    ( ∀ pc' sevm' pre' post',
        Exec pc' sevm' pre' (.ok post') →
        sevm'.depth < sevm.depth →
        Prog.At c.prog ca pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        c.PreWf ca sevm' pre' →
        c.Post ca sevm' post' ) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- Dropping a premise the obligation never used. -/
theorem SoundNoMem.sound {c : ContractSpec} {ca : Adr} (h : c.SoundNoMem ca) :
    c.Sound ca :=
  fun hfork h_run h_ca h_ih _ h_pre => h hfork h_run h_ca h_ih h_pre

/-- `Sound` with the memory premise left as a parameter.  `mw := Mem.Wf` is
`Sound`; `mw := fun _ => True` is `SoundNoMem` with the premise supplied by
`trivial`.  Only the generic dispatcher plumbing is stated at it, so that
`sound_of_dispatch` and `soundNoMem_of_dispatch` are one proof rather than
two; a contract states its own obligation at `Sound` or `SoundNoMem`. -/
def SoundWith (c : ContractSpec) (ca : Adr) (mw : Mem → Prop) : Prop :=
  ∀ {sevm pre post},
    CoveredFork sevm.benvStat.fork →
    Prog.Run sevm pre c.prog post →
    sevm.currentTarget = ca →
    ( ∀ pc' sevm' pre' post',
        Exec pc' sevm' pre' (.ok post') →
        sevm'.depth < sevm.depth →
        Prog.At c.prog ca pc' sevm' pre' →
        CoveredFork sevm'.benvStat.fork →
        c.PreWf ca sevm' pre' →
        c.Post ca sevm' post' ) →
    mw pre.memory →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- `SoundWith` at the trivial memory premise is `SoundNoMem`. -/
theorem SoundWith.soundNoMem {c : ContractSpec} {ca : Adr}
    (h : c.SoundWith ca (fun _ => True)) : c.SoundNoMem ca :=
  fun hfork h_run h_ca h_ih h_pre => h hfork h_run h_ca h_ih trivial h_pre

/-- What the frame-level ladder delivers, and what every rung above it
consumes.  `preserves_inv : c.Sound ca → c.Preserves ca`. -/
def Preserves (c : ContractSpec) (ca : Adr) : Prop :=
  ∀ sevm pre post,
    CoveredFork sevm.benvStat.fork →
    Exec 0 sevm pre (.ok post) →
    (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
    (sevm.currentTarget = ca → Mem.Wf pre.memory) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- What the frame-level ladder delivers for a contract that never reads
memory: `Preserves` with no memory premise at all, so an arbitrary successful
execution starting in the contract's frame is covered whatever the machine's
memory looks like.  `preserves_noMem : c.SoundNoMem ca → c.PreservesNoMem ca`,
and `PreservesNoMem.preserves` weakens it back for the message-, transaction-
and block-level rungs, every one of which consumes `c.Preserves ca`. -/
def PreservesNoMem (c : ContractSpec) (ca : Adr) : Prop :=
  ∀ sevm pre post,
    CoveredFork sevm.benvStat.fork →
    Exec 0 sevm pre (.ok post) →
    (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- Dropping a premise the frame theorem never used. -/
theorem PreservesNoMem.preserves {c : ContractSpec} {ca : Adr}
    (h : c.PreservesNoMem ca) : c.Preserves ca :=
  fun sevm pre post hfork exc h_code _ h_pre => h sevm pre post hfork exc h_code h_pre

def sound_toSem {c : ContractSpec} {ca : Adr} (h : c.Sound ca) :
    (c.toSem).Sound ca := by
  intro sevm pre post hfork hrun hca ih hwf hpre
  apply post_toSem
  apply h hfork hrun hca
  · intro pc' sevm' pre' post' hex hd hat hfork' hpw
    apply post_ofSem
    apply ih pc' sevm' pre' post' hex hd
      (by simpa [Prog.codeSem, CodeSem.At, Prog.At, ContractSpec.toSem] using hat) hfork'
      (preWf_toSem hpw)
  · exact hwf
  · exact pre_ofSem hpre

def soundNoMem_toSem {c : ContractSpec} {ca : Adr} (h : c.SoundNoMem ca) :
    (c.toSem).SoundNoMem ca := by
  intro sevm pre post hfork hrun hca ih hpre
  apply post_toSem
  apply h hfork hrun hca
  · intro pc' sevm' pre' post' hex hd hat hfork' hpw
    apply post_ofSem
    apply ih pc' sevm' pre' post' hex hd
      (by simpa [Prog.codeSem, CodeSem.At, Prog.At, ContractSpec.toSem] using hat) hfork'
      (preWf_toSem hpw)
  · exact pre_ofSem hpre

def preserves_toSem {c : ContractSpec} {ca : Adr} (h : c.Preserves ca) :
    (c.toSem).Preserves ca := by
  intro sevm pre post hfork hex hcode hwf hpre
  apply post_toSem
  apply h sevm pre post hfork hex
  · intro hca
    simpa [Prog.codeSem, ContractSpec.toSem] using hcode hca
  · exact hwf
  · exact pre_ofSem hpre

def preservesNoMem_toSem {c : ContractSpec} {ca : Adr}
    (h : c.PreservesNoMem ca) : (c.toSem).PreservesNoMem ca := by
  intro sevm pre post hfork hex hcode hpre
  apply post_toSem
  apply h sevm pre post hfork hex
  · intro hca
    simpa [Prog.codeSem, ContractSpec.toSem] using hcode hca
  · exact pre_ofSem hpre

def preserves_ofSem {c : ContractSpec} {ca : Adr}
    (h : (c.toSem).Preserves ca) : c.Preserves ca := by
  intro sevm pre post hfork hex hcode hwf hpre
  apply post_ofSem
  apply h sevm pre post hfork hex
  · intro hca
    simpa [Prog.codeSem, ContractSpec.toSem] using hcode hca
  · exact hwf
  · exact pre_toSem hpre

def preservesNoMem_ofSem {c : ContractSpec} {ca : Adr}
    (h : (c.toSem).PreservesNoMem ca) : c.PreservesNoMem ca := by
  intro sevm pre post hfork hex hcode hpre
  apply post_ofSem
  apply h sevm pre post hfork hex
  · intro hca
    simpa [Prog.codeSem, ContractSpec.toSem] using hcode hca
  · exact pre_toSem hpre

/-! ### The frame-level ladder

`lift_inv` (CommonProofs.lean) is already generic in the program and in the two
predicates; what was WETH-specific about `weth_preserves_solvent` was only the
five obligations fed to it.  Four of those are discharged here once and for
all, for every contract.  The fifth — that a top-level run of the contract's
own program takes the precondition to the postcondition — is the contract's
own work and stays a hypothesis.

`preserves_lift` does that work once, generic in the frame invariant `σ` that
`lift_inv` is instantiated at, because two instantiations are wanted:
`c.PreWf ca` for a contract that reasons about memory, and `c.Pre ca` for one
that does not.  The four ladder rungs are indifferent to the difference — each
re-establishes `σ` under `sevm.currentTarget ≠ ca`, where a memory conjunct is
vacuous, and the one rung that also has to produce `σ` at a *spawned child*
frame gets `Mem.Wf` outright from `Xinst.some_child_wf`.  So the three
transport hypotheses below are everything `σ` has to expose, and there is one
ladder proof rather than one per memory discipline. -/

theorem preserves_lift (c : ContractSpec) (ca : Adr)
    (σ : Sevm → Devm → Prop)
    (σ_pre : ∀ {e : Sevm} {d : Devm}, σ e d → c.Pre ca e d)
    (σ_of_ne : ∀ {e : Sevm} {d : Devm},
      e.currentTarget ≠ ca → c.Pre ca e d → σ e d)
    (σ_of_wf : ∀ {e : Sevm} {d : Devm},
      Mem.Wf d.memory → c.Pre ca e d → σ e d)
    ( body :
      ∀ {sevm pre post},
        Prog.Run sevm pre c.prog post →
        sevm.currentTarget = ca →
        ( ∀ pc' sevm' pre' post',
            Exec pc' sevm' pre' (.ok post') →
            sevm'.depth < sevm.depth →
            Prog.At c.prog ca pc' sevm' pre' →
            σ sevm' pre' ∧ CoveredFork sevm'.benvStat.fork →
            c.Post ca sevm' post' ) →
        σ sevm pre ∧ CoveredFork sevm.benvStat.fork →
        c.Post ca sevm post ) :
    ∀ sevm pre post,
      CoveredFork sevm.benvStat.fork →
      Exec 0 sevm pre (.ok post) →
      (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
      σ sevm pre →
      c.Post ca sevm post := by
  intro sevm pre post hfork exc h_code hσ
  apply post_ofSem
  apply ContractSpecSem.preserves_lift_sem c.toSem ca σ
    (fun h => pre_toSem (σ_pre h))
    (fun hne h => σ_of_ne hne (pre_ofSem h))
    (fun hwf h => σ_of_wf hwf (pre_ofSem h))
  · intro sevmg preg postg h_rung h_eqg h_ihg h_preg
    exact post_toSem (body h_rung h_eqg
      (fun pcg sevmg2 preg2 postg2 hex hd hat hpair =>
        post_ofSem (h_ihg pcg sevmg2 preg2 postg2 hex hd
          (by simpa [Prog.codeSem, CodeSem.At, Prog.At, ContractSpec.toSem] using hat)
          hpair))
      h_preg)
  · exact hfork
  · exact exc
  · intro hca
    simpa [ContractSpec.toSem, Prog.codeSem] using h_code hca
  · exact hσ

theorem preserves_inv (c : ContractSpec) (ca : Adr) (body : c.Sound ca) :
    c.Preserves ca :=
  preserves_ofSem (ContractSpecSem.preserves_inv_sem c.toSem ca
    (sound_toSem body))

/-- The premise-free frame-level ladder: the same `lift_inv` plumbing at
`σ := c.Pre ca`, so no memory premise is manufactured anywhere and none
reaches the frame theorem.  The obligation's deeper-frame hypothesis is still
phrased at `PreWf`, which is strictly less than what this instantiation
delivers, so it is weakened on the way in. -/
theorem preserves_noMem (c : ContractSpec) (ca : Adr) (body : c.SoundNoMem ca) :
    c.PreservesNoMem ca :=
  preservesNoMem_ofSem (ContractSpecSem.preserves_noMem_sem c.toSem ca
    (soundNoMem_toSem body))

/-- The `exec` counterpart: with sufficiency proved in Jaune there is no fuel
to quantify away, so the hypothesis is a plain equation about the interpreter. -/
theorem exec_preserves_inv (c : ContractSpec) (ca : Adr) (hp : c.Preserves ca)
    (sevm : Sevm) (pre post : Devm)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : exec ⟨0, sevm, pre⟩ = .ok post)
    (h_code : sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog)
    (h_wf : sevm.currentTarget = ca → Mem.Wf pre.memory)
    (h_pc : c.Pre ca sevm pre) : c.Post ca sevm post :=
  post_ofSem (ContractSpecSem.exec_preserves_inv_sem c.toSem ca
    (preserves_toSem hp) sevm pre post hfork h_run
    (by simpa [ContractSpec.toSem, Prog.codeSem] using h_code) h_wf
    (pre_toSem h_pc))
/-- The `exec` counterpart of `PreservesNoMem`, with no memory premise. -/
theorem exec_preserves_noMem (c : ContractSpec) (ca : Adr)
    (hp : c.PreservesNoMem ca)
    (sevm : Sevm) (pre post : Devm)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_run : exec ⟨0, sevm, pre⟩ = .ok post)
    (h_code : sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog)
    (h_pc : c.Pre ca sevm pre) : c.Post ca sevm post :=
  post_ofSem (ContractSpecSem.exec_preserves_noMem_sem c.toSem ca
    (preservesNoMem_toSem hp) sevm pre post hfork h_run
    (by simpa [ContractSpec.toSem, Prog.codeSem] using h_code)
    (pre_toSem h_pc))


/-! ### The dispatcher decomposition of `Sound`

The plain Blanc dispatch protocol has program shape
`⟨Func.mainWith k (DispatchTree.ofSorted funcs), aux⟩`; receive-aware contracts
put one empty-calldata branch in front of that same dispatcher.  The reasoning
that carries a run from `fsig` down to one of its dispatch targets is shared in
full by `post_of_run_dispatch_with`.  `sound_of_dispatch_with` absorbs the plain
`Prog.Run`/`call 0` unwrap and `fsig` prefix, while
`sound_of_receive_dispatch_with` also absorbs the receive split.  All three
reuse `dispatchWith_inv`'s two scratch-line side conditions and its tree-shaped
membership obligation, and leave a contract with one per-target obligation per
entry of its own function *list*, plus one for the fallback at index `k`.

All three are generic in the memory premise `mw`, which the dispatch walk
transports along line and pop steps but never inspects.  `sound_of_dispatch`
and `sound_of_receive_dispatch` are the `Mem.Wf` instances — `FuncSound` in,
`Sound` out — and `soundNoMem_of_dispatch` and `soundNoMem_of_receive_dispatch`
are the trivial ones — `FuncSoundNoMem` in, `SoundNoMem` out, which is the
route to a frame theorem with no memory premise.

Two notes on the hypotheses, both results rather than bookkeeping:

* **There is no sortedness hypothesis.**  `Sound` is a safety property, and
  sortedness governs reachability, not safety: a misordered list makes some
  target unreachable, which cannot make the dispatcher unsound.  The one step
  that might plausibly have consumed it — turning tree membership into list
  membership — needs only `funcs ≠ []`, by
  `DispatchTree.mem_of_mem_ofSorted`.  Pair `DispatchTree.sorted` with a
  contract to get reachability; it is not needed for soundness.

* **`fsig` is discharged field-wise, not through `Devm.state`.**  The three
  dispatcher obligations below are all one argument — the world state did not
  change, so the precondition survives — via `Line.Inv Devm.state` and
  `Pre.state_eq`.  `fsig` is not: `line_inv` cannot prove
  `Line.Inv Devm.state fsig`, because the `Ninst.Hinv Devm.state` family has
  members only for the scratch instructions (`pushB256`, `eq`, `dup`, `gt`) and
  none for `calldataload` or `shr`.  It needs no hypothesis of its own either —
  `Pre.of_eqs` transports the precondition along the three field observables,
  each of which `line_inv` does prove across `fsig`. -/

/-- The per-function obligation left by `sound_of_dispatch`: `f`'s walk takes
the contract's precondition to its postcondition, given the entry state the
dispatcher hands it and the induction hypothesis for deeper frames.  That
induction hypothesis is part of the entry condition and is not optional — a
target that re-enters the contract (WETH's `withdraw`) genuinely consumes it.

The frame is executing the contract itself (`sevm.currentTarget = ca`); this is
`Sound`'s own hypothesis, carried down to the targets.  It is what lets a
contract state its per-function lemmas at `sevm.currentTarget`, as WETH's ten
do, instead of restating them at an abstract address.

Stated relative to the program's aux context rather than to `c.prog.aux`,
because `Func.call` indices are positional: a lemma relating
`FuncSound c ca aux f` to `FuncSound c' ca (aux ++ extra) f` is what would make
an extension's obligations reusable, and it wants `aux` in hand. -/
def FuncSound (c : ContractSpec) (ca : Adr) (aux : List Func) (f : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    CoveredFork sevm.benvStat.fork →
    sevm.currentTarget = ca →
    c.Pre ca sevm s →
    Mem.Wf s.memory →
    Exec.InvDepth sevm.depth ca c.prog (c.PreWf ca) (c.Post ca) →
    Func.Run (c.prog.main :: aux) sevm s f r →
    c.Post ca sevm r

/-- The same obligation for a target that never consults the memory invariant.

`FuncSound` hands a target `Mem.Wf` for its entry state; that is what makes a
memory-reasoning obligation statable at all.  But the invariant does not ride
across an intervening walk for free: a wrapper that *writes* memory (WETH10's
allowance spending writes two scratch words and hashes them) has to
re-establish it through `Mem.Wf.write`/`.extend` before it can hand it on.  A
family of targets that never reads the invariant should not have to pay for
that transport, and — more to the point — a contract all of whose targets are
stated here assembles to `SoundNoMem`, hence to the premise-free frame theorem
`PreservesNoMem`.  This is the stronger of the two obligations: it has to hold
at an arbitrary entry memory.

The deeper-frame hypothesis is *not* weakened: it stays phrased at `PreWf`,
because that is what the ladder can deliver, and a re-entrant target consumes
it at a child frame whose memory is `initDevm`'s. -/
def FuncSoundNoMem (c : ContractSpec) (ca : Adr) (aux : List Func) (f : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    CoveredFork sevm.benvStat.fork →
    sevm.currentTarget = ca →
    c.Pre ca sevm s →
    Exec.InvDepth sevm.depth ca c.prog (c.PreWf ca) (c.Post ca) →
    Func.Run (c.prog.main :: aux) sevm s f r →
    c.Post ca sevm r

/-- Dropping a premise the obligation never used.  `funcSound_of_core` is the
in-tree consumer: a storage-only target's obligation is established at
`FuncSoundNoMem`, where it belongs, and weakened here for callers (Lido's
storage-silent leaves) that want the memory-carrying form. -/
theorem FuncSoundNoMem.funcSound {c : ContractSpec} {ca : Adr}
    {aux : List Func} {f : Func} (h : c.FuncSoundNoMem ca aux f) :
    c.FuncSound ca aux f :=
  fun hfork h_ct h_pre _ h_ih h_run => h hfork h_ct h_pre h_ih h_run

/-- `FuncSound` with the memory premise left as a parameter; the per-target
counterpart of `SoundWith`, and the form the generic dispatcher plumbing
consumes so that the memory-carrying and premise-free dispatch theorems share
a single proof. -/
def FuncSoundWith (c : ContractSpec) (ca : Adr) (aux : List Func)
    (mw : Mem → Prop) (f : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    CoveredFork sevm.benvStat.fork →
    sevm.currentTarget = ca →
    c.Pre ca sevm s →
    mw s.memory →
    Exec.InvDepth sevm.depth ca c.prog (c.PreWf ca) (c.Post ca) →
    Func.Run (c.prog.main :: aux) sevm s f r →
    c.Post ca sevm r

/-- A target that never reads memory meets the parameterised obligation at
*every* memory premise, the trivial one included. -/
theorem FuncSoundNoMem.funcSoundWith {c : ContractSpec} {ca : Adr}
    {aux : List Func} {mw : Mem → Prop} {f : Func}
    (h : c.FuncSoundNoMem ca aux f) : c.FuncSoundWith ca aux mw f :=
  fun hfork h_ct h_pre _ h_ih h_run => h hfork h_ct h_pre h_ih h_run

/-- The contract-neutral core of dispatcher soundness.  Starting immediately
after `fsig`, a successful walk through a generated dispatch tree reaches
either its indexed fallback or one of the listed targets.  Keeping this as a
run-level theorem lets alternate public ingress shapes (notably a payable
empty-calldata receive branch) share the exact selector/fallback proof.

Generic in the memory premise `mw`: the walk only ever *transports* it along
line and pop steps, never inspects it, so the memory-carrying and premise-free
dispatch theorems are this one proof at two instantiations. -/
theorem post_of_run_dispatch_with {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    {mw : Mem → Prop}
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSoundWith c ca aux mw p.2)
    (h_fall : FuncSoundWith c ca aux mw fallback)
    {sevm : Sevm} {s r : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_ca : sevm.currentTarget = ca)
    (h_pre : c.Pre ca sevm s)
    (h_wf : mw s.memory)
    (h_ih : Exec.InvDepth sevm.depth ca c.prog (c.PreWf ca) (c.Post ca))
    (h_run :
      Func.Run (c.prog.main :: aux) sevm s
        (dispatchWith k (DispatchTree.ofSorted funcs)) r) :
    c.Post ca sevm r := by
  apply
    ( @dispatchWith_inv
        (c.prog.main :: aux) k fallback
        ( fun e s =>
            e.currentTarget = ca ∧
            c.Pre ca e s ∧
            mw s.memory ∧
            Exec.InvDepth e.depth ca c.prog (c.PreWf ca) (c.Post ca) ∧
            CoveredFork e.benvStat.fork )
        (fun e r => c.Post ca e r)
        ?_ ?_ h_fb ?_ (DispatchTree.ofSorted funcs) ?_
        sevm s r ⟨h_ca, h_pre, h_wf, h_ih, hfork⟩ h_run )
  · intro e s x w s' s'' ⟨h_ct, hp, hmw, hih, hfork_e⟩ hline hpop
    refine ⟨h_ct, ?_, ?_, hih, hfork_e⟩
    · have h_state : s.state = s'.state :=
        Line.of_inv Devm.state (by line_inv) hline
      exact hp.state_eq (hpop.state.symm.trans h_state.symm)
    · have h_mem : s.memory = s''.memory :=
        (Line.of_inv Devm.memory (by line_inv) hline).trans hpop.memory
      rw [← h_mem]; exact hmw
  · intro e s x w s' s'' ⟨h_ct, hp, hmw, hih, hfork_e⟩ hline hpop
    refine ⟨h_ct, ?_, ?_, hih, hfork_e⟩
    · have h_state : s.state = s'.state :=
        Line.of_inv Devm.state (by line_inv) hline
      exact hp.state_eq (hpop.state.symm.trans h_state.symm)
    · have h_mem : s.memory = s''.memory :=
        (Line.of_inv Devm.memory (by line_inv) hline).trans hpop.memory
      rw [← h_mem]; exact hmw
  · intro e s s' r ⟨h_ct, hp, hmw, hih, hfork_e⟩ hburn hrun
    exact h_fall hfork_e h_ct (hp.state_eq hburn.state.symm) (hburn.memory ▸ hmw) hih hrun
  · intro e s r wf h_mem ⟨h_ct, hp, hmw, hih, hfork_e⟩ hrun
    exact h_funcs wf (DispatchTree.mem_of_mem_ofSorted h_ne h_mem)
      hfork_e h_ct hp hmw hih hrun

/-- The memory-carrying instance of `post_of_run_dispatch_with`. -/
theorem post_of_run_dispatch {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSound c ca aux p.2)
    (h_fall : FuncSound c ca aux fallback)
    {sevm : Sevm} {s r : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_ca : sevm.currentTarget = ca)
    (h_pre : c.Pre ca sevm s)
    (h_wf : Mem.Wf s.memory)
    (h_ih : Exec.InvDepth sevm.depth ca c.prog (c.PreWf ca) (c.Post ca))
    (h_run :
      Func.Run (c.prog.main :: aux) sevm s
        (dispatchWith k (DispatchTree.ofSorted funcs)) r) :
    c.Post ca sevm r :=
  post_of_run_dispatch_with (mw := Mem.Wf) h_ne h_fb (fun p hp => h_funcs p hp)
    h_fall hfork h_ca h_pre h_wf h_ih h_run

/-- `SoundWith` for a dispatcher-shaped program, reduced to one per-target
obligation plus one for the fallback.  `h_fb` locates the fallback at the
index the generated `Func.call k` uses; at a concrete contract it is `rfl`. -/
theorem sound_of_dispatch_with {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    {mw : Mem → Prop}
    (h_shape : c.prog = ⟨Func.mainWith k (DispatchTree.ofSorted funcs), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSoundWith c ca aux mw p.2)
    (h_fall : FuncSoundWith c ca aux mw fallback) :
    c.SoundWith ca mw := by
  have h_aux : c.prog.aux = aux := by rw [h_shape]
  have h_main : c.prog.main = Func.mainWith k (DispatchTree.ofSorted funcs) := by rw [h_shape]
  have h_fs : Func.mainWith k (DispatchTree.ofSorted funcs) :: aux = c.prog.main :: aux := by
    rw [h_main]
  intro sevm pre post hfork run h_ca ih h_wf h_pre
  -- `Sound` hands the deeper-frame hypothesis in its raw form; every consumer
  -- below wants the `ifOk`-wrapped one.
  have ih' : Exec.InvDepth sevm.depth ca c.prog (c.PreWf ca) (c.Post ca) := by
    intro pc' sevm' devm' exn'
    cases exn'
    · simp only [ifOk, implies_true]
    · apply ih
  clear ih
  -- unwrap the initial `call 0` into a run of the program's own `main`
  dsimp only [Prog.Run] at run
  rw [h_aux] at run
  cases run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases h_eq
  have h_pre₀ : c.Pre ca sevm s₀ := h_pre.state_eq burn.state.symm
  have h_wf₀ : mw s₀.memory := by rw [← burn.memory]; exact h_wf
  clear h_pre h_wf burn pre
  rw [h_main] at run
  -- run off the `fsig` prefix of `Func.mainWith`
  refine run_prepend_elim _ fsig ?_ run
  intro s₁ h₁ run₁
  have h_pre₁ : c.Pre ca sevm s₁ :=
    h_pre₀.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) h₁).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) h₁).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) h₁).symm ca)
  have h_wf₁ : mw s₁.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) h₁]; exact h_wf₀
  clear h_pre₀ h_wf₀ h₁ run s₀
  rw [h_fs] at run₁
  exact post_of_run_dispatch_with h_ne h_fb h_funcs h_fall hfork h_ca h_pre₁ h_wf₁ ih' run₁

/-- `Sound` for a dispatcher-shaped program, reduced to one `FuncSound` per
dispatch target plus one for the fallback. -/
theorem sound_of_dispatch {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    (h_shape : c.prog = ⟨Func.mainWith k (DispatchTree.ofSorted funcs), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSound c ca aux p.2)
    (h_fall : FuncSound c ca aux fallback) :
    c.Sound ca :=
  sound_of_dispatch_with (mw := Mem.Wf) h_shape h_ne h_fb
    (fun p hp => h_funcs p hp) h_fall

/-- `SoundNoMem` for a dispatcher-shaped program, reduced to one
`FuncSoundNoMem` per dispatch target plus one for the fallback.  This is the
route to the premise-free frame theorem. -/
theorem soundNoMem_of_dispatch {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    (h_shape : c.prog = ⟨Func.mainWith k (DispatchTree.ofSorted funcs), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSoundNoMem c ca aux p.2)
    (h_fall : FuncSoundNoMem c ca aux fallback) :
    c.SoundNoMem ca :=
  SoundWith.soundNoMem
    (sound_of_dispatch_with (mw := fun _ => True) h_shape h_ne h_fb
      (fun p hp => FuncSoundNoMem.funcSoundWith (mw := fun _ => True) (h_funcs p hp))
      (FuncSoundNoMem.funcSoundWith (mw := fun _ => True) h_fall))

/-- `SoundWith` for the receive-aware public ingress used by
wrapped-native-token contracts.  Empty calldata takes `receive`; nonempty
calldata runs the same `fsig`/generated-dispatch protocol as
`sound_of_dispatch_with`.  Successful receive, fallback, and selector walks are
reduced uniformly to the per-target obligation. -/
theorem sound_of_receive_dispatch_with {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func}
    {fallback receive : Func} {mw : Mem → Prop}
    (h_shape : c.prog =
      ⟨Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs))), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSoundWith c ca aux mw p.2)
    (h_fall : FuncSoundWith c ca aux mw fallback)
    (h_receive : FuncSoundWith c ca aux mw receive) :
    c.SoundWith ca mw := by
  have h_aux : c.prog.aux = aux := by rw [h_shape]
  have h_main : c.prog.main =
      Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs))) := by
    rw [h_shape]
  have h_ctx :
      (Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs)))) :: aux =
        c.prog.main :: aux := by
    rw [h_main]
  intro sevm pre post hfork run h_ca ih h_wf h_pre
  have ih' : Exec.InvDepth sevm.depth ca c.prog (c.PreWf ca) (c.Post ca) := by
    intro pc' sevm' devm' exn'
    cases exn'
    · simp only [ifOk, implies_true]
    · apply ih
  clear ih
  dsimp only [Prog.Run] at run
  rw [h_aux] at run
  cases run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases h_eq
  have h_pre₀ : c.Pre ca sevm s₀ := h_pre.state_eq burn.state.symm
  have h_wf₀ : mw s₀.memory := by rw [← burn.memory]; exact h_wf
  clear h_pre h_wf burn pre
  rw [h_main] at run
  refine run_prepend_elim _ [Ninst.calldatasize, Ninst.iszero] ?_ run
  intro s₁ h₁ run₁
  have h_pre₁ : c.Pre ca sevm s₁ :=
    h_pre₀.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) h₁).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) h₁).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) h₁).symm ca)
  have h_wf₁ : mw s₁.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) h₁]; exact h_wf₀
  clear h_pre₀ h_wf₀ h₁ run s₀
  rcases of_run_branch run₁ with
    ⟨s₂, h_pop, h_dispatch⟩ |
    ⟨w, s₂, s₃, h_ne_zero, h_pop, h_burn, h_receive_run⟩
  · rw [h_ctx] at h_dispatch
    refine run_prepend_elim _ fsig ?_ h_dispatch
    intro s₃ h_fsig h_dispatch'
    have h_pre₃ : c.Pre ca sevm s₃ :=
      (h_pre₁.state_eq h_pop.state.symm).of_eqs
        (congrFun (Line.of_inv Devm.getCode (by line_inv) h_fsig).symm ca)
        (Line.of_inv Devm.getBal (by line_inv) h_fsig).symm
        (congrFun (Line.of_inv Devm.getStor (by line_inv) h_fsig).symm ca)
    have h_wf₃ : mw s₃.memory := by
      rw [← Line.of_inv Devm.memory (by line_inv) h_fsig, ← h_pop.memory]
      exact h_wf₁
    exact post_of_run_dispatch_with h_ne h_fb h_funcs h_fall hfork
      h_ca h_pre₃ h_wf₃ ih' h_dispatch'
  · rw [h_ctx] at h_receive_run
    refine h_receive hfork h_ca
      (h_pre₁.state_eq (h_burn.state.symm.trans h_pop.state.symm))
      ?_ ih' h_receive_run
    rw [← h_burn.memory, ← h_pop.memory]; exact h_wf₁

/-- `Sound` for the receive-aware public ingress, at `FuncSound`. -/
theorem sound_of_receive_dispatch {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func}
    {fallback receive : Func}
    (h_shape : c.prog =
      ⟨Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs))), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSound c ca aux p.2)
    (h_fall : FuncSound c ca aux fallback)
    (h_receive : FuncSound c ca aux receive) :
    c.Sound ca :=
  sound_of_receive_dispatch_with (mw := Mem.Wf) h_shape h_ne h_fb
    (fun p hp => h_funcs p hp) h_fall h_receive

/-- `SoundNoMem` for the receive-aware public ingress, at `FuncSoundNoMem`:
the route to the premise-free frame theorem for a receive-aware contract whose
targets never read memory. -/
theorem soundNoMem_of_receive_dispatch {c : ContractSpec} {ca : Adr} {k : Nat}
    {funcs : List (B256 × Func)} {aux : List Func}
    {fallback receive : Func}
    (h_shape : c.prog =
      ⟨Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs))), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, FuncSoundNoMem c ca aux p.2)
    (h_fall : FuncSoundNoMem c ca aux fallback)
    (h_receive : FuncSoundNoMem c ca aux receive) :
    c.SoundNoMem ca :=
  SoundWith.soundNoMem
    (sound_of_receive_dispatch_with (mw := fun _ => True) h_shape h_ne h_fb
      (fun p hp => FuncSoundNoMem.funcSoundWith (mw := fun _ => True) (h_funcs p hp))
      (FuncSoundNoMem.funcSoundWith (mw := fun _ => True) h_fall)
      (FuncSoundNoMem.funcSoundWith (mw := fun _ => True) h_receive))



theorem StateInv.incrNonce {wa a : Adr} {w : Jaune.State}
    (h : c.StateInv wa w) : c.StateInv wa (w.incrNonce a) := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.incrNonce (c := c.toSem) (stateInv_toSem h))

theorem StateInv.addBal {ca a : Adr} {val : B256} {w : Jaune.State}
    (hsum : sum w.bal + val.toNat < 2 ^ 256)
    (h : c.StateInv ca w) : c.StateInv ca (w.addBal a val) := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.addBal (c := c.toSem) hsum (stateInv_toSem h))

theorem StateInv.subBal {ca a : Adr} {val : B256} {w w' : Jaune.State}
    (hne : a ≠ ca) (h_sub : w.subBal a val = some w')
    (h : c.StateInv ca w) : c.StateInv ca w' := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.subBal (c := c.toSem) hne h_sub (stateInv_toSem h))

theorem StateInv.destroyAccount {ca a : Adr} {w : Jaune.State}
    (hne : a ≠ ca) (h : c.StateInv ca w) : c.StateInv ca (destroyAccount w a) := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.destroyAccount (c := c.toSem) hne (stateInv_toSem h))

theorem StateInv.foldl_destroyAccount {wa : Adr} :
    ∀ {as : List Adr} {w : Jaune.State},
      (∀ a ∈ as, a ≠ wa) → c.StateInv wa w →
        c.StateInv wa (as.foldl Jaune.destroyAccount w)
  | [], _, _, h => h
  | a :: as, w, hne, h => by
    exact stateInv_ofSem (ContractSpecSem.StateInv.foldl_destroyAccount
      (c := c.toSem) hne (stateInv_toSem h))

-- `Devm.get{Bal,Stor,Code}` are by definition the corresponding `State.*`
-- projections of `devm.state`, so a `Post` plus code-preservation is exactly
-- `StateInv` on the underlying state.
lemma StateInv.of_postcond {ca : Adr} {sevm : Sevm} {devm : Devm}
    (h_post : c.Post ca sevm devm)
    (h_code : some (devm.state.getCode ca).toList = Prog.compile c.prog) :
    c.StateInv ca devm.state := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.of_postcond (c := c.toSem) (post_toSem h_post) (by simpa [ContractSpec.toSem, Prog.codeSem] using h_code))

lemma Pre.of_inv_transfer {ca : Adr} {sevm' : Sevm} {devm' : Devm}
    {st st_mid : Jaune.State} {caller target : Adr} {value : B256}
    (h_inv : c.StateInv ca st)
    (h_ne : caller ≠ ca)
    (h_sub : st.subBal caller value = some st_mid)
    (h_state : devm'.state = st_mid.addBal target value)
    (h_ct' : sevm'.currentTarget = target)
    (h_val : sevm'.currentTarget = ca → sevm'.value = value) :
    c.Pre ca sevm' devm' := by
  exact pre_ofSem (ContractSpecSem.Pre.of_inv_transfer (c := c.toSem)
    (stateInv_toSem h_inv) h_ne h_sub h_state h_ct' h_val)

-- No-transfer counterpart of `Pre.of_inv_transfer`: when no value moves,
-- the pre-state is the invariant state itself, and `PreSolvent` reduces to the
-- value-free solvency provided `value = 0` whenever the frame targets `wa`.
lemma Pre.of_inv_eqs {wa : Adr} {sevm : Sevm} {devm : Devm}
    (h_inv : c.StateInv wa devm.state)
    (h_val0 : sevm.currentTarget = wa → sevm.value = 0) :
    c.Pre wa sevm devm := by
  exact pre_ofSem (ContractSpecSem.Pre.of_inv_eqs (c := c.toSem) (stateInv_toSem h_inv) h_val0)

lemma Pre.of_inv_benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)
    (hb : msg.benvAfterTransfer = .ok benv)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.Pre wa (initSevm (msg.withBenv benv)) (initDevm (msg.withBenv benv)) := by
  exact pre_ofSem (ContractSpecSem.Pre.of_inv_benvAfterTransfer (c := c.toSem)
    h_ne h_val0 hb (stateInv_toSem h_inv))

-- The post-transfer state itself still satisfies `StateInv`: the transfer only
-- credits `ca` or moves value between accounts other than `ca`, which is
-- exactly what `side_transfer` and `inv_transfer` say.
lemma StateInv.of_benvAfterTransfer {ca : Adr} {msg : Msg} {benv : Benv}
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (hb : msg.benvAfterTransfer = .ok benv)
    (h_inv : c.StateInv ca msg.benv.state) :
    c.StateInv ca benv.state := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.of_benvAfterTransfer
    (c := c.toSem) h_ne hb (stateInv_toSem h_inv))

lemma StateInv.setStor_ne {wa a : Adr} {s : Stor} {w : Jaune.State}
    (hne : a ≠ wa) (h : c.StateInv wa w) : c.StateInv wa (w.setStor a s) := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.setStor_ne (c := c.toSem) hne (stateInv_toSem h))

lemma StateInv.setCode_ne {wa a : Adr} {cd : ByteArray} {w : Jaune.State}
    (hne : a ≠ wa) (h : c.StateInv wa w) : c.StateInv wa (w.setCode a cd) := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.setCode_ne (c := c.toSem) hne (stateInv_toSem h))

end ContractSpec

namespace ContractSpec

/-- **The quantified open-contract statement**: the invariant of any
dispatcher-shaped program all of whose targets satisfy `FuncSound` is
preserved by arbitrary executions — including arbitrary reentrant callback
code, which is what `FuncSound`'s deeper-frame hypothesis carries.
`sound_of_dispatch` composed with `preserves_inv`; fmint instantiates it
(`Blanc/Conserved.lean`, `fmintSpec_preserves`) with twelve discharged
obligations and a vacuous fallback. -/
theorem preserves_of_dispatch {c : ContractSpec} {ca : Adr}
    {k : Nat} {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    (h_shape : c.prog = ⟨Func.mainWith k (DispatchTree.ofSorted funcs), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, c.FuncSound ca aux p.2)
    (h_fall : c.FuncSound ca aux fallback) :
    c.Preserves ca :=
  c.preserves_inv ca (sound_of_dispatch h_shape h_ne h_fb h_funcs h_fall)

/-- The premise-free counterpart of `preserves_of_dispatch`: with every target
stated at `FuncSoundNoMem`, the frame theorem carries no memory premise at
all.  `PreservesNoMem.preserves` recovers `preserves_of_dispatch`'s conclusion
for the rungs above. -/
theorem preservesNoMem_of_dispatch {c : ContractSpec} {ca : Adr}
    {k : Nat} {funcs : List (B256 × Func)} {aux : List Func} {fallback : Func}
    (h_shape : c.prog = ⟨Func.mainWith k (DispatchTree.ofSorted funcs), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, c.FuncSoundNoMem ca aux p.2)
    (h_fall : c.FuncSoundNoMem ca aux fallback) :
    c.PreservesNoMem ca :=
  c.preserves_noMem ca (soundNoMem_of_dispatch h_shape h_ne h_fb h_funcs h_fall)

/-- The receive-aware counterpart of `preserves_of_dispatch`.  It adds exactly
one contract obligation: `FuncSound` for the empty-calldata receive target. -/
theorem preserves_of_receive_dispatch {c : ContractSpec} {ca : Adr}
    {k : Nat} {funcs : List (B256 × Func)} {aux : List Func}
    {fallback receive : Func}
    (h_shape : c.prog =
      ⟨Ninst.calldatasize ::: Ninst.iszero :::
        (receive <?>
          (fsig +++ dispatchWith k (DispatchTree.ofSorted funcs))), aux⟩)
    (h_ne : funcs ≠ [])
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_funcs : ∀ p ∈ funcs, c.FuncSound ca aux p.2)
    (h_fall : c.FuncSound ca aux fallback)
    (h_receive : c.FuncSound ca aux receive) :
    c.Preserves ca :=
  c.preserves_inv ca
    (sound_of_receive_dispatch h_shape h_ne h_fb h_funcs h_fall h_receive)

/-- A storage-only invariant's per-target obligation is exactly its
program-free core: for a spec whose `Side` is trivial and whose `Inv`
ignores the callvalue and balance arguments, `FuncSoundNoMem` follows from
`Func.Core` alone.  This is how a transported core re-enters the extended
contract's obligations without a re-walk.  It lands at `FuncSoundNoMem`
because a program-free core cannot read memory: nothing here needs the
entry-memory premise, so nothing here should charge for it. -/
theorem funcSoundNoMem_of_core {c : ContractSpec} {ca : Adr}
    {aux : List Func} {f : Func}
    (h_side : ∀ bal, c.Side bal)
    (h_stor : ∀ {s : Stor} {v b v' b' : B256}, c.Inv s v b → c.Inv s v' b')
    (h_core : Func.Core (c.prog.main :: aux) (fun st => c.Inv st 0 0) f) :
    c.FuncSoundNoMem ca aux f := by
  intro sevm s r _ h_ct h_pre _ h_run
  subst h_ct
  exact ⟨h_side _, h_stor (h_core h_run (h_stor (h_pre.inv.1 rfl)))⟩

/-- `funcSoundNoMem_of_core` weakened to the memory-carrying obligation. -/
theorem funcSound_of_core {c : ContractSpec} {ca : Adr}
    {aux : List Func} {f : Func}
    (h_side : ∀ bal, c.Side bal)
    (h_stor : ∀ {s : Stor} {v b v' b' : B256}, c.Inv s v b → c.Inv s v' b')
    (h_core : Func.Core (c.prog.main :: aux) (fun st => c.Inv st 0 0) f) :
    c.FuncSound ca aux f :=
  FuncSoundNoMem.funcSound (funcSoundNoMem_of_core h_side h_stor h_core)

end ContractSpec

namespace ContractSpec

/-! ### The message- and block-environment forms of the invariant

The generic counterparts of `Blanc.Msg.InvSolvent` and `Blanc.Benv.InvSolvent`. -/

structure MsgInv (c : ContractSpec) (wa : Adr) (msg : Msg) : Prop where
  (state : c.StateInv wa msg.benv.state)
  (nodel : Msg.NoDel wa msg)
  (code : msg.target.isNone = false → msg.currentTarget = wa →
    some msg.code.toList = Prog.compile c.prog)
  (codeAddress : msg.target.isNone = false → msg.currentTarget = wa →
    msg.codeAddress = some wa)
  (ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
  (val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)

structure BenvInv (c : ContractSpec) (wa : Adr) (benv : Benv) : Prop where
  (state : c.StateInv wa benv.state)
  (ca : wa ∉ benv.createdAccounts)

def msgInv_toSem {c : ContractSpec} {wa : Adr} {msg : Msg}
    (h : c.MsgInv wa msg) : (c.toSem).MsgInv wa msg :=
  { state := stateInv_toSem h.state
    nodel := h.nodel
    code := by simpa [ContractSpec.toSem, Prog.codeSem] using h.code
    codeAddress := h.codeAddress
    ne := h.ne
    val0 := h.val0 }

def msgInv_ofSem {c : ContractSpec} {wa : Adr} {msg : Msg}
    (h : (c.toSem).MsgInv wa msg) : c.MsgInv wa msg :=
  { state := stateInv_ofSem h.state
    nodel := h.nodel
    code := by simpa [ContractSpec.toSem, Prog.codeSem] using h.code
    codeAddress := h.codeAddress
    ne := h.ne
    val0 := h.val0 }

def benvInv_toSem {c : ContractSpec} {wa : Adr} {benv : Benv}
    (h : c.BenvInv wa benv) : (c.toSem).BenvInv wa benv :=
  ⟨stateInv_toSem h.state, h.ca⟩

def benvInv_ofSem {c : ContractSpec} {wa : Adr} {benv : Benv}
    (h : (c.toSem).BenvInv wa benv) : c.BenvInv wa benv :=
  ⟨stateInv_ofSem h.state, h.ca⟩

variable {c : ContractSpec}

lemma StateInv.of_exec_precond {wa : Adr} {sevm : Sevm} {pre post : Devm}
    (hp : c.Preserves wa)
    (hfork : CoveredFork sevm.benvStat.fork)
    (h_pc : c.Pre wa sevm pre)
    (h_code : sevm.currentTarget = wa → some sevm.code.toList = Prog.compile c.prog)
    (h_wf : sevm.currentTarget = wa → Mem.Wf pre.memory)
    (exc : Exec 0 sevm pre (.ok post)) :
    c.StateInv wa post.state := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.of_exec_precond (c := c.toSem)
    (preserves_toSem hp) hfork (pre_toSem h_pc)
    (by simpa [ContractSpec.toSem, Prog.codeSem] using h_code) h_wf exc)

theorem processMessage_preserves_inv {wa : Adr} {msg : Msg} {evm : Devm}
    (hfork : CoveredFork msg.benv.stat.fork)
    (hp : c.Preserves wa)
    (h_run : processMessage msg = .ok evm)
    (h_code : msg.currentTarget = wa → some msg.code.toList = Prog.compile c.prog)
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_val0 : msg.shouldTransferValue = false → msg.currentTarget = wa → msg.value = 0)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa evm.state := by
  exact stateInv_ofSem (ContractSpecSem.processMessage_preserves_inv (c := c.toSem)
    hfork (preserves_toSem hp) h_run
    (by simpa [ContractSpec.toSem, Prog.codeSem] using h_code) h_ne h_val0
    (stateInv_toSem h_inv))

theorem processCreateMessage_preserves_inv {wa : Adr} {msg : Msg} {evm : Devm}
    (hfork : CoveredFork msg.benv.stat.fork)
    (hp : c.Preserves wa)
    (h_run : processCreateMessage msg = .ok evm)
    (h_ct_ne : msg.currentTarget ≠ wa)
    (h_ne : msg.shouldTransferValue = true → msg.caller ≠ wa)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa evm.state := by
  exact stateInv_ofSem (ContractSpecSem.processCreateMessage_preserves_inv (c := c.toSem)
    hfork (preserves_toSem hp) h_run h_ct_ne h_ne (stateInv_toSem h_inv))

lemma setDelegationStep_preserves_inv {wa : Adr} {auth : Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationStep auth msg refund = .ok (msg', refund'))
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa msg'.benv.state := by
  exact stateInv_ofSem (ContractSpecSem.setDelegationStep_preserves_inv (c := c.toSem)
    h_run (stateInv_toSem h_inv))

lemma setDelegationLoop_preserves_inv {wa : Adr} {auths : List Auth} {msg msg' : Msg}
    {refund refund' : B256}
    (h_run : setDelegationLoop auths msg refund = .ok (msg', refund'))
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa msg'.benv.state := by
  exact stateInv_ofSem (ContractSpecSem.setDelegationLoop_preserves_inv (c := c.toSem)
    h_run (stateInv_toSem h_inv))

lemma setDelegation_preserves_inv {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h_inv : c.StateInv wa msg.benv.state) :
    c.StateInv wa msg'.benv.state := by
  exact stateInv_ofSem (ContractSpecSem.setDelegation_preserves_inv (c := c.toSem)
    h_run (stateInv_toSem h_inv))

lemma MsgInv.pc {wa : Adr} {msg : Msg} {codeSrc : Adr → ByteArray}
    (h : c.MsgInv wa msg) :
    c.MsgInv wa
      (match getDelegatedCodeAddress msg.code with
      | none => msg
      | some dca =>
        { msg with
          disablePrecompiles := true,
          accessedAddresses := msg.accessedAddresses.insert dca,
          code := codeSrc dca,
          codeAddress := some dca }) := by
  exact msgInv_ofSem (ContractSpecSem.MsgInv.pc (c := c.toSem)
    (codeSrc := codeSrc) (msgInv_toSem h))

lemma setDelegation_preserves_msgInv {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h : c.MsgInv wa msg) :
    c.MsgInv wa msg' := by
  exact msgInv_ofSem (ContractSpecSem.setDelegation_preserves_msgInv (c := c.toSem)
    h_run (msgInv_toSem h))

theorem processMessageCall_preserves_inv {wa : Adr} {msg : Msg} {st' : Jaune.State}
    {out : MsgCallOutput}
    (hfork : CoveredFork msg.benv.stat.fork)
    (hp : c.Preserves wa)
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h_inv : c.MsgInv wa msg) :
    c.StateInv wa st' ∧ (∀ a ∈ out.accountsToDelete.toList, a ≠ wa) := by
  have h := ContractSpecSem.processMessageCall_preserves_inv (c := c.toSem)
    hfork (preserves_toSem hp) h_run (msgInv_toSem h_inv)
  exact ⟨stateInv_ofSem h.1, h.2⟩

lemma checkTransaction_sender_ne_of_inv {wa : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    (h_check :
      checkTransaction benv bout tx =
        .ok ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩)
    (h_inv : c.BenvInv wa benv) :
    sender ≠ wa := by
  exact ContractSpecSem.checkTransaction_sender_ne_of_inv (c := c.toSem)
    h_check (benvInv_toSem h_inv)

lemma prepareMessage_preserves_inv {wa : Adr}
    {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h_prep : prepareMessage benv tenv tx = .ok msg)
    (h_state : c.StateInv wa benv.state)
    (h_ca : wa ∉ benv.createdAccounts)
    (h_origin_ne : tenv.stat.origin ≠ wa) :
    c.MsgInv wa msg := by
  exact msgInv_ofSem (ContractSpecSem.prepareMessage_preserves_inv (c := c.toSem)
    h_prep (stateInv_toSem h_state) h_ca h_origin_ne)

lemma StateInv.add_transaction_gas_credits {wa : Adr}
    {baseState debitState postMsgState : Jaune.State}
    {benv : Benv} {tx : Tx}
    {sender : Adr} {effectiveGasPrice : Nat}
    {validationSender : Adr}
    {intrinsicGas calldataFloorGasCost refundCounter : Nat}
    {txOutput : MsgCallOutput}
    (h_validate :
      validateTransaction benv.stat.rules tx validationSender =
        .ok ⟨intrinsicGas, calldataFloorGasCost⟩)
    -- the upfront-fee modulus bound, in `benv` form: the caller derives it
    -- from `checkTransaction_upfront_lt_modulus` (whose `beginTransaction`
    -- environment is only defeq) and ascribes it here.
    (h_fee_lt :
      tx.gas * effectiveGasPrice +
        (if tx.isTypeThree = true then
          calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
        else 0) < 2 ^ 256)
    (h_debit :
      (baseState.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
          else
            0).toB256 =
        some debitState)
    (h_msg_sum : sum postMsgState.bal ≤ sum debitState.bal)
    (h_base_sum : sum baseState.bal < 2 ^ 256)
    (h_post : c.StateInv wa postMsgState) :
    c.StateInv wa
      ((postMsgState.addBal sender
          ((tx.gas -
              max (tx.gas - txOutput.gasLeft -
                min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
                calldataFloorGasCost) *
            effectiveGasPrice).toB256).addBal
        benv.stat.coinbase
          (max (tx.gas - txOutput.gasLeft -
              min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
              calldataFloorGasCost *
            (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256) := by
  exact stateInv_ofSem (ContractSpecSem.StateInv.add_transaction_gas_credits
    (c := c.toSem) h_validate h_fee_lt h_debit h_msg_sum h_base_sum
    (stateInv_toSem h_post))

theorem processTransaction_preserves_inv (wa : Adr)
    (hp : c.Preserves wa)
    (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) (i : Nat) (st : Jaune.State)
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) : c.BenvInv wa (benv.withState st) := by
  exact benvInv_ofSem (ContractSpecSem.processTransaction_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_sum := h_sum) (h_inv := benvInv_toSem h_inv)
    (hfork := hfork))

theorem applyTransactions_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (txis : List (Nat × Tx)) (benv benv' : Benv) (bout bout' : BlockOutput)
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) : c.BenvInv wa benv' := by
  exact benvInv_ofSem (ContractSpecSem.applyTransactions_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_sum := h_sum) (h_inv := benvInv_toSem h_inv)
    (hfork := hfork))

lemma processUncheckedSystemTransaction_preserves_inv_sum_le (wa : Adr)
    (hp : c.Preserves wa)
    (benv : Benv) (target : Adr) (data : Bytes)
    (st : Jaune.State) (out : MsgCallOutput)
    (h_run : processUncheckedSystemTransaction benv target data = .ok ⟨st, out⟩)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) :
    c.StateInv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  have h := ContractSpecSem.processUncheckedSystemTransaction_preserves_inv_sum_le
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_inv := benvInv_toSem h_inv) (hfork := hfork)
  exact ⟨stateInv_ofSem h.1, h.2⟩

lemma processWithdrawalsState_preserves_inv (wa : Adr)
    (st : Jaune.State) (wds : List Withdrawal)
    (h_bound : sum st.bal + wdsum wds < 2 ^ 256)
    (h_inv : c.StateInv wa st) :
    c.StateInv wa (processWithdrawalsState st wds) := by
  exact stateInv_ofSem (ContractSpecSem.processWithdrawalsState_preserves_inv
    (c := c.toSem) (wa := wa) (h_bound := h_bound)
    (h_inv := stateInv_toSem h_inv))

lemma runRequestContracts_preserves_inv_sum_le (wa : Adr)
    (hp : c.Preserves wa)
    (idx : Nat) (contracts : List (UInt8 × Adr))
    (benv : Benv) (acc : List Bytes) (bal : BalBuilder)
    {st : Jaune.State} {acc' : List Bytes} {bal' : BalBuilder}
    (h_run : runRequestContracts idx contracts benv acc bal = .ok ⟨st, acc', bal'⟩)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) :
    c.StateInv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  have h := ContractSpecSem.runRequestContracts_preserves_inv_sum_le
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_inv := benvInv_toSem h_inv) (hfork := hfork)
  exact ⟨stateInv_ofSem h.1, h.2⟩

lemma processGeneralPurposeRequests_preserves_inv_sum_le (wa : Adr)
    (hp : c.Preserves wa)
    (benv : Benv) (bout : BlockOutput)
    (st : Jaune.State) (bout' : BlockOutput)
    (h_run : processGeneralPurposeRequests benv bout = .ok ⟨st, bout'⟩)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) :
    c.StateInv wa st ∧ sum st.bal ≤ sum benv.state.bal := by
  have h := ContractSpecSem.processGeneralPurposeRequests_preserves_inv_sum_le
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_inv := benvInv_toSem h_inv) (hfork := hfork)
  exact ⟨stateInv_ofSem h.1, h.2⟩

theorem applyBody_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (benv : Benv) (txs : List (Bytes ⊕ Tx)) (wds : List Withdrawal)
    (st : Jaune.State) (bout : BlockOutput)
    (h_run : applyBody benv txs wds = .ok ⟨st, bout⟩)
    (h_wds : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (h_inv : c.BenvInv wa benv)
    (hfork : CoveredFork benv.stat.fork) : c.StateInv wa st := by
  exact stateInv_ofSem (ContractSpecSem.applyBody_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_wds := h_wds) (h_inv := benvInv_toSem h_inv)
    (hfork := hfork))

theorem stateTransitionAt_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (f : Fork)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionAt f ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state)
    (hfork : CoveredFork f) : c.StateInv wa ch'.state := by
  exact stateInv_ofSem (ContractSpecSem.stateTransitionAt_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_wds := h_wds) (h_inv := stateInv_toSem h_inv)
    (hfork := hfork))

theorem stateTransitionUsing_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (cfg : ChainConfig) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state)
    (hcov : ∀ (t : Nat) (f' : Fork), cfg.forkAt t = .ok f' → CoveredFork f') :
    c.StateInv wa ch'.state := by
  exact stateInv_ofSem (ContractSpecSem.stateTransitionUsing_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_wds := h_wds) (h_inv := stateInv_toSem h_inv)
    (hcov := hcov))

theorem stateTransition_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  exact stateInv_ofSem (ContractSpecSem.stateTransition_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_wds := h_wds) (h_inv := stateInv_toSem h_inv))

theorem chainUsing_preserves_inv (wa : Adr) (hp : c.Preserves wa) (cfg : ChainConfig)
    (ch ch' : BlockChain) (h_reach : BlockChain.ReachUsing cfg ch ch')
    (h_inv : c.StateInv wa ch.state)
    (hcov : ∀ (t : Nat) (f' : Fork), cfg.forkAt t = .ok f' → CoveredFork f') :
    c.StateInv wa ch'.state := by
  exact stateInv_ofSem (ContractSpecSem.chainUsing_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_reach := h_reach) (h_inv := stateInv_toSem h_inv) (hcov := hcov))

theorem chain_preserves_inv (wa : Adr) (hp : c.Preserves wa) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  exact stateInv_ofSem (ContractSpecSem.chain_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_reach := h_reach) (h_inv := stateInv_toSem h_inv))

theorem addBlockToChainAt_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (f : Fork) (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainAt f ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state)
    (hfork : CoveredFork f) : c.StateInv wa ch'.state := by
  exact stateInv_ofSem (ContractSpecSem.addBlockToChainAt_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_wds := h_wds) (h_inv := stateInv_toSem h_inv)
    (hfork := hfork))

theorem addBlockToChainUsing_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (cfg : ChainConfig) (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChainUsing cfg ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state)
    (hcov : ∀ (t : Nat) (f' : Fork), cfg.forkAt t = .ok f' → CoveredFork f') :
    c.StateInv wa ch'.state := by
  exact stateInv_ofSem (ContractSpecSem.addBlockToChainUsing_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_wds := h_wds) (h_inv := stateInv_toSem h_inv)
    (hcov := hcov))

theorem addBlockToChain_preserves_inv (wa : Adr) (hp : c.Preserves wa)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : c.StateInv wa ch.state) : c.StateInv wa ch'.state := by
  exact stateInv_ofSem (ContractSpecSem.addBlockToChain_preserves_inv
    (c := c.toSem) (wa := wa) (hp := preserves_toSem hp)
    (h_run := h_run) (h_wds := h_wds) (h_inv := stateInv_toSem h_inv))

end ContractSpec


end Blanc
