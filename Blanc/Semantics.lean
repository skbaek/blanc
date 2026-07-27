-- Semantics.lean : formalized semantics of the EVM and Blanc

import Blanc.Basic
import Elevm.Hash
import Elevm.Execution



def Rinst.toB8 : Rinst → B8
  | add          => 0x01
  | mul          => 0x02
  | sub          => 0x03
  | div          => 0x04
  | sdiv         => 0x05
  | mod          => 0x06
  | smod         => 0x07
  | addmod       => 0x08
  | mulmod       => 0x09
  | exp          => 0x0A
  | signextend   => 0x0B
  | lt           => 0x10
  | gt           => 0x11
  | slt          => 0x12
  | sgt          => 0x13
  | eq           => 0x14
  | iszero       => 0x15
  | and          => 0x16
  | or           => 0x17
  | xor          => 0x18
  | not          => 0x19
  | byte         => 0x1A
  | shl          => 0x1B
  | shr          => 0x1C
  | sar          => 0x1D
  | clz          => 0x1E
  | kec          => 0x20
  | address      => 0x30
  | balance      => 0x31
  | origin       => 0x32
  | caller       => 0x33
  | callvalue    => 0x34
  | calldataload => 0x35
  | calldatasize => 0x36
  | calldatacopy => 0x37
  | codesize     => 0x38
  | codecopy     => 0x39
  | gasprice     => 0x3A
  | extcodesize  => 0x3B
  | extcodecopy  => 0x3C
  | retdatasize  => 0x3D
  | retdatacopy  => 0x3E
  | extcodehash  => 0x3F
  | blockhash    => 0x40
  | coinbase     => 0x41
  | timestamp    => 0x42
  | number       => 0x43
  | prevrandao   => 0x44
  | gaslimit     => 0x45
  | chainid      => 0x46
  | selfbalance  => 0x47
  | basefee      => 0x48
  | blobhash     => 0x49
  | blobbasefee  => 0x4A
  | pop          => 0x50
  | mload        => 0x51
  | mstore       => 0x52
  | mstore8      => 0x53
  | sload        => 0x54
  | sstore       => 0x55
  | pc           => 0x58
  | msize        => 0x59
  | gas          => 0x5A
  | tload        => 0x5C
  | tstore       => 0x5D
  | mcopy        => 0x5E
  | dup n        => 0x80 + n.val.toUInt8
  | swap n       => 0x90 + n.val.toUInt8
  | log n        => 0xA0 + n.val.toUInt8

abbrev Stack : Type := List B256

def Stack.Push (x y xy : Stack) : Prop := x <++ xy ++> y
def Stack.Pop (x xy y : Stack) : Prop := x <++ xy ++> y

inductive Func : Type
  | branch : Func → Func → Func
  | last : Linst → Func
  | next : Ninst → Func → Func
  | call : Nat → Func

structure Prog : Type where
  (main : Func)
  (aux : List Func)

def Jinst.Run (evm : Evm) :
    Jinst → Except (String × Devm) (Nat × Devm) → Prop :=
  λ j ex => j.run evm = ex

def Linst.Run (sevm : Sevm) (devm : Devm) : Linst → Execution → Prop :=
  λ l ex => l.run sevm devm = ex

def Xlot : Type := Option (Evm × Execution)

/-- Fieldwise relations used to assemble the canonical `Devm.Rel` frames. -/
structure Devm.Rels : Type where
  (stack : List B256 → List B256 → Prop)
  (memory : Mem → Mem → Prop)
  (gasLeft : Nat → Nat → Prop)
  (logs : List Log → List Log → Prop)
  (refundCounter : Int → Int → Prop)
  (output : B8L → B8L → Prop)
  (accountsToDelete : AdrSet → AdrSet → Prop)
  (returnData : B8L → B8L → Prop)
  (error : Option String → Option String → Prop)
  (accessedAddresses : AdrSet → AdrSet → Prop)
  (accessedStorageKeys : KeySet → KeySet → Prop)
  (state : State → State → Prop)
  (createdAccounts : AdrSet → AdrSet → Prop)
  (transientStorage : Tra → Tra → Prop)

/-- Canonical relation between dynamic EVM states, assembled field by field. -/
structure Devm.Rel (rels : Devm.Rels) (devm devm' : Devm) : Prop where
  (stack : rels.stack devm.stack devm'.stack)
  (memory : rels.memory devm.memory devm'.memory)
  (gasLeft : rels.gasLeft devm.gasLeft devm'.gasLeft)
  (logs : rels.logs devm.logs devm'.logs)
  (refundCounter : rels.refundCounter devm.refundCounter devm'.refundCounter)
  (output : rels.output devm.output devm'.output)
  ( accountsToDelete :
    rels.accountsToDelete devm.accountsToDelete devm'.accountsToDelete)
  (returnData : rels.returnData devm.returnData devm'.returnData)
  (error : rels.error devm.error devm'.error)
  ( accessedAddresses :
    rels.accessedAddresses devm.accessedAddresses devm'.accessedAddresses )
  ( accessedStorageKeys :
    rels.accessedStorageKeys devm.accessedStorageKeys devm'.accessedStorageKeys )
  (state : rels.state devm.state devm'.state)
  ( createdAccounts :
    rels.createdAccounts devm.createdAccounts devm'.createdAccounts )
  ( transientStorage :
    rels.transientStorage devm.transientStorage devm'.transientStorage )

def Devm.Rels.eq : Devm.Rels :=
  {
    stack := _root_.Eq,
    memory := _root_.Eq,
    gasLeft := _root_.Eq,
    logs := _root_.Eq,
    refundCounter := _root_.Eq,
    output := _root_.Eq,
    accountsToDelete := _root_.Eq,
    returnData := _root_.Eq,
    error := _root_.Eq,
    accessedAddresses := _root_.Eq,
    accessedStorageKeys := _root_.Eq,
    state := _root_.Eq,
    createdAccounts := _root_.Eq,
    transientStorage := _root_.Eq
  }

def Devm.Burn : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    gasLeft := (· ≥ · )
  }

lemma Nat.le_iff_exists (m n : Nat) : m ≤ n ↔ ∃ k, n = m + k := by
  constructor
  · intro _
    exists n - m
    omega
  · rintro ⟨k, hk⟩
    omega


def Devm.PopBurn (xs : List B256) : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    stack := Stack.Pop xs
    gasLeft := (· ≥ ·)
      -- λ gas gas' => ∃ diff : Nat, gas = gas' + diff
  }

def Linst.At (code : ByteArray) (pc : Nat) (l : Linst) : Prop := code.getInst pc = some (.last l)
def Ninst.At (code : ByteArray) (pc : Nat) (n : Ninst) : Prop := code.getInst pc = some (.next n)
def Jinst.At (code : ByteArray) (pc : Nat) (j : Jinst) : Prop := code.getInst pc = some (.jump j)
def Rinst.At (code : ByteArray) (pc : Nat) (r : Rinst) : Prop := code.getInst pc = some (.next (.reg r))
def Xinst.At (code : ByteArray) (pc : Nat) (x : Xinst) : Prop := code.getInst pc = some (.next (.exec x))

def Except.Split {ξ υ ζ : Type}
    (e : Except ξ υ) (e' : Except ξ ζ) (q : υ → Prop) : Prop :=
  (∃ x, e = .error x ∧ e' = .error x) ∨ (∃ y : υ, e = .ok y ∧ q y)

def Except.SplitXl {ξ υ ζ : Type}
    (e : Except ξ υ) (xl : Xlot) (e' : Except ξ ζ) (q : υ → Prop) : Prop :=
  (∃ x, e = .error x ∧ e' = .error x ∧ xl = .none) ∨ (∃ y : υ, e = .ok y ∧ q y)

/-! ### The recursion-facing relational layer.

Each former hand-maintained mirror is now a thin, non-recursive wrapper: an
equation about the flattened frame/step functions of ELeVM.  `RunFrame` is the
generic frame relation; the named mirrors specialize it so that the statements
consumed by `Common.lean` and `Solvent.lean` keep their current shape. -/

def RunFrame (f : Frame) (xl : Xlot)
    (r : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  match f.enter with
  | .done r' => xl = .none ∧ r = r'
  | .run evm => ∃ raw, xl = .some ⟨evm, raw⟩ ∧ r = f.settle raw

def ExecuteCode (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  match executeCode.enter msg with
  | .inl evm => ∃ raw, xl = .some ⟨evm, raw⟩ ∧ ex = executeCode.handleError raw
  | .inr raw => xl = .none ∧ ex = executeCode.handleError raw

def ProcessMessage (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  RunFrame (Frame.ofCall msg) xl ex

def ProcessCreateMessage (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  RunFrame (Frame.ofCreate msg) xl ex

def XStep.Run (s : XStep) (xl : Xlot) (ex : Execution) : Prop :=
  match s with
  | .done ex' => xl = .none ∧ ex = ex'
  | .spawn f rsm => ∃ r, RunFrame f xl r ∧ ex = rsm.run r

def GenericCreate (sevm : Sevm) (devm : Devm) (endowment : B256) (newAddress : Adr)
    (memoryIndex memorySize : Nat) (xl : Xlot) (ex : Execution) : Prop :=
  XStep.Run
    (genericCreate.step sevm devm endowment newAddress memoryIndex memorySize)
    xl ex

def GenericCall
    (sevm: Sevm)
    (devm: Devm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (input_index:  Nat)
    (input_size:   Nat)
    (output_index: Nat)
    (output_size:  Nat)
    (code : ByteArray)
    (disablePrecompiles: Bool)
    (xl : Xlot)
    (ex : Execution) : Prop :=
  XStep.Run
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall input_index input_size
      output_index output_size code disablePrecompiles)
    xl ex

def Xinst.Run (sevm : Sevm) (devm : Devm) :
    Xinst → Xlot → Execution → Prop :=
  fun x xl ex => XStep.Run (Xinst.step sevm devm x) xl ex

def Step.Run (s : Step) (xl : Xlot) (ex : Execution) : Prop :=
  match s with
  | .halt ex' => xl = .none ∧ ex = ex'
  | .cont _ devm => xl = .none ∧ ex = .ok devm
  | .spawn f rsm _ => ∃ r, RunFrame f xl r ∧ ex = rsm.run r

def Ninst.Run' (pc : Nat) (sevm : Sevm) (devm : Devm)
    (n : Ninst) (xl : Xlot) (ex : Execution) : Prop :=
  Step.Run (Ninst.step ⟨pc, sevm, devm⟩ n) xl ex

/- Exec pc sevm devm ex is provable iff
    ∃ lim : Nat, exec ⟨pc, sevm, devm⟩ lim = Fueled.ofExcept ex
   holds; fuel exhaustion is excluded by the shape of the equation.  The
   relation is the generic derivation tree over the flattened driver's step
   outcomes: every premise other than a sub-derivation is an equation about a
   non-recursive function. -/
inductive Exec : Nat → Sevm → Devm → Execution → Type
  | halt {pc sevm devm ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .halt ex →
    Exec pc sevm devm ex
  | cont {pc sevm devm pc' devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex
  | doneErr {pc sevm devm f rsm pc' r e} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .done r →
    rsm.run r = .error e →
    Exec pc sevm devm (.error e)
  | doneOk {pc sevm devm f rsm pc' r devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .done r →
    rsm.run r = .ok devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex
  | runErr {pc sevm devm f rsm pc' cevm raw e} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .run cevm →
    Exec cevm.pc cevm.sta cevm.dyna raw →
    rsm.run (f.settle raw) = .error e →
    Exec pc sevm devm (.error e)
  | runOk {pc sevm devm f rsm pc' cevm raw devm' ex} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
    f.enter = .run cevm →
    Exec cevm.pc cevm.sta cevm.dyna raw →
    rsm.run (f.settle raw) = .ok devm' →
    Exec pc' sevm devm' ex →
    Exec pc sevm devm ex

def Xlot.Filled : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ => Nonempty (Exec evm.pc evm.sta evm.dyna exn)


def Ninst.Run (sevm : Sevm) (devm : Devm) (n : Ninst) (devm' : Devm) : Prop :=
  ∃ xl : Xlot, xl.Filled ∧ ∃ pc, Ninst.Run' pc sevm devm n xl (.ok devm')

inductive Func.Run : List Func → Sevm → Devm → Func → Devm → Prop
  | zero :
    ∀ {fs sevm devm devm' f g devm''},
      Devm.PopBurn [0] devm devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (branch f g) devm''
  | succ :
    ∀ {fs sevm devm w devm' f g devm_jd devm''},
      w ≠ 0 →
      Devm.PopBurn [w] devm devm' →
      Devm.Burn devm' devm_jd →
      Func.Run fs sevm devm_jd g devm'' →
      Func.Run fs sevm devm (branch f g) devm''
  | last :
    ∀ {fs sevm devm i devm' },
      Linst.Run sevm devm i (.ok devm') →
      Func.Run fs sevm devm (last i) devm'
  | next :
    ∀ {fs sevm devm i devm' f devm''},
      Ninst.Run sevm devm i devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (next i f) devm''
  | call :
    ∀ {fs sevm devm devm' k f devm''},
      fs[k]? = some f →
      Devm.Burn devm devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (call k) devm''

def Prog.Run (sevm : Sevm) (devm : Devm) (p : Prog) (devm' : Devm) : Prop :=
  Func.Run (p.main :: p.aux) sevm devm (.call 0) devm'

-------------------------------------------------------------------------------



/- Machinery for reasoning about fuel-bounded (`Fueled`) computations.
   A completed run is witnessed by an equation `f lim = Fueled.ofExcept ex`;
   fuel exhaustion (`Fueled.exhausted`) is ruled out by the mere shape of such
   an equation, so no `≠ "RecursionLimit"` side conditions are needed. -/

namespace Fueled

variable {ε ζ : Type} {α β : Type}

lemma ext {x y : Fueled ε α} (h : x.run = y.run) : x = y := h

lemma exhausted_ne_ofExcept {x : Except ε α} :
    (Fueled.exhausted : Fueled ε α) ≠ Fueled.ofExcept x :=
  fun h => nomatch congrArg ExceptT.run h

lemma ofExcept_ne_exhausted {x : Except ε α} :
    (Fueled.ofExcept x : Fueled ε α) ≠ Fueled.exhausted :=
  fun h => nomatch congrArg ExceptT.run h

lemma ne_exhausted_of_eq_ofExcept {x : Fueled ε α} {ex : Except ε α}
    (h : x = Fueled.ofExcept ex) : x ≠ Fueled.exhausted := by
  rw [h]; exact ofExcept_ne_exhausted

@[simp] lemma ofExcept_inj {x y : Except ε α} :
    (Fueled.ofExcept x : Fueled ε α) = Fueled.ofExcept y ↔ x = y :=
  ⟨fun h => Option.some.inj (congrArg ExceptT.run h), fun h => by rw [h]⟩

@[simp] lemma ok_inj {x y : α} :
    (Fueled.ok x : Fueled ε α) = Fueled.ok y ↔ x = y :=
  ofExcept_inj.trans ⟨Except.ok.inj, congrArg _⟩

@[simp] lemma error_inj {e e' : ε} :
    (Fueled.error e : Fueled ε α) = Fueled.error e' ↔ e = e' :=
  ofExcept_inj.trans ⟨Except.error.inj, congrArg _⟩

@[simp] lemma ok_ne_error {x : α} {e : ε} :
    (Fueled.ok x : Fueled ε α) = Fueled.error e ↔ False :=
  by
    constructor
    · intro h
      cases Fueled.ofExcept_inj.mp h
    · exact False.elim

@[simp] lemma error_ne_ok {x : α} {e : ε} :
    (Fueled.error e : Fueled ε α) = Fueled.ok x ↔ False :=
  by
    constructor
    · intro h
      cases Fueled.ofExcept_inj.mp h
    · exact False.elim

@[simp] lemma exhausted_ne_ok {x : α} :
    (Fueled.exhausted : Fueled ε α) = Fueled.ok x ↔ False :=
  ⟨fun h => exhausted_ne_ofExcept h, False.elim⟩

@[simp] lemma exhausted_ne_error {e : ε} :
    (Fueled.exhausted : Fueled ε α) = Fueled.error e ↔ False :=
  ⟨fun h => exhausted_ne_ofExcept h, False.elim⟩

@[simp] lemma ok_ne_exhausted {x : α} :
    (Fueled.ok x : Fueled ε α) = Fueled.exhausted ↔ False :=
  ⟨fun h => ofExcept_ne_exhausted h, False.elim⟩

@[simp] lemma error_ne_exhausted {e : ε} :
    (Fueled.error e : Fueled ε α) = Fueled.exhausted ↔ False :=
  ⟨fun h => ofExcept_ne_exhausted h, False.elim⟩

@[simp] lemma exhausted_ne_ofExcept_iff {x : Except ε α} :
    (Fueled.exhausted : Fueled ε α) = Fueled.ofExcept x ↔ False :=
  ⟨fun h => exhausted_ne_ofExcept h, False.elim⟩

@[simp] lemma ofExcept_eq_ok_iff {x : Except ε α} {y : α} :
    (Fueled.ofExcept x : Fueled ε α) = Fueled.ok y ↔ x = .ok y := ofExcept_inj

@[simp] lemma ofExcept_eq_error_iff {x : Except ε α} {e : ε} :
    (Fueled.ofExcept x : Fueled ε α) = Fueled.error e ↔ x = .error e := ofExcept_inj

lemma ok_bind (y : α) (f : α → Fueled ε β) :
    (Fueled.ok y : Fueled ε α) >>= f = f y := rfl

lemma error_bind (e : ε) (f : α → Fueled ε β) :
    (Fueled.error e : Fueled ε α) >>= f = Fueled.error e := rfl

lemma exhausted_bind (f : α → Fueled ε β) :
    (Fueled.exhausted : Fueled ε α) >>= f = Fueled.exhausted := rfl

lemma ofExcept_ok_bind (y : α) (f : α → Fueled ε β) :
    Fueled.ofExcept (.ok y) >>= f = f y := rfl

lemma ofExcept_error_bind (e : ε) (f : α → Fueled ε β) :
    Fueled.ofExcept (.error e) >>= f = Fueled.ofExcept (.error e) := rfl

lemma lift_bind_lift {x : Except ε α} {g : α → Except ε β} :
    ((liftM x : Fueled ε α) >>= fun y => liftM (g y)) =
      (liftM (x >>= g) : Fueled ε β) := by
  cases x <;> rfl

lemma assert_eq (p : Prop) [Decidable p] (e : ε) :
    (Fueled.assert p e : Fueled ε Unit) =
      Fueled.ofExcept (Except.assert p e) := by
  by_cases hp : p
  · simp only [Fueled.assert, Except.assert, if_pos hp]; rfl
  · simp only [Fueled.assert, Except.assert, if_neg hp]; rfl

lemma mapResult_ofExcept (g : Except ε α → Except ζ β) (x : Except ε α) :
    Fueled.mapResult g (Fueled.ofExcept x) = Fueled.ofExcept (g x) := rfl

lemma mapResult_exhausted (g : Except ε α → Except ζ β) :
    Fueled.mapResult g (Fueled.exhausted : Fueled ε α) = Fueled.exhausted := rfl

theorem of_bind_eq {x : Fueled ε α} {f : α → Fueled ε β} {ex : Except ε β}
    (h : x >>= f = Fueled.ofExcept ex) :
    (∃ e, x = Fueled.ofExcept (.error e) ∧ ex = .error e) ∨
      (∃ y, x = Fueled.ofExcept (.ok y) ∧ f y = Fueled.ofExcept ex) := by
  have hrun : x.run >>= ExceptT.bindCont f = some ex := congrArg ExceptT.run h
  rcases hx : x.run with _ | ⟨e | y⟩ <;> rw [hx] at hrun
  · cases hrun
  · left; exact ⟨e, Fueled.ext hx, (Option.some.inj hrun).symm⟩
  · right; exact ⟨y, Fueled.ext hx, Fueled.ext hrun⟩

theorem of_lift_bind_eq {x : Except ε α} {f : α → Fueled ε β} {ex : Except ε β}
    (h : Fueled.ofExcept x >>= f = Fueled.ofExcept ex) :
    (∃ e, x = .error e ∧ ex = .error e) ∨
      (∃ y, x = .ok y ∧ f y = Fueled.ofExcept ex) := by
  rcases of_bind_eq h with ⟨e, hx, hex⟩ | ⟨y, hx, hf⟩
  · exact Or.inl ⟨e, ofExcept_inj.mp hx, hex⟩
  · exact Or.inr ⟨y, ofExcept_inj.mp hx, hf⟩

theorem of_bind_eq' {x : Fueled ε α} {f : α → Fueled ε β} {ex : Except ε β}
    (h : x >>= f = Fueled.ofExcept ex) :
    ∃ ex', x = Fueled.ofExcept ex' ∧
      Fueled.ofExcept ex' >>= f = Fueled.ofExcept ex := by
  rcases of_bind_eq h with ⟨e, hx, hex⟩ | ⟨y, hx, hf⟩
  · refine ⟨.error e, hx, ?_⟩; rw [ofExcept_error_bind, hex]
  · refine ⟨.ok y, hx, ?_⟩; rw [ofExcept_ok_bind]; exact hf

theorem of_bind_eq_ok {x : Fueled ε α} {f : α → Fueled ε β} {z : β}
    (h : x >>= f = Fueled.ok z) :
    ∃ y, x = Fueled.ok y ∧ f y = Fueled.ok z := by
  rcases of_bind_eq (ex := .ok z) h with ⟨e, _, hex⟩ | ⟨y, hx, hf⟩
  · cases hex
  · exact ⟨y, hx, hf⟩

theorem of_lift_bind_eq_ok {x : Except ε α} {f : α → Fueled ε β} {z : β}
    (h : Fueled.ofExcept x >>= f = Fueled.ok z) :
    ∃ y, x = .ok y ∧ f y = Fueled.ok z := by
  rcases of_lift_bind_eq (ex := .ok z) h with ⟨e, _, hex⟩ | ⟨y, hx, hf⟩
  · cases hex
  · exact ⟨y, hx, hf⟩

theorem of_mapResult_eq {g : Except ε α → Except ζ β} {x : Fueled ε α}
    {ex : Except ζ β} (h : Fueled.mapResult g x = Fueled.ofExcept ex) :
    ∃ ex', x = Fueled.ofExcept ex' ∧ g ex' = ex := by
  have hrun : x.run.map g = some ex := congrArg ExceptT.run h
  rcases hx : x.run with _ | ex' <;> rw [hx] at hrun
  · cases hrun
  · exact ⟨ex', Fueled.ext hx, Option.some.inj hrun⟩

lemma bind_eq_bind {x : Fueled ε α} {f g : α → Fueled ε β}
    (h : ∀ y, x = Fueled.ok y → f y = g y) : x >>= f = x >>= g := by
  rcases hx : x.run with _ | ⟨e | y⟩
  · apply Fueled.ext
    show x.run >>= ExceptT.bindCont f = x.run >>= ExceptT.bindCont g
    rw [hx]; rfl
  · apply Fueled.ext
    show x.run >>= ExceptT.bindCont f = x.run >>= ExceptT.bindCont g
    rw [hx]; rfl
  · have hxy : x = Fueled.ok y := Fueled.ext hx
    rw [hxy, ok_bind, ok_bind]; exact h y hxy

lemma ne_exhausted_of_bind {x : Fueled ε α} {f : α → Fueled ε β} {y : α}
    (h : x >>= f ≠ Fueled.exhausted) (eq : x = Fueled.ok y) :
    f y ≠ Fueled.exhausted := by
  intro hex; apply h; rw [eq, ok_bind, hex]

lemma head_ne_exhausted_of_bind {x : Fueled ε α} {f : α → Fueled ε β}
    (h : x >>= f ≠ Fueled.exhausted) : x ≠ Fueled.exhausted := by
  intro hex; apply h; rw [hex, exhausted_bind]

lemma mapResult_ne_exhausted {g : Except ε α → Except ζ β} {x : Fueled ε α}
    (h : Fueled.mapResult g x ≠ Fueled.exhausted) : x ≠ Fueled.exhausted := by
  intro hex; apply h; rw [hex, mapResult_exhausted]

lemma bind_eq_of_eq_ok_of_eq {x : Except ε α} {y : α} {z : Fueled ε β}
    {f : α → Fueled ε β} (eq_ok : x = .ok y) (eq : f y = z) :
    Fueled.ofExcept x >>= f = z := by
  rw [eq_ok, ofExcept_ok_bind]; exact eq

end Fueled

def Saturates {ε υ} (n : Nat) (f : Nat → Fueled ε υ) : Prop :=
  f n ≠ Fueled.exhausted → ∀ m, n < m → (f n = f m)

/-- Driver-level fuel monotonicity: one induction on `lim`, quantified over the
whole machine state so the child recursion can reuse the hypothesis at the
same fuel.  This replaces the old eight-field `Saturation` record and its
per-function proof. -/
theorem exec_saturates (lim : Nat) : ∀ evm : Evm, Saturates lim (exec evm) := by
  induction lim with
  | zero =>
    intro evm ne
    simp only [exec] at ne
    cases ne rfl
  | succ lim ih =>
    intro evm ne m gt
    rcases m with _ | m
    · cases Nat.not_lt_zero _ gt
    have gt' : lim < m := Nat.lt_of_succ_lt_succ gt
    simp only [exec] at ne ⊢
    rcases hstep : evm.step with ex | ⟨pc, devm⟩ | ⟨f, rsm, pc⟩
    · rfl
    · rw [hstep] at ne
      exact ih _ ne m gt'
    · rw [hstep] at ne
      simp only [] at ne ⊢
      rcases henter : f.enter with r | child
      · rw [henter] at ne
        simp only [] at ne ⊢
        rcases hr : rsm.run r with e | devm
        · rfl
        · rw [hr] at ne
          exact ih _ ne m gt'
      · rw [henter] at ne
        simp only [] at ne ⊢
        rcases hrun : (exec child lim).run with _ | raw
        · rw [hrun] at ne
          cases ne rfl
        · rw [hrun] at ne
          have child_ne : exec child lim ≠ Fueled.exhausted := by
            intro h
            rw [h, Fueled.exhausted_run] at hrun
            cases hrun
          rw [← ih child child_ne m gt', hrun]
          simp only [] at ne ⊢
          rcases hr : rsm.run (f.settle raw) with e | devm
          · rfl
          · rw [hr] at ne
            exact ih _ ne m gt'

/-! ### Depth side conditions for the strong induction of `Common.lean`.

Every `.spawn` produced by the step functions is depth-guarded, so a child
frame always sits strictly below its parent, and entering a frame preserves
the frame's own depth. -/

lemma genericCall.step_spawn_depth
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {f : Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Frame.ofCall, callMsg]
  all_goals omega

lemma genericCreate.step_spawn_depth
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals
    simp only [Frame.ofCreate, processCreateMessage.msg, Msg.withBenv,
      createMsg, not_or] at *
  all_goals omega

lemma Xinst.step_spawn_depth {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm) :
    f.inner.depth < sevm.depth := by
  cases x <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact genericCreate.step_spawn_depth hs
      | exact genericCall.step_spawn_depth hs

lemma Step.ofExecution_ne_spawn {pc : Nat} {ex : Execution}
    {f : Frame} {rsm : Resume} {pc' : Nat} :
    Step.ofExecution pc ex ≠ .spawn f rsm pc' := by
  cases ex <;> simp [Step.ofExecution]

lemma Step.ofJump_ne_spawn {j : Except (String × Devm) (Nat × Devm)}
    {f : Frame} {rsm : Resume} {pc' : Nat} :
    Step.ofJump j ≠ .spawn f rsm pc' := by
  cases j <;> simp [Step.ofJump]

lemma XStep.toStep_spawn {pc : Nat} {s : XStep}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (h : XStep.toStep pc s = .spawn f rsm pc') : s = .spawn f rsm := by
  cases s
  · cases Step.ofExecution_ne_spawn h
  · cases h; rfl

/-- A spawned child frame sits strictly below its parent's depth. -/
lemma Step.spawn_depth_lt {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') :
    f.inner.depth < sevm.depth := by
  unfold Evm.step at hs
  split at hs
  · cases hs
  · rename_i n hgi
    rcases n with r | x | ⟨xs, hxs⟩ <;> simp only [Ninst.step] at hs
    · cases Step.ofExecution_ne_spawn hs
    · exact Xinst.step_spawn_depth (XStep.toStep_spawn hs)
    · cases Step.ofExecution_ne_spawn hs
  · cases Step.ofJump_ne_spawn hs
  · cases hs

/-- Entering a frame preserves the frame's own depth. -/
lemma Frame.enter_run_depth {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) : cevm.sta.depth = f.inner.depth := by
  unfold Frame.enter at h
  split at h
  · cases h
  · rename_i benv hbenv
    split at h
    · cases h
      rename_i heq
      unfold executeCode.enter at heq
      simp only [] at heq
      split at heq
      · cases heq; rfl
      · split at heq
        · cases heq
        · cases heq; rfl
    · cases h

/-! ### Adequacy: the relational and executable semantics agree. -/

lemma of_exec' :
    ∀ (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      Exec pc sevm devm exn →
      ∃ lim, ∀ lim' > lim, (exec ⟨pc, sevm, devm⟩ lim' = Fueled.ofExcept exn) := by
  apply Exec.rec
  · intro pc sevm devm ex hstep
    refine ⟨0, fun lim' gt => ?_⟩
    rcases lim' with _ | lim'
    · cases Nat.not_lt_zero _ gt
    simp only [exec, hstep]
  · intro pc sevm devm pc' devm' ex hstep _ ih
    rcases ih with ⟨lim, ih⟩
    refine ⟨lim + 1, fun lim' gt => ?_⟩
    rcases lim' with _ | lim'
    · cases Nat.not_lt_zero _ gt
    simp only [exec, hstep]
    exact ih lim' (by omega)
  · intro pc sevm devm f rsm pc' r e hstep henter hr
    refine ⟨0, fun lim' gt => ?_⟩
    rcases lim' with _ | lim'
    · cases Nat.not_lt_zero _ gt
    simp only [exec, hstep, henter, hr]
  · intro pc sevm devm f rsm pc' r devm' ex hstep henter hr _ ih
    rcases ih with ⟨lim, ih⟩
    refine ⟨lim + 1, fun lim' gt => ?_⟩
    rcases lim' with _ | lim'
    · cases Nat.not_lt_zero _ gt
    simp only [exec, hstep, henter, hr]
    exact ih lim' (by omega)
  · intro pc sevm devm f rsm pc' cevm raw e hstep henter _ hr ihc
    rcases ihc with ⟨limc, ihc⟩
    refine ⟨limc + 1, fun lim' gt => ?_⟩
    rcases lim' with _ | lim'
    · cases Nat.not_lt_zero _ gt
    have hc : exec cevm lim' = Fueled.ofExcept raw := ihc lim' (by omega)
    simp only [exec, hstep, henter]
    rw [hc]
    simp only [Fueled.ofExcept_run, hr]
  · intro pc sevm devm f rsm pc' cevm raw devm' ex hstep henter _ hr _ ihc ih
    rcases ihc with ⟨limc, ihc⟩
    rcases ih with ⟨limp, ih⟩
    refine ⟨max limc limp + 1, fun lim' gt => ?_⟩
    rcases lim' with _ | lim'
    · cases Nat.not_lt_zero _ gt
    have hc : exec cevm lim' = Fueled.ofExcept raw := ihc lim' (by omega)
    simp only [exec, hstep, henter]
    rw [hc]
    simp only [Fueled.ofExcept_run, hr]
    exact ih lim' (by omega)

set_option linter.defProp false in
@[reducible] def of_exec :
    ∀ (lim : Nat) (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      (exec ⟨pc, sevm, devm⟩ lim = Fueled.ofExcept exn) →
      Nonempty (Exec pc sevm devm exn) := by
  apply Nat.strongRec
  intro lim ih pc sevm devm exn exec_eq
  cases lim with
  | zero =>
    simp only [exec] at exec_eq
    cases Fueled.exhausted_ne_ofExcept exec_eq
  | succ lim =>
    simp only [exec] at exec_eq
    rcases hstep : Evm.step ⟨pc, sevm, devm⟩ with ex | ⟨pc', devm'⟩ | ⟨f, rsm, pc'⟩ <;>
      rw [hstep] at exec_eq <;> simp only [] at exec_eq
    · rw [← Fueled.ofExcept_inj.mp exec_eq]
      exact ⟨Exec.halt hstep⟩
    · rcases ih lim (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
      exact ⟨Exec.cont hstep exc⟩
    · rcases henter : f.enter with r | cevm <;>
        rw [henter] at exec_eq <;> simp only [] at exec_eq
      · rcases hr : rsm.run r with e | devm' <;>
          rw [hr] at exec_eq <;> simp only [] at exec_eq
        · rw [← Fueled.ofExcept_inj.mp exec_eq]
          exact ⟨Exec.doneErr hstep henter hr⟩
        · rcases ih lim (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
          exact ⟨Exec.doneOk hstep henter hr exc⟩
      · rcases hrun : (exec cevm lim).run with _ | raw <;>
          rw [hrun] at exec_eq <;> simp only [] at exec_eq
        · cases Fueled.exhausted_ne_ofExcept exec_eq
        · have hc : exec cevm lim = Fueled.ofExcept raw := Fueled.ext hrun
          rcases ih lim (Nat.lt_succ_self _) cevm.pc cevm.sta cevm.dyna raw hc with
            ⟨excChild⟩
          rcases hr : rsm.run (f.settle raw) with e | devm' <;>
            rw [hr] at exec_eq <;> simp only [] at exec_eq
          · rw [← Fueled.ofExcept_inj.mp exec_eq]
            exact ⟨Exec.runErr hstep henter excChild hr⟩
          · rcases ih lim (Nat.lt_succ_self _) pc' sevm devm' exn exec_eq with ⟨exc⟩
            exact ⟨Exec.runOk hstep henter excChild hr exc⟩

lemma exec_iff_exec_eq (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
    Nonempty (Exec pc sevm devm exn) ↔
      ∃ lim, exec ⟨pc, sevm, devm⟩ lim = Fueled.ofExcept exn := by
  constructor
  · intro ⟨exc⟩
    rcases of_exec' _ _ _ _ exc with ⟨lim, eq⟩
    exact ⟨lim + 1, eq (lim + 1) (by omega)⟩
  · intro ⟨lim, eq⟩; exact of_exec _ _ _ _ _ eq

def Xlot.Good (lim : Nat) : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ => ∃ lim' ≤ lim, exec evm lim' = Fueled.ofExcept exn

lemma of_runFrame {f : Frame} {lim : Nat}
    {r : Except (String × State × AdrSet × Tra) Devm}
    (eq : runFrame f lim = Fueled.ofExcept r) :
    ∃ xl : Xlot, xl.Good lim ∧ RunFrame f xl r := by
  unfold runFrame at eq
  rcases henter : f.enter with r' | evm <;> rw [henter] at eq
  · refine ⟨.none, trivial, ?_⟩
    unfold RunFrame
    rw [henter]
    exact ⟨rfl, (Fueled.ofExcept_inj.mp eq).symm⟩
  · rcases Fueled.of_mapResult_eq eq with ⟨raw, hexec, hsettle⟩
    refine ⟨.some ⟨evm, raw⟩, ⟨lim, le_refl _, hexec⟩, ?_⟩
    unfold RunFrame
    rw [henter]
    exact ⟨raw, rfl, hsettle.symm⟩

lemma of_processMessage (msg : Msg) (lim : Nat)
    (ex : Except (String × State × AdrSet × Tra) Devm)
    (eq : processMessage msg lim = Fueled.ofExcept ex) :
    ∃ xl : Xlot, xl.Good lim ∧ ProcessMessage msg xl ex :=
  of_runFrame eq

lemma of_processCreateMessage (msg : Msg) (lim : Nat)
    (ex : Except (String × State × AdrSet × Tra) Devm)
    (eq : processCreateMessage msg lim = Fueled.ofExcept ex) :
    ∃ xl : Xlot,
      xl.Good lim ∧
      ProcessCreateMessage msg xl ex :=
  of_runFrame eq
