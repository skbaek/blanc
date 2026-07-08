import Blanc.temp

def Benv.EquivForDelegation (b1 b2 : Benv) : Prop :=
  b2.createdAccounts = b1.createdAccounts ∧
  ∀ a, (b1.state.getCode a).toList ≠ [] → b2.state.getCode a = b1.state.getCode a

lemma Benv.EquivForDelegation_refl (b : Benv) : Benv.EquivForDelegation b b := by
  refine ⟨rfl, fun a _ => rfl⟩

lemma Benv.EquivForDelegation_trans {b1 b2 b3 : Benv} (h12 : Benv.EquivForDelegation b1 b2) (h23 : Benv.EquivForDelegation b2 b3) :
    Benv.EquivForDelegation b1 b3 := by
  rcases h12 with ⟨h1c, h1code⟩
  rcases h23 with ⟨h2c, h2code⟩
  refine ⟨by rw [h2c, h1c], fun a ha => ?_⟩
  have h1 := h1code a ha
  have ha2' : (b2.state.getCode a).toList ≠ [] := by
    rw [h1]
    exact ha
  rw [h2code a ha2', h1]

lemma forIn_inv {α β : Type} {I : β → Prop} {l : List α} {init : β}
    {f : α → β → Except String (ForInStep β)}
    (h_init : I init)
    (h_step : ∀ a b b', a ∈ l → I b → f a b = .ok (.yield b') → I b')
    (h_done : ∀ a b b', a ∈ l → I b → f a b = .ok (.done b') → I b')
    {res : β}
    (h_run : Id.run (ExceptT.run (forIn l init f)) = .ok res) : I res := by
  sorry

lemma setDelegation_benv_equiv {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩) :
    Benv.EquivForDelegation msg.benv msg'.benv := by
  sorry

lemma setDelegation_msg_noDel_test {wa : Adr} {msg msg' : Msg} {v : B256}
    (h_run : setDelegation msg = .ok ⟨msg', v⟩)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa msg' := by
  have heq := setDelegation_benv_equiv h_run
  rcases heq with ⟨h_ca, h_code⟩
  have h_code_wa := h_code wa
  have h2 := h_code_wa h.code
  constructor
  · rw [h_ca]; exact h.ca
  · rw [h2]; exact h.code
