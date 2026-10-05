import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Deploy
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.CheckTries
import Blanc.Lift.NodeWalk
import Blanc.Lift.KernelBatch

/-! # V− setup, message 3: `initialize` through the proxy — the message and its start

The third root message: the code-free `creator` calls the clone `proxyAddr` with
`initialize(string,string,address[4],uint256[4],uint256,uint256)` (selector `0xa461b3c8`),
value 0, at transaction depth 1024, over exactly the world the two creations settle to
(`setupState initialWorld`, also the block-original state). The arguments, ABI-encoded:

* `_name = ""`, `_symbol = ""` (the cheapest strings: the stored name is the fixed prefix
  `"Curve.fi Factory Pool: "` and the symbol `"-f"`);
* `_coins = [0xEeee…EEeE, tokenAddr, 0, 0]` (ETH as coin 0, the token fixture as coin 1);
* `_rate_multipliers = [10^18, 10^18, 0, 0]`, `_A = 100`, `_fee = 0`.

The world is given by the shadows of the walk engine (`acs0`, `stor0`), derived from the
setup's account facts, so the walk never inspects it; its block-original state is the closed
term `setupState initialWorld`, which the walk evaluates only at `SSTORE` (the original value). -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun

/-- A big-endian 32-byte ABI word. -/
def abiWord (n : Nat) : Bytes :=
  (List.range 32).reverse.map fun i => ((n >>> (8 * i)) % 256).toUInt8

/-- The ETH sentinel coin address `0xEeee…EEeE`. -/
def ethCoin : Adr := 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE

/-- The ABI-encoded `initialize("", "", [ETH, T, 0, 0], [1e18, 1e18, 0, 0], 100, 0)`: twelve
head words (the two string offsets `0x180`, `0x1a0`, the eight static array words, `_A`,
`_fee`) and the two empty strings' length words. -/
def initCall : Bytes :=
  [0xa4, 0x61, 0xb3, 0xc8] ++ abiWord 0x180 ++ abiWord 0x1a0 ++
    abiWord ethCoin.toNat ++ abiWord tokenAddr.toNat ++ abiWord 0 ++ abiWord 0 ++
    abiWord (10 ^ 18) ++ abiWord (10 ^ 18) ++ abiWord 0 ++ abiWord 0 ++
    abiWord 100 ++ abiWord 0 ++ abiWord 0 ++ abiWord 0

/-- The gas of message 3. -/
def initGas : Nat := 1000000

/-- The forwarder runtime at the clone. -/
abbrev fwdCode : ByteArray := Blanc.forwarderCode Blanc.curvePlainImpl6326

/-- Message 3: `creator` calls the clone with `initialize`, over world `W`. -/
def initMsg (fork : Fork) (W : State) : Msg := callMsg fork W proxyAddr fwdCode initCall initGas

/-- The world message 3 starts from: the creations' settled world over the disclosed start. -/
def world2 : State := setupState initialWorld

/-- The accounts of `world2` with storage dropped. -/
def acs2 : AcctShadow :=
  [(creator, ⟨0, creatorFunds, .empty, .empty⟩),
   (implAddr, ⟨1, 0, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩),
   (proxyAddr, ⟨1, 0, .empty, fwdCode⟩)]

/-- The storage of `world2`: the implementation's `fee = 31337` only. -/
def stor2 : StorShadow := [((implAddr, (10 : B256)), (31337 : B256))]

theorem creator_ne_implAddr : creator ≠ implAddr := by decide
theorem creator_ne_proxyAddr : creator ≠ proxyAddr := by decide

theorem initialWorld_get (a : Adr) :
    initialWorld.get a = if a = creator then { Acct.nil with bal := creatorFunds } else .nil := by
  unfold Fixed.Reach.initialWorld
  by_cases h : a = creator
  · subst h
    rw [if_pos rfl]
    exact State.get_set_self _ _ _
  · rw [if_neg h, State.get_set_ne _ (Ne.symm h)]
    rfl

/-- `world2`, account by account (from `setup_creations`). -/
theorem world2_get (a : Adr) :
    world2.get a = if a = implAddr then implAccount else if a = proxyAddr then proxyAccount
      else initialWorld.get a := by
  obtain ⟨-, postP, -, -, -, -, -, -, -, -, -, hI, hP, hF, hS⟩ :=
    setup_creations .prague CoveredFork.prague initialWorld initialWorld_absent.1
      initialWorld_absent.2
  unfold world2
  rw [← hS]
  by_cases hi : a = implAddr
  · subst hi; rw [if_pos rfl, hI]
  · rw [if_neg hi]
    by_cases hp : a = proxyAddr
    · subst hp; rw [if_pos rfl, hP]
    · rw [if_neg hp, hF a hi hp]

theorem acctAgree2 : AcctAgree world2 acs2 := by
  intro a
  rw [world2_get, initialWorld_get]
  by_cases hc : a = creator
  · subst hc
    rw [if_neg creator_ne_implAddr, if_neg creator_ne_proxyAddr, if_pos rfl]
    rfl
  · by_cases hi : a = implAddr
    · subst hi; rfl
    · by_cases hp : a = proxyAddr
      · subst hp; rfl
      · rw [if_neg hi, if_neg hp, if_neg hc]
        simp only [acs2, lookupA, Ne.symm hc, Ne.symm hi, Ne.symm hp, if_false]
        rfl

theorem storAgree2 : ∀ a k, storOf world2 a k = lookupS stor2 a k := by
  intro a k
  unfold storOf
  rw [world2_get, initialWorld_get]
  by_cases hi : a = implAddr
  · subst hi
    rw [if_pos rfl]
    show (Stor.empty.set 10 31337).get k = _
    rw [Stor.get_set_ite]
    simp only [stor2, lookupS, true_and]
    by_cases hk : (10 : B256) = k
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk]
      rfl
  · rw [if_neg hi]
    have hl : lookupS stor2 a k = 0 := by
      simp only [stor2, lookupS, Ne.symm hi, false_and, if_false]
    rw [hl]
    by_cases hp : a = proxyAddr
    · subst hp; rfl
    · rw [if_neg hp]
      split <;> rfl

/-- The Prague block environment's message 3, its frame and the machine it enters with. -/
def msg3 : Msg := initMsg .prague world2

def frame3 : Frame := Frame.ofCall msg3

def e3 : Evm := match frameEnterS frame3 acs2 with | .run e => e | .done _ => default

theorem e3_eq : frameEnterS frame3 acs2 = .run e3 := by kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
