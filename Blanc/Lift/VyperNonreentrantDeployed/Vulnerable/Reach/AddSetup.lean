import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.InitRun
import Blanc.Lift.VyperNonreentrantDeployed.Token20.Check
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Check
import Blanc.Lift.NodeWalkOrig

/-! # V− setup, message 7: the first `add_liquidity` — the message and its world

The seventh root message: the code-free `creator` calls the clone `proxyAddr` with
`add_liquidity(uint256[2],uint256,address)` (selector `0x0c3e4b54`) for
`([1000, 1000], 0, attackerAddr)`, value 1000 wei (coin 0 is ETH), 1,000,000 gas, over the world
`approve` settles to.  That world is described by the shadows `acs6` (accounts) and `stor6`
(storage): the creator, the implementation, the clone, the token and the attacker, and the
storage of the initialized pool, the implementation's sentinel and the token's
`balanceOf[creator] = 10^6` and `allowance[creator][proxy] = 1000`.

The walk engine reads the world only through the shadows.  The one exception is the `SSTORE`
charge, which reads the transaction-original storage (`origState`, the input world itself for
a root message); the kernel facts are evaluated with the original state replaced by the closed
world `world6` built from the same shadows (`Blanc/Lift/NodeWalkOrig.lean` transports them
back), so they hold for every input world `W` the shadows describe. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun

/-- The forwarder's code tries (depth 6 covers its 45 bytes). -/
def fwdTriesM : CodeTries fwdCode 6 := CodeTries.ofCode fwdCode 6 (by decide) (by decide)

/-- `allowance[creator][proxyAddr]`'s slot at the token. -/
def allowCPSlot : B256 := Token20.allowSlot creator proxyAddr

/-- The accounts of the world `approve` settles to, storage dropped. -/
def accts6 : List (Adr × Acct) :=
  [(creator, ⟨0, creatorFunds, .empty, .empty⟩),
   (implAddr, ⟨1, 0, .empty, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code⟩),
   (proxyAddr, ⟨1, 0, .empty, fwdCode⟩),
   (tokenAddr, ⟨1, 0, .empty, Token20.code⟩),
   (attackerAddr, ⟨1, 0, .empty, AttackerR.code⟩)]

/-- The account shadow of that world. -/
def acs6 : AcctShadow := acctShadowOf accts6

/-- The token's two writes of the setup, newest first: `approve`'s allowance and the
constructor's mint. -/
def tokenWrites : StorShadow :=
  [((tokenAddr, allowCPSlot), 1000), ((tokenAddr, creator.toB256), 1000000)]

/-- The storage shadow of the world `approve` settles to. -/
def stor6 : StorShadow := tokenWrites ++ initWrites ++ stor2

/-- A closed world with exactly the accounts `acs6` and the storage `stor6`: the original
state of the kernel facts. -/
def world6 : State := stateFoldStor (stateFoldAcct default accts6) stor6.reverse

theorem storShadowOf_reverse (l : StorShadow) : storShadowOf l.reverse = l := by
  unfold storShadowOf
  rw [List.foldl_reverse]
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.foldr_cons, ih]

theorem world6_stor : ∀ a k, storOf world6 a k = lookupS stor6 a k := by
  intro a k
  rw [world6, storOf_stateFoldStor _ (storOf_stateFoldAcct accts6), storShadowOf_reverse]

theorem world6_acct : AcctAgree world6 acs6 :=
  acctAgree_stateFoldStor _ (acctAgree_stateFoldAcct accts6)

/-- Any world whose storage the shadow `stor6` describes has `world6`'s original storage. -/
theorem origAgree6 {W : State} (h : ∀ a k, storOf W a k = lookupS stor6 a k) :
    OrigAgree world6 W := fun a k => (world6_stor a k).trans (h a k).symm

/-- The ABI-encoded `add_liquidity([1000, 1000], 0, attackerAddr)`. -/
def addCall : Bytes :=
  [0x0c, 0x3e, 0x4b, 0x54] ++ abiWord 1000 ++ abiWord 1000 ++ abiWord 0 ++ abiWord attackerAddr.toNat

/-- The gas of message 7. -/
def addGas : Nat := 1000000

/-- Message 7: `creator` calls the clone with `add_liquidity`, value 1000, over world `W`. -/
def addMsg (fork : Fork) (W : State) : Msg :=
  { callMsg fork W proxyAddr fwdCode addCall addGas with value := 1000 }

/-- The kernel's message: Prague. -/
def msgA (W : State) : Msg := addMsg .prague W

def frameA (W : State) : Frame := Frame.ofCall (msgA W)

/-- The forwarder's entry machine. -/
def eA (W : State) : Evm := match frameEnterS (frameA W) acs6 with | .run e => e | .done _ => default

/-- The account shadow after the message's value transfer (1000 wei from the creator to the
clone). -/
def acsA : AcctShadow := acsTransfer (msgA world6) acs6

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
