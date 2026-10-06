import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach.Init
import Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.Deploy
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.Deploy
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Check
import Blanc.Lift.NodeWalkOrig
import Blanc.Lift.WitnessShadow

/-! # The V+ funding messages: worlds, messages and shadows

After the four setup messages (`Reach.setup_init`), the code-free `creator` sends, each from the
previous settled world:

5. a CREATE of the shared synthetic token `T` at `tokenAddr = 0x3333…3333` (its constructor
   mints `balanceOf[creator] := 10^6`; `Token20.Creation`), 200,000 gas;
6. a CREATE of the labelled synthetic receiver `R` at `receiverAddr = 0x6666…6666`
   (`ReceiverR`: on receiving ETH it attempts `add_liquidity([v, 0], 0)` through the clone with
   the value, and returns normally when that fails), 100,000 gas;
7. `T.approve(P, 1000)`, 100,000 gas;
8. `P.add_liquidity([1000, 1000], 0)` with value 1000, 1,000,000 gas;

and then (V5) `P.remove_liquidity(200, [0, 0], R)`, 1,000,000 gas.  The creations use V1's
`createMsg`; the calls use V2's root-call conventions (`Init.callMsg`: chain id 1, timestamp
1700000000, depth 1024, empty accessed sets) with the target, code and value set
(`rootCall`).

Every input world is a closed term: `world4` is the settled world of `set_oracle`, `world5` and
`world6` are the creations' settled worlds as the operations Jaune applies, and each later world
is the previous call's halted machine's state.  The kernel facts of a call are evaluated over a
message whose original state is replaced by `origOf stor` (a cheap world holding exactly the
storage the input world's shadow describes) and transported to the real message
(`Blanc/Lift/NodeWalkOrig.lean`): evaluating the real original state would re-run every earlier
message. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

/-- The labelled synthetic receiver's address (disclosed; not a historical account). -/
def receiverAddr : Adr := 0x6666666666666666666666666666666666666666

/-- The world `set_oracle` settles to: the clean pool. -/
@[irreducible] def world4 : State := (dO world3).state

/-- **Message 5**: the synthetic token creation input at `tokenAddr`, 200,000 gas. -/
def tokenCreateMsg (fork : Fork) (W : State) : Msg :=
  createMsg fork W tokenAddr Blanc.Lift.VyperNonreentrantDeployed.Token20.Creation.creationCode
    200000

/-- **Message 6**: the synthetic receiver creation input at `receiverAddr`, 100,000 gas. -/
def receiverCreateMsg (fork : Fork) (W : State) : Msg :=
  createMsg fork W receiverAddr
    Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.creationCode 100000

/-- The token creation's settled world, as the operations Jaune applies. -/
def world5 : State :=
  ((CreateEntry.entryState world4 creator tokenAddr).setStorVal tokenAddr creator.toB256
    1000000).setCode tokenAddr Blanc.Lift.VyperNonreentrantDeployed.Token20.code

/-- The receiver creation's settled world, as the operations Jaune applies. -/
def world6 : State :=
  (CreateEntry.entryState world5 creator receiverAddr).setCode receiverAddr
    Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code

/-! ## Root calls -/

/-- A root call from `creator` over world `W` to `target` running `code`, with value `v`
(V2's `callMsg` conventions). -/
def rootCall (fork : Fork) (W : State) (target : Adr) (code : ByteArray) (data : Bytes)
    (gas : Nat) (v : B256) : Msg :=
  { callMsg fork W data gas with
    target := some target, currentTarget := target, codeAddress := some target, code := code,
    value := v }

/-- The kernel's message: Prague, original state `O`. -/
def kCall (W O : State) (target : Adr) (code : ByteArray) (data : Bytes) (gas : Nat) (v : B256) :
    Msg :=
  (rootCall .prague W target code data gas v).withOrig O

theorem rootCall_re (g : Fork) (W O : State) (target : Adr) (code : ByteArray) (data : Bytes)
    (gas : Nat) (v : B256) :
    rootCall g W target code data gas v =
      ((kCall W O target code data gas v).withFork g).withOrig W := rfl

/-- The pool's clone runtime. -/
abbrev fwd : ByteArray := Blanc.forwarderCode Blanc.curvePlainImpl847e

/-- `approve(address,uint256)` = `0x095ea7b3` with `(P, 1000)`. -/
def approveCall : Bytes := [0x09, 0x5e, 0xa7, 0xb3] ++ Witness.word proxyAddr.toNat ++ Witness.word 1000

/-- `add_liquidity(uint256[2],uint256)` = `0x0b4c7e4d` with `([1000, 1000], 0)`. -/
def addCall : Bytes :=
  [0x0b, 0x4c, 0x7e, 0x4d] ++ Witness.word 1000 ++ Witness.word 1000 ++ Witness.word 0

/-- `remove_liquidity(uint256,uint256[2],address)` = `0x3eb1719f` with `(200, [0, 0], R)`. -/
def removeCall : Bytes :=
  [0x3e, 0xb1, 0x71, 0x9f] ++ Witness.word 200 ++ Witness.word 0 ++ Witness.word 0 ++
    Witness.word receiverAddr.toNat

/-- **Message 7**: `T.approve(P, 1000)`, 100,000 gas. -/
def approveMsg (fork : Fork) (W : State) : Msg :=
  rootCall fork W tokenAddr Blanc.Lift.VyperNonreentrantDeployed.Token20.code approveCall 100000 0

/-- **Message 8**: `P.add_liquidity([1000, 1000], 0)` with 1000 wei, 1,000,000 gas. -/
def addMsg (fork : Fork) (W : State) : Msg :=
  rootCall fork W proxyAddr fwd addCall 1000000 1000

/-- **The V5 call**: `P.remove_liquidity(200, [0, 0], R)`, 1,000,000 gas. -/
def removeMsg (fork : Fork) (W : State) : Msg :=
  rootCall fork W proxyAddr fwd removeCall 1000000 0

/-! ## Shadows -/

/-- The token's account once created (nonce 1, no balance, the registered runtime). -/
def tokenAccount : Acct :=
  { Acct.nil with nonce := 1, code := Blanc.Lift.VyperNonreentrantDeployed.Token20.code }

/-- The receiver's account once created. -/
def receiverAccount : Acct :=
  { Acct.nil with nonce := 1, code := Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code }

/-- The accounts after the creations. -/
def accts6 : List (Adr × Acct) := accts0 ++ [(tokenAddr, tokenAccount), (receiverAddr, receiverAccount)]

def acs6 : AcctShadow := acctShadowOf accts6

/-- The storage after the token creation: the mint, then the clean pool. -/
def stor5 : StorShadow := ((tokenAddr, creator.toB256), 1000000) :: storOracle

/-- The token's tries (depth 9 covers its 299 bytes). -/
def tokenTries : CodeTries Blanc.Lift.VyperNonreentrantDeployed.Token20.code 9 :=
  CodeTries.ofCode Blanc.Lift.VyperNonreentrantDeployed.Token20.code 9 (by decide +kernel)
    (by decide +kernel)

/-- The receiver's tries. -/
abbrev recvTries : CodeTries Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code 7 :=
  Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.codeTries

/-! ## Installing an account -/

/-- A world that differs from `W` only at `T`, where it holds `ac`, is described by the shadows
of `W` with `ac`'s view and storage added. -/
theorem worldIs_install {W post : State} {acs : AcctShadow} {stor stor' : StorShadow} {T : Adr}
    {ac : Acct} (hW : WorldIs W acs stor) (hT : post.get T = ac)
    (hO : ∀ a, a ≠ T → post.get a = W.get a) (hS : ∀ k, ac.stor.get k = lookupS stor' T k)
    (hS' : ∀ a k, a ≠ T → lookupS stor' a k = lookupS stor a k) :
    WorldIs post ((T, acctView ac) :: acs) stor' := by
  refine ⟨fun a => ?_, fun a k => ?_⟩
  · by_cases h : T = a
    · subst h; rw [hT]; simp only [lookupA, ↓reduceIte]
    · rw [hO a (Ne.symm h)]; simp only [lookupA, h, ↓reduceIte]; exact hW.1 a
  · by_cases h : a = T
    · subst h; unfold storOf; rw [hT]; exact hS k
    · unfold storOf; rw [hO a h, hS' a k h]; exact hW.2 a k

theorem lookupS_storOracle_ne {a : Adr} (ha : a ≠ proxyAddr) (hi : a ≠ implAddr) (k : B256) :
    lookupS storOracle a k = 0 := by
  have h := lookupS_append_of_absent (p := []) (l := storOracle) (a := a) (fun e he => by
    simp only [storOracle, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> first | exact Ne.symm ha | exact Ne.symm hi) k
  simpa only [List.nil_append, lookupS] using h

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
