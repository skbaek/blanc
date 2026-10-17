import Blanc.Lift.Curve3Pool.Observe

/-!
# The raw effect of a pool frame: what a walk delivers

The walks never need to know how `Model.step` is rendered on chain. A walk of entry `c` from a
frame `D` that ended in `post` delivers a `RawEffect D post e o`: an environment `e` the frame
observed (`EnvOf`), a model result `o` it computed (`step s e c = some o`, stated separately so
the walk can produce it from its own arithmetic facts), and

* `stor`: the pool's storage only changed at the call's **footprint** (`footprint c`, the model
  fields the entry may write), and each footprint slot reads the new state's field
  (`Fld.Reads`). Every other slot — the lock included, which the guarded entries set to `1` and
  clear before `STOP` — reads as at entry;
* `logs`: the frame's log list is its entry list, then every committed child's logs in order,
  then the model's events (`eventLog`). In every entry of this contract the frame's own `LOG`s
  come after its last external call, so this is exact with no premise on the children;
* `output`: the model's return word as 32 bytes, or for a `STOP` the entry output;
* `calls`: for a non-static frame, its state-changing calls are the model's (`modelCalls`).

`Refine.lean` turns a `RawEffect` into `Checkpoint post o.state` (the pure refinement).

## Events

The eleven event topics are `keccak256` of the event signatures; each is a `PUSH32` in the
runtime at its `LOG` site (TokenExchange 0x2c2a, AddLiquidity 0x186c, RemoveLiquidity 0x3011,
RemoveLiquidityOne 0x4739, RemoveLiquidityImbalance 0x3961, RampA 0x48e3, StopRampA 0x4973, and
the four admin topics), and the `LOGn` arity is the number of `indexed` fields plus one.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-! ## Fields and footprints -/

/-- The 21 model fields, one per storage slot. -/
inductive Fld
  | coin (i : Fin 3)
  | bal (i : Fin 3)
  | fee | adminFee | owner | token | initialA | futureA | initialATime | futureATime
  | adminActionsDeadline | transferOwnershipDeadline | futureFee | futureAdminFee | futureOwner
  | isKilled | killDeadline
deriving DecidableEq

namespace Fld

/-- A field's slot. -/
def slot : Fld → B256
  | coin i => coinSlot i
  | bal i => balanceSlot i
  | fee => feeSlot
  | adminFee => adminFeeSlot
  | owner => ownerSlot
  | token => tokenSlot
  | initialA => initialASlot
  | futureA => futureASlot
  | initialATime => initialATimeSlot
  | futureATime => futureATimeSlot
  | adminActionsDeadline => adminActionsDeadlineSlot
  | transferOwnershipDeadline => transferOwnershipDeadlineSlot
  | futureFee => futureFeeSlot
  | futureAdminFee => futureAdminFeeSlot
  | futureOwner => futureOwnerSlot
  | isKilled => isKilledSlot
  | killDeadline => killDeadlineSlot

/-- The storage reads the field of `s` at its slot (the `Abstracts` clause). -/
def Reads (stor : Stor) (s : State) : Fld → Prop
  | coin i => (stor.get (coinSlot i)).toNat = s.coins.get i
  | bal i => (stor.get (balanceSlot i)).toNat = s.balances.get i
  | fee => (stor.get feeSlot).toNat = s.fee
  | adminFee => (stor.get adminFeeSlot).toNat = s.adminFee
  | owner => (stor.get ownerSlot).toNat = s.owner
  | token => (stor.get tokenSlot).toNat = s.token
  | initialA => (stor.get initialASlot).toNat = s.initialA
  | futureA => (stor.get futureASlot).toNat = s.futureA
  | initialATime => (stor.get initialATimeSlot).toNat = s.initialATime
  | futureATime => (stor.get futureATimeSlot).toNat = s.futureATime
  | adminActionsDeadline => (stor.get adminActionsDeadlineSlot).toNat = s.adminActionsDeadline
  | transferOwnershipDeadline =>
      (stor.get transferOwnershipDeadlineSlot).toNat = s.transferOwnershipDeadline
  | futureFee => (stor.get futureFeeSlot).toNat = s.futureFee
  | futureAdminFee => (stor.get futureAdminFeeSlot).toNat = s.futureAdminFee
  | futureOwner => (stor.get futureOwnerSlot).toNat = s.futureOwner
  | isKilled => stor.get isKilledSlot = boolWord s.isKilled
  | killDeadline => (stor.get killDeadlineSlot).toNat = s.killDeadline

/-- Two states agree at the field. -/
def Same (s t : State) : Fld → Prop
  | coin i => s.coins.get i = t.coins.get i
  | bal i => s.balances.get i = t.balances.get i
  | fee => s.fee = t.fee
  | adminFee => s.adminFee = t.adminFee
  | owner => s.owner = t.owner
  | token => s.token = t.token
  | initialA => s.initialA = t.initialA
  | futureA => s.futureA = t.futureA
  | initialATime => s.initialATime = t.initialATime
  | futureATime => s.futureATime = t.futureATime
  | adminActionsDeadline => s.adminActionsDeadline = t.adminActionsDeadline
  | transferOwnershipDeadline => s.transferOwnershipDeadline = t.transferOwnershipDeadline
  | futureFee => s.futureFee = t.futureFee
  | futureAdminFee => s.futureAdminFee = t.futureAdminFee
  | futureOwner => s.futureOwner = t.futureOwner
  | isKilled => s.isKilled = t.isKilled
  | killDeadline => s.killDeadline = t.killDeadline

end Fld

/-- The three balance fields. -/
def balFlds : List Fld := [.bal 0, .bal 1, .bal 2]

/-- **The fields an entry may write** (every other field of the model's new state is the old
one, `step_footprint`). -/
def footprint : Call → List Fld
  | .addLiquidity _ _ | .exchange _ _ _ _ | .removeLiquidity _ _
  | .removeLiquidityImbalance _ _ | .removeLiquidityOneCoin _ _ _ | .donateAdminFees => balFlds
  | .rampA _ _ | .stopRampA => [.initialA, .futureA, .initialATime, .futureATime]
  | .commitNewFee _ _ => [.adminActionsDeadline, .futureFee, .futureAdminFee]
  | .applyNewFee => [.adminActionsDeadline, .fee, .adminFee]
  | .revertNewParameters => [.adminActionsDeadline]
  | .commitTransferOwnership _ => [.transferOwnershipDeadline, .futureOwner]
  | .applyTransferOwnership => [.transferOwnershipDeadline, .owner]
  | .revertTransferOwnership => [.transferOwnershipDeadline]
  | .killMe | .unkillMe => [.isKilled]
  | _ => []

/-- **The storage effect of a frame of `c`**: off the footprint's slots the storage reads as
before (slot by slot); at each footprint slot it reads the new state's field. -/
structure StorEffect (c : Call) (pre post : Stor) (s' : State) : Prop where
  kept : ∀ x, (∀ f ∈ footprint c, f.slot ≠ x) → post.get x = pre.get x
  written : ∀ f ∈ footprint c, f.Reads post s'

/-! ## Events and return data -/

def topicTokenExchange : B256 :=
  0x8b3e96f2b889fa771c53c981b40daf005f63f637f1869f707052d15a3dd97140
def topicAddLiquidity : B256 :=
  0x423f6495a08fc652425cf4ed0d1f9e37e571d9b9529b1c1c23cce780b2e7df0d
def topicRemoveLiquidity : B256 :=
  0xa49d4cf02656aebf8c771f5a8585638a2a15ee6c97cf7205d4208ed7c1df252d
def topicRemoveLiquidityOne : B256 :=
  0x9e96dd3b997a2a257eec4df9bb6eaf626e206df5f543bd963682d143300be310
def topicRemoveLiquidityImbalance : B256 :=
  0x173599dbf9c6ca6f7c3b590df07ae98a45d74ff54065505141e7de6c46a624c2
def topicCommitNewAdmin : B256 :=
  0x181aa3aa17d4cbf99265dd4443eba009433d3cde79d60164fde1d1a192beb935
def topicNewAdmin : B256 :=
  0x71614071b88dee5e0b2ae578a9dd7b2ebbe9ae832ba419dc0242cd065a290b6c
def topicCommitNewFee : B256 :=
  0x351fc5da2fbf480f2225debf3664a4bc90fa9923743aad58b4603f648e931fe0
def topicNewFee : B256 :=
  0xbe12859b636aed607d5230b2cc2711f68d70e51060e6cca1f575ef5d2fcc95d1
def topicRampA : B256 :=
  0xa2b71ec6df949300b59aab36b55e189697b750119dd349fcfa8c0f779e83c254
def topicStopRampA : B256 :=
  0x46e22fb3709ad289f62ce63d469248536dbc78d82b84a3d7e74ad606dc201938

/-- Three words (`uint256[3]` in event data). -/
def wordsV3 (v : V3) : Bytes := word v.v0 ++ word v.v1 ++ word v.v2

/-- **The log entry of a model event** from the pool at `pool`: topic 0 the signature hash,
then the `indexed` fields; the data the other fields as words, in declaration order. -/
def eventLog (pool : Adr) : Event → Log
  | .tokenExchange buyer i sold j bought =>
      ⟨pool, [topicTokenExchange, Nat.toB256 buyer], word i ++ word sold ++ word j ++ word bought⟩
  | .addLiquidity p amounts fees inv supply =>
      ⟨pool, [topicAddLiquidity, Nat.toB256 p],
        wordsV3 amounts ++ wordsV3 fees ++ word inv ++ word supply⟩
  | .removeLiquidity p amounts fees supply =>
      ⟨pool, [topicRemoveLiquidity, Nat.toB256 p], wordsV3 amounts ++ wordsV3 fees ++ word supply⟩
  | .removeLiquidityOne p amount coins =>
      ⟨pool, [topicRemoveLiquidityOne, Nat.toB256 p], word amount ++ word coins⟩
  | .removeLiquidityImbalance p amounts fees inv supply =>
      ⟨pool, [topicRemoveLiquidityImbalance, Nat.toB256 p],
        wordsV3 amounts ++ wordsV3 fees ++ word inv ++ word supply⟩
  | .commitNewAdmin d a => ⟨pool, [topicCommitNewAdmin, Nat.toB256 d, Nat.toB256 a], []⟩
  | .newAdmin a => ⟨pool, [topicNewAdmin, Nat.toB256 a], []⟩
  | .commitNewFee d f af => ⟨pool, [topicCommitNewFee, Nat.toB256 d], word f ++ word af⟩
  | .newFee f af => ⟨pool, [topicNewFee], word f ++ word af⟩
  | .rampA a0 a1 t0 t1 => ⟨pool, [topicRampA], word a0 ++ word a1 ++ word t0 ++ word t1⟩
  | .stopRampA a t => ⟨pool, [topicStopRampA], word a ++ word t⟩

/-- The output a model return word leaves: 32 bytes, or for `STOP` the output at entry. -/
def retOut (entry : Bytes) : Option Nat → Bytes
  | some r => word r
  | none => entry

/-! ## The walk contract -/

/-- **The raw effect of a successful pool frame** `D` ending in `post`, for the observed `e`
and the model result `o` (see the module note). -/
structure RawEffect (D : Exec.Deriv) (post : Devm) (e : Env) (o : Out) : Prop where
  env : EnvOf D e
  stor : StorEffect (decodeCall D.sevm) (entryStor D) (post.getStor D.sevm.currentTarget)
    o.state
  logs : post.logs = D.devm.logs ++ (children D).flatMap (fun c => c.post.logs) ++
    o.events.map (eventLog D.sevm.currentTarget)
  output : post.output = retOut D.devm.output o.ret
  calls : D.sevm.isStatic = false → CallsOf D = modelCalls D o.calls

end Blanc.Lift.Curve3Pool
