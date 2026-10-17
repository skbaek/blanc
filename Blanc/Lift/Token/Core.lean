import Blanc.ExecutionTraceSettledFrames
import Blanc.Lift.ExactWalk
import Blanc.Lift.CallerProvenance

/-!
# Token interface core (contract-neutral)

What a token's **address** answers along a configured history, with no storage layout: a pure
`Book` (ledger, step per entered frame, decoded operation, balances, allowances, a well-formedness
predicate), the pure `BookLaws` the composition consumes, and the `Core` that ties a book to the
settled frames of a history (`replayAt`, `replayEnd`, the `balanceOf`/`transfer` answers).

Facets are separate structures over a `Book` or a `Core` (here `TransferLive`; `Erc20Abi` in
`Blanc/Lift/Token/Abi.lean`), so a further facet (for example a minter/supply facet) is added in its
own file without editing `Core`.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace

/-- What an entered token frame asks, as far as the core speaks of it. -/
inductive Op
  | balanceOf (holder : Adr)
  | transfer (dst : Adr) (amount : Nat)
  | transferFrom (src dst : Adr) (amount : Nat)
  | approve (spender : Adr) (amount : Nat)
  /-- A call that can only credit its caller (WETH9 `deposit`). -/
  | credit
  | other

/-- The most a holder's own call of this shape may debit the holder. -/
def Op.debit (holder : Adr) : Op → Nat
  | .transfer _ v => v
  | .transferFrom src _ v => if src = holder then v else 0
  | _ => 0

/-- A holder's own call that cannot raise an allowance or withdraw the holder's funds otherwise
than by an exact transfer. -/
def Op.HolderSafe : Op → Prop
  | .balanceOf _ => True
  | .transfer _ _ => True
  | .credit => True
  | _ => False

/-- The pure book of one token: an abstract ledger, the effect of one committed entry frame (its
message, `Sevm`), the answers, and a well-formedness predicate.  No storage layout. -/
structure Book where
  Ledger : Type
  step : Ledger → Sevm → Option Ledger
  op : Sevm → Op
  bal : Ledger → Adr → Nat
  allow : Ledger → Adr → Adr → Nat
  Good : Ledger → Prop

/-- Run a list of entered frames' messages. -/
def Book.run (B : Book) : B.Ledger → List Sevm → Option B.Ledger
  | l, [] => some l
  | l, a :: as => (B.step l a).bind fun l' => B.run l' as

/-- The pure laws the composition consumes. -/
structure BookLaws (B : Book) : Prop where
  /-- Nobody but the holder, or a spender the holder approved, lowers the holder's balance. -/
  holder_only : ∀ {l l' : B.Ledger} {a : Sevm} {h : Adr}, B.Good l → B.step l a = some l' →
    B.bal l' h < B.bal l h → a.caller = h ∨ 0 < B.allow l h a.caller
  /-- Only the owner raises its own allowances. -/
  allow_owner : ∀ {l l' : B.Ledger} {a : Sevm} {h g : Adr}, B.Good l → B.step l a = some l' →
    B.allow l h g < B.allow l' h g → a.caller = h
  /-- A holder's own holder-safe call debits it at most by its declared amount. -/
  holder_debit : ∀ {l l' : B.Ledger} {a : Sevm} {h : Adr}, B.Good l → B.step l a = some l' →
    a.caller = h → (B.op a).HolderSafe → B.bal l h ≤ B.bal l' h + (B.op a).debit h
  /-- A committed transfer to someone else debits the sender exactly. -/
  transfer_exact : ∀ {l l' : B.Ledger} {a : Sevm} {dst : Adr} {v : Nat}, B.Good l →
    B.step l a = some l' → B.op a = .transfer dst v → dst ≠ a.caller →
    B.bal l' a.caller + v = B.bal l a.caller
  /-- A holder's own holder-safe call does not raise the holder's allowances. -/
  allow_safe : ∀ {l l' : B.Ledger} {a : Sevm} {h g : Adr}, B.Good l → B.step l a = some l' →
    a.caller = h → (B.op a).HolderSafe → B.allow l' h g ≤ B.allow l h g

/-- The frame a caller enters at the token's address: storage owner and code address are both the
token (a proxy's entry frame, never its delegatecalled implementation frame). -/
def IsEntry (T : Adr) (f : Exec.Frame) : Prop :=
  f.sevm.currentTarget = T ∧ f.sevm.codeAddress = some T

open Classical in
/-- The messages of the non-static entry frames among `fs`, in order. -/
noncomputable def entryAsks (T : Adr) (fs : List Exec.Frame) : List Sevm :=
  (fs.filter fun f => decide (IsEntry T f ∧ f.sevm.isStatic = false)).map (·.sevm)

/-- **The token core: what the address `T` answers along a configured history.**  `Hist` is the
instance's trace-local premise slot (code or implementation unchanged, footprint, hash freshness);
`ledgerOf` reads a world's booked ledger (it may depend on the trace, for a trace-selected
footprint).  The position-indexed answer is `replayAt`: at the entry of every settled frame the
booked ledger is the book run over exactly the entered writer frames before it. -/
structure Core (T : Adr) (B : Book) where
  Hist : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain},
    ConfiguredHistoryTrace cfg checkpoint future → Prop
  ledgerOf : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain},
    ConfiguredHistoryTrace cfg checkpoint future → State → B.Ledger
  /-- Holders whose `balanceOf` answer the core vouches for (WETH9: tracked rows). -/
  Answerable : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain},
    ConfiguredHistoryTrace cfg checkpoint future → Adr → Prop
  replayAt : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      tr.settledFrames = before ++ f :: after →
      B.run (ledgerOf tr checkpoint.state) (entryAsks T before) = some (ledgerOf tr f.pre.state)
  replayEnd : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      B.run (ledgerOf tr checkpoint.state) (entryAsks T tr.settledFrames) =
        some (ledgerOf tr future.state)
  goodStart : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      B.Good (ledgerOf tr checkpoint.state)
  goodAt : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ f ∈ tr.settledFrames, B.Good (ledgerOf tr f.pre.state)
  /-- A committed `balanceOf(h)` entry frame, static or not, answers the booked balance there. -/
  balanceAnswer : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ g ∈ tr.settledFrames, IsEntry T g → ∀ {h : Adr}, B.op g.sevm = .balanceOf h →
        Answerable tr h →
        g.post.output = (Nat.toB256 (B.bal (ledgerOf tr g.pre.state) h)).toBytes
  /-- A committed `transfer` entry frame answers success. -/
  transferAnswer : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ g ∈ tr.settledFrames, IsEntry T g → ∀ {dst : Adr} {v : Nat},
        B.op g.sevm = .transfer dst v →
        g.post.output = [] ∨ (32 ≤ g.post.output.length ∧
          Bytes.toB256 (g.post.output.sliceD 0 32 0) ≠ 0)
  /-- A settled frame at `T` that is not an entry is entered only from frames at `T` (a proxy's
  delegatecalled implementation frame); in particular every frame a foreign contract calls at `T`
  is an entry. -/
  decodes : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ g ∈ tr.settledFrames, g.sevm.currentTarget = T → ¬ IsEntry T g →
        ∀ P ∈ tr.settledFrames, g ∈ Exec.childFrames P.run → P.sevm.currentTarget = T

/-- **Facet: frame-level transfer liveness** (input to C4(b)).  At any world the instance accepts,
a fresh entry frame of `T` decoding an affordable `transfer` runs to success at an exact,
world-determined cost, answering success. -/
structure TransferLive (T : Adr) (B : Book) where
  WorldOk : State → Prop
  FrameOk : Sevm → State → Prop
  ledgerAt : State → B.Ledger
  cost : Sevm → Devm → Nat
  live : ∀ {sevm : Sevm} {pre : Devm} {G : Nat} {dst : Adr} {v : Nat},
    sevm.currentTarget = T → sevm.codeAddress = some T → sevm.code = pre.state.getCode T →
    FrameOk sevm pre.state → CoveredFork sevm.benvStat.fork →
    sevm.value = 0 → sevm.isStatic = false → pre.output = [] →
    WorldOk pre.state → B.op sevm = .transfer dst v → v ≤ B.bal (ledgerAt pre.state) sevm.caller →
    cost sevm pre ≤ G → cost sevm pre + gCallStipend ≤ G →
    ∃ post, Nonempty (Exec 0 sevm (St pre [] Mem.empty G) (.ok post)) ∧ post.gasLeft + cost sevm pre = G ∧
      post.output = (Nat.toB256 1).toBytes ∧ WorldOk post.state ∧
      (dst ≠ sevm.caller → B.bal (ledgerAt post.state) sevm.caller + v =
        B.bal (ledgerAt pre.state) sevm.caller)

end Blanc.Lift.Token
