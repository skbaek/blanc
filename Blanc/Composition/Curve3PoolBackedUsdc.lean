import Blanc.Composition.Curve3PoolBackedUsdt
import Blanc.Composition.UsdcTokenCore
import Blanc.Lift.Usdc.EntryPositional
import Blanc.Lift.Usdc.V2Answer
import Blanc.Lift.Usdc.V2_1Answer

/-!
# The pool's books of USDC are covered

USDC reads one word two ways: FiatTokenV2_2 its low 255 bits, the earlier versions the whole word. The walk reads the bits
throughout. Entering a frame the reading can only rise, since bits are at most the word; leaving one running the earlier
versions it is equal, by `UsdcMovesOnce.below`. A reader's answer is the bits at its position: under V2_2 by its code, and
under an earlier version because by `UsdcMovesOnce.onward` nothing before it ran V2_2, so its position is the cut or the
exit of a frame running words.
-/

namespace Blanc.Composition.Curve3PoolBacked

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolPublic Blanc.Composition.Curve3PoolCoinKeep
open Blanc.Lift.Curve3Pool (answerWord balanceOfData transferSel transferFromSel adrOf)
open Blanc.Lift.CurveCoins (PoolCoinSel)

variable {d : Deployment} {future : BlockChain} {h : MainnetHistory d.minter.post future}

/-- USDC's entry for the pool, as a book: the low 255 bits at every position. -/
noncomputable def usdcBook : CoinBook where
  T := usdc
  V := Usdc.ledgerView
  Obs := Usdc.ChainObs usdc
  Good := Usdc.EntryGood usdc
  held := Usdc.heldAt usdc pool
  debit := ownDebit pool
  credit := ownCredit pool
  Rd := fun _ m => Usdc.balanceBits (m (Usdc.balSlot pool))

theorem pool_bal_ne_impl : Usdc.balSlot pool ≠ Usdc.implSlot := Usdc.entryApart_pool.impl
theorem pool_bal_ne_admin : Usdc.balSlot pool ≠ Usdc.adminSlot := Usdc.entryApart_pool.admin

theorem view_bal (w : StorWords) : Usdc.ledgerView w (Usdc.balSlot pool) = w (Usdc.balSlot pool) :=
  Usdc.ledgerView_bal pool_bal_ne_impl pool_bal_ne_admin

/-! ## What USDC answers -/

/-- **A committed `balanceOf` frame of the proxy answers the entry it names, as its version reads it.** -/
theorem usdc_balanceOf_answer {F : Exec.Frame} (pc : F.pc = 0) (code : F.sevm.code = Usdc.Proxy.code)
    (fork : HistFork F.sevm.benvStat.fork) (has : (F.pre.getCode F.sevm.currentTarget).toList ≠ [])
    (notAdmin : F.sevm.caller ≠ Usdc.adminOf F.pre.state F.sevm.currentTarget)
    (certified : Usdc.UsdcCertified F.pre F.sevm.currentTarget) (size : F.sevm.data.length < 2 ^ 256)
    (sel : Blanc.Sevm.selector F.sevm = 0x70a08231) :
    (Usdc.V22At F.sevm.currentTarget F → F.post.output =
      (Usdc.lo255 &&& (F.pre.state.getStor F.sevm.currentTarget).get (Usdc.balSlot (Sevm.dataWord F.sevm 4).toAdr)).toBytes) ∧
    (¬ Usdc.V22At F.sevm.currentTarget F → F.post.output =
      ((F.pre.state.getStor F.sevm.currentTarget).get (Usdc.balSlot (Sevm.dataWord F.sevm 4).toAdr)).toBytes) := by
  obtain ⟨fpc, sevm, pre, out, run, committed⟩ := F
  dsimp only at pc code fork has notAdmin certified size sel ⊢
  subst pc
  cases out with
  | error e => cases committed
  | ok post =>
  have hsg := fork.stateGas_none
  have version : CurveCoins.UsdcVersion (pre.getCode (pre.getStorVal sevm.currentTarget Usdc.implSlot).toAdr) := certified.1
  obtain ⟨G, E⟩ := Usdc.proxy_entry_child run code hsg fork.bal_none has notAdmin version.not_delegation
    (certified.2.2 _) size
  have gfork : HistFork G.sevm.benvStat.fork := by rw [E.stat]; exact fork
  have gsel : Blanc.Sevm.selector G.sevm = 0x70a08231 := by
    simp only [Blanc.Sevm.selector, Sevm.dataWord, E.data] at sel ⊢
    exact sel
  have gword : Sevm.dataWord G.sevm 4 = Sevm.dataWord sevm 4 := by
    simp only [Sevm.dataWord, E.data]
  have gval : ∀ k, G.pre.getStorVal G.sevm.currentTarget k = (pre.state.getStor sevm.currentTarget).get k := fun k => by
    rw [E.target]
    exact congrArg (fun s => Stor.get s k) E.preStor
  have out' : post.output = G.post.output := E.output
  have st : G.pre = St G.pre [] Mem.empty G.pre.gasLeft := by
    rw [← E.fresh.1, ← E.fresh.2]
    exact St.self' _
  constructor
  · intro v22
    have gcode : G.sevm.code = Usdc.Impl.code := E.code.trans v22
    have r := run_of_frame Usdc.Impl.cert_check rfl E.pc gcode gfork.stateGas_none
    rw [E.fresh.1, E.fresh.2] at r
    have o := UsdcToken.frame_balanceOf_output gfork gsel r
    rw [gword, gval] at o
    change _ = (Usdc.lo255 &&& _).toBytes
    exact out'.trans o
  · intro notV22
    rcases version with c | c | c
    · have gcode := E.code.trans c
      have r := run_of_frame Usdc.ImplV2.cert_check rfl E.pc gcode gfork.stateGas_none
      have o := Usdc.ImplV2.frame_balanceOf_output gfork E.wf gsel r
      rw [gword, gval] at o
      exact out'.trans o
    · have gcode := E.code.trans c
      have r := run_of_frame Usdc.ImplV2_1.cert_check rfl E.pc gcode gfork.stateGas_none
      have o := Usdc.ImplV2_1.frame_balanceOf_output gfork E.wf gsel r
      rw [gword, gval] at o
      exact out'.trans o
    · exact (notV22 c).elim

end Blanc.Composition.Curve3PoolBacked
