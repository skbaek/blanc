import Blanc.Lift.Usdc.SignedPaths
import Blanc.Lift.Usdc.LibSeam
import Blanc.Lift.Usdc.HistoryReplay
import Blanc.Lift.Usdc.HistFFacts
import Blanc.Lift.HistoryGas
import Blanc.ExecutionTraceEntered

/-!
# The Pair never signs a USDC entry (unit N, amendment A10)

`usdc_neverSigner_pairCode`: along a `UsdcHistF` history (so along every `UsdcHist` history,
`UsdcHist.toUsdcHistF`), no settled entry frame of the proxy whose
book signer is a holder running the Pair's runtime commits (for any code semantics with that image;
`Blanc/Composition/UsdcNeverSigner.lean` instantiates `pairSem` as `usdc_neverSigner_pair`).  An entry from the admin word asks an admin selector
(`proxy_admin_selectors`), never a signed one; any other entry forwards to one implementation frame
with the same value and calldata (`usdc_entry_forward`), which is itself settled, and no successful
implementation frame is signed by the Pair (`impl_signed_not_ok`, F7) given the history gas bound
(F8), the Pair's persisted code, the library's code, the precompile premise and `LibRejects` (F6).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.Token

/-- A signed USDC message asks one of the eight signed selectors. -/
theorem usdcSigner_selector {e : Sevm} {a : Adr} (h : usdcSigner e = some a) :
    Blanc.Sevm.selector e ∈ [0x9fd5a6cf, 0xd505accf, 0xcf092995, 0xe3ee160e, 0x88b7ab63, 0xef55bec6,
      0xb7b72899, 0x5a049a70] := by
  unfold usdcSigner at h
  split at h
  · rename_i o s v hdec
    rcases (decode_permit hdec).1 with s | s <;> rw [s] <;> decide
  · rename_i s d v n hdec
    rcases (decode_twa hdec).1 with s | s <;> rw [s] <;> decide
  · rename_i s d v n hdec
    rcases (decode_rwa hdec).1 with s | s <;> rw [s] <;> decide
  · rename_i a n hdec
    rcases (decode_cancel hdec).1 with s | s <;> rw [s] <;> decide
  · cases h

/-- **A holder running the Pair's code never signs a settled USDC entry**, for any code semantics
whose image is the Pair's runtime (the composition instantiates `pairSem`). -/
theorem usdc_neverSigner_pairCode {P pair : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHistF P K₀ tr) {sem : CodeSem} (image : sem.image = some UniswapV2Pair.code.toList)
    (installed : some (checkpoint.state.getCode pair).toList = sem.image)
    (pairNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp pair)
    (hsilent : NoStaticAnswer UniswapV2Pair.code 0x1626ba7e) :
    NeverSigner P (usdcBookS P) tr pair := by
  refine ⟨fun g member entry _ signed => ?_⟩
  change usdcSigner g.sevm = some pair at signed
  have facts := usdc_settled_factsF tr hist g member
  have codeEq := usdc_entry_codeF tr hist member entry
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  obtain ⟨r, hafter⟩ := tr.settledFrames_contig split
  have inDesc : ∀ c ∈ Exec.descendantFrames g.run, c ∈ tr.settledFrames := fun c hc => by
    rw [split, hafter]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hc))
  revert inDesc codeEq signed
  refine frame_cases_ok (Q := fun g => IsEntry P g → SettledFactsF P (historyKeyUniverse P tr K₀)
    (adminOf checkpoint.state P) g → usdcSigner g.sevm = some pair → g.sevm.code = Proxy.code →
    (∀ c ∈ Exec.descendantFrames g.run, c ∈ tr.settledFrames) → False) g facts.pc ?_ entry facts
  intro sevm pre post run _ entry facts signed codeEq inDesc
  by_cases admin : sevm.caller = adminOf pre.state P
  · have admin' : sevm.caller = adminOf pre.state sevm.currentTarget := by rw [entry.1]; exact admin
    have sel := usdcSigner_selector signed
    rcases proxy_admin_selectors run codeEq facts.fork admin' with (s | s) | s
    · rw [s] at sel; exact absurd sel (by decide)
    · rw [s] at sel; exact absurd sel (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at s
      rcases s with s | s | s <;> rw [s] at sel <;> exact absurd sel (by decide)
  obtain ⟨c, -, desc, ct, -, -, cvalue, cdata, -, ccode⟩ :=
    usdc_entry_forward run codeEq facts.fork entry.1 facts.codes facts.slots.1 admin facts.data
  have cmem : c ∈ tr.settledFrames := inDesc c (by rw [desc]; exact List.mem_cons_self)
  have cfacts := usdc_settled_factsF tr hist c cmem
  have fresh : Exec.FreshEntry c.sevm c.pre :=
    tr.rawFrames_entered enteredCondition_fresh _ (tr.settled_mem_rawFrames c cmem)
  have gas : c.pre.gasMeasure < 2 ^ 256 := tr.rawFrame_gas _ (tr.settled_mem_rawFrames c cmem)
  have pairCode : c.pre.getCode pair = UniswapV2Pair.code :=
    bytes_eq_of_image ((tr.settled_codeImage sem pair installed c cmem).trans image)
  have csigned : usdcSigner c.sevm = some pair := by
    unfold usdcSigner; rw [decodeCall_congr cvalue cdata]; exact signed
  revert ct ccode fresh gas pairCode csigned
  refine frame_cases_ok (Q := fun c => SettledFactsF P (historyKeyUniverse P tr K₀)
    (adminOf checkpoint.state P) c → c.sevm.currentTarget = P → c.sevm.code = Impl.code →
    Exec.FreshEntry c.sevm c.pre → c.pre.gasMeasure < 2 ^ 256 →
    c.pre.getCode pair = UniswapV2Pair.code → usdcSigner c.sevm = some pair → False) c cfacts.pc ?_
    cfacts
  intro sevm' pre' post' run' _ cfacts ct ccode fresh gas pairCode csigned
  exact impl_signed_not_ok run' ccode cfacts.fork cfacts.fork.rules_stateGas_none ct fresh.2 fresh.1
    gas cfacts.codes.2.2 pairCode (pairNotPrecompile _ cfacts.fork) (LibSeam.lib_rejects_pair hsilent) csigned

end Blanc.Lift.Usdc
