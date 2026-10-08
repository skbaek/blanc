import Blanc.Lift.UniswapV2Pair.PairDispatchCursor
import Blanc.Lift.CursorNoExecSuffix
import Blanc.Lift.UniswapV2Pair.StaticViewClassify

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Literal rows of the Pair dispatcher used by the call-free entries. -/
inductive PairNoCallComparison
  | at002b | at0036 | at0041 | at004c | at0057 | at0071 | at007d | at0088 | at0097 | at00a3 | at00ae | at00b9 | at00c4 | at00d3 | at00df | at00ea | at00f9 | at0105 | at0110 | at011b | at0126 | at0131 | at0140 | at014c | at0157 | at0166 | at0172 | at017d | at0188 | at0197 | at01a3 | at01ae

def PairNoCallComparison.bytes : PairNoCallComparison → List UInt8
  | .at002b => [0xba, 0x9a, 0x7a, 0x56]
  | .at0036 => [0xd2, 0x12, 0x20, 0xa7]
  | .at0041 => [0xd2, 0x12, 0x20, 0xa7]
  | .at004c => [0xd5, 0x05, 0xac, 0xcf]
  | .at0057 => [0xdd, 0x62, 0xed, 0x3e]
  | .at0071 => [0xba, 0x9a, 0x7a, 0x56]
  | .at007d => [0xbc, 0x25, 0xcf, 0x77]
  | .at0088 => [0xc4, 0x5a, 0x01, 0x55]
  | .at0097 => [0x7e, 0xce, 0xbe, 0x00]
  | .at00a3 => [0x7e, 0xce, 0xbe, 0x00]
  | .at00ae => [0x89, 0xaf, 0xcb, 0x44]
  | .at00b9 => [0x95, 0xd8, 0x9b, 0x41]
  | .at00c4 => [0xa9, 0x05, 0x9c, 0xbb]
  | .at00d3 => [0x6a, 0x62, 0x78, 0x42]
  | .at00df => [0x70, 0xa0, 0x82, 0x31]
  | .at00ea => [0x74, 0x64, 0xfc, 0x3d]
  | .at00f9 => [0x23, 0xb8, 0x72, 0xdd]
  | .at0105 => [0x36, 0x44, 0xe5, 0x15]
  | .at0110 => [0x36, 0x44, 0xe5, 0x15]
  | .at011b => [0x48, 0x5c, 0xc9, 0x55]
  | .at0126 => [0x59, 0x09, 0xc0, 0xd5]
  | .at0131 => [0x5a, 0x3d, 0x54, 0x93]
  | .at0140 => [0x23, 0xb8, 0x72, 0xdd]
  | .at014c => [0x30, 0xad, 0xf8, 0x1f]
  | .at0157 => [0x31, 0x3c, 0xe5, 0x67]
  | .at0166 => [0x09, 0x5e, 0xa7, 0xb3]
  | .at0172 => [0x09, 0x5e, 0xa7, 0xb3]
  | .at017d => [0x0d, 0xfe, 0x16, 0x81]
  | .at0188 => [0x18, 0x16, 0x0d, 0xdd]
  | .at0197 => [0x02, 0x2c, 0x0d, 0x9f]
  | .at01a3 => [0x06, 0xfd, 0xde, 0x03]
  | .at01ae => [0x09, 0x02, 0xf1, 0xac]

def PairNoCallComparison.target : PairNoCallComparison → List UInt8
  | .at002b => [0x00, 0x97]
  | .at0036 => [0x00, 0x71]
  | .at0041 => [0x05, 0xda]
  | .at004c => [0x05, 0xe2]
  | .at0057 => [0x06, 0x40]
  | .at0071 => [0x05, 0x97]
  | .at007d => [0x05, 0x9f]
  | .at0088 => [0x05, 0xd2]
  | .at0097 => [0x00, 0xd3]
  | .at00a3 => [0x04, 0xd7]
  | .at00ae => [0x05, 0x0a]
  | .at00b9 => [0x05, 0x56]
  | .at00c4 => [0x05, 0x5e]
  | .at00d3 => [0x04, 0x69]
  | .at00df => [0x04, 0x9c]
  | .at00ea => [0x04, 0xcf]
  | .at00f9 => [0x01, 0x66]
  | .at0105 => [0x01, 0x40]
  | .at0110 => [0x04, 0x16]
  | .at011b => [0x04, 0x1e]
  | .at0126 => [0x04, 0x59]
  | .at0131 => [0x04, 0x61]
  | .at0140 => [0x03, 0xad]
  | .at014c => [0x03, 0xf0]
  | .at0157 => [0x03, 0xf8]
  | .at0166 => [0x01, 0x97]
  | .at0172 => [0x03, 0x15]
  | .at017d => [0x03, 0x62]
  | .at0188 => [0x03, 0x93]
  | .at0197 => [0x01, 0xbe]
  | .at01a3 => [0x02, 0x59]
  | .at01ae => [0x02, 0xd6]

def PairNoCallComparison.isGt : PairNoCallComparison → Bool
  | .at002b | .at0036 | .at0097 | .at00f9 | .at0105 | .at0166 => true
  | _ => false

def PairNoCallComparison.op (q : PairNoCallComparison) : Rinst :=
  if q.isGt then .gt else .eq

def PairNoCallComparison.line (q : PairNoCallComparison) : List Ninst :=
  [.reg (.dup 0), .push q.bytes (by cases q <;> decide),
   .reg q.op, .push q.target (by cases q <;> decide)]

def PairNoCallComparison.tail : PairNoCallComparison → SFunc
  | .at002b => (.branch t_0036_c0 t_0097_c0)
  | .at0036 => (.branch t_0041_c0 t_0071_c0)
  | .at0041 => (.branchTo t_004c_c0 75)
  | .at004c => (.branchTo t_0057_c0 76)
  | .at0057 => (.branchTo t_0062_c0 77)
  | .at0071 => (.branchTo t_007d_c0 79)
  | .at007d => (.branchTo t_0088_c0 80)
  | .at0088 => (.branchTo t_0093_c0 81)
  | .at0097 => (.branch t_00a3_c0 t_00d3_c0)
  | .at00a3 => (.branchTo t_00ae_c0 82)
  | .at00ae => (.branchTo t_00b9_c0 83)
  | .at00b9 => (.branchTo t_00c4_c0 84)
  | .at00c4 => (.branchTo t_00cf_c0 85)
  | .at00d3 => (.branchTo t_00df_c0 86)
  | .at00df => (.branchTo t_00ea_c0 87)
  | .at00ea => (.branchTo t_00f5_c0 88)
  | .at00f9 => (.branch t_0105_c0 t_0166_c0)
  | .at0105 => (.branch t_0110_c0 t_0140_c0)
  | .at0110 => (.branchTo t_011b_c0 89)
  | .at011b => (.branchTo t_0126_c0 90)
  | .at0126 => (.branchTo t_0131_c0 91)
  | .at0131 => (.branchTo t_013c_c0 92)
  | .at0140 => (.branchTo t_014c_c0 93)
  | .at014c => (.branchTo t_0157_c0 94)
  | .at0157 => (.branchTo t_0162_c0 95)
  | .at0166 => (.branch t_0172_c0 t_0197_c0)
  | .at0172 => (.branchTo t_017d_c0 96)
  | .at017d => (.branchTo t_0188_c0 97)
  | .at0188 => (.branchTo t_0193_c0 98)
  | .at0197 => (.branchTo t_01a3_c0 99)
  | .at01a3 => (.branchTo t_01ae_c0 100)
  | .at01ae => (.branchTo t_01b9_c0 101)

def PairNoCallComparison.body (q : PairNoCallComparison) : SFunc :=
  q.line.foldr SFunc.next q.tail

def PairNoCallComparison.compute (q : PairNoCallComparison) (sel : B256) : B256 :=
  if q.isGt then B256.gtCheck (Bytes.toB256 q.bytes) sel
  else B256.eqCheck (Bytes.toB256 q.bytes) sel

/-- Each literal row retains the selector, memory and complete world. -/
theorem PairNoCallComparison.line_inv {sevm : Sevm} {b d : Devm}
    {S : List B256} {M : Mem} {G : Nat} (q : PairNoCallComparison) (sel : B256)
    (run : Line.Run sevm (St b (sel :: S) M G) q.line d) :
    ∃ G', d = St b (Bytes.toB256 q.target :: q.compute sel :: sel :: S) M G' := by
  dsimp only [PairNoCallComparison.line] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  by_cases gt : q.isGt = true
  · simp only [PairNoCallComparison.op, gt, ite_true] at step
    obtain ⟨_, rfl⟩ := ri_gt step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨gas, state⟩ := ri_push step
    cases run
    exact ⟨gas, by simpa only [PairNoCallComparison.compute, gt, ite_true] using state⟩
  · rw [PairNoCallComparison.op, ite_eq_right gt] at step
    obtain ⟨_, rfl⟩ := ri_eq step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨gas, state⟩ := ri_push step
    cases run
    exact ⟨gas, by simpa only [PairNoCallComparison.compute, ite_eq_right gt] using state⟩

/-- The literal comparison is traversed on the original checked cursor. -/
theorem PairNoCallComparison.cut {root : Exec.Deriv} {b post : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} (q : PairNoCallComparison) (sel : B256)
    (cut : CursorStateAt code cert root q.body b (sel :: S) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code cert root q.tail b
      (Bytes.toB256 q.target :: q.compute sel :: sel :: S) M K) := by
  apply cut.line cert_check success fork q.line rfl
  · intro n member x equal
    subst n
    simp only [PairNoCallComparison.line, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member
  · exact q.line_inv sel

/-- The four immediate writers and all seventeen actual view selectors. -/
inductive PairNoCallEntry
  | transfer | approve | transferFrom | initialize | decimals | minimumLiquidity | permitTypehash | domainSeparator | price0CumulativeLast | price1CumulativeLast | kLast | factory | token0 | token1 | name | symbol | totalSupply | balanceOf | nonces | allowance | getReserves

def PairNoCallEntry.selector : PairNoCallEntry → B256
  | .transfer => 0xa9059cbb
  | .approve => 0x95ea7b3
  | .transferFrom => 0x23b872dd
  | .initialize => 0x485cc955
  | .decimals => StaticView.selector (.scalar (.constant .decimals))
  | .minimumLiquidity => StaticView.selector (.scalar (.constant .minimumLiquidity))
  | .permitTypehash => StaticView.selector (.scalar (.constant .permitTypehash))
  | .domainSeparator => StaticView.selector (.scalar (.stored .domainSeparator))
  | .price0CumulativeLast => StaticView.selector (.scalar (.stored .price0CumulativeLast))
  | .price1CumulativeLast => StaticView.selector (.scalar (.stored .price1CumulativeLast))
  | .kLast => StaticView.selector (.scalar (.stored .kLast))
  | .factory => StaticView.selector (.scalar (.address .factory))
  | .token0 => StaticView.selector (.scalar (.address .token0))
  | .token1 => StaticView.selector (.scalar (.address .token1))
  | .name => StaticView.selector (.string .name)
  | .symbol => StaticView.selector (.string .symbol)
  | .totalSupply => StaticView.selector (.totalSupply)
  | .balanceOf => StaticView.selector (.singleMapping .balanceOf)
  | .nonces => StaticView.selector (.singleMapping .nonces)
  | .allowance => StaticView.selector (.allowance)
  | .getReserves => StaticView.selector (.getReserves)

def PairNoCallEntry.tree : PairNoCallEntry → SFunc
  | .transfer => t_055e_c85
  | .approve => t_0315_c96
  | .transferFrom => t_03ad_c93
  | .initialize => t_041e_c90
  | .decimals => t_03f8_c95
  | .minimumLiquidity => t_0597_c79
  | .permitTypehash => t_03f0_c94
  | .domainSeparator => t_0416_c89
  | .price0CumulativeLast => t_0459_c91
  | .price1CumulativeLast => t_0461_c92
  | .kLast => t_04cf_c88
  | .factory => t_05d2_c81
  | .token0 => t_0362_c97
  | .token1 => t_05da_c75
  | .name => t_0259_c100
  | .symbol => t_0556_c84
  | .totalSupply => t_0393_c98
  | .balanceOf => t_049c_c87
  | .nonces => t_04d7_c82
  | .allowance => t_0640_c77
  | .getReserves => t_02d6_c101

def PairNoCallEntry.region : PairNoCallEntry → List Nat
  | .transfer => [9, 40, 59, 61, 72]
  | .approve => [51, 64]
  | .transferFrom => [9, 10, 48, 59, 61, 72]
  | .initialize => [45]
  | .decimals => [50]
  | .minimumLiquidity => [33]
  | .permitTypehash => [49]
  | .domainSeparator => [44]
  | .price0CumulativeLast => [46]
  | .price1CumulativeLast => [47]
  | .kLast => [43]
  | .factory => [35]
  | .token0 => [52]
  | .token1 => [28]
  | .name => [1, 39, 55]
  | .symbol => [1, 38, 39]
  | .totalSupply => [53]
  | .balanceOf => [42]
  | .nonces => [36]
  | .allowance => [30]
  | .getReserves => [56]

theorem PairNoCallEntry.region_closed (entry : PairNoCallEntry) :
    ExecFreeSet cert.prog entry.region = true := by
  cases entry <;> decide

theorem PairNoCallEntry.tree_free (entry : PairNoCallEntry) :
    entry.tree.execFreeIn entry.region = true := by
  cases entry <;> decide

/-- The selected function is reached by an actual call-free prefix; all world,
memory and continuation fields come from the same successful original root. -/
theorem PairNoCallEntry.cursor_state {sevm : Sevm} {b post : Devm} {G : Nat}
    (entry : PairNoCallEntry) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = entry.selector)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      entry.tree b [entry.selector] getterInitMemory []) := by
  cases entry with
  | transfer =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_002b_c0 b [0xa9059cbb] getterInitMemory [] at cut
    obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0xa9059cbb cut rfl fork
    change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
      (0x97 :: 1 :: [0xa9059cbb]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0097.cut 0xa9059cbb cut rfl fork
    change CursorStateAt code cert _ (.branch t_00a3_c0 t_00d3_c0) b
      (0xd3 :: 0 :: [0xa9059cbb]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00a3.cut 0xa9059cbb cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00ae_c0 82) b
      (0x4d7 :: 0 :: [0xa9059cbb]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00ae.cut 0xa9059cbb cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00b9_c0 83) b
      (0x50a :: 0 :: [0xa9059cbb]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00b9.cut 0xa9059cbb cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00c4_c0 84) b
      (0x556 :: 0 :: [0xa9059cbb]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00c4.cut 0xa9059cbb cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00cf_c0 85) b
      (0x55e :: 1 :: [0xa9059cbb]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | approve =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x95ea7b3] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x95ea7b3 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 1 :: [0x95ea7b3]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0166.cut 0x95ea7b3 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0172_c0 t_0197_c0) b
      (0x197 :: 0 :: [0x95ea7b3]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0172.cut 0x95ea7b3 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_017d_c0 96) b
      (0x315 :: 1 :: [0x95ea7b3]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | transferFrom =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x23b872dd] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x23b872dd cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 0 :: [0x23b872dd]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0105.cut 0x23b872dd cut rfl fork
    change CursorStateAt code cert _ (.branch t_0110_c0 t_0140_c0) b
      (0x140 :: 1 :: [0x23b872dd]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0140.cut 0x23b872dd cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_014c_c0 93) b
      (0x3ad :: 1 :: [0x23b872dd]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | «initialize» =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x485cc955] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x485cc955 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 0 :: [0x485cc955]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0105.cut 0x485cc955 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0110_c0 t_0140_c0) b
      (0x140 :: 0 :: [0x485cc955]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0110.cut 0x485cc955 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_011b_c0 89) b
      (0x416 :: 0 :: [0x485cc955]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at011b.cut 0x485cc955 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0126_c0 90) b
      (0x41e :: 1 :: [0x485cc955]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | decimals =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x313ce567] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x313ce567 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 0 :: [0x313ce567]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0105.cut 0x313ce567 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0110_c0 t_0140_c0) b
      (0x140 :: 1 :: [0x313ce567]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0140.cut 0x313ce567 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_014c_c0 93) b
      (0x3ad :: 0 :: [0x313ce567]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at014c.cut 0x313ce567 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0157_c0 94) b
      (0x3f0 :: 0 :: [0x313ce567]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0157.cut 0x313ce567 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0162_c0 95) b
      (0x3f8 :: 1 :: [0x313ce567]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | minimumLiquidity =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_002b_c0 b [0xba9a7a56] getterInitMemory [] at cut
    obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0xba9a7a56 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
      (0x97 :: 0 :: [0xba9a7a56]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0036.cut 0xba9a7a56 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0041_c0 t_0071_c0) b
      (0x71 :: 1 :: [0xba9a7a56]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0071.cut 0xba9a7a56 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_007d_c0 79) b
      (0x597 :: 1 :: [0xba9a7a56]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | permitTypehash =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x30adf81f] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x30adf81f cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 0 :: [0x30adf81f]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0105.cut 0x30adf81f cut rfl fork
    change CursorStateAt code cert _ (.branch t_0110_c0 t_0140_c0) b
      (0x140 :: 1 :: [0x30adf81f]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0140.cut 0x30adf81f cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_014c_c0 93) b
      (0x3ad :: 0 :: [0x30adf81f]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at014c.cut 0x30adf81f cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0157_c0 94) b
      (0x3f0 :: 1 :: [0x30adf81f]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | domainSeparator =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x3644e515] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x3644e515 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 0 :: [0x3644e515]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0105.cut 0x3644e515 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0110_c0 t_0140_c0) b
      (0x140 :: 0 :: [0x3644e515]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0110.cut 0x3644e515 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_011b_c0 89) b
      (0x416 :: 1 :: [0x3644e515]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | price0CumulativeLast =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x5909c0d5] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x5909c0d5 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 0 :: [0x5909c0d5]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0105.cut 0x5909c0d5 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0110_c0 t_0140_c0) b
      (0x140 :: 0 :: [0x5909c0d5]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0110.cut 0x5909c0d5 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_011b_c0 89) b
      (0x416 :: 0 :: [0x5909c0d5]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at011b.cut 0x5909c0d5 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0126_c0 90) b
      (0x41e :: 0 :: [0x5909c0d5]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0126.cut 0x5909c0d5 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0131_c0 91) b
      (0x459 :: 1 :: [0x5909c0d5]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | price1CumulativeLast =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x5a3d5493] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x5a3d5493 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 0 :: [0x5a3d5493]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0105.cut 0x5a3d5493 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0110_c0 t_0140_c0) b
      (0x140 :: 0 :: [0x5a3d5493]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0110.cut 0x5a3d5493 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_011b_c0 89) b
      (0x416 :: 0 :: [0x5a3d5493]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at011b.cut 0x5a3d5493 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0126_c0 90) b
      (0x41e :: 0 :: [0x5a3d5493]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0126.cut 0x5a3d5493 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0131_c0 91) b
      (0x459 :: 0 :: [0x5a3d5493]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0131.cut 0x5a3d5493 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_013c_c0 92) b
      (0x461 :: 1 :: [0x5a3d5493]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | kLast =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_002b_c0 b [0x7464fc3d] getterInitMemory [] at cut
    obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0x7464fc3d cut rfl fork
    change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
      (0x97 :: 1 :: [0x7464fc3d]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0097.cut 0x7464fc3d cut rfl fork
    change CursorStateAt code cert _ (.branch t_00a3_c0 t_00d3_c0) b
      (0xd3 :: 1 :: [0x7464fc3d]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00d3.cut 0x7464fc3d cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00df_c0 86) b
      (0x469 :: 0 :: [0x7464fc3d]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00df.cut 0x7464fc3d cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00ea_c0 87) b
      (0x49c :: 0 :: [0x7464fc3d]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00ea.cut 0x7464fc3d cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00f5_c0 88) b
      (0x4cf :: 1 :: [0x7464fc3d]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | factory =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_002b_c0 b [0xc45a0155] getterInitMemory [] at cut
    obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0xc45a0155 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
      (0x97 :: 0 :: [0xc45a0155]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0036.cut 0xc45a0155 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0041_c0 t_0071_c0) b
      (0x71 :: 1 :: [0xc45a0155]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0071.cut 0xc45a0155 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_007d_c0 79) b
      (0x597 :: 0 :: [0xc45a0155]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at007d.cut 0xc45a0155 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0088_c0 80) b
      (0x59f :: 0 :: [0xc45a0155]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0088.cut 0xc45a0155 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0093_c0 81) b
      (0x5d2 :: 1 :: [0xc45a0155]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | token0 =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0xdfe1681] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0xdfe1681 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 1 :: [0xdfe1681]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0166.cut 0xdfe1681 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0172_c0 t_0197_c0) b
      (0x197 :: 0 :: [0xdfe1681]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0172.cut 0xdfe1681 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_017d_c0 96) b
      (0x315 :: 0 :: [0xdfe1681]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at017d.cut 0xdfe1681 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0188_c0 97) b
      (0x362 :: 1 :: [0xdfe1681]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | token1 =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_002b_c0 b [0xd21220a7] getterInitMemory [] at cut
    obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0xd21220a7 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
      (0x97 :: 0 :: [0xd21220a7]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0036.cut 0xd21220a7 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0041_c0 t_0071_c0) b
      (0x71 :: 0 :: [0xd21220a7]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0041.cut 0xd21220a7 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_004c_c0 75) b
      (0x5da :: 1 :: [0xd21220a7]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | name =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x6fdde03] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x6fdde03 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 1 :: [0x6fdde03]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0166.cut 0x6fdde03 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0172_c0 t_0197_c0) b
      (0x197 :: 1 :: [0x6fdde03]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0197.cut 0x6fdde03 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_01a3_c0 99) b
      (0x1be :: 0 :: [0x6fdde03]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at01a3.cut 0x6fdde03 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_01ae_c0 100) b
      (0x259 :: 1 :: [0x6fdde03]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | symbol =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_002b_c0 b [0x95d89b41] getterInitMemory [] at cut
    obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0x95d89b41 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
      (0x97 :: 1 :: [0x95d89b41]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0097.cut 0x95d89b41 cut rfl fork
    change CursorStateAt code cert _ (.branch t_00a3_c0 t_00d3_c0) b
      (0xd3 :: 0 :: [0x95d89b41]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00a3.cut 0x95d89b41 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00ae_c0 82) b
      (0x4d7 :: 0 :: [0x95d89b41]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00ae.cut 0x95d89b41 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00b9_c0 83) b
      (0x50a :: 0 :: [0x95d89b41]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00b9.cut 0x95d89b41 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00c4_c0 84) b
      (0x556 :: 1 :: [0x95d89b41]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | totalSupply =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x18160ddd] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x18160ddd cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 1 :: [0x18160ddd]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0166.cut 0x18160ddd cut rfl fork
    change CursorStateAt code cert _ (.branch t_0172_c0 t_0197_c0) b
      (0x197 :: 0 :: [0x18160ddd]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0172.cut 0x18160ddd cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_017d_c0 96) b
      (0x315 :: 0 :: [0x18160ddd]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at017d.cut 0x18160ddd cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0188_c0 97) b
      (0x362 :: 0 :: [0x18160ddd]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0188.cut 0x18160ddd cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0193_c0 98) b
      (0x393 :: 1 :: [0x18160ddd]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | balanceOf =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_002b_c0 b [0x70a08231] getterInitMemory [] at cut
    obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0x70a08231 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
      (0x97 :: 1 :: [0x70a08231]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0097.cut 0x70a08231 cut rfl fork
    change CursorStateAt code cert _ (.branch t_00a3_c0 t_00d3_c0) b
      (0xd3 :: 1 :: [0x70a08231]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00d3.cut 0x70a08231 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00df_c0 86) b
      (0x469 :: 0 :: [0x70a08231]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00df.cut 0x70a08231 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00ea_c0 87) b
      (0x49c :: 1 :: [0x70a08231]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | nonces =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_002b_c0 b [0x7ecebe00] getterInitMemory [] at cut
    obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0x7ecebe00 cut rfl fork
    change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
      (0x97 :: 1 :: [0x7ecebe00]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0097.cut 0x7ecebe00 cut rfl fork
    change CursorStateAt code cert _ (.branch t_00a3_c0 t_00d3_c0) b
      (0xd3 :: 0 :: [0x7ecebe00]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00a3.cut 0x7ecebe00 cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_00ae_c0 82) b
      (0x4d7 :: 1 :: [0x7ecebe00]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | allowance =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_002b_c0 b [0xdd62ed3e] getterInitMemory [] at cut
    obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0xdd62ed3e cut rfl fork
    change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
      (0x97 :: 0 :: [0xdd62ed3e]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0036.cut 0xdd62ed3e cut rfl fork
    change CursorStateAt code cert _ (.branch t_0041_c0 t_0071_c0) b
      (0x71 :: 0 :: [0xdd62ed3e]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0041.cut 0xdd62ed3e cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_004c_c0 75) b
      (0x5da :: 0 :: [0xdd62ed3e]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at004c.cut 0xdd62ed3e cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0057_c0 76) b
      (0x5e2 :: 0 :: [0xdd62ed3e]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0057.cut 0xdd62ed3e cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_0062_c0 77) b
      (0x640 :: 1 :: [0xdd62ed3e]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl
  | getReserves =>
    obtain ⟨cut⟩ := pair_dispatch_selector_cursor_state codeEq fork selector run
    change CursorStateAt code cert _ t_00f9_c0 b [0x902f1ac] getterInitMemory [] at cut
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at00f9.cut 0x902f1ac cut rfl fork
    change CursorStateAt code cert _ (.branch t_0105_c0 t_0166_c0) b
      (0x166 :: 1 :: [0x902f1ac]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0166.cut 0x902f1ac cut rfl fork
    change CursorStateAt code cert _ (.branch t_0172_c0 t_0197_c0) b
      (0x197 :: 1 :: [0x902f1ac]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.branchSucc cert_check rfl fork (by decide)
    obtain ⟨cut⟩ := cut.dest cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at0197.cut 0x902f1ac cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_01a3_c0 99) b
      (0x1be :: 0 :: [0x902f1ac]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at01a3.cut 0x902f1ac cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_01ae_c0 100) b
      (0x259 :: 0 :: [0x902f1ac]) getterInitMemory [] at guard
    obtain ⟨cut⟩ := guard.toZero cert_check rfl fork
    obtain ⟨guard⟩ := PairNoCallComparison.at01ae.cut 0x902f1ac cut rfl fork
    change CursorStateAt code cert _ (.branchTo t_01b9_c0 101) b
      (0x2d6 :: 1 :: [0x902f1ac]) getterInitMemory [] at guard
    exact guard.toSucc cert_check rfl fork (by decide) rfl

/-- The checked selected suffix and original prefix exclude every same-frame
external instruction of this successful original bytecode execution. -/
theorem PairNoCallEntry.root_noExec {sevm : Sevm} {b post : Devm} {G : Nat}
    (entry : PairNoCallEntry) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = entry.selector)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  obtain ⟨cut⟩ := entry.cursor_state codeEq fork selector run
  have suffix := cut.placed.noExecSuffix cert_check (cut.sevm_eq ▸ fork)
    entry.region_closed (by rw [cut.tree]; exact entry.tree_free)
    (by rw [cut.continuations]; simp only [List.not_mem_nil, false_implies, implies_true])
  intro N reached x decoded
  rcases cut.free.2 N reached with after | clean
  · exact suffix N after x decoded
  · exact clean x decoded

end Blanc.Lift.UniswapV2Pair
