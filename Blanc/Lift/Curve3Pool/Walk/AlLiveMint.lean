import Blanc.Lift.Curve3Pool.Walk.AlLiveD2Get
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityMint

/-!
# `add_liquidity`, forward: the mint amount, `mint`, the event and `STOP`

`rx_al_mint0` (first deposit, `t_170b_c1273`, memory `0xa40`: `mint_amount = D1`) and
`rx_al_mint1` (`t_170b_c1339`, memory `0xba0`: `mint_amount = token_supply * (D2 - D0) / D0`,
checked) leave the amount at `0xba0` and reach the tail (`t_177d_c8` / `t_177d_c1339`, one shape
`alTail`); `rx_al_tail` runs the slippage test, `token.mint(msg.sender, mint_amount)` (answered by
`MintOkAt`, window `0xc7c`/`0xd00`), the `AddLiquidity` event (the new supply checked) and the
lock's release.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

def alTail (a1 : SFunc) (a2 : SFunc) (a3 : SFunc) (a4 : SFunc) : SFunc :=
  (.dest (.next (.push [0x08, 0xc3, 0x79, 0xa0] (by decide)) (.next (.push [0x0b, 0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.push [0x0b, 0xe0] (by decide)) (.next (.reg .mstore) (.next (.push [0x14] (by decide)) (.next (.push [0x0c, 0x00] (by decide)) (.next (.reg .mstore) (.next (.push [0x53, 0x6c, 0x69, 0x70, 0x70, 0x61, 0x67, 0x65, 0x20, 0x73, 0x63, 0x72, 0x65, 0x77, 0x65, 0x64, 0x20, 0x79, 0x6f, 0x75, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.push [0x0c, 0x20] (by decide)) (.next (.reg .mstore) (.next (.push [0x0c, 0x00] (by decide)) (.next (.reg .pop) (.next (.push [0x64] (by decide)) (.next (.reg .calldataload) (.next (.push [0x0b, 0xa0] (by decide)) (.next (.reg .mload) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [0x17, 0xcf] (by decide)) (.branch a1 (.dest (.next (.push [0x20] (by decide)) (.next (.push [0x0d, 0x00] (by decide)) (.next (.push [0x44] (by decide)) (.next (.push [0x40, 0xc1, 0x0f, 0x19] (by decide)) (.next (.push [0x0c, 0x60] (by decide)) (.next (.reg .mstore) (.next (.reg .caller) (.next (.push [0x0c, 0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x0b, 0xa0] (by decide)) (.next (.reg .mload) (.next (.push [0x0c, 0xa0] (by decide)) (.next (.reg .mstore) (.next (.push [0x0c, 0x7c] (by decide)) (.next (.push [0x00] (by decide)) (.next (.push [0x05] (by decide)) (.next (.reg .sload) (.next (.reg .gas) (.next (.exec .call) (.next (.push [0x17, 0xff] (by decide)) (.branch a2 (.dest (.next (.push [0x1f] (by decide)) (.next (.reg .returndatasize) (.next (.reg .gt) (.next (.push [0x18, 0x0c] (by decide)) (.branch a3 (.dest (.next (.push [0x00] (by decide)) (.next (.reg .pop) (.next (.push [0x0d, 0x00] (by decide)) (.next (.reg .pop) (.next (.push [0x04] (by decide)) (.next (.reg .calldataload) (.next (.push [0x0d, 0x20] (by decide)) (.next (.reg .mstore) (.next (.push [0x24] (by decide)) (.next (.reg .calldataload) (.next (.push [0x0d, 0x40] (by decide)) (.next (.reg .mstore) (.next (.push [0x44] (by decide)) (.next (.reg .calldataload) (.next (.push [0x0d, 0x60] (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x0d, 0x80] (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0x60] (by decide)) (.next (.reg .mload) (.next (.push [0x0d, 0xa0] (by decide)) (.next (.reg .mstore) (.next (.push [0x01, 0x80] (by decide)) (.next (.reg .mload) (.next (.push [0x0d, 0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x09, 0x00] (by decide)) (.next (.reg .mload) (.next (.push [0x0d, 0xe0] (by decide)) (.next (.reg .mstore) (.next (.push [0x02, 0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x0b, 0xa0] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 1)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3)) (.next (.reg .add) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [0x18, 0x5f] (by decide)) (.branch a4 (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x0e, 0x00] (by decide)) (.next (.reg .mstore) (.next (.reg .caller) (.next (.push [0x42, 0x3f, 0x64, 0x95, 0xa0, 0x8f, 0xc6, 0x52, 0x42, 0x5c, 0xf4, 0xed, 0x0d, 0x1f, 0x9e, 0x37, 0xe5, 0x71, 0xd9, 0xb9, 0x52, 0x9b, 0x1c, 0x1c, 0x23, 0xcc, 0xe7, 0x80, 0xb2, 0xe7, 0xdf, 0x0d] (by decide)) (.next (.push [0x01, 0x00] (by decide)) (.next (.push [0x0d, 0x20] (by decide)) (.next (.reg (.log 2)) (.next (.push [0x00] (by decide)) (.next (.push [0xff, 0xff, 0xff] (by decide)) (.next (.reg .sstore) (.last .stop)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem t_177d_c8_eq : t_177d_c8 = alTail t_17c9_c8 t_17fb_c8 t_1808_c8 t_185b_c8 := rfl
theorem t_177d_c1339_eq :
    t_177d_c1339 = alTail t_17c9_c1339 t_17fb_c1339 t_1808_c1339 t_185b_c1339 := rfl

theorem al_prog_8 : cert.prog[8]? = some t_177d_c8 := rfl

/-- **The first deposit's mint amount, forward**: `mint_amount = D1`. -/
theorem rx_al_mint0 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes}
    {G R : Nat} {Q : Outcome → Prop} {D1 : B256}
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xa40)
    (hT : WordAt img 0x240 0) (hD1 : WordAt img 0x900 D1)
    (hG : R + 200 ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0xbc0 → (∀ o w, WordAt img o w → o + 32 ≤ 0xba0 → WordAt img' o w) →
      WordAt img' 0xba0 D1 → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_177d_c8 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_170b_c1273 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 98 := ⟨G - 98, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xba0) (c := 43) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xa40 0xba0 32 = 0xbc0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x240) (v := 0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hT) (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_zero' (by decide) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x900) (v := D1) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xba0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xbc0 0xba0 32 = 0xbc0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_jump al_prog_8 ·)
  exact k M _ g1 hR hW hsz (fun o w hw ho => by wauto) (by wauto) (by omega) (by omega)

/-- `add_liquidity`'s mint amount on a positive supply. -/
abbrev alMintW (T D0 D2 : B256) : B256 := T * (D2 - D0) / D0

/-- **The mint amount on a positive supply, forward**:
`mint_amount = token_supply * (D2 - D0) / D0`, checked. -/
theorem rx_al_mint1 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes}
    {G R : Nat} {Q : Outcome → Prop} {T D0 D2 : B256}
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xba0)
    (hT : WordAt img 0x240 T) (hD0 : WordAt img 0x2e0 D0) (hD2 : WordAt img 0xa20 D2)
    (hT0 : T ≠ 0) (hge : ¬ D2 < D0) (hmul : B256.Nofm T (D2 - D0)) (hD00 : D0 ≠ 0)
    (hG : R + 300 ≤ G) (hroom : S.length + 20 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0xbc0 → (∀ o w, WordAt img o w → o + 32 ≤ 0xba0 → WordAt img' o w) →
      WordAt img' 0xba0 (alMintW T D0 D2) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_177d_c1339 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_170b_c1339 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 222 := ⟨G - 222, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xba0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xba0 0xba0 32 = 0xbc0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x240) (v := T) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hT) (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (show B256.eqCheck (B256.eqCheck T 0) 0 ≠ 0 by
    unfold B256.eqCheck; simp only [hT0, ↓reduceIte]; decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x240) (v := T) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hT) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xa20) (v := D2) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD2) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0) (v := D0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hge) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_or rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (B256.mulGuard_of_nofm hmul) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0) (v := D0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD0) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ hD00 ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_div rfl (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xba0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xbc0 0xba0 32 = 0xbc0 by decide] at hsz
  exact k M _ g1 hR hW hsz (fun o w hw ho => by wauto) (by wauto) (by omega) (by omega)

/-- **The tail, forward** (`alTail`, memory `0xbc0`): the slippage test, `mint`, the event (the
new supply checked), the lock released, `STOP`. -/
theorem rx_al_tail {sevm : Sevm} {b : Devm} {σ : Stor} {W W' : Devm → Prop} {S : List B256}
    {M : Mem} {img : Bytes} {G U : Nat} {Q : Outcome → Prop} {T mint : B256}
    {a1 a2 a3 a4 : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hL : ExLive sevm W b σ) (hW'c : WClosed sevm W')
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0xbc0)
    (hT : WordAt img 0x240 T) (hm : WordAt img 0xba0 mint)
    (hslip : ¬ mint < Sevm.dataWord sevm (Bytes.toB256 [0x64])) (hadd : ¬ T + mint < T)
    (hmint : MintOkAt sevm W W' (σ.get tokenSlot) mint U 0xc7c 0xd00)
    (hG : U + 60000 ≤ G) (hGb : G < 2 ^ 256) (hroom : S.length + 20 < 1024)
    (k : ∀ D : Devm, ExLive sevm W' D (σ.set (Bytes.toB256 [0xff, 0xff, 0xff]) (Bytes.toB256 [0])) →
      Q (.halted D)) :
    SFunc.RunEx cert.prog sevm (St b S M G) (alTail a1 a2 a3 a4) Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 200 := ⟨G - 200, by omega⟩
  unfold alTail
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xbc0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xbc0 0xbc0 32 = 0xbe0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xbe0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xbe0 0xbe0 32 = 0xc00 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc00) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc00 0xc00 32 = 0xc20 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc20) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc20 0xc20 32 = 0xc40 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xba0) (v := mint) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm) (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hslip) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc60) (c := 10) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc40 0xc60 32 = 0xc80 by decide] at hsz
  xr (rx_caller (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xc80) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xc80 0xc80 32 = 0xca0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xba0) (v := mint) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xca0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xca0 0xca0 32 = 0xcc0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sloadV hfork (by hrs) (by omega) ?_; intro g2 b2 v2 hb2 hv2 hg21 hg22; replace hv2 := hL.val hv2; replace hL := hL.sloadE hb2
  rw [show Bytes.toB256 [5] = tokenSlot by decide] at hv2; subst hv2
  obtain ⟨g3, rfl⟩ : ∃ g, g2 = g + 2 := ⟨g2 - 2, by omega⟩
  xr (rx_gas (by hrs) ·)
  rw [show Bytes.toB256 [0] = (0 : B256) by decide,
    show Bytes.toB256 [0x0c, 0x7c] = (0xc7c : B256) by decide,
    show Bytes.toB256 [0x44] = (0x44 : B256) by decide,
    show Bytes.toB256 [0x0d, 0x00] = (0xd00 : B256) by decide,
    show Bytes.toB256 [0x20] = (0x20 : B256) by decide]
  have hin : (M.read (0xc7c : B256).toNat (0x44 : B256).toNat).1 =
      mintSel ++ sevm.caller.toB256.toBytes ++ mint.toBytes := by
    rw [hR.read, show (0xc7c : B256).toNat = 0xc7c by decide,
      show (0x44 : B256).toNat = 0x44 by decide]
    exact al_mint_input _ _ _
  obtain ⟨d, hrun, hpost, hok, hrdlt, hgas, hgle, hstor, hWd, hidd⟩ :=
    hmint b2 S M g3 hL.w (by omega) (by omega) hin (by hrs)
  xr (.next hrun ·)
  obtain ⟨hmem, -⟩ := hpost.settled (by decide)
  rw [show (0xc7c : B256).toNat = 0xc7c by decide, show (0x44 : B256).toNat = 0x44 by decide,
    show (0xd00 : B256).toNat = 0xd00 by decide, show (0x20 : B256).toNat = 0x20 by decide] at hmem
  have hd : d = St d (1 :: S) d.memory d.gasLeft := St.self hpost.stack rfl
  rw [hd]
  have hext : (M.extends [(0xc7c, 0x44), (0xd00, 0x20)]).size = 0xd20 := by
    show memExtsSize M.size _ = _
    rw [hsz]; decide
  have hsz5 : d.memory.size = 0xd20 := by
    rw [hmem, Mem.size_write_of_le (by rw [hext, List.length_take]; omega), hext]
  have hR5 := (hR.extends [(0xc7c, 0x44), (0xd00, 0x20)]).write (hW.extends _) 0xd00
    (d.returnData.take 0x20)
  rw [← hmem] at hR5
  have hW5 : Mem.Wf d.memory := by rw [hmem]; exact (hW.extends _).write _ _
  have hLd : ExLive sevm W' d σ :=
    ⟨fun x => by rw [hstor]; exact hL.stor x, hidd hL.id, hW'c, hWd⟩
  clear hR hW hsz hext hmem hrun hpost hin
  have hR := hR5; have hW := hW5; have hsz := hsz5
  clear hR5 hW5 hsz5
  obtain ⟨g10, hg10⟩ : ∃ g, d.gasLeft = g + 30000 := ⟨d.gasLeft - 30000, by omega⟩
  rw [hg10]
  have hgt : B256.gtCheck (Nat.toB256 d.returnData.length) (Bytes.toB256 [0x1f]) ≠ 0 := by
    apply gtCheck_ne_zero_of_lt
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hrdlt,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide]
    omega
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by decide) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_returndatasize (by hrs) ·)
  xr (rx_gt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by xbr) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xd20) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xd20 0xd20 32 = 0xd40 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xd40) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xd40 0xd40 32 = 0xd60 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xd60) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xd60 0xd60 32 = 0xd80 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x140) hR hsz rfl (by decide) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xd80) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xd80 0xd80 32 = 0xda0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x160) hR hsz rfl (by decide) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xda0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xda0 0xda0 32 = 0xdc0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x180) hR hsz rfl (by decide) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xdc0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xdc0 0xdc0 32 = 0xde0 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x900) hR hsz rfl (by decide) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xde0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xde0 0xde0 32 = 0xe00 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x240) (v := T) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hT) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0xba0) (v := mint) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hm) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hadd) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0xe00) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0xe00 0xe00 32 = 0xe20 by decide] at hsz
  xr (rx_caller (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_log2 (c := 3173) hstatic (by rw [St.extCost_eq hsz]; decide) rfl (read_covered_len hsz (by decide) (by decide)) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_sstoreV hfork hstatic (by omega) ?_; intro g2 b2 hb2 hg21 hg22
  have hL2 := (hLd.addLogE _).sstoreE hb2
  exact ⟨_, .last rfl, k _ (hL2.st _ _ _)⟩

end Blanc.Lift.Curve3Pool
