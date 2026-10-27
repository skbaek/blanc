import Blanc.Lift.Usdc.OldTransferFromEntry
import Blanc.Lift.Usdc.V2TransferFromCallee

/-! Original V2 transferFrom dispatch and guards retain the actual caller stack. -/
namespace Blanc.Lift.Usdc.V2TransferFromEntry

open Jaune Blanc Blanc.Lift
variable {observe : Conf → Conf → Prop}

/-- The public checks leave these words below the internal transfer call. -/
def guardedStack (sevm : Sevm) (owner recipient : Adr) (amount : B256)
    (S : List B256) : List B256 :=
  recipient.toB256 :: owner.toB256 :: sevm.caller.toB256 :: 0 ::
    amount :: recipient.toB256 :: owner.toB256 :: S

/-- Any later store passes the actual public checks and enters the balance callee. -/
theorem public_to_body {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {owner recipient : Adr} {b : Devm} {amount : B256}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b (amount :: recipient.toB256 :: owner.toB256 :: S) M G,
        ImplV2.t_11f1_c59, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ b' M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (amount :: recipient.toB256 :: owner.toB256 :: 0x147d ::
        guardedStack sevm owner recipient amount S) M' G',
        ImplV2.t_3ef8_c74, ImplV2.t_147d_c59 :: K⟩ T := by
  exact OldTransferFromEntry.public_to_body (version := .v2) (by decide) erase run hT cont

/-- The checked dispatcher routes transferFrom through its original ABI wrapper. -/
theorem route_transferFrom : SFunc.selWalk 0x23b872dd
    (.next (.reg (.dup 0)) (.next (.push [0x8a, 0x6d, 0xb9, 0xc3] (by decide))
      (.next (.reg .gt) (.next (.push [0x01, 0xbd] (by decide))
        (.branch ImplV2.t_002b_c0 ImplV2.t_01bd_c0))))) =
    .inl (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd], 147) := by
  exact OldTransferFromEntry.route_v2

/-- Follow the selected prefix to its store; the final frame outcome is unrestricted. -/
theorem entry_to_body {Q : Sevm → Devm → Ninst → Devm → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b S M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∃ S' b' M' G', ObservedReach Q observe ImplV2.cert.prog sevm
      ⟨St b' (Sevm.dataWord sevm 68 :: (Sevm.dataWord sevm 36).toAdr.toB256 ::
        (Sevm.dataWord sevm 4).toAdr.toB256 :: 0x147d ::
        guardedStack sevm (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
          (Sevm.dataWord sevm 68) S') M' G', ImplV2.t_3ef8_c74,
        [ImplV2.t_147d_c59, ImplV2.t_0407_c147]⟩ T := by
  exact OldTransferFromEntry.entry_to_body (version := .v2) (by decide) erase selected run hT

end Blanc.Lift.Usdc.V2TransferFromEntry
