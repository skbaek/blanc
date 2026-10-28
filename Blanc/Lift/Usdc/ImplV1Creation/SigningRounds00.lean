import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb00 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x28 0x6b 0xee 0x84 0x12 0x0 0x30 0xf9)) 1 (by decide) (UInt64.ofBytes 0xb9 0x80 0x80 0xb7 0x91 0x66 0x83 0x0)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x40 0x60 0x80 0x60 0xee 0x2f)) 3 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x14 0x60 0x1 0x60 0x0)) 4 (by decide) (UInt64.ofBytes 0x19 0x2 0xff 0x60 0x81 0x54 0x81 0xa)) 5 (by decide) (UInt64.ofBytes 0x90 0x17 0x2 0x15 0x15 0x83 0x90 0x16)) 6 (by decide) (UInt64.ofBytes 0x61 0x55 0xb 0x60 0x0 0x60 0x50 0x55)) 7 (by decide) (UInt64.ofBytes 0x1 0x64 0x41 0x0 0x61 0x33 0x3c 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x1 0x64 0x2 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0x4 0x90 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x80 0x5b 0x56 0x84 0x0)) 11 (by decide) (UInt64.ofBytes 0x73 0x81 0x54 0x81 0xa 0x0 0x1 0x61)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x90 0x16 0x19 0x2 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x83)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed00 : Vector UInt64 25 :=
  #v[0x286bee84120030f9, 0xb98080b791668300, 0x605240608060ee2f, 0x1611460016000, 0x1902ff608154810a, 0x9017021515839016, 0x61550b6000605055, 0x164410061333c00, 0x1640200000000, 0x615b560490000000, 0x800060805b568400, 0x738154810a000161, 0xffffffffffffffff, 0xffffffffffffffff, 0x90161902ffffffff, 0xffffffffffff7383, 0xffffffffffffffff, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

private theorem words00 : absorb00 state00 = absorbed00 := by
  decide +kernel

private def quarter00_1 : Vector UInt64 25 :=
  #v[0x2e6aa759a0b6db0a, 0x33d5954805d8c19, 0xc97397b50fc56d93, 0x82b38579970628da, 0xcf59a863696ad1af, 0x43dfe476c3f9c15b, 0xf2090a9111b27f43, 0x6f7cadbd1f4368ed, 0xb06de008aa95a63, 0xf2be06d08aa37289, 0xc8581197f61a33d6, 0xe1944ccd665beb56, 0x808e251c8a895827, 0x90284c7a5fe21dd2, 0xc3ef22f774f618f, 0x803ce17b9c556b9, 0x3bfccff1f32a9009, 0xbb60bf66f89374ca, 0xb41591b24b0439bf, 0x5e443a04b1739d5d, 0x499d8ac883dd8ab8, 0xebf7768a7a15a3bf, 0xb199f6c168413dfe, 0x909d8889df0b39a6, 0x8b854ad05f0f0caf]

private theorem rounds00_0 : sixRounds 0 (by decide) absorbed00 = quarter00_1 := by
  decide +kernel

private def quarter00_2 : Vector UInt64 25 :=
  #v[0x1aa056e43607c479, 0xa602dde7a02e56d, 0x6a2d8f5e163cfdd3, 0xd38c90eb242c6b30, 0xe78b30b0dfeb89e6, 0x9d739966d0e7f9fb, 0x779b65a3bee5575a, 0x25c7ea7033dd5bb4, 0xb3e248850a1a8ab3, 0x16d66ffc69cb1464, 0xc5fbb1194a9d56cf, 0xa628eb38b5bf02c2, 0x757ba2cc77a20d6d, 0x55c13a97ad580f32, 0x1d8c4d24462197b0, 0x3106084340aebe9f, 0xc8c8c0fa14ddabaf, 0xb5dd9d77b6d39e7d, 0xa0be68c891842164, 0xe096e6b56eb372ed, 0x45f54c9ed5fd8ab8, 0xe04df1b6777da614, 0x614291e5b0c0d4a0, 0x5a8d964ad3f9732a, 0x2283fe60ef524f82]

private theorem rounds00_1 : sixRounds 6 (by decide) quarter00_1 = quarter00_2 := by
  decide +kernel

private def quarter00_3 : Vector UInt64 25 :=
  #v[0x9883c7f1a5351354, 0xebc80902cfb17248, 0xdcc2045ff73d0530, 0xea1d7211217aa93d, 0x241476ba6d4308dd, 0xc6754c0167ad8179, 0xc920e8b7a2770a21, 0xdc72220a7aa7b4a3, 0xd6670742a92efff1, 0x409860d0ee63acd, 0xd5ba77742aaaf36c, 0xc5511f0307158859, 0xa53207080a170014, 0x4b1bd3df08414eb9, 0x648ec9dd523130c4, 0x3d8f921914ab10c7, 0x2abe7a844b80bd00, 0x1831030216315bd1, 0x487314cdb008a655, 0xdb7ab271119d25b9, 0xd85d52fab61a16e, 0xd23f6c2d1f9fcc81, 0xcae9e79fb51bcd43, 0xd7cf2c0be55f1ccd, 0x4dac417cd8092d19]

private theorem rounds00_2 : sixRounds 12 (by decide) quarter00_2 = quarter00_3 := by
  decide +kernel

private theorem rounds00_3 : sixRounds 18 (by decide) quarter00_3 = state01 := by
  decide +kernel

private theorem perm00 : KECCAK.f1600 absorbed00 = state01 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds00_0, rounds00_1, rounds00_2, rounds00_3]
  rfl

theorem block00 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes00 ++ tail) state00 =
      KECCAK.Bytes.run 0 tail state01 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes00 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb00 ws)) := by
    rfl
  exact (step state00).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words00).trans perm00))

private def absorb01 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x2 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0x50 0x50 0x55 0x90 0x17)) 2 (by decide) (UInt64.ofBytes 0x0 0x60 0x93 0x0 0x61 0x80 0x5b 0x2f)) 3 (by decide) (UInt64.ofBytes 0x60 0x80 0x60 0x0 0xf3 0x0 0x60 0x39)) 4 (by decide) (UInt64.ofBytes 0x1 0x61 0x10 0x36 0x4 0x60 0x52 0x40)) 5 (by decide) (UInt64.ofBytes 0x0 0x1 0x7c 0x35 0x0 0x60 0x57 0x8b)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0x63 0x4 0x90 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0xde 0xfd 0x6 0x63 0x80 0x16 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0x90 0x1 0x61 0x14 0x3)) 12 (by decide) (UInt64.ofBytes 0x20 0x2 0x61 0x14 0xb3 0xa7 0x5e 0x9)) 13 (by decide) (UInt64.ofBytes 0x14 0xdd 0xd 0x16 0x18 0x63 0x80 0x57)) 14 (by decide) (UInt64.ofBytes 0x89 0x1a 0x63 0x80 0x57 0x85 0x2 0x61)) 15 (by decide) (UInt64.ofBytes 0x80 0x57 0xb0 0x2 0x61 0x14 0x66 0x52)) 16 (by decide) (UInt64.ofBytes 0x2 0x61 0x14 0xdd 0x72 0xb8 0x23 0x63))

private def absorbed01 : Vector UInt64 25 :=
  #v[0xb1fc4278990d6d0, 0xc343785e1967eaff, 0xa7aa7b69b1024292, 0xe52158ab1b85bf66, 0xd0c301d8b54af3a, 0x8ecdd42cdaae7d65, 0x9635692e74e3f70a, 0xadeb7aa7b4957a8b, 0x744b9e5443576bd5, 0x373a83af160cb5e8, 0x9d614f54b2e553ab, 0x89bea6ce7f4dc5cb, 0xf0044e505b4de3f6, 0xcdb40d37428fb81f, 0xa3d8b1762ae058e1, 0xb5c3c060a6081199, 0x34963be779efcae3, 0x3183ddffe111069, 0x4c7876988209c21c, 0x94103f25c2e4f671, 0x9f04a5d99fc7a114, 0x1c88580a1faa50f9, 0x10aa76c58a5e8641, 0xea11c50764b7c663, 0x277defc69499beb9]

private theorem words01 : absorb01 state01 = absorbed01 := by
  decide +kernel

private def quarter01_1 : Vector UInt64 25 :=
  #v[0x38adfc3740fdd37d, 0xb6e213c3a97610f3, 0xec029c10db4a7ef7, 0x9ec872f960de016d, 0x6afc51e0ce54c0d, 0xe9941d6912f5ddbc, 0x4afa6d58199f8d52, 0xb6ca4acc8e0d36ca, 0xe91ef8e398ab237e, 0xbddb1f61dd34a532, 0xf09ffcf99aac35d5, 0x60aaf3f502f492a2, 0x5511859e6c847340, 0xb80a71c91ec06416, 0xe02c9d544eeb8fa, 0x6bbf4a5183f6cb00, 0x49968822db4af76b, 0xdfdee0be8eda8c8f, 0x49bd7a0528a8db07, 0x469a13db4536aa9e, 0x76fdc25cefb8c691, 0xe59b1da93ffd59da, 0x242812977c90375, 0x6bfe32f330c7c930, 0x315cd532410a7b47]

private theorem rounds01_0 : sixRounds 0 (by decide) absorbed01 = quarter01_1 := by
  decide +kernel

private def quarter01_2 : Vector UInt64 25 :=
  #v[0xd94c4c6b99fc668c, 0x7c54108f7620eb26, 0x5126b687e93f5315, 0x8538d9c2721c7c73, 0x7a0475e23c4545c, 0xb84836fb26c87f7b, 0xbd660fc5a6922cbb, 0x349fe1ec3ed01efa, 0x70a2b06f781c1043, 0x4ae8d0c2b6cdfad8, 0x92261ec99c498080, 0x36d1c9d7df0dbb57, 0x1242a041927252e0, 0xa2a3916ef8291335, 0x37c163c16aec331e, 0x3130344f9c6cbcc1, 0xcd399bdf8c5debd9, 0x7fe57458fe83a01e, 0xd04970ae58b1627a, 0x77fe1c914aca9d62, 0xb3c46903650c6302, 0x9fb58f8f69f4eb21, 0x704964baec59a636, 0xf9e7d99b3b115145, 0x19bc3ebea2e76398]

private theorem rounds01_1 : sixRounds 6 (by decide) quarter01_1 = quarter01_2 := by
  decide +kernel

private def quarter01_3 : Vector UInt64 25 :=
  #v[0xccf4c5c27aa9c845, 0x2b5797f5ccfb2b64, 0x7d0cfdfb17c0becc, 0x6e43fc4d97efcaf2, 0xd85cd7d98b0e4b18, 0xefb86ca6d43f8c17, 0xc23d9ddd33131d8f, 0x11c91ef7b6ae8f07, 0xd6302a98ad61e1e0, 0x8e4fb410ab296c19, 0xe7cb3c0787a0c95f, 0xe9fc267966c85139, 0xd948131cbf807f4b, 0x1556dc65aaedf749, 0xcc969141ae75b3b3, 0x11808ad217842d4d, 0xa95a30f2f53d1602, 0x778950b4541dfec4, 0xd88b1755ec394d96, 0xfbcd14e2548d9b75, 0x28043e2732fdc405, 0x89a8d8576dfa14bc, 0x9a6d06a7819a5ddc, 0xc1946d8fb656fff4, 0x2cb62532d75e73b1]

private theorem rounds01_2 : sixRounds 12 (by decide) quarter01_2 = quarter01_3 := by
  decide +kernel

private theorem rounds01_3 : sixRounds 18 (by decide) quarter01_3 = state02 := by
  decide +kernel

private theorem perm01 : KECCAK.f1600 absorbed01 = state02 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds01_0, rounds01_1, rounds01_2, rounds01_3]
  rfl

theorem block01 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes01 ++ tail) state01 =
      KECCAK.Bytes.run 0 tail state02 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes01 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb01 ws)) := by
    rfl
  exact (step state01).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words01).trans perm01))

private def absorb02 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xd5 0xaf 0x92 0x30 0x63 0x80 0x57 0xf3)) 1 (by decide) (UInt64.ofBytes 0x31 0x63 0x80 0x57 0x78 0x3 0x61 0x14)) 2 (by decide) (UInt64.ofBytes 0x57 0xd3 0x3 0x61 0x14 0x67 0xe5 0x3c)) 3 (by decide) (UInt64.ofBytes 0x61 0x14 0x2b 0x16 0x57 0x33 0x63 0x80)) 4 (by decide) (UInt64.ofBytes 0x9f 0xd9 0x35 0x63 0x80 0x57 0x4 0x4)) 5 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0x86 0x5 0x61 0x14 0x35)) 6 (by decide) (UInt64.ofBytes 0xdd 0x5 0x61 0x14 0x3a 0xa8 0x4b 0x3f)) 7 (by decide) (UInt64.ofBytes 0x14 0x19 0xf 0xc1 0x40 0x63 0x80 0x57)) 8 (by decide) (UInt64.ofBytes 0x96 0x42 0x63 0x80 0x57 0xf4 0x5 0x61)) 9 (by decide) (UInt64.ofBytes 0x80 0x57 0x59 0x6 0x61 0x14 0x68 0x6c)) 10 (by decide) (UInt64.ofBytes 0x6 0x61 0x14 0x56 0xd9 0x44 0x4e 0x63)) 11 (by decide) (UInt64.ofBytes 0x3c 0xab 0x4b 0x55 0x63 0x80 0x57 0x86)) 12 (by decide) (UInt64.ofBytes 0x5c 0x63 0x80 0x57 0xeb 0x6 0x61 0x14)) 13 (by decide) (UInt64.ofBytes 0x57 0x2e 0x7 0x61 0x14 0xbb 0x5a 0x97)) 14 (by decide) (UInt64.ofBytes 0x61 0x14 0x31 0x82 0xa0 0x70 0x63 0x80)) 15 (by decide) (UInt64.ofBytes 0xcb 0x56 0x84 0x63 0x80 0x57 0x5d 0x7)) 16 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0xb4 0x7 0x61 0x14 0x59))

private def absorbed02 : Vector UInt64 25 :=
  #v[0x30c8cfdd61e48455, 0xe4f6c731768a04d2, 0xf206b8d854a047f8, 0xbc6a2a5c7a832367, 0xb09725308b8857e6, 0x5a4ef3de51939371, 0xc27e915f96dd4ee5, 0xdbaff76ba15e8178, 0x6e412b4817495b33, 0x4178c9edd4c905d8, 0xba37118c0bcfe65b, 0xc5fe5aff6f51aa81, 0x9038bece06278d68, 0x63de94325caee87d, 0xd69ff82d220bd89b, 0x51efb3c3fe807aa8, 0x4ad1607d17cfd2d, 0xdd70d8a02c4e75df, 0x925122567d519787, 0x11cc23579786e0db, 0x9989599e5d346b71, 0x3a9ae151beff036b, 0xe81cb923affdf964, 0xf6f24ed6b6286b07, 0x4bb48f1ec3ea1783]

private theorem words02 : absorb02 state02 = absorbed02 := by
  decide +kernel

private def quarter02_1 : Vector UInt64 25 :=
  #v[0x9c90cb677727a712, 0x5e0163cdfdb57bbd, 0x46c0f41ffbfc9830, 0xdd944b051e1a1144, 0xa71bfd8a78d1d5a8, 0x2805a5933fafc2d1, 0xace4306411370923, 0xf10efad191dfa722, 0x253c9b2a2178088b, 0xb84290752656f5df, 0x76622fdcc08f0be, 0x2d2259035b10e47, 0xc346cd0d524c8a2d, 0x6c7d355bd99ba291, 0x82f8eab34fde90af, 0xbe1245223a840d73, 0x6afdeebe1078f17a, 0xa8cfc35bde8dc39e, 0x2ea77148a6b6aa47, 0x1e02cf85413df598, 0x3bfae61274fea091, 0xa17090c969b6ca1e, 0xd984240c50c607ea, 0x3cf0b7883f368814, 0x492312f946a83482]

private theorem rounds02_0 : sixRounds 0 (by decide) absorbed02 = quarter02_1 := by
  decide +kernel

private def quarter02_2 : Vector UInt64 25 :=
  #v[0x39838369a6391186, 0xa58e3c3424632628, 0x8607877847a1734e, 0x202df902c8e1d3e2, 0x675ba28ceabd33f2, 0xf48deddfa4c0ea87, 0x408806dc4670d9c5, 0x3e55b9dabfe2a3ae, 0x182a27ba19af3b4c, 0x3e957e2426ea2257, 0xd015115ccad1ceb1, 0xa237a4c8ac95ab8c, 0x355db0990b349a82, 0xddcf8f15285e84ca, 0x3c9b8bc7bfdb79b9, 0xb8869550c76f62b, 0x18d85f4329ee23a9, 0x92b1cc834a1c25b2, 0x521ce449b7a48502, 0xf1b46cae774af300, 0xb88cb03936b06ea1, 0xe5d93667e5aaf9e3, 0x9744df270a6caee2, 0x9db253b51f7b1890, 0xc6e09289d740e39f]

private theorem rounds02_1 : sixRounds 6 (by decide) quarter02_1 = quarter02_2 := by
  decide +kernel

private def quarter02_3 : Vector UInt64 25 :=
  #v[0xd0f07e7c04a87ede, 0x2fe2aa7beb689bd3, 0xbae9c160cada2916, 0x2867be5bb3fe468, 0xc6a6e05e4726280d, 0x1d089cf40ec2d1c4, 0xfbd9e005f34aa17a, 0xae3b6b0f6cb147fc, 0x4b499d46286fda17, 0xaa4e762d1491c02b, 0xad79150de62e174a, 0xe6f35e67f2804b24, 0xcaaa0d340528acd4, 0x691a957b47e870ca, 0x99dff5e24997f09, 0x5498d0369b9fd551, 0x18be43ffbcea2cae, 0x37962e4cb56d8d3c, 0x6995e5de15baddb4, 0xc64ee021ba1c0325, 0x549032eebdba5d38, 0x93a5d184dcf45e27, 0x860b6f565d055a1f, 0xf5ff40bf58034c0d, 0x300cdde99fa95bac]

private theorem rounds02_2 : sixRounds 12 (by decide) quarter02_2 = quarter02_3 := by
  decide +kernel

private theorem rounds02_3 : sixRounds 18 (by decide) quarter02_3 = state03 := by
  decide +kernel

private theorem perm02 : KECCAK.f1600 absorbed02 = state03 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds02_0, rounds02_1, rounds02_2, rounds02_3]
  rfl

theorem block02 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes02 ++ tail) state02 =
      KECCAK.Bytes.run 0 tail state03 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes02 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb02 ws)) := by
    rfl
  exact (step state02).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words02).trans perm02))

private def absorb03 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xcb 0x7 0x61 0x14 0xc3 0xb9 0x6d 0x8a)) 1 (by decide) (UInt64.ofBytes 0x14 0x5b 0xcb 0xa5 0x8d 0x63 0x80 0x57)) 2 (by decide) (UInt64.ofBytes 0xd8 0x95 0x63 0x80 0x57 0x22 0x8 0x61)) 3 (by decide) (UInt64.ofBytes 0x80 0x57 0x79 0x8 0x61 0x14 0x41 0x9b)) 4 (by decide) (UInt64.ofBytes 0x9 0x61 0x14 0x6d 0x50 0xd0 0x9f 0x63)) 5 (by decide) (UInt64.ofBytes 0xbb 0x9c 0x5 0xa9 0x63 0x80 0x57 0x9)) 6 (by decide) (UInt64.ofBytes 0xaa 0x63 0x80 0x57 0x60 0x9 0x61 0x14)) 7 (by decide) (UInt64.ofBytes 0x57 0xc5 0x9 0x61 0x14 0xe4 0xe1 0x20)) 8 (by decide) (UInt64.ofBytes 0x61 0x14 0x1a 0x1e 0x27 0xaa 0x63 0x80)) 9 (by decide) (UInt64.ofBytes 0xbf 0x38 0xad 0x63 0x80 0x57 0x8 0xa)) 10 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0x63 0xa 0x61 0x14 0x22)) 11 (by decide) (UInt64.ofBytes 0xa6 0xa 0x61 0x14 0x30 0x24 0x10 0xbd)) 12 (by decide) (UInt64.ofBytes 0x14 0x3e 0xed 0x62 0xdd 0x63 0x80 0x57)) 13 (by decide) (UInt64.ofBytes 0xa6 0xe5 0x63 0x80 0x57 0xfd 0xa 0x61)) 14 (by decide) (UInt64.ofBytes 0x80 0x57 0x74 0xb 0x61 0x14 0xf 0xb1)) 15 (by decide) (UInt64.ofBytes 0xc 0x61 0x14 0x8b 0xe3 0xfd 0xf2 0x63)) 16 (by decide) (UInt64.ofBytes 0xe4 0x2b 0xf9 0xf9 0x63 0x80 0x57 0x4))

private def absorbed03 : Vector UInt64 25 :=
  #v[0x209de264f64282ff, 0xd660ab534eca8f39, 0x43be6b687c8e77b, 0x343a2a3ad20ddb4f, 0x3cb0789785ecf815, 0xb6f91fb4c3e160dd, 0xd3f00e7cab53f6fd, 0xc1b3cb7377fd6aa, 0x9fa76314bf461fce, 0xf0966f9b0758474b, 0xb7567c8131cbf255, 0xc47fd9ecf6b9c27f, 0xd5b3e51ba69a1814, 0x947e28f9431ffcbe, 0x7d8f175f7e3ff0d5, 0xaa9431f1def3f476, 0xcbbc713d952d4c3c, 0xf0cbf5a159731898, 0x2ce6cf9028679f0f, 0x515d427db52e5df7, 0xb2b60fa1ed832c6, 0x129855fa78a87262, 0x2f11f730aecb4561, 0x1251c3a967387ab6, 0xf25b53310ae42559]

private theorem words03 : absorb03 state03 = absorbed03 := by
  decide +kernel

private def quarter03_1 : Vector UInt64 25 :=
  #v[0x146232fe987d4c24, 0xace0ca517f898dc6, 0x86713a8ffe53cf0b, 0x96b06cc76f22d31f, 0xa9990852fe7314d, 0x2fd40df33df5439f, 0xfb4d20230d90862, 0x34d7f390e09263c0, 0x1d631bd3ff4fd7e, 0xba84f6c12120b135, 0xd13d613c9cd60668, 0xabb97b4608b5c72b, 0xc994e8d5497f57eb, 0x47814ec3d82ea7ec, 0x6189970569b26f5a, 0x42c50bfdcc1074d6, 0xcf298ea7d83827c7, 0xf1d417c5076c94f6, 0x187e93cc82b7e801, 0x6596f06678dadc5c, 0xae91e77a1ed52eb, 0x575e8883b2631d9f, 0x8d5f26d8dc702c04, 0xbca2dc6045434f58, 0x7423ea024b6e3ba3]

private theorem rounds03_0 : sixRounds 0 (by decide) absorbed03 = quarter03_1 := by
  decide +kernel

private def quarter03_2 : Vector UInt64 25 :=
  #v[0xa6e85733e4d21b18, 0xc259ea00b409bea1, 0xe5f6c1ff3f6115c6, 0xe98e6f4f3adb2762, 0x55685b83fc0b1b72, 0xf0672e5f0ef8b398, 0x296061ab0e6daaa4, 0xb9c3529f822e0af, 0x6fae205aa0fd79a7, 0xc356be4b1bd3ef0e, 0x556dae9b14e74442, 0x196fed9315d1094e, 0x8ae5ec56f183fd7f, 0x9c6131c55434bce8, 0xba97e7ce2fc57187, 0x38e4cb0a84a6b5d5, 0xb7f4b7200be42540, 0xf56931c0c8d22c82, 0xcc5fec23f9041d35, 0x81d5627d9bd9f75d, 0xa23cba76f0efecce, 0xf4b51f93e7c47d60, 0xa8aa1349e5498121, 0x2df2f2e79b28d6, 0xa6e3ff1c084cedd7]

private theorem rounds03_1 : sixRounds 6 (by decide) quarter03_1 = quarter03_2 := by
  decide +kernel

private def quarter03_3 : Vector UInt64 25 :=
  #v[0xf39bcd711fa41b7c, 0x437cb3ec17943868, 0xac6a9ef186263a3b, 0xe759f00c75d2babe, 0xbb31c8d098224d1, 0xe6a7c323d55b1f, 0x818914e8bf364711, 0xb95cc41f8a8b2c7c, 0x6bc450c938e94591, 0x17c83b472af26ac8, 0x57710797cc0d7ac2, 0xf84c020b38fac0c8, 0x2039553d2e31c852, 0x2b7dc34cd83906b7, 0x922e45b35bde6e77, 0x3ccb937143984d2c, 0xb27abf7f736a85d4, 0x2bd12934c06e5be1, 0x390c438bb96d2246, 0xd1ea8b7a6a8d74b6, 0x930a3d7bf7ee8018, 0xbcc553657ba7b149, 0x5cb58e46faf33104, 0x4092705d9cb63a68, 0x3af595bef8cb67a]

private theorem rounds03_2 : sixRounds 12 (by decide) quarter03_2 = quarter03_3 := by
  decide +kernel

private theorem rounds03_3 : sixRounds 18 (by decide) quarter03_3 = state04 := by
  decide +kernel

private theorem perm03 : KECCAK.f1600 absorbed03 = state04 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds03_0, rounds03_1, rounds03_2, rounds03_3]
  rfl

theorem block03 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes03 ++ tail) state03 =
      KECCAK.Bytes.run 0 tail state04 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes03 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb03 ws)) := by
    rfl
  exact (step state03).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words03).trans perm03))

private def absorb04 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xfe 0x63 0x80 0x57 0x47 0xc 0x61 0x14)) 1 (by decide) (UInt64.ofBytes 0x57 0x8a 0xc 0x61 0x14 0x87 0x5a 0x57)) 2 (by decide) (UInt64.ofBytes 0x80 0x34 0x5b 0xfd 0x80 0x0 0x60 0x5b)) 3 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x9c 0x1 0x61 0x15)) 4 (by decide) (UInt64.ofBytes 0xc 0x61 0xa5 0x1 0x61 0x50 0x5b 0xfd)) 5 (by decide) (UInt64.ofBytes 0x80 0x80 0x51 0x40 0x60 0x5b 0x56 0xe5)) 6 (by decide) (UInt64.ofBytes 0x52 0x82 0x3 0x81 0x82 0x1 0x20 0x60)) 7 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x51 0x81 0x81 0x83)) 8 (by decide) (UInt64.ofBytes 0x20 0x60 0x90 0x51 0x80 0x50 0x91 0x1)) 9 (by decide) (UInt64.ofBytes 0x5b 0x0 0x60 0x83 0x83 0x80 0x90 0x1)) 10 (by decide) (UInt64.ofBytes 0x57 0xe5 0x1 0x61 0x15 0x10 0x81 0x83)) 11 (by decide) (UInt64.ofBytes 0x52 0x1 0x84 0x81 0x51 0x1 0x82 0x80)) 12 (by decide) (UInt64.ofBytes 0x1 0x61 0x50 0x90 0x1 0x81 0x20 0x60)) 13 (by decide) (UInt64.ofBytes 0x90 0x50 0x50 0x50 0x50 0x5b 0x56 0xca)) 14 (by decide) (UInt64.ofBytes 0x16 0x1f 0x60 0x90 0x1 0x81 0x90 0x50)) 15 (by decide) (UInt64.ofBytes 0x82 0x80 0x57 0x12 0x2 0x61 0x15 0x80)) 16 (by decide) (UInt64.ofBytes 0x20 0x60 0x83 0x1 0x60 0x51 0x80 0x3))

private def absorbed04 : Vector UInt64 25 :=
  #v[0x65c0af81798894eb, 0xe8eb8c01d8be1a6f, 0x5113203135d1d188, 0x720f472bee62dd3, 0x3dfd13be99785e1, 0xf5835055ece5e4be, 0xe8840c9dfb1e67a, 0x772c09c9b418511, 0x5da7be3f6db127ae, 0xa0fe3fb74252bd44, 0xc841ba9cc25a0a9d, 0xeea741a2a204b112, 0x36d2250332049bfc, 0x9a474e711273a54c, 0xfcf50be1fd30915b, 0xe0b853b0ead64d31, 0xc8589910f0092ca1, 0x307136469af0df23, 0x3643cbe626b77ce2, 0x3343bae14f36f9c5, 0xf1f7f188b8ec0360, 0xe2480de468bffb5a, 0x7fe79d15305a66f, 0x5f7246ab5584b813, 0xfafb3609e49fb8ea]

private theorem words04 : absorb04 state04 = absorbed04 := by
  decide +kernel

private def quarter04_1 : Vector UInt64 25 :=
  #v[0xdcee2e817028d11c, 0xb5c2caf689c01a93, 0x73cc69ed0a3b53ae, 0xfd1852234646b423, 0xd5a6dc0230cf2a83, 0x375e6b15ff11ed3e, 0x4b0c53ed23118c30, 0xe7d9b23ddf9f2334, 0x6f6008702c1b5deb, 0x7d038ab3880d8e77, 0xdc8bc384abe4203b, 0x883cf9e6ded61aa8, 0x4b01bf1fb1de0f62, 0x177ad2a9c3c947d9, 0x7a6cb685469503dd, 0x8e1caa10bc167304, 0x8e1687f4fda71dec, 0xb271c307861a975d, 0x7bc9ca17bcd5a8a3, 0xd2f6dc0a334dd7d0, 0x95750b171ca5e2b9, 0x47a2d294218e7baf, 0x1937043626f43823, 0x9febfc40b1a63438, 0xe40d42c211b80638]

private theorem rounds04_0 : sixRounds 0 (by decide) absorbed04 = quarter04_1 := by
  decide +kernel

private def quarter04_2 : Vector UInt64 25 :=
  #v[0xde895bb231a8c565, 0x1fa39be703aecf6f, 0x59bce936ce2e5e, 0x9d433392e1f0ae9c, 0x51449b6f7eede7e9, 0x9211dd41978b16e7, 0xfa6bc2d97e90002, 0xd289fa0e62ac230d, 0xc5aa2a27ed6091bd, 0x651e46a8062bee9b, 0xeca2fd884edff95d, 0x3bd730de449812c4, 0x9b647342217a910c, 0x5db731e6b1c0c6ac, 0xe71d87189d2b9573, 0x27584103313419c, 0x2bd7d02ed2336367, 0xd3f96edb554d801, 0x8f87bad8f2941e08, 0xc654ffb0ef2678ee, 0x4c19cc758ca5a3ec, 0x5bf7c4c1f89500b3, 0x9a280fdc16a19afc, 0x43204781730b85ee, 0x754f26c9d2670c15]

private theorem rounds04_1 : sixRounds 6 (by decide) quarter04_1 = quarter04_2 := by
  decide +kernel

private def quarter04_3 : Vector UInt64 25 :=
  #v[0xc4545175afbe0da4, 0x9ceec69d7c8881d9, 0x1ccfecd2a06c18cd, 0x37abbc7a8098f1c0, 0x728fc3addfc1b3c1, 0xad49c3efbb1ce96d, 0x99ac035e9829c2, 0xf5f3b4ec3082900, 0x6d611c781f8e4f3d, 0xac6dae7969ed31a2, 0x25058d2c637aea7, 0xb33f083d7bb36290, 0x3c16bfcf179b69ab, 0xf3407e6af5ec301a, 0x2c500c942aab0583, 0x91a50c90bd76082b, 0xd84b8b87f0479e8d, 0x54b59093e8510066, 0x16311a3ae17e2de8, 0x23b6bde1d8cfb0d9, 0xbf853f08b6f6391e, 0x310570635fa50a4b, 0x3eaf4d1528a5d9ef, 0x33bb1433893ab055, 0xe6a344cec6382a58]

private theorem rounds04_2 : sixRounds 12 (by decide) quarter04_2 = quarter04_3 := by
  decide +kernel

private theorem rounds04_3 : sixRounds 18 (by decide) quarter04_3 = state05 := by
  decide +kernel

private theorem perm04 : KECCAK.f1600 absorbed04 = state05 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds04_0, rounds04_1, rounds04_2, rounds04_3]
  rfl

theorem block04 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes04 ++ tail) state04 =
      KECCAK.Bytes.run 0 tail state05 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes04 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb04 ws)) := by
    rfl
  exact (step state04).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words04).trans perm04))

private def absorb05 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x16 0x19 0x3 0xa 0x0 0x1 0x61 0x3)) 1 (by decide) (UInt64.ofBytes 0x5b 0x50 0x91 0x1 0x20 0x60 0x52 0x81)) 2 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x50 0x92 0x50)) 3 (by decide) (UInt64.ofBytes 0x80 0x34 0x5b 0xf3 0x90 0x3 0x91 0x80)) 4 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x2c 0x2 0x61 0x15)) 5 (by decide) (UInt64.ofBytes 0x4 0x60 0x6b 0x2 0x61 0x50 0x5b 0xfd)) 6 (by decide) (UInt64.ofBytes 0x80 0x80 0x90 0x1 0x81 0x3 0x36 0x80)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x35)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x90 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x80 0x90 0x91 0x92 0x90 0x1 0x20 0x60)) 11 (by decide) (UInt64.ofBytes 0x91 0x92 0x90 0x1 0x20 0x60 0x90 0x35)) 12 (by decide) (UInt64.ofBytes 0x56 0x83 0xd 0x61 0x50 0x50 0x50 0x90)) 13 (by decide) (UInt64.ofBytes 0x15 0x15 0x82 0x80 0x51 0x40 0x60 0x5b)) 14 (by decide) (UInt64.ofBytes 0x91 0x1 0x20 0x60 0x52 0x81 0x15 0x15)) 15 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 16 (by decide) (UInt64.ofBytes 0x2 0x61 0x15 0x80 0x34 0x5b 0xf3 0x90))

private def absorbed05 : Vector UInt64 25 :=
  #v[0xa64a6d588f46886e, 0x9c1b92bc1c9013, 0x2908f003b5e0a721, 0xe7d64467dc14b29c, 0x679bed301e00ebc8, 0xaf84d8ee888973ba, 0x9ebfc5bce0e28c32, 0x91bfa5651384cf9b, 0xf1798cc327d4aec0, 0xcfe0609315eb1dc2, 0x311029c158223774, 0x195ed2dd23dc4ae8, 0x9b5035315907f0f9, 0x3379c6b92438907d, 0xe858174ec46808c5, 0x438d2a7f95b1c591, 0xf35baa6eb98433b, 0xf51595c964eb7c2b, 0x11f5c44b9cab0bea, 0x8f4e64141fed11c4, 0x72bfcab88a3b678, 0x14f08d173ddea4a9, 0x613f1ee8ace4fd42, 0x5981dcdae388058b, 0x59fd9006474af67a]

private theorem words05 : absorb05 state05 = absorbed05 := by
  decide +kernel

private def quarter05_1 : Vector UInt64 25 :=
  #v[0x31aec2debc8903ec, 0xff269c55d7dc04b8, 0x2fab46f5cd7593e8, 0x30b91582789132af, 0x92833f51a817863b, 0x594c94e4a84a8d6a, 0xe29994bad80c0344, 0x284cc536731cb893, 0x184aecd25314c39f, 0x1dab0681b425acaf, 0x92aa4bd2fb9f0c67, 0x6160d924dca4afd1, 0x44d9a2b8789fe365, 0xf7cf5dca33a7c677, 0x1b4b3c19b50dee98, 0x14e4c42d78b581e0, 0x3c0b32794a1fc531, 0x3e9449efb8532718, 0xfa8a2cd890772ac0, 0xba4d12e271ca6896, 0xe67cbd02deab96a, 0x55fcbfa0df60a0de, 0xc2f67f4c0cdc7e90, 0x87b435f710c459bc, 0xc9428e0448ea8cc4]

private theorem rounds05_0 : sixRounds 0 (by decide) absorbed05 = quarter05_1 := by
  decide +kernel

private def quarter05_2 : Vector UInt64 25 :=
  #v[0x8387d44ae9f3d511, 0x26e3fd9b3c51d25, 0x852a0511360cbf77, 0xdf54fdc8ee1ee328, 0x4b57de59d8f3284, 0xee3ca7da53c8cd46, 0x3ab9907974c8be2a, 0xf69db4855da65d31, 0xe961a97de30a4cc0, 0xbb0ceee216632b8d, 0xb8842fdbe462259f, 0xc6f88b69a027590d, 0x33a83306ea08d185, 0x267f04be58cfd939, 0xa8ede78a2562884b, 0xb1c568894d2f0aaf, 0x642a9ad87e17cb64, 0x2e5eb72e8d68a2aa, 0xf81c8db4e8aa0660, 0xb0e6c519fb03b007, 0x2cb2ab75a47e6bb9, 0x40faa4a8b6782786, 0xa8d3fda10c14935, 0xff65acc115ede5e0, 0x8cc4f7df745588a1]

private theorem rounds05_1 : sixRounds 6 (by decide) quarter05_1 = quarter05_2 := by
  decide +kernel

private def quarter05_3 : Vector UInt64 25 :=
  #v[0x27b00eccb672c167, 0x5bbb59b7f416f334, 0x98746a0a7a052271, 0x439c3a62e86f67ea, 0xcd8b54acba79453d, 0x46d78ba260a74004, 0xcab47333119ac3ae, 0x6892932d4d20667d, 0xda150fc9f5f9112e, 0xa7453902d19f060f, 0xf7929b23e0ec208c, 0x88ceb42b5a1b82d0, 0x1e748e4ad6980c8e, 0x1675542dc9620621, 0x3a7a22cdc34917, 0x696adb334c3db907, 0xd985a232946c8d24, 0x1c9a58ab4483e3d8, 0x2700578bc58fcc1c, 0x988a55ccf649d49e, 0x2c3c1be8d6c4c086, 0x1c164ba1ff955a3d, 0xd2af249dc02deefa, 0xf785d10c70a7edd1, 0x4b579772eefe250b]

private theorem rounds05_2 : sixRounds 12 (by decide) quarter05_2 = quarter05_3 := by
  decide +kernel

private theorem rounds05_3 : sixRounds 18 (by decide) quarter05_3 = state06 := by
  decide +kernel

private theorem perm05 : KECCAK.f1600 absorbed05 = state06 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds05_0, rounds05_1, rounds05_2, rounds05_3]
  rfl

theorem block05 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes05 ++ tail) state05 =
      KECCAK.Bytes.run 0 tail state06 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes05 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb05 ws)) := by
    rfl
  exact (step state05).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words05).trans perm05))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
