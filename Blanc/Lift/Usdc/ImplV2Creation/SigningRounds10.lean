import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb060 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 1 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x23 0x60 0x52 0x82 0x3)) 2 (by decide) (UInt64.ofBytes 0x23 0x60 0x86 0x55 0x61 0x80 0x1 0x20)) 3 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 4 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 5 (by decide) (UInt64.ofBytes 0xe7 0x1f 0x61 0x11 0x84 0x0 0x60 0x5b)) 6 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x1 0x4)) 12 (by decide) (UInt64.ofBytes 0x52 0x81 0x29 0x60 0x52 0x82 0x3 0x81)) 13 (by decide) (UInt64.ofBytes 0x60 0x6a 0x56 0x61 0x80 0x1 0x20 0x60)) 14 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x40 0x60 0x39 0x91 0x29)) 15 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 16 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x0 0x60 0x33 0x5b 0xfd))

private def absorbed060 : Vector UInt64 25 :=
  #v[0xd5773dc59456a5a1, 0x1065a27833712b2a, 0xfb9372c4e04b6719, 0x2ada4e628731c48b, 0x4a9b3fcbc95c042e, 0xa3421fc21040c3b0, 0x7ff96efeb8ff4e4f, 0x80cd8b715b243fd3, 0xd103565ae1d5c1d1, 0xc0b32e4da0cf4511, 0x471c7a0966106eef, 0x8eb8c7f7560b5a0, 0x10eb7bb07b9560b, 0x999129ee3fc4fb77, 0xdcd74190b697d5bb, 0x3426ed01e201790b, 0xc738e389443a21de, 0x1e1d6971cdb0139, 0x3f3aba11f4ddbc2e, 0x8529f2e28666ade5, 0x6fbe8eca69cf7c38, 0xd7fbb620e22b3acd, 0xd48a607c3cb450c, 0x47fbad272b34ef88, 0xbff5037b1aa5d8fd]

private theorem words060 : absorb060 state060 = absorbed060 := by
  decide +kernel

private def quarter060_1 : Vector UInt64 25 :=
  #v[0x7aacc117f1a07f9, 0x5104ce8478ee9e8, 0x77b3274367f6d9ce, 0x450269927737ad1a, 0x5667e7dc9e0e5d13, 0x4b95159765a58dd5, 0xe8d50fca52a88fd3, 0xe0ed0de96803fe66, 0xa79ad207df41c725, 0x460465408808e63f, 0xf0a286082ac776fd, 0x27dae4c2e7d83d9c, 0x3b5f67b154bf2cf2, 0xc7094424fca86736, 0x8e6338227040d585, 0xd476a687fbf7b4fe, 0x50b0c08e883d74e0, 0xf3a58cb6e15135a6, 0x7fbbc40dba27cfa5, 0xebbe188769d90c87, 0xd5eb78efaa61ef50, 0x8b227a2f0021134b, 0xbb23cf7ca39549f8, 0x4aa2fa24ee5e4fea, 0x3a7e1d18d90a96e0]

private theorem rounds060_0 : sixRounds 0 (by decide) absorbed060 = quarter060_1 := by
  decide +kernel

private def quarter060_2 : Vector UInt64 25 :=
  #v[0xa27636b773ab6b0b, 0x9c55c48811d9ada9, 0x16b9175691cea5e2, 0x5bcfca6c3db681cb, 0xfa4554d954dc5bbc, 0xedbd1f0b6b47933, 0x9d340bc4fd6e99dd, 0xfe734c7627c1c217, 0xd2ddd7c084dda5e, 0xb2e826988efc0c7a, 0x7cc1308c91707471, 0x2b50217a687d408c, 0x7174ef9e67d9a21f, 0xef28bd9c051455bd, 0x6a0f17e6ab204fad, 0xcb2e1d534fe40f5a, 0x559cf13ab614e23d, 0x4ff09ed7c251999a, 0x67240115f29f299b, 0xcd1a287b9226a5d5, 0x76852da943116d32, 0x5b0d06a3191ef71a, 0x15310e74cd1f0fe, 0x872ed20a4d6658aa, 0x553a2b3d6c68a32a]

private theorem rounds060_1 : sixRounds 6 (by decide) quarter060_1 = quarter060_2 := by
  decide +kernel

private def quarter060_3 : Vector UInt64 25 :=
  #v[0x3b2260cc509ef63b, 0xfdb48822155315dc, 0xd4222aa0ab05cb2a, 0x157ffe0331fb1bc2, 0x64e84ca5a2417211, 0x7279512183036047, 0x514cddbdf65414db, 0xef8b2e07d2aa62a4, 0x113d0f2756b10ede, 0x7a1edc47278a8647, 0x59eaf9fc1ce6fb73, 0x85053c1bceb1ca20, 0x9f1e718181e099f5, 0x183b712f433824e2, 0xaafa6055817bfd0e, 0x8923b524eacfdc9a, 0x98e08927b6faa540, 0xba6de13f85710fe, 0x19f2c330c981b8d3, 0xcabce4c93448f6a, 0x5f33af832eb128a4, 0x34c1e581695be7e8, 0xcfedf3736cb75c5f, 0xf13d54c2293211e5, 0xbd0485a053681b01]

private theorem rounds060_2 : sixRounds 12 (by decide) quarter060_2 = quarter060_3 := by
  decide +kernel

private theorem rounds060_3 : sixRounds 18 (by decide) quarter060_3 = state061 := by
  decide +kernel

private theorem perm060 : KECCAK.f1600 absorbed060 = state061 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds060_0, rounds060_1, rounds060_2, rounds060_3]
  rfl

theorem block060 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes060 ++ tail) state060 =
      KECCAK.Bytes.run 0 tail state061 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes060 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb060 ws)) := by
    rfl
  exact (step state060).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words060).trans perm060))

private def absorb061 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x90 0x40 0x60 0x52 0x20 0x60 0xd 0x60)) 1 (by decide) (UInt64.ofBytes 0x20 0x61 0x15 0x11 0x85 0x80 0x54 0x20)) 2 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57 0x50)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x80 0x80 0x1 0x4 0x60)) 8 (by decide) (UInt64.ofBytes 0x81 0x2e 0x60 0x52 0x82 0x3 0x81 0x82)) 9 (by decide) (UInt64.ofBytes 0x9d 0x58 0x61 0x80 0x1 0x20 0x60 0x52)) 10 (by decide) (UInt64.ofBytes 0x91 0x1 0x40 0x60 0x39 0x91 0x2e 0x60)) 11 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 12 (by decide) (UInt64.ofBytes 0x20 0x61 0x54 0xb 0x60 0x5b 0xfd 0x90)) 13 (by decide) (UInt64.ofBytes 0x5b 0x56 0xfd 0x41 0x61 0x86 0x90 0x5d)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x55 0xb 0x60)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed061 : Vector UInt64 25 :=
  #v[0x4b1502b4c6059e1b, 0x4f9551089dee10a1, 0x52c9e8750245b54e, 0x941603b2dec00770, 0xe7be06268c0a8fdf, 0x4fca4cd40b548d2f, 0x7cff1fd29ecdf03c, 0xd62ff7c541fab2aa, 0x309af1dedcfc563, 0x95d8ece0d57c1592, 0xf98dba91537f8091, 0x3c4ff9de21ee25e6, 0xbc433f657f9e980f, 0x58c53819d1a5529, 0xa4e6b880e8597df3, 0xa4af0210f207669a, 0x133ca7bd8631f68d, 0xab14a795e388697, 0xd5c0c28de73df3b4, 0x68d06f7fadde483c, 0x8dbeb6c1262a853d, 0xc7a6c21b6574b3b3, 0x62d11274b44cacd3, 0xaebdd20e2e9d966f, 0xe967f7f3ee43b11e]

private theorem words061 : absorb061 state061 = absorbed061 := by
  decide +kernel

private def quarter061_1 : Vector UInt64 25 :=
  #v[0xc020c55d469ba132, 0x12185ba006f55e9c, 0xa57cc2e9e18d59c, 0xdec0c9ac5c3841b3, 0xb8b307750ed8025c, 0xf968064d7ba0d17e, 0x1bad173fea07f15b, 0x4bca6c5f481878b8, 0xb132662f90c8de64, 0xe35943c7d22500b4, 0x2d70fdfd811a4a10, 0x45e206027473893d, 0x45f9d3450c958534, 0x54f983761a2bb00c, 0x1ee6566ea30de5d1, 0x5b55002bb05580c0, 0xaa6587cf5607f4d5, 0x5ded130beb7347d4, 0x29fd8e571a6f5b2c, 0xb4b9f9277e608a20, 0x31fd2744e95605d3, 0x68cd3a014b301305, 0xe75ed45bbfe96bf3, 0x1969d2ae22987532, 0x49c3d7e440227a04]

private theorem rounds061_0 : sixRounds 0 (by decide) absorbed061 = quarter061_1 := by
  decide +kernel

private def quarter061_2 : Vector UInt64 25 :=
  #v[0x4fbfaf515c019c22, 0x3372dba9f45a60da, 0x716424c5737f3bc9, 0x9759fae557530674, 0x3ea38ca946854a1b, 0xadcbf184cb03bd3b, 0xf6319453980e13d8, 0xcaf93498d9bb1aa0, 0xdea6e60fdad4373e, 0xdab5fa3b5dd0856d, 0xf6ea4b7a982b4ebe, 0x8352bf12f7557331, 0xad61cfd8d306f32d, 0xc376a4549640589c, 0xa1f22d1294dfed3a, 0x782e9b57b12c6905, 0xc85e8301c1d1c3b6, 0xbeda57b6a5452c74, 0x35867589b87fc8bc, 0x8c89a5b78ea9985a, 0x482acf684d39af26, 0xc7cc999a0111fe28, 0xba244655313eb93a, 0x36ad0608e2cda52a, 0x6a85a359d529e830]

private theorem rounds061_1 : sixRounds 6 (by decide) quarter061_1 = quarter061_2 := by
  decide +kernel

private def quarter061_3 : Vector UInt64 25 :=
  #v[0x143f3f4ab6fbee75, 0xa1d7d25ffe20c368, 0xd2c9078c9cbcb877, 0xe3c4e332b5da2a0, 0x5892c6578af6348a, 0xc36700957a45eab8, 0x8edf2a73cd0a788f, 0x7ae25a1287e9350f, 0xeed2f65f91557245, 0xcb1bb29715ef0dba, 0x4809bd845b94b08a, 0xede1c06e0ebbee99, 0x8127d7a6870dc187, 0x7a39cc8db4516069, 0x49db242b9165005c, 0x956e92c79a24e74a, 0x894a18fa4c229ad7, 0xa1a1938f9bb9e365, 0x6628f6c423abc2c1, 0x677d07aced3d9c87, 0x3c645f62c6f3e8a6, 0x8b1f3a62634b1d20, 0xd7c8cf1d53f08a55, 0x1c1bec55274f3a21, 0xd203c33dfa2ee5d5]

private theorem rounds061_2 : sixRounds 12 (by decide) quarter061_2 = quarter061_3 := by
  decide +kernel

private theorem rounds061_3 : sixRounds 18 (by decide) quarter061_3 = state062 := by
  decide +kernel

private theorem perm061 : KECCAK.f1600 absorbed061 = state062 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds061_0, rounds061_1, rounds061_2, rounds061_3]
  rfl

theorem block061 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes061 ++ tail) state061 =
      KECCAK.Bytes.run 0 tail state062 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes061 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb061 ws)) := by
    rfl
  exact (step state061).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words061).trans perm061))

private def absorb062 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0x86)) 1 (by decide) (UInt64.ofBytes 0x20 0x90 0x40 0x60 0x52 0x20 0x60 0x9)) 2 (by decide) (UInt64.ofBytes 0x41 0x61 0x86 0x90 0x90 0x20 0x61 0x54)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0x56 0xfd)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0x87)) 7 (by decide) (UInt64.ofBytes 0x20 0x90 0x40 0x60 0x52 0x20 0x60 0x9)) 8 (by decide) (UInt64.ofBytes 0x41 0x61 0x86 0x81 0xc0 0x20 0x61 0x55)) 9 (by decide) (UInt64.ofBytes 0x81 0x81 0x0 0x60 0x33 0x5b 0x56 0x23)) 10 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x20 0x60 0xd 0x60 0x52)) 11 (by decide) (UInt64.ofBytes 0x90 0x93 0x20 0x90 0x82 0x91 0x40 0x60)) 12 (by decide) (UInt64.ofBytes 0x90 0x52 0x81 0x88 0x51 0x80 0x55 0x93)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x51)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x16 0x8a 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xc9 0x7d 0xf8 0x30 0x85 0xab 0x7f 0x93))

private def absorbed062 : Vector UInt64 25 :=
  #v[0x6ea7fdbd84dda6d7, 0x7f2ea7b512d917a2, 0xc5a76e26bb0a681b, 0x5c9a2193d96cc1a, 0x7dc2d3fc0ff72761, 0x78a62a955692a122, 0xb211b536cc156b42, 0x8876dea2242d0011, 0x181836d6f3652de3, 0xc1e613a1b914af49, 0x75779e04b99307b2, 0x15a4f0b9c897ce46, 0x7efaa30695a3d907, 0x6fa67e31800afe14, 0x88903e8e4da4175d, 0xf17381a124aac16c, 0x76ad3847a5781637, 0x183834c38a1eab66, 0x80a699695bcce776, 0x38be44a928f17fbb, 0x4551d3e33caf2f82, 0xaf36a9269de42268, 0xa2d61cf70013be73, 0x48708c6bdaf854ad, 0xbde2d9a59609aba2]

private theorem words062 : absorb062 state062 = absorbed062 := by
  decide +kernel

private def quarter062_1 : Vector UInt64 25 :=
  #v[0xa19a51faf8713d45, 0x4c907e12e199b741, 0x805f415d7ea31ffc, 0x3368e9665a557540, 0xb869ec53b5e4c4c5, 0xfc29a15c7f9e44c2, 0xe545bcecf63482f7, 0x8deb9d8076df41d3, 0xa002d2c5587018f8, 0xcf4640b242266e58, 0xfcc64503547e23c3, 0x5db61096a0f38b27, 0x1b3d4f752bd8e528, 0x93abf36cca01b4d4, 0x822a7e73420e61c4, 0x533620e8acde12c4, 0x728d1e4d03aaebc1, 0xa6cd32321b1b8600, 0x20a5ee759630fdfe, 0x47541ce8862ce85c, 0xaff14a28ed7c8431, 0x4a2f26f0c1d8ba58, 0x96d9187f66d1f256, 0xa23c1dfa0873c894, 0x11e4ca72ec0102b4]

private theorem rounds062_0 : sixRounds 0 (by decide) absorbed062 = quarter062_1 := by
  decide +kernel

private def quarter062_2 : Vector UInt64 25 :=
  #v[0xcfab27d765d6f31d, 0x8737d04ee594d9d6, 0x195b5bd3d130133a, 0x2057eb12b251f9c6, 0x4436b2d7d32112b7, 0x19fbcaa85cf347c9, 0x53155f91b856b5ba, 0x4596b44c028add4e, 0x28db2ca87961f484, 0xbefa58b112d74d26, 0x244cf116a8495f6f, 0xc21c804e009ef906, 0x42efab68da7fb268, 0x3e7a2081a506ea7a, 0x506f29e79ddfe54a, 0xfd9d16f11d8f295d, 0x2003cee7853dfd20, 0x170f602e14a8dcb1, 0x111b6c2660c49e65, 0xeeaf0ec8bf47d3e7, 0x89585d1f43efd181, 0xc29a10ff37168a39, 0x6b22bc44c2af1ce5, 0xcaebf60d8ecd1172, 0xefb695d5b7991721]

private theorem rounds062_1 : sixRounds 6 (by decide) quarter062_1 = quarter062_2 := by
  decide +kernel

private def quarter062_3 : Vector UInt64 25 :=
  #v[0x3d6106baea8e5e50, 0xd8f59381770e7dd2, 0xf8fc6379211ca12d, 0xa08ab5abf43e0c72, 0x913a3067d3cc8ba6, 0x7210874ba43674ec, 0x2c372e032dbf270d, 0xc3b6908e41188a1d, 0x9ad6da9cb1233acc, 0x7cbf045c4eb78f63, 0xb5855f1aa98d646e, 0xc37f6a545a431ea9, 0x91f127aea4842b7b, 0xd49a10cb7a6f7ee7, 0xbd105c57a9ff8c9, 0xa0ae574ed1985da, 0xda3346dbaca66e1e, 0xcfc1c3754db26c19, 0xd7504c5f0383a46, 0x129035ecd5e33d41, 0x84164d5321310bc8, 0x853a9945f9659a09, 0xab2f554801b47e86, 0xbefbeafeec8a25f3, 0xc6bd5fca54be96be]

private theorem rounds062_2 : sixRounds 12 (by decide) quarter062_2 = quarter062_3 := by
  decide +kernel

private theorem rounds062_3 : sixRounds 18 (by decide) quarter062_3 = state063 := by
  decide +kernel

private theorem perm062 : KECCAK.f1600 absorbed062 = state063 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds062_0, rounds062_1, rounds062_2, rounds062_3]
  rfl

theorem block062 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes062 ++ tail) state062 =
      KECCAK.Bytes.run 0 tail state063 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes062 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb062 ws)) := by
    rfl
  exact (step state062).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words062).trans perm062))

private def absorb063 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x17 0xf9 0x3b 0x62 0xc4 0x34 0x92 0xb5)) 1 (by decide) (UInt64.ofBytes 0x74 0x75 0x64 0x6d 0x53 0xb2 0x2b 0x21)) 2 (by decide) (UInt64.ofBytes 0xe0 0xed 0xc2 0x92 0xda 0xe5 0xe7 0xc8)) 3 (by decide) (UInt64.ofBytes 0x90 0x1 0x3 0x90 0x82 0x92 0xf8 0xc9)) 4 (by decide) (UInt64.ofBytes 0x52 0x81 0x86 0x51 0x80 0x40 0x60 0xa3)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x51 0x90)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x88 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xf2 0xdd 0x7f 0x91 0x0 0x60 0x91 0x16)) 9 (by decide) (UInt64.ofBytes 0xc2 0x69 0x9b 0xc8 0xe2 0x1b 0xad 0x52)) 10 (by decide) (UInt64.ofBytes 0x2b 0x95 0xaa 0x8d 0x37 0xfc 0x68 0xb0)) 11 (by decide) (UInt64.ofBytes 0xf5 0x28 0x16 0xa1 0xc4 0x63 0xf1 0xa7)) 12 (by decide) (UInt64.ofBytes 0x81 0x91 0xef 0xb3 0x23 0xf5 0x4d 0x5a)) 13 (by decide) (UInt64.ofBytes 0x50 0xa3 0x90 0x1 0x20 0x60 0x3 0x90)) 14 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x94 0x95 0x1 0x60)) 15 (by decide) (UInt64.ofBytes 0x1 0x74 0x54 0x1 0x60 0x5b 0x56 0x50)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed063 : Vector UInt64 25 :=
  #v[0xc237300e99055494, 0x29e04a1495917386, 0xa08c7a79aa906adb, 0x922d026c59fade3e, 0x8375bdba6a75dfde, 0xd07121910e09bb8f, 0x70569b8d49deaa14, 0x7b5e4e12f511eb69, 0xe23c0cc98027dd8a, 0x6cc7305993341de6, 0xf753c482a366aa7d, 0xcd9096ee20e8156c, 0x56d02501f5d0433c, 0x959d753fd0fb5ba4, 0xde7540f9e960fcb4, 0xba638334216f709e, 0x68373a1400f36fcf, 0x16b933e83d0df999, 0x3534bd12f4a56a27, 0xaac7aaa261ebf366, 0xa89d592140b9f2c6, 0xea89bda3ab003d45, 0x4d84826da9d020d4, 0x8285d0a40379f629, 0x49cc47c179b7250c]

private theorem words063 : absorb063 state063 = absorbed063 := by
  decide +kernel

private def quarter063_1 : Vector UInt64 25 :=
  #v[0x89e07eb3b20baf84, 0x1bbb2ff68bc8a68d, 0x1b70f3379e513e6a, 0x6eb6e739fa5c93f1, 0x66eee98f13e31f02, 0x72a2702d7e649d61, 0x52dc6dc57b9c3efe, 0x7366324f202e21a7, 0x7048d3ed95189a79, 0xd760a0c8e2d72ce0, 0x37fe234d527c5649, 0xc4798468512cddc3, 0x8ad4ca00fd285609, 0xb8c197b7fba338ae, 0x3136d1507aaefe3f, 0xcc80ac632f5c283d, 0xaad588546a8ba6dc, 0x72f6ce88728112e3, 0xba8ce827f4a34ad6, 0xfdb56bdd9c3c9e58, 0x7b6ea49e3e097318, 0x1cd0d455f0283d28, 0x80a96798985d26f7, 0xae7eb66b23eeab0, 0x45265a6984227162]

private theorem rounds063_0 : sixRounds 0 (by decide) absorbed063 = quarter063_1 := by
  decide +kernel

private def quarter063_2 : Vector UInt64 25 :=
  #v[0x36c46499a757c1f8, 0x8380af1c20cb1c55, 0x372bad55a368923, 0x7512a28cc9b7fee5, 0xc92ddf86f5a3e4d9, 0x28a28f3894f8043d, 0xaced9ea489b57c6, 0xa835e34a69758b63, 0xd442dc60367e1611, 0x3cb119343019347f, 0xd27c058d854b722b, 0xed8f97b578bad8c6, 0x9805d2662f1a73b4, 0xfe7f33c918ce3429, 0xf3fc2cfc00df7b59, 0x85b406adae78eb71, 0xc28f3b40606a939c, 0x86ee1b0336067afb, 0x3627d99d4b645a0c, 0xd75c04a36e8cba56, 0xb5fb6db6fbda0c75, 0x3ecf02ee6f0751cc, 0xfc3c1cc24ca7584, 0x74ee81f4831a4926, 0x4ec804953b21c20e]

private theorem rounds063_1 : sixRounds 6 (by decide) quarter063_1 = quarter063_2 := by
  decide +kernel

private def quarter063_3 : Vector UInt64 25 :=
  #v[0x1abda1b8dd81208c, 0xf031fbea2795c0bc, 0x2729531b942e577c, 0x115e0cfaec01b6dd, 0xbc3d00df7524f717, 0x2d38e68dad15cc91, 0xcef0b8af0b74add6, 0x63c039b225ce7aca, 0x3196597f2c0f9a01, 0x261bbd82a6307023, 0x710b3fadb46d2487, 0x7352c59430d6dd40, 0x60b08c7f3b77822e, 0x526fe45574b1f74e, 0xcaeb8bf5ecf6ae34, 0x4c13f584642c47b4, 0x988a06c88a3cee67, 0x61d795bcf6d9b182, 0xd439595bb6616345, 0x4b9de80864b42e74, 0x2782d267a2979ec0, 0x8838d25f9b913e4e, 0x792aceaf4c37477e, 0xd696ae8b1eb94a35, 0x89007eb89ce54d54]

private theorem rounds063_2 : sixRounds 12 (by decide) quarter063_2 = quarter063_3 := by
  decide +kernel

private theorem rounds063_3 : sixRounds 18 (by decide) quarter063_3 = state064 := by
  decide +kernel

private theorem perm063 : KECCAK.f1600 absorbed063 = state064 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds063_0, rounds063_1, rounds063_2, rounds063_3]
  rfl

theorem block063 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes063 ++ tail) state063 =
      KECCAK.Bytes.run 0 tail state064 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes063 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb063 ws)) := by
    rfl
  exact (step state063).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words063).trans perm063))

private def absorb064 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x2 0x22 0x61 0x15 0x16)) 3 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x81 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x24 0x60 0x10 0x60 0x52 0x1 0x82 0x4)) 9 (by decide) (UInt64.ofBytes 0x73 0x75 0x61 0x50 0x7f 0x52 0x1 0x82)) 10 (by decide) (UInt64.ofBytes 0x61 0x70 0x20 0x3a 0x65 0x6c 0x62 0x61)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x64 0x65 0x73 0x75)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x1 0x82 0x44 0x60 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x60 0x3 0x90 0x81 0x90 0x51 0x90 0x52)) 15 (by decide) (UInt64.ofBytes 0x0 0x60 0x33 0x5b 0xfd 0x90 0x1 0x64)) 16 (by decide) (UInt64.ofBytes 0x52 0x20 0x60 0xc 0x60 0x52 0x81 0x90))

private def absorbed064 : Vector UInt64 25 :=
  #v[0xd6a3546f43b8cc3f, 0x718226e838d93d8d, 0x6afdd201ea79fc99, 0x3cdf6a721f20da18, 0xd5cceaf8801ee7dd, 0xf44b0b9c6d3082aa, 0x705f8018edc08a, 0x59f43252387b0ab7, 0xa30f2b06cf3230c7, 0xf6b3c21e06bfbc21, 0xc49956d2015a3b8, 0x82f741d911100c42, 0x12af1a0e466acec2, 0xc378d9c6ba1cd9a9, 0xc43d887a7b81a1a1, 0xa50486da066c1dc5, 0x64429f29fe0b9923, 0x681464afdb5582fe, 0xbe77e4e550f1c502, 0x3c7934a1fc4f2360, 0x1611cd154a614eec, 0xc4209291e5539c26, 0xd8fbfe983d2712a4, 0x44f00ea43d8cae28, 0x69b57c0476fd62e7]

private theorem words064 : absorb064 state064 = absorbed064 := by
  decide +kernel

private def quarter064_1 : Vector UInt64 25 :=
  #v[0x8c27e7226d7d5627, 0x30f60cb7fca55140, 0x72b5d43e901ec104, 0xeb0e50d1aa9d857e, 0x2e33ac3daa1540b3, 0x9a67286da8523bf5, 0x41a42218e6b5d4f2, 0x90f41fb9d26daf5c, 0xf6981c8f84f6cbfe, 0x184726aa8561b233, 0x1d5d9be4e65963a5, 0x37d1fb582b7a4597, 0xb6d8a0aac71acdd8, 0x5120352c73b92f7c, 0x9c1ad4ec519e6941, 0x5833e57a4cffc55, 0xb55bc368a8e50e26, 0x937109bdf147533e, 0x70fce8bc28d7ee2c, 0x724573af6ef6ff45, 0xa7891875f340df67, 0x40519b5088631734, 0xd9755d35754af94d, 0xd6de3be899dbd8fa, 0x940a382ddb8769ed]

private theorem rounds064_0 : sixRounds 0 (by decide) absorbed064 = quarter064_1 := by
  decide +kernel

private def quarter064_2 : Vector UInt64 25 :=
  #v[0x142d7a09543343c2, 0x959e1294bebd7603, 0x6d52af7b5267045b, 0xcb2469cd9997286f, 0x8c23d549ce688691, 0xbac5bad1fcb27aef, 0xa0f16fee47b70c3a, 0xe274e2deacf68452, 0xda8cb07ee2948141, 0x35ce26924f3a64de, 0x54c35d131261676a, 0xe09d36c3096c833b, 0x35c23609d253c59a, 0xeec0cee31a0807c6, 0xeb38703a9921d027, 0x57a640fcced79299, 0xf7a13b1952270127, 0x158392facaa97926, 0xe05dd87641193920, 0xebc346c6756bdd69, 0xca4611596e79c9e8, 0x2e791fd01d3f67e8, 0x9f7b8b702caabd30, 0x3bbacc717fffe04e, 0x153e99babf87ff55]

private theorem rounds064_1 : sixRounds 6 (by decide) quarter064_1 = quarter064_2 := by
  decide +kernel

private def quarter064_3 : Vector UInt64 25 :=
  #v[0x31b24173b2f462bc, 0x24572eba57155e18, 0x2d9c814f9ad25aa4, 0xff1aa8a44e37e121, 0xc78a0aef916fbf21, 0x2f2c0fb5ca492d60, 0xda0c7b7f5cb0026e, 0xca981b7eae82de1c, 0xfcfbcd07fc1628e0, 0xb8bb25aeba0e4be8, 0xebe7ea9c7b1dcca3, 0xee7ae1ab97b2d55, 0x82b06495145a1e35, 0x293e9b5b99fff1f0, 0x55f9cfe3486a6630, 0x1342550444aaff4, 0x5963c7ce4a5224e0, 0x509bd325ac38035c, 0x6c8a710865f17be8, 0x3a7bafa04dc135ac, 0x41fc889a10c9904, 0x51aa5ccc80fede98, 0xf5d1fa8f74d1667c, 0x461910fdbb1dd74d, 0x42cc2cda5d6e8a08]

private theorem rounds064_2 : sixRounds 12 (by decide) quarter064_2 = quarter064_3 := by
  decide +kernel

private theorem rounds064_3 : sixRounds 18 (by decide) quarter064_3 = state065 := by
  decide +kernel

private theorem perm064 : KECCAK.f1600 absorbed064 = state065 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds064_0, rounds064_1, rounds064_2, rounds064_3]
  rfl

theorem block064 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes064 ++ tail) state064 =
      KECCAK.Bytes.run 0 tail state065 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes064 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb064 ws)) := by
    rfl
  exact (step state064).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words064).trans perm064))

private def absorb065 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x16 0xff 0x60 0x54 0x20 0x90 0x40 0x60)) 1 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0x6a 0x22 0x61)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 7 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 8 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x21)) 9 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x21 0x60 0x34 0x57)) 10 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 11 (by decide) (UInt64.ofBytes 0x0 0x60 0x33 0x5b 0xfd 0x90 0x3 0x91)) 12 (by decide) (UInt64.ofBytes 0x52 0x20 0x60 0x3 0x60 0x52 0x81 0x81)) 13 (by decide) (UInt64.ofBytes 0x16 0xff 0x60 0x54 0x20 0x90 0x40 0x60)) 14 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x57 0xd3 0x22 0x61 0x15)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed065 : Vector UInt64 25 :=
  #v[0x468338a717cc69b5, 0x8e6810e503a79c16, 0xe175af98816ea29e, 0xf8052516aad96980, 0xa026020599f005bc, 0x13f2b4fcd7f0b544, 0x7876b19d656b480e, 0x2bb10daae86c3ab8, 0xdbd8d66c974a7567, 0x54c4f321f7d7ae56, 0x3e7c3ed7db8fc10a, 0x90001d9354f35cb2, 0x7f823c9832636efd, 0x51ce7c77476b2d44, 0x1fb3dbf0f679108e, 0xe5ca5009d213cfa2, 0xc638078432ef752e, 0x818acaffc2848edf, 0x92eadf9565fc78cd, 0x36c8ef8438a172f3, 0xa9442b2740c964c2, 0xfce76ed4c59e4e85, 0xd45c038be0ff3a86, 0x1dde0d10e808712c, 0x186649170acaa940]

private theorem words065 : absorb065 state065 = absorbed065 := by
  decide +kernel

private def quarter065_1 : Vector UInt64 25 :=
  #v[0x82c605b88723b30, 0xade00ea9b344ce0b, 0xd2782372850b89c0, 0x44c47efe799c8da6, 0xddcd13789e4ad226, 0x4836856d5c21df57, 0xd73ae40686dcb9c7, 0xc88cff737b0ccd01, 0x4706a2b1cb938992, 0x6b3a50a14d97565d, 0xec94c42a2a87ea48, 0xc8179889d3c9a183, 0xbce1d2c28f0312b6, 0x76ec8857266a8a93, 0xc318ebf5e8b84157, 0x425d3155afbc9c82, 0x2ebd233f00433688, 0xd68339a6ac94f978, 0xb9102af0416602fa, 0x24ef629085ec60e7, 0xcc5769c66d8172f7, 0xda15a3186dde07e0, 0xdbc0006668e4fda5, 0x8d9dfbd7fe940551, 0x3ca40d4abbd86ecc]

private theorem rounds065_0 : sixRounds 0 (by decide) absorbed065 = quarter065_1 := by
  decide +kernel

private def quarter065_2 : Vector UInt64 25 :=
  #v[0xc9bf07173fd5a922, 0xab7115a5c0a5883f, 0xc6224a2865107060, 0xb10573c2bd2d9796, 0xa34c9ea6ef152bf3, 0xe4bd8ef8cfc1565a, 0x22bca57371239570, 0xdd0e82638c2a33bb, 0xbe29303443333f0d, 0x9dc066be20cf02f6, 0xff7962215d900bcf, 0x70a6206f680ec910, 0x245fdd4ef474795c, 0x896d26982694ef2d, 0xaf2b453436c479e9, 0x5d681e5a15950dd8, 0x6e4c4f2cef04319f, 0x5614fbfb06bcc3fa, 0x5f72621701092119, 0xdfdc9348541d1c88, 0xf1bc2c57a8efe3db, 0x21ce1ba27f8f4fb4, 0x50549e9e00f7ee96, 0xa333dd82af29e99a, 0x81dbb31225bf8055]

private theorem rounds065_1 : sixRounds 6 (by decide) quarter065_1 = quarter065_2 := by
  decide +kernel

private def quarter065_3 : Vector UInt64 25 :=
  #v[0x707c93daecb1ac4a, 0xed9293497bc0fc1f, 0xfd014f479b35cfdf, 0x3371216db5d355b4, 0xa1c72bf575649a26, 0x336f544c7b69ad81, 0x6eb1256aae0ce4d5, 0x22d4cb043a8bcbba, 0x779019d50fe9d957, 0xea1cb5c3a53e0a22, 0x9869fb7d97c6410f, 0x6e6b9df2549e4da0, 0xf8bce01cc8d15ddd, 0x912d627051cde29, 0x1f74732d72bdb8af, 0xbb0d6b0cb117d2f4, 0x72db3cd43ee543f4, 0x903bb40b9f220cc0, 0x80334eccd5a2a875, 0xf5139761aa2e728f, 0x918f81de197a0b8b, 0x75e7938c04239584, 0x7a0f18847e2273cc, 0x1dd254a339894b30, 0x8e6522795d39c0ba]

private theorem rounds065_2 : sixRounds 12 (by decide) quarter065_2 = quarter065_3 := by
  decide +kernel

private theorem rounds065_3 : sixRounds 18 (by decide) quarter065_3 = state066 := by
  decide +kernel

private theorem perm065 : KECCAK.f1600 absorbed065 = state066 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds065_0, rounds065_1, rounds065_2, rounds065_3]
  rfl

theorem block065 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes065 ++ tail) state065 =
      KECCAK.Bytes.run 0 tail state066 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes065 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb065 ws)) := by
    rfl
  exact (step state065).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words065).trans perm065))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
