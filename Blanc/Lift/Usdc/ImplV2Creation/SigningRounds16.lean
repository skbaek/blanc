import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb096 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x0 0x1 0x74 0x54 0x1 0x60 0x5b 0x56)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x16 0xff 0x60 0x4 0x90 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x80 0x40 0x60 0x57 0x19 0x33 0x61 0x15)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x4 0x60 0x20 0x60 0x52 0x81 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x82 0x24 0x60 0x10 0x60 0x52 0x1 0x82)) 12 (by decide) (UInt64.ofBytes 0x61 0x73 0x75 0x61 0x50 0x7f 0x52 0x1)) 13 (by decide) (UInt64.ofBytes 0x75 0x61 0x70 0x20 0x3a 0x65 0x6c 0x62)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x64 0x65 0x73)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x44 0x60 0x0 0x0 0x0))

private def absorbed096 : Vector UInt64 25 :=
  #v[0xf97ee222e711a499, 0x1c398927299d3b1d, 0xdec76d7d4b88838e, 0xf80efb4ee63625c5, 0xc28ceabbd8273a8e, 0x1eb8870e3d09adcf, 0x388e10598af71fae, 0xffae123a1f64fe81, 0x70bb52da8c3b3866, 0x3eca6242fb1a75bf, 0x130832267b8bdf90, 0xb6ce87635c587500, 0x815226b59b0eae5c, 0x464a043c2986e73d, 0xa6821242e891a561, 0xbf7e645e820a7a85, 0x7d5b54a4a548d04e, 0xbc00a5bc7d530601, 0x73df5e8f040fde48, 0xb55dec5dfeab0565, 0xd16d17c0855acda1, 0xce6f7b7f65d19afc, 0x6f9f08e054782556, 0xc231b4cef239ef9d, 0xe8cdf7cad7b3d4ec]

private theorem words096 : absorb096 state096 = absorbed096 := by
  decide +kernel

private def quarter096_1 : Vector UInt64 25 :=
  #v[0x2455b8e6483d9131, 0xa8bd5f73531cf824, 0xec9bf9538a30941a, 0xa1237ae3318feb6d, 0xf7440ed7bb98587c, 0x99064ed18e891874, 0x321a119568fde4fb, 0x9a6d8acb64281e6, 0x94a2e6321035c412, 0xd1222f079b918f7f, 0xab5f2114b2f1cba4, 0xbf3f7e765d073cbf, 0xbae771c8c7eaa2f7, 0x31d969557af45dfb, 0xf907f80007fe1f93, 0x530c6d3e3a648b1d, 0xe526fa64db2ba53b, 0x455546254e261677, 0xa7e0fffed35321d0, 0x9667ade5f20f95cf, 0xbd147fe941599d46, 0x53b5bae787d3aec2, 0x799bbf7a9b730c54, 0x4e72c07c55a1dde3, 0xc6107d634eb6187b]

private theorem rounds096_0 : sixRounds 0 (by decide) absorbed096 = quarter096_1 := by
  decide +kernel

private def quarter096_2 : Vector UInt64 25 :=
  #v[0x1e655a8cacb2afb0, 0x6ab9b8429ae47629, 0xc1bd7e22d1e5d408, 0x5b46e6f5ae17c195, 0x4995b0f27e4d35fc, 0x88200d742c4f2189, 0x2cdeaf5bedcf5ba, 0xfe4edf6149749946, 0x475cf4d72b0bd663, 0x6f4c4643aa743218, 0x657cfe52eb87b6b6, 0x2404f9b541f5a47d, 0xe86e853af5d350d6, 0xa165842d670be553, 0xb68f4e68f0ce97b8, 0x8fbff6dd6801d23d, 0x3e59141a97153165, 0x424a5fe07876551f, 0xe040755cba978e73, 0xdeb8c065ae79f47e, 0x4f309e109c54d4ce, 0x42c649255ee6ea16, 0x672ec53c4ed150ea, 0xdc431700012004e1, 0xbfb91d2246405117]

private theorem rounds096_1 : sixRounds 6 (by decide) quarter096_1 = quarter096_2 := by
  decide +kernel

private def quarter096_3 : Vector UInt64 25 :=
  #v[0xaf4e9a485f0233be, 0x7f71398284fdcb4c, 0x974ca9ec8ff1302f, 0xc16eaf21ed6fb525, 0x40c6a63b7a0477dc, 0xdcabca4ff9677f49, 0xa3be2054edf30e0b, 0xfa14896652924c79, 0xe6e17b6d59ba4fd1, 0x165f854e8f21f4d, 0x306cb14624845d01, 0x5cce3e8ec382c13b, 0x711b902ea999d2e7, 0x6d8aa0e9bce9cf9f, 0x50d456c042a78d1e, 0x9fb72a6ee9680716, 0xc4e145aa14147a98, 0xcfa384d7b95112ba, 0x977e940da9eea0c6, 0x95bba3d429401809, 0xc3f22483a72750d7, 0x56476245d196f6fb, 0xaf85cafee86d5396, 0x225a97717b5c16b6, 0x7bae8effa6777dd8]

private theorem rounds096_2 : sixRounds 12 (by decide) quarter096_2 = quarter096_3 := by
  decide +kernel

private theorem rounds096_3 : sixRounds 18 (by decide) quarter096_3 = state097 := by
  decide +kernel

private theorem perm096 : KECCAK.f1600 absorbed096 = state097 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds096_0, rounds096_1, rounds096_2, rounds096_3]
  rfl

theorem block096 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes096 ++ tail) state096 =
      KECCAK.Bytes.run 0 tail state097 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes096 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb096 ws)) := by
    rfl
  exact (step state096).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words096).trans perm096))

private def absorb097 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x64 0x60 0x3 0x90 0x81 0x90 0x51 0x90)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90 0x1)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x0 0x60 0x16 0x89 0xff)) 5 (by decide) (UInt64.ofBytes 0x90 0x40 0x60 0x52 0x20 0x60 0x3 0x60)) 6 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x90 0x89 0x54 0x20)) 7 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0x9a 0x33 0x61)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 13 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 14 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x25)) 15 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x25 0x60 0xc5 0x59)) 16 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1))

private def absorbed097 : Vector UInt64 25 :=
  #v[0x6f977bef65188b05, 0x3af531d60ba95b1f, 0xa276523b2e318640, 0xd7b0d2df6a1990a, 0x977841b374b32213, 0xdbfdee9dae212fbe, 0xbf6fa2c3432544ed, 0x8edd662ebc17c85, 0xfc4327bc35f91c8e, 0x50086068c713b33d, 0x53687bf80662eef, 0x5999fdb36af93bca, 0x44dfd30bd6e47b4a, 0xbde429d782f5f133, 0x4a2b8d9d3308fb80, 0xd2a0f03e3934f139, 0xcfd4ee49d1f158ef, 0x8f4a78a50457d186, 0x9a3625b5b1359477, 0x1b3e6b774e0b5170, 0x1475aee0f3536d3, 0xd67e2e1dd27ea13a, 0x8b32507a94e14ae1, 0xe2607ff49bf5b9dc, 0x3e8e9eb9b8913dd8]

private theorem words097 : absorb097 state097 = absorbed097 := by
  decide +kernel

private def quarter097_1 : Vector UInt64 25 :=
  #v[0x3e4d44661eee2b6a, 0x1bfcb59e89c2dacf, 0xebc07cc03786d9f5, 0xdfb0ce4f435065c, 0x80255af4687dd47d, 0x514b414635a9b1c, 0xe825df18910db1f9, 0x3eec36a5fd337b96, 0x5a11b45f791c84f5, 0x39ccb81789740414, 0x19a148966990571b, 0x41d491be9a8d992d, 0x235621227df1652a, 0x5678374ebaa23074, 0x5aacec26b95baa44, 0x8912554732127b46, 0x99ac98aae749db4d, 0xe95d5b6c1182456, 0x7c2d186b8ede56a6, 0xda47ede33a0a74ff, 0xe35b6c00756ce92b, 0x9fde1b3058dd95f5, 0xdf46c9d5d5724003, 0x62767629daa0f9f3, 0x2cec6719a808ab8a]

private theorem rounds097_0 : sixRounds 0 (by decide) absorbed097 = quarter097_1 := by
  decide +kernel

private def quarter097_2 : Vector UInt64 25 :=
  #v[0x8ff8681bec087eb7, 0xdd51230d6caeb0ec, 0xd58f060faf2b86dd, 0x2aadc2dd16da1b66, 0x6fc56cb9633bd455, 0x8f291de326040ba6, 0x6f9ac5288f36480b, 0xd71d2f60007e27c8, 0x89b9c66d10d298e4, 0x6367488034a056ca, 0xd6bd8d2752ea4980, 0xd045ac164bdc3d5e, 0x57c3bb9b4c157b5a, 0x1fa50b10073bc523, 0xd69f9868ff35b8ab, 0x9b8a2a6ff2aa1504, 0xc71889429550e7d1, 0x896a163e7ab18af0, 0x4098a8b6e75f1bbe, 0xd14e84c13c6e4622, 0xd1c99daf1f8fbbc3, 0x834dd2328e16d1a1, 0x20cb57193055bcdd, 0x560247a81fcc0ac9, 0x1f97f74a9516f0b4]

private theorem rounds097_1 : sixRounds 6 (by decide) quarter097_1 = quarter097_2 := by
  decide +kernel

private def quarter097_3 : Vector UInt64 25 :=
  #v[0x3f0ad5ed93f97e6f, 0xbd51081cc09086e4, 0x7c77b270a9f294e, 0x19e652ac90187303, 0x82e47c3f5646fc28, 0x1928e5bab8e04758, 0x1a4c08a4a0f8b4c3, 0x18ece87cd6df9cfb, 0x5b03a9371fabade4, 0x44c9b23db0ac23e7, 0xb373d2f3762f0a93, 0xbf0522c7dfe1c690, 0x9be6e2de5ca893b6, 0xbca4aa02e555bfdb, 0x75c74120b0d2498c, 0xc4dbb78712b53d74, 0x976a2ccf356f1803, 0x31a15b373e86cbb4, 0x904389387a1869f, 0x4c026f6c6bbb2cab, 0x23928bb7be239962, 0xd782fc1ea5da66ea, 0x831fbe003ffdaa97, 0x5517ab39f94c743c, 0xf7ab001b9222eb7e]

private theorem rounds097_2 : sixRounds 12 (by decide) quarter097_2 = quarter097_3 := by
  decide +kernel

private theorem rounds097_3 : sixRounds 18 (by decide) quarter097_3 = state098 := by
  decide +kernel

private theorem perm097 : KECCAK.f1600 absorbed097 = state098 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds097_0, rounds097_1, rounds097_2, rounds097_3]
  rfl

theorem block097 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes097 ++ tail) state097 =
      KECCAK.Bytes.run 0 tail state098 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes097 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb097 ws)) := by
    rfl
  exact (step state097).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words097).trans perm097))

private def absorb098 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3 0x91)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x81 0x90 0x0 0x60 0x16 0x89 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x40 0x60 0x52 0x20 0x60 0x3 0x60 0x52)) 5 (by decide) (UInt64.ofBytes 0x16 0xff 0x60 0x90 0x89 0x54 0x20 0x90)) 6 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x57 0x1b 0x34 0x61 0x15)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x80 0x80 0x1 0x4 0x60 0x52 0x81 0x0)) 12 (by decide) (UInt64.ofBytes 0x52 0x82 0x3 0x81 0x82 0x1 0x20 0x60)) 13 (by decide) (UInt64.ofBytes 0x80 0x1 0x20 0x60 0x52 0x81 0x25 0x60)) 14 (by decide) (UInt64.ofBytes 0x60 0x39 0x91 0x25 0x60 0xc5 0x59 0x61)) 15 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x40)) 16 (by decide) (UInt64.ofBytes 0x31 0x61 0x5b 0xfd 0x90 0x3 0x91 0x80))

private def absorbed098 : Vector UInt64 25 :=
  #v[0x871de4222352ec56, 0x56ee497e56d08696, 0xad1da83948b3ff6d, 0x4481450d10bc1b7, 0xdc602bf9b2e3cd8d, 0x8656f4761e0b2f4a, 0x507545197712edc, 0xd56db536628dab6a, 0x13a816616ca14268, 0x666acdd860c8de0b, 0x2c5a58c29ec927f5, 0xc20b74a014dd6af, 0x1e79ebc17067801b, 0x5484662b24cbc12c, 0x73c89f6fe1cde836, 0x71818c11f1f6593b, 0xf2d5e6e6b1287953, 0xc94036a6f164a651, 0x66064eb1dff2c330, 0xec99da9028c47070, 0xd86439188f0931ef, 0xe99562adf337033d, 0x258147b62916d1a0, 0xb1e9b145e09886fd, 0xb1f312e040c9e0cc]

private theorem words098 : absorb098 state098 = absorbed098 := by
  decide +kernel

private def quarter098_1 : Vector UInt64 25 :=
  #v[0xa2ec5f6e142e7fb, 0x56f4d023a991e1cc, 0x1b743efe5a35eb07, 0x4238d13cd36d1d38, 0xcd1cb2a44e9470ec, 0x55aae424e045fe73, 0xfe4b56e7e0784043, 0xa4fb43fb2e3a9898, 0x14bc9c5984f43ce5, 0x14673b357f224937, 0x8de8aecabd51399f, 0xce8273bc63f44c03, 0x2f9fa225cc897cd4, 0x35e09734614aa3d1, 0x18ada497942b421b, 0xed474c30ec45dc62, 0x9894216a2d9e2292, 0x1accaf174c015df7, 0x99e1306c30b2859a, 0x2c159658bca6dfbe, 0xf09819b72fd2a25d, 0xe101ffdab0379d65, 0x5e8070e40404dfd4, 0x48b0f578bb95f45f, 0xe3e20a56c0712da2]

private theorem rounds098_0 : sixRounds 0 (by decide) absorbed098 = quarter098_1 := by
  decide +kernel

private def quarter098_2 : Vector UInt64 25 :=
  #v[0x50b17ec89098840b, 0xb8c92824ec2297c9, 0x1ef11bf509f0f19a, 0xb1a37dac37092ed9, 0x31f748f7dd2c6f07, 0x61511987d2dec91a, 0x1e7478a1e8ecf5b2, 0x9493c9cbba1eb1ff, 0xb7151ea4f6ee7cf2, 0xbe6b85a1ffe4fdf, 0xbb4a1bd76c0ef227, 0x2d12a3a286fc6442, 0x6e262e8e7b8c48e1, 0x99f120aec786ad73, 0xe52984c11a2a87dc, 0x40d91f7e129ae4b, 0xfbfa70e685b76081, 0xc5dc77275ae2c9c8, 0x60411a30a7408841, 0x7170c2cccb1d7edb, 0xc23b85f7445efd1e, 0x5e6c95e105761c6f, 0xaf8a3154d66ea8ba, 0x96b8390b733b6e54, 0xad76ed41e08b6a0c]

private theorem rounds098_1 : sixRounds 6 (by decide) quarter098_1 = quarter098_2 := by
  decide +kernel

private def quarter098_3 : Vector UInt64 25 :=
  #v[0x6ac665b21d7ce301, 0x6f5c0e35a71c1fa1, 0xe757203407fbbeee, 0x8568e3371376fa3d, 0x800f6506032af48d, 0xbc47abc2160fce96, 0x3787e1a8d9f7cf36, 0x24763391cdb20eb0, 0x14efe7c3e41c13f3, 0x2d97dd72116753a3, 0x37880520a98a17f0, 0x5742cdf15c24fb8f, 0x486d82bc83e7b049, 0xb4dd5509ec43c69c, 0xc87937ab245fbff9, 0x9178dc09bec6e912, 0xdb20fa204bb3e64a, 0x1e32fd85d167289c, 0x8d552a72ed9fb210, 0x5d914b2424ccda, 0x53a9636ce4f3fdc9, 0x44295a980e98badf, 0xe1935748baabb010, 0xbd62245a5d1cb1f5, 0x8f082f7a93a83b1c]

private theorem rounds098_2 : sixRounds 12 (by decide) quarter098_2 = quarter098_3 := by
  decide +kernel

private theorem rounds098_3 : sixRounds 18 (by decide) quarter098_3 = state099 := by
  decide +kernel

private theorem perm098 : KECCAK.f1600 absorbed098 = state099 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds098_0, rounds098_1, rounds098_2, rounds098_3]
  rfl

theorem block098 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes098 ++ tail) state098 =
      KECCAK.Bytes.run 0 tail state099 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes098 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb098 ws)) := by
    rfl
  exact (step state098).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words098).trans perm098))

private def absorb099 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x8b 0x8b 0x8b 0x8b 0x8b 0x8b 0x8b 0xd0)) 1 (by decide) (UInt64.ofBytes 0x7f 0x5b 0x56 0x25 0x46 0x61 0x8b 0x8b)) 2 (by decide) (UInt64.ofBytes 0x7f 0x1f 0xa 0x5 0xbb 0x22 0x42 0x42)) 3 (by decide) (UInt64.ofBytes 0x26 0x1f 0x67 0xa5 0x32 0x72 0x1 0x14)) 4 (by decide) (UInt64.ofBytes 0xd5 0x4b 0x50 0xf 0x42 0xd3 0xa2 0x80)) 5 (by decide) (UInt64.ofBytes 0x8a 0x19 0x53 0x5c 0x3 0x3 0xcf 0x65)) 6 (by decide) (UInt64.ofBytes 0x1 0x74 0x54 0x1 0x60 0x5b 0x56 0x81)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0xda 0x34 0x61 0x15 0x16)) 11 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x81 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x24 0x60 0x10 0x60 0x52 0x1 0x82 0x4))

private def absorbed099 : Vector UInt64 25 :=
  #v[0xd1dce4278e2516f9, 0x21398e3f7b0994e5, 0x47d4c84754040b6a, 0x87ad3113625938b2, 0x530b40b3af16be59, 0x1d7e8e75356155e2, 0xba923296b9daa69c, 0xecc7a1db61b65bcd, 0xdf939108a759008c, 0x688e4610da1ec5f9, 0xfa9be78d50dbcb0, 0xe9d2851a4c8ad4ec, 0x88469f9a87ddc06b, 0x513db6b1ea57be65, 0xdf8008cf884353c7, 0x6c063279ef383843, 0xd821aa20bead5229, 0x60f640fd7b97f3a8, 0x1b34a46b0bc7a80a, 0x30ad4841ce9698b0, 0xe0ff1a47e54bff31, 0xb92184e74d0b9390, 0x62b1fba75bd3f77d, 0x128006f1cc7521c8, 0x3b776f00a0454229]

private theorem words099 : absorb099 state099 = absorbed099 := by
  decide +kernel

private def quarter099_1 : Vector UInt64 25 :=
  #v[0x49e902776d53c4f6, 0xa17b2fb3055bfca9, 0xab85bb67354e4896, 0x62c08a77a4c8b102, 0xcbbd9626884b86d, 0x66d768548b323010, 0xabbc6ab86f92000b, 0x32b5f77d0c79c740, 0x416b5f8fd55cc225, 0xcb88df4b5a3a71e7, 0xee8697a0db96a31, 0x791a407ab45c1a6d, 0x950d388a906415a7, 0x1342835c17b8c32f, 0x7cfb4ab55e49551c, 0x8db2c8b0be242de0, 0xd9168a938864838, 0x3f827b5a444773e8, 0x73247dd20865e3f8, 0x2a5fad480b8245c5, 0xe104ffde1fb2ffbb, 0x18df0f67eec395de, 0x98a0f5dccdb22b9c, 0x36c54fb076f04f85, 0x627753060d7cf1a]

private theorem rounds099_0 : sixRounds 0 (by decide) absorbed099 = quarter099_1 := by
  decide +kernel

private def quarter099_2 : Vector UInt64 25 :=
  #v[0xeef20136f7686758, 0x32e974c3036c5952, 0xa6028eb077b5d995, 0x2201d45ac98bb3ca, 0xfc6072f88c33a2e4, 0xc6e8ecfd8c06ca56, 0x5c6164045f08d926, 0xa278ce0f6bdaeb54, 0xffba03dddb29c972, 0x41488c4b81e89061, 0xe6dcab3945faea56, 0x9d4eb88a7824e9af, 0x5e1f4cd8153dfd83, 0x86da0cd86a52d12, 0xd9cd99541a7033, 0xeec21a4624f510cd, 0x6129d8ac0ae64363, 0xc6d51455a70d096b, 0x2da8e27d4aba0bd0, 0x777b1d9195f6672d, 0xf76125d9d8429589, 0xdb34bd20f76217e, 0xf31d70faabb96a3e, 0xbb87a4a1f16c3cc8, 0xff7dae63d1619805]

private theorem rounds099_1 : sixRounds 6 (by decide) quarter099_1 = quarter099_2 := by
  decide +kernel

private def quarter099_3 : Vector UInt64 25 :=
  #v[0xd5656a99822ec62f, 0x10bfe20368d4c2aa, 0xe0f60f6e976f7ace, 0x76b80a26c6cc1858, 0xd34a13191d758597, 0x470def266e710511, 0x8095869527535377, 0xe1b73183f08189c3, 0xa8d6754a68bebc37, 0x23c5a81bdea43fb, 0x3144a54fbdf9a9a5, 0xf592f9d9ae379e93, 0x295141061361578f, 0x94f5879625d21c8d, 0x977da34e82bc9c82, 0x902e98b2fd58897d, 0x5174c7b26999a422, 0x5fbc7e1d7d7e3172, 0xa4731c08cb8f7f15, 0x42c8dcc7d7c6bb29, 0x418e35e848afbab3, 0x754918dbb2f07c50, 0x683211cb49eb93da, 0xbf2c997eccdec995, 0x3771f869474fc92e]

private theorem rounds099_2 : sixRounds 12 (by decide) quarter099_2 = quarter099_3 := by
  decide +kernel

private theorem rounds099_3 : sixRounds 18 (by decide) quarter099_3 = state100 := by
  decide +kernel

private theorem perm099 : KECCAK.f1600 absorbed099 = state100 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds099_0, rounds099_1, rounds099_2, rounds099_3]
  rfl

theorem block099 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes099 ++ tail) state099 =
      KECCAK.Bytes.run 0 tail state100 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes099 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb099 ws)) := by
    rfl
  exact (step state099).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words099).trans perm099))

private def absorb100 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x73 0x75 0x61 0x50 0x7f 0x52 0x1 0x82)) 1 (by decide) (UInt64.ofBytes 0x61 0x70 0x20 0x3a 0x65 0x6c 0x62 0x61)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x64 0x65 0x73 0x75)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x1 0x82 0x44 0x60 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x60 0x3 0x90 0x81 0x90 0x51 0x90 0x52)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x5b 0xfd 0x90 0x1 0x64)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x81 0x90 0x0 0x60 0x16 0x87 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x40 0x60 0x52 0x20 0x60 0x3 0x60 0x52)) 11 (by decide) (UInt64.ofBytes 0x16 0xff 0x60 0x90 0x87 0x54 0x20 0x90)) 12 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x57 0x5b 0x35 0x61 0x15)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed100 : Vector UInt64 25 :=
  #v[0x40fb7d2761318fc2, 0xa61dbbfa1bb5b3b2, 0x1026443c50bdb75, 0xbe589faa78a769f9, 0x6da38c2b68da33a1, 0x29f0ed7658e9f6c3, 0xec8284a3a81418f9, 0x1146072fd5c8a2f4, 0x61f1115c69059b52, 0x36b46d7f256b1e50, 0xc77c9a4caaeb13e0, 0x40c125c0b8740de1, 0xc2aefa7b9bef3bf4, 0x2c029a97507da09c, 0x2078f2cc960bf573, 0x95e3d135af255aa6, 0xf28b42f71d29d396, 0x5788c342575ccc79, 0x67b4e26c37093495, 0x10154978cf534f21, 0xbf931bf952af8698, 0x5adb53c547c7f18a, 0x903fca4b70db36d8, 0x35630767f90bf514, 0x9e2533ee0368a74a]

private theorem words100 : absorb100 state100 = absorbed100 := by
  decide +kernel

private def quarter100_1 : Vector UInt64 25 :=
  #v[0x81e602d5147ceb7c, 0x22b498b8347d5715, 0x27da70aef3b4e4bb, 0x2b9ec31fa03155af, 0x98bab154d2c6505d, 0xb9f823ecd5a259b, 0x3319243782fd430e, 0xe0edfb8c471627a2, 0xa34306859773c46f, 0x65b951b012a52f03, 0xee5807d6aa9070f7, 0x2cff013ccdf2dda6, 0x56d5ea3e9c6a1b8a, 0x2224ee04ca46ecf3, 0xa8f23a9328c1aca1, 0x616d89267ebd240b, 0xc840cb52f13fd118, 0xfc12824f4d8b304e, 0x7c3468fed81e85ae, 0xd18a3116794bdf04, 0x9635b44f81e118ec, 0xa51bfc233198e8d2, 0x37ece95c0e95c09c, 0x216c909d63a2e477, 0xb3563fa98b509074]

private theorem rounds100_0 : sixRounds 0 (by decide) absorbed100 = quarter100_1 := by
  decide +kernel

private def quarter100_2 : Vector UInt64 25 :=
  #v[0xcb48ca72e04b2446, 0x93cc09f12c79f91b, 0xf2f305dcbf6310f8, 0x9bbb4b2c92182be, 0xe2aa3464bf18d707, 0x4dd31816cf628125, 0xf3670da22f232f8d, 0x9125def61f70ffc2, 0x71e76522c026b5bf, 0xca800b4ba80d4e0c, 0xe9ecbdaa8884f756, 0xde235441f7d7d845, 0x548572aa65c4a9d1, 0xd7b810b0cac9acfa, 0xfc37166ab8eb0a4a, 0xb1746b6b02b6083d, 0x4386c86f887ed3f9, 0x787c5697578bac34, 0x9c281611fe14df55, 0xf9dcc0fa6e817726, 0xa9f94beb8f0bcf37, 0x4d79253e11b0f331, 0xe66c42ad09f66c86, 0x484f1086508d2ebf, 0x705f635825c0d887]

private theorem rounds100_1 : sixRounds 6 (by decide) quarter100_1 = quarter100_2 := by
  decide +kernel

private def quarter100_3 : Vector UInt64 25 :=
  #v[0x29ecce4253fc3034, 0xfaa06596fb8f5c6, 0x57279f6ba1ddd754, 0x760c9724decb7148, 0xd075e204286c59fe, 0x3d02e36d98a96718, 0x4709eb4c20b2bc4d, 0x5b599621d01d79d, 0x2f135cf47fd8636b, 0xb5746859d5c7e6c4, 0xe4238fe56ff3e2a0, 0xc49ba3b6d218b7a0, 0x184ff40428f3fa25, 0x984aa4ee2559b366, 0xf69573ba1d693059, 0x8a28fb83a9fa5de9, 0x2c34d30cb7827ec, 0x5145ca076988a23d, 0x900aa46679452a0a, 0xa43a70a51590559d, 0x4286e96bf54eb6e2, 0x4b58a46d86476415, 0xe5dd849d03e16825, 0xa9c3e33167046e60, 0x2a875a7624e41df3]

private theorem rounds100_2 : sixRounds 12 (by decide) quarter100_2 = quarter100_3 := by
  decide +kernel

private theorem rounds100_3 : sixRounds 18 (by decide) quarter100_3 = state101 := by
  decide +kernel

private theorem perm100 : KECCAK.f1600 absorbed100 = state101 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds100_0, rounds100_1, rounds100_2, rounds100_3]
  rfl

theorem block100 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes100 ++ tail) state100 =
      KECCAK.Bytes.run 0 tail state101 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes100 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb100 ws)) := by
    rfl
  exact (step state100).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words100).trans perm100))

private def absorb101 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x80 0x80 0x1 0x4 0x60 0x52 0x81 0x0)) 1 (by decide) (UInt64.ofBytes 0x52 0x82 0x3 0x81 0x82 0x1 0x20 0x60)) 2 (by decide) (UInt64.ofBytes 0x80 0x1 0x20 0x60 0x52 0x81 0x25 0x60)) 3 (by decide) (UInt64.ofBytes 0x60 0x39 0x91 0x25 0x60 0xc5 0x59 0x61)) 4 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x40)) 5 (by decide) (UInt64.ofBytes 0xff 0x73 0x5b 0xfd 0x90 0x3 0x91 0x80)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x90 0x0 0x60 0x16 0x87 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x60 0x52 0x20 0x60 0x3 0x60 0x52 0x81)) 10 (by decide) (UInt64.ofBytes 0xff 0x60 0x90 0x87 0x54 0x20 0x90 0x40)) 11 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0xdc 0x35 0x61 0x15 0x16)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x80 0x1 0x4 0x60 0x52 0x81 0x0 0x0))

private def absorbed101 : Vector UInt64 25 :=
  #v[0xc1538d524607d0e9, 0x11853fb7dfaaf6b6, 0xae13871ac207ec0d, 0x71e043b23cbc4ded, 0x48b0fbb271cdc068, 0x693ebeb125b49217, 0x688ae7a77616491f, 0x6497f745fd986b02, 0x96d7f4d7b93b2775, 0x18ca8866b88a3aec, 0xda87f36508c6a98f, 0xcb58a8b623d650b8, 0x78737757260906c7, 0xdff5fccda350b286, 0x5762f7b44e987e30, 0x32b6a33357f7e60c, 0x9e71501b30cd57c8, 0x453907fdf497b2dc, 0xba3da37ad93652d, 0x946b26cf20bc9974, 0x4fe9626529c9d6a1, 0xf8f93f4cb52596af, 0x505f3c531420da86, 0xfef4cde22fac4710, 0x31794d466996143e]

private theorem words101 : absorb101 state101 = absorbed101 := by
  decide +kernel

private def quarter101_1 : Vector UInt64 25 :=
  #v[0x3b6b1d12c8965394, 0x911c8d3fcc28f3a4, 0xe4c879d5886d1bcc, 0x84299d811b58c42, 0xa054518e483616cb, 0xe4dcf0379992ab2e, 0x17398cd72dadc71, 0x1e2815412550d121, 0x350481f0d3055d2c, 0xb95803799e03a7c9, 0x2f98dafc2e793267, 0x104b1c0abe012108, 0x7e501b792244b72f, 0x405d118c642b2f08, 0x4bf63ff47f8ff702, 0x9500cc57b3138f44, 0x98d090f1584f8f8b, 0x2b6760d81344a45c, 0xec0e0e9a9c29e476, 0x52338924deb3d8d2, 0xa48b438ec6da1892, 0x45c3e719b0e979ed, 0x8344e1ffa156ae20, 0xaedd92904efd6531, 0x6361d6826d079c2e]

private theorem rounds101_0 : sixRounds 0 (by decide) absorbed101 = quarter101_1 := by
  decide +kernel

private def quarter101_2 : Vector UInt64 25 :=
  #v[0x2c32b5d662dd9343, 0x932f91ce6dfe073b, 0xaa0dd16ae37ca021, 0x26cc6033aee63910, 0xe395ad9b9bb327da, 0x96aa096c08660f55, 0x2cb09bcc0e2f837d, 0xf1091cdfa12ce939, 0x1558b73fd2ea3df4, 0xe1f7736441814901, 0x14be4673b56bd22a, 0x69d21b3d70b0762f, 0xc67fd28d02ccf767, 0x2fd345d322ce2798, 0x8b19eeb3b0d9d89, 0x79165adc1b343870, 0x1122bb864ba55ead, 0x93d05b097aa8e617, 0x446665cd416f0850, 0x9bbf375fe2a70411, 0x2cf2a6baae5d237e, 0x5f80fc73f04c8f6c, 0x5ff5dcdf2300c506, 0x12897db740158d59, 0x65a4f69e8b8bfb53]

private theorem rounds101_1 : sixRounds 6 (by decide) quarter101_1 = quarter101_2 := by
  decide +kernel

private def quarter101_3 : Vector UInt64 25 :=
  #v[0xcd653ef8333335a9, 0xa7c0305d4f6c691d, 0x64599a5b0f5b5660, 0x520775d194b75e8d, 0x68264a3d12484860, 0x46c7e2eb97dc04a2, 0xf536a1cefad900b2, 0x8a73f9eb916d3781, 0xf164db63c26261c8, 0x57323be31d16238a, 0x1a458b08581348e4, 0x748559be4775adf8, 0xbe174599902e195a, 0x8580c6320f772038, 0xf0d0200e4244c302, 0xe442d057b4d559b0, 0x3966acebe56677fa, 0x3021753bf28fdd04, 0x5b6c04d91a6cc208, 0x3d8877a2d11997eb, 0xe83ccf663d75eb41, 0x9d80e5ce2cfbc5b8, 0x828d3a4f5e21b2dd, 0x80f9fcd7478e2c0b, 0xe4fe32a129f1458d]

private theorem rounds101_2 : sixRounds 12 (by decide) quarter101_2 = quarter101_3 := by
  decide +kernel

private theorem rounds101_3 : sixRounds 18 (by decide) quarter101_3 = state102 := by
  decide +kernel

private theorem perm101 : KECCAK.f1600 absorbed101 = state102 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds101_0, rounds101_1, rounds101_2, rounds101_3]
  rfl

theorem block101 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes101 ++ tail) state101 =
      KECCAK.Bytes.run 0 tail state102 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes101 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb101 ws)) := by
    rfl
  exact (step state101).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words101).trans perm101))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
