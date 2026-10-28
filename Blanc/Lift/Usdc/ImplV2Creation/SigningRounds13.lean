import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb078 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x1 0x74)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x90 0x17 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0xa0 0x85 0x69 0x7f 0x51 0x40 0x60 0x55)) 4 (by decide) (UInt64.ofBytes 0xd3 0x2 0x66 0xe6 0x68 0xa1 0x10 0x22)) 5 (by decide) (UInt64.ofBytes 0x2b 0xf9 0x70 0xe 0xdb 0xb6 0x5c 0x23)) 6 (by decide) (UInt64.ofBytes 0x3d 0xf 0x3c 0xa3 0x76 0xd3 0xa4 0x3b)) 7 (by decide) (UInt64.ofBytes 0x0 0x60 0x90 0x25 0xf6 0xbf 0x34 0x94)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0x56 0xa1 0x90)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0xff)) 12 (by decide) (UInt64.ofBytes 0x20 0x90 0x40 0x60 0x52 0x20 0x60 0xd)) 13 (by decide) (UInt64.ofBytes 0x73 0x54 0x0 0x60 0x5b 0x56 0x90 0x54)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x5b 0x56 0x90 0x16 0xff 0xff 0xff 0xff))

private def absorbed078 : Vector UInt64 25 :=
  #v[0xf7f62d0f32f3d122, 0x2377a2ad8e3a242, 0x90621bd777c9cb96, 0xc4622872ab1b33e2, 0xd513fbd7fc4188c5, 0x8360f2d0257236da, 0x376377d7a13bb28, 0x2aaf0f22bac74bf2, 0xee45c065a7e6f02, 0x208a903d772e13fd, 0xa83812822cdea268, 0xfe6d16f159e2e57a, 0x2e7714e71e30ac8f, 0xbd52fa002c878297, 0xe6b3c02cafbd2692, 0x51c43c981bc99b56, 0x77f7ded8fc02842b, 0x19f94a61dd1503bc, 0xbfd3788fa2cc657f, 0x6dd5f99ee064696a, 0xb5a513d52a9707a2, 0xe3e660bcab6c86a5, 0x827873b303a3432b, 0x408cf63660cfb641, 0x5aec56ffb648e8d8]

private theorem words078 : absorb078 state078 = absorbed078 := by
  decide +kernel

private def quarter078_1 : Vector UInt64 25 :=
  #v[0x6c13e6035ed7dfd6, 0xcf926928cac8cd35, 0xebb620d3c7cdb474, 0x4bd3b77797ed5ed1, 0xf17a10440096896e, 0x633d9e9b76b9a6cb, 0x38716a53c998f0fc, 0xe3cf7b923a83aa45, 0x9696c6b1147d78a3, 0x8256d3c77817d0c, 0xcafa02d29e4f9a3d, 0x3fd764bdec225b23, 0x3f08eff1c934627, 0x175aab7b0cb9f145, 0x39280003602ad74d, 0x8fc4b995a06fe6b9, 0xd155b3e3692b06ca, 0x806b283604b5ab75, 0xe38b098a06b9a98b, 0x12e07502136e0432, 0xcd376210f306f38b, 0xc07aa13cf92efb36, 0xaba3554ec8c18d0a, 0x96d84ca3bd3b70ac, 0x2b1b2f0d347253c9]

private theorem rounds078_0 : sixRounds 0 (by decide) absorbed078 = quarter078_1 := by
  decide +kernel

private def quarter078_2 : Vector UInt64 25 :=
  #v[0x49962dcea88c133e, 0x370df88976903f53, 0xf48cb8086d0e40b5, 0x519e7ab3f3b0555b, 0x480f4ae2d3a0f830, 0xd83e17530c6960e3, 0x4fcd388ae94a20b3, 0xa5e5adcdc32ae20c, 0x2fc07a2670bcb0ce, 0x216bfe684426c202, 0x95ff7ffc410102f1, 0x7d66a9b0ac376708, 0xca79bed6b8c9cd36, 0xd8880faea765a507, 0x1cfc73c81481bb98, 0xea06d517c65275c1, 0xa57e7d0fc5980f63, 0xaa9695b058505db9, 0x12181daf6b9f4d9e, 0xbda7a2406c4c4624, 0xdc679ae12c6f1e9b, 0x6d44ef4d49f4ac9c, 0x53d940675ab173d, 0xbb1bf4c9fd14dc, 0x7e23b4d83188ac85]

private theorem rounds078_1 : sixRounds 6 (by decide) quarter078_1 = quarter078_2 := by
  decide +kernel

private def quarter078_3 : Vector UInt64 25 :=
  #v[0xf727fb95ac1cc947, 0x24cbba736983f40c, 0x3a1faf3c9b5fe046, 0x33f4ce710d52f172, 0x2266902219db26fc, 0x627444dc41b1f377, 0x16f3688b04cfb6ad, 0xd0c8152169ba1365, 0xdc9bc3d38e4724f5, 0xc3b12dad22044aac, 0xdac1458ddb4e437e, 0xb373ab39936a7194, 0x285b5f5e7e02bdf1, 0x1f9a7eba894e1ffd, 0x7492e6ede97d21c0, 0x56c516efb3763d1a, 0xd99bf991856d9f72, 0x713d6f0a056eaf8c, 0x4ecd5b80a6cc4824, 0x934b65d383c0c7e6, 0xc62b4b24fb9bd331, 0x87dbfaeaee3fc943, 0xd134f93bcd7f61da, 0xdf1f5a3b2896a9ac, 0xb051a8718250fba8]

private theorem rounds078_2 : sixRounds 12 (by decide) quarter078_2 = quarter078_3 := by
  decide +kernel

private theorem rounds078_3 : sixRounds 18 (by decide) quarter078_3 = state079 := by
  decide +kernel

private theorem perm078 : KECCAK.f1600 absorbed078 = state079 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds078_0, rounds078_1, rounds078_2, rounds078_3]
  rfl

theorem block078 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes078 ++ tail) state078 =
      KECCAK.Bytes.run 0 tail state079 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes078 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb078 ws)) := by
    rfl
  exact (step state078).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words078).trans perm078))

private def absorb079 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x54 0x80 0x5 0x60)) 1 (by decide) (UInt64.ofBytes 0x16 0x85 0x1 0x60 0x2 0x60 0x20 0x60)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0x7f 0x2 0x0 0x1 0x61 0x15)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x90 0x1 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x1f 0x60 0x4 0x93 0x90 0x93 0x16 0x94)) 8 (by decide) (UInt64.ofBytes 0x82 0x2 0x84 0x4 0x90 0x84 0x1 0x81)) 9 (by decide) (UInt64.ofBytes 0x81 0x81 0x52 0x92 0x90 0x1 0x84 0x1)) 10 (by decide) (UInt64.ofBytes 0x80 0x82 0x82 0x1 0x83 0x91 0x92 0x52)) 11 (by decide) (UInt64.ofBytes 0x1f 0x60 0x80 0x57 0x4e 0xf 0x61 0x15)) 12 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x57 0x23 0xf 0x61 0x10)) 13 (by decide) (UInt64.ofBytes 0x91 0x52 0x83 0x2 0x4 0x54 0x83 0x80)) 14 (by decide) (UInt64.ofBytes 0x56 0x4e 0xf 0x61 0x91 0x1 0x20 0x60)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x54 0x1 0x60 0x5b)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed079 : Vector UInt64 25 :=
  #v[0xbc121462924afb80, 0x8568e3fd45bad294, 0xe0fe859bbdf33308, 0x1f4dafd502c7a07e, 0x5f8e6b4fd4af9a65, 0xee2946b91e65e37c, 0x1ce0388bf26a9433, 0xeb0e0645ab08f862, 0xcf2c9030c48a220c, 0x24bab1b07b75b0a0, 0x59030d85916eff59, 0x3d411790996d18b8, 0x62b8bafd18c13c91, 0x2d0ea80d5bfb9e0e, 0xd40d8e4a17169988, 0x919d5b7551d15f5, 0xae658867a2e3362, 0x126ce635309068ca, 0x135d7b585c951cde, 0x2491dc09fcf7fa27, 0x66d377e9ee89d727, 0xfe210b46d164eb55, 0xac9e9fde3c93a502, 0x512f26ff5a3c3a76, 0xc01926ced0bb96a6]

private theorem words079 : absorb079 state079 = absorbed079 := by
  decide +kernel

private def quarter079_1 : Vector UInt64 25 :=
  #v[0x637bb6f8d4697af6, 0x68cf3598e46d4336, 0xc817559b7c00557b, 0x59368cc2db074d52, 0x664b80879620b464, 0xe09bfd19cdb834fa, 0x98f095de2e646292, 0x57cade80245c7c30, 0x9383f246749446ac, 0x566b933ca1baf67a, 0xb7a35e1ceaf90c61, 0x7db103d618269786, 0xee040847ab3401aa, 0x3dd532a4d77f6c01, 0x749f7788e8e2b772, 0x16d5dec0a7e8f2f6, 0x3f0b0d0e9f3a0634, 0x9e1c730a5a2c6f2a, 0x83ec556daa27fdd1, 0xa818bb1db287787c, 0x88bbf8b98696d742, 0x4411a4f6bb1c0ba, 0x7813bad60275d192, 0x6396b16db37eee6e, 0x2265d7aa1ac3ccf0]

private theorem rounds079_0 : sixRounds 0 (by decide) absorbed079 = quarter079_1 := by
  decide +kernel

private def quarter079_2 : Vector UInt64 25 :=
  #v[0x3579725ba6f23c90, 0x41e8c6a5c450005c, 0xa4c44b817a4064ed, 0x4a86140e3b4455dc, 0x2f5e4bc34a780989, 0xfeaeaf46f5582434, 0xda2ab6d4c6ef8f27, 0xe3aba0185fee2d2a, 0xfd7a31d425733208, 0x5f86d93f514119b, 0xc0c3b89aa2600fdd, 0xddb00afca92bd75a, 0x52d1217173e37b04, 0xf6dd0a3d2df274c0, 0x3f89bd62dd7dc21e, 0x36f38122f598d7e7, 0x94d7e887d12fdae1, 0xca3e4fc477e9cdd0, 0x4e4a489865f48644, 0x7e46eab8b90d553c, 0x77bf8ba7965e5538, 0xf7f9589a044777a7, 0xa8f1203899d6f80d, 0x7511569d94be5152, 0x9a7fde22f7051a7a]

private theorem rounds079_1 : sixRounds 6 (by decide) quarter079_1 = quarter079_2 := by
  decide +kernel

private def quarter079_3 : Vector UInt64 25 :=
  #v[0x76dc703856b0e7c1, 0x8d6421b9d82265f7, 0xbcd2da2bae4f5085, 0x54972ca87091666a, 0x761a84db5d34fd3, 0x161f4e8b58488d0c, 0x3f30b80b92c1e731, 0x8e8a495f050141f3, 0xb6ecb7af8e051c6b, 0x73640edc32ff0016, 0xa81608fc738603ab, 0x6b92f77d3a6efffc, 0x3d7d24c7089cf4cf, 0x1e55019a01a5a90f, 0x5e4317e1f9967930, 0xb4740adefa944ae, 0x34c36d4642ef83ec, 0x42089844e7b3ffcd, 0xb892a784270a984b, 0x3c3e0b78a2de2073, 0xfde508bdd8a5e5e8, 0xb537e1aea2e1b81d, 0xeb17ce266869bcf, 0x58f000c1f29b4fec, 0xb49bdafbf140211a]

private theorem rounds079_2 : sixRounds 12 (by decide) quarter079_2 = quarter079_3 := by
  decide +kernel

private theorem rounds079_3 : sixRounds 18 (by decide) quarter079_3 = state080 := by
  decide +kernel

private theorem perm079 : KECCAK.f1600 absorbed079 = state080 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds079_0, rounds079_1, rounds079_2, rounds079_3]
  rfl

theorem block079 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes079 ++ tail) state079 =
      KECCAK.Bytes.run 0 tail state080 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes079 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb079 ws)) := by
    rfl
  exact (step state079).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words079).trans perm079))

private def absorb080 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x7c 0x7c 0x7f 0x5b 0x56 0x81 0x16 0xff)) 2 (by decide) (UInt64.ofBytes 0x9e 0xf4 0x43 0x87 0xa1 0x67 0xdb 0x6c)) 3 (by decide) (UInt64.ofBytes 0xed 0x52 0xd 0xf5 0x35 0x9b 0xfa 0xc6)) 4 (by decide) (UInt64.ofBytes 0x3b 0xe1 0x92 0xc5 0x4c 0xed 0xcb 0x5)) 5 (by decide) (UInt64.ofBytes 0x56 0x81 0x67 0x22 0x1a 0x1c 0x50 0x44)) 6 (by decide) (UInt64.ofBytes 0x74 0x90 0x0 0x60 0x54 0x1 0x60 0x5b)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x1)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x60 0x4 0x90 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x60 0x57 0xc3 0x2a 0x61 0x15 0x16 0xff)) 11 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80 0x40)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x60 0x10 0x60 0x52 0x1 0x82 0x4 0x60))

private def absorbed080 : Vector UInt64 25 :=
  #v[0xe12e953c30d349d7, 0x7ce40faad17b5d23, 0xa3c7d21d5bf6ee59, 0x4d23e45c90918991, 0x36c44477da72f2ae, 0x87e53257895b1a18, 0xf078d09a9d1c1ee5, 0xdf39a400cff4d066, 0x926b35bdb1789b20, 0xb5013259f80dce9, 0xa6071bc702579cd9, 0xeab1f2642d75a92e, 0x6b65c7a0156854da, 0x4afcf0b1cb6dd491, 0xaaf7388def1179a8, 0xcccd2eb8d5c4a6b2, 0xf1c39f28d8d9096c, 0x1fbc4114a5f14487, 0xfeb7566c82fed514, 0xcb690365ce9509b1, 0x6a7d87f51ffd3b95, 0xd2d5e24852e9291b, 0xdc6678faf88335b1, 0x2f97076e5e7b846d, 0xf23c12335e4ff16c]

private theorem words080 : absorb080 state080 = absorbed080 := by
  decide +kernel

private def quarter080_1 : Vector UInt64 25 :=
  #v[0x8525d391f2827727, 0x7d0aaaad71e02336, 0xb0f1fc2e96dc72d8, 0x62c50f0f45217f97, 0xa65ac4529c950091, 0xa1fd1cb14e2bb078, 0x3127b8b339418f3f, 0x4f7ad02db505f8d6, 0xd323b20d2dc71ba0, 0xac7c5f4ab81304cf, 0x2fa5bdcc18f4fae5, 0xd42211869409799f, 0xe3e360d8ff0cf471, 0x59ba15f1700d019d, 0x76067d15eaf4350, 0x29ce266200e10a59, 0xf4d268eed4f28e25, 0x472abb51ab52f060, 0x431a3b879f56fa50, 0xd114b2f819a7e58e, 0xbcf469699109e1fd, 0xc417d69c6edb97aa, 0xc899add4d5fd226e, 0xe5f44e25a99126df, 0xa57239bca747e648]

private theorem rounds080_0 : sixRounds 0 (by decide) absorbed080 = quarter080_1 := by
  decide +kernel

private def quarter080_2 : Vector UInt64 25 :=
  #v[0x151fb4ffcfe4ede3, 0x42c984b6b5798e2e, 0x78d7a8b92513c062, 0x44b88228926a5ad8, 0xca56e811b67aec1e, 0x64537aa0eeeec86a, 0x634e94e6283e2f4, 0xe54de0df36e844e, 0x6914dd040ff35f83, 0xeced48194d8e8126, 0xf092923a1abd7632, 0x3614d94a32f17657, 0xf4cb710696c4fc7c, 0x6baa02f03e62a240, 0x6ba81b9d3badaed9, 0xca300664d3e33ad2, 0xcbf784d05191032a, 0xe499972f199868ae, 0x7cff277b23bdaff0, 0xc6f7eefc28379800, 0x4ac7bce0a5408373, 0x67de6152a790d04c, 0x604b5cfa2f37e28a, 0x39763bdffa7f0989, 0x98516322c454ffe3]

private theorem rounds080_1 : sixRounds 6 (by decide) quarter080_1 = quarter080_2 := by
  decide +kernel

private def quarter080_3 : Vector UInt64 25 :=
  #v[0x85c02b5d44651449, 0x587417f002da7122, 0x94971004bb6f2514, 0x757cb472731e15e5, 0x96c647d4a4382383, 0x72a32fac398f9843, 0x15078ea39bbd3454, 0x4dd1cde59f4666f0, 0x4856d0963b8119e7, 0x2b86659891f3fc93, 0x80d6eb4da1f456bd, 0xdf1d191ffd4a0ca0, 0x5c949f15e6fa4e54, 0x61dc6c521858267b, 0xb3d8bf1d6398f06f, 0x7c51efa3e08c0bb1, 0xa1d3eef7cee48880, 0xef03bfa2338848f3, 0xc86ac2b7e70595f7, 0x86965771c6ba6aae, 0x136593506cb3ee04, 0xbba64d7fe459d11b, 0x376d1952f38d228c, 0x493a225984a097e5, 0x3d73756291789d4f]

private theorem rounds080_2 : sixRounds 12 (by decide) quarter080_2 = quarter080_3 := by
  decide +kernel

private theorem rounds080_3 : sixRounds 18 (by decide) quarter080_3 = state081 := by
  decide +kernel

private theorem perm080 : KECCAK.f1600 absorbed080 = state081 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds080_0, rounds080_1, rounds080_2, rounds080_3]
  rfl

theorem block080 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes080 ++ tail) state080 =
      KECCAK.Bytes.run 0 tail state081 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes080 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb080 ws)) := by
    rfl
  exact (step state080).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words080).trans perm080))

private def absorb081 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x75 0x61 0x50 0x7f 0x52 0x1 0x82 0x24)) 1 (by decide) (UInt64.ofBytes 0x70 0x20 0x3a 0x65 0x6c 0x62 0x61 0x73)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x64 0x65 0x73 0x75 0x61)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x82 0x44 0x60 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x3 0x90 0x81 0x90 0x51 0x90 0x52 0x1)) 6 (by decide) (UInt64.ofBytes 0x60 0x33 0x5b 0xfd 0x90 0x1 0x64 0x60)) 7 (by decide) (UInt64.ofBytes 0x20 0x60 0x3 0x60 0x52 0x81 0x81 0x0)) 8 (by decide) (UInt64.ofBytes 0xff 0x60 0x54 0x20 0x90 0x40 0x60 0x52)) 9 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x2c 0x2b 0x61 0x15 0x16)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x80 0x1 0x4 0x60 0x52 0x81 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x82 0x3 0x81 0x82 0x1 0x20 0x60 0x80)) 16 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x25 0x60 0x52))

private def absorbed081 : Vector UInt64 25 :=
  #v[0x41a9abe59537d625, 0xfd5f16af20f6596a, 0x8f29e4b85c2242b9, 0x3b87396e986872c5, 0x13cbe5d08f467a9f, 0x368675abb41636c1, 0xd327b838acf99004, 0x1833b04e341a1088, 0xa793fc838d3c0754, 0xe1bef2687ebdada2, 0x3ca67e2375e6482, 0x7bb6396112ee208c, 0x522bc665ea134b21, 0xd5a278843f7ede7e, 0x95a3d7b0da071273, 0xe7da00b5a7993027, 0xa59ec55365df0b88, 0xe92e34d45b06ddf1, 0x65e1777129f3aac, 0xcf83ac62f96b55bd, 0x97a3a6f2dee04353, 0x1eef63784d947076, 0x4b606b840e2ad36d, 0x354bae70232e196d, 0x66da3d6ea7432b5a]

private theorem words081 : absorb081 state081 = absorbed081 := by
  decide +kernel

private def quarter081_1 : Vector UInt64 25 :=
  #v[0x1406d062cbca173a, 0x2c1973213f1a4f03, 0xdcd6c36fe2fff801, 0xa6729bb215f1b4e7, 0x3d3ac1938a9a55c8, 0xdaadaf958f142e81, 0xca147d28035bf7f, 0x6c8ec39a87e0240e, 0x9d73f8083d0b544b, 0xc257f6e80ed503e9, 0x21a0bc71a8eb569c, 0x75ec48da3289dcda, 0x2736e36a86c531d7, 0x8692e0b140bfd94e, 0x7fb2e2a2d2ebbfac, 0x388c5463217d91d8, 0xc2e820707fdafb70, 0x7fb13cb2377de90d, 0xe561c3a2707e1d7f, 0xd9aa1b4847baae87, 0x6e5601d650ac60e7, 0x152a7c575b3a9319, 0xd258372b04cbc5c5, 0x2c8fafc3103d6994, 0x2c351d561d54a8db]

private theorem rounds081_0 : sixRounds 0 (by decide) absorbed081 = quarter081_1 := by
  decide +kernel

private def quarter081_2 : Vector UInt64 25 :=
  #v[0x9615d5f496d21b1d, 0x52cc5b29a69578b3, 0x911d24d9cc5eda14, 0x30647212cc60a527, 0x4bbac7718350b383, 0x5a337e02d0f31832, 0x21424a7868a676c6, 0xcbadc95a2629dce9, 0xb3fe58c186fde92b, 0x8628266d8bee8701, 0x759acf0cfc7256e5, 0xb56b5a09a64c05df, 0x9438c0d346e0dcf2, 0x45c357d13dd8dcbc, 0xc568b72bc45cbe19, 0xadbdb53b2773f833, 0xbfa367d5a83e83fe, 0x69ca8e32c4298775, 0x1a785c3b93acc03d, 0x6f981ab4b3beab60, 0x8da72a16aa6d0de7, 0xe54eda8e95b0b4c5, 0x9d661bee3718f030, 0xd82299e8cac4e9af, 0x472ee0012c7ad7f2]

private theorem rounds081_1 : sixRounds 6 (by decide) quarter081_1 = quarter081_2 := by
  decide +kernel

private def quarter081_3 : Vector UInt64 25 :=
  #v[0x7bb04308e8234db1, 0x37130a88c8c183de, 0xa770cc541dfa5b10, 0x495f83620e75c6e4, 0xeb7bcd496becf370, 0xd67b69f7c3e96d58, 0xd8fc4b1bf4a56af5, 0x61d7b0757efeb670, 0xa0b7b747657311d7, 0x635c65c58de40870, 0x4202fa6f61c91ec2, 0x9b9022ac5108fc5f, 0x9b891d0683bbbf6e, 0x292b3dfef4a4f26a, 0x74caf17e87fbee30, 0x84771786c4fb9a00, 0x86cd50483f1c5d18, 0xbfe94b260a3ad423, 0x2cb5da1e0a1472d7, 0x3ff1dd72594b0a85, 0x7047c31c4b667ccf, 0x39f12ca4afd1efc1, 0xcaf25fb4e01ef879, 0x35b35b9ef8ca162d, 0x741e9e75a4f7c1c9]

private theorem rounds081_2 : sixRounds 12 (by decide) quarter081_2 = quarter081_3 := by
  decide +kernel

private theorem rounds081_3 : sixRounds 18 (by decide) quarter081_3 = state082 := by
  decide +kernel

private theorem perm081 : KECCAK.f1600 absorbed081 = state082 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds081_0, rounds081_1, rounds081_2, rounds081_3]
  rfl

theorem block081 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes081 ++ tail) state081 =
      KECCAK.Bytes.run 0 tail state082 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes081 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb081 ws)) := by
    rfl
  exact (step state081).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words081).trans perm081))

private def absorb082 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x39 0x91 0x25 0x60 0xc5 0x59 0x61 0x80)) 1 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x40 0x60)) 2 (by decide) (UInt64.ofBytes 0x73 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x0 0x60 0x16 0x84 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x52 0x20 0x60 0x3 0x60 0x52 0x81 0x90)) 7 (by decide) (UInt64.ofBytes 0x60 0x90 0x84 0x54 0x20 0x90 0x40 0x60)) 8 (by decide) (UInt64.ofBytes 0x60 0x57 0xad 0x2b 0x61 0x15 0x16 0xff)) 9 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x1 0x4 0x60 0x52 0x81 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x3 0x81 0x82 0x1 0x20 0x60 0x80 0x80)) 15 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x25 0x60 0x52 0x82)) 16 (by decide) (UInt64.ofBytes 0x91 0x25 0x60 0xc5 0x59 0x61 0x80 0x1))

private def absorbed082 : Vector UInt64 25 :=
  #v[0x84cc2117c2b814b5, 0xf3e39026a7f0399, 0x18566c70360cf136, 0x1b355ce0ecfdc02, 0x16c85f56dd6701ce, 0x74e965bda219c382, 0x85de486e0ae957e7, 0x3edc64fa1b27209f, 0x71d8396ab02ce13f, 0xec068c2742c5bfa5, 0xc3a8b813b8e5c2be, 0xe66151d0667399f0, 0xf59731421fb86c9f, 0x3266b8e94ff19aa8, 0xecfd00239ba7208f, 0x26b7f37f05fc8cb8, 0x107ee327379b7120, 0xa5c7018a7f79c4e, 0xfadade2561aba0e2, 0x83c2678250673084, 0x62eed08ce7f76516, 0xcb1b29d63cd32729, 0xea4183701bed380f, 0x7b393103fae3a5fa, 0xd651622df1da6e21]

private theorem words082 : absorb082 state082 = absorbed082 := by
  decide +kernel

private def quarter082_1 : Vector UInt64 25 :=
  #v[0xb49988c3ea76675c, 0xb26a814ad6a9cd0f, 0x44955c75b2dfc9ec, 0xae48944ee96f07b, 0x579fbcfaa3066e93, 0x6f28dd1e57c24c85, 0xc3fd7e8553681260, 0x894548dbfef424a3, 0x9c645ade40bbc732, 0x59b4302e33c27f6e, 0x2846b88286891cd3, 0x365ce1f13a15188d, 0x1e78e369310d2054, 0x4ab3c8d65653165, 0x5bb76cafa71d4f5a, 0x4c110320fc40b78e, 0xd137546f2671613d, 0x76dc3e8e6b1e177, 0x31195bfab174e923, 0x1acc142598d2083d, 0xc88e5aaca0583624, 0x3433a1b86a5247b6, 0xb3b85d4c4d0cc6f1, 0x68fa60d468eae11a, 0x9a4c613f0729f316]

private theorem rounds082_0 : sixRounds 0 (by decide) absorbed082 = quarter082_1 := by
  decide +kernel

private def quarter082_2 : Vector UInt64 25 :=
  #v[0x7ae58d0690656291, 0xd2d2fb2efd25341c, 0x54020215e0bc3aba, 0xe3ccba81ab63b2a8, 0x34c170c152ba1742, 0x812e48392c7efad0, 0x35b3ba6e065c6ad7, 0x3da48dea041e21bf, 0x83d35a47052f8d14, 0xfb21bcb5e665160b, 0xbfbd43c576bc0ab, 0xd24eecc2e9d5d0a2, 0xb582502dcff12f71, 0xf38662be3391b401, 0xa606879f23543b49, 0x5c1495354c899003, 0xe02423a55d7efb3e, 0x463c47cb5736ca83, 0xbb88c9d5af8f1646, 0x7a668bab0ae8079b, 0xf8a89528051af54d, 0xa15085d9999e9bd3, 0xcf76627286f14afa, 0x63c7ea473ef4533, 0xcb793f31b4d057c2]

private theorem rounds082_1 : sixRounds 6 (by decide) quarter082_1 = quarter082_2 := by
  decide +kernel

private def quarter082_3 : Vector UInt64 25 :=
  #v[0xa297ab28b07e78cd, 0xaabe0a55b229d932, 0x42e02295ed3c2282, 0x7d5c5da1702e4636, 0x74327bfb3615c4a8, 0x736f991f53ba473a, 0xa8118a5ec8725a74, 0xa7271955361eea20, 0xa1561c6a3a4df70e, 0xc8b29f5f1b70b193, 0x8cc2f6bcc77a808a, 0x307d0eb5250c04d2, 0xa2b0b9bf6032be6d, 0x8f3a30524fb94569, 0x8f167990120377b8, 0x8a31aec6ccdc60da, 0xe41b25f8acf33ea0, 0x2a025eec1489834a, 0x30f4cbf7ef5a7f51, 0x7f51e5b790a9a51b, 0xa8729bd10c3cdf6, 0xbe9832ca294bd85e, 0x866f84ec4f0db07e, 0xfc82967cc2f91a19, 0x38e7c1226ba41271]

private theorem rounds082_2 : sixRounds 12 (by decide) quarter082_2 = quarter082_3 := by
  decide +kernel

private theorem rounds082_3 : sixRounds 18 (by decide) quarter082_3 = state083 := by
  decide +kernel

private theorem perm082 : KECCAK.f1600 absorbed082 = state083 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds082_0, rounds082_1, rounds082_2, rounds082_3]
  rfl

theorem block082 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes082 ++ tail) state082 =
      KECCAK.Bytes.run 0 tail state083 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes082 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb082 ws)) := by
    rfl
  exact (step state082).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words082).trans perm082))

private def absorb083 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x40 0x60 0x39)) 1 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51 0x40)) 2 (by decide) (UInt64.ofBytes 0x43 0x61 0x86 0x86 0x33 0xd8 0x10 0x61)) 3 (by decide) (UInt64.ofBytes 0x0 0x60 0x54 0x1 0x60 0x5b 0x56 0xfa)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x1 0x74 0x90)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x90 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x45 0x2c 0x61 0x15 0x16 0xff 0x60 0x4)) 8 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x80 0x40 0x60 0x57)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x60 0x52 0x1 0x82 0x4 0x60 0x20 0x60)) 14 (by decide) (UInt64.ofBytes 0x50 0x7f 0x52 0x1 0x82 0x24 0x60 0x10)) 15 (by decide) (UInt64.ofBytes 0x3a 0x65 0x6c 0x62 0x61 0x73 0x75 0x61)) 16 (by decide) (UInt64.ofBytes 0x0 0x64 0x65 0x73 0x75 0x61 0x70 0x20))

private def absorbed083 : Vector UInt64 25 :=
  #v[0x253f5ac836a519c8, 0x19185c98b5d08fa, 0x7127f871db98890f, 0xb8e02781b435eec1, 0x3be7c0c4f6c1fb74, 0x7e4c4b9e7748c9fa, 0xb3d799847454c093, 0xf540f73727778625, 0x14517628b47de934, 0xe98d2eb5d9323f7f, 0x938c2c75eb90258e, 0x99a7f6895c1da494, 0xa2c192e1b1738b6a, 0x7ddb14edbff11e78, 0x6ada5523ec5300aa, 0xe1b810b5f8ffc306, 0x7a6e004a9bfcb0a1, 0xc25da447107c2fb0, 0x47e4a829b5c8f660, 0x977548d2ce1f2a47, 0x8a5fdef947e5a1c2, 0xc3b527db8212239e, 0x212a542942f0620e, 0xbe3ae2ef918afc61, 0xfd2f7ee0c181f291]

private theorem words083 : absorb083 state083 = absorbed083 := by
  decide +kernel

private def quarter083_1 : Vector UInt64 25 :=
  #v[0x840f7d2d7601755, 0x33bcf5677df02941, 0xfca35bf2f4f8a111, 0xa702314178af92d1, 0x1eef5243b8d89d1d, 0xa8439a4761a5dba1, 0xae9ec84e2cb47ea7, 0xadd554fd2bc98522, 0x20699300450f5307, 0x2efe17778f1b1fca, 0x21d83942164c2014, 0x404dbba762644f68, 0x1aac476ec7223665, 0x2c342ac254ed397d, 0xa2296c51d9bba652, 0xf136e065b40e089a, 0xc74dab25800b31f0, 0xda0ab0ed89605db5, 0x6b5064dd22ef68c0, 0x95fb2e0c4ba4dc80, 0x990bc035087edaed, 0x38efac53b803fe3e, 0x673fd2e0298f5ded, 0xf1980389345cd0ab, 0x902d2b1c6679f85a]

private theorem rounds083_0 : sixRounds 0 (by decide) absorbed083 = quarter083_1 := by
  decide +kernel

private def quarter083_2 : Vector UInt64 25 :=
  #v[0xb7dac434ee46f78d, 0xe98a2ff9e1eec967, 0xa8bd0041447822dd, 0x9a0725c91698f436, 0xc18e3c53d86a062c, 0x7b6b3a20e8fd32eb, 0x2506dd10193f3110, 0xe8c4b69867d5aa52, 0x3b368b5dbc5fa7a3, 0xdc8a25beecee3032, 0xa2938f2678db70a8, 0x95a0bc2ee97829e0, 0x5dea7d7c9644445f, 0x9eeac365491d5f94, 0x78d0d8f7a8c36dd8, 0xf5180bbedeb0611c, 0x3250efba6f622d93, 0x1d2c843b199bf1c0, 0x115a950a3abd2c30, 0x31d0490ccd17d26c, 0xf2f0052972c0b1ef, 0x5291485f38cd7ce1, 0xe652cc6c5c657038, 0xa43ba2da239cd977, 0xef27fac54d3af408]

private theorem rounds083_1 : sixRounds 6 (by decide) quarter083_1 = quarter083_2 := by
  decide +kernel

private def quarter083_3 : Vector UInt64 25 :=
  #v[0x626a158cfe7a2b7e, 0x357d40a0b337d5f9, 0x1a782a0bf51eae, 0x15e663f630f59cb6, 0xba9b07a0623d443, 0xbcb5c3982aeb4993, 0x764a3b955e79196a, 0xcb35045805252ac5, 0x15dce1b9d6b4a519, 0x95e0f00716a2fc61, 0xe7013c347ab91e02, 0xb4aa900f9d666b06, 0xebe0a058210b30ff, 0x9f894b90c3f7a57c, 0x7796603638b87c69, 0xa06d57f59380fcfd, 0x984b6c2060908dde, 0xe63eeef3bc083e82, 0x2113059c6be5ead6, 0x379c0777568d8602, 0x183d50bca142d836, 0xce93046533349246, 0x5760eece4a2110f0, 0xdaa28797424c9c5d, 0xf395ab8a8fb99002]

private theorem rounds083_2 : sixRounds 12 (by decide) quarter083_2 = quarter083_3 := by
  decide +kernel

private theorem rounds083_3 : sixRounds 18 (by decide) quarter083_3 = state084 := by
  decide +kernel

private theorem perm083 : KECCAK.f1600 absorbed083 = state084 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds083_0, rounds083_1, rounds083_2, rounds083_3]
  rfl

theorem block083 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes083 ++ tail) state083 =
      KECCAK.Bytes.run 0 tail state084 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes083 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb083 ws)) := by
    rfl
  exact (step state083).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words083).trans perm083))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
