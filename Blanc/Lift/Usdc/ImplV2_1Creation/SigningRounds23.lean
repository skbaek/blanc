import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb138 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x10 0x60 0x52 0x81 0x81 0x0 0x60 0x16)) 1 (by decide) (UInt64.ofBytes 0x80 0x40 0x60 0x52 0x81 0x90 0x20 0x60)) 2 (by decide) (UInt64.ofBytes 0x52 0x91 0x90 0x52 0x84 0x85 0x20 0x83)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0x7f 0x54 0x80 0x20 0x82 0x80)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x60 0x16 0x0 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x91 0x92 0x83 0x51 0x55 0x90 0x17 0x1)) 9 (by decide) (UInt64.ofBytes 0x59 0xee 0x28 0x35 0x50 0xde 0x98 0x7f)) 10 (by decide) (UInt64.ofBytes 0xa8 0x76 0x25 0xa 0xc 0xef 0x75 0xb5)) 11 (by decide) (UInt64.ofBytes 0x5b 0x68 0xa5 0x29 0xc0 0xbf 0x97 0x24)) 12 (by decide) (UInt64.ofBytes 0x10 0x9b 0x47 0x33 0xc3 0x9e 0x9e 0x20)) 13 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x50 0x50 0xa3 0x91 0xa5)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x7f 0x7f 0x0)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xa4 0x57 0x73 0x6e 0x57 0x5d 0xff 0xff))

private def absorbed138 : Vector UInt64 25 :=
  #v[0xa94332299c28bf79, 0x54849786a784523d, 0xd3e07bf8964cf878, 0xff1b1f7ff7729ee4, 0x65beb2d5f504bb7b, 0xa1b58d5e9a4fa398, 0xd62b97c6f582f4df, 0xf3f538778aa3aa64, 0xf946b9baec6178b, 0x4294638c7bb9c4cb, 0xb12bbeb5c66e1909, 0x9c471a0d6450b010, 0xdacfe4237a401a74, 0xad9f8af178fd10b6, 0xae34293aa18166d2, 0x2a2dd5a8cf5db876, 0xd06063dd8c00f539, 0xb54bac98a9f06ec3, 0xfcd323bea74939d, 0x4c80532b735e3641, 0xe0bf28d72b672021, 0x29f80c6f60710358, 0x9b27bb1b5a28a454, 0xeebb6dfb009dbcb5, 0xb6e0c40ae2e9ada8]

private theorem words138 : absorb138 state138 = absorbed138 := by
  decide +kernel

private def quarter138_1 : Vector UInt64 25 :=
  #v[0xc624d4a41392df4c, 0xc09595a8d18b5b6e, 0x84d3955f3a852a0c, 0xc142f441017c6882, 0x5e58c08ca8807c4a, 0x912264c5a69f4357, 0xbedc3d832e35c25b, 0xa72f91c319c8ffc6, 0x29b82e020294a200, 0xfc70a0b1723ff5d1, 0x911a937310f00ed2, 0xabd2a9f41dac2b9d, 0x2eb75517d9842836, 0xf9db694c8e06765d, 0xf4b52963e942a1d, 0xc4c4ab7670be96a4, 0x1cf2b4758690079c, 0x57396f34a03c8c3e, 0x4c54a519a7ca9e1f, 0xc9fafe1fa3d15614, 0x3778a724a998a763, 0xca1a0d1c407a9c71, 0x3fcbddeeb65982e4, 0xd4f040c91dbb7c8c, 0x48b7b55d4c782e3]

private theorem rounds138_0 : sixRounds 0 (by decide) absorbed138 = quarter138_1 := by
  decide +kernel

private def quarter138_2 : Vector UInt64 25 :=
  #v[0x417d7c09311236e8, 0xf037e9227c6290db, 0xfd44bb1742a59896, 0xb8b9977c61905e6f, 0x819d66d0a318e947, 0x71f240ac9c3c07b4, 0xb0ff5ac7805b3861, 0xce1eb6a25d0650cf, 0xdde48d4eb5982714, 0x4de0c902ae51dcb0, 0x3e8ce9c82eadcb2e, 0xf6b36a122f08be1e, 0xae80b88324f907ee, 0xa25e127e004f5f20, 0x203827b3cf39fc2b, 0x5a3f5725073d2bb6, 0x40839accddd6becb, 0xbf0f67a88654fa32, 0x7e99ebbfabd18dc1, 0xa0dc67dae385d568, 0xb85e4a18326b0aa1, 0x8ff6c6bebff4e75, 0x1069cdf578838d36, 0x5798f6084e5c52d4, 0x4d817f13226786d2]

private theorem rounds138_1 : sixRounds 6 (by decide) quarter138_1 = quarter138_2 := by
  decide +kernel

private def quarter138_3 : Vector UInt64 25 :=
  #v[0xf92c9133b0af3121, 0x8ac59b9a4edb5aae, 0x4e5ea7083949e5a, 0x44165f2fcd302d1f, 0x5cae68b92fa7d072, 0xd2859f893c54c7ec, 0x58db1808d269ad24, 0xcc4cd529238a4d13, 0x77654c2719651b30, 0x7c52ca94a3eb5e76, 0xd54b275b79217786, 0x2a30728393828d23, 0x5e0daaaf37e253b, 0x32bb41b21a6d2bfa, 0x7542d11e44186393, 0xa170c0eacfba393d, 0x1dd700a45574c2ae, 0x8f2624bf2cf07f60, 0x3857f70a48a43f01, 0x456fdbf904713cf0, 0xf3cef5c426a6c4ec, 0x7be48a0db2953990, 0x4707b8491043840, 0xbabf2bb2498f7e97, 0x86efc39e41e54072]

private theorem rounds138_2 : sixRounds 12 (by decide) quarter138_2 = quarter138_3 := by
  decide +kernel

private theorem rounds138_3 : sixRounds 18 (by decide) quarter138_3 = state139 := by
  decide +kernel

private theorem perm138 : KECCAK.f1600 absorbed138 = state139 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds138_0, rounds138_1, rounds138_2, rounds138_3]
  rfl

theorem block138 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes138 ++ tail) state138 =
      KECCAK.Bytes.run 0 tail state139 := by
  exact run_block_of_step bytes138 tail absorb138 state138 absorbed138
    state139 (fun _ => rfl) words138 perm138

private def absorb139 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1b 0x68 0x46 0x2f 0xe9 0xdf 0x1d 0x50)) 1 (by decide) (UInt64.ofBytes 0xbf 0x49 0x61 0x15 0x11 0x82 0xa0 0x20)) 2 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x1 0x4)) 8 (by decide) (UInt64.ofBytes 0x52 0x81 0x26 0x60 0x52 0x82 0x3 0x81)) 9 (by decide) (UInt64.ofBytes 0x60 0x6f 0x52 0x61 0x80 0x1 0x20 0x60)) 10 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x40 0x60 0x39 0x91 0x26)) 11 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 12 (by decide) (UInt64.ofBytes 0x1b 0x60 0x16 0xff 0x60 0x83 0x5b 0xfd)) 13 (by decide) (UInt64.ofBytes 0x57 0xd7 0x49 0x61 0x15 0x80 0x15 0x14)) 14 (by decide) (UInt64.ofBytes 0x14 0x1c 0x60 0x16 0xff 0x60 0x83 0x50)) 15 (by decide) (UInt64.ofBytes 0x60 0x57 0x2d 0x4a 0x61 0x15 0x5b 0x15)) 16 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40))

private def absorbed139 : Vector UInt64 25 :=
  #v[0x73316e741a166, 0x6aee58902b141330, 0xaaff25da543080df, 0x27b549459d68d20, 0x4e5a9bd11e1a9726, 0xc2fe0509737cd2e7, 0xddae15c617ec99cd, 0x6e6ed10262f807d3, 0xc448f0513c92b680, 0x33a69d6de1b5579a, 0x861e5f83d29fe162, 0x5ce38f868024e267, 0xaaf96c8d23f6d75a, 0x849e42d0b602a128, 0xdbb13af8527b5334, 0x73efafced57ad364, 0xb397b93af61997e, 0x6e2f91f143ba0162, 0xdf3760ae6ab8a491, 0xd21c79899f439b03, 0xdde84494dcd1941, 0xf14e2354f593b747, 0xe8b24c5dc100525d, 0x5ba63d468063e16a, 0x1cd36e7752465d0f]

private theorem words139 : absorb139 state139 = absorbed139 := by
  decide +kernel

private def quarter139_1 : Vector UInt64 25 :=
  #v[0x8a8439feaea49414, 0xe049f4207533dd78, 0x8371fdfb3ce2638b, 0xc20175cb162abb2a, 0x87b1fc6f9c91b0e8, 0xbe7d5a213c51aa89, 0xa85da7946cb92c64, 0xd8707caccf94aea6, 0xa7d516e5d2c67557, 0xbae8e6fdad159d77, 0xb73a9734e829d28e, 0xc4f5d7916ed61144, 0x892259b0ce4ce6f1, 0xe6718da18c57174f, 0xbbd927e3236d572b, 0x45b70baaecc477f, 0x1b4136d236c3b3bb, 0xe2276de8ee2ab9fb, 0x73bc334a5f27f8d, 0x5810f1a6a8c63baf, 0x3dbb3271fa6b7b96, 0x4e09e67dd791f0b6, 0x6fd631d849191c40, 0xc6a5accb1bbf5d7c, 0xb8e5a4050808f6bf]

private theorem rounds139_0 : sixRounds 0 (by decide) absorbed139 = quarter139_1 := by
  decide +kernel

private def quarter139_2 : Vector UInt64 25 :=
  #v[0xc7f71744834527c0, 0xaf3201a02cf5281, 0x3ce70b1da8c7e47e, 0xe458e99ca79ad2a4, 0xa6803d2cebb1558b, 0x719b39cfc6d9f706, 0xad7444df9d6de563, 0x2e362b8bcc7fc8d, 0x56fe34395ec702d0, 0x1607a016e3ef8e22, 0xfc7490c3da24642a, 0xe3b082c8789d19bb, 0x1bf8a323fecb03b7, 0x7a12f501b3b0a706, 0x36c4590cc5bfb47c, 0xb0bf74fc837269b, 0x67953ef64603053c, 0xb0be997eab75704a, 0x2797c34598a5b7ac, 0x9aa1ba6df59fcba4, 0x7c4aef424f6c7f2a, 0xddb7b21519dae839, 0xbd9cc94504a257cd, 0x6e64f1324d3e50b6, 0xf35d9c69f0b9b6da]

private theorem rounds139_1 : sixRounds 6 (by decide) quarter139_1 = quarter139_2 := by
  decide +kernel

private def quarter139_3 : Vector UInt64 25 :=
  #v[0x1a573d38a02a4e7c, 0x9df174d1c11a3fc5, 0x9af2dcbf1d734f7a, 0xd725fed5d479d3cf, 0xeee99622cf2b5293, 0x74a500993c6a3e8f, 0xedfa2be72d1874a5, 0x27966a10a8e95295, 0xb89eea9562fdec2, 0xbfa1ed1d44425232, 0x7c68a94d081660b6, 0x66241986946c2796, 0x4720194dc7879a89, 0xe5b1598f7888647f, 0xfc8b53af9dc8b9e4, 0x4fb2efd5fd78f7d4, 0xcdaac5e547951ad0, 0xb84f26461986b39d, 0x9527c708e9b2f6e0, 0x1a02a71295bb08e1, 0xe6826d7c263e9962, 0x2127f1d01c1a3b1f, 0xc7c9cb4249f2a0d, 0x66e23a8d97a4ea32, 0x3d20bd90757fb123]

private theorem rounds139_2 : sixRounds 12 (by decide) quarter139_2 = quarter139_3 := by
  decide +kernel

private theorem rounds139_3 : sixRounds 18 (by decide) quarter139_3 = state140 := by
  decide +kernel

private theorem perm139 : KECCAK.f1600 absorbed139 = state140 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds139_0, rounds139_1, rounds139_2, rounds139_3]
  rfl

theorem block139 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes139 ++ tail) state139 =
      KECCAK.Bytes.run 0 tail state140 := by
  exact run_block_of_step bytes139 tail absorb139 state139 absorbed139
    state140 (fun _ => rfl) words139 perm139

private def absorb140 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x1 0x4 0x60 0x52 0x81 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x3 0x81 0x82 0x1 0x20 0x60 0x80 0x80)) 5 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x26 0x60 0x52 0x82)) 6 (by decide) (UInt64.ofBytes 0x91 0x26 0x60 0x32 0x4f 0x61 0x80 0x1)) 7 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x40 0x60 0x39)) 8 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51 0x40)) 9 (by decide) (UInt64.ofBytes 0x86 0x86 0x86 0x86 0x1 0x60 0x0 0x60)) 10 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x60 0x51 0x40 0x60)) 11 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x52 0x40 0x60 0x1 0x20)) 12 (by decide) (UInt64.ofBytes 0x84 0x1 0x20 0x60 0x52 0x81 0x85 0x80)) 13 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x16 0xff 0x60)) 14 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x52 0x81 0x83)) 15 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x94 0x1 0x20 0x60 0x52)) 16 (by decide) (UInt64.ofBytes 0x60 0x51 0x40 0x60 0x20 0x60 0x50 0x50))

private def absorbed140 : Vector UInt64 25 :=
  #v[0xddb4db8e262748e8, 0xd43b11da430eeb46, 0x745c3f82c5485c1a, 0x6c6d3574e7e3fc2c, 0xeedbc1d9509a9ec3, 0x7efcf3f083769cce, 0x281195ba1ec57992, 0x1867fb0de439c4aa, 0x5aeabfbeee4657e7, 0xc85c938c10513252, 0xa406b31edc1b9bfb, 0xc4113cd715b61689, 0xf94b3ec0d118cf49, 0xe9049e1cad0ea8d5, 0xa0a5fe5a2f4d1e30, 0xdfd2a8deeb46508b, 0xf74579fc8e8972be, 0x43e7bc1a404fba9c, 0xbe7c1118b42c3282, 0x21edf644b3548511, 0x46ac311cf14fe473, 0xe4d4e507d2a83dd2, 0xf6d38998a88ef2df, 0xfc9f05dfd4fa0a5f, 0x2d9d6c1bc055c981]

private theorem words140 : absorb140 state140 = absorbed140 := by
  decide +kernel

private def quarter140_1 : Vector UInt64 25 :=
  #v[0xae332c0522a3d24f, 0xf487a3f7a316035d, 0x82029ecfde7aab63, 0x9e2527e4ab2a5d7, 0x90ac1581ca3d5bc9, 0xa98523515de7c5d3, 0x14e2538078083e08, 0xa44b3bff460f350, 0x753590f78012cb03, 0x4a6041bf11fe7fed, 0xe20688a038853ad0, 0xfc649ad9b7d5104, 0xe0234f2564315fff, 0x106d65bef7b96591, 0x1c49e732a5c1c6c6, 0x1f85e7f0f045248b, 0xb2c8092292e1e909, 0xc3277bbfd4d6183e, 0x2b394296b8ae74cc, 0x35647f9c384b674d, 0x3fa05ae058b28198, 0x9a37cc69950ff06, 0xebad213366bd50f4, 0xaa143439cac26d7b, 0xc994551f71031253]

private theorem rounds140_0 : sixRounds 0 (by decide) absorbed140 = quarter140_1 := by
  decide +kernel

private def quarter140_2 : Vector UInt64 25 :=
  #v[0x9bceceadc826b54e, 0xee46df0de6a2ce31, 0x15ac6e8a54e47d45, 0x5bd8516e17bfeece, 0x9e5d4f725f05893c, 0x3c1cdf0997aff4f4, 0x63bd7ea841d98b9f, 0xccf000512ec39512, 0x6733f248810a9825, 0xa623c7d902d89061, 0x6fe30a710717c2c6, 0x7115b8288785d5a1, 0x1f7ae2592dae16ce, 0xf19d67efa7c66825, 0x27ad40e56021725b, 0x1a0ed182402b721f, 0x25ac8ca6bae65143, 0xcc7f6da1b30d3b67, 0x7e57d16729ed405a, 0xb337da7e17993efa, 0x511204bff62d44af, 0x318d1ce6e2579cd0, 0xdab747de5ccbf0b2, 0xf5063007566c294e, 0xc0717ba57eca1948]

private theorem rounds140_1 : sixRounds 6 (by decide) quarter140_1 = quarter140_2 := by
  decide +kernel

private def quarter140_3 : Vector UInt64 25 :=
  #v[0x1cdb3de320d74228, 0x43c62b941baa5d96, 0xf87058a51722a0e5, 0xa2cbeb20d9f9c2be, 0x656ddce7658c004c, 0xbaf5b816b4be1107, 0xbe3b600de5b47037, 0x28a4f5bb1e49dba5, 0xe70ac0c2d6ab5519, 0xd3b46feda468e2af, 0x8b672cca1d49b731, 0x21752ade353fbd61, 0xd76c210662ada56b, 0xcd159e23fe6fd6da, 0x8827af3b555ab3ab, 0xed03cffdf298b131, 0xd7db6f00cae5173, 0xecb369833e999060, 0x7b5cbfc7fe7dd963, 0xde585ab7192db8b0, 0x558de8fd3332ebd2, 0x2036748c91665ddb, 0x845585dd5082a96c, 0xeb06f64965b3e530, 0xaa18f10db88ca275]

private theorem rounds140_2 : sixRounds 12 (by decide) quarter140_2 = quarter140_3 := by
  decide +kernel

private theorem rounds140_3 : sixRounds 18 (by decide) quarter140_3 = state141 := by
  decide +kernel

private theorem perm140 : KECCAK.f1600 absorbed140 = state141 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds140_0, rounds140_1, rounds140_2, rounds140_3]
  rfl

theorem block140 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes140 ++ tail) state140 =
      KECCAK.Bytes.run 0 tail state141 := by
  exact run_block_of_step bytes140 tail absorb140 state140 absorbed140
    state141 (fun _ => rfl) words140 perm140

private def absorb141 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x90 0x3 0x84 0x80 0x90 0x3 0x81 0x20)) 1 (by decide) (UInt64.ofBytes 0x4a 0x61 0x15 0x80 0x15 0xfa 0x5a 0x85)) 2 (by decide) (UInt64.ofBytes 0x3d 0x3e 0x80 0x0 0x60 0x3d 0x57 0x89)) 3 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x5b 0xfd 0x0 0x60)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x7f 0x51)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x73 0x50 0x50 0x91 0x51 0x1 0xe0 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x4b 0x61 0x16 0x81 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x80 0x40 0x60 0x57 0x36)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed141 : Vector UInt64 25 :=
  #v[0x2cb00a08bf6b031e, 0x9b354732f3330851, 0x81f980220074602f, 0x7d9bd9f8ec77ac49, 0x1f38ee1772fa4c5c, 0x5076aea4d573dd31, 0xea12fee99db574b6, 0x9b443576059113a3, 0x5aa14ec5f2995a4c, 0x3d2587a7b2ae02b8, 0x1681e9130b833b7a, 0x8f0952f2e68d96cc, 0xb89d233f35be9919, 0xd940993a149371b1, 0x1941c398021a9603, 0x48856be71eb5003a, 0x5937e891860411aa, 0xe3557013adc808d5, 0x2592e912df7a88d7, 0x5bc40a46e9911152, 0x6363e6f9c4ee9149, 0x978a49fd2a614059, 0xcaab00b0b354b9af, 0xc504bc581f2056a1, 0xbcede3e29d367d7f]

private theorem words141 : absorb141 state141 = absorbed141 := by
  decide +kernel

private def quarter141_1 : Vector UInt64 25 :=
  #v[0xcaf013e24d9fbe35, 0x99003fa486ddfd37, 0xef0cfd73d5e33f3a, 0xf1af7439d97e4202, 0x6d58c5880a27f9f3, 0x958ae4b338c46b63, 0x8c6edce64b9177d, 0x6fc1cdf2fb1ab8a7, 0x22fb1e34c646db9d, 0x68f0f9a86a712985, 0xaf6b67c7fc488fe0, 0xb03e7f38962a8a62, 0x3a28d9362df5a3f3, 0x7b7a050a34321e78, 0xeae5ad72b4f24507, 0xd48d7b419d4cd0ea, 0xcd828c3c445479e4, 0x70ba993d3a0c61c1, 0x15f8d5dcf9771095, 0x2436be44b3e127cc, 0xd64307c6e8ddef0d, 0x84d204a7521f6ff6, 0x172c772b9eb69aed, 0xae74aafc8b2f49cb, 0x8a4f5b35a2bb3c87]

private theorem rounds141_0 : sixRounds 0 (by decide) absorbed141 = quarter141_1 := by
  decide +kernel

private def quarter141_2 : Vector UInt64 25 :=
  #v[0xc0dd980866910b7a, 0xcfb69074fa4b38b7, 0x3476f66b4fb9a44e, 0x98db1d2f2cceb24, 0x52b266a84f0ca08d, 0x509c70c9f8b82678, 0xbf5ccbc27ab7e12c, 0x266e7c852a86d0cc, 0x20e25faf0ed54193, 0x6d7e4576fd0669c8, 0x247cf6db34f3d572, 0x3c1a978898314cf4, 0x4b76a2c82a783f1d, 0xc0d693efa7239654, 0x78903d0547591624, 0x17bb3487deb7a6c, 0x814c322f9a31b5a6, 0xabd001401e4f6d88, 0xd7a23afcb4d50518, 0xa0d4247e2a9e2ea4, 0x2fa390d8b37f2cb2, 0x2ca4905efc18340c, 0x10e524d7cabbcc6a, 0xeb831e30dff280b9, 0x959bbac71d492884]

private theorem rounds141_1 : sixRounds 6 (by decide) quarter141_1 = quarter141_2 := by
  decide +kernel

private def quarter141_3 : Vector UInt64 25 :=
  #v[0x7cc2fba02c5703de, 0x9b45b2f5db025ea5, 0xbba70aa7d2934ec8, 0x9ef2e72e02d9596a, 0xe599d98273a811bd, 0xe20e2259f882ccaf, 0xb6ee8cbd8cee391b, 0x2560d689423f4e7c, 0x4224a449e3092cf2, 0x5b1cb04bfaaef64f, 0x687f1120dd3eb0ee, 0x23bf18593d8826b, 0x8fefb9ade9c4d1f3, 0x81744da14d134043, 0x4180d2f4c37846d3, 0x7ee9e14a702d377d, 0xf09275a6b4ab9b7b, 0x1f39c1ab0e78da70, 0x17cfbab05844324e, 0x1a512fd1bedbed0d, 0xd6af7e2a30a5c7a, 0x501657c269c3a69, 0xc4919b4bb2e3bf76, 0x98e745fffe841f9a, 0x87334a2cf517e466]

private theorem rounds141_2 : sixRounds 12 (by decide) quarter141_2 = quarter141_3 := by
  decide +kernel

private theorem rounds141_3 : sixRounds 18 (by decide) quarter141_3 = state142 := by
  decide +kernel

private theorem perm141 : KECCAK.f1600 absorbed141 = state142 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds141_0, rounds141_1, rounds141_2, rounds141_3]
  rfl

theorem block141 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes141 ++ tail) state141 =
      KECCAK.Bytes.run 0 tail state142 := by
  exact run_block_of_step bytes141 tail absorb141 state141 absorbed141
    state142 (fun _ => rfl) words141 perm141

private def absorb142 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x4 0x60 0x20 0x60 0x52)) 1 (by decide) (UInt64.ofBytes 0x7f 0x52 0x1 0x82 0x24 0x60 0x1c 0x60)) 2 (by decide) (UInt64.ofBytes 0x65 0x76 0x6f 0x63 0x65 0x52 0x43 0x45)) 3 (by decide) (UInt64.ofBytes 0x6c 0x61 0x76 0x6e 0x69 0x20 0x3a 0x72)) 4 (by decide) (UInt64.ofBytes 0x61 0x6e 0x67 0x69 0x73 0x20 0x64 0x69)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x65 0x72 0x75 0x74)) 6 (by decide) (UInt64.ofBytes 0x90 0x51 0x90 0x52 0x1 0x82 0x44 0x60)) 7 (by decide) (UInt64.ofBytes 0xfd 0x90 0x1 0x64 0x60 0x3 0x90 0x81)) 8 (by decide) (UInt64.ofBytes 0x50 0x50 0x93 0x94 0x5b 0x50 0x90 0x5b)) 9 (by decide) (UInt64.ofBytes 0x4b 0x61 0x60 0x60 0x5b 0x56 0x50 0x50)) 10 (by decide) (UInt64.ofBytes 0x60 0x60 0x85 0x0 0x60 0x84 0x84 0x39)) 11 (by decide) (UInt64.ofBytes 0x56 0x17 0x4d 0x61 0x85 0x56 0x4b 0x61)) 12 (by decide) (UInt64.ofBytes 0x80 0x40 0x60 0x57 0xc1 0x4b 0x61 0x5b)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed142 : Vector UInt64 25 :=
  #v[0x4f41a980d643412c, 0xbd21abb91f317d4c, 0x19fae77df2c2e6b8, 0xfdbd41b07e7058c9, 0xf306c63dfb884ddf, 0xd30d9130b8d20ca4, 0x4c89262edfdc9e88, 0x3361be9972547d71, 0x1b00e3b15d97ad6, 0x110973348f330aac, 0xd03d0ce8da9f72b, 0x703515463aee2e, 0x774c952c7fa8953e, 0x8311a1703bf7663c, 0xf7af7097e98b31a8, 0x4b22c50a696bcf90, 0x93426fdc01c6e2e4, 0xa6c848c79fa9d9f1, 0xa133fb866af221eb, 0x7df42ac7b42ab28e, 0x908c3fd0d41b1df7, 0x2992e4e8dbf06002, 0xdd6b962efbb95038, 0xfe724081d17d6621, 0xaab9591fd4dedf16]

private theorem words142 : absorb142 state142 = absorbed142 := by
  decide +kernel

private def quarter142_1 : Vector UInt64 25 :=
  #v[0xf7bfe071fa8c970, 0xa57b5fa137d8489, 0x4358365ba33710b2, 0xb6d59d522ae40324, 0xad1ec46a103e72ba, 0xc8cc50ae6a691c73, 0x7843f2a12a08f882, 0x59ed9fd13bd84a25, 0xe9a9af96d3529548, 0xb7814312d8026334, 0xf975003df5498e6c, 0x499328aef6822137, 0xa02f1a926c564e3f, 0x780b193fab18cff3, 0x126ab67684983865, 0x9d1ef3c143169447, 0x9573a8852d739570, 0x39973f6d37d1ec73, 0x7fd3667067973ced, 0x6202325b5bde557f, 0xe7511d57470d5ea4, 0x33c3100d92854ffb, 0x4130473cde607208, 0x22871c216c61eb04, 0xce9fb458bcda9d97]

private theorem rounds142_0 : sixRounds 0 (by decide) absorbed142 = quarter142_1 := by
  decide +kernel

private def quarter142_2 : Vector UInt64 25 :=
  #v[0x81578f82d6df8ad4, 0xbb9fe37678e8a21d, 0x5a9f8adade891778, 0xe289aa16903c1f13, 0x4bf50d3091b8063d, 0xa1a8e1d7b58d4126, 0x8df313dcd6c445f3, 0x1501f9cbf9c8b0a6, 0xac89cf54cdb8ddf7, 0x60d9a047714aa3a5, 0x6a04b192073eb27d, 0xeb3e29f764a95c7f, 0x8714922dc852d8b0, 0x604113363ecf3eee, 0x47174aa3a495b96f, 0xf0f4602422fb68d0, 0x6ba2884513b583b5, 0x65ddebfa52e80820, 0x760d647fe30a9894, 0xcd127b72233d5aa8, 0x853ee23d0023d52c, 0xd4143df7e1b0b9eb, 0xbb016a85c7c41c49, 0xacc09228019dd648, 0xfecfc581e56e1e73]

private theorem rounds142_1 : sixRounds 6 (by decide) quarter142_1 = quarter142_2 := by
  decide +kernel

private def quarter142_3 : Vector UInt64 25 :=
  #v[0x5af57036c55d25de, 0xc3302b287c6363f0, 0xfe1afbde429da56, 0x848b1b061ee75178, 0x4f3c3b799b09c2e6, 0xa413939cae8506ee, 0xf42ef08ef37deacd, 0xe82b834da498cee6, 0x7a356be6f60b5c1e, 0xf8b6e2da4a457d2c, 0xe9351b4f598b394c, 0x520456c4577dcd26, 0x11bfbabbfefb08fd, 0x5617e00f22882bae, 0x87080f88ae114548, 0x11d907d66a9e1fb2, 0x5746fe3046e01376, 0x7cfc4e9102ee0b2f, 0xd55328fc9cdeb632, 0x175c3307fbd800f7, 0x522b73c376987bae, 0x645893fbac98acb5, 0x8afd94bd700d0d59, 0x18719a42ffdec237, 0x9afe8b38b156e671]

private theorem rounds142_2 : sixRounds 12 (by decide) quarter142_2 = quarter142_3 := by
  decide +kernel

private theorem rounds142_3 : sixRounds 18 (by decide) quarter142_3 = state143 := by
  decide +kernel

private theorem perm142 : KECCAK.f1600 absorbed142 = state143 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds142_0, rounds142_1, rounds142_2, rounds142_3]
  rfl

theorem block142 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes142 ++ tail) state142 =
      KECCAK.Bytes.run 0 tail state143 := by
  exact run_block_of_step bytes142 tail absorb142 state142 absorbed142
    state143 (fun _ => rfl) words142 perm142

private def absorb143 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x4 0x60 0x20 0x60 0x52 0x81 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x82 0x24 0x60 0x1d 0x60 0x52 0x1 0x82)) 2 (by decide) (UInt64.ofBytes 0x65 0x72 0x64 0x64 0x41 0x7f 0x52 0x1)) 3 (by decide) (UInt64.ofBytes 0x6c 0x6c 0x61 0x63 0x20 0x3a 0x73 0x73)) 4 (by decide) (UInt64.ofBytes 0x2d 0x6e 0x6f 0x6e 0x20 0x6f 0x74 0x20)) 5 (by decide) (UInt64.ofBytes 0x74 0x63 0x61 0x72 0x74 0x6e 0x6f 0x63)) 6 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x44 0x60 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x64 0x60 0x3 0x90 0x81 0x90 0x51 0x90)) 8 (by decide) (UInt64.ofBytes 0x60 0x60 0x0 0x60 0x5b 0xfd 0x90 0x1)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x86)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x85 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x51 0x80 0x82 0x80 0x51 0x40 0x60 0x87)) 13 (by decide) (UInt64.ofBytes 0x83 0x83 0x80 0x90 0x1 0x20 0x60 0x90)) 14 (by decide) (UInt64.ofBytes 0x2b 0x4c 0x61 0x10 0x83 0x20 0x60 0x5b)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0x7f 0x52 0x82 0x51 0x80 0x57)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed143 : Vector UInt64 25 :=
  #v[0x7e869eb68c576494, 0xa278da9fad74ca3, 0xfc053311e2294eb2, 0x7c2f313844d9cbc7, 0x659589a9f8ca2056, 0x85005fc79872dc25, 0x643228922729e247, 0xdb6cbe1447cca962, 0xe7aa1bf1d81c3964, 0x67b6dc4a7f73c427, 0x1ae873c56a924820, 0x88664af738061317, 0xb5628bd1f42f601, 0x23010dbb05faaa46, 0x276bc5b6e96456f8, 0x504c66d2e296678c, 0x7dfa7e7148a0f681, 0x9b18dc2e1f24ed7b, 0xe677a149f0b02992, 0xfec3cf621c8181fd, 0xf37a9af97a978c6d, 0xf437f60209445f14, 0x54a727baa8aace89, 0x810004f11dce65, 0x1d84fbc8e326a55f]

private theorem words143 : absorb143 state143 = absorbed143 := by
  decide +kernel

private def quarter143_1 : Vector UInt64 25 :=
  #v[0x3179c5f5e703cc23, 0xba3dfac660644089, 0x799ef4a6acb72be3, 0xade914ccb3a5960a, 0xd945ad268fbcd52b, 0x30b612c88f0254a2, 0xd3c902ba218d2559, 0xc005656e9887bfa6, 0x76486f9900946e51, 0x90fc09a6628e059d, 0xb7c86a02ca5a67c, 0xdc03ff07382699f5, 0xe2a16e875db8023, 0xe625f7cfa6073d7a, 0xbb2f20a5e4110249, 0x21e93acadcf1528d, 0x5797b5863beb4151, 0x1fa0c6f56d1756ae, 0x74d01984f078a6f6, 0x76d50a6e2c97f201, 0xba542c987c960f4b, 0x1aac3d1e7dca8257, 0xcdc485b6a71a1bbc, 0xc59f5a38f363b2c1, 0x9e02e53986797153]

private theorem rounds143_0 : sixRounds 0 (by decide) absorbed143 = quarter143_1 := by
  decide +kernel

private def quarter143_2 : Vector UInt64 25 :=
  #v[0x7fc2b485d3123a24, 0x872263b406523060, 0xe8603af81fee0e93, 0x4568f47000d16aec, 0x3a4563b207c0fd60, 0x69802399d126cf8b, 0xf6bda0c870ef87ca, 0xe304f78f2a4dba05, 0x9414ca7d81f98525, 0x8efce96a6ef7412f, 0x6b08b9e41678168a, 0x20e47cb408ea52fc, 0xa0ef9b946b18c125, 0xb353b4896cf6556a, 0xfe59199ab68f2c85, 0xcc57103e6408896f, 0x81ec630fa000975b, 0x7dba7dba726501f9, 0x2ee4ea01d290aa10, 0xe30116fbd42ee491, 0xb9503e7199eaf42, 0xe0d65a7ebcf398be, 0x7cb43d82ff585b8, 0xd958c10c6105c65a, 0xf92ac4b3f0266159]

private theorem rounds143_1 : sixRounds 6 (by decide) quarter143_1 = quarter143_2 := by
  decide +kernel

private def quarter143_3 : Vector UInt64 25 :=
  #v[0x9e6da85fa47c72a3, 0x322dd7025aba45d8, 0x25912a1363b50ee8, 0x70c6ae2c2348588, 0xd4c92011e4d59b24, 0xd9ca6fda5ed9c3f2, 0x53464e2487ca54f8, 0xd24b5baf757889d3, 0xc211603f9fee7797, 0x1140aac654fc01, 0x5303bcb71c7130d4, 0x5e941eccd554b988, 0xa1d84dee36200a24, 0xc5d3363d39a6d2db, 0x5abed0e4f92dde34, 0x9fd7cc22d6626930, 0xdd50502ca68ebd65, 0xce99888c4aaa2d94, 0xf1fc2dd29a2d7bb4, 0x79390f6135d714c4, 0x7c076adc71a45712, 0x5946774882827e8e, 0xea34b8ab12c124e0, 0xabdd20c9b92cbeb7, 0xf5b74d1afe5f653e]

private theorem rounds143_2 : sixRounds 12 (by decide) quarter143_2 = quarter143_3 := by
  decide +kernel

private theorem rounds143_3 : sixRounds 18 (by decide) quarter143_3 = state144 := by
  decide +kernel

private theorem perm143 : KECCAK.f1600 absorbed143 = state144 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds143_0, rounds143_1, rounds143_2, rounds143_3]
  rfl

theorem block143 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes143 ++ tail) state143 =
      KECCAK.Bytes.run 0 tail state144 := by
  exact run_block_of_step bytes143 tail absorb143 state143 absorbed143
    state144 (fun _ => rfl) words143 perm143

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
