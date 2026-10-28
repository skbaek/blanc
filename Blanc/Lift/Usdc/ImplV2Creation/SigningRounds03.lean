import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb018 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x35 0x50 0x5b 0xfd 0x80)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x5b 0x56 0x37 0x28 0x61 0x16 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x5b 0x56 0x5f 0x28 0x61 0x70 0x4 0x61)) 5 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x23 0x4 0x61)) 6 (by decide) (UInt64.ofBytes 0x53 0x9 0x61 0x15 0x10 0x81 0x20 0x60)) 7 (by decide) (UInt64.ofBytes 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x29 0x61 0x16 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x29 0x61 0x35 0x7 0x61 0x5b 0x56 0x39)) 12 (by decide) (UInt64.ofBytes 0x29 0x61 0x59 0x3 0x61 0x5b 0x56 0x61)) 13 (by decide) (UInt64.ofBytes 0x29 0x61 0x35 0x7 0x61 0x5b 0x56 0x7d)) 14 (by decide) (UInt64.ofBytes 0x2a 0x61 0x23 0x4 0x61 0x5b 0x56 0xf6)) 15 (by decide) (UInt64.ofBytes 0x4 0x60 0x7 0x4 0x61 0x5b 0x56 0x12)) 16 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x40 0x60 0x3 0x36 0x80))

private def absorbed018 : Vector UInt64 25 :=
  #v[0x68f871c81d03edab, 0x627056fc7ba8419e, 0x30648e77360282dc, 0xec6604a7896f908d, 0x61860dbe09642784, 0xcd27b26b7e4ee67c, 0x7751dea6e92093aa, 0x6f979499c1519d24, 0xbb3f4673da21dbb0, 0x74321132caeff4f8, 0xdd2e4f110f069d5a, 0x7db50fba07b9a7fb, 0x8c3495e48dfbb7dc, 0xbccc9aca8c016465, 0x3a390ee59bb858b1, 0x48f893dc8a7425ba, 0xb4c400f05bd076b8, 0xa23fb6de44959825, 0x44d4f4d3bf9e0d3c, 0x808b11945f57d8f1, 0x700c4208bbd23c7, 0xd98699354dd45420, 0xd62aeac7b902fb3c, 0x959c89c723c89ea7, 0x5cabe5d2607c8f65]

private theorem words018 : absorb018 state018 = absorbed018 := by
  decide +kernel

private def quarter018_1 : Vector UInt64 25 :=
  #v[0x300859504a16d2ec, 0xf21e4ec1f016f0d0, 0x969ac0e5b75e547e, 0xc07d80da441b9237, 0x473d29efc495eb16, 0x581073fd76ff0734, 0x4a147d80c3e068c0, 0x7a0380f8d5c239d3, 0x3ed4c3effa375c89, 0xdfc68a44eed1273c, 0x92986c5275d52b3, 0xe1de3e7ff54503fd, 0xcf4510b2447c4a55, 0xfa5ebe2a1e936233, 0x2491ea0022b4626, 0x5feae808e12b0196, 0x923947fadd02720a, 0x2b41fd0ea488c62f, 0x63dac33f5901cb83, 0x217338b51174eff8, 0x3494d67f081a100a, 0x52441300ac6a946e, 0x3a24b35cbbbd96e2, 0x2062ad91c53076ca, 0x1151169aaf5cb3be]

private theorem rounds018_0 : sixRounds 0 (by decide) absorbed018 = quarter018_1 := by
  decide +kernel

private def quarter018_2 : Vector UInt64 25 :=
  #v[0xbe87847079ebea1d, 0xe0756bf097d1d5e, 0x4c334d6226574039, 0xaea6240aa3d4d2cc, 0x6ada09cd65725192, 0x69d8fd44e4fc5175, 0x43429d719f99bfa5, 0x604507a244d0638c, 0xa73ae7f6365afa13, 0xa631097d910e7003, 0xc78a56c518c68a4d, 0x595c4379df527378, 0x2841f5be84e5546e, 0xdb9cd9b34a0d5ec9, 0xe3b61283e331537e, 0xfc7fa593b18c44a2, 0x461339d6807c4e5c, 0x437e8543f0e7d4ab, 0xd3f4c4e444ef3e5f, 0xc2745c370e3c0274, 0x5ca15d2f9246ea69, 0xc3ac7554cead0dfc, 0xb60d172a77d6cccb, 0x15c77aa40feb0177, 0x559991649aeb205c]

private theorem rounds018_1 : sixRounds 6 (by decide) quarter018_1 = quarter018_2 := by
  decide +kernel

private def quarter018_3 : Vector UInt64 25 :=
  #v[0x332f8b79363be4f9, 0x2d4fa5ae88f5baa2, 0x522fc5f31fe1a13f, 0x142a903ff1d50ca2, 0xe10056bd50b400cd, 0xbdb0ede591b82340, 0xe012a2a6976c47ec, 0x8f5b389093423caf, 0xdea3cf3e8d03983f, 0xd22171febbe07cae, 0x489527cac69ef824, 0x3958eff196d000ce, 0xde9c98e996b2b4de, 0xe2291e34d70bc668, 0x7445da458f68b200, 0x96bbe2c3d5b3daf8, 0x2ff69d3834ccdf5f, 0x826a766589b38160, 0xc44e3a9004c4bea, 0xd7a8554f498ddc44, 0x86b6a729fa8a97ac, 0x4fca80573ebfd499, 0x461d8506525040b9, 0xc09dae358d5c5f4, 0xfdef660e2f437694]

private theorem rounds018_2 : sixRounds 12 (by decide) quarter018_2 = quarter018_3 := by
  decide +kernel

private theorem rounds018_3 : sixRounds 18 (by decide) quarter018_3 = state019 := by
  decide +kernel

private theorem perm018 : KECCAK.f1600 absorbed018 = state019 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds018_0, rounds018_1, rounds018_2, rounds018_3]
  rfl

theorem block018 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes018 ++ tail) state018 =
      KECCAK.Bytes.run 0 tail state019 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes018 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb018 ws)) := by
    rfl
  exact (step state018).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words018).trans perm018))

private def absorb019 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0xa6 0x9 0x61)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x50 0x5b)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x81 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x61 0x35 0x1 0x20 0x60 0x90 0x16 0x35)) 5 (by decide) (UInt64.ofBytes 0x60 0x7 0x4 0x61 0x5b 0x56 0x36 0x2a)) 6 (by decide) (UInt64.ofBytes 0x10 0x81 0x40 0x60 0x3 0x36 0x80 0x4)) 7 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xdf 0x9 0x61 0x15)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x50 0x5b 0xfd)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x35 0x1 0x20 0x60 0x90 0x16 0x35 0x81)) 12 (by decide) (UInt64.ofBytes 0x70 0x4 0x61 0x5b 0x56 0xb8 0x2b 0x61)) 13 (by decide) (UInt64.ofBytes 0x81 0x20 0x60 0x3 0x36 0x80 0x4 0x60)) 14 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x18 0xa 0x61 0x15 0x10)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x35 0x50 0x5b 0xfd 0x80)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed019 : Vector UInt64 25 :=
  #v[0xa3f65b36ad2346f6, 0x8ca405d4d31d4c39, 0x2cfc72be75b47a69, 0xde5215cc3d9180bd, 0xec1db49210c41e4d, 0x20862f621656455d, 0xf2df7050b523d359, 0x667db734b02e0b2, 0xafd8a917bb69be94, 0x842f2cfae5361098, 0xf6751174f617f05b, 0xe054a3a16df85dfa, 0x310860f35845dfd6, 0x2431397639a6b8a9, 0x96c4e1ceb0c07b4c, 0x97da0b09db7c20, 0x3bc946269dc82b0d, 0xd61fc761e35e1ef0, 0x767560ee8f22029b, 0x4f555e0335a33a8e, 0x6f3c9dd1b31bc9d4, 0x250db32d23491245, 0x556eae02ffab89eb, 0xb3d1768624696355, 0xd9b021adccd719d8]

private theorem words019 : absorb019 state019 = absorbed019 := by
  decide +kernel

private def quarter019_1 : Vector UInt64 25 :=
  #v[0xda985c4ab0272968, 0x4098388fd6e85278, 0x2924967ba93f6112, 0xd38c4d4b34720a8f, 0xe859fc854a5a721d, 0x1c0dfe27ebd74f19, 0x55fb752f9a2feb6b, 0xb06be78b442e2f1f, 0x3f90b7508bf3799a, 0xc8840eabaa582ae4, 0xab94dad339f3e5a3, 0x2bd83ca2de6a3171, 0x5b81eb7fccc4c26f, 0x26a814868d6d1742, 0x483ebc1d2b253645, 0xfa675bc7032a4600, 0x8ddb8a35aa7452e4, 0xfa013df50bbf8463, 0x8c45ae5a01d2e6cc, 0xc867bc550a39bd06, 0xe9616eecc7cf42b9, 0xea57258399dde5f3, 0x7b306558d9a70807, 0x858c4505b3073e26, 0x316baa2a15957251]

private theorem rounds019_0 : sixRounds 0 (by decide) absorbed019 = quarter019_1 := by
  decide +kernel

private def quarter019_2 : Vector UInt64 25 :=
  #v[0x85e36b4aacb5661a, 0xc7f2435ad820f945, 0x7a0607eba8d0093b, 0x5bf1e7cf8d9ef8dc, 0xa3df956e3c1ecb4, 0xd1438f6c39433534, 0x9b44ecda1f993a0e, 0xdeb29093ccb17aa6, 0x159279c42ec73926, 0xc2f78a02de0a91da, 0x7922eedc940ca257, 0x3ed24291937c647b, 0x30030317286581c8, 0x99329211a74948e, 0x9b6251a667caf6cd, 0x985fb2323c8c1cca, 0x50b62657b896faa1, 0x3b181a1216c5eca7, 0x8beeea2159c9405b, 0x1a295ffac1732663, 0x26c21bfe25f3aeaf, 0xf3982ad3b4991587, 0x3cf6c2b3f6b6c1ba, 0xca8867b9f3c6b7a0, 0x6cc07093d37c18e9]

private theorem rounds019_1 : sixRounds 6 (by decide) quarter019_1 = quarter019_2 := by
  decide +kernel

private def quarter019_3 : Vector UInt64 25 :=
  #v[0x7a85506badd41ee0, 0x3859998e261d4229, 0x221bb65eb07315b3, 0x1221cce2b7b7d7fb, 0x26d8310c78fdf687, 0xaab30c8fcc7cf757, 0xf6e686e7f57adf2a, 0x9e161ff7da4d8c38, 0x20dd04c4a9f25027, 0xe1ba8c7688f8636, 0x9ea8f63fb71b91d, 0x1eb9f7b666f6447b, 0xd7bd72215a42b23a, 0x272490d1f944283f, 0xc13fcbf8e470b6f9, 0x2af57d1414fc7583, 0xfde7234bd15d5ba5, 0x6ef5db96f2b807bd, 0xea34a04df0054782, 0x1a9083a419a1db4d, 0x9e89d983049c7b49, 0x9f9bb96a4952598b, 0x2719c419a3c0b2bb, 0x68e8425fe0acc7e6, 0x8bfd199db3a27c80]

private theorem rounds019_2 : sixRounds 12 (by decide) quarter019_2 = quarter019_3 := by
  decide +kernel

private theorem rounds019_3 : sixRounds 18 (by decide) quarter019_3 = state020 := by
  decide +kernel

private theorem perm019 : KECCAK.f1600 absorbed019 = state020 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds019_0, rounds019_1, rounds019_2, rounds019_3]
  rfl

theorem block019 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes019 ++ tail) state019 =
      KECCAK.Bytes.run 0 tail state020 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes019 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb019 ws)) := by
    rfl
  exact (step state019).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words019).trans perm019))

private def absorb020 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x5b 0x56 0x3a 0x2d 0x61 0x16 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x7 0x4 0x61)) 3 (by decide) (UInt64.ofBytes 0x4b 0xa 0x61 0x15 0x10 0x81 0x20 0x60)) 4 (by decide) (UInt64.ofBytes 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x2e 0x61 0x16 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x4 0x60 0x70 0x4 0x61 0x5b 0x56 0xa1)) 9 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x20 0x60 0x3 0x36 0x80)) 10 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x7e 0xa 0x61)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x35 0x50 0x5b)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x4 0x61 0x5b 0x56 0xcc 0x2e 0x61 0x16)) 15 (by decide) (UInt64.ofBytes 0x1 0x61 0x3 0x36 0x80 0x4 0x60 0x70)) 16 (by decide) (UInt64.ofBytes 0x57 0xb2 0xa 0x61 0x15 0x10 0x81 0x20))

private def absorbed020 : Vector UInt64 25 :=
  #v[0xe2a656d7be49ce72, 0x2be9b56574db2b75, 0xf05e4bd5b2252c9, 0x1dbdea823d2ca068, 0x9cb7ada24693316d, 0xd316725daf16e4e, 0x42c941514ee2d917, 0x1852e05a1cc08deb, 0xeaef0433530acc65, 0x9bf99aa33089271c, 0xd82c2c3556927de9, 0xe7e9b232b963ff36, 0xff442c301d6c4b87, 0x8b85a719a7e8e1f4, 0x6cb4b24c0b5fc4d8, 0xdac1ea78d7742da2, 0x6538c434b12991b5, 0xa39c988f6e0004ce, 0xcb152acebcfbfecf, 0x2b1615fcd9ce8585, 0xf1ba930a2319c98a, 0xc57a970d214dc03c, 0xf561f42bf12c1f5b, 0x877b72ee40046d7e, 0xe804c3aadb78ac14]

private theorem words020 : absorb020 state020 = absorbed020 := by
  decide +kernel

private def quarter020_1 : Vector UInt64 25 :=
  #v[0x57549f8bca0b3989, 0xb7beff9073072939, 0xf9b452f29084d39e, 0xcf48428e65d773cb, 0x3ae52099044b7daf, 0x966473da2d9a46e7, 0x1e1549f5dffeb57a, 0x4a726b54159bbe56, 0x256eb2f636cb93e3, 0x86d2d5539948fa32, 0x1c307de2a0ebf13d, 0x4b9edaf983dcdf77, 0xd86f82aa6fa7123, 0x1571509cd7d8d57a, 0x17ea190ecf531a17, 0x59fe5246887491f6, 0x3eeef06344d1d8ec, 0xd67825fae80232b4, 0x9706d5d3712bf5b7, 0x4db0460ce378bf91, 0x5c28d7a22a59ed77, 0xab7ef062d9609942, 0xe7ccc75a6f061689, 0x7c375108f866b105, 0x766c594e92cd78dd]

private theorem rounds020_0 : sixRounds 0 (by decide) absorbed020 = quarter020_1 := by
  decide +kernel

private def quarter020_2 : Vector UInt64 25 :=
  #v[0xbb7ead478b86c21d, 0xe8bfc00e8cd26af2, 0xd81838b4a5b67aec, 0x7a851ca734faa0ff, 0x56caa5485a447cb4, 0xebc2ea7339820900, 0x77ecc24e3b710f00, 0x7b13a7272ed278a6, 0x8f14d636e2dfb984, 0x4cea6de51a4aefac, 0x4bc6f6db9bdaee8c, 0xe5c3bcfd5de619af, 0xba1fe3f15d30d18f, 0x55d1b950141699f, 0x7692c93a77282dd2, 0xf315b9ba98d240b4, 0x3421ee3300a069e7, 0xa5d28b39ac9d4132, 0xac5e528d08f7a8f7, 0xe92ebf5fa4d47e40, 0x8cd9b5f5b61e1c90, 0xccf24f8387bb9e26, 0xd2aa894515d26139, 0xcf6e8dff75c250d8, 0x8bfe2931b603fae5]

private theorem rounds020_1 : sixRounds 6 (by decide) quarter020_1 = quarter020_2 := by
  decide +kernel

private def quarter020_3 : Vector UInt64 25 :=
  #v[0xdc66a3fe8b1a1374, 0x4ccc242a4572eb7f, 0xa22f68e9b87a78b, 0x2160e3cec88eb1e1, 0x4f95315101a52140, 0xecb5bbba96ee1c0d, 0xb21a9310b870307c, 0x1c9d432892406bc2, 0xb9a4c6e604b18c7c, 0x3f877633aa667317, 0x8711d71a6ed374c0, 0x80da277bbf04c76a, 0x86518c1e04cd4745, 0xb869080038f81291, 0x27983e41c771225, 0xa62eae4d970a580, 0x38e3c37903f2608c, 0x957e64505e3a8ec, 0xd5407b08217880f1, 0xe3bc66dfed607ef8, 0x5bfc82c0923296b8, 0x7e6d2be3726594b5, 0x9b38fa15e1066e6e, 0xedc9672f6f5aa2e4, 0xe0aaa0f2b6fb79ef]

private theorem rounds020_2 : sixRounds 12 (by decide) quarter020_2 = quarter020_3 := by
  decide +kernel

private theorem rounds020_3 : sixRounds 18 (by decide) quarter020_3 = state021 := by
  decide +kernel

private theorem perm020 : KECCAK.f1600 absorbed020 = state021 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds020_0, rounds020_1, rounds020_2, rounds020_3]
  rfl

theorem block020 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes020 ++ tail) state020 =
      KECCAK.Bytes.run 0 tail state021 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes020 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb020 ws)) := by
    rfl
  exact (step state020).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words020).trans perm020))

private def absorb021 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0x73 0x50 0x5b 0xfd 0x80 0x0 0x60)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x91 0x16 0x81 0x35 0x81 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x16 0x91 0x90 0x35 0x1 0x81 0x20 0x60)) 5 (by decide) (UInt64.ofBytes 0x60 0x90 0x35 0x1 0x81 0x40 0x60 0x90)) 6 (by decide) (UInt64.ofBytes 0x81 0x80 0x60 0x90 0x35 0x1 0x81 0x60)) 7 (by decide) (UInt64.ofBytes 0x35 0x1 0x81 0xa0 0x60 0x90 0x35 0x1)) 8 (by decide) (UInt64.ofBytes 0x35 0x1 0x82 0xc0 0x60 0xff 0x60 0x90)) 9 (by decide) (UInt64.ofBytes 0x90 0x35 0x1 0x81 0xe0 0x60 0x90 0x16)) 10 (by decide) (UInt64.ofBytes 0x33 0x30 0x61 0x35 0x1 0x0 0x1 0x61)) 11 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x70 0x4 0x61 0x5b 0x56)) 12 (by decide) (UInt64.ofBytes 0x61 0x15 0x10 0x81 0x60 0x60 0x3 0x36)) 13 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x1d 0xb)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x50)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x35 0x81 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed021 : Vector UInt64 25 :=
  #v[0xe182ff05687ba85e, 0x9d1608dcfd97dce0, 0x2eec284753138bfd, 0xccc0638111ed265, 0xc8922cd2e114b08b, 0x6022840775bd47af, 0xe87955111c9d80f1, 0x34c521646a21a63e, 0x516bae54a0e4f2b, 0x42139aba0661de8e, 0x2ecb0f67e427b387, 0xb6358e9734553d5f, 0xfec2a5f68ee94960, 0x348c9f4f578b3c40, 0x6e6193c80553a892, 0xa75be2876871e0fe, 0x48f6da8290d02c17, 0xd202aa5c777d5af, 0xd506f4121b898f96, 0x62f23532a38d1d8, 0xb795a43ae2558036, 0xcad76075b38aa6e5, 0x4d853cd26684ff6f, 0x588364513d471d56, 0x8253f59298102c38]

private theorem words021 : absorb021 state021 = absorbed021 := by
  decide +kernel

private def quarter021_1 : Vector UInt64 25 :=
  #v[0x5b33790de2b784f1, 0xb816f9fc67cbf4aa, 0xc018edfdde609453, 0x18f8609c5add8a17, 0x5cc83ab9ae9ce698, 0xcafba93110f45eac, 0xcf8e3c1d2560c787, 0xe5a0efd4b8eddede, 0x415e43f785e1caf, 0xcb8589ee68e10233, 0xd751957bbbde6b3c, 0x3eaee205185ff64c, 0xbda1117307d0d5b7, 0xb5454e009df29a2b, 0xf2174698c7f35f69, 0x652677652b2128b, 0x1bbd411d483b4d77, 0xce176d5820d3c73b, 0x65f9b0732eb14b73, 0xa575512974784609, 0x38876b6bed96faf1, 0x2db3c2a250c95dad, 0xd30733dc23c90db9, 0x1d8a21e0fca638e9, 0x8910385d06bff28]

private theorem rounds021_0 : sixRounds 0 (by decide) absorbed021 = quarter021_1 := by
  decide +kernel

private def quarter021_2 : Vector UInt64 25 :=
  #v[0xb4da5a62b61f42c7, 0xad65db1b5678f06b, 0x69d1dfcbfbdc5ad4, 0xa7f635db8d20a328, 0xf445de4f8d104bc3, 0x44a25cf68a5eb772, 0x5af7c72844bd3c8a, 0x14dac42b9474e0bf, 0xddbb5dae06dc3daa, 0x3fa30c38933d8774, 0xb75df128c673e83e, 0xbba1b6806f5fa306, 0x77d3f7ef159def21, 0x1104bc820515a7a, 0x7775f04a67a1564b, 0xf893a49cd822069e, 0xd34cb235e842192, 0x100128139722040e, 0x67d015178be2f7af, 0xe1c39dd7855aaa55, 0xde46fbee59fbda35, 0x48b65beb1b6636da, 0x4e3407eaa916d807, 0xd92d9c282e300597, 0xf8496007a96ccdc6]

private theorem rounds021_1 : sixRounds 6 (by decide) quarter021_1 = quarter021_2 := by
  decide +kernel

private def quarter021_3 : Vector UInt64 25 :=
  #v[0x2e32b4519e230ab, 0xe408807f90c638e7, 0xa40edca815575b1e, 0x4ebb710b45b6de54, 0xcb3f13a11b98c655, 0xcfc6106b877db860, 0x1f39dd89d8be4e73, 0x6d1aad1b9ab6e1ce, 0xe58608c8d4487877, 0xaf6f6801ba50f2b4, 0xf7c232affa85bd28, 0x4a6b38e2202ebe5c, 0x88d0558383e5148f, 0x68968b93f407e67f, 0x69c73cde2ba0d426, 0xb357613620f8e4a0, 0xf66159ad23227119, 0xe58543f46585e904, 0x2499b3421dbc67c, 0xc142e9df5048bf0c, 0x90907cc87494b60c, 0x3ebb5d9dcdbb9e71, 0x804b0c633368894f, 0xef4c07a579a816b7, 0x9142873fd5425d84]

private theorem rounds021_2 : sixRounds 12 (by decide) quarter021_2 = quarter021_3 := by
  decide +kernel

private theorem rounds021_3 : sixRounds 18 (by decide) quarter021_3 = state022 := by
  decide +kernel

private theorem perm021 : KECCAK.f1600 absorbed021 = state022 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds021_0, rounds021_1, rounds021_2, rounds021_3]
  rfl

theorem block021 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes021 ++ tail) state021 =
      KECCAK.Bytes.run 0 tail state022 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes021 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb021 ws)) := by
    rfl
  exact (step state021).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words021).trans perm021))

private def absorb022 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x35 0x1 0x81 0x20 0x60 0x91 0x16 0x81)) 1 (by decide) (UInt64.ofBytes 0x35 0x1 0x40 0x60 0x90 0x16 0x91 0x90)) 2 (by decide) (UInt64.ofBytes 0x35 0x7 0x61 0x5b 0x56 0xdd 0x31 0x61)) 3 (by decide) (UInt64.ofBytes 0x70 0x4 0x61 0x5b 0x56 0x73 0x32 0x61)) 4 (by decide) (UInt64.ofBytes 0x20 0x1 0x61 0x3 0x36 0x80 0x4 0x60)) 5 (by decide) (UInt64.ofBytes 0x60 0x57 0x69 0xb 0x61 0x15 0x10 0x81)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x50 0x5b 0xfd 0x80 0x0)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x60 0x91 0x16 0x81 0x35 0x81 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x90 0x16 0x91 0x90 0x35 0x1 0x81 0x20)) 11 (by decide) (UInt64.ofBytes 0x60 0x60 0x90 0x35 0x1 0x81 0x40 0x60)) 12 (by decide) (UInt64.ofBytes 0x1 0x81 0x80 0x60 0x90 0x35 0x1 0x81)) 13 (by decide) (UInt64.ofBytes 0x90 0x35 0x1 0x81 0xa0 0x60 0x90 0x35)) 14 (by decide) (UInt64.ofBytes 0x16 0x35 0x1 0x82 0xc0 0x60 0xff 0x60)) 15 (by decide) (UInt64.ofBytes 0x61 0x90 0x35 0x1 0x81 0xe0 0x60 0x90)) 16 (by decide) (UInt64.ofBytes 0x56 0x8f 0x32 0x61 0x35 0x1 0x0 0x1))

private def absorbed022 : Vector UInt64 25 :=
  #v[0x2b319840a521bbee, 0x8504db2b0e93a479, 0xc115ea2639739a64, 0x70783e395ea3206e, 0xb4aa23050b17b8f0, 0xbdf5009dac489ed2, 0xbc7f547b9861149b, 0x13093180a6d2fdf0, 0xa9726b11f64ab45c, 0xb8e736421dc964e6, 0x953e93699b9bd610, 0xfb984c5b1e3e470, 0x2a163ea5e0bc736e, 0x6bd8f7b9de09c53b, 0x347e6cb1ea4a2e03, 0x870ff7eb9fc6b2c1, 0x39c49f5f8513d80a, 0x7e875447667bda22, 0x6ab100a621351c2c, 0x8a566450d95f750d, 0xc52d314e32e991ca, 0x92751ee4f6a020ee, 0x61cbc8943f2772f9, 0xc9bedfde126959f7, 0x6e70933e4501509f]

private theorem words022 : absorb022 state022 = absorbed022 := by
  decide +kernel

private def quarter022_1 : Vector UInt64 25 :=
  #v[0xe7eb22e3f34c10a0, 0x64af7c62a2157d1, 0x48c7a3192f313641, 0x99f9b59db6a7f345, 0x84f77cc71b730626, 0x987b4a14b82278b7, 0x70f216ec4673be5b, 0xdb9b449fc6a16481, 0xbfaf4b3f34e945df, 0x1f932d90a2f3d28d, 0x926b52479c91be7a, 0xa249233c2dfa603a, 0x5cd7df4e34b66c5f, 0xaacd3454e315ca0f, 0x4b8b2d53c37ab6ef, 0x79ad2e2a26403441, 0x29428ab0aa90b676, 0x8f2621da69b1d7ab, 0x7fae868f65a4178, 0x3fb03e660f999abf, 0xddb4ef59424733c9, 0xbba78d7993b93030, 0xb5e68d0fe53b0b0e, 0x6bb81c40fb874795, 0x8a6280c3c09c09f4]

private theorem rounds022_0 : sixRounds 0 (by decide) absorbed022 = quarter022_1 := by
  decide +kernel

private def quarter022_2 : Vector UInt64 25 :=
  #v[0x66e08d9fdd89c477, 0xa74b89e42042346, 0x3fa1b67fa046d1bc, 0x76453ea18905e615, 0xe8b0308a57fe538d, 0x8c1cc69371269be4, 0xf1fedba352acefa2, 0xe94a43c950d766b5, 0x3350108656f654e8, 0x27c78f202e512688, 0x8435cccd8a464dc8, 0x2de631b0ec500147, 0x5a59c41fbc159e50, 0x9cef51d7d95cb151, 0xf9c079ecee3b2109, 0x3a7a7052c88923c2, 0x215a5061b7181549, 0x40a1cde6aeadb6c1, 0x9fdbbcc49497857d, 0xa2673fa99bf3355, 0x6531efdcba157366, 0xda50c573a5a82e2, 0xc64ec6e0cf8c8dc, 0xbd94d63b19537076, 0x55894efa38bb2c3e]

private theorem rounds022_1 : sixRounds 6 (by decide) quarter022_1 = quarter022_2 := by
  decide +kernel

private def quarter022_3 : Vector UInt64 25 :=
  #v[0x9e5ef3b53f5c2b4e, 0xa06197105af8976c, 0x559914eba2c3a037, 0xa8fec9e1cdcc72a, 0x462b96f1cba99f63, 0x54718675ad5860ce, 0xf56ff19ab6571ef2, 0x32095c46f7fdc19d, 0xe66510b10077f7e2, 0x8a178dd76a32fc87, 0x942eb32db20e65f6, 0x8568abf48ae426ad, 0x15497d3c5caf9bc8, 0xaa5a9772534f3ab3, 0xf70276313849913, 0x170eba85accaab60, 0xd636b8e630a37e39, 0x67a36ce13acc5fae, 0x87b30531a1711457, 0xc8486b21435cf05d, 0x7499edd76a5919cc, 0x4dd6581d48f9fa0b, 0x1b85e3533cb69669, 0x6421bfb7f09915c3, 0xba83c47f73ad794]

private theorem rounds022_2 : sixRounds 12 (by decide) quarter022_2 = quarter022_3 := by
  decide +kernel

private theorem rounds022_3 : sixRounds 18 (by decide) quarter022_3 = state023 := by
  decide +kernel

private theorem perm022 : KECCAK.f1600 absorbed022 = state023 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds022_0, rounds022_1, rounds022_2, rounds022_3]
  rfl

theorem block022 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes022 ++ tail) state022 =
      KECCAK.Bytes.run 0 tail state023 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes022 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb022 ws)) := by
    rfl
  exact (step state022).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words022).trans perm022))

private def absorb023 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x56 0x2c 0x34 0x61 0x23 0x4 0x61 0x5b)) 1 (by decide) (UInt64.ofBytes 0x36 0x80 0x4 0x60 0x70 0x4 0x61 0x5b)) 2 (by decide) (UInt64.ofBytes 0xb 0x61 0x15 0x10 0x81 0xe0 0x60 0x3)) 3 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0xdc)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x81 0x35 0x81 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x90 0x35 0x1 0x81 0x20 0x60 0x91 0x16)) 8 (by decide) (UInt64.ofBytes 0x35 0x1 0x81 0x40 0x60 0x90 0x16 0x91)) 9 (by decide) (UInt64.ofBytes 0x60 0x90 0x35 0x1 0x81 0x60 0x60 0x90)) 10 (by decide) (UInt64.ofBytes 0x90 0x16 0x35 0x1 0x82 0x80 0x60 0xff)) 11 (by decide) (UInt64.ofBytes 0xc0 0x60 0x90 0x35 0x1 0x81 0xa0 0x60)) 12 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0x50 0x34 0x61 0x35 0x1)) 13 (by decide) (UInt64.ofBytes 0x60 0x3 0x36 0x80 0x4 0x60 0x70 0x4)) 14 (by decide) (UInt64.ofBytes 0x57 0x3a 0xc 0x61 0x15 0x10 0x81 0x20)) 15 (by decide) (UInt64.ofBytes 0x90 0x1 0x81 0x5b 0xfd 0x80 0x0 0x60)) 16 (by decide) (UInt64.ofBytes 0x1 0x64 0x35 0x81 0x1 0x81 0x20 0x60))

private def absorbed023 : Vector UInt64 25 :=
  #v[0xd49ceb7cc54b126, 0xed8328db3091c1c1, 0xeda1b46152b6a80d, 0x1966ca20c6c4e7a7, 0xfa3da98a5b3cc2b3, 0x6edd16c09fa52dfa, 0xfdb0fbfa0a1be15f, 0x53a8e67f8e558741, 0x2a7f49b0605800ac, 0xe0e00ff422291f0c, 0x3493256e63ce007d, 0x8cd3ea1e950870ee, 0x2ce6b59b10053f11, 0xbee3182c04dbef55, 0x3a46d534566d279d, 0xae1ceb97de711214, 0xd0becb0071afae3c, 0x42e1d6c708b89be6, 0x8b1d5e30c8813f4, 0x3e2473bca1ef0465, 0xeaadf4c25b3344e8, 0xce9a00abdd0d59fc, 0x50feadf8c4d56a8b, 0xf73654af51d36a81, 0xa1b0fe5a0ad26432]

private theorem words023 : absorb023 state023 = absorbed023 := by
  decide +kernel

private def quarter023_1 : Vector UInt64 25 :=
  #v[0x1c0a7de8e01192b3, 0x70aa214909d6bce3, 0xc3b6531e8b609870, 0x56c196ca5c902fc2, 0xa179754eea334585, 0x5c07e03f85692a65, 0x9a90e87d8c3acdc3, 0x213c3805fcbb6b43, 0xf02f13d225f34e81, 0x2119c06f8160369d, 0x8216c65cc71e44e7, 0xf21d40e0180f7f78, 0x6a1f7afa06b9b58d, 0xe84d6c671ee03cae, 0x9e0f7db1467d928d, 0x732f006964c774ba, 0x2ba01b0ab7b7a1dc, 0x5f24e3a2cbcf238b, 0xfbc8ec1e46c5a534, 0xe027ac9996b67c7e, 0x1cab186937fdedb5, 0x95f2b12f9238dca6, 0x8b9acbeaf9a109ba, 0x24c8e68413b9f227, 0xf0a79ca9df36c454]

private theorem rounds023_0 : sixRounds 0 (by decide) absorbed023 = quarter023_1 := by
  decide +kernel

private def quarter023_2 : Vector UInt64 25 :=
  #v[0x4f46a83df3fdc6dd, 0x199c96a8a9b17e2f, 0x621c4eee7fc280c1, 0xd85cfdc2f9084e86, 0x764541681f0fe14a, 0x59bf8faaacf9b6f3, 0x85f126bbfcb393ba, 0xc29e846228a9122d, 0x7d5dff349ec4bb4c, 0xad56a149834d6f34, 0xbc120384fc681b26, 0xf5e91cfea23f82ea, 0x9966b96e4b4c294f, 0xa4819fa9f9614309, 0x91801d9ede9f5478, 0xa730190d180e37de, 0xbc8aa0bfcaed7fae, 0x2faabaffffe4cf44, 0x6b3be70a3fb32e4d, 0xdf05720510ac5c40, 0xd7b35e73e9d490ea, 0xafa0a4a1ae9cc381, 0x319c399a5f979c68, 0x202cc86e9237a13a, 0xd178bc3ed729b4c1]

private theorem rounds023_1 : sixRounds 6 (by decide) quarter023_1 = quarter023_2 := by
  decide +kernel

private def quarter023_3 : Vector UInt64 25 :=
  #v[0xfeeb1e9080ca29bc, 0xceee692e8a1f7ace, 0x1427a1f5f18ae230, 0x97f547beb4b4e01b, 0x3a8822babc08ab25, 0x8e4a686901ea7f27, 0x2f3fa56e34b9a181, 0x7fbc88a64ddbce30, 0xeabe92caeeb27706, 0x4b5e3921eee56d76, 0x34fbb6b111f5597c, 0xb71713abe5f6c3d1, 0x7c30113d5e0e401e, 0xc82132378706ae65, 0x1d221f40c23aa602, 0x733dde112f3408b3, 0x934948f5eb053bd, 0x7a0fe4cf6e20fec5, 0x62cd5d51f5b3cb88, 0xfa8e8547ff993a03, 0x2023aa6ac3eda0eb, 0xf09a018e7c689a4, 0x7debd2146c196dba, 0x1b59b94d7cf90e78, 0xcdba8c5b2df18c07]

private theorem rounds023_2 : sixRounds 12 (by decide) quarter023_2 = quarter023_3 := by
  decide +kernel

private theorem rounds023_3 : sixRounds 18 (by decide) quarter023_3 = state024 := by
  decide +kernel

private theorem perm023 : KECCAK.f1600 absorbed023 = state024 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds023_0, rounds023_1, rounds023_2, rounds023_3]
  rfl

theorem block023 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes023 ++ tail) state023 =
      KECCAK.Bytes.run 0 tail state024 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes023 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb023 ws)) := by
    rfl
  exact (step state023).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words023).trans perm023))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
