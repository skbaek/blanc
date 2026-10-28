import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb24 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x35 0x80 0x80 0x90 0x1)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x90 0x16 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x2b 0x61 0x50 0x50 0x50 0x90 0x91 0x92)) 5 (by decide) (UInt64.ofBytes 0x15 0x80 0x34 0x5b 0x0 0x5b 0x56 0x9b)) 6 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x53 0xc 0x61)) 7 (by decide) (UInt64.ofBytes 0x80 0x4 0x60 0x88 0xc 0x61 0x50 0x5b)) 8 (by decide) (UInt64.ofBytes 0x35 0x80 0x80 0x90 0x1 0x81 0x3 0x36)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x60 0x90 0x16 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x50 0x50 0x90 0x91 0x92 0x90 0x1 0x20)) 13 (by decide) (UInt64.ofBytes 0x5b 0x0 0x5b 0x56 0xc2 0x2c 0x61 0x50)) 14 (by decide) (UInt64.ofBytes 0x60 0x57 0x96 0xc 0x61 0x15 0x80 0x34)) 15 (by decide) (UInt64.ofBytes 0xcb 0xc 0x61 0x50 0x5b 0xfd 0x80 0x0)) 16 (by decide) (UInt64.ofBytes 0x90 0x1 0x81 0x3 0x36 0x80 0x4 0x60))

private def absorbed24 : Vector UInt64 25 :=
  #v[0x75215260c374c29b, 0x1a3e771ef655a4fb, 0xf9e9cf7ea1e310fd, 0xaf9bd19f69ac8e8d, 0x359ec3dfea489765, 0xe01946d747809b5e, 0xb811a76fbc0fa288, 0x73a327394573f39d, 0x7c9d87caa9df9d00, 0xc7e7869c6b0f603d, 0x3dd1e66e19a81f1b, 0xa425503a3416ef90, 0xc880cfcd3ac64284, 0xbd133618601a0027, 0x626996e3bf8c8c31, 0xf2e5e92c95532b1a, 0x2738870720431cf0, 0x4de937a5fd9b7541, 0x2ee37392b935edac, 0xe00c24604a0b30e, 0x7deba4774ce0797, 0xb49c8e40c71ab44f, 0x741e4049c67ca3f1, 0x66abd16af251a796, 0x1a09a2cf2083412f]

private theorem words24 : absorb24 state24 = absorbed24 := by
  decide +kernel

private def quarter24_1 : Vector UInt64 25 :=
  #v[0x196ea398f0a4a45c, 0x7d98ecdacfbffa2c, 0x9090ab1da2b8193e, 0xc6389774f1871639, 0xf21db0d6a45a7283, 0x177afde732961e8e, 0xf4854837da40edf5, 0x56000a1aaceed7ac, 0x416048c974e9fb93, 0x84a642352190498, 0x8da336fd51df46a3, 0x10e5606dcf247442, 0xb8296a6ddec62b9a, 0xb08ff12e328f5d53, 0x5ed63d23ac11de9e, 0xf69d0f943ad62d8f, 0xea7439c16015bd9e, 0xe5ab1e5ebdc2f726, 0xf6276d3b287ad5a5, 0xdc37d3c3f5eeccda, 0x9b33be2c7f3fae10, 0xd5376785da7ddba9, 0x1f30fb327742b944, 0x56e4b129e54ce75c, 0xd3ccb9f57d31cd80]

private theorem rounds24_0 : sixRounds 0 (by decide) absorbed24 = quarter24_1 := by
  decide +kernel

private def quarter24_2 : Vector UInt64 25 :=
  #v[0x852002209ff3c68, 0x4ed664c588b4722c, 0x791cf86ecbbfc6ec, 0x6831cbe4a88392f2, 0x765e7f5e06868a08, 0xdb9a926e4d909507, 0xa332a0f8c176e1f1, 0x6565d8ead1790b0c, 0x29f4ad2ba6178eaf, 0x16c2325f2656a786, 0x8f180dfe33b1f4d8, 0xa153d64d72b061e4, 0x6940e47eadd7cb5c, 0xe6b5684035090f02, 0x6921660ccc008888, 0xd536e06f75b0e1e0, 0x275bb78f0295c9f8, 0xb34ec987d882207a, 0x49503993ac480c6e, 0xc016d26f752eddd, 0x9e24eef562bf79db, 0x7deec5a82bcd553c, 0xd3a57f264dee1204, 0x9df3cf8c30997243, 0xbb02d4f663e337c]

private theorem rounds24_1 : sixRounds 6 (by decide) quarter24_1 = quarter24_2 := by
  decide +kernel

private def quarter24_3 : Vector UInt64 25 :=
  #v[0x56c9d791d4d15f3f, 0xe43cfa2c3cef2903, 0x71439c93d8994c8c, 0xca672c933d2661fd, 0x62d057bc1d0e467f, 0x1e9ea73992aa0e29, 0x6f4c71abc47276f3, 0x1d44c4e937ab2c08, 0xb74b138966265fd3, 0x2de893df1394a736, 0xae495422a6999f97, 0x735c2eed87b12788, 0x81a835192f99fae7, 0x6a0f6d751f76c69a, 0xa50811de1369697a, 0x7f48b41c20e0c248, 0xa49db830e91ee348, 0x2ebc91ed08b19bb3, 0x64961d586f60bb30, 0xbfc50748dc5fff6, 0xe4faa712c9fc9925, 0x63a43e51b96af928, 0x5fc588994e93b06b, 0xedfcae1da4db238b, 0xe87ddce37ddcad]

private theorem rounds24_2 : sixRounds 12 (by decide) quarter24_2 = quarter24_3 := by
  decide +kernel

private theorem rounds24_3 : sixRounds 18 (by decide) quarter24_3 = state25 := by
  decide +kernel

private theorem perm24 : KECCAK.f1600 absorbed24 = state25 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds24_0, rounds24_1, rounds24_2, rounds24_3]
  rfl

theorem block24 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes24 ++ tail) state24 =
      KECCAK.Bytes.run 0 tail state25 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes24 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb24 ws)) := by
    rfl
  exact (step state24).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words24).trans perm24))

private def absorb25 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x35 0x80 0x80)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x91 0x92 0x90 0x1 0x20 0x60 0x90 0x16)) 4 (by decide) (UInt64.ofBytes 0x56 0xbc 0x2d 0x61 0x50 0x50 0x50 0x90)) 5 (by decide) (UInt64.ofBytes 0x15 0x15 0x82 0x80 0x51 0x40 0x60 0x5b)) 6 (by decide) (UInt64.ofBytes 0x91 0x1 0x20 0x60 0x52 0x81 0x15 0x15)) 7 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 8 (by decide) (UInt64.ofBytes 0x60 0x54 0x80 0x4 0x60 0x5b 0xf3 0x90)) 9 (by decide) (UInt64.ofBytes 0x1 0x61 0x15 0x16 0x1 0x60 0x81 0x1)) 10 (by decide) (UInt64.ofBytes 0x4 0x90 0x2 0x60 0x16 0x3 0x2 0x0)) 11 (by decide) (UInt64.ofBytes 0x91 0x80 0x20 0x60 0x1 0x1f 0x60 0x80)) 12 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x1 0x20 0x60 0x2 0x4)) 13 (by decide) (UInt64.ofBytes 0x92 0x80 0x52 0x40 0x60 0x1 0x81 0x90)) 14 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x81 0x90 0x91)) 15 (by decide) (UInt64.ofBytes 0x1 0x60 0x81 0x1 0x60 0x54 0x80 0x82)) 16 (by decide) (UInt64.ofBytes 0x16 0x3 0x2 0x0 0x1 0x61 0x15 0x16))

private def absorbed25 : Vector UInt64 25 :=
  #v[0x65b5ece06e68eb09, 0x35feee7a8e647db, 0x315f7ab3660ae282, 0xc1848861b6cd6171, 0xb9cb1ea36801836a, 0x89b8b629b1c450d0, 0x25d880b16969f0c8, 0x55f797bffdae5581, 0x456db0ba26e56419, 0xd8d0b143ad120a1f, 0xfb771e2274d0047f, 0x3bd558a9474c81d9, 0xb50be9c3fdcaaf1c, 0xf02098097698c9f7, 0xc38edcdfda16f15b, 0xc2b29af7b70971d6, 0x4bd528c514c38fad, 0xe8266fe7e9289a38, 0xe868f4b7af4bbd98, 0x89a721f010472faf, 0x947ab51b06cc621e, 0x7435d18c681c33f4, 0x51fd2506738c46ee, 0xca005ff8ddcfe382, 0x266e0f89aea4c3a9]

private theorem words25 : absorb25 state25 = absorbed25 := by
  decide +kernel

private def quarter25_1 : Vector UInt64 25 :=
  #v[0xd99180e3c33ef1bf, 0x6f0ddc83520d62c3, 0x9dfaf8c4453587c1, 0x223ec30cf136a189, 0xd828ab2c3f440415, 0xe9c421a04e4e3c96, 0x416f69820741a4cc, 0x7f89e9225404d84b, 0x2794108fab51c382, 0xbb773441c2381fe8, 0x89d83ef3817a1433, 0x1c31d67fc5c1ac30, 0xcdd0d1c128e1bf86, 0x94cef2b5f84644df, 0x26461f86a225eb24, 0x69f06221841205a3, 0x4ab219dc09b559b7, 0x19d6b70065f4a4c8, 0x413026c3ad907001, 0x480fd290356e7aa8, 0xfa6d10b34d4bc631, 0x8062c8510091d204, 0x794e108c1a9f863e, 0xcee31b64a478b082, 0xcea02eb3cdde5b64]

private theorem rounds25_0 : sixRounds 0 (by decide) absorbed25 = quarter25_1 := by
  decide +kernel

private def quarter25_2 : Vector UInt64 25 :=
  #v[0xe15f05f58012f0ea, 0x9b6ba6e69ddeb2ea, 0xecc2fabc63119c68, 0xf79e618d7f2dbb11, 0xd1d68e043126ac3f, 0x415da565134eefaa, 0xb41a2a4d41e6ac61, 0x6423b33b8afbbd40, 0xb9a3b329018fab8d, 0x2643e5c98c88f539, 0x59433ddeffc89b22, 0xda8ce3919c35be42, 0x14cd95306739b584, 0x137394741423deca, 0x44ed864536dd5589, 0x50e8aeff177c99db, 0x4ac1c2614a3a5079, 0x8f10c2e9758c83ab, 0x87dad2a59ebb796b, 0xa3f3892335853fff, 0x82562b2045b40a99, 0x6d8eae793ca88e37, 0xc31f41b72e48f1b1, 0x9297321360d36a23, 0x88e3fc2d1e8938a7]

private theorem rounds25_1 : sixRounds 6 (by decide) quarter25_1 = quarter25_2 := by
  decide +kernel

private def quarter25_3 : Vector UInt64 25 :=
  #v[0xcb2bb4bb9e2d8256, 0x4c6fb079d7edd723, 0x5112c6b3bb3e573b, 0xde930ac2e5a53202, 0x85b23d650e6beef2, 0x397a85534b7ad073, 0x62f955ea8d8dd698, 0xc1f92f5d2793692b, 0x92708577edf18cdc, 0x12e51f7285625e7c, 0xfc208ee188dff5d8, 0x52993fc64c315b6, 0x7c2f21f6fc6d693, 0x30448fd1142d20b8, 0xcf735c802ca72ed2, 0x38a4530499914e65, 0xb93ca2891e948c2, 0x4e1c07ebe6bb32dd, 0xd410ff76b7b9eec0, 0x81bc000b9a0095ec, 0x439b1f88ddce5c5c, 0xd232565fd24277e1, 0xc573e6455f9cc0a9, 0x100134f919509d80, 0x923ea61d46e58f0c]

private theorem rounds25_2 : sixRounds 12 (by decide) quarter25_2 = quarter25_3 := by
  decide +kernel

private theorem rounds25_3 : sixRounds 18 (by decide) quarter25_3 = state26 := by
  decide +kernel

private theorem perm25 : KECCAK.f1600 absorbed25 = state26 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds25_0, rounds25_1, rounds25_2, rounds25_3]
  rfl

theorem block25 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes25 ++ tail) state25 =
      KECCAK.Bytes.run 0 tail state26 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes25 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb25 ws)) := by
    rfl
  exact (step state25).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words25).trans perm25))

private def absorb26 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xd 0x61 0x15 0x80 0x4 0x90 0x2 0x60)) 1 (by decide) (UInt64.ofBytes 0xd 0x61 0x10 0x1f 0x60 0x80 0x57 0x7b)) 2 (by decide) (UInt64.ofBytes 0x54 0x83 0x80 0x0 0x1 0x61 0x57 0x50)) 3 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x91 0x52 0x83 0x2 0x4)) 4 (by decide) (UInt64.ofBytes 0x1 0x82 0x5b 0x56 0x7b 0xd 0x61 0x91)) 5 (by decide) (UInt64.ofBytes 0x60 0x20 0x60 0x52 0x0 0x60 0x90 0x91)) 6 (by decide) (UInt64.ofBytes 0x52 0x81 0x54 0x81 0x5b 0x90 0x20 0x0)) 7 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x1 0x1 0x60 0x90)) 8 (by decide) (UInt64.ofBytes 0x82 0x57 0x5e 0xd 0x61 0x11 0x83 0x80)) 9 (by decide) (UInt64.ofBytes 0x91 0x1 0x82 0x16 0x1f 0x60 0x3 0x90)) 10 (by decide) (UInt64.ofBytes 0x56 0x81 0x50 0x50 0x50 0x50 0x50 0x5b)) 11 (by decide) (UInt64.ofBytes 0x90 0x14 0x60 0x1 0x60 0x0 0x60 0x5b)) 12 (by decide) (UInt64.ofBytes 0x4 0x90 0xa 0x0 0x1 0x61 0x90 0x54)) 13 (by decide) (UInt64.ofBytes 0xd 0x61 0x15 0x15 0x15 0x16 0xff 0x60)) 14 (by decide) (UInt64.ofBytes 0x33 0x5b 0xfd 0x80 0x0 0x60 0x57 0xa1)) 15 (by decide) (UInt64.ofBytes 0x0 0x60 0x3 0x60 0x15 0x15 0x0 0x60)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x83))

private def absorbed26 : Vector UInt64 25 :=
  #v[0x5a3438558125102a, 0x46035e8ec620ff68, 0xa9ef1ef8469cfeeb, 0xb5aa9cf3e4d44fc1, 0xa158589f31870f55, 0x523bf1d2c936dee3, 0xbfca315746f910cb, 0xcff3ce08431c301a, 0xc17c52c05648131b, 0x33b72d2dab2dcf41, 0x37348ad3a692f529, 0xf1e1a79bd40030cf, 0x33abdea0c2c63c44, 0xa9c9a65b2a62e998, 0xc4ebecd88e168f06, 0x9dbb4bb3383ec4e8, 0xb70e050e13737986, 0x87a0528a5d0dd3c9, 0x7c9d36d7bcde53bf, 0x5a4b8a256c14af4a, 0x889d4c30a92197ed, 0x344e5de051a237a, 0x756fad1f06ee06cf, 0x2ebc5b7421702f48, 0xf681b8e5010175e5]

private theorem words26 : absorb26 state26 = absorbed26 := by
  decide +kernel

private def quarter26_1 : Vector UInt64 25 :=
  #v[0xa6a37b2cbc9c5c3a, 0xf8057de6bf678b6d, 0x1d79d9f336b34208, 0x8df8d301a29ffb22, 0x71aeb50ff306b9af, 0xf083dba8ce08381b, 0xc2f5eeb83a370fb6, 0xe577373063f9904, 0x2897edacd5bf8ff1, 0xfcef79706ce948ce, 0x9222ca5a81bd9736, 0x2b43b8d6e0c46967, 0xe47e0823a1d2d22, 0xd85095e5112d32d4, 0x282cd3d99f2c7088, 0x69a312b7e7a0c930, 0x8f03a8cc90c7c000, 0x9b758d793ffd1530, 0x914cf78a322b3fdd, 0x75527c6449eda6e1, 0x1f0d9f4293f33b0d, 0xc5d1ade36e1fb0ad, 0x31a89a6ee279dc8a, 0x155f9158442a0579, 0x9face6a6fa2da62]

private theorem rounds26_0 : sixRounds 0 (by decide) absorbed26 = quarter26_1 := by
  decide +kernel

private def quarter26_2 : Vector UInt64 25 :=
  #v[0xfcca09e40fc8aab5, 0xaa795b213613a74b, 0x112b1c7b4d9f5765, 0x78d468c759f4aeb5, 0x117b9ade5c153ec2, 0x6402a89854ff3376, 0xd8d23e847070e571, 0x26fa36823c6b6f1e, 0x4b5c139f19f6823f, 0xba2d2a2c5b2a5def, 0xba645c7383376579, 0xd4a9138cae42d153, 0xbf080c704fcb6b50, 0x36d398a9cc4c6e1a, 0x1336533986ed6f60, 0x7fc2e13f2165dceb, 0x761acb86cf64661b, 0x8dd4460d3ff7c384, 0xe4f4f0b44952f55, 0xcc5978e079a5a6f2, 0x72a001c855760d97, 0x1b823602779c52fd, 0x4daf19ab9de3d4a6, 0xdf8de98d8b374f3d, 0xaa2d5cbcd70ce084]

private theorem rounds26_1 : sixRounds 6 (by decide) quarter26_1 = quarter26_2 := by
  decide +kernel

private def quarter26_3 : Vector UInt64 25 :=
  #v[0x29beb6ab715911f8, 0x3e7ca7efdddc7e5d, 0xcc8ee3fc46daf140, 0x38774808a3f3cbbd, 0x21f3bfc1ebe364a8, 0x9144999cf4480fb, 0x43743c884fd96ef3, 0x273aed453aba6219, 0x2270fe0f9cbf2976, 0xfbd41220f4ad87b4, 0x856d6d226db59119, 0x783886e2726dfbf0, 0x9b0b9253c42a224e, 0xded73bf38af3e84f, 0x86eed0735bbbee6b, 0x39630b71602cc47e, 0xfeb0c5ed8b4edf1e, 0x7221a1202367d59e, 0xbd6b10b79529bf13, 0xedb282dafd495254, 0xeeb850421f5803f0, 0xdf728c94b145ec00, 0xf01d88976b94cec9, 0xa42ac56e51d620, 0xa541b17c7f522cd9]

private theorem rounds26_2 : sixRounds 12 (by decide) quarter26_2 = quarter26_3 := by
  decide +kernel

private theorem rounds26_3 : sixRounds 18 (by decide) quarter26_3 = state27 := by
  decide +kernel

private theorem perm26 : KECCAK.f1600 absorbed26 = state27 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds26_0, rounds26_1, rounds26_2, rounds26_3]
  rfl

theorem block26 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes26 ++ tail) state26 =
      KECCAK.Bytes.run 0 tail state27 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes26 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb26 ws)) := by
    rfl
  exact (step state26).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words26).trans perm26))

private def absorb27 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x90 0x1 0x20)) 6 (by decide) (UInt64.ofBytes 0x90 0x54 0x90 0x0 0x60 0x20 0x0 0x60)) 7 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0xa 0x0 0x1 0x61)) 8 (by decide) (UInt64.ofBytes 0xe 0x61 0x15 0x15 0x14 0x15 0x15 0x16)) 9 (by decide) (UInt64.ofBytes 0x83 0x5b 0xfd 0x80 0x0 0x60 0x57 0x1)) 10 (by decide) (UInt64.ofBytes 0x0 0x60 0x3 0x60 0x15 0x15 0x0 0x60)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x83)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff))

private def absorbed27 : Vector UInt64 25 :=
  #v[0xd3ea18026fb5ace6, 0x1a5639d89e1ef628, 0x7f76d59def1e225c, 0x434bea8ad74f663a, 0x70b0e79888cdd3ec, 0x9670c6674f807165, 0xe418a664dcf9011b, 0x5722415c00de9f40, 0xf0797344acf6575a, 0xe92e08721d84f37d, 0x4e38a0a23a28b2af, 0x5cd1dac2e58a9fc5, 0x64ec9b4fe3c3034d, 0x2167ed0b0116a28, 0xa171f41a18fdb33a, 0xb3ce552bd8396f83, 0x9e7b2bd14f6758a4, 0x7a6dc311fe200a8, 0x7ca2c48d67570fe3, 0xeaf8ec8c8236ea90, 0x3fc58e0d211edd87, 0x12b937a74b79fce9, 0xd5dc7d4a2c9eab38, 0xd2efa0c4b400d67a, 0x5879a1672d85cd8f]

private theorem words27 : absorb27 state27 = absorbed27 := by
  decide +kernel

private def quarter27_1 : Vector UInt64 25 :=
  #v[0x879a5a6fdc3a8b30, 0x63fbbd31b79b90a5, 0x47aa5139b03736b, 0x859fca2eb910b906, 0x4ac82657d4cbd48a, 0xd8d0247e02824c51, 0x7d28c2d34860c5c0, 0x77c1bbb8ea09bc30, 0x2ad77d255e427a24, 0x1ab8ee93f385ae54, 0x31dd1d3a4625f00a, 0x872f29111acec765, 0xa8196c04ae896f4e, 0x14000107ff4e7e0b, 0x55ee5f024113dad9, 0x66d48ac2ff0a202b, 0x8126042dc9dc6730, 0xa41221cb6866b7d2, 0xee7899fdd03ecd5e, 0xf3441c4556cbfdde, 0xadfd401c67d85032, 0xdae61e2fc66c51da, 0x72fc90acefb74aae, 0x697b8a5ca5e9d728, 0x662fe1cdedcc5d4b]

private theorem rounds27_0 : sixRounds 0 (by decide) absorbed27 = quarter27_1 := by
  decide +kernel

private def quarter27_2 : Vector UInt64 25 :=
  #v[0xf9832718e3c8a904, 0xce621effcba22af, 0x2dd4d810140f2405, 0x2142048f32401097, 0x18dfa38747c7ffd3, 0x5b73de1c109555d0, 0x2276ee3fe8ac31e6, 0x1aae98062bd82e36, 0xddb361b8019a55b2, 0xfac8515cbb824233, 0x8b07d392c8181209, 0xddabcaab07b4e8f1, 0x9324ca81f50dfa7a, 0xd65170be2ad7cbe5, 0xb8f6d626049027a9, 0xa4f35e2bec4f033f, 0x39a2c287c9c0219c, 0x74aa483b5ef0a385, 0xfa16daba3f6e3e43, 0xeb0c62152aa793c1, 0x7a0d474c0fdea93a, 0x2ef2b3428f252dbe, 0x6b233ae0e297e121, 0x91241637c04a78e7, 0x56fd5c24dfaaf287]

private theorem rounds27_1 : sixRounds 6 (by decide) quarter27_1 = quarter27_2 := by
  decide +kernel

private def quarter27_3 : Vector UInt64 25 :=
  #v[0xee8497c572870f70, 0x3d5f67eadbbe97ee, 0xfbb7b255eab64a60, 0x89c5c8d67247a760, 0x691f31a37b2c0b71, 0x6fb41166d4180f29, 0x6f3eeeb26913bff, 0x427e954f7701a381, 0xaa913233fcecd831, 0x9a3c63c44112c6dc, 0x4edbd35dd1f2b756, 0xc7ec65ec5bc502da, 0x62a4080f103eba1a, 0x5268dca7fff55068, 0xb66aa2e8becf8fef, 0x3f269b90dbdf1f5c, 0xd0603c6269c4d3de, 0xad635e2146f68cfb, 0x8a854072df1254fe, 0x700440e0e176fc5f, 0xc96e28320666444b, 0x7f37c7febc55caf7, 0x734079966e0f9d9e, 0x109989ed8e9c28af, 0x6cc4b9dfc18ea192]

private theorem rounds27_2 : sixRounds 12 (by decide) quarter27_2 = quarter27_3 := by
  decide +kernel

private theorem rounds27_3 : sixRounds 18 (by decide) quarter27_3 = state28 := by
  decide +kernel

private theorem perm27 : KECCAK.f1600 absorbed27 = state28 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds27_0, rounds27_1, rounds27_2, rounds27_3]
  rfl

theorem block27 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes27 ++ tail) state27 =
      KECCAK.Bytes.run 0 tail state28 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes27 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb27 ws)) := by
    rfl
  exact (step state27).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words27).trans perm27))

private def absorb28 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x90 0x1 0x20)) 1 (by decide) (UInt64.ofBytes 0x90 0x54 0x90 0x0 0x60 0x20 0x0 0x60)) 2 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0xa 0x0 0x1 0x61)) 3 (by decide) (UInt64.ofBytes 0xe 0x61 0x15 0x15 0x14 0x15 0x15 0x16)) 4 (by decide) (UInt64.ofBytes 0x83 0x5b 0xfd 0x80 0x0 0x60 0x57 0x61)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x33 0x0 0x60 0xa 0x60)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x16 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x81 0x90 0x1 0x20 0x60 0x52 0x81 0x16)) 12 (by decide) (UInt64.ofBytes 0x60 0x20 0x0 0x60 0x1 0x20 0x60 0x52)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x87 0x0)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73))

private def absorbed28 : Vector UInt64 25 :=
  #v[0xe319f3fbfa630152, 0xdc75028f024721e8, 0x11d8cfd52cce2725, 0x6d14d708eb72716a, 0x91015b7a4e9730f, 0x245d2aa109200d27, 0xe2d6d8a385636a83, 0xd762bb22f573c712, 0xeb0af30d86caaffd, 0x5c70bfb83d98ccd7, 0xf47fc15bb3ac33df, 0x3ff5d2b733650885, 0x301b9dcb15c97361, 0xb80db3791dd4781c, 0xe5ce0d9daee6ac63, 0x1399564acd87bfb0, 0x7a360f206cd445bf, 0x8e1f8f3e6b6746af, 0x97892b5238545ea6, 0xae63d53b90c17f5d, 0x1c066fd249eefb8, 0x79e0de938f905ba6, 0xe1fc6bb91a577b29, 0x5f69e0c1de2b2faa, 0xe93a93f30a818ccd]

private theorem words28 : absorb28 state28 = absorbed28 := by
  decide +kernel

private def quarter28_1 : Vector UInt64 25 :=
  #v[0xd3fddd6cdb1f9916, 0xe375164944163f90, 0x4acc45ffa76174d6, 0xf03a4587c59d7e2f, 0xcac5715dd02db25e, 0xdca1daf122db1d9c, 0x8b68e353236f6bfa, 0x48931d90140e0ed0, 0xec93cd5d46e3f0c2, 0xd9452ef39cadca02, 0xaebbdc428f625bc2, 0xe09936a5dade52f5, 0x5fa768969962e662, 0xc45584ed357e4419, 0x106947e002289a73, 0xb5077972124c7b70, 0x17d9f5c9925ee6fa, 0x97165c3514ec7729, 0xd37dbaa685e61b45, 0x4af59cb3fff13f82, 0x186c719b05f2dba8, 0x1b610030648c0a7c, 0xd3d72cffcad74c29, 0x25e671e5689b92a, 0x3c5b314b9e96e5da]

private theorem rounds28_0 : sixRounds 0 (by decide) absorbed28 = quarter28_1 := by
  decide +kernel

private def quarter28_2 : Vector UInt64 25 :=
  #v[0xdd90d9e3b8e04c40, 0xcc7471f3f8fafe87, 0x3402dfbf6fa28a84, 0xd5c5a834846bf2dd, 0xf67630173cecdb95, 0x6f2c8228a6952024, 0xea8818171b958266, 0x94d088728e6e8646, 0x648d45cb643e423d, 0xb1affc165fcda829, 0xf4dbce764ff18ac3, 0xa9548ce6dac50959, 0x2dd629f8ffc326ca, 0x521e3368aa5cfe5d, 0x44073b917c00589e, 0x12cd007df3124a5c, 0x3be21d6843c4a8db, 0xa569c15d10da59c2, 0x3922da524ec4407e, 0x8500a187c032419c, 0x80b97cede08d68f, 0xf7e1505bf79113b7, 0x49be1b5e0e66f15f, 0xd7165c2214337a5f, 0xd4d2c416c673678c]

private theorem rounds28_1 : sixRounds 6 (by decide) quarter28_1 = quarter28_2 := by
  decide +kernel

private def quarter28_3 : Vector UInt64 25 :=
  #v[0x71bb9ca0d2aa063d, 0x61b839903f007272, 0xdbcf529bf1e3c440, 0x5cff6154d5eb5c3d, 0x75b740289f2382a2, 0x5dad2404ad42d03f, 0xfd4e301196e9f524, 0xe56862186751702d, 0xd052e4acf9469cb8, 0x37b4796f90791850, 0x8b31fec278fc32c7, 0x109ea68240670f47, 0x47d017aa9b24241c, 0xe0f9a3cf246cb2fe, 0x23309a51794092d9, 0x352563f07b7b60c3, 0xa202fa94013d6c5, 0x592e2855ef872a80, 0x28bc397ae81a028f, 0x504b73688f0bf61b, 0x49301418d326e368, 0xa44345aa8f4c38c1, 0x6e5b27792814acdd, 0xc286224124c51844, 0xcb1be8611e2066b5]

private theorem rounds28_2 : sixRounds 12 (by decide) quarter28_2 = quarter28_3 := by
  decide +kernel

private theorem rounds28_3 : sixRounds 18 (by decide) quarter28_3 = state29 := by
  decide +kernel

private theorem perm28 : KECCAK.f1600 absorbed28 = state29 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds28_0, rounds28_1, rounds28_2, rounds28_3]
  rfl

theorem block28 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes28 ++ tail) state28 =
      KECCAK.Bytes.run 0 tail state29 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes28 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb28 ws)) := by
    rfl
  exact (step state28).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words28).trans perm28))

private def absorb29 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x52 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x90 0x1 0x20 0x60)) 3 (by decide) (UInt64.ofBytes 0x50 0x55 0x90 0x81 0x20 0x0 0x60 0x1)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x84)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x33 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x8c 0x7f 0x16 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xd1 0x5b 0x7d 0xec 0xeb 0xe5 0xe1 0x5b)) 11 (by decide) (UInt64.ofBytes 0xdd 0xf3 0x84 0x1e 0x7d 0x42 0x71 0x4f)) 12 (by decide) (UInt64.ofBytes 0x5b 0x1e 0x29 0xb2 0xf7 0xc0 0x14 0x3)) 13 (by decide) (UInt64.ofBytes 0x86 0x25 0xb9 0xc3 0xc7 0xc8 0xa 0x20)) 14 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x82 0x80 0x51 0x40 0x60)) 15 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x20)) 16 (by decide) (UInt64.ofBytes 0x92 0x1 0x60 0xa3 0x90 0x3 0x91 0x80))

private def absorbed29 : Vector UInt64 25 :=
  #v[0x7f7f0f19d746fc3d, 0x36827acfb29bd341, 0x301b3b33f81fa981, 0x8731aa52bfc6dd0, 0xcefe4934a98d8269, 0x827aff5577bb1d3b, 0xcb8aaebd583a671b, 0x4de8500b99fc1b55, 0x6cd92e375173fc82, 0x619bca9c04a72a73, 0xccbdb9a55703f773, 0xdc1825765c3fc68a, 0xf420bc7110144586, 0xcf7d89447fa4d165, 0xe1a367b9149c18c0, 0x2b812b6a898d042f, 0x4617198c6a9c4c4e, 0x4cc6adffd4d1cc0c, 0x2e07d41c9f026b4, 0xba15e1f724fc91de, 0xd0f3100d9f83e3e7, 0xb4ff53b8b683c864, 0x4ee735ce12a6a5fe, 0x622c89f87f36c8d1, 0xf3135e1d3e73299d]

private theorem words29 : absorb29 state29 = absorbed29 := by
  decide +kernel

private def quarter29_1 : Vector UInt64 25 :=
  #v[0xeef8b7380c3d4b16, 0x92b21efbad37dc47, 0x1920dd8ab6dc155c, 0x50828043b9921675, 0x2557c41a503ffc8, 0x4592faf111750000, 0x3174b0c98ab21e78, 0x3281e5fbee9d2c87, 0x44ad78fe2fc51634, 0xf0c1011cb704228c, 0x94c84b3ee7606ce8, 0x24677007c55b4b10, 0x68eae1a82ebf1ece, 0x903dea2162e9030d, 0xb88633b12ead2ca, 0x5785149cb3ce0c95, 0xefe45e266da2e2a6, 0x804f4628585b18de, 0xb8e1ef86cd8d9e5, 0x639cae84c7ce07fa, 0x434930fdb30d73ef, 0xe0afd4511c72acdf, 0xf9d7f5dcd262bee3, 0xb101982481df3465, 0x74b8d5b758e4adca]

private theorem rounds29_0 : sixRounds 0 (by decide) absorbed29 = quarter29_1 := by
  decide +kernel

private def quarter29_2 : Vector UInt64 25 :=
  #v[0xef961c0a00d31aec, 0xbd452aaa05994b54, 0xb0a283207a5adff9, 0x632718f739a00843, 0x3523414cb644cf92, 0x42ec9e3e03b9b849, 0x41562300fccfe30d, 0xcc140b07a4f7c16e, 0xc8f995681ac354de, 0x3715b6911ff2aba, 0x31160934ca6b79ea, 0x21fefb5121331951, 0x67ac9828f9b6cd0b, 0xa5f05eac6ca71ddf, 0x795d7a83df46d87d, 0x4e688629c8c79beb, 0x421a666f41c9d894, 0x1b960f61cd876451, 0xf653ef0141ec0f42, 0x506f1ad424cc5f24, 0x93adab26697f67df, 0xe8785ea8a819d5a3, 0x6ac46e06113cdd1a, 0x9e125849bf07faa5, 0x90922617c70e7a78]

private theorem rounds29_1 : sixRounds 6 (by decide) quarter29_1 = quarter29_2 := by
  decide +kernel

private def quarter29_3 : Vector UInt64 25 :=
  #v[0x602bb472ea132b4, 0x9978b4afc13d5ee1, 0xee003c38d709f05a, 0x6ece0645e5e333ca, 0xd78c7acd76e478d3, 0xa1a7cc4d13957033, 0xfa1491bcc158cb43, 0xe0d0aa0854ad6ada, 0xc3087839425f0492, 0x1fe9805fb01bfedc, 0x53bbbec89cd3d64d, 0xff91c2d7cfd1f2be, 0xed830e74f8636378, 0x2e16adc7f575f8d0, 0xd91443341cdc76da, 0xc5342f615b632d50, 0x6e46db006abe3d1e, 0x27e4a72d2f10c829, 0xb57851a3c9a9761e, 0xd8a60c1d4d99d8e3, 0x2a1c97cc82858ddd, 0xbd56907f0324218a, 0x3d3cb91b82145b1, 0x3fcc29f6f4ef73b6, 0xe7975a91f5e4611d]

private theorem rounds29_2 : sixRounds 12 (by decide) quarter29_2 = quarter29_3 := by
  decide +kernel

private theorem rounds29_3 : sixRounds 18 (by decide) quarter29_3 = state30 := by
  decide +kernel

private theorem perm29 : KECCAK.f1600 absorbed29 = state30 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds29_0, rounds29_1, rounds29_2, rounds29_3]
  rfl

theorem block29 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes29 ++ tail) state29 =
      KECCAK.Bytes.run 0 tail state30 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes29 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb29 ws)) := by
    rfl
  exact (step state29).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words29).trans perm29))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
