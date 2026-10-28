import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb150 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x69 0x20 0x3a 0x72 0x65 0x76 0x6f 0x63)) 1 (by decide) (UInt64.ofBytes 0x73 0x20 0x64 0x69 0x6c 0x61 0x76 0x6e)) 2 (by decide) (UInt64.ofBytes 0x65 0x72 0x75 0x74 0x61 0x6e 0x67 0x69)) 3 (by decide) (UInt64.ofBytes 0x6c 0x61 0x76 0x20 0x27 0x76 0x27 0x20)) 4 (by decide) (UInt64.ofBytes 0x6c 0x62 0x61 0x6e 0x77 0x4f 0x65 0x75)) 5 (by decide) (UInt64.ofBytes 0x6f 0x20 0x77 0x65 0x6e 0x20 0x3a 0x65)) 6 (by decide) (UInt64.ofBytes 0x20 0x73 0x69 0x20 0x72 0x65 0x6e 0x77)) 7 (by decide) (UInt64.ofBytes 0x6f 0x72 0x65 0x7a 0x20 0x65 0x68 0x74)) 8 (by decide) (UInt64.ofBytes 0x73 0x73 0x65 0x72 0x64 0x64 0x61 0x20)) 9 (by decide) (UInt64.ofBytes 0x61 0x20 0x3a 0x30 0x32 0x43 0x52 0x45)) 10 (by decide) (UInt64.ofBytes 0x74 0x20 0x65 0x76 0x6f 0x72 0x70 0x70)) 11 (by decide) (UInt64.ofBytes 0x65 0x7a 0x20 0x65 0x68 0x74 0x20 0x6f)) 12 (by decide) (UInt64.ofBytes 0x65 0x72 0x64 0x64 0x61 0x20 0x6f 0x72)) 13 (by decide) (UInt64.ofBytes 0x6f 0x54 0x74 0x61 0x69 0x46 0x73 0x73)) 14 (by decide) (UInt64.ofBytes 0x77 0x65 0x6e 0x20 0x3a 0x6e 0x65 0x6b)) 15 (by decide) (UInt64.ofBytes 0x20 0x72 0x65 0x73 0x75 0x61 0x70 0x20)) 16 (by decide) (UInt64.ofBytes 0x7a 0x20 0x65 0x68 0x74 0x20 0x73 0x69))

private def absorbed150 : Vector UInt64 25 :=
  #v[0x4e62c413301e04e1, 0xe93c42e2bed037, 0xd082d84b81bcabc4, 0x1ff9f493012c43a0, 0x9355b20a7fdb5a26, 0xe3c74f8af7b1a0d7, 0x8f4f60dab52b8861, 0xaf1a67b45dd682a, 0xa915366cd8460936, 0x6a6c74abd4206cd6, 0x83c562b569c5bc9a, 0xf7350fbfdba4b5d8, 0xa263944920d399d1, 0xd65222a045445bad, 0x2a5ffe03913a189d, 0x5e447b5a775b359, 0x4aeb8f327fa4bf40, 0xa1b0a7d49047b44e, 0x526f67adc40c9f2f, 0xc0ef0cc612ff11e6, 0x8ff946807f7fc92e, 0x5044c1239d516df3, 0xefbc3d42f3adddfe, 0x3fa17d9188ed2ed8, 0xd904e83f3a481baa]

private theorem words150 : absorb150 state150 = absorbed150 := by
  decide +kernel

private def quarter150_1 : Vector UInt64 25 :=
  #v[0x7843976043fe783a, 0xef68f2bbd0ecce1a, 0x5bc26c191ddd2e4d, 0x8ea77be58e33bd4e, 0x93751434df6facf1, 0xb337be7d126cd94f, 0xc9828324909e0194, 0x7194efb1e6f783b1, 0x5e7e9479cf065766, 0x359a92be4a9b2a93, 0xef08d30e932971e, 0xaaabb2d689d59102, 0x769ca6ed0619cc22, 0xfc1833b3672ce4a5, 0x17ebd1f558d4c0d7, 0x5b888f5e2f56056a, 0x7807e25330630389, 0x61afd8318effcc4, 0x19c282e2ab17dcff, 0x9ad8b193e5fc57bb, 0xb091ae835ae3686e, 0x5895b0f75f462e00, 0xbd30684e52b7b88f, 0x6f843cdddf5d67c5, 0x1cf5ea1ed61644e5]

private theorem rounds150_0 : sixRounds 0 (by decide) absorbed150 = quarter150_1 := by
  decide +kernel

private def quarter150_2 : Vector UInt64 25 :=
  #v[0xae84acea2d910e08, 0x853dff8877bcaae9, 0x4aa3f42112229245, 0xec9f89fcb39ee4b2, 0x56335cb261711350, 0xfb2199f54c22cb86, 0xf85095dedb9c4a38, 0x95ae3d7066011435, 0x778c2837f73927be, 0x137ea16f571eb6dd, 0x438b952cbe1568c2, 0xdd5ee7c247006a56, 0xcaa433aab7f85320, 0x3332ea36d87e24e, 0xae060658603abeb6, 0xfa99782a25538ebd, 0x2c8f5245e39ceb13, 0x33349e3ff405f830, 0x64690e61125fb771, 0x52bf174e7406edaa, 0xf1b92c1fa001cb4b, 0xea9c51c62f1e6c6b, 0x5b75419c70910f06, 0x6008e855cade36da, 0xa409de8141099511]

private theorem rounds150_1 : sixRounds 6 (by decide) quarter150_1 = quarter150_2 := by
  decide +kernel

private def quarter150_3 : Vector UInt64 25 :=
  #v[0xee029e8ff118ddd1, 0xfd585bb74ad97b34, 0x2c7caa61ea2ce6c5, 0x6f8f60a08f96ba4b, 0xbb7e6a6d9c0f3e33, 0x55e117057c23ad3a, 0xc793f3fe08564723, 0x6a83eefe161847bf, 0x2825d514940ce749, 0x56e84e8114ae2b68, 0x5ab7a3e6a43ef4d4, 0xbc9994b7d1dc6a7d, 0x96c832173c93ba67, 0xb788953ba3e440e8, 0xdf38f3cc644df624, 0xa66f3400db16de1e, 0xff6b230b607dcc8d, 0x8c619de39edc3ad4, 0x463af9730d35e845, 0xfca44342add5dadd, 0xe80163769da85155, 0x7c9632da0f0674ae, 0xc50123e211854bf1, 0xd816c70f29f51c2b, 0x5afdb668be82acc]

private theorem rounds150_2 : sixRounds 12 (by decide) quarter150_2 = quarter150_3 := by
  decide +kernel

private theorem rounds150_3 : sixRounds 18 (by decide) quarter150_3 = state151 := by
  decide +kernel

private theorem perm150 : KECCAK.f1600 absorbed150 = state151 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds150_0, rounds150_1, rounds150_2, rounds150_3]
  rfl

theorem block150 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes150 ++ tail) state150 =
      KECCAK.Bytes.run 0 tail state151 := by
  exact run_block_of_step bytes150 tail absorb150 state150 absorbed150
    state151 (fun _ => rfl) words150 perm150

private def absorb151 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x72 0x64 0x64 0x61 0x20 0x6f 0x72 0x65)) 1 (by decide) (UInt64.ofBytes 0x75 0x63 0x73 0x65 0x52 0x73 0x73 0x65)) 2 (by decide) (UInt64.ofBytes 0x65 0x6e 0x20 0x3a 0x65 0x6c 0x62 0x61)) 3 (by decide) (UInt64.ofBytes 0x65 0x75 0x63 0x73 0x65 0x72 0x20 0x77)) 4 (by decide) (UInt64.ofBytes 0x65 0x68 0x74 0x20 0x73 0x69 0x20 0x72)) 5 (by decide) (UInt64.ofBytes 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a 0x20)) 6 (by decide) (UInt64.ofBytes 0x61 0x69 0x46 0x73 0x73 0x65 0x72 0x64)) 7 (by decide) (UInt64.ofBytes 0x20 0x3a 0x6e 0x65 0x6b 0x6f 0x54 0x74)) 8 (by decide) (UInt64.ofBytes 0x6f 0x6d 0x61 0x20 0x74 0x6e 0x69 0x6d)) 9 (by decide) (UInt64.ofBytes 0x20 0x74 0x6f 0x6e 0x20 0x74 0x6e 0x75)) 10 (by decide) (UInt64.ofBytes 0x20 0x72 0x65 0x74 0x61 0x65 0x72 0x67)) 11 (by decide) (UInt64.ofBytes 0x52 0x45 0x30 0x20 0x6e 0x61 0x68 0x74)) 12 (by decide) (UInt64.ofBytes 0x61 0x72 0x74 0x20 0x3a 0x30 0x32 0x43)) 13 (by decide) (UInt64.ofBytes 0x6d 0x61 0x20 0x72 0x65 0x66 0x73 0x6e)) 14 (by decide) (UInt64.ofBytes 0x63 0x78 0x65 0x20 0x74 0x6e 0x75 0x6f)) 15 (by decide) (UInt64.ofBytes 0x6c 0x61 0x62 0x20 0x73 0x64 0x65 0x65)) 16 (by decide) (UInt64.ofBytes 0x74 0x61 0x69 0x46 0x65 0x63 0x6e 0x61))

private def absorbed151 : Vector UInt64 25 :=
  #v[0xf2d3d61414e7035d, 0x616dbcffb19df4a6, 0xb6ad7543f4176498, 0x5e6ada190e4497f0, 0xea0f883d76a88c18, 0xa9a4e9737b3ad3f5, 0xa8f57d922da618ce, 0x867ad0fe52eddec, 0x528a71be23fb78ea, 0x3a0d2494ea4944ad, 0xff30f8363737fd73, 0x45fdf287f6b8450d, 0xb987c219b57d4fc9, 0xaf628e98fe0ac12e, 0xb88dc461166acbb0, 0xd6215f9c565ee3c4, 0xe26354a94a46299e, 0x5082a679e9bbbe74, 0x5fbbbb779ab50ee2, 0x7d0c12d024eaf6bc, 0xca6a5d6dab539730, 0x448c5a8f76a4c551, 0xd9329dcf395b4f6e, 0x14b65e8a20836968, 0xd9365a6d4ead8156]

private theorem words151 : absorb151 state151 = absorbed151 := by
  decide +kernel

private def quarter151_1 : Vector UInt64 25 :=
  #v[0xcbc327420aed9c9b, 0xa0d560f61e5508b1, 0x99c6a9caf999d902, 0xf42cdc78961a961a, 0xda92d62fc8ff709, 0xfea11183bbb40a22, 0x991cfd57b7e69372, 0xcee95f2bcbcb010a, 0x818fa9193aef3f33, 0xe33415562d0b4d32, 0xb62d7c4600be02a3, 0x5a1d7cf985699841, 0xb681cb193b21f7dc, 0xce4e6c831d9f879e, 0x40548fee47e899ec, 0x33922ccdb0dca76a, 0x8942fad83937721f, 0xcc2a112b05d3d856, 0x4ebe7b622e26f9, 0x25c38dff5ef01947, 0xcc1c734331fa081, 0xbf9b0a416026b926, 0xef2d416874c4d478, 0x166b2a39e0739453, 0x8558399ff448ea76]

private theorem rounds151_0 : sixRounds 0 (by decide) absorbed151 = quarter151_1 := by
  decide +kernel

private def quarter151_2 : Vector UInt64 25 :=
  #v[0x6209fba11d551c7c, 0xc64b7bc594e0a137, 0x8e558c6ef9626de9, 0x6fdf95a0b86dd155, 0x5815b0d07fd20cf7, 0xa79d2780985ddb91, 0xa66b2c032a98d81f, 0x6f3573ce57cf05ab, 0xba68ef4ecf46861a, 0xb87bc8e7b588e9e5, 0xabb009ea1888f8d2, 0xc284ca979718ead0, 0xc90aae7ca26a78e1, 0x1c29e0e816dbbada, 0xb15efd94ff257759, 0x9444a3e3f92ad6dc, 0xb1f8602c04b6e2f3, 0x992b0b991d329750, 0xfac72a6407a133ad, 0x7122f10f278f9bd5, 0x92c6c23f86adef0d, 0xc96b0473f3a5ec3f, 0xfa53b42d547d6400, 0xb00252f54036ba9d, 0x66f555c630944bfb]

private theorem rounds151_1 : sixRounds 6 (by decide) quarter151_1 = quarter151_2 := by
  decide +kernel

private def quarter151_3 : Vector UInt64 25 :=
  #v[0x7be92129abb45ad7, 0x7f1d1b03308d008, 0x8519fd7027d0e77, 0x5b5766db8cbfca4f, 0xc59e6c4643e03ec, 0x4d805497cf64ecfc, 0xc3673cd19d9a2380, 0xfa012a48f7e113a1, 0x85ad3e070a2b98b, 0x8b1cb8641e9f7968, 0x1c94643034412e39, 0xac83a55236140630, 0xfef5f73ef42dd00e, 0x8f1a2c0f8be72e0e, 0x1fa3e079c60b88d1, 0xf724f24a64ac5c30, 0x40fa288e32544771, 0xafe63603ec17df13, 0x452ecc981ffd95b9, 0x9fd51afffac01bd5, 0xc7cd27af6472c34a, 0x2c40cebc3c7f688d, 0xb7681c5f05176de, 0xd12e9787c6b4a9e7, 0xb9bc51acfbaa438c]

private theorem rounds151_2 : sixRounds 12 (by decide) quarter151_2 = quarter151_3 := by
  decide +kernel

private theorem rounds151_3 : sixRounds 18 (by decide) quarter151_3 = state152 := by
  decide +kernel

private theorem perm151 : KECCAK.f1600 absorbed151 = state152 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds151_0, rounds151_1, rounds151_2, rounds151_3]
  rfl

theorem block151 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes151 ++ tail) state151 =
      KECCAK.Bytes.run 0 tail state152 := by
  exact run_block_of_step bytes151 tail absorb151 state151 absorbed151
    state152 (fun _ => rfl) words151 perm151

private def absorb152 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x63 0x20 0x3a 0x6e 0x65 0x6b 0x6f 0x54)) 1 (by decide) (UInt64.ofBytes 0x73 0x69 0x20 0x72 0x65 0x6c 0x6c 0x61)) 2 (by decide) (UInt64.ofBytes 0x65 0x68 0x74 0x20 0x74 0x6f 0x6e 0x20)) 3 (by decide) (UInt64.ofBytes 0x4d 0x72 0x65 0x74 0x73 0x61 0x6d 0x20)) 4 (by decide) (UInt64.ofBytes 0x61 0x6c 0x42 0x72 0x65 0x74 0x6e 0x69)) 5 (by decide) (UInt64.ofBytes 0x62 0x61 0x74 0x73 0x69 0x6c 0x6b 0x63)) 6 (by decide) (UInt64.ofBytes 0x6c 0x6c 0x61 0x63 0x20 0x3a 0x65 0x6c)) 7 (by decide) (UInt64.ofBytes 0x6f 0x6e 0x20 0x73 0x69 0x20 0x72 0x65)) 8 (by decide) (UInt64.ofBytes 0x6c 0x62 0x20 0x65 0x68 0x74 0x20 0x74)) 9 (by decide) (UInt64.ofBytes 0x65 0x74 0x73 0x69 0x6c 0x6b 0x63 0x61)) 10 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x72)) 11 (by decide) (UInt64.ofBytes 0x6e 0x72 0x75 0x62 0x20 0x3a 0x6e 0x65)) 12 (by decide) (UInt64.ofBytes 0x20 0x74 0x6e 0x75 0x6f 0x6d 0x61 0x20)) 13 (by decide) (UInt64.ofBytes 0x20 0x73 0x64 0x65 0x65 0x63 0x78 0x65)) 14 (by decide) (UInt64.ofBytes 0x46 0x65 0x63 0x6e 0x61 0x6c 0x61 0x62)) 15 (by decide) (UInt64.ofBytes 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69)) 16 (by decide) (UInt64.ofBytes 0x72 0x65 0x6c 0x6c 0x61 0x63 0x20 0x3a))

private def absorbed152 : Vector UInt64 25 :=
  #v[0x387c8f0aa658c6e2, 0xe873112030c87080, 0x1ad19e3e9755743f, 0xcb367ea60b458be6, 0x56f516d8b2719b22, 0xc21285b2168c423, 0xa18c1b40ab122fb5, 0x30c916b9288d6a8b, 0xd3518c3d25c3e48b, 0xcba0c37587d4ca69, 0x8037c4ff2cff8d40, 0x6f453cafc137200c, 0x2933185b3f9d3e95, 0x69949520678ae15e, 0xda41132d31aeb1fc, 0xb0dbde36e4b928dd, 0xb1f0c4e4ba9dfe21, 0x86d9290f62869ac1, 0x32d0cdb88d0b1b37, 0xa15fb942de8d49c5, 0x2fbddaf127c9f0a2, 0x463a8ae403ab4d3d, 0x8fba30ca8f702afd, 0xa35fd913c50279e2, 0x5555845209820a35]

private theorem words152 : absorb152 state152 = absorbed152 := by
  decide +kernel

private def quarter152_1 : Vector UInt64 25 :=
  #v[0x1d32ace4cfe39c9, 0xa8294a79af938b69, 0x578589c2e881a0e5, 0x540191267bebb351, 0xd7d84c87b51fdc82, 0x4f3234e2c941f387, 0x3541b40cf8dc733, 0xa7a989d4faf0e060, 0xb8d3d7c83d09f74a, 0x546e0d238adc87ee, 0xf350020a39dc8b69, 0xdbe836939b2c6390, 0xb2963847f9ccdfd9, 0xce755465c3ca0336, 0xe3aec7e72faf9e82, 0xbefff45c1035e57c, 0xed65f8bf71b718d0, 0xbc82c8db3e89ea41, 0xb350545ebca1145f, 0x991dc984c78d307a, 0xb22f746c74162338, 0x358371ccfa1bbe4f, 0x16696304b611fbaa, 0xf448b54e24c28c45, 0x302a48ac279a3b8c]

private theorem rounds152_0 : sixRounds 0 (by decide) absorbed152 = quarter152_1 := by
  decide +kernel

private def quarter152_2 : Vector UInt64 25 :=
  #v[0x13b38fce484c932b, 0xfd1b25ba61527aa9, 0xcbfc2a67fc112cc0, 0x974951161974104d, 0xa84bc89e0e0f5c34, 0xb572433575e0da38, 0xa16da1772c9f0833, 0x3f5b5d1f39a1e0fd, 0xf4370406abc50077, 0xfff8ebfbaffaa555, 0x75f36e310334efa6, 0x881571f81a4b8532, 0x4864d2c1c9be922e, 0x3c9b663a2d2e0870, 0xd7faff6c0b329dfd, 0xff983edf2fad250f, 0x5378888a2016d55c, 0x2a2fafd1c1c1e385, 0xf1600f2e65947f2a, 0x5112178f63fd4895, 0x50ec3e2ca3d7707c, 0x133be393e862b551, 0x967f247f60408fa7, 0x26f8d34777ff10a6, 0xf363c72652bdd3dc]

private theorem rounds152_1 : sixRounds 6 (by decide) quarter152_1 = quarter152_2 := by
  decide +kernel

private def quarter152_3 : Vector UInt64 25 :=
  #v[0x72bbac577d0d6fc7, 0x23972b483e851d0e, 0xba3da1a213afbbb8, 0x4ddfa1d0616bf4a, 0x802031695b3b54a6, 0x73fe5b1274b034b9, 0x25c2357725301cc2, 0x24fc3f5b12080aac, 0x707edf31e228514f, 0x7cb2449a1002a3b, 0xdec0d25d1bf577e1, 0x3ca7e795c7dae060, 0xd21dce12984afed5, 0x6361019d42ef6903, 0x365cc4fd09c615ff, 0x28e3a5f05ba13a1c, 0xff26a98834cd9ff6, 0x3676b2b0c5517e3a, 0x8282ecfe45cf15ee, 0x1737d73d1162e94c, 0xac3f596c282b9020, 0xcf4ae5668bc7264, 0x7beae48ef88a66df, 0x791f3490e9a3acd6, 0x593e1109079a974d]

private theorem rounds152_2 : sixRounds 12 (by decide) quarter152_2 = quarter152_3 := by
  decide +kernel

private theorem rounds152_3 : sixRounds 18 (by decide) quarter152_3 = state153 := by
  decide +kernel

private theorem perm152 : KECCAK.f1600 absorbed152 = state153 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds152_0, rounds152_1, rounds152_2, rounds152_3]
  rfl

theorem block152 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes152 ++ tail) state152 =
      KECCAK.Bytes.run 0 tail state153 := by
  exact run_block_of_step bytes152 tail absorb152 state152 absorbed152
    state153 (fun _ => rfl) words152 perm152

private def absorb153 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x20 0x74 0x6f 0x6e 0x20 0x73 0x69 0x20)) 1 (by decide) (UInt64.ofBytes 0x72 0x65 0x74 0x6e 0x69 0x6d 0x20 0x61)) 2 (by decide) (UInt64.ofBytes 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46)) 3 (by decide) (UInt64.ofBytes 0x6d 0x20 0x77 0x65 0x6e 0x20 0x3a 0x6e)) 4 (by decide) (UInt64.ofBytes 0x6e 0x69 0x4d 0x72 0x65 0x74 0x73 0x61)) 5 (by decide) (UInt64.ofBytes 0x74 0x20 0x73 0x69 0x20 0x72 0x65 0x74)) 6 (by decide) (UInt64.ofBytes 0x20 0x6f 0x72 0x65 0x7a 0x20 0x65 0x68)) 7 (by decide) (UInt64.ofBytes 0x52 0x73 0x73 0x65 0x72 0x64 0x64 0x61)) 8 (by decide) (UInt64.ofBytes 0x65 0x6c 0x62 0x61 0x75 0x63 0x73 0x65)) 9 (by decide) (UInt64.ofBytes 0x72 0x65 0x6c 0x6c 0x61 0x63 0x20 0x3a)) 10 (by decide) (UInt64.ofBytes 0x20 0x74 0x6f 0x6e 0x20 0x73 0x69 0x20)) 11 (by decide) (UInt64.ofBytes 0x63 0x73 0x65 0x72 0x20 0x65 0x68 0x74)) 12 (by decide) (UInt64.ofBytes 0x30 0x32 0x43 0x52 0x45 0x72 0x65 0x75)) 13 (by decide) (UInt64.ofBytes 0x66 0x73 0x6e 0x61 0x72 0x74 0x20 0x3a)) 14 (by decide) (UInt64.ofBytes 0x6e 0x75 0x6f 0x6d 0x61 0x20 0x72 0x65)) 15 (by decide) (UInt64.ofBytes 0x64 0x65 0x65 0x63 0x78 0x65 0x20 0x74)) 16 (by decide) (UInt64.ofBytes 0x61 0x77 0x6f 0x6c 0x6c 0x61 0x20 0x73))

private def absorbed153 : Vector UInt64 25 :=
  #v[0xa3ec94d50f69146f, 0xbfae98a2b9f68cca, 0xbb454634d5301992, 0x1bf4f5b50bf5544f, 0x93ab1a568ddaf934, 0xc3241a7b486b35ad, 0xe4302b086af441b, 0xcef2f55276253788, 0x5408e3626edd2aa0, 0x669a0d1a18672b0d, 0xe158e255615346c7, 0x108f4856f6d09382, 0xb1b64ee02dabe2a9, 0xed7a795abb770654, 0x59066e3fd540f2f2, 0x20a00d19b6d3d8c7, 0x627e8d4de088a988, 0x187b2d9f7c43e9ff, 0xf4686e2fa3eb9368, 0x6058ee75ec721847, 0xd8e93082e21069c5, 0x75a2f73a21820153, 0x67170a1c6ba9b970, 0x9e911e96c8b1b475, 0xa5e69c0a1641db16]

private theorem words153 : absorb153 state153 = absorbed153 := by
  decide +kernel

private def quarter153_1 : Vector UInt64 25 :=
  #v[0xf98cf59a3f88dbae, 0xf0c7bee70dacc554, 0x6e0c697484e09e84, 0x12c12e64db83e3ef, 0xb14f53251d70a4, 0xeed3180e8b5589da, 0xc1e20c70039acf7f, 0x138d49353eeb9bd8, 0x4a7b8366a795268f, 0x4fd360703a9dd8d4, 0x13b550cbe2bff406, 0x9d08c3fe134a7885, 0xc216ece5a067d040, 0xef7a8cf8b4901aef, 0xa28fad7e459d2693, 0xfde90781b3c1f336, 0x75f2709b87fc2261, 0x6c3facdd11461b04, 0x2746d24d83397856, 0xa4942e51101ba5c9, 0x2d000df2bc54259b, 0xd507c796af83b888, 0xa82b09a165de26c3, 0x98ef50b5dea6009e, 0x5f46e649a11ade35]

private theorem rounds153_0 : sixRounds 0 (by decide) absorbed153 = quarter153_1 := by
  decide +kernel

private def quarter153_2 : Vector UInt64 25 :=
  #v[0x50262f38e27e9a55, 0x974d150154a84537, 0xb7f5ce3196fc4563, 0xd996d7ab1809f9fe, 0x631d3af7ead0d5bf, 0xd3ffc0f6c9438deb, 0x1e4651203549ff07, 0xf05c0ee57cb30869, 0x25f3e19bb6868e3b, 0xd665e997fa87a012, 0xee7312ab58e6c20b, 0xd38b4e2b84b3e9b6, 0x5802f476fe6508ef, 0x16fb3021eb397ff1, 0xc00b6444c60a5f8a, 0x3daf6acb6b8f0e6a, 0xa3f2251da4c278b4, 0xd4c0102c265c98da, 0x873d5d3d9cdb1f00, 0x7fa3fe1cd54b676d, 0xa5f39c6d1cd31ad6, 0xb8b93062df2e1c2d, 0xbcb7e17af123f485, 0xae6acb8fa5fccf7f, 0xb79da4d415f80496]

private theorem rounds153_1 : sixRounds 6 (by decide) quarter153_1 = quarter153_2 := by
  decide +kernel

private def quarter153_3 : Vector UInt64 25 :=
  #v[0x11d2380c1204e6d5, 0xa99afc11f477b8f0, 0x1e3c9ce75e141ef5, 0x3d50897507064423, 0xc65387538756636f, 0x3305d4761e4c493, 0x153adc5dd45a9708, 0x374449a4fb6bb611, 0xa29c0c63f2498e4d, 0x462a40ad6270ebbc, 0xa7271b682fd54d7b, 0x22372b608375f7e4, 0x92a596de7d3e71fe, 0x8deae47f501a9f40, 0xf857f3de69532690, 0x1da15cb0b953ed74, 0x800fa52f9be276b5, 0xf262d4dae0399ac8, 0x3a7b1b9803555df2, 0xac2d1e33f1b641df, 0x3758c9dc36e722b6, 0xd6fa2942631fd557, 0xc1e4c6d81f77f8bd, 0x8740f6840ee390ab, 0xaa75cb9c0e002245]

private theorem rounds153_2 : sixRounds 12 (by decide) quarter153_2 = quarter153_3 := by
  decide +kernel

private theorem rounds153_3 : sixRounds 18 (by decide) quarter153_3 = state154 := by
  decide +kernel

private theorem perm153 : KECCAK.f1600 absorbed153 = state154 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds153_0, rounds153_1, rounds153_2, rounds153_3]
  rfl

theorem block153 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes153 ++ tail) state153 =
      KECCAK.Bytes.run 0 tail state154 := by
  exact run_block_of_step bytes153 tail absorb153 state153 absorbed153
    state154 (fun _ => rfl) words153 perm153

private def absorb154 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x54 0x74 0x61 0x69 0x46 0x65 0x63 0x6e)) 1 (by decide) (UInt64.ofBytes 0x65 0x6e 0x20 0x3a 0x6e 0x65 0x6b 0x6f)) 2 (by decide) (UInt64.ofBytes 0x6c 0x6b 0x63 0x61 0x6c 0x62 0x20 0x77)) 3 (by decide) (UInt64.ofBytes 0x73 0x69 0x20 0x72 0x65 0x74 0x73 0x69)) 4 (by decide) (UInt64.ofBytes 0x72 0x65 0x7a 0x20 0x65 0x68 0x74 0x20)) 5 (by decide) (UInt64.ofBytes 0x73 0x65 0x72 0x64 0x64 0x61 0x20 0x6f)) 6 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x73)) 7 (by decide) (UInt64.ofBytes 0x61 0x63 0x20 0x3a 0x32 0x56 0x6e 0x65)) 8 (by decide) (UInt64.ofBytes 0x73 0x75 0x6d 0x20 0x72 0x65 0x6c 0x6c)) 9 (by decide) (UInt64.ofBytes 0x65 0x68 0x74 0x20 0x65 0x62 0x20 0x74)) 10 (by decide) (UInt64.ofBytes 0x69 0x46 0x65 0x65 0x79 0x61 0x70 0x20)) 11 (by decide) (UInt64.ofBytes 0x3a 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61)) 12 (by decide) (UInt64.ofBytes 0x63 0x61 0x72 0x74 0x6e 0x6f 0x63 0x20)) 13 (by decide) (UInt64.ofBytes 0x72 0x6c 0x61 0x20 0x73 0x69 0x20 0x74)) 14 (by decide) (UInt64.ofBytes 0x69 0x6e 0x69 0x20 0x79 0x64 0x61 0x65)) 15 (by decide) (UInt64.ofBytes 0x64 0x65 0x7a 0x69 0x6c 0x61 0x69 0x74)) 16 (by decide) (UInt64.ofBytes 0x74 0x20 0x3a 0x30 0x32 0x43 0x52 0x45))

private def absorbed154 : Vector UInt64 25 :=
  #v[0xc99f593310c9de5f, 0x169a1c3a22994340, 0x954c1b6f624b8bcc, 0x4566b07072202c13, 0xc73e79b0b12d978, 0x1735f16a1bbe9bd7, 0x6eb6904b689c2a28, 0x41309e75a3126322, 0x51912e83cf753254, 0xe93c7e03e440b08e, 0xe08f3612615a1a3f, 0x5e76250dbc46511d, 0x8feb8a7939da4318, 0x56b86bddb4575d29, 0x3d6bba617b3d852, 0x297da51416ebe92c, 0xaa1eceb5cdb3ecec, 0x8990077c611f3cae, 0xb8186fd4b7c80f92, 0x1f666e25a3f87cdb, 0x6ef79aedb97259c5, 0x2a2bd0749669c2c5, 0xa917bccbe25c6861, 0x89d59a6a862cae17, 0xca661bb407559213]

private theorem words154 : absorb154 state154 = absorbed154 := by
  decide +kernel

private def quarter154_1 : Vector UInt64 25 :=
  #v[0x4b793c4648b4abb, 0xdeb33e57bc6b7578, 0xced9a33361580347, 0x5e5d8187f1609558, 0xba7849c801e45814, 0xf326c5674821328f, 0x7bbaee018baa76c0, 0xa7e350993109ff15, 0x8e44c2caa01f4ba7, 0xe49bc5b966754dd5, 0xb1e4230d85c11778, 0x2a67e483aea5d8f, 0x84e58fbf866ad07b, 0x97cf2fefb5d12f40, 0xa59e5b0d90afee11, 0x5e2a52c5aa01019d, 0x502676aa55c09699, 0xd5ee983ca3e913df, 0xd2ce0a266001a3cb, 0x6555a886eddfc7, 0x90026ffdefb2b669, 0x3d64b13b2a27da, 0xe69ab5136dafde19, 0x58401cb9ad36c8fb, 0x6d29009a2fdd3995]

private theorem rounds154_0 : sixRounds 0 (by decide) absorbed154 = quarter154_1 := by
  decide +kernel

private def quarter154_2 : Vector UInt64 25 :=
  #v[0xf90a44a135e7fc52, 0x8d686c82cef6f28, 0xeafeb22de08ae918, 0x68b7c0cc45eca321, 0x23b29333623eb075, 0xdbc9c6a7b6d539bc, 0x722b7da16f74219e, 0x407d978f4e6dab67, 0x438de7b33b708bb5, 0x7a0d204d14392e28, 0x6d4917843bb335e, 0xd9a5680b2748ad15, 0xfd75f1ca5e40b3ce, 0x5ccd8f6afb1c0820, 0xd7f6504e89a4571d, 0x47b44fe6b6ff3f75, 0x87512516c1f749ca, 0x99aae6dc71550f24, 0x80d5e37f981021ad, 0x7524587b7dc35403, 0x82715271224a5dc, 0x411be288ab00fbfc, 0x5bf48ec8cac9da35, 0xcaee21328d3c6fa9, 0x666f307c2f1009e3]

private theorem rounds154_1 : sixRounds 6 (by decide) quarter154_1 = quarter154_2 := by
  decide +kernel

private def quarter154_3 : Vector UInt64 25 :=
  #v[0xab83e110e3ceee72, 0xb6ccb8000cbd60f7, 0x13c366350ffac9f1, 0xf3df5b835c9a3d1, 0x451e3a3540246b61, 0xbd2548dd957a387d, 0xa591ae785e7c66d3, 0x108bbadc0545b1ea, 0x80e773572c433634, 0x426baace14b295b0, 0x76a66e90cf2de6a4, 0x321563bddc16c3fc, 0x89d1c816984451ed, 0xbbe09b762b93b40a, 0xcb370ad540a4376b, 0xa3e92becc6906a2f, 0xf068afcb702538bf, 0xcdcb23c996037dda, 0xfcdad8a4406b3e1b, 0xd4845c97cd084d75, 0x6c782446bb87ed3c, 0x46d39fb9db2c0f92, 0x7e3034ef87cd2d8f, 0x4d8ca8d06c3f8c2d, 0x66c9517f53343768]

private theorem rounds154_2 : sixRounds 12 (by decide) quarter154_2 = quarter154_3 := by
  decide +kernel

private theorem rounds154_3 : sixRounds 18 (by decide) quarter154_3 = state155 := by
  decide +kernel

private theorem perm154 : KECCAK.f1600 absorbed154 = state155 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds154_0, rounds154_1, rounds154_2, rounds154_3]
  rfl

theorem block154 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes154 ++ tail) state154 =
      KECCAK.Bytes.run 0 tail state155 := by
  exact run_block_of_step bytes154 tail absorb154 state154 absorbed154
    state155 (fun _ => rfl) words154 perm154

private def absorb155 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x20 0x72 0x65 0x66 0x73 0x6e 0x61 0x72)) 1 (by decide) (UInt64.ofBytes 0x65 0x68 0x74 0x20 0x6d 0x6f 0x72 0x66)) 2 (by decide) (UInt64.ofBytes 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a 0x20)) 3 (by decide) (UInt64.ofBytes 0x43 0x52 0x45 0x73 0x73 0x65 0x72 0x64)) 4 (by decide) (UInt64.ofBytes 0x72 0x70 0x70 0x61 0x20 0x3a 0x30 0x32)) 5 (by decide) (UInt64.ofBytes 0x6d 0x6f 0x72 0x66 0x20 0x65 0x76 0x6f)) 6 (by decide) (UInt64.ofBytes 0x72 0x65 0x7a 0x20 0x65 0x68 0x74 0x20)) 7 (by decide) (UInt64.ofBytes 0x73 0x65 0x72 0x64 0x64 0x61 0x20 0x6f)) 8 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x73)) 9 (by decide) (UInt64.ofBytes 0x74 0x6e 0x69 0x6d 0x20 0x3a 0x6e 0x65)) 10 (by decide) (UInt64.ofBytes 0x20 0x74 0x6e 0x75 0x6f 0x6d 0x61 0x20)) 11 (by decide) (UInt64.ofBytes 0x20 0x73 0x64 0x65 0x65 0x63 0x78 0x65)) 12 (by decide) (UInt64.ofBytes 0x6c 0x41 0x72 0x65 0x74 0x6e 0x69 0x6d)) 13 (by decide) (UInt64.ofBytes 0x50 0x65 0x63 0x6e 0x61 0x77 0x6f 0x6c)) 14 (by decide) (UInt64.ofBytes 0x3a 0x65 0x6c 0x62 0x61 0x73 0x75 0x61)) 15 (by decide) (UInt64.ofBytes 0x20 0x72 0x65 0x6c 0x6c 0x61 0x63 0x20)) 16 (by decide) (UInt64.ofBytes 0x74 0x20 0x74 0x6f 0x6e 0x20 0x73 0x69))

private def absorbed155 : Vector UInt64 25 :=
  #v[0x3570119b976a8e72, 0xbfe30d0c0366670d, 0x1df607b0cd09ef, 0xbab2058ccc3ff5ab, 0x5aa27abf05e8f98c, 0x87c31cad69523f12, 0x80b1b12b17ab06a2, 0xa311a569841219c3, 0xa6a8b795d96a485c, 0xb762f3f245854891, 0xa218f40afbe10565, 0x5d51d344ca47b0f7, 0x2c8b94bb605ec7e0, 0xd424c63408242497, 0x80bbbeb8fa820ca6, 0x3eb54b4883753c78, 0x8f51b960668b8353, 0x61ee565e2863b8af, 0xc5dc6e8b8957ce51, 0x7f5ac6d15bae7bb3, 0xadcd143326251152, 0x4175b1049bd95428, 0x310207ae4d4ecd1f, 0x8b21c0d6fc2e9804, 0x88b0cf76002d93a3]

private theorem words155 : absorb155 state155 = absorbed155 := by
  decide +kernel

private def quarter155_1 : Vector UInt64 25 :=
  #v[0xef0c545a1b8fa85b, 0xc6321b7bb640716, 0xd8b82d333b92bbf4, 0xa9fb34ec0e9fed51, 0x8488e66a4a9083d7, 0x7879655ef4d2f13a, 0xc31d6f8eefcaa6a3, 0x2e2aabe844742a8f, 0x6d3b08b5a2ccfe64, 0x6d59f41b6b2fe9d, 0xfb0d69d26ce9765e, 0x87e7069fef5fe585, 0x2fd4a76b994456c4, 0xbf349033193431e8, 0xed0cecfc01edb8fe, 0x8ad7c661e1e11e4e, 0x62184858d7763ff3, 0x2fae9b0f6c6eae7e, 0x52021d254a0cf08e, 0x4ce0c34854c33117, 0x12f1ccfa970ff54f, 0x721d700fcad7f5ee, 0xad1c1ec5d47220e3, 0x33ab568b3ffa5773, 0x464369fc4576dec]

private theorem rounds155_0 : sixRounds 0 (by decide) absorbed155 = quarter155_1 := by
  decide +kernel

private def quarter155_2 : Vector UInt64 25 :=
  #v[0xab2e8540c4719f65, 0x3ec0f5e6d4b21640, 0x278c44c0474b7b26, 0xfc3e0967e8f91a0e, 0x1a7cd544d0cbc0aa, 0x83b3828d09f8d654, 0x4b97e8f6925a1cf7, 0xf3d9b9b4e7146430, 0x5a555664b483f0ce, 0xa135ae43e4fb59e3, 0xfd1f34edd9cdaa6b, 0x15157a8f767fdd74, 0xc7c8a1cad94c94a8, 0x40927ee3da5bb067, 0x7f3f631701157189, 0x3d4d9fc8693bb02d, 0xe72a25f37fd52470, 0x12ba0cd7d917288b, 0xdaba9250ccb6edf0, 0x12296994cffdff3f, 0x27c2d6ca7f9c9fcb, 0xcc166d74e86f10c, 0x7b644878d3a94898, 0xec9e3dc604179e81, 0x3817c2ab0cae2bb7]

private theorem rounds155_1 : sixRounds 6 (by decide) quarter155_1 = quarter155_2 := by
  decide +kernel

private def quarter155_3 : Vector UInt64 25 :=
  #v[0xc856140f4fea01f6, 0xe33a87955e0e684, 0x7b760f6fc2ac1d44, 0x5db17257bfa8430a, 0x9c660681bff37ac8, 0xa484c98b01c17529, 0xa27e528373c12334, 0x755dd3b2f8d04aed, 0x6e9162749e46df3f, 0xd3a62e34caa27226, 0x1d019262f0643597, 0x8a309dfc98a0a42b, 0xf48cdd3eb34afad8, 0x4aa3961a63f9c773, 0xe69f7954b81057d8, 0x4d725c6622f93928, 0x4438311d452f83ea, 0x469e1347b9dd04f, 0x4f50a5652119f5a0, 0x218b084a556beb30, 0x68f14e1915221e5e, 0x700f8519dda02c4d, 0x70be251a7fbb386e, 0x72959131a75ae635, 0x8eb4e6ecf89f4794]

private theorem rounds155_2 : sixRounds 12 (by decide) quarter155_2 = quarter155_3 := by
  decide +kernel

private theorem rounds155_3 : sixRounds 18 (by decide) quarter155_3 = state156 := by
  decide +kernel

private theorem perm155 : KECCAK.f1600 absorbed155 = state156 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds155_0, rounds155_1, rounds155_2, rounds155_3]
  rfl

theorem block155 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes155 ++ tail) state155 =
      KECCAK.Bytes.run 0 tail state156 := by
  exact run_block_of_step bytes155 tail absorb155 state155 absorbed155
    state156 (fun _ => rfl) words155 perm155

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
