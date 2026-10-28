import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb006 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x9f 0xd9 0x35 0x63 0x80 0x57 0x41 0x5)) 1 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0x2d 0x7 0x61 0x14 0x35)) 2 (by decide) (UInt64.ofBytes 0x5e 0x7 0x61 0x14 0x15 0xe5 0x44 0x36)) 3 (by decide) (UInt64.ofBytes 0x63 0x80 0x5b 0x56 0x4c 0x3 0x61 0x57)) 4 (by decide) (UInt64.ofBytes 0xb5 0x4 0x61 0x14 0x45 0x0 0xb6 0x2a)) 5 (by decide) (UInt64.ofBytes 0x14 0xd5 0xaf 0x92 0x30 0x63 0x80 0x57)) 6 (by decide) (UInt64.ofBytes 0xad 0x30 0x63 0x80 0x57 0xe8 0x4 0x61)) 7 (by decide) (UInt64.ofBytes 0x61 0x57 0x1b 0x5 0x61 0x14 0x1f 0xf8)) 8 (by decide) (UInt64.ofBytes 0x16 0x18 0x63 0x80 0x5b 0x56 0x4c 0x3)) 9 (by decide) (UInt64.ofBytes 0x80 0x57 0x2a 0x3 0x61 0x11 0xdd 0xd)) 10 (by decide) (UInt64.ofBytes 0x4 0x61 0x14 0xdd 0xd 0x16 0x18 0x63)) 11 (by decide) (UInt64.ofBytes 0x66 0x52 0x89 0x1a 0x63 0x80 0x57 0x35)) 12 (by decide) (UInt64.ofBytes 0x23 0x63 0x80 0x57 0x3d 0x4 0x61 0x14)) 13 (by decide) (UInt64.ofBytes 0x57 0x72 0x4 0x61 0x14 0xdd 0x72 0xb8)) 14 (by decide) (UInt64.ofBytes 0x6 0x63 0x80 0x5b 0x56 0x4c 0x3 0x61)) 15 (by decide) (UInt64.ofBytes 0x57 0x51 0x3 0x61 0x14 0x3 0xde 0xfd)) 16 (by decide) (UInt64.ofBytes 0x61 0x14 0xb3 0xa7 0x5e 0x9 0x63 0x80))

private def absorbed006 : Vector UInt64 25 :=
  #v[0x3dfca6b0057b7710, 0x230679236ebf0993, 0xfb416f8acfeb5460, 0x5d9812634a56cca1, 0x27c41980e573e18e, 0xa2adea590db27c95, 0xe95d4c3f956dac18, 0x2915974f5e3550f6, 0x38ea4cdf12d0be10, 0x567135ff60320b22, 0x70f786a25d95e151, 0x5ed168447da972ab, 0x8f16f38ed52c831c, 0x71b22b8eca60adfe, 0xa850f594bd7f6208, 0x1953fd31b51de17, 0xbbe6dae70f89ca7f, 0xd455cca7ba897bf9, 0xd94ca3691d6d7f5b, 0x462c20e31defb91, 0x5a43d0c2ef6ccd8f, 0xb2f82834636eb0d8, 0x6eb770891672d714, 0x6f4bc69c794b3bc, 0x8c71c28eed5dcd64]

private theorem words006 : absorb006 state006 = absorbed006 := by
  decide +kernel

private def quarter006_1 : Vector UInt64 25 :=
  #v[0x18988bc8f4e1e7d3, 0xc02110ac51fc5358, 0x67bed1182da1acd, 0x3d1f70fbb89b5770, 0xc4c3fbe62c801434, 0xd3ea7792faea25fb, 0xdae423bd97e0961a, 0x49d2597b1e4e762c, 0xfbb839dec87576c4, 0xaf92f1a41f6c2e07, 0x5e8c22c01e95b239, 0x17a57c498be7ac10, 0xf859f2299d38b096, 0x2c0eb1b914364523, 0xcc7d3ec268a90380, 0xef6678a502fd8445, 0x33431e452b2d0a70, 0x1f3b03d4a1075dcd, 0x6944f1dd03281a98, 0x3ef0a56e2e77cb52, 0x8ff091e0eba9e904, 0x68e3b0a9ab77f843, 0x53c0b1a0f6922537, 0x9543c1b129748f17, 0xe26eed9b7ce9278e]

private theorem rounds006_0 : sixRounds 0 (by decide) absorbed006 = quarter006_1 := by
  decide +kernel

private def quarter006_2 : Vector UInt64 25 :=
  #v[0xbebb66b1f2989187, 0xeb81aa20b905fe15, 0x21d213ab386f8f89, 0xfe9bc542e5e090c2, 0xb665477242c7c147, 0xb66d57fcad213a46, 0x7e5ec887ba49130c, 0xd097f60e996a78e3, 0xd15535362d552539, 0x223cc4281c857a57, 0xe0d2fc9f0cc8471b, 0xb80296c86901cb52, 0x6fae6201b13055e6, 0xb5d0f8e69fae51e6, 0x1ac9a0850362271f, 0x4b96ce2c087b4d7, 0xcdd127c006ecd5af, 0xfe52bfbdba4d3805, 0x337eb6e1f7abf832, 0x985f0bda68a5de02, 0x11f8d49ee25d50a, 0x7fcdd0f4b23e10c8, 0xaa72904c549217cb, 0x21e4f8558ace3e7c, 0x1f1edd54e3213d46]

private theorem rounds006_1 : sixRounds 6 (by decide) quarter006_1 = quarter006_2 := by
  decide +kernel

private def quarter006_3 : Vector UInt64 25 :=
  #v[0x6a89c22cbbd37c30, 0x6db0846c5f97d288, 0xf5dc7cc2ac900e1d, 0x1e040785ea69df25, 0x27fa6342ee801e35, 0xf45a7197e64c2f16, 0x600bbfe1511256ae, 0xb44f6886a0f068a4, 0x8709edb48a2d4c1c, 0x92db782f38ca1bd0, 0x33a154ec396db2bf, 0x19d3c0761f87cdfd, 0x9c3e28f1074ec7a0, 0xcd1177f1825e3bc5, 0x55c0f42f9e997168, 0xc8a1020602ee2e25, 0x3b0ca9b46cb2b443, 0x18e8ee749087acd3, 0xab99e31d0302aaf7, 0xee97d49dfce84a6a, 0x21b6593c1ad5e999, 0x991f8aaf035397a4, 0x8edb76dd88f93830, 0x58ec15938bf90841, 0x1d83af078ababfd3]

private theorem rounds006_2 : sixRounds 12 (by decide) quarter006_2 = quarter006_3 := by
  decide +kernel

private theorem rounds006_3 : sixRounds 18 (by decide) quarter006_3 = state007 := by
  decide +kernel

private theorem perm006 : KECCAK.f1600 absorbed006 = state007 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds006_0, rounds006_1, rounds006_2, rounds006_3]
  rfl

theorem block006 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes006 ++ tail) state006 =
      KECCAK.Bytes.run 0 tail state007 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes006 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb006 ws)) := by
    rfl
  exact (step state006).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words006).trans perm006))

private def absorb007 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xb4 0xc8 0x10 0x63 0x80 0x57 0xce 0x3)) 1 (by decide) (UInt64.ofBytes 0x60 0x5b 0x57 0x1b 0x4 0x61 0x14 0x4)) 2 (by decide) (UInt64.ofBytes 0x61 0x59 0x3 0x61 0x5b 0xfd 0x80 0x0)) 3 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x5b 0x56 0xaa 0xe)) 4 (by decide) (UInt64.ofBytes 0x81 0x51 0x83 0x52 0x82 0x80 0x20 0x60)) 5 (by decide) (UInt64.ofBytes 0x83 0x92 0x91 0x51 0x83 0x52 0x1 0x83)) 6 (by decide) (UInt64.ofBytes 0x90 0x1 0x85 0x91 0x1 0x83 0x90 0x92)) 7 (by decide) (UInt64.ofBytes 0x81 0x83 0x5b 0x0 0x60 0x83 0x83 0x80)) 8 (by decide) (UInt64.ofBytes 0x81 0x81 0x57 0x93 0x3 0x61 0x15 0x10)) 9 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x1 0x82 0x83 0x51 0x1)) 10 (by decide) (UInt64.ofBytes 0x50 0x50 0x5b 0x56 0x7b 0x3 0x61 0x1)) 11 (by decide) (UInt64.ofBytes 0x90 0x1 0x81 0x90 0x50 0x90 0x50 0x50)) 12 (by decide) (UInt64.ofBytes 0xc0 0x3 0x61 0x15 0x80 0x16 0x1f 0x60)) 13 (by decide) (UInt64.ofBytes 0x1 0x60 0x51 0x80 0x3 0x82 0x80 0x57)) 14 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x3 0x20 0x60 0x83)) 15 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x16 0x19 0x3)) 16 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x92 0x50 0x5b 0x50 0x91))

private def absorbed007 : Vector UInt64 25 :=
  #v[0x96dfe509161658e9, 0x2afb21835c2ce178, 0xa557f4fa9adc387b, 0xcf4c807a1ecd0bb8, 0xdf33dfefda953566, 0x9f92ba045b22fd27, 0xf5a6a311ced298d2, 0x894e20c6808d750d, 0x62ed8e3eef42e063, 0x10cfda629482309a, 0x938e5280855b0ffe, 0x68b1d88caa5c35cd, 0x20fa39808e9913b1, 0x8090d2142596e0e3, 0x1f329e11d1ce8045, 0x84ea6524d57c5f9c, 0xdf48bc6405f1d743, 0x10547ddb1ada9f82, 0xff7a02a947139600, 0x7ac9c6a232f0dc18, 0x2b1ac03df015e730, 0x9e8cba9ffeb4787a, 0xacf22e8b3b36428a, 0x237feba1a9e8617e, 0x8fda468bd47d0940]

private theorem words007 : absorb007 state007 = absorbed007 := by
  decide +kernel

private def quarter007_1 : Vector UInt64 25 :=
  #v[0xba46b33ebba77688, 0xbed1e79c595251e6, 0x88bc0a400f2cb6a7, 0xb96ca97526377e64, 0xdbf27a1ab18eba54, 0x37c90a2b88ec69f1, 0x26cc86dc90f83193, 0xa39bb52f52b09731, 0x951683d2d6f9ed4, 0xfe753899b850a9eb, 0xfd8d9a857607e58f, 0x303f8a18ab1732d, 0x359fde3b487a8f1c, 0xeb11b21e6d9db6d7, 0x51e1724f1a968687, 0x48389ecfb12b0787, 0x8c0299b45b414ff9, 0x329f9e5f15479f97, 0x3cb07dc3f1b55782, 0xd6fc1736089aaa1, 0xd40d6673007b57b7, 0xe0e08d33de7c2439, 0xd966af92b6cb2272, 0x9d56b71f3534f5dc, 0x142e106339d6638d]

private theorem rounds007_0 : sixRounds 0 (by decide) absorbed007 = quarter007_1 := by
  decide +kernel

private def quarter007_2 : Vector UInt64 25 :=
  #v[0x1d2dd8a85570d987, 0xafa7358e63ecf185, 0x64dbc7b55d4cd186, 0xce3abe45ed5a510f, 0xbb8608c3695c0a3a, 0xfe0850f7e79154c4, 0x762902eb98fc9f81, 0x25733b763701b891, 0x44fb605cdabe82cd, 0x9c33184a1bb1942e, 0x79f6d7138efb32f, 0x7dcc598ae4c02e32, 0x7219be1a63750ca, 0x45cd640f6399eabd, 0x89ac51e0f8f735dd, 0xa5c5fdec2c5d0054, 0xdff40d051bcf90f1, 0x40ade3d153f1ba44, 0x2e0a349b0ab16dc0, 0xac100c3db907c7bd, 0xed5a220cc234817c, 0x23ae1ba782b5a14a, 0xf10e525eb25acffe, 0x1ede42421cf7e5a0, 0x2921d370e095e25e]

private theorem rounds007_1 : sixRounds 6 (by decide) quarter007_1 = quarter007_2 := by
  decide +kernel

private def quarter007_3 : Vector UInt64 25 :=
  #v[0xf63c8259931f863e, 0xe23849845486de3d, 0xc8b4a7eb27be0956, 0x17741e88c63852a8, 0x2251e9f7d2abbbb3, 0xd7f111674f09042c, 0x611915cef4f99139, 0x414ff087d1b6dec, 0xc1ce463528c82921, 0x2a0778f8960a0f12, 0xd3caefa1b17f031e, 0x5ba4a86a5cbe4328, 0xd2bcf9a53ec917f2, 0xe50fcac175e61cad, 0xc27909e88134d70c, 0x9dfc932a089bed1a, 0x364129d0ff27d71a, 0x1c5f1e457e568571, 0x9878b43aa443f472, 0xda2e84972d8d847f, 0xb1d73fc7e98b2731, 0xe74278e75f832e85, 0xe2199dcd7ef69602, 0x2875f6e237c79c8d, 0xc164e6649aff60c9]

private theorem rounds007_2 : sixRounds 12 (by decide) quarter007_2 = quarter007_3 := by
  decide +kernel

private theorem rounds007_3 : sixRounds 18 (by decide) quarter007_3 = state008 := by
  decide +kernel

private theorem perm007 : KECCAK.f1600 absorbed007 = state008 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds007_0, rounds007_1, rounds007_2, rounds007_3]
  rfl

theorem block007 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes007 ++ tail) state007 =
      KECCAK.Bytes.run 0 tail state008 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes007 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb007 ws)) := by
    rfl
  exact (step state007).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words007).trans perm007))

private def absorb008 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xf3 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 1 (by decide) (UInt64.ofBytes 0x36 0x80 0x4 0x60 0x7 0x4 0x61 0x5b)) 2 (by decide) (UInt64.ofBytes 0x3 0x61 0x15 0x10 0x81 0x40 0x60 0x3)) 3 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0xe4)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x16 0x35 0x81 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x56 0xf 0x61 0x35 0x1 0x20 0x60 0x90)) 8 (by decide) (UInt64.ofBytes 0x15 0x91 0x51 0x80 0x40 0x60 0x5b 0x56)) 9 (by decide) (UInt64.ofBytes 0x3 0x90 0x81 0x90 0x51 0x52 0x82 0x15)) 10 (by decide) (UInt64.ofBytes 0x4 0x61 0x5b 0xf3 0x90 0x1 0x20 0x60)) 11 (by decide) (UInt64.ofBytes 0x40 0x60 0x5b 0x56 0xe3 0x10 0x61 0x23)) 12 (by decide) (UInt64.ofBytes 0x81 0x90 0x51 0x52 0x82 0x91 0x51 0x80)) 13 (by decide) (UInt64.ofBytes 0x5b 0xf3 0x90 0x1 0x20 0x60 0x3 0x90)) 14 (by decide) (UInt64.ofBytes 0x5b 0x56 0x7 0x11 0x61 0x23 0x4 0x61)) 15 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x70 0x4 0x61)) 16 (by decide) (UInt64.ofBytes 0x53 0x4 0x61 0x15 0x10 0x81 0x20 0x60))

private def absorbed008 : Vector UInt64 25 :=
  #v[0x7d264b3ef7d50dda, 0x9e24cf39e18e2a6b, 0xc1e32151f0388e7b, 0xe1a98d4aca616240, 0xad21de174b38933e, 0xfa4f3038e56b7ccf, 0x46644e8872fd4815, 0xecd1a4f081629da8, 0xcac30199d6e512f, 0xc0eb582e31be0cb3, 0xe1e8ead55b9def49, 0xd4bdbe01c4bb94b1, 0xb5b42aa77e062099, 0xd47eb7b671ad4323, 0xd060b293a30cce0d, 0x5c9a5c46ed566a44, 0x338f9aa63a4f5ab, 0xe9acebc92790c07b, 0x7b2651614ac0563f, 0xa1e0a3ab4b7a498a, 0x3614767764e5313, 0x887fa2a01e9e94ac, 0x8fc3c73afff524e7, 0x32f2c054bf8f3e45, 0xedca4bb24c0f7e00]

private theorem words008 : absorb008 state008 = absorbed008 := by
  decide +kernel

private def quarter008_1 : Vector UInt64 25 :=
  #v[0x1ae9f68175daf837, 0xa8ca066c85283c26, 0xf275523a3220f801, 0xb6fa77afad1dac24, 0x4cba43785712bd72, 0x35503eea7d01e416, 0xe381381586e845f5, 0xdef04a25cc823850, 0xf5bbed927fb347ce, 0x656d12a3e4b6fa80, 0xaf46f90fb20d7b94, 0x3c04f0f1653095db, 0x1bc414e8342afc9d, 0x39c75ed80058d037, 0xab5681f50d2ebc0, 0xa4065b6ff12e89c6, 0x30439b3bb3f5277f, 0x85d98c6b1e49ce03, 0xe96b96905ea0a2dd, 0xbfdab2a8d23f31c1, 0x525b4be12bfc1658, 0xf8382df6116066d8, 0x39b7485fcf37e480, 0x1863bbcacc66916, 0x244d47c008740e6a]

private theorem rounds008_0 : sixRounds 0 (by decide) absorbed008 = quarter008_1 := by
  decide +kernel

private def quarter008_2 : Vector UInt64 25 :=
  #v[0xdefec3542ebb4e89, 0x4a2bf7cba4d9b8eb, 0x3a26468bb1ab66f5, 0x160bf0a473fdf371, 0x4423f76646d10b22, 0x94f398120d2671de, 0xd08800532052726a, 0xac67daf755f88378, 0xab96e6055d4c9e9c, 0x18e436e05d7e5f42, 0x1535324d999e2ab5, 0x65c6917fe70f9583, 0x7b5ad85be394e871, 0xda68fd8cf618b73d, 0xa38cae67cae292c3, 0x5a7f497b386fbbac, 0x2b880662ab560412, 0x428a386fdf7d5c33, 0x3f0e47d7ad6485d0, 0xa492ad8d2049a745, 0x384652cdb49ea43c, 0xd2c175d7a0f1e07b, 0x6ac7c94f32cfeb3e, 0xb450d99a497c7d, 0x8e108f61c0d2dd4f]

private theorem rounds008_1 : sixRounds 6 (by decide) quarter008_1 = quarter008_2 := by
  decide +kernel

private def quarter008_3 : Vector UInt64 25 :=
  #v[0x1199e1979ded7e49, 0x4e6448bd13b36e8a, 0x7d41189e08055395, 0xb04d9a96babfb42f, 0x25f7d67dfeb64d60, 0x9f3d046af35c9f25, 0xe2055b156bdeed89, 0x6a2dc0625cb28b49, 0x22f8011c8ab36cc0, 0x88030aa3a20079cf, 0x9fa7ebfbad32d509, 0xa3d23f642b7d0ea3, 0xabe74a3019b21570, 0xcfc45de39b8c4ccb, 0xf7ae257d166e1353, 0x4c19b9776b7802e7, 0xc1681af38a58527b, 0xcd02341907d6752a, 0x8aaa33ec1ad0708d, 0x32597cc85be1abfb, 0xaa37c129068cbe6d, 0x3c5f10b9313dc255, 0x13f1efe6d86e8b8c, 0x26e6145988270ced, 0xc7694b4a4dd755b6]

private theorem rounds008_2 : sixRounds 12 (by decide) quarter008_2 = quarter008_3 := by
  decide +kernel

private theorem rounds008_3 : sixRounds 18 (by decide) quarter008_3 = state009 := by
  decide +kernel

private theorem perm008 : KECCAK.f1600 absorbed008 = state009 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds008_0, rounds008_1, rounds008_2, rounds008_3]
  rfl

theorem block008 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes008 ++ tail) state008 =
      KECCAK.Bytes.run 0 tail state009 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes008 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb008 ws)) := by
    rfl
  exact (step state008).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words008).trans perm008))

private def absorb009 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x11 0x61 0x16 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x7 0x4 0x61 0x5b 0x0 0x5b 0x56 0xd)) 5 (by decide) (UInt64.ofBytes 0x81 0x60 0x60 0x3 0x36 0x80 0x4 0x60)) 6 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x88 0x4 0x61 0x15 0x10)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x50 0x5b 0xfd 0x80)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x20 0x60 0x91 0x16 0x81 0x35 0x81 0xff)) 11 (by decide) (UInt64.ofBytes 0x60 0x90 0x16 0x91 0x90 0x35 0x1 0x81)) 12 (by decide) (UInt64.ofBytes 0x5b 0x56 0xf1 0x11 0x61 0x35 0x1 0x40)) 13 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x70 0x4 0x61)) 14 (by decide) (UInt64.ofBytes 0xcb 0x4 0x61 0x15 0x10 0x81 0x20 0x60)) 15 (by decide) (UInt64.ofBytes 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73))

private def absorbed009 : Vector UInt64 25 :=
  #v[0xf929b9dac7b33ceb, 0x79e52fc62280bfd4, 0x4430729df2cbe4e0, 0x47b6690e80cb9afa, 0x914d723fec63e2, 0xbefd46dcb25c652, 0xe64ea1ce00c0d7e1, 0xad9e19189bcd9c77, 0x8e312d1940ce3986, 0x3062451a942af068, 0x27c257585fc0f5b6, 0xe9f2fd3197e0fd01, 0xa65c80aafcb2411, 0xac5e420da0c02bfa, 0x3717b2223dc6492e, 0xb192ce46a42b0394, 0xdf23bd44c6753023, 0xe7235e724cb6ca67, 0x8e7b32b5891ddbc5, 0x66a02a295d973c32, 0x6673a9a499b5c5f6, 0xcf811f997566108e, 0x2d0a98dbd1c22176, 0x1ab6255a62b83ea9, 0x63fb95c98a541055]

private theorem words009 : absorb009 state009 = absorbed009 := by
  decide +kernel

private def quarter009_1 : Vector UInt64 25 :=
  #v[0xbc40af8923a27f1d, 0x2fb6063fe04bce02, 0x63f48f23716c309c, 0x135b217ab752e0f4, 0xc310ab460e088fa3, 0xfa97c22154ed4408, 0x4a2029af516eeead, 0x833866faecc58ccb, 0xf0ecafc3d86105af, 0xca10929638de0ea5, 0xfbb06a7ba2f1f935, 0x83708800eb879022, 0xa45f22d6de2af8bb, 0xf9ec83a40d96bd24, 0x7bdc1be570d32aaa, 0x6d09a73b65648fcd, 0x1e58d5475e96d2e1, 0x85ffdc769e8b4b6e, 0x6571ae50d5d4a752, 0xc4d707c951608415, 0x460604840f960922, 0x5c4f2a89caf6c957, 0xc53cd71f4fe4d3f9, 0x1eddec792c108797, 0xfbf7605ba10e8eea]

private theorem rounds009_0 : sixRounds 0 (by decide) absorbed009 = quarter009_1 := by
  decide +kernel

private def quarter009_2 : Vector UInt64 25 :=
  #v[0xb90caabad326b940, 0x2a34a6f984f705f0, 0xbbd57ce17e494440, 0xa15e0988b805113a, 0xfe54c49b6cbecffa, 0xc5f5d45d1a8c4bd2, 0x6bec6bc0273ed2d7, 0xd3569ec1fc117c61, 0xb86c34c657cbe234, 0xc042c1d1003be0d3, 0x11e5595dc2e19398, 0xf1dba8cb22f04419, 0x2baf76c40ed1ef46, 0xc1a9016b00e12283, 0x875731dd990a40c9, 0x3ebe310d7b2b4141, 0x9356ede3d844af92, 0x2f642c2db5890682, 0xeb376df3c8555ab2, 0x95fcca3747f1f3c8, 0x470a10094ced8436, 0xe60828604afd5848, 0x965ec94e56e7a9f1, 0xedf6c06e6d70c4f3, 0xd87ce35d691e9098]

private theorem rounds009_1 : sixRounds 6 (by decide) quarter009_1 = quarter009_2 := by
  decide +kernel

private def quarter009_3 : Vector UInt64 25 :=
  #v[0x4557ad20fa8186d8, 0xf3aeca0e3ac8ca52, 0x79d5c887ffef2876, 0xf7e3ef76e4845b65, 0xa8fc3fffc5eeedf1, 0xb67f9cf4309a6290, 0x94c04e86a30ca9e2, 0xb8ab4d86d39ed4ac, 0x37b209156d11d314, 0x35d0b1a2dbb38f4d, 0x20224900d3c944b8, 0xaab146198a328a8a, 0x472e43db12ea0ace, 0x3354246f5a1e7c89, 0xeccf79b15a00e8fe, 0x3b10b96e2eaa3860, 0x2a9196eb58534176, 0x671e95cf424d148d, 0x223fafe375873107, 0x7314cce7380779c4, 0x9c12b4433178b562, 0x6e152614a044f12a, 0x49b7b4157b13e598, 0xa29bc8c00d37dcfc, 0x5f2c3f96ef0352e0]

private theorem rounds009_2 : sixRounds 12 (by decide) quarter009_2 = quarter009_3 := by
  decide +kernel

private theorem rounds009_3 : sixRounds 18 (by decide) quarter009_3 = state010 := by
  decide +kernel

private theorem perm009 : KECCAK.f1600 absorbed009 = state010 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds009_0, rounds009_1, rounds009_2, rounds009_3]
  rfl

theorem block009 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes009 ++ tail) state009 =
      KECCAK.Bytes.run 0 tail state010 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes009 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb009 ws)) := by
    rfl
  exact (step state009).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words009).trans perm009))

private def absorb010 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x14 0x61 0x16 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x4 0x60 0x7 0x4 0x61 0x5b 0x56 0xf7)) 3 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x20 0x60 0x3 0x36 0x80)) 4 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0xfe 0x4 0x61)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x35 0x50 0x5b)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x4 0x61 0x5b 0x56 0x58 0x16 0x61 0x16)) 9 (by decide) (UInt64.ofBytes 0x5 0x61 0x5b 0x56 0x51 0x17 0x61 0x23)) 10 (by decide) (UInt64.ofBytes 0x40 0x60 0x5b 0x56 0x75 0x17 0x61 0x2b)) 11 (by decide) (UInt64.ofBytes 0x82 0x16 0x92 0x90 0xff 0x60 0x51 0x80)) 12 (by decide) (UInt64.ofBytes 0x20 0x60 0x3 0x90 0x81 0x90 0x51 0x52)) 13 (by decide) (UInt64.ofBytes 0x60 0x70 0x4 0x61 0x5b 0xf3 0x90 0x1)) 14 (by decide) (UInt64.ofBytes 0x81 0x0 0x1 0x61 0x3 0x36 0x80 0x4)) 15 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x58 0x5 0x61 0x15 0x10)) 16 (by decide) (UInt64.ofBytes 0x20 0x60 0x90 0x1 0x81 0x5b 0xfd 0x80))

private def absorbed010 : Vector UInt64 25 :=
  #v[0x32c1ff9f8c52777d, 0x4614fcbed2d7ff87, 0xa22cdb83134b6f1a, 0x6e63bac542b9eb01, 0x2ab7d7d155f7c8a2, 0x4bfba482eafc1695, 0x3015a4cd924e0746, 0xe5df7b2b5c442d21, 0x85b50eb527ddab29, 0x2fa1f430e7007e19, 0xf140c67a9c2ca699, 0x8c70ea8629ba5b8e, 0x3504ccfb182ff88, 0x3638886490e4d3e3, 0x276e705f96a57d3f, 0x2b42ffdb84c19639, 0xda695147ee8ba337, 0xf1f339ce0bab6be0, 0xe6a20f6b4baaedcb, 0xdcfe6cfe20a55df7, 0x96d97c7d56d64cfa, 0x221727fbd6afecf2, 0xfa354296401ba941, 0xf5b025923f5bda26, 0xbf74e6726d877985]

private theorem words010 : absorb010 state010 = absorbed010 := by
  decide +kernel

private def quarter010_1 : Vector UInt64 25 :=
  #v[0x77fe85fe30509a04, 0x9da1f906cf867985, 0x4335b4c4f92b46f3, 0xb892b5d290bcdf66, 0xc942e6db62305eb6, 0x12a34b6148d6c8f4, 0x9938d3bf03ddf7e2, 0xdf40c0c0530968ea, 0xa2b63f44f541c9c6, 0x8fcaee002d5a7644, 0xd6f2a4f2dd7a9937, 0x170b2ef67ef41cb3, 0x921fc295c253bbb7, 0xfba950e878b3613c, 0xb24edc53e32d90a8, 0x1d0bf1708d5255e8, 0xae16608cf132a423, 0x79129b31178355b4, 0xb4d7fdfcb1cb4558, 0x5d8d6e20c61d7bf0, 0x3d3ee59d20a8cf5e, 0x392077f9e1cb3882, 0x954e36aa444e895f, 0xb8e78e590f64d6f, 0xb6c3c54cdb6154c9]

private theorem rounds010_0 : sixRounds 0 (by decide) absorbed010 = quarter010_1 := by
  decide +kernel

private def quarter010_2 : Vector UInt64 25 :=
  #v[0x7e7e9a4d2617be64, 0x8fe542b90683d512, 0x84724a9d4e2508c6, 0xb41399abd2ee801b, 0x42992891ad992816, 0xe10c54dc1ddd8204, 0xddc5618e6c14868d, 0x8bee62d6aeab2f8f, 0xffae7e282bcac4c, 0xb17c8332df2caac7, 0xd918793f065f8e0b, 0x1a82bfa0984e771f, 0x1dff8af28cdc1b5e, 0x22323edcfabc4141, 0x6a2c45527dcb5966, 0x225f44057485dad, 0x8f62a3dfa79057b1, 0x20d98793a5e2fc63, 0x1a1c3d263cf937a, 0x8454bdc2067b29df, 0x2b6a8eed490cfa60, 0x104d03c7fd37c9cf, 0xf6242f626328e9fd, 0xce4538d04e37fa48, 0x722a7977515a7291]

private theorem rounds010_1 : sixRounds 6 (by decide) quarter010_1 = quarter010_2 := by
  decide +kernel

private def quarter010_3 : Vector UInt64 25 :=
  #v[0xf5b676931de94154, 0xd8a66fb4d7531b61, 0x3908ed2fdd36aa9e, 0x961be9fead98c2d4, 0x2065777aa8e5d82e, 0x898776d17df2852c, 0xaf915c488d2d271c, 0xb10ff0685c2c136e, 0xd1e3c8af66bbc03a, 0x95c95430251c0baf, 0x4d1b7c89a71d21b0, 0xe0e6811f17ed1dff, 0x55ec1f1a7757e631, 0xa856b8556760692b, 0xa59062568695d80e, 0x243759073a9d429e, 0xbcc77fa0946edd2e, 0xd5a4c8dd9bc657cb, 0x5084518acc62390e, 0x4e1f284bad0446f0, 0x7fa3488cbcbf1581, 0x6a19e6551ec4e3b8, 0x80768a489f4c27b1, 0x9b8b9f9c24a7e95c, 0xdda54d8ae06e5805]

private theorem rounds010_2 : sixRounds 12 (by decide) quarter010_2 = quarter010_3 := by
  decide +kernel

private theorem rounds010_3 : sixRounds 18 (by decide) quarter010_3 = state011 := by
  decide +kernel

private theorem perm010 : KECCAK.f1600 absorbed010 = state011 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds010_0, rounds010_1, rounds010_2, rounds010_3]
  rfl

theorem block010 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes010 ++ tail) state010 =
      KECCAK.Bytes.run 0 tail state011 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes010 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb010 ws)) := by
    rfl
  exact (step state010).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words010).trans perm010))

private def absorb011 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x1 0x64 0x35 0x81 0x1 0x81)) 1 (by decide) (UInt64.ofBytes 0x73 0x5 0x61 0x15 0x11 0x81 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x1 0x82 0x5b 0xfd 0x80 0x0 0x60 0x57)) 3 (by decide) (UInt64.ofBytes 0x61 0x15 0x11 0x1 0x82 0x20 0x60 0x83)) 4 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x85 0x5)) 5 (by decide) (UInt64.ofBytes 0x84 0x91 0x1 0x20 0x60 0x90 0x35 0x80)) 6 (by decide) (UInt64.ofBytes 0x64 0x11 0x1 0x84 0x2 0x83 0x1 0x60)) 7 (by decide) (UInt64.ofBytes 0x17 0x11 0x83 0x0 0x0 0x0 0x0 0x1)) 8 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xa7 0x5 0x61 0x15)) 9 (by decide) (UInt64.ofBytes 0x1f 0x60 0x80 0x80 0x90 0x91 0x5b 0xfd)) 10 (by decide) (UInt64.ofBytes 0x60 0x2 0x4 0x91 0x80 0x20 0x60 0x1)) 11 (by decide) (UInt64.ofBytes 0x1 0x81 0x90 0x51 0x40 0x60 0x1 0x20)) 12 (by decide) (UInt64.ofBytes 0x90 0x91 0x92 0x93 0x80 0x52 0x40 0x60)) 13 (by decide) (UInt64.ofBytes 0x83 0x83 0x1 0x20 0x60 0x52 0x81 0x81)) 14 (by decide) (UInt64.ofBytes 0x1 0x92 0x0 0x60 0x37 0x84 0x82 0x80)) 15 (by decide) (UInt64.ofBytes 0x94 0x95 0x92 0x50 0x52 0x91 0x90 0x91)) 16 (by decide) (UInt64.ofBytes 0x35 0x50 0x93 0x1 0x81 0x20 0x60 0x93))

private def absorbed011 : Vector UInt64 25 :=
  #v[0xea15d82cb801d344, 0xfe04a749a868199, 0x492ccc19f3c618fb, 0xedbc7a141706757d, 0x802e953b0b4d0c78, 0x8028424e5da6a065, 0x7ba663f14d041089, 0x4f9cdaeb41da67d0, 0xb5eef31b1cea7221, 0xc27fe12ac7bfce4d, 0xb4b24c2339a69379, 0xb185f542efe27593, 0x87412b6e7578c894, 0xe962025684f6e06f, 0x351d30553a891ae8, 0x74ebde003a113ae3, 0x6529179e83e84c28, 0x90c96209b6048b0b, 0xdcb9097e3720f069, 0x54ce983a05093a5f, 0x1b4e874d0b01852d, 0x4962a2b40406cf58, 0xb98b4573bdb12f17, 0x3d86ac1c4b43bdb1, 0x4536ee8c6dcd2fd0]

private theorem words011 : absorb011 state011 = absorbed011 := by
  decide +kernel

private def quarter011_1 : Vector UInt64 25 :=
  #v[0x791f839e3205ba58, 0x2d5eba83ddc01f38, 0x7b68a60288c6d30, 0xe3681885e12d825d, 0xd6608ea97bf0e093, 0xe6bf33d1e1080765, 0x58016d8d22281e72, 0x261d6db3c8463f20, 0x16d54c9286173676, 0xeb76096e7722d833, 0xdc1cfd96747a0de7, 0x5769cf381edb1207, 0x1b241f286bfc2511, 0x7dec2a6e2101ff60, 0xcee2d2d33881050b, 0x76b9623d88e68661, 0xe2370ad65f68effd, 0xad826e22dc19eed4, 0x99051d0467d920a0, 0x2a653ae83c23be5d, 0xb4f424db393632cc, 0x5184ba51ec8fa358, 0xb89323f21611c28e, 0x193cd52a4d08e8a2, 0x877a15a93dbd11f6]

private theorem rounds011_0 : sixRounds 0 (by decide) absorbed011 = quarter011_1 := by
  decide +kernel

private def quarter011_2 : Vector UInt64 25 :=
  #v[0x948be53b974b39e6, 0x7f3b3e750b288826, 0xf48d6aca7d34769b, 0xbc8f17b8a54b7761, 0xfc57a99397b42259, 0x8435aada42bebe63, 0x7872bb96d77ea639, 0xd9e01f2b66251197, 0x1afb0380ddcb2ecc, 0x8bb6c61ecbc61bef, 0xd81aaf6fc18ef285, 0xb8d0edb148125c04, 0xac5d3388f78fa199, 0xb88d7e112b17aaa1, 0x5b20d3a9e3175fce, 0xf78f1f4433abd0f3, 0x96bf79a5fd0d1e5e, 0x8acb061428004b29, 0x9e76aa9be6d50872, 0x32e6da5c800c5c73, 0xbd58e6134bb05c39, 0xbd2149f14a9e1cc6, 0x7851857aa428959f, 0x971fe888789c582, 0x8714dcd2fe0a5b80]

private theorem rounds011_1 : sixRounds 6 (by decide) quarter011_1 = quarter011_2 := by
  decide +kernel

private def quarter011_3 : Vector UInt64 25 :=
  #v[0xba5ab9a5455486a2, 0x90f9cfee7e15354f, 0xa31e9f37b46878b9, 0x13d772b600966ec0, 0x9140d94a761d5b80, 0xa2f72b38903acf02, 0xe5696d6f6a85d61d, 0x1beb1516f657efa8, 0xff49418cce9e6cf5, 0xc0b9d84703043aa5, 0x5ba51a57916d30be, 0x6f9f15fa7e5acdeb, 0x428c79b8ada90588, 0xdd2a4c935a3d5ddc, 0x88835e496b82c2ac, 0x44c1ce353ea72104, 0xcdfa7cf97efef740, 0xb8c22a89accbdb48, 0x11ceeae5968c7dc, 0x869fd72361b110ed, 0x28536c0d6f440af0, 0xa18330bdfa860e1f, 0xafaa42790e5d58f2, 0x688b0ae5ab9e41b8, 0xb023f601b8fa4561]

private theorem rounds011_2 : sixRounds 12 (by decide) quarter011_2 = quarter011_3 := by
  decide +kernel

private theorem rounds011_3 : sixRounds 18 (by decide) quarter011_3 = state012 := by
  decide +kernel

private theorem perm011 : KECCAK.f1600 absorbed011 = state012 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds011_0, rounds011_1, rounds011_2, rounds011_3]
  rfl

theorem block011 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes011 ++ tail) state011 =
      KECCAK.Bytes.run 0 tail state012 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes011 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb011 ws)) := by
    rfl
  exact (step state011).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words011).trans perm011))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
