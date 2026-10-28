import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb12 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x91 0x1 0x20 0x60 0x52 0x81 0x16 0xff)) 3 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 4 (by decide) (UInt64.ofBytes 0x5 0x61 0x15 0x80 0x34 0x5b 0xf3 0x90)) 5 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0xe9)) 6 (by decide) (UInt64.ofBytes 0x5b 0x56 0x33 0x19 0x61 0xf2 0x5 0x61)) 7 (by decide) (UInt64.ofBytes 0x0 0x6 0x61 0x15 0x80 0x34 0x5b 0x0)) 8 (by decide) (UInt64.ofBytes 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 9 (by decide) (UInt64.ofBytes 0x81 0x3 0x36 0x80 0x4 0x60 0x3f 0x6)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x35 0x80 0x80 0x90 0x1)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x90 0x16 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x20 0x60 0x90 0x35 0x80 0x90 0x91 0x92)) 15 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x90 0x91 0x92 0x90 0x1)) 16 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x5b 0x56 0xd8 0x19 0x61))

private def absorbed12 : Vector UInt64 25 :=
  #v[0x8a3c4d12579d6e86, 0x616edeb60d678487, 0x13f363067e612d80, 0xe02f38f02d35f7d6, 0x4f3161b458aa66e9, 0x20afe2bb9243c9d2, 0x12b8a0f881ca61f8, 0x3a1ba514d8412cbd, 0x856d051c9507d0b5, 0xe5ed2c22618b04f6, 0x877a32ab3226156f, 0x728a85f5ea557800, 0x2daf41e52d840e56, 0x5a037987ee52a197, 0x37ec159ba4b7102, 0xc46603033b76f22f, 0x2aaa970aa1580d0c, 0x6bf072e1cf61df81, 0x2cd4e6aaffe010de, 0x1f9589af6b0f1a1b, 0x3540a43485a0d3bf, 0x4ce671853eabe72d, 0xdbe0065fddab0da2, 0xa0c31b3104371072, 0x4c2f667674efb4cf]

private theorem words12 : absorb12 state12 = absorbed12 := by
  decide +kernel

private def quarter12_1 : Vector UInt64 25 :=
  #v[0x696249fe0f6a9ec5, 0xc13e367ea2b0604f, 0x72c0b627b9f9e310, 0xc8b8bfb2815937aa, 0xb161622c1dd83ea8, 0xb5091f77dd0bf492, 0x1e3bab18373a32ee, 0x6c10ed197480eb5c, 0x93ebcbadb1e5ff56, 0xb14ab103aeee4eac, 0xdfadcacd68315e1f, 0xab27acf392ff9cd1, 0x4c654d8a6a75c7f0, 0xd5732f8185d63e82, 0xf379d8c5f6845a19, 0x42cc864f7e8def9a, 0x8abd0a6a66d36688, 0x5b0627e4f158ced9, 0x27b2f80225c1ad49, 0x3af3d4b1c39b9a34, 0x41b5dc38d1b83df7, 0xc61b4143541c83bb, 0x54beffd605a117ce, 0x9b3782ba8eb02bfc, 0x507d0e065ed61f4]

private theorem rounds12_0 : sixRounds 0 (by decide) absorbed12 = quarter12_1 := by
  decide +kernel

private def quarter12_2 : Vector UInt64 25 :=
  #v[0x763a62c6879b9ea, 0x45df6422441f65d0, 0xfbb029e33da90985, 0xe5b4dcdba301ce48, 0xde955e353877b22d, 0xb450408d6184216b, 0xa72dcf92cbdec98d, 0x4b07532e102ccae7, 0xf3af605251dad1d, 0x656f57a5c0fd0830, 0x8e05b6250247f77c, 0xc4b92a0c2b758e36, 0x212f9a77b11989a9, 0x8ff3df9f39192265, 0x3b67680533729227, 0x9c48a6009fd0bc0, 0x5ac209d4b28728bb, 0x7dcf9fb8cdb78eaa, 0xed49f29d5467afc8, 0x66b76a337347c802, 0xf8dafff6660c845b, 0x4053ffc95786d234, 0xb63899e2e0cd0988, 0xb97a9e80f890842, 0xe197c6c3c3149077]

private theorem rounds12_1 : sixRounds 6 (by decide) quarter12_1 = quarter12_2 := by
  decide +kernel

private def quarter12_3 : Vector UInt64 25 :=
  #v[0x8843684d70ff45a, 0x34333ad5e60e1063, 0xa4b06c73594a5fe6, 0x359a7d6cd4ca2b72, 0x482f7cc8dc8754f8, 0x17d5d8af6b56848d, 0x220211d9da95c068, 0x3d5798e17e9f2669, 0xfcf98ad6f878b8ed, 0xea2e4de893625964, 0xd5bfd741dd195642, 0x16138ae59b819121, 0x19aeb244c2bf950e, 0xceeaa9db17924b5, 0x331760da3f0505f3, 0xa2abe1712eb71187, 0xfe3879db179afd99, 0x750c3bdb777f1f29, 0x9a8b29bf5de2041c, 0xd212340e853faf52, 0x2df4eeae46cf42f4, 0x9394428f5c435066, 0x641248b4c550dff3, 0x7409a18dc569f946, 0xc5aaa184e04b5cbd]

private theorem rounds12_2 : sixRounds 12 (by decide) quarter12_2 = quarter12_3 := by
  decide +kernel

private theorem rounds12_3 : sixRounds 18 (by decide) quarter12_3 = state13 := by
  decide +kernel

private theorem perm12 : KECCAK.f1600 absorbed12 = state13 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds12_0, rounds12_1, rounds12_2, rounds12_3]
  rfl

theorem block12 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes12 ++ tail) state12 =
      KECCAK.Bytes.run 0 tail state13 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes12 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb12 ws)) := by
    rfl
  exact (step state12).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words12).trans perm12))

private def absorb13 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x81 0x15 0x15 0x15 0x15 0x82 0x80)) 1 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x20 0x60)) 2 (by decide) (UInt64.ofBytes 0x34 0x5b 0xf3 0x90 0x3 0x91 0x80 0x51)) 3 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x65 0x6 0x61 0x15 0x80)) 4 (by decide) (UInt64.ofBytes 0x60 0x84 0x6 0x61 0x50 0x5b 0xfd 0x80)) 5 (by decide) (UInt64.ofBytes 0x80 0x90 0x1 0x81 0x3 0x36 0x80 0x4)) 6 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x35 0x80)) 7 (by decide) (UInt64.ofBytes 0x7a 0x1d 0x61 0x50 0x50 0x50 0x90 0x91)) 8 (by decide) (UInt64.ofBytes 0x61 0x15 0x80 0x34 0x5b 0x0 0x5b 0x56)) 9 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x92 0x6)) 10 (by decide) (UInt64.ofBytes 0x36 0x80 0x4 0x60 0xd1 0x6 0x61 0x50)) 11 (by decide) (UInt64.ofBytes 0x73 0x35 0x80 0x80 0x90 0x1 0x81 0x3)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x20 0x60 0x90 0x16 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x90 0x35 0x80 0x90 0x91 0x92 0x90 0x1)) 16 (by decide) (UInt64.ofBytes 0x50 0x90 0x91 0x92 0x90 0x1 0x20 0x60))

private def absorbed13 : Vector UInt64 25 :=
  #v[0x6846aed8a432ce1b, 0x839287ae739b432, 0x2a94814891fb8878, 0x36e49690fd67f128, 0xe81d8952aadc8fce, 0x86fd0b9e7b0502fb, 0x633c67f1c59c0aa5, 0x143a156c1b9e6d4d, 0xa0b18a1cb64ec52, 0x772329a524f351b7, 0x8a60df2123fe976, 0x9626742f2224e9da, 0x96e8c40aec88b3c6, 0xb8129fdc0e25c4b, 0x10f37ee49f33de12, 0xa88033eb67f79a52, 0x9dbfd52a885e2132, 0x2038dedc5437602, 0xc40e19ea3b8dbcdf, 0xdc58a72a8eb9d9, 0xde92ed2078bbaaa7, 0x58cc60eb397c681e, 0x16dc0421e524ff24, 0xf81112e3e3f84831, 0xb5ee7f000f349d90]

private theorem words13 : absorb13 state13 = absorbed13 := by
  decide +kernel

private def quarter13_1 : Vector UInt64 25 :=
  #v[0xabcbf65e40aed19c, 0xf2f9f2224b537d1c, 0x4e1b5fe64600b941, 0x535e3023add54622, 0x29ed4270d1277a27, 0x1f217d8f584c842b, 0x6b0bac7828030af7, 0xcc02dcea665aaddc, 0xb0c495d692777219, 0xa1447049e07b0da5, 0xbeb6161843e2f9e4, 0x7089ba11dd5757ad, 0x1dac96df7835202f, 0x56491e7971f46dfb, 0xd11917ca9ee8eeb6, 0xc74853dcade0cdb2, 0x52c0990230b4ef77, 0x41d5b4f5be449244, 0xe96d28e69ac1f92f, 0x7a734778fb7bc99b, 0x1c749a7614125571, 0x44c5d7fb51ad9956, 0x7cb899d4c8c91a11, 0xc9050242020a071e, 0x1be05c6fb6062eaa]

private theorem rounds13_0 : sixRounds 0 (by decide) absorbed13 = quarter13_1 := by
  decide +kernel

private def quarter13_2 : Vector UInt64 25 :=
  #v[0xbc774c071ef8525d, 0xb93ed0afc2f6a8fe, 0x3e6312757747fa7a, 0x38f300eeef5812a3, 0x625ceb159daf8603, 0xacde468c6c30b343, 0x8d8013ac81c8c4de, 0x3f3e2bb6fd563e5f, 0x9b1d1c45b2b70a78, 0x1b307a2260482cc, 0x6370d6377ccd4258, 0xb2dd5a52cc2c8e5c, 0xb90b3471c523bbe1, 0xde2624658d4d03ff, 0x24d461fa3dfe9aa5, 0xfdad3d542b596c31, 0x5a2ea544b4fef1c5, 0xac3db873351320ba, 0x95e4b7e292972e4f, 0x630d4740604f0aad, 0x6ceda486f781e358, 0x69db3337d0d6c567, 0x80490e6a5e8e00cc, 0x429129dda1835274, 0xf53061f720669195]

private theorem rounds13_1 : sixRounds 6 (by decide) quarter13_1 = quarter13_2 := by
  decide +kernel

private def quarter13_3 : Vector UInt64 25 :=
  #v[0xb97fda008ec86cbf, 0x1a94f79bf383aee0, 0xa51d04229287dee2, 0xee1441473c44689a, 0xda99a39d9f7f0be, 0x1f798634b319d73d, 0x41d293ce0cc3d7d6, 0xa9e0d2fffd7b0532, 0x13c97637302322a6, 0x4fdd8cb1c0f06fd1, 0xbc41b91940a48166, 0xed76b67ebff9cb32, 0xb4888d6d75ef190b, 0xb3525f506360a05c, 0x54bd94b5d2e623f2, 0x9c6961fb87275666, 0x254b3d24fe4f7c8d, 0x77708dc012639d41, 0x44398d2c264f8e39, 0xf28d8f14d6c8bb03, 0x84fe31db31d7ada7, 0x43393ad29a6c8047, 0xc0f403c3b824a178, 0xaf0377a27517c062, 0x2955fc2a78c0a582]

private theorem rounds13_2 : sixRounds 12 (by decide) quarter13_2 = quarter13_3 := by
  decide +kernel

private theorem rounds13_3 : sixRounds 18 (by decide) quarter13_3 = state14 := by
  decide +kernel

private theorem perm13 : KECCAK.f1600 absorbed13 = state14 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds13_0, rounds13_1, rounds13_2, rounds13_3]
  rfl

theorem block13 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes13 ++ tail) state13 =
      KECCAK.Bytes.run 0 tail state14 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes13 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb13 ws)) := by
    rfl
  exact (step state13).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words13).trans perm13))

private def absorb14 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0xe1 0x1f 0x61 0x50 0x50)) 1 (by decide) (UInt64.ofBytes 0x15 0x15 0x15 0x15 0x82 0x80 0x51 0x40)) 2 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x20 0x60 0x52 0x81)) 3 (by decide) (UInt64.ofBytes 0xf3 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 4 (by decide) (UInt64.ofBytes 0x57 0xf7 0x6 0x61 0x15 0x80 0x34 0x5b)) 5 (by decide) (UInt64.ofBytes 0x7 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60)) 6 (by decide) (UInt64.ofBytes 0x1 0x81 0x3 0x36 0x80 0x4 0x60 0x2c)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x80 0x80 0x90)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 11 (by decide) (UInt64.ofBytes 0x4f 0x21 0x61 0x50 0x50 0x50 0x90 0x91)) 12 (by decide) (UInt64.ofBytes 0x61 0x15 0x80 0x34 0x5b 0x0 0x5b 0x56)) 13 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x3a 0x7)) 14 (by decide) (UInt64.ofBytes 0x56 0x75 0x22 0x61 0x43 0x7 0x61 0x50)) 15 (by decide) (UInt64.ofBytes 0x15 0x15 0x82 0x80 0x51 0x40 0x60 0x5b)) 16 (by decide) (UInt64.ofBytes 0x91 0x1 0x20 0x60 0x52 0x81 0x15 0x15))

private def absorbed14 : Vector UInt64 25 :=
  #v[0xebefcedcce5f0ff9, 0x2a51b99ea8eef3f6, 0xb8bfe2c5abb074fc, 0xf45bcd6e75d86f28, 0xd9a46c613dad01db, 0x4074b1401f6a8237, 0x1ccc7f967da8409c, 0x8315b2a26d13231d, 0x30aaf83b1a2d806f, 0x84d9b7086f5a5ce, 0xb1fbc8f21e581dd3, 0xe6d4d7e7725627e6, 0x7eaa16e00696b593, 0x4ef5209b5eb30a6a, 0x88f91a41e83b44d2, 0x5339f9b6446e5fc7, 0xe261f65a551ae77f, 0xbd2bed22a14fdfb5, 0x5a85bd8be039ccdf, 0x5c0cc0f23813d81d, 0xde38d1980dcd28a3, 0x5334e33c7f4341f0, 0x41c572bd833b6fd3, 0x2b9c4dbe3a4c4ceb, 0x419523b54014da1d]

private theorem words14 : absorb14 state14 = absorbed14 := by
  decide +kernel

private def quarter14_1 : Vector UInt64 25 :=
  #v[0x5803e498f0a3bea7, 0x50a3f026c505036d, 0x81d0b0a98db5cdd8, 0xc66372a96c8554f, 0xfa06e476cbd472b5, 0x391290c424cb5480, 0x4f5a2680e68b432b, 0x8388b78a7e472adb, 0x1a435189fae05095, 0x69314a999e87bc46, 0xe3f832d7b273e9e1, 0xc2c8af81dd9973d3, 0xc84f10bc823d74fa, 0xc0442d7f621ffb68, 0x5427d0a80460b912, 0xea7d0e72281b4bc9, 0x1c31f9d8d0bf7a77, 0x941dc34d3537e65e, 0x668331ec6c98bfd8, 0x244b2e8a0acb7b24, 0x1f294c8924204cfc, 0x5101f6ea0a705fdb, 0xf11e69039b9c1a13, 0xa0f60cc829f652f5, 0x1779a641f39f461b]

private theorem rounds14_0 : sixRounds 0 (by decide) absorbed14 = quarter14_1 := by
  decide +kernel

private def quarter14_2 : Vector UInt64 25 :=
  #v[0x8b9404598a20deeb, 0xe7a7d3b4ede980a1, 0xde9699470ae06129, 0x70eaa56af7d9fa5c, 0x856c3f02e675c50e, 0x3723899c8af51d7f, 0xd14efcb6719143f4, 0xb08fd736844cddf8, 0x25342164de3139ae, 0x2e3ae24d66935811, 0xfc3535c639f56d06, 0xa8eda7cf85775507, 0x32edb9ee1abd4f9c, 0x7ea796110caf21c0, 0xf5d56f50b8ba2bb7, 0xd2c8a9eb79696efa, 0x7171c032b7334bd0, 0xc2ea4c52284cc121, 0x2f1c2c0de4a9c364, 0xece36c97263cb815, 0x69c72ec176a1470a, 0xa5eb954e18265463, 0x744acc882dfd89b8, 0x2f3ec186b4ec9333, 0xcd4146ce655fc1c]

private theorem rounds14_1 : sixRounds 6 (by decide) quarter14_1 = quarter14_2 := by
  decide +kernel

private def quarter14_3 : Vector UInt64 25 :=
  #v[0x219c52529a6851d9, 0xc1e4850db79db9d9, 0xcc8313875f7972c7, 0x1697bc010313d4f8, 0x1de8e981aee7281e, 0x96d97c8594865e0a, 0x9ac9389f78a9601, 0xa17f8ed5b4c674d1, 0x419f505a3263df2b, 0x749b3ddbd7d728bc, 0x931330dcb9a074f8, 0xef0c670b2c61ec7b, 0x8745c5569c0ef586, 0x34f417b87dd44d3, 0x2a52040dcfcfbf11, 0x556b4e392fce6e36, 0xdd3d30749141a370, 0x2c229c6b92bb4580, 0x2b89367afdc368f5, 0x73323449532383a0, 0xd310d64e0dd126a2, 0x4a6febed18e8e3ab, 0x674039d61b8b0d81, 0x82fc58f76ca11c58, 0xad23f8c49c574f4d]

private theorem rounds14_2 : sixRounds 12 (by decide) quarter14_2 = quarter14_3 := by
  decide +kernel

private theorem rounds14_3 : sixRounds 18 (by decide) quarter14_3 = state15 := by
  decide +kernel

private theorem perm14 : KECCAK.f1600 absorbed14 = state15 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds14_0, rounds14_1, rounds14_2, rounds14_3]
  rfl

theorem block14 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes14 ++ tail) state14 =
      KECCAK.Bytes.run 0 tail state15 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes14 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb14 ws)) := by
    rfl
  exact (step state14).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words14).trans perm14))

private def absorb15 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 1 (by decide) (UInt64.ofBytes 0x7 0x61 0x15 0x80 0x34 0x5b 0xf3 0x90)) 2 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0x69)) 3 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x9e 0x7 0x61)) 4 (by decide) (UInt64.ofBytes 0xff 0x73 0x35 0x80 0x80 0x90 0x1 0x81)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x16 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x61 0x50 0x50 0x50 0x90 0x91 0x92 0x90)) 9 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x5b 0x56 0x88 0x22)) 10 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x20 0x60 0x52 0x81 0x82)) 11 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 12 (by decide) (UInt64.ofBytes 0xc0 0x7 0x61 0x15 0x80 0x34 0x5b 0xf3)) 13 (by decide) (UInt64.ofBytes 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 14 (by decide) (UInt64.ofBytes 0x0 0x5b 0x56 0xd1 0x22 0x61 0xc9 0x7)) 15 (by decide) (UInt64.ofBytes 0x57 0xd7 0x7 0x61 0x15 0x80 0x34 0x5b)) 16 (by decide) (UInt64.ofBytes 0x8 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60))

private def absorbed15 : Vector UInt64 25 :=
  #v[0x94b611a872def21, 0xfa88929dc8291507, 0x6ed7d8fb8c5fdf8b, 0xee50c519cfbc5076, 0xa4fd12aff1f826f1, 0xbcda25d7fb898143, 0x4921c88d816047cd, 0xf543b7cb2de4807f, 0xf38cb8fe9c6de434, 0x882adb4164b8ba7a, 0x63e6721e73ba0761, 0x65500469d5ada2b0, 0x7a0b3a76c2b4f018, 0xf356e045bad13b5e, 0x8b3c81e86b072251, 0x4df74be1174689a0, 0x110608c0278bee64, 0x493ddef5b0a9240f, 0xd06d7e7b944b43db, 0x866c407d280e20e6, 0xfde3a4693c912065, 0xf9e5e52e56dcf7b4, 0xa958e40beef89692, 0x6e34d2f8a781e935, 0xee5390538ea40223]

private theorem words15 : absorb15 state15 = absorbed15 := by
  decide +kernel

private def quarter15_1 : Vector UInt64 25 :=
  #v[0xc108821d3270d9a7, 0xe2602e4d493e41d8, 0xb403449adbfc7b8b, 0xb4b494ec59b26228, 0x4c47fe7135639107, 0xbe5f4653a77b18f8, 0xf351c5d54a08d174, 0x9a36fe6772f1ab6e, 0x2babd69de5c0c7eb, 0x10b2d22849566036, 0x7dcb7985bd6b81ad, 0x2a89ba407aa5687, 0xf6a0b23b24c83454, 0xc0f31ea85b0d43c2, 0x6efc4ba11819448a, 0xf96278cc0be4f9b6, 0x2d1cd6c42b313804, 0x452e9eae4088f043, 0x2493ea09f95256f6, 0xb287cd85281a33a1, 0xa48747ca77029586, 0x4c0f63462614384a, 0x90cdce0db2eec2f9, 0x1da7dc8ca18977ee, 0xc119919512099d20]

private theorem rounds15_0 : sixRounds 0 (by decide) absorbed15 = quarter15_1 := by
  decide +kernel

private def quarter15_2 : Vector UInt64 25 :=
  #v[0x4cbc046a7be59e4b, 0xf215b0a1b811f076, 0x467cc6c5ac6937f6, 0x5bebec78373a5a6c, 0x34d9f9c030a17743, 0x21a82614230d9525, 0xac12d6d467534a75, 0x33a1e57fa2d6c8d0, 0xcfb08b48662d5810, 0xd3343dca90e5c526, 0x9419dcccaf4de805, 0x67a9ce7d62dfa7f9, 0x11c4eba464b08b4f, 0x23d362956985a818, 0xd75eabcb153165fc, 0xda1120bec34f0751, 0x278531a1ff80b9da, 0x4d87af1de628e2fa, 0xfad13d7959db99d0, 0xdd664e0697b9b8da, 0x64c3e6a11ee807b6, 0x492f014c603fbd7d, 0xb7b25070b5d03016, 0x7676014cd3da230, 0xbdcd3837191da4c]

private theorem rounds15_1 : sixRounds 6 (by decide) quarter15_1 = quarter15_2 := by
  decide +kernel

private def quarter15_3 : Vector UInt64 25 :=
  #v[0x12dd52be4a60002b, 0x76b03f9dd2fcde80, 0x9d58a2e08252c2f9, 0xad4738493828fe85, 0xef305e10379da424, 0x22e4cf8d641c553e, 0xe669321e38af9a2b, 0x584b61087e6a2f91, 0x1efe1b3fadda9fab, 0x1a3edcdd6c1392b5, 0xea003e4c79523912, 0x96fe2b771d32f7ce, 0x3cc98860056a81c2, 0x262eaf658c904253, 0x27d92e9727ae9104, 0x793b54a7bd726364, 0x1f0a81bf6a258d5b, 0x5fb655763f5bf631, 0x499612332a57b46b, 0xf713a2975fc633e0, 0x3a30374e4d3ab7d1, 0x213dd00e53bdb603, 0xd86b28e6af28c3cd, 0x67e59ab619e83bb2, 0x75ab02ef283c1bb8]

private theorem rounds15_2 : sixRounds 12 (by decide) quarter15_2 = quarter15_3 := by
  decide +kernel

private theorem rounds15_3 : sixRounds 18 (by decide) quarter15_3 = state16 := by
  decide +kernel

private theorem perm15 : KECCAK.f1600 absorbed15 = state16 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds15_0, rounds15_1, rounds15_2, rounds15_3]
  rfl

theorem block15 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes15 ++ tail) state15 =
      KECCAK.Bytes.run 0 tail state16 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes15 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb15 ws)) := by
    rfl
  exact (step state15).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words15).trans perm15))

private def absorb16 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x81 0x3 0x36 0x80 0x4 0x60 0xc)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x80 0x80 0x90)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 5 (by decide) (UInt64.ofBytes 0x75 0x23 0x61 0x50 0x50 0x50 0x90 0x91)) 6 (by decide) (UInt64.ofBytes 0x81 0x82 0x80 0x51 0x40 0x60 0x5b 0x56)) 7 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x20 0x60 0x52)) 8 (by decide) (UInt64.ofBytes 0x5b 0xf3 0x90 0x3 0x91 0x80 0x51 0x40)) 9 (by decide) (UInt64.ofBytes 0x60 0x57 0x2e 0x8 0x61 0x15 0x80 0x34)) 10 (by decide) (UInt64.ofBytes 0x37 0x8 0x61 0x50 0x5b 0xfd 0x80 0x0)) 11 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x5b 0x56 0xbe 0x23 0x61)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x82 0x80)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed16 : Vector UInt64 25 :=
  #v[0xdc81e0c207b2b10e, 0xfa29a006ea7ff8b1, 0xa8575af9e5a5a5db, 0xad536a2819a73cdf, 0xf804e9da81fa5f78, 0x11f6ff53c87b6f34, 0x8383eef078374cd2, 0x148402b35c624c66, 0x2be4f8d9bc653a60, 0x3c7bd8a31e44b9d4, 0xd6921652fcf3f04f, 0xf4b3f4a6d2cc7544, 0x32ecdc887609d544, 0x8cae3e87a270156d, 0xc4d14bedc4f7593f, 0xd771e5b7e383b25b, 0x4db92375e7a04a36, 0xc1ae286799032f5, 0xd62806ae6518a010, 0x9c02b22e6b4eaae6, 0x770fb8f7c9d74d1d, 0xc7ace09abc66690f, 0xc514e037d2770940, 0x5820b5e72e044c78, 0xe69e670ece4781d6]

private theorem words16 : absorb16 state16 = absorbed16 := by
  decide +kernel

private def quarter16_1 : Vector UInt64 25 :=
  #v[0xc055209466e4e7c1, 0x4f21fabc83b4c7ae, 0xfde421d30dc21189, 0x759270a4c467fbf2, 0x1d0d3d58b5a3a3e9, 0x4c255ad6645e1f6f, 0x55a775318498ed96, 0x4fbfa943ae964889, 0xfe4158699e7876fb, 0x71da4705f68487d1, 0x5699cddc0ff69768, 0xc5693259a6d1369, 0x826593d74aa16288, 0x3c498a9a448d47ef, 0x74e2bbf75a6488c, 0x20437715487c0ed1, 0x4eee2596312a0234, 0xe36919718f1636d8, 0xc9879ba6aa4a2ea5, 0x475563cd645aa4bb, 0x8daf0414e02b7157, 0x979082670775fadf, 0xe3a51d254ca50da0, 0xb39d88ded2916743, 0x8cfd660b607a9bbc]

private theorem rounds16_0 : sixRounds 0 (by decide) absorbed16 = quarter16_1 := by
  decide +kernel

private def quarter16_2 : Vector UInt64 25 :=
  #v[0xb7755552d5040d1, 0x4d3c3a0ff438048d, 0xb0e308e2f0e701ee, 0xf4af5e535497b267, 0x6f3c19c88f48cfe4, 0xca0200ac383bfa25, 0xf773b98c7f91e245, 0x12936f7113a8e0c5, 0xf5d5d2a7a9ac9708, 0xbb4d666d284d5f37, 0x975018e51a1e270e, 0xdbcd709c1dab18e4, 0x7780f4ba379a3435, 0x9d98818db8675c04, 0x67e35747b003e6f9, 0x882bff4054476a19, 0x4a374cd655501c51, 0x9521af6141ca004b, 0x47710cff233141ca, 0x2122d249a25ff99e, 0x716dc8a64d90acce, 0xb3b23f92041127cf, 0xdde1f3db9b6995a7, 0xf6d765c2b1061f22, 0x44f672e002e2e696]

private theorem rounds16_1 : sixRounds 6 (by decide) quarter16_1 = quarter16_2 := by
  decide +kernel

private def quarter16_3 : Vector UInt64 25 :=
  #v[0x644253a774411d75, 0xca4fc29676c4f278, 0xcf8355d1c3458b71, 0xbc9df5c30aee4e8b, 0xe54fbc56b0be3889, 0x20f2bb868b684fad, 0x1d49f4adad95a2e7, 0xa3642ba0be2fbfc8, 0xe0ad6f26e2ce4e9e, 0xd9442b903f37e2c2, 0x8af214cf0c4082a3, 0x3ba777a9d53d71e5, 0xfcda7630645c350c, 0xb7ef0d096232f7a2, 0xe75f7fa136880064, 0xd127feacf0153498, 0x1b23e2a287552114, 0x66c2eee98530205f, 0x3f52c76b177b7ea3, 0xbed6336cc2d54a41, 0x51e85866af031356, 0x19104aa002f68759, 0x424df4396675b857, 0x34270081ff30b754, 0x79992c071d64504d]

private theorem rounds16_2 : sixRounds 12 (by decide) quarter16_2 = quarter16_3 := by
  decide +kernel

private theorem rounds16_3 : sixRounds 18 (by decide) quarter16_3 = state17 := by
  decide +kernel

private theorem perm16 : KECCAK.f1600 absorbed16 = state17 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds16_0, rounds16_1, rounds16_2, rounds16_3]
  rfl

theorem block16 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes16 ++ tail) state16 =
      KECCAK.Bytes.run 0 tail state17 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes16 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb16 ws)) := by
    rfl
  exact (step state16).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words16).trans perm16))

private def absorb17 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x20 0x60)) 2 (by decide) (UInt64.ofBytes 0x34 0x5b 0xf3 0x90 0x3 0x91 0x80 0x51)) 3 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x85 0x8 0x61 0x15 0x80)) 4 (by decide) (UInt64.ofBytes 0x61 0x8e 0x8 0x61 0x50 0x5b 0xfd 0x80)) 5 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x5b 0x56 0xe7 0x23)) 6 (by decide) (UInt64.ofBytes 0x82 0x3 0x81 0x82 0x1 0x20 0x60 0x80)) 7 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x51 0x81 0x81 0x83 0x52)) 8 (by decide) (UInt64.ofBytes 0x60 0x90 0x51 0x80 0x50 0x91 0x1 0x20)) 9 (by decide) (UInt64.ofBytes 0x0 0x60 0x83 0x83 0x80 0x90 0x1 0x20)) 10 (by decide) (UInt64.ofBytes 0xce 0x8 0x61 0x15 0x10 0x81 0x83 0x5b)) 11 (by decide) (UInt64.ofBytes 0x1 0x84 0x81 0x51 0x1 0x82 0x80 0x57)) 12 (by decide) (UInt64.ofBytes 0x61 0x50 0x90 0x1 0x81 0x20 0x60 0x52)) 13 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x5b 0x56 0xb3 0x8)) 14 (by decide) (UInt64.ofBytes 0x1f 0x60 0x90 0x1 0x81 0x90 0x50 0x90)) 15 (by decide) (UInt64.ofBytes 0x80 0x57 0xfb 0x8 0x61 0x15 0x80 0x16)) 16 (by decide) (UInt64.ofBytes 0x60 0x83 0x1 0x60 0x51 0x80 0x3 0x82))

private def absorbed17 : Vector UInt64 25 :=
  #v[0xe33b59ae7059b932, 0x474131d690651303, 0x1ac7aa4e6c16bbe1, 0x8eab14b1d9d10804, 0x30b7bf577e805d79, 0x54908bfc3d47abc7, 0xda7144ed59fda8f4, 0x1acc874cbe3b7dfa, 0xadf219478f667368, 0x161ed86e0497bb79, 0x9e4f92159487112, 0xb0d910fc1fcfa716, 0x352e716dc6a14374, 0xd3c316576d333ff2, 0x994cf9846757d81d, 0x5e046dd68917ff3, 0x63433b5d57683e09, 0x6a64022c6c1d398b, 0x8dc9d81e9f6112dd, 0x4d0d411ce900ee10, 0x65fb75809aa05f47, 0x88f11efeb2c1bb62, 0xeb008da00729c753, 0x7ba1a12f646a9c16, 0x6542ecd5d054e7b8]

private theorem words17 : absorb17 state17 = absorbed17 := by
  decide +kernel

private def quarter17_1 : Vector UInt64 25 :=
  #v[0x331333f0a68567e6, 0xf900f309374ec625, 0xe413a2a0b2c1815c, 0xd3c0322037e83870, 0xd3d3ff5bd54b3f92, 0x73d6cddade0233d0, 0x39a3c4f2324438b1, 0x9c88af01a1758f93, 0xc1bc5743feeb2e81, 0xedf52554fdaa8e14, 0xa1c07f6efec5c2f0, 0xee82db02ed95992f, 0x8735fe6f8ce73e1e, 0x57a556acf2589fba, 0x4770e5facf5de8ad, 0x5ee75daeb0b9e449, 0x33b5ad89a3c85663, 0xc98f4aa86b4cdc37, 0x7678417e2b9f0225, 0xcfac0703e276c91a, 0xeb9948de8836a921, 0x69f720b5409763a7, 0x8111a46da1f9d161, 0xbbf90b6f0413ef24, 0x5c7a282e3bbec7c1]

private theorem rounds17_0 : sixRounds 0 (by decide) absorbed17 = quarter17_1 := by
  decide +kernel

private def quarter17_2 : Vector UInt64 25 :=
  #v[0xfd71f225adb36f11, 0xd9b67d46ced6718a, 0x2a6064f6e7d4ae5f, 0x99a7ebca460d62fb, 0x136ba8ec66f0b894, 0xc81a063e88e72f0d, 0xc2bdaf7ee93b1ca4, 0xaa812e1eab5f398c, 0x4b789dd0b8c1b316, 0xf3a1d245e5ddb292, 0x31a4179482a10c33, 0x388d048f0b375c95, 0xd16d7f0678e95eef, 0xf4640e70e8f065f0, 0x51981cb78281ca7f, 0x3e442c2179278af4, 0x95e455903c851421, 0xbb527606223c9211, 0x5927a688bf649af6, 0xf2577d3d9801bf84, 0xc5e8e17423cd9c3a, 0x9d0566a256971bd9, 0x5e561a293a72335e, 0x1def554e395209ce, 0x4863000a22f1cbc1]

private theorem rounds17_1 : sixRounds 6 (by decide) quarter17_1 = quarter17_2 := by
  decide +kernel

private def quarter17_3 : Vector UInt64 25 :=
  #v[0x24a8133a9d682207, 0xd860a20a7987111a, 0xd48b8832b4a2e1c0, 0x662b8c5a57f6509, 0x7772a6de90b6d58c, 0xe6cad7f1fd0a5919, 0x5c554afcd1803269, 0x9f40268c62d184f4, 0x9341f17bb8540e25, 0xc5d5cc0c9e505508, 0x3b2f729667eea0dd, 0xbcf45b0f8c599b40, 0xc4caa448c387c8eb, 0xac2705e728054af1, 0xc10c12ca7606ba1a, 0x1816555d2e3e2c61, 0xf5ba6e9c78a8e46, 0x688084fc59d518c0, 0xb3e69e39ffc51eed, 0x688148dfaf00f57b, 0xd263268971c35add, 0x77175680d0cd9536, 0xe77ecce3571cf1fc, 0xafea48d81040d116, 0xe445b7802af75fde]

private theorem rounds17_2 : sixRounds 12 (by decide) quarter17_2 = quarter17_3 := by
  decide +kernel

private theorem rounds17_3 : sixRounds 18 (by decide) quarter17_3 = state18 := by
  decide +kernel

private theorem perm17 : KECCAK.f1600 absorbed17 = state18 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds17_0, rounds17_1, rounds17_2, rounds17_3]
  rfl

theorem block17 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes17 ++ tail) state17 =
      KECCAK.Bytes.run 0 tail state18 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes17 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb17 ws)) := by
    rfl
  exact (step state17).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words17).trans perm17))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
