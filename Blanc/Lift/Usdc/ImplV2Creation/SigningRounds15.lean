import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb090 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x57 0xbe 0x2f 0x61 0x16 0x81 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 9 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x32 0x60 0x52 0x82 0x3)) 10 (by decide) (UInt64.ofBytes 0x32 0x60 0x93 0x59 0x61 0x80 0x1 0x20)) 11 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 12 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0x7f 0x54 0x80 0x2 0x60 0x5b)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed090 : Vector UInt64 25 :=
  #v[0xb65dc41baa11b518, 0x41bdf0302d2e9322, 0x1bc89db5d54de29e, 0xb9ae5f8d99db312c, 0xc17d5f45d7ea8119, 0x78f7281857309087, 0x40d8c86cb33d11b3, 0xd3b079ed319ba099, 0x62d41032f164b024, 0x4542ea3e2b86b5a9, 0x14eaf8beb2818e9a, 0xfcbaec530b04840a, 0x23e1ee4af914a5ad, 0x8375ab082db41cbf, 0x40b24163af23c2e1, 0x43fb9a18b2478e2b, 0x282b80357878ff88, 0xe8facd82d1ebe8d5, 0x5628cb4255d7e0f9, 0xb3f46d415ef61ff1, 0xf1085b718547d957, 0x8808e10b6d97796, 0x6bbfa0dd829d1e5e, 0x492eecfae312a26c, 0x6ff9a96b5a57f7c0]

private theorem words090 : absorb090 state090 = absorbed090 := by
  decide +kernel

private def quarter090_1 : Vector UInt64 25 :=
  #v[0xa7a94219152a8421, 0xb03e8504acc3a866, 0x2fbc14ab7a5f3151, 0x4ed0c509b87875be, 0xc1612a85263e2106, 0x2a51d55b9ad54e31, 0x102ec83807e09718, 0x2951ef699567d30e, 0xfc2c6cfee28a7f04, 0x5c4bc8cfe8d8d062, 0x8bc84976ad28627a, 0x93f89ac6ca4a8ad1, 0x282467b47f5d86a8, 0x29f574095614d9da, 0x938b480f5ed8ea, 0x955316a2f4431f84, 0x3fe4ec4b7816dde, 0x1a48cfbe60b10f57, 0x4fd92df93308a1, 0x3013a84314198f6a, 0xb223edec1d7104a2, 0x5a1e245a76025062, 0xb5736a6d0eb2d68f, 0x3bf10a395425ca9e, 0xcfd8838848b79c77]

private theorem rounds090_0 : sixRounds 0 (by decide) absorbed090 = quarter090_1 := by
  decide +kernel

private def quarter090_2 : Vector UInt64 25 :=
  #v[0x8ade1c18f11cfe29, 0x68b9ba79bf7c8a0c, 0x1599004a104f07a2, 0x52e6b4de360d8f71, 0x1d8fb3aaabf53841, 0x79c7b85f0e2134ac, 0x9df9bdaeff05661e, 0x46ffe89cba88e17d, 0xc11cdb0a1f3f30bd, 0xc7bee339e807b68b, 0x198403e9d53935d2, 0x915f0faee9efe5ca, 0x2bd8c6e65de71941, 0x20e9e29dafebee49, 0xe98e4b6b4605e712, 0xbcd34baf89942db1, 0x36f4f775070a51e5, 0xce979b89137e56b7, 0x4238210b3d862200, 0xc0f9eefa37de5430, 0xe006b002e5faad83, 0x3a008ef5fc46a48c, 0x98096339eb8a5e9e, 0xfab5c3cd7855dfe8, 0x96191a425b5040bc]

private theorem rounds090_1 : sixRounds 6 (by decide) quarter090_1 = quarter090_2 := by
  decide +kernel

private def quarter090_3 : Vector UInt64 25 :=
  #v[0x91fd5e0421c55b92, 0x584ebfd31e5c73c9, 0x14a3e5ff5182ea97, 0xca5871de765420fa, 0xfa4e1ff37e0ded19, 0x4374165e13403009, 0x1ef2a7c6d242c8eb, 0xe070e16714cd7ea2, 0xa02f64b4f7e7ea38, 0x14f2639cc7f3d0e1, 0xc0e8253e17683eac, 0xee8f42895f78fcb9, 0xfd31861741f31cc7, 0xea36368cafb5466b, 0xf7dc2bf97857fae3, 0x350bcee0c722f855, 0x2c4154c0e6e37d2a, 0x167215cb459e5f4a, 0x11c7bfad6369c535, 0xc067e9b3beac1908, 0x4aff72382199034a, 0x6c4a78794fecddd1, 0x19ad223e105fba16, 0x86e818d9adf53837, 0xfbd71d657d4c017]

private theorem rounds090_2 : sixRounds 12 (by decide) quarter090_2 = quarter090_3 := by
  decide +kernel

private theorem rounds090_3 : sixRounds 18 (by decide) quarter090_3 = state091 := by
  decide +kernel

private theorem perm090 : KECCAK.f1600 absorbed090 = state091 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds090_0, rounds090_1, rounds090_2, rounds090_3]
  rfl

theorem block090 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes090 ++ tail) state090 =
      KECCAK.Bytes.run 0 tail state091 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes090 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb090 ws)) := by
    rfl
  exact (step state090).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words090).trans perm090))

private def absorb091 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x73 0x16 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x91 0x16 0x81 0x83 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x60 0x55 0x90 0x82 0x91 0x17 0x91 0x90)) 5 (by decide) (UInt64.ofBytes 0x73 0xc6 0x7f 0x90 0x16 0x91 0x51 0x40)) 6 (by decide) (UInt64.ofBytes 0xcb 0x5e 0xe9 0x1c 0x11 0x2c 0x1 0x98)) 7 (by decide) (UInt64.ofBytes 0x73 0x97 0x6c 0x9 0x33 0xb9 0x29 0x74)) 8 (by decide) (UInt64.ofBytes 0x1a 0xa7 0x75 0x11 0x42 0x6c 0xee 0x80)) 9 (by decide) (UInt64.ofBytes 0x60 0x90 0x6e 0xc0 0x88 0x6c 0x4c 0x4a)) 10 (by decide) (UInt64.ofBytes 0x1 0x60 0x5b 0x56 0x50 0xa2 0x90 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x1 0x74 0x54)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x90 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0xbd 0x30 0x61 0x15 0x16 0xff 0x60 0x4)) 15 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x80 0x40 0x60 0x57)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79))

private def absorbed091 : Vector UInt64 25 :=
  #v[0x762c1a5049d4532d, 0x6c67e636ae93f791, 0x59055fff1f9b84c2, 0xf8efee10dcdcb180, 0xb56773d71261c0ce, 0x7bc67f0fa4599f49, 0xa56aa3b9f7110688, 0xc986cd9ed3a3e39a, 0x9630fcc1cd7e0bc7, 0xa09228f8d73b5604, 0x220d7a594b3e0eaf, 0xa0219bbd452cbdda, 0x8d361e62e7e40c14, 0xd274625e2c08370c, 0xaf06049de2ac47aa, 0xcaae34a91e7bfe8f, 0x40978def89f8788a, 0xe254b37b2b79b534, 0x6579e0ada4b08b11, 0x4eea8987777f33d0, 0x4c24f5ea26858280, 0x43b1d22dc8255fd1, 0x5efa960aa2c37ce4, 0xfe255f5a5e490ab1, 0x49a5183086c81ff1]

private theorem words091 : absorb091 state091 = absorbed091 := by
  decide +kernel

private def quarter091_1 : Vector UInt64 25 :=
  #v[0xd6889341bcd4176, 0xb06d94aff34ea497, 0x5d49268a02e3ed02, 0x613834b0fb8adf56, 0x84d644f619b2e203, 0xa28a8fa4e9cb73c6, 0xc1cbe82c1b484121, 0x501f62ad63cd6932, 0xc1c3fdc9b0f339db, 0x15a6e1b98dd09ad3, 0x647ab2e49db5f869, 0x144bf92c19fd72e2, 0xec536638cde3c3af, 0xa6f312884f0396e7, 0xbcaabe5f42cdcf5a, 0x6dfd57199be949a0, 0x9e0c5398fb8c2f10, 0x8e21b6bef715f33, 0x871dc629e70d0377, 0x1fb0d6188ac30255, 0x6f367f4280076ef7, 0xa816fcced27d48c7, 0x1da22f329136b6, 0x8c8640c88dc5ddb9, 0x7a46d8ab9348a395]

private theorem rounds091_0 : sixRounds 0 (by decide) absorbed091 = quarter091_1 := by
  decide +kernel

private def quarter091_2 : Vector UInt64 25 :=
  #v[0xbeef9bd5b2b151a5, 0x64b353d3676a56a4, 0xcffce48c23a8d5e4, 0x11602bf09e829a6, 0x8f22d672ac58b3a2, 0x6f6cdc44c89933a8, 0x804e10c47453b21e, 0xa05fd0a6ef276ee7, 0x5dff154461ff1d1c, 0x510bfd12fbc55a07, 0x8b97846ca6aa3ee9, 0xd10a26a735e3b49b, 0x47dd8df64b34e7d1, 0xd26d2825ce6960d3, 0x7c4bf8cc33ad63c4, 0xc3cbf8bf3b11c27d, 0xc5a8f56bf1721099, 0x19626f6b24450d20, 0x6a6d9c0bde691068, 0x14ba92e7fe3b2c29, 0xa1c32757c241680e, 0x95fcba3323986ef4, 0xe873031070b3d2e9, 0xf3158c973ea6d8d5, 0xb3625c6160f63720]

private theorem rounds091_1 : sixRounds 6 (by decide) quarter091_1 = quarter091_2 := by
  decide +kernel

private def quarter091_3 : Vector UInt64 25 :=
  #v[0x63a6042ce2d6a681, 0x860edcbe286ca388, 0x2c304323b0842850, 0x567d30ca5e1258e, 0xdc467f90fb837486, 0x2f4fc8042a070880, 0xb8b620afa1586cec, 0x9429610b4ee2028d, 0x3ca5a332821c870, 0x827e5563959393fc, 0xb19696d7f479280c, 0x504303678a1ccba1, 0x3834dd2c71a23195, 0x8f3535ad8819cd07, 0x40376ab7b0499f35, 0x264c531b80be1a96, 0x3ee8d52749211db2, 0xd7fdabb86361a599, 0x46284a46fb95d383, 0xcd6356be34b08671, 0x3f14ac847e151caa, 0x6ee16819a5f5d24, 0x9a083fbd04086b8c, 0x5ad87285369fba86, 0x8e464f9fb61ad3f2]

private theorem rounds091_2 : sixRounds 12 (by decide) quarter091_2 = quarter091_3 := by
  decide +kernel

private theorem rounds091_3 : sixRounds 18 (by decide) quarter091_3 = state092 := by
  decide +kernel

private theorem perm091 : KECCAK.f1600 absorbed091 = state092 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds091_0, rounds091_1, rounds091_2, rounds091_3]
  rfl

theorem block091 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes091 ++ tail) state091 =
      KECCAK.Bytes.run 0 tail state092 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes091 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb091 ws)) := by
    rfl
  exact (step state091).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words091).trans perm091))

private def absorb092 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x60 0x52 0x1 0x82 0x4 0x60 0x20 0x60)) 4 (by decide) (UInt64.ofBytes 0x50 0x7f 0x52 0x1 0x82 0x24 0x60 0x10)) 5 (by decide) (UInt64.ofBytes 0x3a 0x65 0x6c 0x62 0x61 0x73 0x75 0x61)) 6 (by decide) (UInt64.ofBytes 0x0 0x64 0x65 0x73 0x75 0x61 0x70 0x20)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x60 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x81 0x90 0x51 0x90 0x52 0x1 0x82 0x44)) 10 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x1 0x64 0x60 0x3 0x90)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x60 0x16 0x89 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x20 0x60 0x3 0x60 0x52 0x81 0x90 0x0)) 15 (by decide) (UInt64.ofBytes 0x90 0x89 0x54 0x20 0x90 0x40 0x60 0x52)) 16 (by decide) (UInt64.ofBytes 0x57 0x3e 0x31 0x61 0x15 0x16 0xff 0x60))

private def absorbed092 : Vector UInt64 25 :=
  #v[0x58c4f20e518b648d, 0xc61204450adcf482, 0xbd0530c35e985068, 0xc6c5a20694493d21, 0xd84ebf82ef01314a, 0x53a885e805b53a70, 0xa5acfe4dbafda111, 0x28b93774bdc1eeb2, 0x2f466e2abe0ef8d9, 0xd2798331eecc551a, 0x691557f56c38c839, 0x64036c822d0034c0, 0x4fefe7a6154d5133, 0x9b92a9cb4856c4cb, 0x841717b3aa0009b0, 0x44fdd4f6b5464c35, 0x392bef0f50e94c59, 0xbc3363a502b7b7d6, 0xcd6db9d066844388, 0x3796b92d18750884, 0xf83fdddb3753c426, 0x76b2e8f63c26f631, 0xae525aabb0e3a65c, 0x9685ca9539d8344c, 0x529fbcec5754d1d0]

private theorem words092 : absorb092 state092 = absorbed092 := by
  decide +kernel

private def quarter092_1 : Vector UInt64 25 :=
  #v[0x386ffae0a5357ef7, 0xff46261fab47f459, 0x78c15fc5b5556a, 0x9bedfeed11a7cba6, 0xa702bcf70c49aee8, 0x5931c8265ee41a63, 0x5dd0f2639262143e, 0xfda1010f9021ac88, 0x106d80976ddf6e4a, 0x5330abc82365075d, 0x9ed598455a53b78f, 0x99e67c39acf31a21, 0x64b627b9a2ff5b74, 0x5fe1ced01fa05c96, 0x795677faea48e73c, 0x7ee979643668c610, 0xd0cae2ff56d93dc6, 0xb6b3b732ef4f1506, 0xf9332f44076b8433, 0xcd59c66494e0f310, 0x2d98dc8755c97464, 0x11ff423d45403da8, 0x8b888c596c966f91, 0xd20d7126f034b8cd, 0x9b6f2b59f893c4d5]

private theorem rounds092_0 : sixRounds 0 (by decide) absorbed092 = quarter092_1 := by
  decide +kernel

private def quarter092_2 : Vector UInt64 25 :=
  #v[0xc81369a201cfa173, 0xed1bab4ef379cf97, 0x5da6d55018d50fc9, 0x5685ec56d610ded3, 0x6b1420e9f5f7029e, 0xcec475d1b23cb6c4, 0x1d43878b929e47a4, 0x1a563f3638f3ac2c, 0xbb0281aa114784e8, 0x5177092ceae7b09c, 0xb659817b313a7310, 0x453a06d9f3440831, 0x935274c1f66c4310, 0x32e8ccbd4d1af33e, 0x661cd1a54c96beaf, 0xc940cd3f67c37f15, 0x625e7687353a6187, 0x8e614c8eff78eae9, 0x70a39ded1f183f76, 0x2154098491deb2be, 0x27d8b3d007984d89, 0x5af4fdad18f20a26, 0x6d6a7587e54c5bd6, 0xa142115209e77c41, 0xf9056222b46b600a]

private theorem rounds092_1 : sixRounds 6 (by decide) quarter092_1 = quarter092_2 := by
  decide +kernel

private def quarter092_3 : Vector UInt64 25 :=
  #v[0x52e98469b20baa13, 0x2b072c26204e2e4d, 0x30c23163752485f6, 0x8e77c6e1205c768b, 0xcbfd37a2719f48d6, 0x8963a3cde9c892b1, 0xc4d64f4c38acc716, 0x5eba3bcdfc3c9351, 0x679ab69e5943735e, 0xaa85c6b81d325b2c, 0xc95bbebcca41ddea, 0xeab596e64e0c9214, 0x648dfa580596799a, 0xb596ba860bb569a4, 0x7038eda6acac794d, 0x5bd8f7d1c32c0387, 0xcaaf6a258cc45d19, 0xb06ddf4c540a4b21, 0xee5aec5e62b15d9d, 0xaf56427ba549283, 0x5df2a1e17c698f14, 0x95d64e4c5eef499a, 0x9d9844ba08c2194c, 0x9d33533fded2711a, 0xa1ef4eb5c559a7c2]

private theorem rounds092_2 : sixRounds 12 (by decide) quarter092_2 = quarter092_3 := by
  decide +kernel

private theorem rounds092_3 : sixRounds 18 (by decide) quarter092_3 = state093 := by
  decide +kernel

private theorem perm092 : KECCAK.f1600 absorbed092 = state093 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds092_0, rounds092_1, rounds092_2, rounds092_3]
  rfl

theorem block092 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes092 ++ tail) state092 =
      KECCAK.Bytes.run 0 tail state093 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes092 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb092 ws)) := by
    rfl
  exact (step state092).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words092).trans perm092))

private def absorb093 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 6 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x25 0x60 0x52 0x82 0x3)) 7 (by decide) (UInt64.ofBytes 0x25 0x60 0xc5 0x59 0x61 0x80 0x1 0x20)) 8 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 9 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x16 0x89 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x60 0x3 0x60 0x52 0x81 0x90 0x0 0x60)) 14 (by decide) (UInt64.ofBytes 0x89 0x54 0x20 0x90 0x40 0x60 0x52 0x20)) 15 (by decide) (UInt64.ofBytes 0xbf 0x31 0x61 0x15 0x16 0xff 0x60 0x90)) 16 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57))

private def absorbed093 : Vector UInt64 25 :=
  #v[0xa4c65858f3f2e5e2, 0x89e5d8c1b6012a6b, 0x8b14dc1ea5ab2943, 0x6ef87afae1903d98, 0x9b2b668658afe435, 0x97d1a912d62579c4, 0x936123dc0e70ecfb, 0x33a15f0871e6f570, 0x6b8ae5d3246a7e49, 0xc8f92d3cee9e3669, 0x6512e33b4d0d400b, 0xba7a802db0a1e852, 0x135a7263a7f6bae, 0x99f712f112245ffb, 0x8a71bf0285eb42f4, 0xde119a9cc9d3cd7e, 0x672a3ba1f2729825, 0x8b6cefe7fc82ec21, 0xfb14085a058e3b77, 0x89a60dbfab5313f8, 0x8c34ef50976fa1ca, 0x6415cf262d25ae50, 0x63cd65eb249fedf9, 0x52cbc0c259213936, 0x58a36014a6646332]

private theorem words093 : absorb093 state093 = absorbed093 := by
  decide +kernel

private def quarter093_1 : Vector UInt64 25 :=
  #v[0x3d2a07be4d192761, 0xb3584861597c1bac, 0xa77e4bc1a755dfce, 0x3c6eb38707225d93, 0xc07851ce2b299913, 0xc7d26fd5a4ce05b4, 0x8c484093332ee11c, 0xa849eabc6a5010c4, 0x3f071bd6f2ad16d8, 0xf13b9719b49d5ad7, 0xa36d8d799de40469, 0x92ffb099e1245ac9, 0x4f8385f5596df788, 0x24ba5f563394d4e6, 0xf2e4ac08d3596a89, 0xb83fc25a0801f3e2, 0xfab5637a6709aaad, 0x18f09ab5096e8b53, 0x22b82758ba4d31d, 0x7423fa6de386e380, 0x9c97a160aad98d1, 0xbb9ebdc2c569d71d, 0xd5b92b40b90b2feb, 0xa5db766971a2445e, 0x714a77253853de5c]

private theorem rounds093_0 : sixRounds 0 (by decide) absorbed093 = quarter093_1 := by
  decide +kernel

private def quarter093_2 : Vector UInt64 25 :=
  #v[0x11ef4c5b1fb10008, 0xe5afedaae1aed246, 0x310db732ec50245, 0x6bd0784f79fff64c, 0x8d8ffd9372749d98, 0x52c99d53e9b9d1c6, 0x1e7d356a481e3e33, 0xf74710410cf889cb, 0xb63827e812211e4a, 0x72a9e0ac5dcbda62, 0xc9bb9f7bf617ac1c, 0x3f2783a19a7335b6, 0xf7948b4bb9dff1b1, 0xaa825d9675d6c8ef, 0x6833f52fc1bf70f0, 0x5bc91aa29d1d5792, 0xf3e29a3eb051c44e, 0xf076c199adafb904, 0xa68e33892d874c16, 0xf79183319ff92f13, 0x2a7c6a8d116228d4, 0x50a6c39fea7aa9ac, 0x90c9dd1bf37a3198, 0x66bd3080da3816e8, 0xda9e23ee889ee14e]

private theorem rounds093_1 : sixRounds 6 (by decide) quarter093_1 = quarter093_2 := by
  decide +kernel

private def quarter093_3 : Vector UInt64 25 :=
  #v[0x9ca563e50fcdf69f, 0xac2fdc1e380869c9, 0xbded31c34b7aa95c, 0x9c738eb59e0f4f36, 0xd100f9de1ef2a8f0, 0xb2a3bb1510e47f54, 0x9eb4f5cb9cb00fbd, 0x45c479c4a38734da, 0x94e71948e87b50f, 0x65f177079ea9adf8, 0x98162c159d1e6640, 0x9113036baf191a67, 0xf0694537fd6b5b35, 0x881aaa354129eaf8, 0x158434539a80735a, 0x4c58444f5a518440, 0x1020d7c5c74208, 0x2e39df2908d3e945, 0xd2257e802612e182, 0xd9e92d1477edf530, 0x87d91e98f128ea4e, 0x5b7418fffe3fa11f, 0x417a18a04e393a56, 0xd12d0dbf08226ac2, 0x13ffb9e0f27646a1]

private theorem rounds093_2 : sixRounds 12 (by decide) quarter093_2 = quarter093_3 := by
  decide +kernel

private theorem rounds093_3 : sixRounds 18 (by decide) quarter093_3 = state094 := by
  decide +kernel

private theorem perm093 : KECCAK.f1600 absorbed093 = state094 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds093_0, rounds093_1, rounds093_2, rounds093_3]
  rfl

theorem block093 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes093 ++ tail) state093 =
      KECCAK.Bytes.run 0 tail state094 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes093 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb093 ws)) := by
    rfl
  exact (step state093).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words093).trans perm093))

private def absorb094 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x1 0x4)) 5 (by decide) (UInt64.ofBytes 0x52 0x81 0x25 0x60 0x52 0x82 0x3 0x81)) 6 (by decide) (UInt64.ofBytes 0x60 0xc5 0x59 0x61 0x80 0x1 0x20 0x60)) 7 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x40 0x60 0x39 0x91 0x25)) 8 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 9 (by decide) (UInt64.ofBytes 0x8b 0x8b 0x8b 0xd0 0x31 0x61 0x5b 0xfd)) 10 (by decide) (UInt64.ofBytes 0x44 0x61 0x8b 0x8b 0x8b 0x8b 0x8b 0x8b)) 11 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x50 0x5b 0x56 0x56)) 12 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x50 0x50 0x50 0x50 0x50)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x54 0xe 0x60)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x60 0x57 0x4d 0x32 0x61 0x14 0x33 0x16))

private def absorbed094 : Vector UInt64 25 :=
  #v[0x5653961f22fcc30f, 0x59443ddba89b1faa, 0xbefb47ba6be95bc8, 0x96ab27e5c299f07d, 0xc31542f16737578e, 0x53f22d0f15a7e7af, 0xe4017a080b98d259, 0xc28668dc1c68f919, 0xa50b6d017bc4ecec, 0x12b0e5ca95fdbdfc, 0x2e1398a8ba805737, 0x4ae9b67fd61ae728, 0xa0d1b20660b84304, 0x165ebc7eede28e64, 0xbe8f0db32ff3c644, 0x96179e4d6516ad57, 0xf5226709cf96ce85, 0x830d20d5e54b0c1c, 0x306c55999f8dcc3a, 0xb4c77c51c276a489, 0xd7c13046f0128876, 0xd936715311e0b6a0, 0xccd09cb2a84a4d99, 0x791b217f6ceda8bc, 0xf6f4e35b1e17be21]

private theorem words094 : absorb094 state094 = absorbed094 := by
  decide +kernel

private def quarter094_1 : Vector UInt64 25 :=
  #v[0x89c9bb8b1570ef9f, 0x427136f34b183582, 0x35fc8f2c97159b71, 0xcf143cc7dc7e14a9, 0x2253f72c8c23dbba, 0x2e43d36b726d1c5b, 0x97f34c8105da6539, 0xb4fd4b9524073d5a, 0xf748bd4471e26d16, 0x5788595fd623fe24, 0x4c4455aef7a1619a, 0xe381f38eb6b37ecf, 0x5e49921c09e313fa, 0x23dae64fdf146ad3, 0xd8bcd38b387f30dd, 0x1e8a8822adce7b57, 0x2ea79fe7ff686fed, 0x330b358aca0d1b96, 0x592665d9cb016695, 0xe58eb2333de909d3, 0x2d43517352bc1cc8, 0x36df3650ca7e9d25, 0x2547783c97c7261e, 0x4a26e532c5a97620, 0xaea10433bda52293]

private theorem rounds094_0 : sixRounds 0 (by decide) absorbed094 = quarter094_1 := by
  decide +kernel

private def quarter094_2 : Vector UInt64 25 :=
  #v[0x63b68eb60ffb7228, 0x4e4b7986c0cef7af, 0x733cffff027384b, 0x44250289b368c565, 0x1bbb0d5d0b62eb0e, 0x1e88e31cff489cfd, 0xe12b0efaae616f88, 0x5088198f4c2fda68, 0x5810fdcba1b90ce6, 0x78237a1124e0662d, 0x870a7d9c38115a50, 0x42c30aa255082eaa, 0x49f531e292379407, 0xc7233d7ea1905b0, 0xfb8d847836be0809, 0xb4705f05bd7c539b, 0x1d13e13e1c9e2e81, 0x1ba5681a8656eebf, 0xc3abb11548c502a, 0x17d8ec906dc19409, 0xc34978cf8c8b3ba5, 0xe02743d09a0a1d7b, 0x9e6d6f19c5a35f57, 0x7e3139e05daaf5b6, 0xf07d60ce676bb43e]

private theorem rounds094_1 : sixRounds 6 (by decide) quarter094_1 = quarter094_2 := by
  decide +kernel

private def quarter094_3 : Vector UInt64 25 :=
  #v[0xd4cb687ef3c9ef4c, 0xd3001dc773bd28de, 0x432f5c256a2ae87, 0xac7dd99b00aef72, 0x15d9bf7f04b873c3, 0x5830bde9322fadc6, 0x78e8827efdbec056, 0x19854d886523ce8b, 0x1b208771d532968c, 0x128e9a6b765a08fd, 0x6073c453cc333b4f, 0xc587d7c0a8e4230b, 0xa36465e22384c62d, 0x6c314baddddd208a, 0xe00c4469a0e052, 0x6d73797ca565a437, 0xc5481fba617d85e0, 0xdbdd488498d1768b, 0xc5bc9ab56e0a3a4c, 0xc713c5a75855db43, 0xc10005018550bacb, 0x5874099776d14bde, 0x723c3d66e5227aaa, 0x3059270732f7881c, 0x7a31b34fb0a5b197]

private theorem rounds094_2 : sixRounds 12 (by decide) quarter094_2 = quarter094_3 := by
  decide +kernel

private theorem rounds094_3 : sixRounds 18 (by decide) quarter094_3 = state095 := by
  decide +kernel

private theorem perm094 : KECCAK.f1600 absorbed094 = state095 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds094_0, rounds094_1, rounds094_2, rounds094_3]
  rfl

theorem block094 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes094 ++ tail) state094 =
      KECCAK.Bytes.run 0 tail state095 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes094 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb094 ws)) := by
    rfl
  exact (step state094).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words094).trans perm094))

private def absorb095 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x1 0x4 0x60 0x52 0x81 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x3 0x81 0x82 0x1 0x20 0x60 0x80 0x80)) 6 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x24 0x60 0x52 0x82)) 7 (by decide) (UInt64.ofBytes 0x91 0x24 0x60 0x84 0x57 0x61 0x80 0x1)) 8 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x40 0x60 0x39)) 9 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51 0x40)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x6e 0x32 0x61)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x56 0x98 0x45 0x61 0x83 0x83 0x16 0x84)) 14 (by decide) (UInt64.ofBytes 0x2 0x60 0x5b 0x56 0x50 0x50 0x50 0x5b)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x54)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed095 : Vector UInt64 25 :=
  #v[0x83e745d2b5bc3d0d, 0xd737d9712caae100, 0xd44b6a371304726e, 0xf9bccdf7f44704e5, 0x7dd21cb68730f593, 0x8b9ab63f2040af3, 0xdc31f6ff6f488c7d, 0xcedd6186701e6669, 0xbcfb7a07d1f58d89, 0xf823c53d81d65a6c, 0x1429e461730a08bb, 0x8f0a56f238e8bbb5, 0x490f163912924253, 0xd15f803840422b40, 0x51d31ecb391cc495, 0xe41d3c2c9b92ed87, 0x79bd85f10e1d3bf8, 0xd535219048d12a54, 0x4648b64f82ecc022, 0x380cb58d460b77e3, 0x7c9def1cecf79c56, 0xd2f542463e1f8ed9, 0xc2e99861d3d6a6fb, 0xae1bc2aa7a5c4094, 0xfa2c0f1f78cc5d1d]

private theorem words095 : absorb095 state095 = absorbed095 := by
  decide +kernel

private def quarter095_1 : Vector UInt64 25 :=
  #v[0xc1a37fa83669a663, 0xc6a81c8d47d95238, 0x4eb8c4e9e076277, 0x6030b1134e3f72f8, 0x94b3a2495bed426a, 0x8a5cdc89b7633061, 0xb4332df0cd38dfd7, 0xe127c53b37297f5a, 0x76eeb1d84c8d4b37, 0x2961d41686853651, 0xf06ae18ebdde3f59, 0x31894be4f1558580, 0x78bd6bfa34c03d22, 0xde9d6c688cf3c366, 0x24991f25b0b03e55, 0x22eb00c3e73c893a, 0x61ab50b36b8ecec3, 0x6481d14be2346960, 0x71eea35aab653d94, 0x859bf17639a8b999, 0xb2a432294c0f7bc1, 0x4d1c9abfc05237d4, 0xec679c26200c3909, 0xc00f19e2717d28a9, 0x84a79dc434dd024f]

private theorem rounds095_0 : sixRounds 0 (by decide) absorbed095 = quarter095_1 := by
  decide +kernel

private def quarter095_2 : Vector UInt64 25 :=
  #v[0xc23d286de8e5c326, 0xe3702fdac108447a, 0xe0fd590aa2ab7f95, 0xae9b405d38496033, 0xb50221f7114df8c7, 0xca9027afd24caced, 0x514254978eb093ab, 0x7f58f97ec9b75219, 0x2b6f8530994c6a73, 0x5773cd2afa1ec8e9, 0x32fc2e4c7a80af1e, 0x375552e9badca85b, 0xa9cbfb8b365e27b, 0xf9a8a57c5688e9d8, 0xb3503426fd514ef4, 0x1fd1e127e55a96c8, 0x30136c0a9dfe45dd, 0x93ca3d8fb9b0c311, 0xc574771160bd5486, 0xd88710222d0ea568, 0xb2990a0d98cf8861, 0xfb071b6a61ac41ae, 0x5e0ee8539d9d5191, 0x386fa55f4cca7ea3, 0x19358ac6f555bd18]

private theorem rounds095_1 : sixRounds 6 (by decide) quarter095_1 = quarter095_2 := by
  decide +kernel

private def quarter095_3 : Vector UInt64 25 :=
  #v[0x35269a148b24ed41, 0xe31ba04e46e39c31, 0x7c2b5a661a7eb0ec, 0xfcc1c3db9b394948, 0xab3cdc7967ab6a52, 0xc92f474a7afe42e9, 0x1dc3ed4ef8d35e1b, 0xb12671d8a172ffac, 0xb78c8d20a904d359, 0x4c731ebaa4f93bf, 0xc6a6008f4314a8dc, 0xec3b6681c0f53e4a, 0xa6f4c9218989dd7a, 0x597877e5bea6d6ed, 0x13283783bfe28a8b, 0x73fbe32a1ac848bd, 0x92beb9859406b1b4, 0x3b038b67b414fd33, 0x54eedb44f2b49f6d, 0x8130a07f67862db1, 0xdb48e401049e04f7, 0xc45f86ae22a74fbf, 0x3769fcffadae824d, 0x32ad3071f1d9484, 0xd6b7eb704701feea]

private theorem rounds095_2 : sixRounds 12 (by decide) quarter095_2 = quarter095_3 := by
  decide +kernel

private theorem rounds095_3 : sixRounds 18 (by decide) quarter095_3 = state096 := by
  decide +kernel

private theorem perm095 : KECCAK.f1600 absorbed095 = state096 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds095_0, rounds095_1, rounds095_2, rounds095_3]
  rfl

theorem block095 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes095 ++ tail) state095 =
      KECCAK.Bytes.run 0 tail state096 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes095 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb095 ws)) := by
    rfl
  exact (step state095).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words095).trans perm095))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
