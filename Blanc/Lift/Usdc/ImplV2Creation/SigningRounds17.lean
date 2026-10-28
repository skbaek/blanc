import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb102 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x82 0x3 0x81 0x82 0x1 0x20 0x60 0x80)) 1 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x25 0x60 0x52)) 2 (by decide) (UInt64.ofBytes 0x39 0x91 0x25 0x60 0xc5 0x59 0x61 0x80)) 3 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x40 0x60)) 4 (by decide) (UInt64.ofBytes 0x61 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51)) 5 (by decide) (UInt64.ofBytes 0x89 0x89 0x89 0x89 0x89 0x89 0xeb 0x35)) 6 (by decide) (UInt64.ofBytes 0x50 0x50 0x5b 0x56 0x5b 0x47 0x61 0x89)) 7 (by decide) (UInt64.ofBytes 0x56 0x50 0x50 0x50 0x50 0x50 0x50 0x50)) 8 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x54 0x12 0x60 0x5b)) 9 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0x52 0x36 0x61)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 15 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 16 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x2c))

private def absorbed102 : Vector UInt64 25 :=
  #v[0x4855a6117437bb3a, 0x5318901e8bc02174, 0x3f990510935b4313, 0x4775bb79d5bc2f70, 0x6a0733f634974f40, 0x5377309284899273, 0x4433e89ddba25f65, 0x172985b7fbd52310, 0xf171f7bc0658e4a0, 0xe064d54ba45bafcb, 0x5c3b24f1dd333aab, 0x41fd85579c82dbce, 0x48676f3d57d8d767, 0x640da9b7da2a2e70, 0x98a99975da15645a, 0x9630abdc06e98c57, 0xe2339df134111c68, 0x822dec767627c7a9, 0x4cc23a81e680a74d, 0x35bfa952ba812f29, 0x32fa840ab75ed56c, 0x18e2568c94802f17, 0x4d600d77fd85c26f, 0xcf7614241d315dc9, 0xd0c3733bc422a67d]

private theorem words102 : absorb102 state102 = absorbed102 := by
  decide +kernel

private def quarter102_1 : Vector UInt64 25 :=
  #v[0x50a4a8bb6608b502, 0x3ad5bb699e4307c3, 0x8c9d7e7a10ac8d52, 0x5df55f6cca4ee225, 0x59e88349606e1fb, 0x6c92a82ff38eb7d8, 0xdebe7125718ad5a, 0x7680984266c01631, 0xd4ea9e317a95f061, 0x89500bdae661d751, 0xb891890f3fc7132, 0xe6e7177733b90e2, 0xeb1166fa125cf625, 0xbf7c30b65f9d69fe, 0xa922406d28f9c244, 0x921517beba659d37, 0xfa2c33c99384debf, 0xeada1bdde4737c45, 0x80a65a67bf583610, 0x548f2f8b734a60b3, 0x5a9a8d9d8de7ec1f, 0x604ac59b0be1dd91, 0x4d50ea50e74c45fc, 0xe744d395c3456e9c, 0x78311ba483253b29]

private theorem rounds102_0 : sixRounds 0 (by decide) absorbed102 = quarter102_1 := by
  decide +kernel

private def quarter102_2 : Vector UInt64 25 :=
  #v[0xde33e702416701c3, 0x1a3fd8031543bc43, 0x3dfb62a772268e5c, 0xf48826640467d016, 0xd62e1e2e652e84a2, 0x947a4277d91d3009, 0x2c2822786dbb76b9, 0x63e5b3e2115fae11, 0x45db62d2202bb29, 0x2ef8533ff0f1eea2, 0x1086262284cbb6dd, 0x9d309f6dc827c59d, 0xcb8f84bf209e68c6, 0xc46ff7dfd215e121, 0x37dfd6afac2889ae, 0xcd166bd8e3cf459b, 0x1d0bc916d71d101a, 0xff1538d4ec0546d7, 0x8742e34316852c9a, 0xa18c62753fb2e06b, 0x11d28fb9a6aeba1, 0x8daf7628f59cefd9, 0x7ec191a5c379fc3e, 0x2b4a08202061b23c, 0x665e9e213f08fe74]

private theorem rounds102_1 : sixRounds 6 (by decide) quarter102_1 = quarter102_2 := by
  decide +kernel

private def quarter102_3 : Vector UInt64 25 :=
  #v[0x2a40c3c000b57bf1, 0xf30b6c97b0c8b2e9, 0x7f8f0e569bb684d2, 0xcb700feba24b6f19, 0x94fa999f5aeb455, 0x814b2f7599c216dc, 0xa0416b89a12312ee, 0xb381727a95e06c1b, 0x6710a403586f71fa, 0xd8fda2e9d437940a, 0x3204ffb086485f69, 0x77738ea3b9d4acc2, 0xe9be5d343e1fe980, 0x3ffb24448e0bc043, 0xb50a0bc5ef81a813, 0x140fafe608982f16, 0xad629220c612c15d, 0xb127655e79d7d5d4, 0xfd806bbe65e0a0db, 0xa3edfc8c6cbd0559, 0xc51321bdac1b3a93, 0xac87c765dad63746, 0x17280e2f08587fed, 0x34993fddfcb38e8b, 0x8086bb6bd8bea00b]

private theorem rounds102_2 : sixRounds 12 (by decide) quarter102_2 = quarter102_3 := by
  decide +kernel

private theorem rounds102_3 : sixRounds 18 (by decide) quarter102_3 = state103 := by
  decide +kernel

private theorem perm102 : KECCAK.f1600 absorbed102 = state103 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds102_0, rounds102_1, rounds102_2, rounds102_3]
  rfl

theorem block102 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes102 ++ tail) state102 =
      KECCAK.Bytes.run 0 tail state103 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes102 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb102 ws)) := by
    rfl
  exact (step state102).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words102).trans perm102))

private def absorb103 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x2c 0x60 0x28 0x58)) 1 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 2 (by decide) (UInt64.ofBytes 0x5e 0x36 0x61 0x5b 0xfd 0x90 0x3 0x91)) 3 (by decide) (UInt64.ofBytes 0x56 0x45 0x54 0x61 0x83 0x83 0x4 0x60)) 4 (by decide) (UInt64.ofBytes 0x80 0x82 0x82 0xd3 0x36 0x61 0x50 0x5b)) 5 (by decide) (UInt64.ofBytes 0x91 0x80 0x20 0x60 0x1 0x1f 0x60 0x80)) 6 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x1 0x20 0x60 0x2 0x4)) 7 (by decide) (UInt64.ofBytes 0x93 0x80 0x52 0x40 0x60 0x1 0x81 0x90)) 8 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x81 0x90 0x91 0x92)) 9 (by decide) (UInt64.ofBytes 0x60 0x37 0x84 0x82 0x80 0x83 0x83 0x1)) 10 (by decide) (UInt64.ofBytes 0x50 0x52 0x91 0x90 0x91 0x1 0x92 0x0)) 11 (by decide) (UInt64.ofBytes 0x1 0x82 0x80 0x51 0x80 0x40 0x60 0x50)) 12 (by decide) (UInt64.ofBytes 0x7f 0x52 0x81 0x1 0x60 0x52 0x91 0x90)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x32)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed103 : Vector UInt64 25 :=
  #v[0x9902b5abe5b4031a, 0x48bc05201fdd453e, 0x837a814a0a01d0f3, 0x7862ec1173ac93d2, 0xd33d8d3dfaaac60d, 0xe8013d5b5b664732, 0xff2bff787ed8c552, 0x8406a58355522f98, 0xbb58e6bd5c4f80bb, 0x1e1348eb75846783, 0x7a1632f6e88273fe, 0x929efd68aef505aa, 0x78fd60be432f7381, 0xb282822d494ee6f8, 0x2c7d19a25ce90799, 0x81b658dc2d23a763, 0x1af5dadeaf6661d2, 0x709ac39d882ef5b1, 0xc1fb824957e1b793, 0x9b5c92cc07ae32e8, 0xa4b4f4347ac0e531, 0x10526f5f074abb70, 0x855edd8a615fa889, 0x569d8817dfca198e, 0xe008c14c8c1baa35]

private theorem words103 : absorb103 state103 = absorbed103 := by
  decide +kernel

private def quarter103_1 : Vector UInt64 25 :=
  #v[0x4437887a87c07d0, 0x18930fae48214cb, 0x915b9640d16ad6c9, 0x432a26763cbcc5a9, 0x641fcb8af0dfdaa0, 0xcc344e0fa475af92, 0x601a97f211ec9304, 0x2ff2eab34b2343de, 0x99d24d7e215bec35, 0x304883ddd55aba3e, 0xf830a5b2dd36097f, 0x203f9ca397228b69, 0x3a638c5bce855c86, 0x2df983ec13a73e5d, 0xd967b2e9eb467f17, 0xe1462dbb3aae0917, 0xac67b273c1a5ae52, 0x2e4d678bd197ee2c, 0x177f41dc40cb2925, 0x8a256fbacdab52b9, 0x2933fef501bbc5c6, 0x9f177b26a637091, 0x7ec706c5482a8cf8, 0x8fbfa7de4b5ab4a, 0x96e0b7250a3d4fb]

private theorem rounds103_0 : sixRounds 0 (by decide) absorbed103 = quarter103_1 := by
  decide +kernel

private def quarter103_2 : Vector UInt64 25 :=
  #v[0x6190ad2641fef0bc, 0x9735097d892d1f0, 0x6d5f2e6b7b08a850, 0x2b4a0aa08243e307, 0x7491c592c4172c0c, 0xb458ff2f0c66f487, 0x31e10e4f869675cb, 0x32df58e5717614f7, 0x1b0f4fdcb8232483, 0xa38d11896ee489ab, 0xeac16f7676781936, 0xb70c35c339981091, 0xc5c67ca1735effe9, 0xb13342bbe99d3471, 0xc2cdb151b660eef3, 0x60bc38063cdea804, 0xde37178b6fe1ddb8, 0xfd797b114c7b914d, 0xe47aa233ad4827d2, 0x1015a1a892686754, 0x6f0f5f8659306abf, 0x9501c5f245e503f3, 0x4ccf351a63a49ca7, 0x3a34336f49acb2fc, 0xfb0237ab1033591e]

private theorem rounds103_1 : sixRounds 6 (by decide) quarter103_1 = quarter103_2 := by
  decide +kernel

private def quarter103_3 : Vector UInt64 25 :=
  #v[0x934fd077030f8199, 0x790fd9603145a7e6, 0x988e95cb88c8d3, 0xd60e0f0f7ab19bc9, 0xdc09692331f8099, 0x581d75c56d5ea3c2, 0x8ab57553e197f954, 0x419e8321d68664a4, 0xaad91a1b9bd33506, 0xe19e99b7b9579182, 0xe0c986b246058a5c, 0x2a997f0b8e65940, 0x8dd54d99face4b2d, 0x74e171a50e8d8338, 0xdbe8af66a36d0c0b, 0xc5fc03887784634a, 0x8f9bbc5a3ed9d9df, 0x6e742e6eb257aabb, 0x4c553c44325097d0, 0x673d594033f5c8bb, 0x6cb6fbb63b4bd284, 0xd0a05deb7c31b98c, 0x3426336fb6509c67, 0xb251e0d0d4d889e6, 0xc4f024f1f68f6098]

private theorem rounds103_2 : sixRounds 12 (by decide) quarter103_2 = quarter103_3 := by
  decide +kernel

private theorem rounds103_3 : sixRounds 18 (by decide) quarter103_3 = state104 := by
  decide +kernel

private theorem perm103 : KECCAK.f1600 absorbed103 = state104 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds103_0, rounds103_1, rounds103_2, rounds103_3]
  rfl

theorem block103 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes103 ++ tail) state103 =
      KECCAK.Bytes.run 0 tail state104 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes103 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb103 ws)) := by
    rfl
  exact (step state103).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words103).trans perm103))

private def absorb104 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x61 0x50 0x91 0x52 0x1 0x82 0x20 0x60)) 1 (by decide) (UInt64.ofBytes 0xf 0x60 0x5b 0x56 0x50 0x90 0x4 0x49)) 2 (by decide) (UInt64.ofBytes 0x7f 0x54 0x80 0x12 0x60 0x50 0x50 0x55)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x0 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x5b 0x56 0x55 0x90 0x17 0x1 0x60 0x16)) 8 (by decide) (UInt64.ofBytes 0x82 0x7a 0xdf 0x9e 0xa 0x8b 0x15 0x7f)) 9 (by decide) (UInt64.ofBytes 0xc6 0x15 0xd5 0x3c 0xf6 0x2 0xad 0x8a)) 10 (by decide) (UInt64.ofBytes 0x6f 0x39 0x7 0xa8 0xb 0xf5 0xf2 0x8e)) 11 (by decide) (UInt64.ofBytes 0x74 0x59 0xa1 0x33 0x28 0x84 0x12 0x6d)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0x56 0x81 0x29)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x81 0x90 0x0 0x60 0x16 0x82 0x91 0xff)) 16 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x20 0x60 0xa 0x60 0x52))

private def absorbed104 : Vector UInt64 25 :=
  #v[0x9acb7417ab8fe505, 0x96545a674dccfa9f, 0x229af43c8db44e32, 0x53e794fc9657f44, 0xa73a9502154d4297, 0x4a61f5b7c6a84822, 0x9cf1878ac6751e82, 0x1c09a7420b1c540e, 0xcd1e530a83f77f44, 0x3c20a110ae8fb4be, 0x2bf9331cf210011d, 0x39dcc9c359596f69, 0xf115af7ccd3d10d5, 0x5be2997a76e28f6, 0x7be811ec8a038134, 0xa3cf233cf318cfd2, 0x75772474d0f54783, 0xcb8d2f3212d27d44, 0xfce9f7edad03a4e9, 0x7985980921245017, 0x2b055b31e071762e, 0x55c65978f239839d, 0x3679811938dbba7e, 0xcc38a8f836c0cc09, 0x5d54f4d93808c5b7]

private theorem words104 : absorb104 state104 = absorbed104 := by
  decide +kernel

private def quarter104_1 : Vector UInt64 25 :=
  #v[0x9213ac49325e1262, 0x265c4aaa96965b4b, 0x5304e713a0d22338, 0x6c43cf32ee8265a, 0x4a6f29c4d9d364d6, 0x1fa54ef15e3b705c, 0x883978f380bcd438, 0xbc28786d2232a3c3, 0xcb957b04c1577b9e, 0xc7d6bab9fad9e3db, 0x39673f0f8d6662bb, 0xf335d0bbc11746f9, 0xfea11f730aa84508, 0x159562b6095304a2, 0x90d772eb1c99cd8d, 0x1156b8fa97c07e47, 0x75e36441d87614a2, 0xeac0529284aa9ca7, 0xb38fa92821f9fcae, 0x4ce2440f41918efc, 0x94d40015063164ce, 0x9f624fda88860228, 0x4553d70978832e83, 0xe8311bb4ac7a034e, 0x763f98dc7f09f2b5]

private theorem rounds104_0 : sixRounds 0 (by decide) absorbed104 = quarter104_1 := by
  decide +kernel

private def quarter104_2 : Vector UInt64 25 :=
  #v[0xa720cfbbb1dae7a4, 0x2f2c9d5628f951ad, 0x8c3fe640688cb2ab, 0x4a1a8ba27315feda, 0x3cf5aaeb10593497, 0xfa1e09f5aa9a4f20, 0x7b4321c592225a3e, 0x80b7758cad2a5026, 0xd56f13652279a255, 0x23bd8889f46be908, 0x6267123f45cbbc4d, 0xa297999aeb8b7646, 0x1d38935f844dc608, 0x45d5b5e953ac4e43, 0xcd71786a11407f71, 0x91fa5782664bc678, 0xc12a2434e65ebd7, 0x260eef5ffc58d106, 0xdd246ccea35754e8, 0xd8b587c037893432, 0x62c7d7ff18762e4a, 0x6fa21f4e5095d720, 0xa1bfd4dfc836756d, 0xe9bf08cd0953783c, 0xa9845013a309f9d3]

private theorem rounds104_1 : sixRounds 6 (by decide) quarter104_1 = quarter104_2 := by
  decide +kernel

private def quarter104_3 : Vector UInt64 25 :=
  #v[0xf397596697263f4d, 0x4b2557156a69f571, 0xa1eb0156502df32, 0x905853e698f9b63a, 0xba19d3851d60fe90, 0x6fa0b9c00b8dee73, 0xf72468c4e397a2b3, 0x9489add7ad494423, 0x7b074499c7cd25cd, 0xc6be63c3889a9e2, 0x2af5495ff5befa1a, 0x8227b932597bebbf, 0x375ceef1c0802841, 0xfc2022e679e515f5, 0x7b606b5b98db7e5f, 0x406c3ebcaf7ba353, 0x24ae20679f4ecc18, 0x111dbcccbc3d463e, 0x675aef890929348a, 0xca77c56ec58977d9, 0x81c2cb640369f225, 0x8861609810559166, 0xa1c2a5b4752fd8d, 0xfc0d884b82193841, 0xf04c48cb57c904a4]

private theorem rounds104_2 : sixRounds 12 (by decide) quarter104_2 = quarter104_3 := by
  decide +kernel

private theorem rounds104_3 : sixRounds 18 (by decide) quarter104_3 = state105 := by
  decide +kernel

private theorem perm104 : KECCAK.f1600 absorbed104 = state105 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds104_0, rounds104_1, rounds104_2, rounds104_3]
  rfl

theorem block104 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes104 ++ tail) state104 =
      KECCAK.Bytes.run 0 tail state105 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes104 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb104 ws)) := by
    rfl
  exact (step state104).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words104).trans perm104))

private def absorb105 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x94 0x90 0x93 0x20 0x83 0x80 0x40 0x60)) 1 (by decide) (UInt64.ofBytes 0x20 0x52 0x91 0x90 0x91 0x52 0x82 0x16)) 2 (by decide) (UInt64.ofBytes 0x74 0x54 0x1 0x60 0x5b 0x56 0x90 0x54)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x1)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x60 0x4 0x90 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x60 0x57 0xeb 0x37 0x61 0x15 0x16 0xff)) 7 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80 0x40)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x60 0x10 0x60 0x52 0x1 0x82 0x4 0x60)) 13 (by decide) (UInt64.ofBytes 0x75 0x61 0x50 0x7f 0x52 0x1 0x82 0x24)) 14 (by decide) (UInt64.ofBytes 0x70 0x20 0x3a 0x65 0x6c 0x62 0x61 0x73)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x64 0x65 0x73 0x75 0x61)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed105 : Vector UInt64 25 :=
  #v[0xd8774fa0cdb783eb, 0x9136c063438df33a, 0x4bd86b3b44ec76a2, 0xa80228048ab5c87f, 0x41d4b693396c3c6, 0x158e3f3831d0b2e9, 0x5ca85347533fa65c, 0xe80797acabfc1c9b, 0xb0e7c6e525063855, 0x5709cb39500994e8, 0x41e74c74024a8740, 0xe77ba0e8703d580b, 0x3088552765babb69, 0x8bee737e988f5757, 0x89e187535e4d1c52, 0x3358c81f93484034, 0xf2974ded4dc02116, 0x91193498b1c07b94, 0x70f67b5dd5857fdb, 0x51f06fd7fcbc7d24, 0xa41b3a05f68d82a0, 0x88590f0c0ca871a3, 0x648738fbacd1b06c, 0x7745c5e713a40ef2, 0x86bbf7ee872197bd]

private theorem words105 : absorb105 state105 = absorbed105 := by
  decide +kernel

private def quarter105_1 : Vector UInt64 25 :=
  #v[0xb9eeda8e51c73ac4, 0xabd7f9c97c58b971, 0x41f541bbe57e42e4, 0x50741ccbf15d5714, 0x59839b307ecd55ba, 0x8f63b696670c52ec, 0x16b04b62785d8b14, 0xa7d6f47f4a11a376, 0xf2c38d5d705d6b4f, 0x9f747afb3d4e653a, 0x8abc2d1ad9745efa, 0xfe4fc44f840017df, 0x344709a1deda6f2d, 0x80df019fb11a3635, 0x71e6aedfcaeb3c0, 0x13396189d78b8c1f, 0xaccbd50c8f6e71ee, 0x1392e72dc5257e28, 0x51d0ee2e0533eaf, 0x1d2b663cf374c22b, 0xe68e73b458f89788, 0xc037029448c03381, 0x228c3f1073924115, 0x943df4f7fa0f085, 0x654e5b885afcbb00]

private theorem rounds105_0 : sixRounds 0 (by decide) absorbed105 = quarter105_1 := by
  decide +kernel

private def quarter105_2 : Vector UInt64 25 :=
  #v[0x32ffd423049dd1ea, 0xafd86f08856fdb31, 0x2f2eb08a4ad19e7a, 0x7c021c260fbe79bb, 0xc193146d8593268b, 0x40201d1817884ed3, 0xb9bfdc25f30222b4, 0xf6b3abd67ff893fd, 0x7a8cd6c3e289435, 0x1ef2901fcc1e4171, 0xbfef9cd04e648c3f, 0x9d40914a3ef36a07, 0xd74077120f85129c, 0x67ed191768bed09d, 0x75e55cc37d55c265, 0xfc7d6b7a39377d8b, 0x8d0dd8011f147958, 0x74001fbc595934dd, 0x1496d4c29f09ff0c, 0x8c2fe1226f24c00a, 0x4efa024aa4490081, 0xc77d417e9bc6cecb, 0xefc5c55612154dfc, 0xf63f5ee0a45d163c, 0xe68795749a556a6d]

private theorem rounds105_1 : sixRounds 6 (by decide) quarter105_1 = quarter105_2 := by
  decide +kernel

private def quarter105_3 : Vector UInt64 25 :=
  #v[0xde0089189354914b, 0xf67ffd2316bbdf03, 0xd152d5575ea6754d, 0xc00bf116dd06df3e, 0x87543e221676e85a, 0x3405c2c43520420c, 0xdc5f227ace07dfa9, 0x4c77856ac6cde8a7, 0xfc1ca173c55622b3, 0xf9c122ae9576eaf1, 0xee724d2c4fd72a34, 0x61ced3ad657c7b49, 0x54f3de4852baa92e, 0x9a3754e7f1a1c2fa, 0xc8da9af3a269b142, 0x92ad26e323dbba52, 0x46da337f1c47e6b0, 0x3a71513cc8a246b5, 0x3116e3fe14fca1d8, 0x412716511e1a2f3a, 0xab59776ee5b180ac, 0xe6f1180dd9797ef8, 0x3dea6eec8d406c54, 0x863bd2dd025f8c8c, 0xf46d13d9331036dd]

private theorem rounds105_2 : sixRounds 12 (by decide) quarter105_2 = quarter105_3 := by
  decide +kernel

private theorem rounds105_3 : sixRounds 18 (by decide) quarter105_3 = state106 := by
  decide +kernel

private theorem perm105 : KECCAK.f1600 absorbed105 = state106 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds105_0, rounds105_1, rounds105_2, rounds105_3]
  rfl

theorem block105 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes105 ++ tail) state105 =
      KECCAK.Bytes.run 0 tail state106 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes105 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb105 ws)) := by
    rfl
  exact (step state105).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words105).trans perm105))

private def absorb106 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x82 0x44 0x60 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x3 0x90 0x81 0x90 0x51 0x90 0x52 0x1)) 2 (by decide) (UInt64.ofBytes 0xff 0x73 0x5b 0xfd 0x90 0x1 0x64 0x60)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x90 0x0 0x60 0x16 0x89 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x60 0x52 0x20 0x60 0x3 0x60 0x52 0x81)) 7 (by decide) (UInt64.ofBytes 0xff 0x60 0x90 0x89 0x54 0x20 0x90 0x40)) 8 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x6c 0x38 0x61 0x15 0x16)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x80 0x1 0x4 0x60 0x52 0x81 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x82 0x3 0x81 0x82 0x1 0x20 0x60 0x80)) 15 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x25 0x60 0x52)) 16 (by decide) (UInt64.ofBytes 0x39 0x91 0x25 0x60 0xc5 0x59 0x61 0x80))

private def absorbed106 : Vector UInt64 25 :=
  #v[0x21927d4658399869, 0xd9d3b1fbcbfb685f, 0x5b2cd25419d5e8e9, 0x7f37496f2fbeab28, 0xf40a803112cc66a2, 0x69fc9eafca94588d, 0xeaa678c517c0ed9, 0x6b07ee620d514cb4, 0x7e66666b515422f6, 0xfb3d6e083355fbff, 0xbfd929a8eb74863c, 0x8c039d5c0de0bb3b, 0x1577b7723a045333, 0x19160a2c28202a35, 0x7136f6b30b48f34e, 0xa3d2658a2b19a3d5, 0xe9c06f721d70d4fd, 0x9e32b0bdd05b77f, 0xa623c3fa4d3ae26a, 0x6aebd67ddaefb87d, 0xafa2442fb298a857, 0xdc540b5b7976f6ac, 0xef15be826a59405b, 0x713fab143d3e2e80, 0xa9e7fd123be04abe]

private theorem words106 : absorb106 state106 = absorbed106 := by
  decide +kernel

private def quarter106_1 : Vector UInt64 25 :=
  #v[0xe8376cbccf9099e6, 0x5b5ddd4866fce338, 0xc1efc3cd4ffd07e6, 0x3170d8088b98eb18, 0xe2dedaac57284943, 0x3fa894d1b871f398, 0x4df4e75e1b8a9bf1, 0x346a3e79a4bfba2d, 0x7ee947b147425315, 0xe69f07aa55a9bbdb, 0x6934ea743a70a1da, 0xc16e59b7045b04ec, 0xda8cc714d85fe029, 0xd58be8eafe730d2c, 0x6d8b77c88f363897, 0x66fdb7a68e406fed, 0x681c546838ecd34, 0xf2d32d513464c072, 0x84d7c044c1a00fbd, 0x80de6c97bea43b6a, 0xb301fa29bb33a463, 0xd382841d83885544, 0xc44ef61c69d25552, 0xcfbe8c279b0b3010, 0x4968d071e7fb3d95]

private theorem rounds106_0 : sixRounds 0 (by decide) absorbed106 = quarter106_1 := by
  decide +kernel

private def quarter106_2 : Vector UInt64 25 :=
  #v[0x775a9c2b186f1260, 0x8dcdd18235fb4bf2, 0xf2e19e77fe196a23, 0x9cb48fd4581ac9a8, 0xba40e730cca382db, 0xe64604102325e56b, 0xe5b377e15145b697, 0x2e8cd4541d4beae3, 0x76743d2b19337baa, 0xfa917e8025c94984, 0x2fd113eafde7f84e, 0x30ab222d2efbfc13, 0xecac4a51dd36dd96, 0xfc9884bb5d5ab673, 0x6830edd44e3ebcc8, 0x4f759d9b1513d78a, 0x17dde97f092e716f, 0x1046cb9104d0be1c, 0x2d60e53cece3c0a6, 0xe16462e16df263df, 0x92f20a15be90096b, 0xac8ca09afc75d7be, 0x9744eaf782614219, 0xd5c72a6c4b3b2589, 0x9de74cf2ea26866]

private theorem rounds106_1 : sixRounds 6 (by decide) quarter106_1 = quarter106_2 := by
  decide +kernel

private def quarter106_3 : Vector UInt64 25 :=
  #v[0xdeeede9d191424b7, 0x38a5bad70c91c844, 0xa889b62940e91681, 0x8c564f8b95bf1fda, 0xda41465d91f8d1dc, 0x76b3b02a808610b7, 0x728471a68b83a64b, 0x929eb63d95e4c039, 0x82f1294ea3bf8088, 0x2927d90252161830, 0x5b0d3f0410c45585, 0xf6892a1d15922e30, 0xed3226233119fee7, 0x73a493009db5ae08, 0x7f2edb0260094fc7, 0xf4cba407d87778fc, 0x93c8360ddf643ced, 0x294c78fc0270e4a7, 0xc145dce742db147, 0x551f8df5caa4fdba, 0x7e2a6aa5009af2f6, 0x56342329c74e95ab, 0xbd54d10e7bc5c9b6, 0xe31ba61b273d94bf, 0xeaf4159cacf00e11]

private theorem rounds106_2 : sixRounds 12 (by decide) quarter106_2 = quarter106_3 := by
  decide +kernel

private theorem rounds106_3 : sixRounds 18 (by decide) quarter106_3 = state107 := by
  decide +kernel

private theorem perm106 : KECCAK.f1600 absorbed106 = state107 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds106_0, rounds106_1, rounds106_2, rounds106_3]
  rfl

theorem block106 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes106 ++ tail) state106 =
      KECCAK.Bytes.run 0 tail state107 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes106 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb106 ws)) := by
    rfl
  exact (step state106).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words106).trans perm106))

private def absorb107 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x40 0x60)) 1 (by decide) (UInt64.ofBytes 0x73 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x0 0x60 0x16 0x89 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x52 0x20 0x60 0x3 0x60 0x52 0x81 0x90)) 6 (by decide) (UInt64.ofBytes 0x60 0x90 0x89 0x54 0x20 0x90 0x40 0x60)) 7 (by decide) (UInt64.ofBytes 0x60 0x57 0xed 0x38 0x61 0x15 0x16 0xff)) 8 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x1 0x4 0x60 0x52 0x81 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x3 0x81 0x82 0x1 0x20 0x60 0x80 0x80)) 14 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x25 0x60 0x52 0x82)) 15 (by decide) (UInt64.ofBytes 0x91 0x25 0x60 0xc5 0x59 0x61 0x80 0x1)) 16 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x40 0x60 0x39))

private def absorbed107 : Vector UInt64 25 :=
  #v[0xc5b27d9b8ed5e916, 0x98d924bac5c567a3, 0x1b6d7fa0bc9a1903, 0x339b3c4462a0a3c9, 0x335d723518c1cfb8, 0x7ffe15cfc3949056, 0x438edf35bba3f30e, 0x3fa4e799fa411824, 0xf49d31cac5ebdda9, 0x9bf1d6b84a0c98d1, 0xbf67ebd472409cc1, 0xced800788ec21518, 0x30337da89d55064f, 0x19bd6dfad4a58f6a, 0xdc2e671c254ea6c8, 0xfb71e18597c216ea, 0xde47af627f4e7c55, 0xf71fb3cadfecc6f0, 0xfa0827b44968f50e, 0x41d11c135d002672, 0x17bf07cb8692b88b, 0x47d3bd0654035a3b, 0x36f742d8e4eccef0, 0x1c1a0714703e4a0a, 0x5257e1d2e1eb7c7a]

private theorem words107 : absorb107 state107 = absorbed107 := by
  decide +kernel

private def quarter107_1 : Vector UInt64 25 :=
  #v[0xecaa681ba71e2369, 0xcfa51d8e3a2560bb, 0x4d35532fad69a259, 0x3c433645435b0afb, 0x849228ca674b8814, 0x541a917df85b5e3c, 0x69182d5099c073fe, 0x4b0bae6867de6f42, 0xf3ffe72b6b645d00, 0x80876fed211a0b69, 0xde7ef8fb62b9fdf2, 0x3b404ed04fc2c76d, 0x69cf79f465c2b138, 0x5508bf2fc25e07df, 0x93cedd31781269a6, 0x3681c2e829a35a06, 0xbea744aaead555af, 0x1e3135718952c9e0, 0xba9431aaeb99ac9e, 0xd316f8c5bdf90e52, 0xc87fdcf081558816, 0xfa4de81f5a7c370a, 0xf8d07dc2220e6a5b, 0x6c8ec63472f901cf, 0x50c48bf402178d92]

private theorem rounds107_0 : sixRounds 0 (by decide) absorbed107 = quarter107_1 := by
  decide +kernel

private def quarter107_2 : Vector UInt64 25 :=
  #v[0xa505c7f4fe681feb, 0xec4303212d4d6669, 0x4b077131fba2d48a, 0xe638fe20a813b8f6, 0x99e1097d3d905546, 0x8c17ed8119c22136, 0xcbbb2aae00fde538, 0xac8f279bfe1fd52c, 0x33bdaea40186be1b, 0x3b99dfe7f71d6184, 0x2d859877f5af2fee, 0x39a8a9b96ab11c35, 0x4a116a593432f43c, 0x63c538c5186de2a0, 0x852fbf68ed1bb255, 0x295bd134e84d93c8, 0xfa829d6534825575, 0x65a53c9e50e18b36, 0xbd711762be02ef6a, 0x841441dc6c64a679, 0x830895b5801a6a7c, 0x75d66e0056b4fb6d, 0x8c1cfe533a4e8d7e, 0x6ee6229d0156854a, 0xa4bb6918a46795e3]

private theorem rounds107_1 : sixRounds 6 (by decide) quarter107_1 = quarter107_2 := by
  decide +kernel

private def quarter107_3 : Vector UInt64 25 :=
  #v[0xbd5a2c3b8a8ff262, 0x1069d5f7cb062e0a, 0x92f0d55081e3fc95, 0x25f6d7623596ca74, 0xb10aaa2e06b3b495, 0xf280cdf64004f776, 0x3bbe0cf2fc7ccf3e, 0xd26de50fb9ccf2fc, 0x43b3f5aa4e7aaa8e, 0x4e4c5b5804bce8e9, 0x38e0e14ce55123c4, 0x488bba3d753d510, 0x5269e5d9b4728c2d, 0xda5f6e24fbc8a6ef, 0xc5c06201c312dfc0, 0xed7b2981496a77b, 0x106f1d1f03dafd1e, 0xb261715a95f52327, 0xc9892ee461ef257b, 0x59be1907441ebfcf, 0x6768936abea39980, 0xe9d3f0061163090c, 0xd0959885ce851d82, 0xc70af20e6b815749, 0x666f6165f3c282f0]

private theorem rounds107_2 : sixRounds 12 (by decide) quarter107_2 = quarter107_3 := by
  decide +kernel

private theorem rounds107_3 : sixRounds 18 (by decide) quarter107_3 = state108 := by
  decide +kernel

private theorem perm107 : KECCAK.f1600 absorbed107 = state108 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds107_0, rounds107_1, rounds107_2, rounds107_3]
  rfl

theorem block107 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes107 ++ tail) state107 =
      KECCAK.Bytes.run 0 tail state108 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes107 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb107 ws)) := by
    rfl
  exact (step state107).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words107).trans perm107))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
