import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb138 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x65 0x72 0x75 0x74 0x61 0x6e 0x67)) 1 (by decide) (UInt64.ofBytes 0x51 0x90 0x52 0x1 0x82 0x44 0x60 0x0)) 2 (by decide) (UInt64.ofBytes 0x90 0x1 0x64 0x60 0x3 0x90 0x81 0x90)) 3 (by decide) (UInt64.ofBytes 0x88 0x88 0x88 0xfa 0x48 0x61 0x5b 0xfd)) 4 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x5b 0x56 0xb1 0x3d 0x61)) 5 (by decide) (UInt64.ofBytes 0x81 0x5b 0x56 0x50 0x50 0x50 0x50 0x50)) 6 (by decide) (UInt64.ofBytes 0x81 0x20 0x1 0x83 0x92 0x20 0x60 0x51)) 7 (by decide) (UInt64.ofBytes 0x20 0x91 0x90 0x91 0x1 0x83 0x91 0x51)) 8 (by decide) (UInt64.ofBytes 0xc3 0x73 0x8b 0x7f 0x51 0x80 0x40 0x60)) 9 (by decide) (UInt64.ofBytes 0xcc 0x2e 0x51 0x3d 0xfe 0xb8 0x9b 0xc6)) 10 (by decide) (UInt64.ofBytes 0x7b 0x9f 0x23 0x79 0xcc 0x59 0xf7 0x4c)) 11 (by decide) (UInt64.ofBytes 0x5d 0xa7 0xa9 0xca 0xfa 0xf 0x9b 0x17)) 12 (by decide) (UInt64.ofBytes 0x1 0x86 0x81 0xf 0x40 0x39 0x2b 0x52)) 13 (by decide) (UInt64.ofBytes 0x52 0x93 0x90 0x93 0x1 0x82 0x80 0x52)) 14 (by decide) (UInt64.ofBytes 0x52 0x91 0x90 0x91 0x1 0x83 0x60 0x60)) 15 (by decide) (UInt64.ofBytes 0x60 0x30 0x52 0x1 0x83 0x80 0x60 0x46)) 16 (by decide) (UInt64.ofBytes 0x52 0x91 0x90 0x91 0x1 0x84 0x80 0xa0))

private def absorbed138 : Vector UInt64 25 :=
  #v[0x8a6a29d12b70e68, 0xd693509d4121ae13, 0xfe1c4a46cbbeeff, 0xf6c74852bc532af0, 0xee1967ec29c48efb, 0x5032fb187ac992d7, 0xa0b1354603e0c63d, 0x5b2c9c5b6046862, 0x4fe85c0a1214caf7, 0x6b450366f791cb64, 0xcd36d1bb702c4da3, 0xedcfdf515359b4b1, 0x515bd2e5e2c854ca, 0x458b7e274d6597d1, 0xad0c4ac8e52f2efd, 0x994ee4e0423fcee9, 0x14c9162f9803c9ee, 0x709e44aace62d30c, 0x8e6fb295414d4db5, 0x19e28b407cf872d5, 0xc53db0949511579f, 0x4180d83c67b7284a, 0x288e3e8aeffb85a4, 0x632994b854ffd0e1, 0xa0d12f0f787c9f13]

private theorem words138 : absorb138 state138 = absorbed138 := by
  decide +kernel

private def quarter138_1 : Vector UInt64 25 :=
  #v[0x226dc16050cfca96, 0x2035481dc00a4dbc, 0xabf84f1935d450b6, 0x3bf481c7db85540d, 0x370de446c8e58f09, 0xedc6771258dda03, 0x541f189b12b93c0d, 0x5ec3b3908f49061c, 0xc0495e03510f04d, 0x4fcb09b108e1ec62, 0x6f32b9fb9d64dd0f, 0xf4c7f11f46144c6a, 0x175c0695e0556df, 0x7399992cae428d2f, 0xcbd8b480f0e89454, 0x74a9ca1b58072693, 0xd103db3fb3135d7e, 0x85815cef085f2139, 0xb38831cda4b69a88, 0xd48a77e651a4dafe, 0xbf838284ae7d0489, 0xf0d962f67d3904c8, 0x7a47ea58052bca6e, 0xa9f204804d4d2ad5, 0x5bafe3c3c3b708b4]

private theorem rounds138_0 : sixRounds 0 (by decide) absorbed138 = quarter138_1 := by
  decide +kernel

private def quarter138_2 : Vector UInt64 25 :=
  #v[0x953816a90253329, 0xf2e1e538cbc73f8c, 0x3767ed1d12cb7f04, 0x42dfa02456f73d58, 0xbeb3051345fe586c, 0xd290042d730d118b, 0x4d15276d67b4bf7f, 0x9958ad55c38b334c, 0x8d070e160817524, 0xb39522b1b7b0e07a, 0x24a6880590208db1, 0xdbeb49ec720e6df7, 0x6cad818b2309da06, 0xf6f7acd99ba7aca6, 0x4958f46ee94f26bb, 0xedcb03655c11d5a1, 0x9f10ea4732563428, 0xc9476f1fa48a5e59, 0x6e4723717d1615af, 0x31f15974b332a849, 0x32a3d5ca1c5e080a, 0x685df29606fa7ca5, 0xf971e6944a611e64, 0x58a3c9a9ffdb987e, 0x500790a415813a28]

private theorem rounds138_1 : sixRounds 6 (by decide) quarter138_1 = quarter138_2 := by
  decide +kernel

private def quarter138_3 : Vector UInt64 25 :=
  #v[0x5a5902950a39ba5b, 0x18a369c1cdd941db, 0x1384811172feb57a, 0x1e20fe2df8631139, 0x863a8569a1cc6d04, 0xd1fcc44e9b7e3665, 0x7713f115d87bb985, 0x5c103d901d56e340, 0xfde578bf8398250c, 0x2219953a13383438, 0x83a06f59e3dab7a9, 0x55985f2dc6b3b09e, 0xb1dd193b8e821380, 0x55455a3edf9629cc, 0xb51f65db7ec3b0ef, 0xb10ceb3d5fc21c4c, 0xdd23a96ae633e870, 0x5d01b3878cab3b64, 0x8fcff8fd7a288fe9, 0x4aca6c06ecab31c6, 0xeed173d3f7fefd6, 0xa6febce732348a0, 0x9aada038352edcc, 0x252f2318dfbb649f, 0xf1780b6c73c53d7d]

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
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes138 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb138 ws)) := by
    rfl
  exact (step state138).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words138).trans perm138))

private def absorb139 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x91 0x90 0x3 0x84 0x80 0x51 0x81)) 1 (by decide) (UInt64.ofBytes 0x90 0x1 0x92 0x90 0xc0 0x60 0x52 0x81)) 2 (by decide) (UInt64.ofBytes 0x56 0x90 0x20 0x1 0x91 0x51 0x80 0x52)) 3 (by decide) (UInt64.ofBytes 0x88 0x88 0x85 0x89 0x82 0x49 0x61 0x5b)) 4 (by decide) (UInt64.ofBytes 0x80 0x40 0x60 0x5b 0x56 0x9e 0x4d 0x61)) 5 (by decide) (UInt64.ofBytes 0x79 0x7a 0x40 0x10 0x8c 0x80 0x7f 0x51)) 6 (by decide) (UInt64.ofBytes 0x63 0xc0 0x38 0xea 0xc7 0xf2 0x3e 0x6f)) 7 (by decide) (UInt64.ofBytes 0x3c 0x3e 0xc6 0xa1 0xb8 0xd2 0xa9 0x8e)) 8 (by decide) (UInt64.ofBytes 0x9d 0xe5 0x4a 0xe8 0x6c 0xf5 0xe1 0xa9)) 9 (by decide) (UInt64.ofBytes 0x73 0x52 0x1 0x82 0x20 0x60 0x3c 0xf7)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x82 0x16 0x8c 0x80 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x16 0x8b 0x90 0x52 0x90 0x81 0x1 0x84)) 14 (by decide) (UInt64.ofBytes 0x82 0x80 0x60 0x52 0x1 0x83 0x60 0x60)) 15 (by decide) (UInt64.ofBytes 0x1 0x82 0xa0 0x60 0x52 0x90 0x8a 0x1)) 16 (by decide) (UInt64.ofBytes 0x88 0x1 0x82 0xc0 0x60 0x52 0x90 0x89))

private def absorbed139 : Vector UInt64 25 :=
  #v[0xac74a56f9238cd8, 0x14ef39126a752128, 0xec0c5698568fc873, 0xbb35109ef717d6ec, 0x32230af5c8300768, 0x7112fcdba3873d21, 0x7d46af11223b2f50, 0xbe854c78537a4411, 0x34be501a1ac1a8f9, 0x7cb205430b210d28, 0x3b7b610f0738c0e0, 0x870557651736c7ff, 0xfd581f340aa445c4, 0x3018035932decbbc, 0x99b7e42057c6834b, 0x1cbed704ed2539dc, 0x4d4b43c2f4965802, 0x1afbe86117e1a4ac, 0xfb35c810419f982c, 0x103db3f005ba5100, 0xe5d6c09ea875ea6b, 0xc290a7193d33f37a, 0xd139497407fe8c0d, 0x85b5ae4cc89a1f02, 0x73e1e870b1d409be]

private theorem words139 : absorb139 state139 = absorbed139 := by
  decide +kernel

private def quarter139_1 : Vector UInt64 25 :=
  #v[0x9e0f4e9aaff7a658, 0x5adbdb9befe39df7, 0x5868e7fa80dde57e, 0xd319c9200b1eb3f1, 0xeb74ba141211ec70, 0x30083603a7aacb56, 0x23210d7ed97954e3, 0x7191c768297a1caa, 0xd96087fcab7360ff, 0xff6bb5a3b49d1c21, 0xccc7980bb5166361, 0x14808b61b0a44d63, 0x45ebf0b3abf730e6, 0xc48963914074e316, 0x247b0833674386e4, 0xe53b7b9c466fd010, 0xcfdab893f9828db, 0x76e642b5f1da4457, 0x2cd814f80feb7b8f, 0xfee37e35ce49b0aa, 0xde4471bbdefe432a, 0xe29df91c0d446b7a, 0xe454eec4afa29518, 0xa3a9aa4e77bc2fcd, 0x1ae1d4c5ce726333]

private theorem rounds139_0 : sixRounds 0 (by decide) absorbed139 = quarter139_1 := by
  decide +kernel

private def quarter139_2 : Vector UInt64 25 :=
  #v[0x61ffdd337bf8dd14, 0xb0e4e07956dee731, 0xe3d53154ce323a2d, 0x952d08132155ca0, 0xc36049e498131906, 0x1da74d5354766d78, 0xea7032f945606d78, 0xe02691a900ed5e36, 0x1e115b237a4ca8b0, 0xc498a49e1925c3b3, 0x9c31efe22854b2c7, 0xa96a7f3bbca55959, 0xa8b62dce41df10d, 0x4956081a3eeafc30, 0xa03fe6f01a2d06f1, 0x27020cad84f38ed0, 0xf04df2df6eaae791, 0x6454c9783393ce64, 0x65835829c5a65963, 0xebe530cff1d726f3, 0x5d435091b4cfb343, 0x5034821bf30ad792, 0xf59f1453536114e3, 0xf15ccfbb34f68f45, 0x3072c4388f91f00d]

private theorem rounds139_1 : sixRounds 6 (by decide) quarter139_1 = quarter139_2 := by
  decide +kernel

private def quarter139_3 : Vector UInt64 25 :=
  #v[0x5f0dd9f6d3c77537, 0x1121f5259d157145, 0x2442ddfbfdd61dc1, 0xbd50a7de6675d36, 0xc384b45275a155ac, 0x9286a5c96ecd8476, 0x4fff177194caa9, 0x84179ddb75fc6ba4, 0x5845566876de7ce6, 0x17b7cd1597e72797, 0x50e6f0a9c27df85f, 0x80eab578e75861bf, 0x51b4f2f169597185, 0xa79d8acf7b6e92b8, 0xc53ad8cbeb070fa5, 0x72897e51bc93d4ef, 0x875735adb6d7fa5e, 0xb45f63a0975cd33, 0x733bba9f21903039, 0xa067b6314c238d28, 0x88887a468b9b9125, 0xa92994c0bb9761f8, 0x5f4f90fc39e5108f, 0xfde40412899c3bf9, 0x6e4171c5383ce97d]

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
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes139 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb139 ws)) := by
    rfl
  exact (step state139).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words139).trans perm139))

private def absorb140 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x88 0x1 0x83 0x80 0xe0 0x60 0x52 0x90)) 1 (by decide) (UInt64.ofBytes 0x90 0x3 0x84 0x80 0x51 0x83 0x52 0x90)) 2 (by decide) (UInt64.ofBytes 0x90 0x0 0x1 0x61 0x52 0x81 0x1 0x91)) 3 (by decide) (UInt64.ofBytes 0x54 0xf 0x60 0x52 0x92 0x90 0x1 0x92)) 4 (by decide) (UInt64.ofBytes 0x86 0x90 0x15 0x4a 0x61 0x90 0x91 0x90)) 5 (by decide) (UInt64.ofBytes 0x5b 0x56 0x2c 0x4d 0x61 0x86 0x86 0x86)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x61 0x14 0x16 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x7f 0x51 0x80 0x40 0x60 0x57 0x97 0x4a)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x1 0x82 0x4 0x60 0x20 0x60 0x52 0x81)) 15 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x24 0x60 0x1e 0x60 0x52)) 16 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x7f))

private def absorbed140 : Vector UInt64 25 :=
  #v[0x6b1df13a59ea1867, 0xc18c5214e9abb6ea, 0x583b2e2fdc0948eb, 0x704f43c114b4f710, 0x3dbdb064ede86231, 0x8d34f25f930364e7, 0xb0859d30ef5787ec, 0x4634433cf521c980, 0x474c4df64b74d38, 0x5aaf9befcbfe411, 0x66952f8e3831b288, 0xa863f3c684eae6c3, 0xd94ad1a63059c6da, 0x8e20db442d520db8, 0xcee8a819c8726d18, 0xb75263299a1addff, 0xfdbaa481fe69c349, 0xad00345371471c9e, 0x3723d9705674bcc2, 0x289c2c72da44f70d, 0xa3d71d307943bb33, 0x5f0afaaa57be49d6, 0x31d2a715cd8c945c, 0x520e6caec897e1f9, 0x1d2b5f292f13d94d]

private theorem words140 : absorb140 state140 = absorbed140 := by
  decide +kernel

private def quarter140_1 : Vector UInt64 25 :=
  #v[0x2573bbc57caaa813, 0xabb577baa067035c, 0x4de5f48d40a7cca6, 0x5052b645aaecad8, 0x2fd1a4af574d04f8, 0xd59b4dbf5132ede6, 0xca04d8c30bb99db3, 0x9a14da46c490b6ad, 0xc1ae402ae0a4a28a, 0x84920d77796a68ee, 0x44cf02112ce97d79, 0xcd3b19f373d4bb56, 0xfd2321b58bb25d5b, 0x59b6ceb5d4224312, 0xcf1d5043cfc89010, 0x8bec638d10f30ce3, 0x1568f99db960bc4d, 0x92ab1770fdf7ad54, 0x4545de8904ddf709, 0xcdefa965105521c5, 0x944783495d762c3, 0xd3145dd6bfd02767, 0x5f9f89a7711b119f, 0x304f9e6734f0bb04, 0x996fef083e792125]

private theorem rounds140_0 : sixRounds 0 (by decide) absorbed140 = quarter140_1 := by
  decide +kernel

private def quarter140_2 : Vector UInt64 25 :=
  #v[0xd3da1a4f78b5f48b, 0xe16d1cbff2ac25f, 0x2057e1588022f5ba, 0x4b25b99a3c7d2c6b, 0xe7083825d052d44b, 0x753f2a50b5a6670b, 0xdb5e1e64614a2c7b, 0x7f9d07ac71d04d22, 0x9902a62f43e5542e, 0x60d6f043006f7b9b, 0x3db2e9b085fac354, 0x8439cc1621d7d7fd, 0xf65dd7ec78356e0a, 0x3c1064dbca21428b, 0x5f8fce256b4c6fa3, 0xdf448ad46ba89ae5, 0xbcd035e81b038a69, 0x23524a3319b0aae3, 0x668bbb2fe6ef76cd, 0x1cd5a1befdf08518, 0x5b403419386bb7f5, 0x8b1915061cd79d51, 0xd0bd6c45292f2fb2, 0xdbb2bb695552f216, 0xb1c3084975de6ad4]

private theorem rounds140_1 : sixRounds 6 (by decide) quarter140_1 = quarter140_2 := by
  decide +kernel

private def quarter140_3 : Vector UInt64 25 :=
  #v[0xa791c5d055f9f601, 0x1e326bae29b6b473, 0x1f0513039f8998be, 0x1c70ee65014885e3, 0x57d362e5853b1d5e, 0xb76fbf68299a3d53, 0xdcaf803a2aff1e2, 0x991e80d761eea4de, 0xda8c9996dc7ebcb4, 0xc9e61e81524e87b6, 0xc5ac6dc3d1beba1a, 0x2c501f7f416b263f, 0x317bd844b7a90264, 0xfe4951767b1de224, 0x224a5d025d61fd65, 0xc93e104e8235d597, 0xc2fa912c38609602, 0x9154b82850ada8c, 0x4fab71dcebad6854, 0xe750255b7d5a838c, 0x3c180d082be0129c, 0xec8e334cd1a64939, 0x14b6841fb8d05e24, 0x849f35990e398e8d, 0x720f1fb6be25d8e4]

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
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes140 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb140 ws)) := by
    rfl
  exact (step state140).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words140).trans perm140))

private def absorb141 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x6e 0x69 0x20 0x3a 0x32 0x56 0x6e 0x65)) 1 (by decide) (UInt64.ofBytes 0x69 0x73 0x20 0x64 0x69 0x6c 0x61 0x76)) 2 (by decide) (UInt64.ofBytes 0x0 0x65 0x72 0x75 0x74 0x61 0x6e 0x67)) 3 (by decide) (UInt64.ofBytes 0x51 0x90 0x52 0x1 0x82 0x44 0x60 0x0)) 4 (by decide) (UInt64.ofBytes 0x90 0x1 0x64 0x60 0x3 0x90 0x81 0x90)) 5 (by decide) (UInt64.ofBytes 0x61 0x86 0x8a 0xa1 0x4a 0x61 0x5b 0xfd)) 6 (by decide) (UInt64.ofBytes 0x8a 0x8c 0x45 0x61 0x5b 0x56 0x5e 0x4e)) 7 (by decide) (UInt64.ofBytes 0x61 0x5b 0x56 0xb1 0x3d 0x61 0x8a 0x8a)) 8 (by decide) (UInt64.ofBytes 0x4d 0x61 0x88 0x88 0x85 0x89 0xb8 0x4a)) 9 (by decide) (UInt64.ofBytes 0x7f 0x51 0x80 0x40 0x60 0x5b 0x56 0x9e)) 10 (by decide) (UInt64.ofBytes 0x43 0x87 0xa1 0x67 0xdb 0x6c 0x7c 0x7c)) 11 (by decide) (UInt64.ofBytes 0xd 0xf5 0x35 0x9b 0xfa 0xc6 0x9e 0xf4)) 12 (by decide) (UInt64.ofBytes 0x92 0xc5 0x4c 0xed 0xcb 0x5 0xed 0x52)) 13 (by decide) (UInt64.ofBytes 0x67 0x22 0x1a 0x1c 0x50 0x44 0x3b 0xe1)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x52 0x1 0x82 0x20 0x60)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed141 : Vector UInt64 25 :=
  #v[0x6e94a17783b73710, 0x5e961aa083487b1d, 0x6e03768356ffd21f, 0x9689831684559ed4, 0x197727d7732f995c, 0x339e007fcf238821, 0x496aa6d6d4b69ca0, 0x41b7f06b8e104865, 0x44e6857c62af2317, 0x2013f754ac6e0d69, 0x802fa0300f28e72c, 0x99632d3193355dcd, 0xcf00f23c64f1cd95, 0x69cf480efa0f5682, 0x348f28df1c327ff1, 0x1142084a5b9906cf, 0x3b48d15edf6510d, 0xe428a5e2c66758db, 0xe595bbdd06c16acd, 0x89c86187869d7b6d, 0xbb0a0f0d9a909b86, 0xe715503f8bceacb6, 0x97401d4f779e7368, 0xf4ccb37851925512, 0x8d9fe2593264b85a]

private theorem words141 : absorb141 state141 = absorbed141 := by
  decide +kernel

private def quarter141_1 : Vector UInt64 25 :=
  #v[0x70c57085fafdb155, 0x65a8469c6f5ac291, 0x4659685c86a0b0fc, 0x1c3334e7d5d5ca98, 0xede92ff504f5fc8b, 0xdde187009840d878, 0x3c3d498738d0c5d5, 0x19cc9b779d801109, 0x37a3c2455bbee762, 0xb4c8a15e5f165cd8, 0xa12b62b3b0720d, 0x859c052fa6625ef4, 0xcd997d4973a93730, 0xc0c0f34ee0a0438c, 0x4c9de0b765e6cf58, 0x106b51dda1fd152a, 0xe48cba7503ed9f43, 0x4d41817c03cd620b, 0xb49d3161f0a44d85, 0xb79d8991c3eea22a, 0x7191aee532c96fbb, 0x7cc072f84ab0090c, 0x424743550bf444e9, 0xe6e5d14b004e2f12, 0x9db93f2e3531d025]

private theorem rounds141_0 : sixRounds 0 (by decide) absorbed141 = quarter141_1 := by
  decide +kernel

private def quarter141_2 : Vector UInt64 25 :=
  #v[0xed8359763e78a00, 0xe2896c430f642394, 0x4b1e920463de5e11, 0x1dd7bb2f83509c0, 0xba61e8b745397993, 0x4dde9e3d3418b795, 0xdd4630407e6b6395, 0x4d8588e93e34d95b, 0x44c99b8e8ff93263, 0x1059bac9729e054c, 0xcb5e4d851155ae79, 0x4f7d9adc4019ed60, 0xdd00589ad4925ed9, 0x1b83b2cb6cb00058, 0x111a73c11580f909, 0x92f62406d70d90af, 0x887a085e3955f5d3, 0xa17175501b23ca7e, 0xf97053e85aa7fd42, 0x9663be6b9da958d, 0x153de875c21441e2, 0x6a065a3dfd7a0851, 0x3fc4b343b4ba4049, 0xe274e0ea16883ac4, 0x31aba65625fba93b]

private theorem rounds141_1 : sixRounds 6 (by decide) quarter141_1 = quarter141_2 := by
  decide +kernel

private def quarter141_3 : Vector UInt64 25 :=
  #v[0x861ca71437f04d86, 0x507f6635f92216b5, 0xeea7b1a46624f7b0, 0x35ac9324cd716eb6, 0xc45c07d3988e44cf, 0xc368829aaa9ca49f, 0x3191a92759066fc8, 0xbb4314a2a0490aa7, 0xc8cbb58cef33f735, 0x2b9e3e93f9579a7f, 0xa5d4690a116eb3d6, 0xdecab3f57740a68d, 0xebd86239dc4d8f3c, 0xd7e57b149efe572, 0xd6b3346bf528a639, 0x1edce543ae284ce1, 0xde60913eba901278, 0xc3b0c02fc05c9e69, 0x942e583c5f0eefa5, 0x19a881871df868c3, 0x3f6358a52be97a70, 0xd29ea45f0f9d81f7, 0x3568d77f177a3061, 0xdb730f5c7f2538c9, 0xfab43edb1131dd55]

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
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes141 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb141 ws)) := by
    rfl
  exact (step state141).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words141).trans perm141))

private def absorb142 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x84 0x82 0x16 0x8c 0x80 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x60 0x60 0x16 0x8b 0x90 0x52 0x90 0x81)) 2 (by decide) (UInt64.ofBytes 0x8a 0x1 0x82 0x80 0x60 0x52 0x1 0x83)) 3 (by decide) (UInt64.ofBytes 0x90 0x89 0x1 0x82 0xa0 0x60 0x52 0x90)) 4 (by decide) (UInt64.ofBytes 0x52 0x90 0x88 0x1 0x82 0xc0 0x60 0x52)) 5 (by decide) (UInt64.ofBytes 0x52 0x90 0x88 0x1 0x83 0x80 0xe0 0x60)) 6 (by decide) (UInt64.ofBytes 0x1 0x91 0x90 0x3 0x84 0x80 0x51 0x83)) 7 (by decide) (UInt64.ofBytes 0x1 0x92 0x90 0x0 0x1 0x61 0x52 0x81)) 8 (by decide) (UInt64.ofBytes 0x91 0x90 0x54 0xf 0x60 0x52 0x92 0x90)) 9 (by decide) (UInt64.ofBytes 0x86 0x86 0x86 0x90 0x4b 0x4b 0x61 0x90)) 10 (by decide) (UInt64.ofBytes 0xff 0x73 0x5b 0x56 0x2c 0x4d 0x61 0x86)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xcd 0x4b 0x61 0x14 0x16 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x80 0x40 0x60 0x57)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed142 : Vector UInt64 25 :=
  #v[0x49a4672d1022de40, 0xbee4acaffa99ee9e, 0x10395439c87991dc, 0x198d9b7c50afb0bf, 0xec9d570725e70e0b, 0x44e2565ca906073a, 0x4a0edfe163d9fc7, 0xffd28e5e5452f643, 0x3d67fa9121216546, 0x6476170eaf70f766, 0x65b3b9345956342f, 0xc1799ee98113c81b, 0x4699c1ec0a7db70b, 0xcee66df25ff25029, 0x992841008dbe1edc, 0x2b5b6700b8df9484, 0x5a17b294b5cd518f, 0x625b4e6f5a15c0b1, 0x7f23028447a53c7a, 0xf3ffb33a7ae123d8, 0x61f20154b0de75b5, 0xf29408e38fcc0ef5, 0x64974857c41597a3, 0x81119ac72e5f3f95, 0x28b1e10cc6145f58]

private theorem words142 : absorb142 state142 = absorbed142 := by
  decide +kernel

private def quarter142_1 : Vector UInt64 25 :=
  #v[0xaddd0e8ad6e6011b, 0x69b0ffc6d05ee111, 0x6fd38897492ea96c, 0xcf3ce97055f579af, 0x7bfd165283d9fcfa, 0x4a55773b3f39db6c, 0xa6dd32f306ff9407, 0xb9685df9020e5867, 0xc8148523ad2de031, 0xefe56f2bdd4ef938, 0x172c40b3157aba80, 0xa244b823449442c5, 0xe0192f79dd3468c8, 0xdd887c436c13e322, 0x59c43f89e4b0a42c, 0x14afebbe893beb53, 0x7aa2e856067e98f2, 0xf2b5ea066c9aff47, 0xc9eedbd395154788, 0xa5f485514a26fd6e, 0xed3a16a9fd0fdf, 0x79625d10320cecbd, 0x49294679d852102f, 0xe53524c033c33526, 0x4d7bf9527e66eca6]

private theorem rounds142_0 : sixRounds 0 (by decide) absorbed142 = quarter142_1 := by
  decide +kernel

private def quarter142_2 : Vector UInt64 25 :=
  #v[0xb3d350c0f875a6b6, 0xed475aa1f213fd7c, 0xf22682caec8b316f, 0xa09473f0ca59b937, 0xeb638fab5192e8cf, 0xef0f5864749caf9f, 0xcc5a898040be67b7, 0xecce48a48d01765c, 0x2509de79ae4799fc, 0x148128f341c4c115, 0x2dc2dc877e3c2a81, 0x46f85fbc077efadc, 0x742239e2cd9c6ea5, 0x242b7d01bb2ed858, 0x253141a30bc03283, 0xa0a96b1dbbba6c79, 0xd191feb72b3f90ac, 0x730fb601a4cfeab, 0xf1b5cce4062b2b40, 0x8b6f96522b90d059, 0x172215ce167854b5, 0x459cbc14c3898b57, 0xe85bd93314a00f52, 0x78c20055203f1070, 0x4f67549217649717]

private theorem rounds142_1 : sixRounds 6 (by decide) quarter142_1 = quarter142_2 := by
  decide +kernel

private def quarter142_3 : Vector UInt64 25 :=
  #v[0x9458be26c4198884, 0xe2b4d2e9ee02ab4a, 0x31782efb25f32a4d, 0x858e502724698249, 0x4dff52c5576ad130, 0x94cf61118901845c, 0x5bbded8d32026406, 0x96cd47ae1a41ab4c, 0x96396141a1330b4c, 0xd2ec3601ffc0f4e3, 0x2a5d23e344aea90, 0xebe7101c2627548d, 0x129ce54a79566e03, 0x23e51cf979a18168, 0x7ae27b45742e7764, 0x7cc36993d53cdf0a, 0x29ee752b73e53128, 0x4e6b789903c6fdf, 0x41588306a1a05055, 0x6a359b87dd648c2, 0xd952588b655574a3, 0xf53b97ede2cf0d01, 0x6786d408679363bc, 0xfce5576823bada8d, 0x566a5742226f22f]

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
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes142 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb142 ws)) := by
    rfl
  exact (step state142).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words142).trans perm142))

private def absorb143 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x1 0x82 0x4 0x60 0x20 0x60)) 3 (by decide) (UInt64.ofBytes 0x46 0x7f 0x52 0x1 0x82 0x24 0x60 0x1e)) 4 (by decide) (UInt64.ofBytes 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61 0x69)) 5 (by decide) (UInt64.ofBytes 0x61 0x76 0x6e 0x69 0x20 0x3a 0x32 0x56)) 6 (by decide) (UInt64.ofBytes 0x6e 0x67 0x69 0x73 0x20 0x64 0x69 0x6c)) 7 (by decide) (UInt64.ofBytes 0x60 0x0 0x0 0x65 0x72 0x75 0x74 0x61)) 8 (by decide) (UInt64.ofBytes 0x81 0x90 0x51 0x90 0x52 0x1 0x82 0x44)) 9 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x1 0x64 0x60 0x3 0x90)) 10 (by decide) (UInt64.ofBytes 0x5e 0x4e 0x61 0x86 0x8a 0xd7 0x4b 0x61)) 11 (by decide) (UInt64.ofBytes 0x8a 0x8a 0x8a 0x8c 0x45 0x61 0x5b 0x56)) 12 (by decide) (UInt64.ofBytes 0x81 0x0 0x60 0x5b 0x56 0xf8 0x3e 0x61)) 13 (by decide) (UInt64.ofBytes 0x57 0x8b 0x4c 0x61 0x15 0x11 0x84 0x84)) 14 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed143 : Vector UInt64 25 :=
  #v[0xadc6fb2468512310, 0x6ef2aca77b6eff6, 0x7e4c41116e569350, 0x302111107fbfe3af, 0xd31d5843fc5f96e2, 0x7fe0a97d53db52c9, 0xd3f9b4a070535173, 0x5398ff6fff3f417f, 0x39fc9b4aaefbcdc7, 0xa9e64929f1ec9dd7, 0x47c84d3fc2beaf5c, 0x7adac6c975b42a16, 0xfbf0fc0465a9d3d, 0x617913c87aa01433, 0xaa2e9ca1da6bc206, 0x1bbb165e9f505371, 0xc222fa7b24d109e1, 0xd796fb75ab634ba, 0x1ff9154df04404, 0x8c21514b8c962543, 0x100d560f13feaab7, 0x5c9430f7d3ccd0c1, 0xa044755b02a28f68, 0xddf580cd0feb651d, 0xd2d1b3e5b0ac9342]

private theorem words143 : absorb143 state143 = absorbed143 := by
  decide +kernel

private def quarter143_1 : Vector UInt64 25 :=
  #v[0x66dc0b881d6a9f38, 0x55c0ecbc5cf29fd1, 0x516e94e7631391ca, 0xafd409da1df1eb16, 0xcacb3149a06f7f21, 0xab9f78d4768d7015, 0x49f7379fbadd4a1a, 0x647c2ca3486d2e3c, 0xff67fa484476ad35, 0xd2ec4b733fdc43eb, 0x3a837bf6595e981c, 0x8a24bd0b9560bf7, 0xc3a4b8296c4719c6, 0xd39c2d99227203d, 0x64f975f83a20f7b6, 0xf6c0cc038fc086e3, 0xf35b2b9bddca6ec8, 0xa58d0b33f878a41a, 0x5a032b3ff62a5e68, 0xfead82f8dfab39b7, 0x12797bec30c1a2b1, 0x9de7cd6227b61bea, 0x3006342c2801b44, 0x65571f274db31a87, 0xbdc107172d63b4da]

private theorem rounds143_0 : sixRounds 0 (by decide) absorbed143 = quarter143_1 := by
  decide +kernel

private def quarter143_2 : Vector UInt64 25 :=
  #v[0x765d5a45f444f9d7, 0xec9b6af70075dfe3, 0x867225c7580bd7f, 0xb1d8e4edf1784b6e, 0x3fc6a780eb8a76c5, 0xc4e7123989511823, 0xa9d4a2ef7ac82bce, 0x328eb0b325e1a1fd, 0xe359a4cc7dcb2366, 0x703ace0c4a0e8fae, 0x9f6176bf41eeacf3, 0x9cb8cb66937619f5, 0x6d39ddc1384a66af, 0x4ba336c0df3de5b9, 0x554e4ba3c00af5c7, 0x4e79f8c3226ef33a, 0x22628b0ec252b7ec, 0x597948d63c463dfd, 0x1e89e515e06bf69e, 0x44ebf64b44bf0b5e, 0x77d999a6f33bd8b6, 0x7bc9ef388d08c2b0, 0x3b27138dd9852ddf, 0xb659b4f7c3369af5, 0xdd6f511403a67cc9]

private theorem rounds143_1 : sixRounds 6 (by decide) quarter143_1 = quarter143_2 := by
  decide +kernel

private def quarter143_3 : Vector UInt64 25 :=
  #v[0x47b550c178debdbe, 0x20d7bb01dfdbe2cd, 0xf6725d0c5006bea7, 0xb5f1e2f25e4204c5, 0xb42709487a1c93bf, 0xa420cd7dcb4d9da8, 0xf976833560ef2d51, 0x91373314aa2546bd, 0xeb62d2beb20d1dcf, 0xe3905c7ae25ef828, 0xc42c86db3d7b7be9, 0x5c19fce4ecec77fb, 0xb83cb986ef7d85a4, 0x5317bed5dfb51ee7, 0xea5bca4dfdffc0d0, 0x4f3ae6238a0043aa, 0x87544d5823a6e6bb, 0x99e19113b4e584ad, 0xa108b5c85ed61572, 0xc24eef1e5ff30622, 0xda93edcba828c06, 0xca9dd767c2ebe741, 0xb01f7f7b66701f27, 0x1b7ada636fa2eb6, 0xe653f1368097210f]

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
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes143 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb143 ws)) := by
    rfl
  exact (step state143).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words143).trans perm143))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
