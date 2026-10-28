import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb036 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x1 0x4)) 4 (by decide) (UInt64.ofBytes 0x52 0x81 0x25 0x60 0x52 0x82 0x3 0x81)) 5 (by decide) (UInt64.ofBytes 0x60 0xc5 0x59 0x61 0x80 0x1 0x20 0x60)) 6 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x40 0x60 0x39 0x91 0x25)) 7 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x85 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x3 0x60 0x52 0x81 0x90 0x0 0x60 0x16)) 12 (by decide) (UInt64.ofBytes 0x54 0x20 0x90 0x40 0x60 0x52 0x20 0x60)) 13 (by decide) (UInt64.ofBytes 0x13 0x61 0x15 0x16 0xff 0x60 0x90 0x85)) 14 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57 0x68)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed036 : Vector UInt64 25 :=
  #v[0xf773aeca4e110c36, 0x5eab0d9b6e0480cb, 0xb12cfe0632f743d0, 0x466ec2c09beaec64, 0x516e1b418409d103, 0x535af5914696663c, 0xac440827bd525f26, 0x3b1ef80f46e177ce, 0x507fc74ada5db5b8, 0xa6f6375c07fc8ed3, 0xe5790e87fc9c9748, 0x7fe46851b3d22223, 0xd39fced443046222, 0xd11a3150163476fb, 0xbd5a0509b7ca6877, 0xf68302ca2f31dca6, 0xfe39c068945e7ca5, 0x30b30c70886c1197, 0x4793c49e9daaf332, 0xb49fb8a1bd2ffd6e, 0x1db7df5ae5c2d7de, 0x9f7734871655e5fe, 0x30968a40c221bac2, 0xfb460b95839e30d9, 0xcd20db726f1eb367]

private theorem words036 : absorb036 state036 = absorbed036 := by
  decide +kernel

private def quarter036_1 : Vector UInt64 25 :=
  #v[0xc6a92a3e437c6f2d, 0x3fbeb82de19b608, 0x895c328467fb0f1e, 0xd7be2f07d4b98a10, 0x5e5201644bcde79c, 0x594e5c389e5979b0, 0xbca25d9123edf8bd, 0x8aa379884100839d, 0x6f44915164848d2c, 0x1598a97bece99fb7, 0x128343e8191170f6, 0xf98a5376da52c2e9, 0xaf2c9f1faf6468c6, 0xd5d01d1212a48599, 0x4ce7abf77e56465c, 0xaa77827e860579f3, 0x95851ff0db5fe1bc, 0xe62e4c161b06ca58, 0xa16a45bea6a64e36, 0x50c13eceee1eccae, 0xbb7071dce5816b8e, 0xd38c4b817feceef0, 0xa8582cd37817786f, 0xb7ef5b6180b04c76, 0x75c90551a4654417]

private theorem rounds036_0 : sixRounds 0 (by decide) absorbed036 = quarter036_1 := by
  decide +kernel

private def quarter036_2 : Vector UInt64 25 :=
  #v[0x1cbb6b61906d7e99, 0xd5f6b4b86faf83b1, 0x23d6115e69edae93, 0x328e2bedf2cf0a46, 0x98267255931227bf, 0x795c9819ae9089, 0xa76390071bebb1bd, 0x954480f426d9d548, 0xdcf9c91a7fe3b8b3, 0xa26c02c1c7f94e47, 0xe72c01085c30a62d, 0x18b4c737c04b22a, 0x9bfdf0fa2a3067d5, 0x7290b17490ff92bc, 0xe76af59184f3d5f8, 0xd1f6d7e66e4c07ea, 0x16ce95294cbc83d6, 0x4f38f6189c32195a, 0xb49d829ab322078e, 0x31e5a20de72e9f88, 0x823fddf0fb787849, 0xb8f63180ca6a000e, 0x985d74c3723d616f, 0x99354f0f636936bb, 0xe775c8ceade8cc1d]

private theorem rounds036_1 : sixRounds 6 (by decide) quarter036_1 = quarter036_2 := by
  decide +kernel

private def quarter036_3 : Vector UInt64 25 :=
  #v[0x62feb3166e0ba640, 0xd411fb51b94bfffa, 0xe6136b36a52ce6dd, 0x476b65349081d5f7, 0x6331372e8e6b0cdb, 0x9293c7773836b7f7, 0xa17188dcb4dbb207, 0x93380ba20d5e400, 0xeadf16dd3c330b7b, 0x9a865dc80bc0e587, 0x8385a49372d49139, 0xab7e906e32f87fca, 0xe0090725fda30a7f, 0xda50e09269a75bc9, 0xa08b404e1cabce9f, 0xfbf3e3fb2ad84ed2, 0x926381fbc1314bf, 0xd2c1fcdcf0bef8d, 0x983d742ba9ccfaaf, 0x51fb9ec3c5c539a, 0x902eed253e1996fe, 0x5db25a039276969c, 0x9a035cb5747617de, 0x45ff9ddd7c2ebd79, 0xb869e2bdc616d7b9]

private theorem rounds036_2 : sixRounds 12 (by decide) quarter036_2 = quarter036_3 := by
  decide +kernel

private theorem rounds036_3 : sixRounds 18 (by decide) quarter036_3 = state037 := by
  decide +kernel

private theorem perm036 : KECCAK.f1600 absorbed036 = state037 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds036_0, rounds036_1, rounds036_2, rounds036_3]
  rfl

theorem block036 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes036 ++ tail) state036 =
      KECCAK.Bytes.run 0 tail state037 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes036 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb036 ws)) := by
    rfl
  exact (step state036).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words036).trans perm036))

private def absorb037 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x80 0x80 0x1 0x4 0x60)) 3 (by decide) (UInt64.ofBytes 0x81 0x25 0x60 0x52 0x82 0x3 0x81 0x82)) 4 (by decide) (UInt64.ofBytes 0xc5 0x59 0x61 0x80 0x1 0x20 0x60 0x52)) 5 (by decide) (UInt64.ofBytes 0x91 0x1 0x40 0x60 0x39 0x91 0x25 0x60)) 6 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0x85)) 11 (by decide) (UInt64.ofBytes 0x20 0x90 0x40 0x60 0x52 0x20 0x60 0x3)) 12 (by decide) (UInt64.ofBytes 0x61 0x15 0x16 0xff 0x60 0x90 0x85 0x54)) 13 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x40 0x60 0x57 0xe9 0x13)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed037 : Vector UInt64 25 :=
  #v[0x84829ee28a0938e5, 0x7323397e95ab90ba, 0xfcdabeb41d7ef2d0, 0x6001dc74a7728fca, 0x277395fd66c00a9b, 0x94dc8c961a20e60c, 0x21cd11b53b4e06ad, 0x92ecbba68949c1da, 0xf82d575cdffe9cd8, 0x12b23988353ff417, 0xc656351a7ff21d9b, 0x84ef323b13bfae1f, 0xe0ff93c1aaca65c5, 0xe0326bbc52fcf6d0, 0x790a680acb80c66d, 0xf336bdde92d37c81, 0xbdd0ede90e38f011, 0xb6a4970ec953078e, 0x8332fe8193b79c0c, 0xd9e10195ffe2f597, 0x5a8deaf2cce8d107, 0x73e99c35ab3746b4, 0xc8b650aeeec60e28, 0xf42e3197c72803aa, 0x5d6f58c23d8fc796]

private theorem words037 : absorb037 state037 = absorbed037 := by
  decide +kernel

private def quarter037_1 : Vector UInt64 25 :=
  #v[0xebf6cf2677737db1, 0xcbc8e1a4a38b7da1, 0xf9e3ff715f1ca075, 0xaae724e96fe3aff2, 0x2cc9d49a8b368b7, 0x39ab1f6df6c4f947, 0xfcc83e4fa6340e7d, 0x8471259d777fcb70, 0xd16d95c8a88ee8d4, 0xcc42dc06c6776411, 0xa1be83b0ba9883a7, 0x1facb17673e05a2b, 0xf066cdf1d5c4422f, 0xdc8f52f494df3981, 0x8d6de09a3a9ba45d, 0xc0ffb7266a970c30, 0xf551e3f7c64c8060, 0x4e403ca54b83db3d, 0xa368aa328fc7d2a2, 0xf0399d81693d2152, 0x89c0f26f1685466, 0x67033afa21942c29, 0xb0c16b6fa495b9ef, 0xb78226e3af1fb10c, 0x77d55d5cb2d206bd]

private theorem rounds037_0 : sixRounds 0 (by decide) absorbed037 = quarter037_1 := by
  decide +kernel

private def quarter037_2 : Vector UInt64 25 :=
  #v[0xd76e1564eaee8508, 0x2b8da9a4e76ad821, 0x48c40e3c9de19e60, 0x9ed8d970cf72c801, 0x920f5c0ebcbb2251, 0x95d2e955c5136822, 0x21ba042d3fac572, 0x8527a875299f9136, 0xe93578750148c3dd, 0xdbcf24c7f88dad84, 0xfa8e57c96e0b698c, 0xc723c026c68a8482, 0xc85ec25a4f155d, 0x5535d2467dfb51c1, 0x202ca5a3167f3d76, 0x1dc77acdbb866402, 0x4f222861779a3064, 0x3cfbc0736c50fcd5, 0x5f8423a10b94e1ae, 0x3feee76822dd4bbf, 0x779aa1d8590874d3, 0x75967ff3a14abdb0, 0x24ba77c7a1d19077, 0xaa6b501c8d8dc5af, 0xe02cfc827ca6fbca]

private theorem rounds037_1 : sixRounds 6 (by decide) quarter037_1 = quarter037_2 := by
  decide +kernel

private def quarter037_3 : Vector UInt64 25 :=
  #v[0xd4c538555afa7f66, 0x2468e0d196416b4, 0xa419768c394d1db7, 0x3bea1a172d502be0, 0xe1c0a06097eadfd8, 0x6614955a841eb526, 0x1c26802649d8321e, 0xe7caef776c17d9fc, 0xf4f12a240dd94cf9, 0xc57c6bb03788f60, 0xd01d89aa26878dfe, 0x4be1844e6d3a4ef9, 0x1d2177e2accd1741, 0xd9df3f9566c8d7e5, 0xe1b7bc8b131052c4, 0x284ea695e4edd8bf, 0x95fc1bef80c70bb4, 0xcf9caa52acf8b2c5, 0x3f738d877e676536, 0xa611f1f53051a013, 0x9f2eea93fa6b9c28, 0x810752876fb06723, 0x57ca0dd0b57da098, 0x7ff4a40efea4e4ba, 0xc9c81c6fa219f881]

private theorem rounds037_2 : sixRounds 12 (by decide) quarter037_2 = quarter037_3 := by
  decide +kernel

private theorem rounds037_3 : sixRounds 18 (by decide) quarter037_3 = state038 := by
  decide +kernel

private theorem perm037 : KECCAK.f1600 absorbed037 = state038 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds037_0, rounds037_1, rounds037_2, rounds037_3]
  rfl

theorem block037 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes037 ++ tail) state037 =
      KECCAK.Bytes.run 0 tail state038 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes037 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb037 ws)) := by
    rfl
  exact (step state037).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words037).trans perm037))

private def absorb038 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x20 0x60 0x80 0x80 0x1 0x4 0x60 0x52)) 2 (by decide) (UInt64.ofBytes 0x25 0x60 0x52 0x82 0x3 0x81 0x82 0x1)) 3 (by decide) (UInt64.ofBytes 0x59 0x61 0x80 0x1 0x20 0x60 0x52 0x81)) 4 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x39 0x91 0x25 0x60 0xc5)) 5 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x0 0x60 0x16 0x87 0xff)) 10 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x20 0x60 0xa 0x60)) 11 (by decide) (UInt64.ofBytes 0x90 0x52 0x84 0x33 0x20 0x83 0x80 0x40)) 12 (by decide) (UInt64.ofBytes 0x15 0x11 0x85 0x54 0x20 0x90 0x52 0x91)) 13 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0x72 0x14 0x61)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed038 : Vector UInt64 25 :=
  #v[0xd39846ca17b2a69e, 0xd64b3d6672e1a83c, 0xf2e88192f559085e, 0xbbd3d81a030fe52a, 0xce6685c9a56de956, 0x2edd145c0685f61b, 0xb660e5248acf0127, 0xc6cc829285a28547, 0xcd53445c02f84f34, 0x1c9641565dbc2a41, 0xaf6bff256b8e909b, 0x5f6965435bcf8fe1, 0x3684cd97f9cfb202, 0x4ba001cc964f3c1c, 0x88e1a040aa2f67fe, 0xb4f8b19750ae4d9a, 0xcf66da5936b2e169, 0x2b2cef5d7b7a9e54, 0xb864de80464e92e9, 0x17a5e6e88cc87f9c, 0xb6ca0a013a82cccd, 0x745a5cbe4bf95792, 0x604fbb844612c7da, 0x3804091aa4039a27, 0x39e4814742f2aef3]

private theorem words038 : absorb038 state038 = absorbed038 := by
  decide +kernel

private def quarter038_1 : Vector UInt64 25 :=
  #v[0x1b74b6fd66a7461c, 0x7ca5cb386a2f608e, 0x57cd98303e1fd5d7, 0xd1c8121c378fa27b, 0xcaf9740229161073, 0x372c7faf05eaa140, 0x2b8dc9cf453c70d4, 0x6479056ebf9d54d5, 0xa9c7a496245ee6ce, 0x3e80c1227588e19e, 0x3901852385241fba, 0x5cffafe5367cdf01, 0xe9b274d2079e4471, 0x3f6be9b23077349c, 0x79cbe82743b25a4e, 0xc41c626787133108, 0xcb8d329f9b50164, 0x76b8835912b2ff78, 0x6ab53b32d6fb505, 0xaa79a0981d53646c, 0x263ffa2cca3880e, 0xc2d40ed1c8f37455, 0xbe5d4ab0e4a76d92, 0xc95c599fc6d013ab, 0x2eaf151849d92c7e]

private theorem rounds038_0 : sixRounds 0 (by decide) absorbed038 = quarter038_1 := by
  decide +kernel

private def quarter038_2 : Vector UInt64 25 :=
  #v[0x42bd45dfd3fbeafc, 0x419e9e66b8352166, 0x314a0dc066b006c6, 0x55df2574bdbd0e4b, 0x94a874240a28f6c3, 0x52b86c4669917852, 0x8eb3787070fd13e0, 0xbef0a54cb61e4460, 0x78c5212cd5a28263, 0x8b637eb6b88a4f08, 0x78f4e4532261acb9, 0x193e9ff919b8c046, 0x47359101f5681448, 0xc94bd530f5c83a2c, 0xc488dc49cc0453ef, 0xd7f309c540f2e67a, 0x84239e33ff98ef18, 0x2ec1ca67b37e3cb2, 0x8564e45fd4608e77, 0x3917f9fcbc5e0662, 0xb4fb9a74445c9123, 0x68960c5c114d4519, 0xf620b3caece68891, 0x4d8caae5fdfbba, 0x70cfe1f86bbb79fa]

private theorem rounds038_1 : sixRounds 6 (by decide) quarter038_1 = quarter038_2 := by
  decide +kernel

private def quarter038_3 : Vector UInt64 25 :=
  #v[0x9a2f902ce543beaf, 0x1908a76645b70710, 0x857e68214bf99a39, 0x3243fa3656fc5eb1, 0xcf610710f5bcdbbb, 0x23d097b681e247b7, 0x7f22c61bfbc53470, 0x8a8d8834f8ba8690, 0xe01931cee8ca9c5e, 0xe5adcdfbbcb05a59, 0xe31969fb7429db4e, 0x274aaf72cd095955, 0xde369de6e63e5b40, 0x2bb9acf8e756697c, 0xa031a1664baf327e, 0x871c6a822bfade32, 0x9e40b17b94de1a14, 0x5cabfbc5a4c4f699, 0x4f9808262fbd0962, 0x70137aa20f325757, 0x6e730a1bd3a7da3, 0x3e1c9ba246fdfef3, 0x4a03382f8ec96a07, 0xb629696550fa8c49, 0xaa020177634221b6]

private theorem rounds038_2 : sixRounds 12 (by decide) quarter038_2 = quarter038_3 := by
  decide +kernel

private theorem rounds038_3 : sixRounds 18 (by decide) quarter038_3 = state039 := by
  decide +kernel

private theorem perm038 : KECCAK.f1600 absorbed038 = state039 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds038_0, rounds038_1, rounds038_2, rounds038_3]
  rfl

theorem block038 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes038 ++ tail) state038 =
      KECCAK.Bytes.run 0 tail state039 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes038 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb038 ws)) := by
    rfl
  exact (step state038).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words038).trans perm038))

private def absorb039 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 3 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x28)) 4 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x28 0x60 0xa8 0x57)) 5 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 6 (by decide) (UInt64.ofBytes 0x7d 0x14 0x61 0x5b 0xfd 0x90 0x3 0x91)) 7 (by decide) (UInt64.ofBytes 0x5b 0x56 0xf8 0x3e 0x61 0x87 0x87 0x87)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x60 0x16 0x87 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x20 0x60 0xa 0x60 0x52 0x81 0x90 0x0)) 12 (by decide) (UInt64.ofBytes 0x20 0x83 0x80 0x40 0x60 0x52 0x81 0x90)) 13 (by decide) (UInt64.ofBytes 0x20 0x90 0x52 0x91 0x90 0x52 0x84 0x33)) 14 (by decide) (UInt64.ofBytes 0x41 0x61 0x86 0x90 0xb8 0x14 0x61 0x54)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0x56 0x23)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed039 : Vector UInt64 25 :=
  #v[0xd10889b801c267b3, 0x2e96d71be92250b6, 0x5b21a8e5d0ed3deb, 0xf4b4d7a0c9444314, 0xc7c97af489e0f750, 0x95e46cfa0b26b552, 0x1e795725d8fcecb4, 0x1fa86b89935f64a8, 0xbb30a9c49c6314e5, 0xa0c66148b97b9e6c, 0xd4585a9ad31a8953, 0x16ced8c6f20d9620, 0xa944a48ac6a21a68, 0xce0e17e5fb5818c4, 0xd38b923fe46139f4, 0x170a9956a4d3ebd2, 0x23bfa35a3aa550fa, 0xa30678ea7c660ec3, 0x801c954e189ca32d, 0x7425973e847575d3, 0x95dd15e58cfafc50, 0x8f5869a0b91d87a2, 0x4411ebd0652901a9, 0x1277c0c5416bc946, 0xd90e5569082500a4]

private theorem words039 : absorb039 state039 = absorbed039 := by
  decide +kernel

private def quarter039_1 : Vector UInt64 25 :=
  #v[0x588e0709511b4d0a, 0x6bf2b3e7d6563511, 0x6538544591f83224, 0xd0c4f95e964dab50, 0x8c2451616113735c, 0x6c7f0895c2a043ff, 0xf54c78f95685aa17, 0xe8a1e75ee832cc65, 0xb4c4dd2f28f91f7c, 0x8a37897e43bcd24a, 0x315c6d16c901bf3d, 0xc45a0dda5f7e4a87, 0x2fba42bf0299c8bc, 0xe8e7d3a425f4f2ed, 0xd2be0cd664ee61dd, 0x54dcf630e3f2cd0b, 0xa98276802012b049, 0xd6fdb370fad81911, 0x23040af9bf6851e8, 0xd6118d026c61b135, 0x162b02e6a20f94f7, 0x39a460aa359ef25e, 0xdbc374f2d5b7b7b1, 0x72ba2beea800c869, 0xe65481fdeb54203c]

private theorem rounds039_0 : sixRounds 0 (by decide) absorbed039 = quarter039_1 := by
  decide +kernel

private def quarter039_2 : Vector UInt64 25 :=
  #v[0x30ef2cfc875d1b97, 0xa2ceee02abfb195e, 0x23c0549ede2fa366, 0x67175524c0d75d5c, 0x264acd49f502fc5b, 0xe2d66fcd0bf3dc4, 0x6c5a11bb7186238e, 0x97a6cca3b35c2af5, 0x49fee1937418b3bd, 0xbb3a9f6858b20028, 0xc21f2c45313ad999, 0xcf157c07f475101a, 0xf131b1f7f8d9a7b6, 0x4b43eaff72df3b55, 0xe81dd9e6177ecf07, 0x9f6fe32845a7d1fa, 0x9068a8c7738cc749, 0xff49c91a0a23ddc6, 0xfa651348486cece6, 0x7618467838a3f481, 0x34510312c9f6b511, 0xfbbdf0f3f700129b, 0x6b6d86f56135f5ee, 0x6ea1134582c36ec5, 0x63b9fb3012c9dbd]

private theorem rounds039_1 : sixRounds 6 (by decide) quarter039_1 = quarter039_2 := by
  decide +kernel

private def quarter039_3 : Vector UInt64 25 :=
  #v[0xc18c69e99df9cd01, 0x498b336a2a879e7b, 0xecabc5dd59ce5f50, 0x48790da57240c169, 0x7c2c6339592fe3a5, 0x63c87bde59f3eb27, 0x6220c414e6c138f6, 0x696d808abc198385, 0xd7e85c282159a75e, 0x365104cb78c998c4, 0x2889af41fd95414c, 0x29014f23ea16a9b2, 0xbd447e30c89073d3, 0x39f2dcf8c13352d1, 0xe33a77df5af50650, 0xd9dcada459a81cc1, 0x9aa972b62dbd9487, 0xb1ff252cd4a6b68f, 0xe713b947b1c3a162, 0x3bb0783dd6f7e489, 0x4107e27a4077d264, 0xf2968e81d8404240, 0x90c1229d4d22abab, 0x30eb4cd99f10a772, 0xfa79a3c6ae4b38ee]

private theorem rounds039_2 : sixRounds 12 (by decide) quarter039_2 = quarter039_3 := by
  decide +kernel

private theorem rounds039_3 : sixRounds 18 (by decide) quarter039_3 = state040 := by
  decide +kernel

private theorem perm039 : KECCAK.f1600 absorbed039 = state040 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds039_0, rounds039_1, rounds039_2, rounds039_3]
  rfl

theorem block039 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes039 ++ tail) state039 =
      KECCAK.Bytes.run 0 tail state040 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes039 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb039 ws)) := by
    rfl
  exact (step state039).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words039).trans perm039))

private def absorb040 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x0 0x60 0x16 0x88)) 2 (by decide) (UInt64.ofBytes 0x40 0x60 0x52 0x81 0x90 0x20 0x60 0xa)) 3 (by decide) (UInt64.ofBytes 0x91 0x90 0x52 0x84 0x33 0x20 0x83 0x80)) 4 (by decide) (UInt64.ofBytes 0x50 0x93 0x1 0x60 0x55 0x20 0x90 0x52)) 5 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x92 0x93 0x50 0x50 0x50)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x54 0x0 0x60 0x5b 0x56)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x7d 0x15 0x61 0x14 0x33 0x16 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x80 0x40 0x60 0x57)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x90 0x81 0x1 0x82 0x4 0x60 0x20 0x60)) 16 (by decide) (UInt64.ofBytes 0x4f 0x7f 0x52 0x1 0x82 0x24 0x60 0x52))

private def absorbed040 : Vector UInt64 25 :=
  #v[0xdf0f18cddcc6bd3b, 0xad51abb610e7ff86, 0x444543999dbe957e, 0x696432fa29640d26, 0x9e0b336a5c92fe0e, 0xc3a03e3a0642be5e, 0x5eca8ca0f55779ca, 0x7d841f94c329131, 0x65a49ee2110f4749, 0xda24b8e6091165c9, 0xb8f3bf6e98ef4a77, 0xdd35a20c87c8a590, 0xae9abbe0c83565ba, 0x70652fddd8c1ce5b, 0xe627421b45111dbe, 0xb7107f75deae6b71, 0xe1905287fee45ea4, 0xf819cc0ee09735a9, 0x6137d9e91f9d536f, 0xf1a4cb6f49a99762, 0x7d2db9b18f9edd8d, 0xaa0b58451e742235, 0xf77bb8b5c2b63262, 0x830500416ae1c681, 0x129aa1de03e471d1]

private theorem words040 : absorb040 state040 = absorbed040 := by
  decide +kernel

private def quarter040_1 : Vector UInt64 25 :=
  #v[0xdf092ad6945af6d0, 0x8e73421a26fea796, 0x2553bcd9cdb9c3bc, 0x3f0cbcda98384224, 0x28bee4148bb77954, 0xc199a795a86ae66a, 0x3c1a767a72026a4d, 0x8103533609b535e2, 0xb8ff7158a43b0ef7, 0x4d0390fc0362f306, 0xe507c5b6b03bbf6f, 0xf7a51e96fe959b76, 0xbcc52928c409bca3, 0xe41ef73e3029a4fa, 0x9074e17a84a2adec, 0x6ef96fd17eec8a7a, 0xe233c4e85fd0ffd4, 0x1689b6b3b25136e4, 0x5d7ec09d1981e63, 0xe40378692c6fa47e, 0xc9f067ceebc210bc, 0xb27a231227621447, 0x8c01e8a4fe006f6e, 0x69766634cd3794d6, 0x17098ca33f1a2733]

private theorem rounds040_0 : sixRounds 0 (by decide) absorbed040 = quarter040_1 := by
  decide +kernel

private def quarter040_2 : Vector UInt64 25 :=
  #v[0xf925deb3dc045dd4, 0xfee12957f47d3127, 0x66c60c08ffe8e44c, 0xeba08cb79d033386, 0x946f943c2b77d8cc, 0x441482ee7d1f8e1, 0x6a6c9c80975f469, 0x40766aa95788863d, 0x749f18a056ec1247, 0x1f8e760dfa29ae9c, 0x5c3b2af308ef9e7e, 0x8489b4da80f14ee1, 0xa9f154f7400a66ef, 0xacefefe562bbef47, 0xd74623204337de36, 0x1f4cefb1aa3156ea, 0xca8c35a72c068813, 0x1cc95a057fea0f15, 0x6e73fb7b58666192, 0xfa63d61913d41801, 0x4318d57edd05434c, 0xdddbfe8c6dbb70ad, 0x21af777a695cf398, 0xcc5b5834e4ce5067, 0xfc7e3765271cb437]

private theorem rounds040_1 : sixRounds 6 (by decide) quarter040_1 = quarter040_2 := by
  decide +kernel

private def quarter040_3 : Vector UInt64 25 :=
  #v[0x9b76d518acdf9659, 0xe7be5fc8ed32e303, 0xa4dfcbeedeb4ee3, 0xf533b1265aa92009, 0x7cbb4bc9586fb73a, 0x830effa2d07b6138, 0x204552a2a601cad1, 0x61e3153920a940fe, 0x63d2fbf2ecae9288, 0xcb4c6e9037528a8f, 0xc5c61e2e6dc2938e, 0xb93e4bdf32530c08, 0x1c58ec26ee46a771, 0x2222433839d655b4, 0xcd0e2d32e7b8853a, 0x4e1d97f2952e6a3e, 0xd23158b805f0a627, 0x839a2fbad0f715e, 0xac49f61f38e1de4a, 0xd5f834c0bafa540b, 0x49641babf4d92ca3, 0x90a0d4390f5ef754, 0xb6ec6c0a2fd88173, 0x78ddc762f6898396, 0xf86d448829b4dbd0]

private theorem rounds040_2 : sixRounds 12 (by decide) quarter040_2 = quarter040_3 := by
  decide +kernel

private theorem rounds040_3 : sixRounds 18 (by decide) quarter040_3 = state041 := by
  decide +kernel

private theorem perm040 : KECCAK.f1600 absorbed040 = state041 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds040_0, rounds040_1, rounds040_2, rounds040_3]
  rfl

theorem block040 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes040 ++ tail) state040 =
      KECCAK.Bytes.run 0 tail state041 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes040 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb040 ws)) := by
    rfl
  exact (step state040).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words040).trans perm040))

private def absorb041 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x20 0x3a 0x65 0x6c 0x62 0x61 0x6e 0x77)) 1 (by decide) (UInt64.ofBytes 0x69 0x20 0x72 0x65 0x6c 0x6c 0x61 0x63)) 2 (by decide) (UInt64.ofBytes 0x68 0x74 0x20 0x74 0x6f 0x6e 0x20 0x73)) 3 (by decide) (UInt64.ofBytes 0x60 0x72 0x65 0x6e 0x77 0x6f 0x20 0x65)) 4 (by decide) (UInt64.ofBytes 0x81 0x90 0x51 0x90 0x52 0x1 0x82 0x44)) 5 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x1 0x64 0x60 0x3 0x90)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x61 0x16 0x81 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x40 0x60 0x57 0xe9 0x15)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x20 0x60 0x80 0x80 0x1 0x4 0x60 0x52)) 15 (by decide) (UInt64.ofBytes 0x2a 0x60 0x52 0x82 0x3 0x81 0x82 0x1)) 16 (by decide) (UInt64.ofBytes 0x56 0x61 0x80 0x1 0x20 0x60 0x52 0x81))

private def absorbed041 : Vector UInt64 25 :=
  #v[0xea884cf51ed67103, 0x773d938f092bdd16, 0xd555e471ceea0086, 0xbe9cf40d4e35820c, 0xc765a12e413a1382, 0x7256e77bba9f83d4, 0x43d8e753e7848944, 0xdf0f5a66474ff521, 0x9cb5329b691256c6, 0x1f794a0605cfaa27, 0xfb3ccaef975a3b24, 0xb4fd7e92baef3094, 0xe404f6e68d0322a9, 0xba51ebcea2ae5ad3, 0xac77afe51bf41491, 0x90bc3f7af2340b0b, 0x4bc2901316ff0744, 0xfa896957f9b500e, 0xed39d9a1a4692cfd, 0x81013a1ad5093dc4, 0x251f5c4f59aff747, 0x9f613e2291ea6f62, 0x310a4a27d6090999, 0xf976ece533c97dc5, 0x94fcbc3ff0bf0f6]

private theorem words041 : absorb041 state041 = absorbed041 := by
  decide +kernel

private def quarter041_1 : Vector UInt64 25 :=
  #v[0x10bc832d38d3bf54, 0xb09840acbd3d7e86, 0xd4a3734dfdfa1cdf, 0x5ea82c482da711f7, 0x3855f856586913e9, 0x60405b723a94179a, 0x152376f8863dd7d2, 0xb02135648e8e04a4, 0xfcc31f697541825f, 0x454d7986ab4733ab, 0x7513c446f345d7ca, 0x2fc4d166c6aa999d, 0x210a44c261ce6731, 0xbf780e59ee7f1633, 0xf721c83fa75e7718, 0xaba61ad066770c03, 0xf990fb6fa0d47101, 0x876513de235460d2, 0x5b37d424dcc6be2c, 0xf41fea196374f5a, 0x17f0afa6fa143ae, 0x323257681c8be49f, 0xde0d512caf410147, 0xc5f753a8d85b3989, 0xe611afd1404d8496]

private theorem rounds041_0 : sixRounds 0 (by decide) absorbed041 = quarter041_1 := by
  decide +kernel

private def quarter041_2 : Vector UInt64 25 :=
  #v[0x7978c8c1f9578167, 0xf4223cdab76bda06, 0x9fd5c0b0ff330102, 0x3f2b726b3bed4c67, 0x85f5cae84d1cad16, 0xae55ae88a0c09e71, 0x3b68e3db7f4c090a, 0x54fcb61b291ae1bf, 0xeecdf5f715519ede, 0x860d5021cb013f4f, 0xd6a21cc2ed28ac91, 0xa6085d3d96424349, 0xdb53020e3d7ceb09, 0x146c693ac3dd1bf7, 0xd2e202b00733deaa, 0x8da86594ad1bdde5, 0x4a01b5401f23372d, 0x8ad4507b15ecf253, 0xe53063ac55e97c1d, 0x1f68948c89bb1ac8, 0xac831292afc0f9a8, 0xbcbb30bb70d0a687, 0x1bf2c6d1f12a2159, 0xae4c58de571c5ab9, 0xf15c1039af467ba8]

private theorem rounds041_1 : sixRounds 6 (by decide) quarter041_1 = quarter041_2 := by
  decide +kernel

private def quarter041_3 : Vector UInt64 25 :=
  #v[0x852f81f927fe13f4, 0x7f23196e9ce302ab, 0x2d1caf44a7cce9ae, 0xf794bd4082ba79dc, 0x45910a9a6e721140, 0x83374d3daa56a24a, 0x80e9d4b4683da347, 0xd06f2d7db8094d18, 0x714e5f9f4790cc1e, 0xfd496f1b71f01f65, 0x573ecf5f70af7bd5, 0xb87b80b1f773db98, 0x1423f89c57ecc21c, 0x7d321670bcb9fffd, 0x5218d8e3bc791119, 0x47d9bfc7e581f16e, 0x98d13a8f43d7b067, 0xd2adecd31676b96a, 0x573d9a33f23eb479, 0x697e8631547e3f70, 0xcf0783f22307345c, 0x99fe37b6ebf527ee, 0x4038ef364783716e, 0x7268a3eaa09f8dc0, 0xbf836e8d226b34b2]

private theorem rounds041_2 : sixRounds 12 (by decide) quarter041_2 = quarter041_3 := by
  decide +kernel

private theorem rounds041_3 : sixRounds 18 (by decide) quarter041_3 = state042 := by
  decide +kernel

private theorem perm041 : KECCAK.f1600 absorbed041 = state042 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds041_0, rounds041_1, rounds041_2, rounds041_3]
  rfl

theorem block041 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes041 ++ tail) state041 =
      KECCAK.Bytes.run 0 tail state042 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes041 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb041 ws)) := by
    rfl
  exact (step state041).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words041).trans perm041))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
