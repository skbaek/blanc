import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb36 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x16 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x0 0x60 0x1 0x20 0x60 0x52 0x81 0x90)) 4 (by decide) (UInt64.ofBytes 0x61 0x15 0x15 0x15 0x11 0x85 0x54 0x20)) 5 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0xaa 0x12)) 6 (by decide) (UInt64.ofBytes 0x0 0x60 0x9 0x60 0x85 0xfc 0x12 0x61)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x8a)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x90 0x1 0x20)) 14 (by decide) (UInt64.ofBytes 0x90 0x12 0x2e 0x61 0x54 0x20 0x0 0x60)) 15 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0x63 0x90 0x91)) 16 (by decide) (UInt64.ofBytes 0x73 0x89 0x0 0x60 0x9 0x60 0x5b 0x56))

private def absorbed36 : Vector UInt64 25 :=
  #v[0x73c0eb432cb68be, 0xe2e2857a0d1029af, 0xb31836bdd883245a, 0x995cbf3493c3d5b6, 0x26017a415313b391, 0xc71cec6d78eb8435, 0x26c9a60ae58ad1bf, 0x2893e8b8a6163a03, 0x7d78c360441356b4, 0x80d19556ab8ad4ba, 0xd5b4dd62b8857cdd, 0x88b88750fae7d88d, 0x70282bb56c5d4e44, 0x9e083764250a3e95, 0x69d5a15aa167437a, 0xfbe07efaccd080d4, 0x563cb5ad52aef826, 0x4c64eecdc8ad9c1d, 0xe08665a3f0d0a6d0, 0xfc0fd265f5e44150, 0xa9e72b49dfb51e85, 0xb0657e7da3a54280, 0x6b4dfc40b41bb398, 0x65600a4700b71716, 0x8261db3ce50331f6]

private theorem words36 : absorb36 state36 = absorbed36 := by
  decide +kernel

private def quarter36_1 : Vector UInt64 25 :=
  #v[0xf89fa2055a2528eb, 0xc3496bd9638f579d, 0x16455e1be59424bc, 0x5185c584494f3b6, 0xbb82a79af5ce6539, 0x149e245131aadd15, 0x1631ad247277db7a, 0x9fad4c1b5f88997f, 0x52d21bd7aba9076c, 0xb374f95c0102cb03, 0x91f0d8f5b26c556a, 0x527479e14553a15e, 0xd628c41f0273985, 0x3feba2d8cd61f83b, 0x4841e4f2b37457db, 0x354793ed9d96be, 0xe41ab70b0cd93a6f, 0x8e3043330a63808d, 0x999d3f95cd90d554, 0xd0b6dbfc5f4a9f77, 0x13a9827fc5069209, 0xacec9e0a734a0747, 0x3b5d905c75776d68, 0x6dbeb90802484a27, 0x834c923e823647cf]

private theorem rounds36_0 : sixRounds 0 (by decide) absorbed36 = quarter36_1 := by
  decide +kernel

private def quarter36_2 : Vector UInt64 25 :=
  #v[0x1a2ea95c37f05ca8, 0x1a90f7a73138d70a, 0xbc9a75ab96cad0f6, 0x143e3420b7666390, 0x4ac6b3497bc35959, 0x2d373e148d99bf40, 0xb705b3559593ae0c, 0x8edd862048b2b4e5, 0xab4bf73c5bd6067f, 0x53e9d163a45dbfbd, 0xd0764076e93e84e2, 0xcb7e36f0f7a982c6, 0x9e9e2c246611a81e, 0x3e1ab83e43d86d6e, 0x2a139f558438a7d0, 0x7c7d92ba1809a6bc, 0x573bfd3fae3ce022, 0xebe073b673fd7e62, 0xe7b04f89019cd37c, 0x41f49c785079abae, 0xcab309d342c88e74, 0xc1991a4c88aad8bc, 0x14353f3379b4cfb4, 0xbccf0a2997137902, 0xf9b0c7c08083640a]

private theorem rounds36_1 : sixRounds 6 (by decide) quarter36_1 = quarter36_2 := by
  decide +kernel

private def quarter36_3 : Vector UInt64 25 :=
  #v[0x7574e2b5a6115f87, 0x6d97dd9aff5a8d17, 0x9efbf5d940d14103, 0x169c9e1756c5baf4, 0xe70e0c13203289e1, 0x10aa7d67ddaf1240, 0x4f8002536e81bc77, 0xfe24b828d9ab4751, 0x3690487a64830664, 0xb6690d1e5406fe1f, 0x77f3ecaa7373965c, 0x971b317099456621, 0x97c0b4602ceeb20d, 0x2bb7635b5c9f397c, 0x29071e63823514c7, 0x40a907434f312412, 0x7b59862927537bb3, 0x2014355c23b1a960, 0xa628c4c62e325da5, 0xcc7c55f4fb5b158b, 0x5f9ecd0188c82bf7, 0x605de6b04b76a09e, 0xc9390322d2c22f3d, 0x2d4c5d9ef3187e7b, 0xe01010e682db605b]

private theorem rounds36_2 : sixRounds 12 (by decide) quarter36_2 = quarter36_3 := by
  decide +kernel

private theorem rounds36_3 : sixRounds 18 (by decide) quarter36_3 = state37 := by
  decide +kernel

private theorem perm36 : KECCAK.f1600 absorbed36 = state37 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds36_0, rounds36_1, rounds36_2, rounds36_3]
  rfl

theorem block36 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes36 ++ tail) state36 =
      KECCAK.Bytes.run 0 tail state37 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes36 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb36 ws)) := by
    rfl
  exact (step state36).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words36).trans perm36))

private def absorb37 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x16 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x0 0x60 0x1 0x20 0x60 0x52 0x81 0x90)) 7 (by decide) (UInt64.ofBytes 0x91 0x13 0x61 0x50 0x55 0x90 0x81 0x20)) 8 (by decide) (UInt64.ofBytes 0xff 0x73 0x89 0x0 0x60 0x9 0x60 0x85)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x52 0x81 0x16 0xff)) 15 (by decide) (UInt64.ofBytes 0x20 0x0 0x60 0x1 0x20 0x60 0x52 0x81)) 16 (by decide) (UInt64.ofBytes 0x63 0x90 0x91 0x90 0x2b 0x2e 0x61 0x54))

private def absorbed37 : Vector UInt64 25 :=
  #v[0xd1629d675d86fe08, 0xffebe797f56a089, 0x109a8c13736fda13, 0x5fa698e9e1324bc3, 0x91c0a053b20681c8, 0xbe2dda666dfd8849, 0xb6b5aaaafa9b0672, 0xcd7833c1ce8cda58, 0xa7d1103dbd6ced7b, 0xf6b7e14f7e8b514a, 0x2e629a0c8a95f966, 0x194b9d91e8f946ae, 0xf07c7ffd189752e3, 0xdf81aaeceec4584e, 0xcdc107364fb3f27f, 0xc9fb12c9d8b8ea2c, 0x52df5e36482b9966, 0xb2454bb542863ff9, 0x7a5b7fe491987175, 0x9c3ea73fdfb03e20, 0x72982e536c49a812, 0x1eae0d81afe6d1b, 0x35f4d43883591d11, 0x5270263838331c42, 0x590ac5ed68d1aa72]

private theorem words37 : absorb37 state37 = absorbed37 := by
  decide +kernel

private def quarter37_1 : Vector UInt64 25 :=
  #v[0x70658cf3b0a3372e, 0x6a1a1ae0ab2b6166, 0xd0e5d81e5b789e16, 0xd99083c75aa7e670, 0xfd51af5046671036, 0xb62ed26291b9d2ca, 0x9ea9115e13bac970, 0xcce6e10488203c93, 0x81719c95461a01e2, 0x10cfd8df31e6bcb0, 0xad65d9acfd44ed40, 0xa12a58d340ed141c, 0x95130778a17220e8, 0x304c039a78cfbb7d, 0x5ddbdfe923b36b84, 0xbd56262d6fef1615, 0xe9e31e713bc7b664, 0x75cfd4b8bb36cd2b, 0x373c6722e1665448, 0x74348f73fe2c92dd, 0xc0e98d9c03b35978, 0xe2e137d0a35203f1, 0xc6f4bbea3a931d6a, 0x4641a44adb90efc8, 0xf86fcab27523db40]

private theorem rounds37_0 : sixRounds 0 (by decide) absorbed37 = quarter37_1 := by
  decide +kernel

private def quarter37_2 : Vector UInt64 25 :=
  #v[0x439450a88f54afae, 0x3bbd786cc78d3d6, 0x6fd43188880cf300, 0x9ab19bafda8073f3, 0x9e9d57022ad6365c, 0x1e8e1ea68178e55f, 0x1f62e69550324f23, 0x21b154ddf156c46d, 0xffc50ab43ac6058c, 0xa5ad66bddb019d69, 0xee598cdd4daf792, 0x40687a28fe37d77c, 0x55a501e46516a895, 0xa5ccda535d6f3a80, 0xec863d5a6d695427, 0x3719406c54a19bf6, 0xe24ee10f44e0c001, 0x340afca6e5f1b775, 0x731f8d62fddaf354, 0x40bdd71eb6c08cc, 0xc54b3616c7d71574, 0xe414a04094361ed9, 0x9663990f946e32e9, 0xaee7854587eb333c, 0x16daaf1ce8c5336e]

private theorem rounds37_1 : sixRounds 6 (by decide) quarter37_1 = quarter37_2 := by
  decide +kernel

private def quarter37_3 : Vector UInt64 25 :=
  #v[0x639e66df69b97b96, 0xb8ac35d8b43049c2, 0xadf01a1a53d2a48f, 0x5be5783f38011411, 0xc5fffca30fe624e3, 0xc7d86f06473c80b8, 0x7ef28968bd69441f, 0xe3ec770b730feb0f, 0x463efbf0c3113e23, 0x90a6ceb58cb956e5, 0xb2b4e123f9cf5c98, 0x389fece51cfc8d95, 0x3035dadd59b63a2f, 0x9f2849a78b792f1, 0x52dac400f70d5f6, 0x8f09cc64cb0d13e9, 0x9e447539fd1afbcd, 0x564095cd80b0bbdc, 0xa148e85c2a558a49, 0x6662ca8a2edf038a, 0xd1c3873b1a87ec63, 0xf68995c7ef99a88e, 0x684b8ea15ee29d56, 0x8e597639f86b4bd8, 0x35d56a4b93f453b1]

private theorem rounds37_2 : sixRounds 12 (by decide) quarter37_2 = quarter37_3 := by
  decide +kernel

private theorem rounds37_3 : sixRounds 18 (by decide) quarter37_3 = state38 := by
  decide +kernel

private theorem perm37 : KECCAK.f1600 absorbed37 = state38 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds37_0, rounds37_1, rounds37_2, rounds37_3]
  rfl

theorem block37 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes37 ++ tail) state37 =
      KECCAK.Bytes.run 0 tail state38 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes37 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb37 ws)) := by
    rfl
  exact (step state37).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words37).trans perm37))

private def absorb38 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x16 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x88 0x0 0x60 0x9)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x16 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x1 0x20 0x60 0x52 0x81)) 8 (by decide) (UInt64.ofBytes 0x90 0x81 0x20 0x0 0x60 0x1 0x20 0x60)) 9 (by decide) (UInt64.ofBytes 0xa 0x60 0x85 0x63 0x14 0x61 0x50 0x55)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x8a 0x0 0x60)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x16)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x81 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x1 0x20 0x60 0x52))

private def absorbed38 : Vector UInt64 25 :=
  #v[0xfcaab35db3b020a3, 0xaedf65eee146be59, 0xd85553ec186f33d1, 0x4896202de5282c87, 0x5d79f505d61c3210, 0x996aff0e825292b3, 0x9274129afdb2f1a3, 0xf77e3611d1b5c367, 0x282b601dbe0e8b3b, 0xd90ed331875cdf39, 0x70b343e7b951eb2c, 0x2b30320afd5fb3fb, 0xf40d26f2003deb1d, 0xd0d3991398542fb7, 0x7e0ffedd7422ec51, 0x1b9229bb4118adfd, 0xeb1924c9013f0fff, 0xe5cd8eacc503d4d6, 0xf2049df2a8224f65, 0x1652c336bc519667, 0x6f3d5dbcce81e754, 0x5f8f86dc278f30d6, 0x949373cac1c821bd, 0x4e373028500f5262, 0x53f4ba0ef4bdbb31]

private theorem words38 : absorb38 state38 = absorbed38 := by
  decide +kernel

private def quarter38_1 : Vector UInt64 25 :=
  #v[0x482a8bd0cb5ab370, 0xd0a5f74ab1f2c7a8, 0x4872d3a7248fc0f6, 0xdff7598b0d4e972c, 0x9d6fb5e70786b1df, 0xebbe903b28af286, 0x9eea27da27de4aa2, 0x72b6c26e0ae97539, 0x334cf5b4d5d2bd1c, 0x32f836e5a15996ad, 0x29df804c5f4c86a8, 0xa9bf93a7baefba7, 0x3aa038cca8f163e3, 0xca88bddce3b05358, 0x92b2aef5e7ae6042, 0x657bb018437e63b, 0x5625caf00333ad32, 0x9869b19cfc25541e, 0x1fca45ffa51763f5, 0x2432cc04ed22c8fe, 0xacd4ed8502f3604, 0xbbb9875ad8a47fad, 0x520c2d8936b155b6, 0xff3aea78ba2a3622, 0xfeb793a1be6933f5]

private theorem rounds38_0 : sixRounds 0 (by decide) absorbed38 = quarter38_1 := by
  decide +kernel

private def quarter38_2 : Vector UInt64 25 :=
  #v[0x50b8e3d8c6a2f8bf, 0x7fd6bdabb4fc907, 0x50053800b3010de4, 0x96db0555025e8f1d, 0x2240175a963e743b, 0xe7e6385a95ea91c1, 0xdb5673335a1ae8d2, 0x1d74dbc19544deca, 0xa4a077f818c8c287, 0x486ab951ab98e121, 0x60db7c3682604f48, 0x7c62096a7137e079, 0x80728488df7afb55, 0x8fb5171189cdec7e, 0x9bab2ae77c185518, 0x48d837eeaef2cc4, 0xfbdcb66fc9d4a65d, 0x94e19b21cc5eeb41, 0x6002785c21281ad5, 0xbfc98850696fe203, 0x5cdd1493827401f, 0x5448f8360229f2a9, 0xe445f0bddf3eda2, 0xf3a076cd8643c3d1, 0xf755f647667bfe8d]

private theorem rounds38_1 : sixRounds 6 (by decide) quarter38_1 = quarter38_2 := by
  decide +kernel

private def quarter38_3 : Vector UInt64 25 :=
  #v[0x704b604cd65c7dc0, 0x3c32fc3edfb425b4, 0xe1f0a45a4b51f54c, 0xb48331ddb96e3c88, 0x19e81de8aaadc0ac, 0x6b8c1ac762dfd22f, 0xb2ecb362186ddc62, 0x692549ddbfe9055d, 0x27926c7a7e8e493, 0xfca81d8907ac51d8, 0xb65f27261d3fdb6a, 0x938dda71a011f8bc, 0x919b2acc9cccd71b, 0xf551d3d7588e0f2a, 0xd972365f2c3dd7f7, 0x43aa9892de0205da, 0xadd6914265317462, 0x25a036ab85d3232e, 0xefc548eb6aa74729, 0x8bfbde98b73d288, 0x964d56b04f74fb54, 0xb724e5fa90dac304, 0xb8f44517ee5e8e6, 0xbc54efcde63ae92, 0x31fe9dfffd6847c3]

private theorem rounds38_2 : sixRounds 12 (by decide) quarter38_2 = quarter38_3 := by
  decide +kernel

private theorem rounds38_3 : sixRounds 18 (by decide) quarter38_3 = state39 := by
  decide +kernel

private theorem perm38 : KECCAK.f1600 absorbed38 = state39 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds38_0, rounds38_1, rounds38_2, rounds38_3]
  rfl

theorem block38 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes38 ++ tail) state38 =
      KECCAK.Bytes.run 0 tail state39 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes38 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb38 ws)) := by
    rfl
  exact (step state38).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words38).trans perm38))

private def absorb39 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x33 0x0 0x60 0x20 0x0 0x60 0x1 0x20)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x16 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x52 0x81 0x90 0x1)) 8 (by decide) (UInt64.ofBytes 0x91 0x90 0x12 0x2e 0x61 0x54 0x20 0x0)) 9 (by decide) (UInt64.ofBytes 0x56 0x16 0xff 0xff 0xff 0xff 0x63 0x90)) 10 (by decide) (UInt64.ofBytes 0xff 0x73 0x89 0x0 0x60 0xa 0x60 0x5b)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x52 0x81 0x16 0xff))

private def absorbed39 : Vector UInt64 25 :=
  #v[0xaa157b9319059180, 0xc6ecd02e4778b0bc, 0xf31d661f20aca519, 0x8d74e3f1a0197211, 0xa94b90241c454ad4, 0x78da5923fbc3c60, 0x694cda2d612fad43, 0xa5fa3a7483c3542b, 0x9c5bdd069b855123, 0xe8eb8a63958a5e57, 0x9bba153fc4ccb901, 0xd44db1847cc172ff, 0x222023cea5d60dc, 0x2927b5c5b24a2dc0, 0xe03d0d205eaf507c, 0xc5cd0468a1fe6360, 0xe5e9fb4a3a7e1758, 0x3b65b170df86eedb, 0x95dabdc3fc7c0d9c, 0x514ad46980fbcacc, 0x40395cda0aee385a, 0xe4fbbaf913bd0ce1, 0xf9a37883d7eae823, 0x6d952cd7451d56a6, 0xf3274a447c4b6dd2]

private theorem words39 : absorb39 state39 = absorbed39 := by
  decide +kernel

private def quarter39_1 : Vector UInt64 25 :=
  #v[0xaaf946bbd15122cd, 0x29d8504fe46a545, 0x1e04ca315d5a1f3, 0x6326f3f858a7fe0, 0x5d4be78d374a0661, 0x9327d2d44291be8a, 0x349cf88ce37c2ce6, 0x603c762376700ba8, 0x1514fe6128e9e2d9, 0x1ba1093dd90aac67, 0x3e9f873cec915670, 0x6df03e1b1724edf6, 0xc86e76c5e8278e77, 0xaa1e3b076cbf0b91, 0x277d56f0dcc125af, 0xdc9029640fec67f3, 0x94352e85500561c2, 0xe4b29b7378ec123d, 0x8147e848d0ab8d6f, 0x5a87f9bc870e65b8, 0xead44b15e1af24d1, 0x33309ee7090cf914, 0x45f9ce6d916ccfbf, 0x9b4bf86fbb92b75f, 0x761f8a85033e2c5c]

private theorem rounds39_0 : sixRounds 0 (by decide) absorbed39 = quarter39_1 := by
  decide +kernel

private def quarter39_2 : Vector UInt64 25 :=
  #v[0xf7aea503c43af0fa, 0xceb7b19769000c66, 0x41d8bdc633f83186, 0xf7a3428676b7cc4d, 0x10a8485c6ff2db9b, 0x8e85cbc3d26f6da4, 0x9df9f0dccce7fe9f, 0xc88778de440ca370, 0xbbefa7bd3da832d7, 0xf7f5a8adb31e066, 0xbd228a7b4fefe618, 0xa99a326fc9e73d90, 0x21357aa64e73d462, 0x522f7bb802953ea8, 0x29c3593f2fd5590b, 0x39b4f541afda670, 0x494cff28fae115d4, 0x2088ede10a2740aa, 0x17344466f7e07642, 0xa8c884713bde9f4c, 0xc69e2edd6f8880a4, 0x793d5c88d28c7fdc, 0x981b461b7223561e, 0x25f0bb6afba14524, 0x7f51eda8f8f740db]

private theorem rounds39_1 : sixRounds 6 (by decide) quarter39_1 = quarter39_2 := by
  decide +kernel

private def quarter39_3 : Vector UInt64 25 :=
  #v[0x140c922be439cc04, 0x1bceaa6287b5a32d, 0xa4cc19bf6eb9bfc1, 0xea5f04ed819479ba, 0x283d11464ffdf027, 0xdf666d12503ff08, 0x84dcfb3fadb89dcd, 0x2389f867b1090aee, 0x9761c78fba27144f, 0x150dc2b09359b46e, 0x9b20a6871a593fcd, 0xcb6271b04bf902c4, 0x9229e558fc79d929, 0xfe56cf1b25678886, 0x6ad0ac0778f935fc, 0x8ef0b50fdaa93583, 0x60a8325d731deb55, 0xee66202f6c43356d, 0x7dda300eb781c3b6, 0xdc712c9c2e083b94, 0xd39f84ec512535bf, 0x6e86a8f7463d46dd, 0xa0a0148f5bd8509f, 0x1a4ea6f410873c6a, 0x3801543e3520069c]

private theorem rounds39_2 : sixRounds 12 (by decide) quarter39_2 = quarter39_3 := by
  decide +kernel

private theorem rounds39_3 : sixRounds 18 (by decide) quarter39_3 = state40 := by
  decide +kernel

private theorem perm39 : KECCAK.f1600 absorbed39 = state40 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds39_0, rounds39_1, rounds39_2, rounds39_3]
  rfl

theorem block39 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes39 ++ tail) state39 =
      KECCAK.Bytes.run 0 tail state40 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes39 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb39 ws)) := by
    rfl
  exact (step state39).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words39).trans perm39))

private def absorb40 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x20 0x0 0x60 0x1 0x20 0x60 0x52 0x81)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x33 0x0 0x60)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x16)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x81 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x1 0x20 0x60 0x52)) 8 (by decide) (UInt64.ofBytes 0x55 0x90 0x81 0x20 0x0 0x60 0x1 0x20)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x85 0x50)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x87)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x7f 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x9b 0xc8 0xe2 0x1b 0xad 0x52 0xf2 0xdd)) 16 (by decide) (UInt64.ofBytes 0xaa 0x8d 0x37 0xfc 0x68 0xb0 0xc2 0x69))

private def absorbed40 : Vector UInt64 25 :=
  #v[0xf69db8e9a7b2ea9, 0x8a8985640bd0690c, 0xaa041278bb7df895, 0x48d30d8d6e4ad5a2, 0x77b3b789481983cc, 0x2a68a302af613c95, 0xb64ba0f5eeb8fa3d, 0xe5e1a5cfe9e7af47, 0x8f3cc6e7b363dea7, 0x258e8023c2fc5439, 0xe75168b6a37beb70, 0xe164d3e42a4ead68, 0x3679a3f463ee6e60, 0x609f6a6bb0d437e5, 0xbe3d72e0eeb56cc7, 0x89bcb894660a1f2e, 0x954d5ce22061d60f, 0xf49ef4b372047a85, 0x4eadf6918ab9c6c7, 0x1811704000fce331, 0xcc637193121203fc, 0xbbeb5bbeb6efb6f8, 0x6c255fe1cf457200, 0x49a3cd2e71fa094c, 0xee13c7e7f08c2cdb]

private theorem words40 : absorb40 state40 = absorbed40 := by
  decide +kernel

private def quarter40_1 : Vector UInt64 25 :=
  #v[0x326971c5210ebab4, 0x155907c3db301fba, 0x93b99dc74dc6d900, 0xd5870cf0182ba0db, 0x76a14872d633d3c, 0xc11972d8345af30c, 0x163a8c72ade60ece, 0xf2629634b900a95f, 0xc6ecb6c0e2fac1db, 0x3ec2951c60ae1cc5, 0x2b94d03124beab6b, 0x5153bf51916c3fae, 0xe86940f1f6e0f89a, 0x61a76b566ed2f924, 0xa958eea34508a6ff, 0x9ad96c6b86aa8da, 0x6063cd7a718a3516, 0x95eb0b2cb683a0be, 0x32fb8754052816d6, 0xb7c183eb4bf8f06a, 0xf644ea77b3be4887, 0xc6193b47927b77ef, 0x89f15d5062578664, 0xea32f25fac18d4f3, 0xbe113b1efad2939]

private theorem rounds40_0 : sixRounds 0 (by decide) absorbed40 = quarter40_1 := by
  decide +kernel

private def quarter40_2 : Vector UInt64 25 :=
  #v[0x5e1a815fcfda819c, 0x91ade8f9673d060d, 0x196c270ed59e1929, 0xc84a5d3439625c71, 0xcd1498ddcdea4d59, 0xe51d8a93bfcef465, 0x5acda81c40243549, 0xf6a89ebee98d1ebb, 0x8d1ac5a31425f259, 0xc8369fc450c14499, 0xa20f4fbbb97f4669, 0xf56c065ce31cded6, 0x1f1bb9eaff27f435, 0x7566469d4053c789, 0x9553555f45682aa0, 0xee5182643bcae696, 0x6263448d73ca0379, 0x7d303ee12ba22a53, 0x328d19361707968a, 0xdee59022ec08124a, 0x516f102c0c8e6996, 0x5d94368c517ce824, 0xb834b91be2fc1c76, 0x34eeb1b80d8af592, 0x1e478f42c313786a]

private theorem rounds40_1 : sixRounds 6 (by decide) quarter40_1 = quarter40_2 := by
  decide +kernel

private def quarter40_3 : Vector UInt64 25 :=
  #v[0x6bfa7294fd7e9eeb, 0x5aba84c5283b9714, 0x2b13af3a10771d39, 0x566944a1bceb22c, 0x1322c5e5ca48e927, 0xa0b89143f429e2b5, 0x592304321f06a2ae, 0x926b1d72ec3a917f, 0xa2a57ce4d5ffab1c, 0x261922e74af26421, 0xa5c07f6d2d717139, 0xb4af41737d519198, 0xd9522b2176ec1b1c, 0xc16b7fc57c3d38fb, 0xca7d8832d6f89321, 0x3ed58e0aaca6c328, 0x74780e040ec2f8de, 0x98939ff68760c6c9, 0xab32e890ac7f0561, 0xe07ceebbe12694c5, 0xf78ba9dcbd9b2aa4, 0x9387e5294c997aa1, 0xa7434cf042068759, 0x363c82bbe3c4adb6, 0x5b745a7052266bcb]

private theorem rounds40_2 : sixRounds 12 (by decide) quarter40_2 = quarter40_3 := by
  decide +kernel

private theorem rounds40_3 : sixRounds 18 (by decide) quarter40_3 = state41 := by
  decide +kernel

private theorem perm40 : KECCAK.f1600 absorbed40 = state41 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds40_0, rounds40_1, rounds40_2, rounds40_3]
  rfl

theorem block40 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes40 ++ tail) state40 =
      KECCAK.Bytes.run 0 tail state41 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes40 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb40 ws)) := by
    rfl
  exact (step state40).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words40).trans perm40))

private def absorb41 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x16 0xa1 0xc4 0x63 0xf1 0xa7 0x2b 0x95)) 1 (by decide) (UInt64.ofBytes 0xef 0xb3 0x23 0xf5 0x4d 0x5a 0xf5 0x28)) 2 (by decide) (UInt64.ofBytes 0x52 0x81 0x82 0x80 0x51 0x40 0x60 0x87)) 3 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x20 0x60)) 4 (by decide) (UInt64.ofBytes 0x1 0x60 0xa3 0x90 0x3 0x91 0x80 0x51)) 5 (by decide) (UInt64.ofBytes 0x50 0x92 0x93 0x50 0x50 0x50 0x50 0x93)) 6 (by decide) (UInt64.ofBytes 0x8 0x60 0x0 0x60 0x5b 0x56 0x50 0x50)) 7 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x90 0x54 0x90 0x0 0x60)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x4 0x90 0xa)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x16)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x33 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x15 0x14 0x16 0xff 0xff 0xff 0xff 0xff))

private def absorbed41 : Vector UInt64 25 :=
  #v[0x91f530b3aa6666f9, 0x5ba939dd9c4617e6, 0x50fb724352aef0a3, 0xd1b104772a850527, 0xceb17411e863e9bd, 0xe20914e800e8379b, 0xbb4fa596fc7e4e65, 0x5f5f46524ca365c2, 0x3f87167cb4ac2122, 0xa4745d9b6d19ea14, 0x68f0e6e7270341f7, 0x5a7a326a05382d32, 0x3e00cd08585708b1, 0x69570588a05349cb, 0x3419fb88fd339a87, 0xb080e06b2a7e10d1, 0xfc2b281d840599fd, 0x66533b10b9056f94, 0xd7c3e2ba5a4d1dd0, 0x51945f778257a40, 0x22c11a985e70826e, 0xdcb97f27926a96ff, 0xa9db173efdae67fd, 0x9a21cd5df3f1187b, 0xcf7ca1bd89a2cd4a]

private theorem words41 : absorb41 state41 = absorbed41 := by
  decide +kernel

private def quarter41_1 : Vector UInt64 25 :=
  #v[0x59b58f458ae07342, 0x4bed4498f97b5664, 0x50fa98d5ddf391db, 0xcb943c2c8aa19222, 0x1be8b6022aa3d72, 0x731e2a1532657dad, 0x4ec3161838683714, 0x52beea2718d37c33, 0x2eedfd8594faa8cc, 0xfb725c1270f9b0b0, 0xadea02b6aa6c40df, 0x6e0c49aeb92b36aa, 0x3e16b40a8a2cd6d4, 0x6a73f25c7ea03955, 0xf0296e695b0b45ec, 0x802d7f16c5ba3931, 0x2702b7582f9abb04, 0x17fe807b03167f22, 0xcb304a43917da061, 0xd5f004bc715836d4, 0xd2c4b84283de9c56, 0xf1951648c2cc0b05, 0x7a6742738d605cd6, 0xa5b810ae587e39b, 0x9f62919585b52a74]

private theorem rounds41_0 : sixRounds 0 (by decide) absorbed41 = quarter41_1 := by
  decide +kernel

private def quarter41_2 : Vector UInt64 25 :=
  #v[0x5922f53db075b6f4, 0xa09227981e5cb905, 0x2ac54a1cbf88dab8, 0xd7b38affd8e4ff5b, 0x6266f4663045d7c5, 0xe50bb3ea12d9c431, 0xf34a511d2c6589b, 0xf1bd9bc011d82d8a, 0xcc0131c9ab45d63a, 0xb0c6f3b99dabeb88, 0x18991a3e87d53bdc, 0x6555b8d895db329f, 0xc975d514e08d8674, 0xe2ba15c97ae49381, 0x896b350496cc4ae0, 0xdae5b30fe6f34230, 0x63a02b4e5220dc05, 0x680ea5ff57f9243a, 0x36020da103d3c31b, 0xd436f1b166ce67b5, 0x48eaaa0fbc3eba5d, 0x1a72f26f5f007a3f, 0xefdd1c94989d1534, 0x327a463bbaf7e2e7, 0x7e0ab1222e6fcd8f]

private theorem rounds41_1 : sixRounds 6 (by decide) quarter41_1 = quarter41_2 := by
  decide +kernel

private def quarter41_3 : Vector UInt64 25 :=
  #v[0xe6645658c5d77b44, 0xe317261f120d18be, 0xd9d24b6ed149417, 0xfbd61d955d2bbe80, 0xc0ece459a56108dc, 0x14eb8a0b28561cfc, 0x4bc194a289d1a0bf, 0xf8f8e1a4e79843f6, 0x637e3cac4860eb41, 0x298f44fcca51a5fe, 0x4274fe4b74405a47, 0xb4890261136d3e79, 0x80e378e5d4c8a48a, 0x9decce33905d30a7, 0xa0028879647e7674, 0x6670dafec6e06afc, 0x78fe52d14df293d5, 0x91a2868be01a1210, 0xc345b7457431b867, 0x7d23cb18655a8b6b, 0xf612d10b3afbf95, 0xbed15b2694a38669, 0x68adcb4a5b3e8df0, 0xc7761b71f5eba9c7, 0x8a3890e233a5ba1d]

private theorem rounds41_2 : sixRounds 12 (by decide) quarter41_2 = quarter41_3 := by
  decide +kernel

private theorem rounds41_3 : sixRounds 18 (by decide) quarter41_3 = state42 := by
  decide +kernel

private theorem perm41 : KECCAK.f1600 absorbed41 = state42 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds41_0, rounds41_1, rounds41_2, rounds41_3]
  rfl

theorem block41 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes41 ++ tail) state41 =
      KECCAK.Bytes.run 0 tail state42 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes41 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb41 ws)) := by
    rfl
  exact (step state41).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words41).trans perm41))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
