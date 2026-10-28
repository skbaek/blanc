import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb54 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x61 0x54 0x20 0x0 0x60 0x1 0x20 0x60)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0x63 0x90 0x91 0x90 0x2b 0x2e)) 2 (by decide) (UInt64.ofBytes 0x60 0x9 0x60 0x5b 0x56 0x16 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x88 0x0)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x52 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x90 0x1 0x20 0x60)) 10 (by decide) (UInt64.ofBytes 0x50 0x55 0x90 0x81 0x20 0x0 0x60 0x1)) 11 (by decide) (UInt64.ofBytes 0x12 0x2e 0x61 0x84 0x85 0x75 0x1c 0x61)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x63 0x90 0x91 0x90)) 13 (by decide) (UInt64.ofBytes 0x33 0x0 0x60 0xd 0x60 0x5b 0x56 0x16)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0xff 0xff 0xff 0xff 0xff))

private def absorbed54 : Vector UInt64 25 :=
  #v[0xac225fb430cd634, 0x896bcb1050aaae09, 0x3df3d4d442974149, 0xaa3ee86c7f53660e, 0x83828a25b0c392df, 0x2fd11e90fe4e07e0, 0xcbe1ca9ef6d5f103, 0x5f9440a2106960f8, 0xc50fc6e6f7be87af, 0x7e53745a7d9e45a3, 0x5808a0b37f0a0c11, 0x151489c1ca349581, 0xc8608591a6291759, 0x8b029cd47335d77a, 0x61e41912b5e12cdd, 0xb0731605296ac8c2, 0xe13f2f66b58c6da8, 0xb5c0d1ccf81500ad, 0x286ef802bd7736a2, 0x9ba9ec4d1bef9a9a, 0x827d50c9cc5a0da3, 0x69b2428a18df5311, 0xd8d8de03baca3345, 0x98dc44581c51fe0c, 0xe4c2ded7a85e0df6]

private theorem words54 : absorb54 state54 = absorbed54 := by
  decide +kernel

private def quarter54_1 : Vector UInt64 25 :=
  #v[0xe0bd2b8e6d697f18, 0x7349eb2cdcb0d3dc, 0x4d2682167942af50, 0xde4c625f4b3a2b6a, 0x38dc652360de74f3, 0x764743b7621ee033, 0xe562508a3fe05052, 0x19e798cfa4f75970, 0xe8636b563343c9c3, 0x1b6219f6be49ca0a, 0xd8d223ee87a9eb9, 0x1c6b733bc0a27057, 0x6b67afc6ba7daae9, 0xacbfe633fc4d33fe, 0x124ec7e85933638b, 0xbe248c579e2e3b98, 0x7d83190109f07f6e, 0x700fa18737131401, 0xf18c6dad45621696, 0xe3c98f68899ca093, 0x43407e916fa65b87, 0x9390a9e650702bf7, 0x866a9dde3164e00f, 0x96752c8cd5b5c483, 0x4546d085db06259c]

private theorem rounds54_0 : sixRounds 0 (by decide) absorbed54 = quarter54_1 := by
  decide +kernel

private def quarter54_2 : Vector UInt64 25 :=
  #v[0xc691ddcf2acfcb7d, 0xf780b1b656b15174, 0x515bc9e16e7ac7ad, 0x3618beefe9d72bd2, 0x6cd25d059415ada0, 0xb07e8781f941dce6, 0x6b28c71a24d0e8c9, 0x191a03627fcb74d3, 0x427c6c2b2fadbeae, 0x85449b64a46bf9ec, 0xeff64538b427301, 0xff80fa92104224b7, 0xd83baf6dc79c1fed, 0x9fba0763fb1d83bb, 0xf5b5ed02935503e7, 0x5e1eb21c376d0155, 0x9a8d1cf30fc60119, 0x492f1b78fbc5da1f, 0x48572bcffcfbf898, 0x56cb9cc211a10c96, 0x54bc3ae1b4329a1d, 0x3263a17c51d6a006, 0xadbd22b7ae5a5e3e, 0x5c22717cf2f46313, 0x94d53e08fafc4be0]

private theorem rounds54_1 : sixRounds 6 (by decide) quarter54_1 = quarter54_2 := by
  decide +kernel

private def quarter54_3 : Vector UInt64 25 :=
  #v[0x3ecaa4d66eb9cdee, 0xc0998d1b3687685c, 0x1d26add0b0b26bb2, 0x49c2fbb22bba8750, 0x5f19b9ad2b2e8c58, 0x52892e471f3b8874, 0xd7fdc5560081fd5a, 0x9a80fefa4f31407a, 0xdea103bf5713e34f, 0x22e1fcb58be81ae6, 0xbb0cf3127c79deb4, 0x2da4e1837f0aec1d, 0xe1263be5ca14fc65, 0x9b0e22b34ae2e9c9, 0xf7eb6d80975e119c, 0x1841ff400c2c138e, 0xa85bb50468ec8ed, 0x7298ad99916f535d, 0x9062b156410aa4b5, 0x586afca523796a1e, 0x5a219d56286d5aec, 0xce4e995dc414c59d, 0xabb3675bd794d783, 0x4989016f6f8f0430, 0x91ffd55ef8178d11]

private theorem rounds54_2 : sixRounds 12 (by decide) quarter54_2 = quarter54_3 := by
  decide +kernel

private theorem rounds54_3 : sixRounds 18 (by decide) quarter54_3 = state55 := by
  decide +kernel

private theorem perm54 : KECCAK.f1600 absorbed54 = state55 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds54_0, rounds54_1, rounds54_2, rounds54_3]
  rfl

theorem block54 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes54 ++ tail) state54 =
      KECCAK.Bytes.run 0 tail state55 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes54 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb54 ws)) := by
    rfl
  exact (step state54).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words54).trans perm54))

private def absorb55 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x16 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x52 0x81 0x90 0x1)) 4 (by decide) (UInt64.ofBytes 0x73 0x85 0x50 0x55 0x90 0x81 0x20 0x0)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0x73 0x33 0x16 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x30 0x85 0xab 0x7f 0x16 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x62 0xc4 0x34 0x92 0xb5 0xc9 0x7d 0xf8)) 12 (by decide) (UInt64.ofBytes 0x6d 0x53 0xb2 0x2b 0x21 0x17 0xf9 0x3b)) 13 (by decide) (UInt64.ofBytes 0x92 0xda 0xe5 0xe7 0xc8 0x74 0x75 0x64)) 14 (by decide) (UInt64.ofBytes 0x40 0x60 0x87 0xf8 0xc9 0xe0 0xed 0xc2)) 15 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x82 0x80 0x51)) 16 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91))

private def absorbed55 : Vector UInt64 25 :=
  #v[0x1ef7db1196be7c6e, 0x67c114281982d470, 0x801738c402e53aaa, 0x8ee00f5f2b2ca031, 0x1d780bcee7bb70f4, 0x5a1f18cf3a0c91bc, 0x29a845eb872e44bc, 0x1debcb9905671808, 0x89a76ef06dd849b0, 0xa702763bc3ca6737, 0x4979d54d204d5340, 0xa5a0610a2ac08f0d, 0x125d3750216f2880, 0x1f541bea94db0ab0, 0xdebca88b678d2c06, 0x13e0f61dcdc1739f, 0x77cb77bac56cd686, 0x7c49202e0e1c064b, 0x9bc788443d67fa30, 0xee986426b2e28ad0, 0x1dfa51f70eb95647, 0x7a4a29cdb87bb507, 0x3e0b575866ae48c0, 0x1399aab3ff22a306, 0x31eba231eabd84a1]

private theorem words55 : absorb55 state55 = absorbed55 := by
  decide +kernel

private def quarter55_1 : Vector UInt64 25 :=
  #v[0x912967c65b20bd9, 0x59ab8d9a61ab1bc, 0x3f06544b465290fc, 0xf4e368f3f66987f7, 0x463cb7687cc2440d, 0xc8b4fa9fde41e4a5, 0xd1b2d29393b25ba5, 0x7e76a3971cdf33f8, 0x44527cd409093f29, 0xfe1e7991d4a34c, 0xcb84c087a2521c57, 0xcdb43d091a8e4b2d, 0x17d5b5933fc4d15f, 0x6a1b00822e012566, 0xab8499093ca1f49, 0x8baf21420dbf3f87, 0x7de8b7c8ff4968bb, 0xdbcfa12be1b681f, 0x29b7e3257c832c4c, 0xcaf9d88e31064f82, 0x650430eba3d907ca, 0xf1d1afa068edc0f8, 0x10b01455ba593481, 0xfe8ed625e8767f17, 0x4fb06c71485c407a]

private theorem rounds55_0 : sixRounds 0 (by decide) absorbed55 = quarter55_1 := by
  decide +kernel

private def quarter55_2 : Vector UInt64 25 :=
  #v[0xf11eefcf4de79009, 0x470223a58d98af7e, 0xd1425191e697ee87, 0xb7d02bbc86f2494f, 0xcb5d91c143139d76, 0xb169323aad75c5ad, 0x43e81fffd19e090a, 0xec44562ea88f3e78, 0x5d75bf4d6b02eac8, 0xed0c801afab50af8, 0x4271e5a9b2a7eca6, 0x29370c0a46c1aa5e, 0xabac4a29ab6c2d17, 0xe85cb4b546a45c23, 0xb0bace6fdfe6cc32, 0x40b6907d6d04fcc9, 0xea062c6162a962fd, 0xf2a4fb80dad84456, 0xdad66fd0a9ecea70, 0x87d5e615429ebfa3, 0x1f980d3a0522910e, 0xba4ba50ca38ac5ff, 0x55a223b7ea4b211e, 0xd84ea1ae33a0c644, 0x966ef66c25cca4ec]

private theorem rounds55_1 : sixRounds 6 (by decide) quarter55_1 = quarter55_2 := by
  decide +kernel

private def quarter55_3 : Vector UInt64 25 :=
  #v[0x6532ea577f6a4ccb, 0x6d74e1a22a282cb0, 0x357bd8896ac330f0, 0x1a51c0bdd3ab72d2, 0x5b3c0e7f673e13d7, 0xe7e0c25e1ebeebee, 0xa3d079deb2ff5ccc, 0xb30949cd0e364e3, 0xf5628b192f732bbe, 0x2af6cbe4d0a7f8da, 0x8a59871ee46e6a5, 0x1c5e81f32cade4ce, 0xe0081d55edc198ac, 0x30111c7cdf05eb8e, 0x74ef2da29f316b6, 0xc447b67b4b049852, 0x4f3b11da05be7107, 0x91e1b99d6462733e, 0xa7e8e332ab8da5bb, 0x897fc1c1b9b52e4a, 0x4b8c325ded4695e1, 0xcaff75055130c347, 0x65b6492b953ef8af, 0xdebc94ad9d1d3cac, 0xcfa2a2d8184677ac]

private theorem rounds55_2 : sixRounds 12 (by decide) quarter55_2 = quarter55_3 := by
  decide +kernel

private theorem rounds55_3 : sixRounds 18 (by decide) quarter55_3 = state56 := by
  decide +kernel

private theorem perm55 : KECCAK.f1600 absorbed55 = state56 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds55_0, rounds55_1, rounds55_2, rounds55_3]
  rfl

theorem block55 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes55 ++ tail) state55 =
      KECCAK.Bytes.run 0 tail state56 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes55 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb55 ws)) := by
    rfl
  exact (step state55).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words55).trans perm55))

private def absorb56 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x85 0xa3 0x90 0x3)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x52 0xf2 0xdd 0x7f 0x0 0x60 0x16 0xff)) 4 (by decide) (UInt64.ofBytes 0xb0 0xc2 0x69 0x9b 0xc8 0xe2 0x1b 0xad)) 5 (by decide) (UInt64.ofBytes 0xa7 0x2b 0x95 0xaa 0x8d 0x37 0xfc 0x68)) 6 (by decide) (UInt64.ofBytes 0x5a 0xf5 0x28 0x16 0xa1 0xc4 0x63 0xf1)) 7 (by decide) (UInt64.ofBytes 0x40 0x60 0x87 0xef 0xb3 0x23 0xf5 0x4d)) 8 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x82 0x80 0x51)) 9 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 10 (by decide) (UInt64.ofBytes 0x50 0x50 0x93 0x1 0x60 0xa3 0x90 0x3)) 11 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x50 0x91 0x92 0x50 0x50)) 12 (by decide) (UInt64.ofBytes 0x54 0x90 0x14 0x60 0x1 0x60 0x0 0x60)) 13 (by decide) (UInt64.ofBytes 0x60 0x4 0x90 0xa 0x0 0x1 0x61 0x90)) 14 (by decide) (UInt64.ofBytes 0x98 0x1d 0x61 0x15 0x15 0x15 0x16 0xff)) 15 (by decide) (UInt64.ofBytes 0x1 0x60 0x5b 0xfd 0x80 0x0 0x60 0x57)) 16 (by decide) (UInt64.ofBytes 0x73 0x33 0x0 0x60 0xc 0x60 0x15 0x15))

private def absorbed56 : Vector UInt64 25 :=
  #v[0x5f5943571aa64967, 0xa28202b1c782109f, 0x3aa56f64f0192461, 0x96a1c4facbf76ba9, 0x57b8fb82c1517843, 0x2471ee0ea79a5612, 0xf12e9773970b43c1, 0x98f0c7e56bace020, 0xb31bf4d8f5e6c568, 0x86031b54f4318623, 0x47175c491c4d02c6, 0xc0960df0615a87c6, 0xec0805b72027916c, 0x8b8c1acad6a22f00, 0x55a73c78e2d89aae, 0x578a642c9bdc1431, 0xf20afd8a85747197, 0xde7634ccbbb6ca6d, 0xca4f3cd207d17bf9, 0xa4a421772f56374c, 0x8603387b4883fb91, 0x1224809e9f9589c2, 0x122f8288cce4217e, 0x2f119e8b195c730f, 0x7b2fb735c1be88c6]

private theorem words56 : absorb56 state56 = absorbed56 := by
  decide +kernel

private def quarter56_1 : Vector UInt64 25 :=
  #v[0xdf04329caa124355, 0x323c29ec83c5db88, 0x56ce8f790b70d9f1, 0xbccf03ecd178614b, 0xdfafcfaed7e8cf95, 0x24e61fcc50ad643c, 0x4b1fb34e759786a2, 0x73ba8c920ddccde8, 0x50362234e50ef7c, 0x3b1f88ea789512e, 0x2e5ae1d23a4f21c4, 0x4c717ced66d02d5b, 0xe84e573424149c7c, 0xb4ff40b70c98842f, 0xf8850bb6fd5f1a2e, 0x305995042637786b, 0x1e9766ff7fba4dca, 0xb4b83bce340051a3, 0xa96019e363ad24c5, 0x2309716a8ce987c1, 0x609210b1b9a524be, 0x6960c01a310a2336, 0x237e217ccde76ba, 0x31475c1593a207ac, 0xe8451c7ce3875296]

private theorem rounds56_0 : sixRounds 0 (by decide) absorbed56 = quarter56_1 := by
  decide +kernel

private def quarter56_2 : Vector UInt64 25 :=
  #v[0xb53b704837162e10, 0x762fc87e72b68551, 0xed1fddc2904d6b64, 0x7bada90d16651dd7, 0x720508d5de0296ae, 0x97b22ea2954a72d4, 0xcdd6e121559f383, 0xd713ceb84ed16c85, 0x11ce3ebc59622420, 0x182a8a6b25f0cd6, 0xf90e7874aebf23f7, 0x446998d5b9a6f9a7, 0xe403de3d00853d1e, 0xb48dbf5eb9f265cd, 0xecc6d49ecb7ca22d, 0x7995e5cb765ffb2d, 0xd0a0ddeea26d6ba3, 0x660b3ece2c978eb9, 0x990d27b9d65e748c, 0x62b9d4354e069565, 0xff0298ad13a6f38d, 0xf57215144de449be, 0x5116c8e2e90eed3a, 0xe190ea82f5287c67, 0x534d88ca027ef408]

private theorem rounds56_1 : sixRounds 6 (by decide) quarter56_1 = quarter56_2 := by
  decide +kernel

private def quarter56_3 : Vector UInt64 25 :=
  #v[0x7f3e1d1968364465, 0xebabda7d0e26d2b9, 0x710bf3ff62807c28, 0xcdedbb5fe3b6be83, 0x116b24d1b3f4dd9e, 0xb05849bab4d27fbd, 0xdd965cff2365534d, 0x4c40037da430db9d, 0x4221435556c6dc24, 0x6ed2567816308be6, 0x73682d24725150bd, 0xe768db9ab535d5aa, 0x4822b97a6e718e94, 0xb49ac20b8737b3b2, 0xfb2f8554643ef63a, 0xf84d7766365b577f, 0x5bb45f0b83ae9a92, 0x130541d2568c561, 0x2627e368316011e8, 0xda0866e5a45074cd, 0xee13b6e03a9aa108, 0xe40e4904bfbeaa52, 0x1a953f1675e11720, 0xd3a68bf3b089ba83, 0x8c06b1c77451f32a]

private theorem rounds56_2 : sixRounds 12 (by decide) quarter56_2 = quarter56_3 := by
  decide +kernel

private theorem rounds56_3 : sixRounds 18 (by decide) quarter56_3 = state57 := by
  decide +kernel

private theorem perm56 : KECCAK.f1600 absorbed56 = state57 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds56_0, rounds56_1, rounds56_2, rounds56_3]
  rfl

theorem block56 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes56 ++ tail) state56 =
      KECCAK.Bytes.run 0 tail state57 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes56 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb56 ws)) := by
    rfl
  exact (step state56).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words56).trans perm56))

private def absorb57 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x16 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x0 0x60 0x1 0x20 0x60 0x52 0x81 0x90)) 7 (by decide) (UInt64.ofBytes 0x1 0x61 0x90 0x54 0x90 0x0 0x60 0x20)) 8 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x4 0x90 0xa 0x0)) 9 (by decide) (UInt64.ofBytes 0x57 0xf7 0x1d 0x61 0x15 0x15 0x14 0x15)) 10 (by decide) (UInt64.ofBytes 0x0 0x60 0x33 0x5b 0xfd 0x80 0x0 0x60)) 11 (by decide) (UInt64.ofBytes 0x73 0x83 0x0 0x60 0x3 0x60 0x15 0x15)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed57 : Vector UInt64 25 :=
  #v[0xdd8f37bc739f9218, 0xac3070d65cdaedf4, 0xc02494a1655ae72b, 0x728b889bf8c49d96, 0xb0aebd0a2681f245, 0xafb3f19730e31f0a, 0x2c9cf191eb168c84, 0x9dcb35e3edb5b8b, 0x76170d37f9f00aec, 0x8a4e004dafc366f6, 0xad2dea9ab83f51b0, 0xe9456810b3d66256, 0xc89bdf23d853df91, 0x5c892e300510ea8e, 0xc166ee785b3c3547, 0xe20f8c5b233d9c25, 0x4e2d9d62e5e33f95, 0xd0de23dd4c4f874f, 0x1592fb8a9b6f077e, 0x454c2f4022f79e58, 0x540ee519fc3e0259, 0xb99eb450582df333, 0x9196134736104f34, 0xd375dfaf72c8a8fe, 0xc6ab6bc8518d393e]

private theorem words57 : absorb57 state57 = absorbed57 := by
  decide +kernel

private def quarter57_1 : Vector UInt64 25 :=
  #v[0x6b01c476c9d51bc, 0x6e031a5f607a47d1, 0xe099e468380b0393, 0x2c76e5f273005ddd, 0x95ab56e125d472e9, 0xbd325dde55a328b8, 0x7664b43730a68722, 0x442caf2436410d14, 0xa439c8b38c7294d8, 0xae73d25e88ea75eb, 0xe0136cfcdc2b0ce4, 0x4cbb4b0e34c0a931, 0xc04baa147ab92e26, 0x48e1487b0eea241, 0xe318a2003d359caa, 0x113bf8bfc4764a4, 0x401c798b0b963153, 0x1166c01776235157, 0x45d1feb73b3d347f, 0xeca00dd7dc0d5c99, 0xe9046b924e41ac85, 0x79cb7a4869dab985, 0xc233f77bd9537305, 0x7785dac5e5fd6ac3, 0x194a3d7a48135c8c]

private theorem rounds57_0 : sixRounds 0 (by decide) absorbed57 = quarter57_1 := by
  decide +kernel

private def quarter57_2 : Vector UInt64 25 :=
  #v[0x9d37aff92b8197f7, 0xb0329b44ab1ebb58, 0x53017901281118de, 0x33fd539d9c046edf, 0x7d7c00ce0fe038eb, 0x66b00532d2d8f290, 0x29d7dcb20d5f87, 0xea3bf018eb01bcf8, 0x3c4ca4afd3e474bb, 0xef7747bdc685372, 0xe21dbc1d9a666736, 0xc7e16f76643622d9, 0xac639086a78f710d, 0x515b23e0fd00ecf9, 0x264ec9c1eab27c6d, 0x9191cd72daf8ac9d, 0x7f60d5ed6baf7633, 0x591f80183f450a6, 0xe43bdd2a7ac234cb, 0x4c36a4e22e7b609f, 0x2ba37eb46862f1e1, 0x849d353fa8d596ef, 0x92ef32071ea87e94, 0xd2df9f8d3d5a1636, 0xb82cd54b8271b8b8]

private theorem rounds57_1 : sixRounds 6 (by decide) quarter57_1 = quarter57_2 := by
  decide +kernel

private def quarter57_3 : Vector UInt64 25 :=
  #v[0xb14dbddcd7b6b2d5, 0x37ece5037ff372e, 0x117ecb527861a7ee, 0x4bae4137368db596, 0x83780a12c83fa50e, 0xe43ebec3b299fec0, 0xf7bf35d407348bcf, 0x9417f5cca9938072, 0x28a065e891b5a994, 0x7b07e51a5407cf4a, 0xfecb0d9afcbc7d90, 0x63ff739f63962d71, 0xc29682244510a40d, 0xed29a66c2de4eda9, 0x3609121fa73badf2, 0xe54219eb1ebcb469, 0x5310fecca981719a, 0xf62c4154bb19617e, 0xdf9356492a2c60b5, 0x86b7ed99037cf9a9, 0x6c6cd82d2de7be18, 0x8cfa50f5f1e3571, 0xa90641402fd5f67b, 0x94c4c70e887840f3, 0x5351992ffd76ea08]

private theorem rounds57_2 : sixRounds 12 (by decide) quarter57_2 = quarter57_3 := by
  decide +kernel

private theorem rounds57_3 : sixRounds 18 (by decide) quarter57_3 = state58 := by
  decide +kernel

private theorem perm57 : KECCAK.f1600 absorbed57 = state58 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds57_0, rounds57_1, rounds57_2, rounds57_3]
  rfl

theorem block57 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes57 ++ tail) state57 =
      KECCAK.Bytes.run 0 tail state58 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes57 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb57 ws)) := by
    rfl
  exact (step state57).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words57).trans perm57))

private def absorb58 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x16 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x0 0x60 0x1 0x20 0x60 0x52 0x81 0x90)) 2 (by decide) (UInt64.ofBytes 0x1 0x61 0x90 0x54 0x90 0x0 0x60 0x20)) 3 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x4 0x90 0xa 0x0)) 4 (by decide) (UInt64.ofBytes 0x57 0x57 0x1e 0x61 0x15 0x15 0x14 0x15)) 5 (by decide) (UInt64.ofBytes 0x60 0x9 0x60 0x5b 0xfd 0x80 0x0 0x60)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x33 0x0)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x52 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x90 0x1 0x20 0x60)) 13 (by decide) (UInt64.ofBytes 0x60 0x50 0x91 0x54 0x20 0x0 0x60 0x1)) 14 (by decide) (UInt64.ofBytes 0xa8 0x1e 0x61 0x15 0x15 0x11 0x83 0x0)) 15 (by decide) (UInt64.ofBytes 0x82 0x82 0x5b 0xfd 0x80 0x0 0x60 0x57)) 16 (by decide) (UInt64.ofBytes 0x57 0xb7 0x1e 0x61 0x15 0x15 0x15 0x10))

private def absorbed58 : Vector UInt64 25 :=
  #v[0x21fc8fbec40294b8, 0xc2d7a68ce7de7d63, 0x530dcd9be67ecc78, 0x69113b8ed867d9da, 0xaec251c0a63cebe6, 0x5b789303b89b21aa, 0xaa92adf47c06e0ba, 0x414e0889c713c4b6, 0x89863a2e5d69bf0c, 0x84bb180c69d57d38, 0x6179a960e476f953, 0xaa6f443a408e994, 0x30312964eff2efa8, 0x5a8da043690bcf92, 0xe17619c6b5f6437f, 0xc186f873657d0b5a, 0x2885c3514f3de62, 0x98ee4cec82951109, 0x8f4369f4528c7185, 0x416a8fc9c1dc7ff6, 0x400551a590f67c4d, 0xe6eb56fedd18c47e, 0x165f937eb7585c92, 0x5b99d53e2a1185c6, 0x7c5dec5a1db08435]

private theorem words58 : absorb58 state58 = absorbed58 := by
  decide +kernel

private def quarter58_1 : Vector UInt64 25 :=
  #v[0x8f3d2617f083a8ff, 0x4728a4045bc3134b, 0x7307581046fcc4fa, 0x1d687553f3b13b53, 0xae7094a4074e3528, 0xc8d89e7f76e4af9a, 0x67e57a98f805a0ca, 0xe9d89b0b5e07c9ed, 0x9e71d142b89eedab, 0x4e5a7a9924e160fe, 0xeb9a14866ca163c4, 0x8394a8b574f95a36, 0xfcf03f4562de22ce, 0x899da706565e4e6b, 0xccb12b20c1b72ecc, 0xcc3a18431e558005, 0x166d851b20ef66ed, 0x529efff3d21dcd33, 0x6750a9fd7b57f712, 0x3238446422747259, 0x84eb16583eece610, 0x41e89d9d49e959a9, 0x14246fa1329e7f1b, 0xd14097bda36c5ff7, 0xf60daf2698b22d78]

private theorem rounds58_0 : sixRounds 0 (by decide) absorbed58 = quarter58_1 := by
  decide +kernel

private def quarter58_2 : Vector UInt64 25 :=
  #v[0xcf7b57299ca64eb2, 0xaa6871cf92c38b3e, 0xe226a2edc5eb04c9, 0x49522d86e0ca5b12, 0x8d2e7c9a83b534e2, 0x8b330c22daf4d155, 0x33cfc5179b4b753c, 0x27c0b1edd471031f, 0x628a772145d11c0, 0x8af754f2f7ac4d92, 0x60d5d85c219eb53a, 0xffb3fdbde73f5399, 0x853dca02c214f39, 0xc2981bf163a235e5, 0x673a179a024b2e1c, 0x39c1561510b17100, 0x7639c4b0d9e0d9ac, 0xecb14251baf97865, 0x3266b6b069969a27, 0x661a2a3033f2d96, 0xe809d3125c417534, 0xdc759fcdc53fdca1, 0x4d0e61febec2814d, 0x78af1bcaef72beee, 0xb81a40567dc803b0]

private theorem rounds58_1 : sixRounds 6 (by decide) quarter58_1 = quarter58_2 := by
  decide +kernel

private def quarter58_3 : Vector UInt64 25 :=
  #v[0xbf78327be0615ecf, 0x51a70edeceab9692, 0x498e3f892f740d8d, 0x5d04b7ccaa40a66b, 0xf78938fa231ffe4a, 0x6a7e179063d24ace, 0x4f2f816422a2737c, 0xaa8fd9ebf1619122, 0x80ac892b309a10e0, 0xbab3f46b050811a7, 0xfb6d72c23870d7f7, 0xdb6253be709b13f4, 0xb6cbafb331370a60, 0xc19658a4f91a8ace, 0xd8955b115a0f8e28, 0xd91f6b5d8a213a4d, 0x1f34a36cd9b85ad3, 0xe87a3725fafee7fa, 0x7bfe8fb6ab740689, 0x7051e400bd2232ad, 0xcc7cf2bbd3c6dcfa, 0x2523cd29965ada81, 0x2cc49c630b7def5d, 0x2ba6979e395cb636, 0xc9ef63a9c9d5ec51]

private theorem rounds58_2 : sixRounds 12 (by decide) quarter58_2 = quarter58_3 := by
  decide +kernel

private theorem rounds58_3 : sixRounds 18 (by decide) quarter58_3 = state59 := by
  decide +kernel

private theorem perm58 : KECCAK.f1600 absorbed58 = state59 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds58_0, rounds58_1, rounds58_2, rounds58_3]
  rfl

theorem block58 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes58 ++ tail) state58 =
      KECCAK.Bytes.run 0 tail state59 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes58 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb58 ws)) := by
    rfl
  exact (step state58).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words58).trans perm58))

private def absorb59 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xcc 0x1e 0x61 0x5b 0xfd 0x80 0x0 0x60)) 1 (by decide) (UInt64.ofBytes 0x90 0x12 0x2e 0x61 0x54 0xb 0x60 0x83)) 2 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0x63 0x90 0x91)) 3 (by decide) (UInt64.ofBytes 0x50 0x55 0x90 0x81 0xb 0x60 0x5b 0x56)) 4 (by decide) (UInt64.ofBytes 0x12 0x2e 0x61 0x83 0x83 0xe5 0x1e 0x61)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x63 0x90 0x91 0x90)) 6 (by decide) (UInt64.ofBytes 0x33 0x0 0x60 0x9 0x60 0x5b 0x56 0x16)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x16 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x52 0x81 0x90 0x1)) 14 (by decide) (UInt64.ofBytes 0x73 0x33 0x50 0x55 0x90 0x81 0x20 0x0)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed59 : Vector UInt64 25 :=
  #v[0x60e35f4f061c9d64, 0x5846cc380c51ef1f, 0x7c0856ff64567dea, 0xdc90b809a09c27a4, 0x19843b4520623ee7, 0x7cd96bbfca82ac38, 0x3fe53bd4f6482d93, 0xcf366dce796060c8, 0xd1b7fc87558fe394, 0xa70d4dbc088259b7, 0x1441f18b5417fcb2, 0x3cafdc9e3d0fd93e, 0xd39324438d81df46, 0xa11f8a0619bfa4be, 0x32e89f6d3285ed2e, 0xd68c6ad01aa61cbb, 0xc60c8bd91e788de8, 0xe76ed933a13bcc2d, 0x14b90fff3e132584, 0x27246591b00bd4a4, 0xfc283b813b15747e, 0x24396eb90d4fb6b0, 0x2f2f843794b588f3, 0xa3ebd6e9c7f8490, 0x21baa02b310f48ab]

private theorem words59 : absorb59 state59 = absorbed59 := by
  decide +kernel

private def quarter59_1 : Vector UInt64 25 :=
  #v[0xe4233574fe8710e3, 0xbe208a2b0c5cd17a, 0xd3f18133a27a8d2a, 0xb0614804dde38e41, 0x6f1223c1a556c2e6, 0xd0ea7e48e708c755, 0xb81e21b572ea3acb, 0x76344a83a9680a4d, 0x78909c116e8434e6, 0x124126e8242e56bd, 0x902925790e245018, 0x5736fce5b1680e5f, 0x149413802fc50fd5, 0xb2bae37432bbd01d, 0xd9af60c5609f669, 0xc2fe2a3d983c5a3b, 0x750b419a00cecd71, 0xf613c70208520f8a, 0x6b5ef4680d0b8465, 0x4ab0b1b43db22367, 0x79a290e22202752a, 0x4f270072d1d8183, 0x68fc8122282cce63, 0x4b32bb0b7dc4a999, 0xb43b9392e260cc62]

private theorem rounds59_0 : sixRounds 0 (by decide) absorbed59 = quarter59_1 := by
  decide +kernel

private def quarter59_2 : Vector UInt64 25 :=
  #v[0x4a11e391bdd39959, 0xbf2d42aec0e05cb3, 0xc249e091106ca9a3, 0x619fa70effa26c0f, 0xcf623814d00f7e0c, 0xc1f64d08bef506d0, 0xe837065bd6901cd9, 0x20b753d0dc14144d, 0xee2706af9916032c, 0x7524f080edd389bd, 0xba9c4c1d9ed0938e, 0x3cae171c18b592a9, 0x552b80b5b1424159, 0x7ba0cfc3bd29dda0, 0x9bc383145df127d, 0x40ebeef304992a57, 0x54b45055f295b44, 0x9c11eeec60f18a, 0xb1a50e6e24ce8812, 0x50e628f4f16f63c3, 0xd536ca8dc3dae586, 0x8ae205e230dc5d44, 0xf86bc396ea00b6c3, 0xa30d4236482c9b6, 0x3ee27b4be7909d15]

private theorem rounds59_1 : sixRounds 6 (by decide) quarter59_1 = quarter59_2 := by
  decide +kernel

private def quarter59_3 : Vector UInt64 25 :=
  #v[0xf6c137f5a1c4d50d, 0xccb6a2caa6158d7e, 0xf6bb91c04a0731ad, 0xaaaef26614695b72, 0xae8f5da6627a5834, 0x2a32923de36db4d7, 0x9a29d43525488903, 0xf12e17f161af0fd3, 0x4fdd2ea97ff009a4, 0xdcccefec539ffd8d, 0x5db02ec87ceacee8, 0xf597394ad72ae638, 0xccde3030712196f7, 0xea388a69e24d6703, 0x9a7dea95755bc3cd, 0x83d1e82317f865b8, 0x13c41c5ef64042b7, 0x3796d29938900e90, 0x62a15d07ddc45a11, 0x6b92eae09ce0a2bc, 0xd4ef5ae7966b7a6, 0x81a50e04b25b1974, 0xd062b97949b674b1, 0x7f8e62636619a6f5, 0x9e61bc905492b26f]

private theorem rounds59_2 : sixRounds 12 (by decide) quarter59_2 = quarter59_3 := by
  decide +kernel

private theorem rounds59_3 : sixRounds 18 (by decide) quarter59_3 = state60 := by
  decide +kernel

private theorem perm59 : KECCAK.f1600 absorbed59 = state60 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds59_0, rounds59_1, rounds59_2, rounds59_3]
  rfl

theorem block59 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes59 ++ tail) state59 =
      KECCAK.Bytes.run 0 tail state60 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes59 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb59 ws)) := by
    rfl
  exact (step state59).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words59).trans perm59))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
