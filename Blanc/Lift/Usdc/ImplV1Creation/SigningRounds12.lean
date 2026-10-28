import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb72 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x85 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x15 0x14 0x16 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0xc5 0x25 0x61 0x15 0x15)) 5 (by decide) (UInt64.ofBytes 0x33 0x0 0x60 0x9 0x60 0x5b 0xfd 0x80)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x16 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x52 0x81 0x90 0x1)) 13 (by decide) (UInt64.ofBytes 0x15 0x15 0x15 0x11 0x84 0x54 0x20 0x0)) 14 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x13 0x26 0x61)) 15 (by decide) (UInt64.ofBytes 0x60 0x9 0x60 0x84 0x65 0x26 0x61 0x5b)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x33 0x0))

private def absorbed72 : Vector UInt64 25 :=
  #v[0xa118f329ac857773, 0x7bb39fdab109cc4, 0xe6caff004dc883c5, 0x68c8dea89f715a60, 0x2d136e7688a8ea1c, 0x7a817f04fe898c61, 0x31936fc93dc7d8d5, 0x1cb384a0ee8c0342, 0x66fd55bc7aaec240, 0xe6680bd66404c17f, 0x1ad9dfaaaa6ae5b7, 0x2544a40841c7d7a6, 0x2880b5ca8c594da2, 0x4ecea557fddaf5c3, 0x329bd1caaebdf34e, 0x430f0c6f3d633798, 0x6b7a7666a93da6c6, 0xb49726c46e18a3d, 0x9799c78f1fcd33ef, 0xad0f439d4958d931, 0xa83cc35aa64273a2, 0x6e76127a1b323923, 0xc80787e9c3390d75, 0xe36c177d7defe75d, 0x685add0ddfcbb83d]

private theorem words72 : absorb72 state72 = absorbed72 := by
  decide +kernel

private def quarter72_1 : Vector UInt64 25 :=
  #v[0xf39b14155430ffc6, 0x2e1c025a58c3b85, 0x47cb70d7cec0ccb6, 0x58c0d3183cafc803, 0x2752fe9aa07babfc, 0x1d7f4a68cf8c5a23, 0x2588d3ae3063cca0, 0x3be58dd3decfb96a, 0x2d4a1c56e081fd0, 0xdead063b07c54e4c, 0xb58212d19a133916, 0x8d483174f5f0f80f, 0xf5b189d76d73fd72, 0x4d07c54fadecef6a, 0xa555306a3cf5c6a9, 0xeeb287d36b198513, 0xf566af876d994077, 0xe6208c40c5ca200, 0x74a7cb920c486b47, 0x15f554e9c6cff66c, 0xcc9580cc55aa8e83, 0xf45925f8c38d3a72, 0xe8431b0e3e45b56b, 0x25160ea26cef96cf, 0x5328db7e888a8eb]

private theorem rounds72_0 : sixRounds 0 (by decide) absorbed72 = quarter72_1 := by
  decide +kernel

private def quarter72_2 : Vector UInt64 25 :=
  #v[0xc866f0642483a9aa, 0xf70d2917af8650fe, 0x16665680d97ce197, 0x36fc388b151d6c6d, 0x877f31a8e3f17ad3, 0xf0f6e95b95fa3e1e, 0x26333d42673263ef, 0x6e3731ca669dc28, 0x47c2d478be15242b, 0xe60908e2bb4be265, 0x54644aab230c594c, 0xa95e8fc215ebff96, 0x66bef66d9d09a20b, 0x7d80a00c708ee264, 0xba73155f7a753272, 0x644ff8ff49c3c00f, 0xc0c7f795e0bb84c0, 0xeea377e9b11620a3, 0x449bb839b77b251a, 0xa9750237de65badd, 0xb5acf7eeb3169f9c, 0x643e22896eca9608, 0x44b379c3d01b97e0, 0xbfb50f79ab66d2b8, 0x6b6029089e3f7b59]

private theorem rounds72_1 : sixRounds 6 (by decide) quarter72_1 = quarter72_2 := by
  decide +kernel

private def quarter72_3 : Vector UInt64 25 :=
  #v[0xd133dff5cbcbf371, 0xa1700de243ce1f08, 0x7ddecc221d7aca58, 0x2e90a56736db39b5, 0xc5baa5e7b9e79ec6, 0x4326d060c173caf6, 0x838f7cd9c2a6fa81, 0xfc906698af015ff3, 0x8b108357c6606151, 0xc0eccaeb34847f2d, 0xf94c7a2af661504f, 0x4147cce5201dd7e5, 0x162db784db49b9a2, 0xc1b2a5db9439bbda, 0xf057d15e27b4dafb, 0x5c079bbb3afd57e1, 0xc38c1a747a6dcb31, 0x4c2cfaac65359ea5, 0x4c926e5bfca43d81, 0xff3326d879a9d728, 0xb926f21f74699465, 0x301dfa65cf3845cc, 0x1b10d5e9161b5f91, 0xdf3e82c7399018ff, 0x1fe2ea043d6510b0]

private theorem rounds72_2 : sixRounds 12 (by decide) quarter72_2 = quarter72_3 := by
  decide +kernel

private theorem rounds72_3 : sixRounds 18 (by decide) quarter72_3 = state73 := by
  decide +kernel

private theorem perm72 : KECCAK.f1600 absorbed72 = state73 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds72_0, rounds72_1, rounds72_2, rounds72_3]
  rfl

theorem block72 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes72 ++ tail) state72 =
      KECCAK.Bytes.run 0 tail state73 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes72 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb72 ws)) := by
    rfl
  exact (step state72).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words72).trans perm72))

private def absorb73 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x52 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x90 0x1 0x20 0x60)) 6 (by decide) (UInt64.ofBytes 0x12 0x2e 0x61 0x54 0x20 0x0 0x60 0x1)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x63 0x90 0x91 0x90)) 8 (by decide) (UInt64.ofBytes 0x33 0x0 0x60 0x9 0x60 0x5b 0x56 0x16)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x16 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x52 0x81 0x90 0x1)) 16 (by decide) (UInt64.ofBytes 0x26 0x61 0x50 0x55 0x90 0x81 0x20 0x0))

private def absorbed73 : Vector UInt64 25 :=
  #v[0xe044e00463bf44, 0xa4bcbf86f4e6af72, 0x5290dd81c386f4cc, 0xa28132ecaa81e7b1, 0xa8232c978cbb2edd, 0x66c394928d889876, 0x95e49f33cda9412d, 0x5f6f372d612338c, 0x6db3eba55c305cc9, 0x339b1f6432f1f5fe, 0x852578c1449d5f9a, 0x684177cce2c13077, 0x7e4a14e1d8d84356, 0x130f0a4b9a1d7609, 0xaf21fc005ab7d26e, 0xbbf9ecc6ba09c001, 0x5d04528998c0b33e, 0x6a5e81bc3c39f31, 0x4fb69bc67a92e5c9, 0x64539ea0bbd013cc, 0xbee015039d091221, 0xf0872571a6542ff9, 0x504fb7cab6b4826f, 0xf20336e9d3e2d830, 0x6babe4e7b18885ef]

private theorem words73 : absorb73 state73 = absorbed73 := by
  decide +kernel

private def quarter73_1 : Vector UInt64 25 :=
  #v[0x5d3324c7a6f6a3e9, 0x69a6285c9d29fbb2, 0x24a24cbb11f47dfb, 0xd8585833cb7eba41, 0x7868041c182da33e, 0x29fdbb7014a27a6, 0x5ee59b17d9c15db, 0x2e74d9540448e1, 0x883923ab59ad8fa4, 0xdb4ef9dc992e61a6, 0xfb9f1557a8dca81d, 0x547440d30df87096, 0x5802fc6370e75039, 0xa22cc71c6460aa53, 0xe092569e22f1a966, 0xa37296f54fe46559, 0xe0ede195c4f3b14c, 0x28f999230eef2a60, 0xf2b7164c39208426, 0x470c67cf41d0a2bd, 0x24d40e7f8571dd8e, 0xa09e4a3ecb822f71, 0xe71563dc497acd68, 0x445873be2f33bbfc, 0xef82bc90f36915eb]

private theorem rounds73_0 : sixRounds 0 (by decide) absorbed73 = quarter73_1 := by
  decide +kernel

private def quarter73_2 : Vector UInt64 25 :=
  #v[0x7f8cc7baf16bb45a, 0xf39a8f88279a6a13, 0xead1b0c7033734af, 0x4a03b4d365dc7b00, 0x386dc42ddcb8c603, 0xac802028fe9dee53, 0x6be78f278963cd06, 0x1c889c6f75bef0b0, 0x447e02eeb6f3c206, 0xc223926846351133, 0xdfe9dee2da21042a, 0xbe3beb49840fbe87, 0x55593d58ed78d0da, 0xca09bf6fc4d8f98e, 0xc66f2b5875b9d8e0, 0xf45ec8c3cf4d3e10, 0x95e3e844110fddaf, 0xac854c8d3cf16f01, 0x8e70a052d00fae48, 0x2b622c13b299b283, 0xbca250d5559d4741, 0x4e45b9c1065e0332, 0xabff454d33f51188, 0x51244c52a18d4dca, 0x7a393f5d4b3bed54]

private theorem rounds73_1 : sixRounds 6 (by decide) quarter73_1 = quarter73_2 := by
  decide +kernel

private def quarter73_3 : Vector UInt64 25 :=
  #v[0x6b7020e6f8fef884, 0x2d02e1b18f437ecd, 0x48e8e80b2f05fef4, 0xa27146eb8f9985fd, 0xd47b62ec711cebdb, 0xce2a7cb82b45fc8f, 0xab1a4767d0c8bb83, 0x5c96f4ecdcb63b48, 0x6243a78dc87e5da6, 0x986bcbda0fa137de, 0x47f1b439da660d74, 0xba140ec430e9f9c1, 0x6d5839dc07148c5c, 0x3bc67f4310e08e73, 0xbff30082823c2180, 0x609bc07978c2a1ea, 0x59a6d23e8bb0a3c, 0x5631073fe4411bd4, 0xd467980ecc666877, 0x13ce2643bc5233b6, 0x46955485a280c0f4, 0xc3684b41a5b04038, 0x49cfad28c392fdd9, 0xc7291cefafa65589, 0x5e626f3783912e7d]

private theorem rounds73_2 : sixRounds 12 (by decide) quarter73_2 = quarter73_3 := by
  decide +kernel

private theorem rounds73_3 : sixRounds 18 (by decide) quarter73_3 = state74 := by
  decide +kernel

private theorem perm73 : KECCAK.f1600 absorbed73 = state74 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds73_0, rounds73_1, rounds73_2, rounds73_3]
  rfl

theorem block73 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes73 ++ tail) state73 =
      KECCAK.Bytes.run 0 tail state74 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes73 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb73 ws)) := by
    rfl
  exact (step state73).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words73).trans perm73))

private def absorb74 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x73 0x88 0x0 0x60 0x9 0x60 0x84 0xfa)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x16 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x0 0x60 0x1 0x20 0x60 0x52 0x81 0x90)) 8 (by decide) (UInt64.ofBytes 0x90 0x91 0x90 0x2b 0x2e 0x61 0x54 0x20)) 9 (by decide) (UInt64.ofBytes 0x5b 0x56 0x16 0xff 0xff 0xff 0xff 0x63)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x87 0x0 0x60 0x9 0x60)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x16 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x81 0x90 0x1 0x20 0x60 0x52 0x81 0x16))

private def absorbed74 : Vector UInt64 25 :=
  #v[0xcc000596a31236f8, 0xe05dad5358305efe, 0x5fe50e69d58126c5, 0xa6abc1d698ceb917, 0xd82ececb735b7b9e, 0xaba6dbd9b59ba0d4, 0xb6dfe2ea573857df, 0x81d00088360918c7, 0x469c6fa2bfc49f60, 0x642069c5fb8d67bb, 0xde53a4b05f07d6cb, 0xf37b3a6ffa8e2a3b, 0xb300c6a1ee1f4e2f, 0x280445568003843e, 0x44acddd7ea7556da, 0x8ee61c18415df456, 0xf9bcf4ee4ba30aa3, 0x130d34cb11a73c9, 0xc18f8ca96a21944d, 0x112689c453a1c5d3, 0x3fe143b2d82174f9, 0xf6f5ce132574b29f, 0xc0898fb6afb71f27, 0x94c74fb27d2acb0b, 0x696f4e2f5828c8a1]

private theorem words74 : absorb74 state74 = absorbed74 := by
  decide +kernel

private def quarter74_1 : Vector UInt64 25 :=
  #v[0x444b1b4656c11334, 0x1add5dfbbf876e21, 0x14efca247c099bc6, 0xc5d0a581e4752935, 0xf77177414f5066f1, 0xc4191cfe796ec272, 0xbf218fc14b95b0b2, 0xa3788f6a632322dc, 0x8b8ccd8fa2492825, 0xb315ed339aaaaf0f, 0xd132d489db5460da, 0xcb7a535f66ee4d08, 0x8f23230e78ac15e0, 0x540bd7dcc914ffab, 0xec8c5cc0607cbbfc, 0x30816a14e0c9f3e8, 0x389dd8d3654de7a2, 0xbea4cb1f6c14626e, 0x784e2df65964c69b, 0xa6e332c5f399d237, 0x161e45adc23f7dee, 0x9eb7b10fd6b94b2a, 0x903cf1ff2e5aa84e, 0x4969a0bcf7de7019, 0xa5636c24bd5388e5]

private theorem rounds74_0 : sixRounds 0 (by decide) absorbed74 = quarter74_1 := by
  decide +kernel

private def quarter74_2 : Vector UInt64 25 :=
  #v[0x591ff2a4fac28632, 0x19b6c9872fb4c070, 0x4807f29e59053487, 0x7ce40f5da92860ad, 0xb433f300c7323d19, 0xc2660f6fefa2e9e2, 0xde71894aac658054, 0x54a34f8db2d05cba, 0xb34b1ddd65339158, 0xcb379fdac8bdc91e, 0x5eed27b5a06aa99e, 0x27f40d447d2eabc3, 0xba221ab3b28d5281, 0xb801e1bd9c87a418, 0xf68d97c3c1a0418e, 0x29157e4a43ae9224, 0x841c1d1ea50fa3c5, 0xc25f9fff73429cb8, 0x3755c118ce433489, 0xf046a0ded735b3ac, 0x18f51d41a8d13106, 0x466c3202a0d727b7, 0xe9d16ac23def8c55, 0xb345265517b35eff, 0x8ac8b9f0861e329f]

private theorem rounds74_1 : sixRounds 6 (by decide) quarter74_1 = quarter74_2 := by
  decide +kernel

private def quarter74_3 : Vector UInt64 25 :=
  #v[0x574636fdc8243d98, 0x5e3ff685ede711b5, 0x8052ad0689b8e42a, 0x26628f725ed6131e, 0x75c12e1ecbca61f0, 0x59841f53dcbe3a97, 0x8b67974f4a2a6678, 0x404ff0dd818bea7f, 0xe77661b8d2b2fe2c, 0xec6c2d6652ef7be3, 0x42b9224aafceb45a, 0x612d5f28d502fa18, 0x1c0195b71879dc0b, 0xcef466769d105fb7, 0xae04224e312a2065, 0x75554988aecea911, 0xc8eae3a70756a7d2, 0x93c29ff21fa90496, 0x1e7fad5607815119, 0x6d3a1513545c633e, 0x2fe89c80f44458e3, 0xf0d6904f4dad3d73, 0x3e54e391eeca3d7e, 0x5132252d63256656, 0x7405910efe1bc775]

private theorem rounds74_2 : sixRounds 12 (by decide) quarter74_2 = quarter74_3 := by
  decide +kernel

private theorem rounds74_3 : sixRounds 18 (by decide) quarter74_3 = state75 := by
  decide +kernel

private theorem perm74 : KECCAK.f1600 absorbed74 = state75 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds74_0, rounds74_1, rounds74_2, rounds74_3]
  rfl

theorem block74 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes74 ++ tail) state74 =
      KECCAK.Bytes.run 0 tail state75 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes74 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb74 ws)) := by
    rfl
  exact (step state74).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words74).trans perm74))

private def absorb75 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x20 0x0 0x60 0x1 0x20 0x60 0x52)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x84 0x50 0x55 0x90)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x33 0x16 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xe2 0x1b 0xad 0x52 0xf2 0xdd 0x7f 0x16)) 8 (by decide) (UInt64.ofBytes 0x37 0xfc 0x68 0xb0 0xc2 0x69 0x9b 0xc8)) 9 (by decide) (UInt64.ofBytes 0xc4 0x63 0xf1 0xa7 0x2b 0x95 0xaa 0x8d)) 10 (by decide) (UInt64.ofBytes 0x23 0xf5 0x4d 0x5a 0xf5 0x28 0x16 0xa1)) 11 (by decide) (UInt64.ofBytes 0x82 0x80 0x51 0x40 0x60 0x86 0xef 0xb3)) 12 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x20 0x60 0x52 0x81)) 13 (by decide) (UInt64.ofBytes 0xa3 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 14 (by decide) (UInt64.ofBytes 0x91 0x92 0x50 0x50 0x50 0x92 0x1 0x60)) 15 (by decide) (UInt64.ofBytes 0x61 0xb6 0x27 0x61 0x5b 0x56 0x50 0x50)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0x56 0xbe 0x23))

private def absorbed75 : Vector UInt64 25 :=
  #v[0x3c30d97cf8f9fec1, 0x9cc5be3ce46bfe2c, 0x8e638d6cd85789d2, 0x48783bcda6efaff0, 0x6f74b39c92c06306, 0xf05d977e2605295f, 0x7dfb58cbf1193396, 0xdd2d914ec4228ef3, 0x8df94a4a4bed83ad, 0x9372c95143e2233, 0x608cc5aaf035a506, 0xe2d1554dc434ad52, 0xd72a03e6d190a4ec, 0xf44e112d532ff474, 0x31915f9a7c15a68a, 0xb72713933b196af0, 0xfe7ffa7c5bde37a7, 0x46b3f7af15741ad5, 0xcbeea9d07e6c3489, 0x1dc9fa12c8fff13d, 0x4b075d493f4f30ee, 0xe3e13d75697eec1a, 0xa8db01331b7afd46, 0x621e9e6e4f7a0501, 0x1835d33430bcb62f]

private theorem words75 : absorb75 state75 = absorbed75 := by
  decide +kernel

private def quarter75_1 : Vector UInt64 25 :=
  #v[0x6e77bf8968085f95, 0x32a055e9aea29512, 0x17379daab02e5ec2, 0xe57fe56277631015, 0x54b6dcf003864db9, 0xea334be6ac2ee91e, 0x6fc77dfbc7fca922, 0x57afcd47efb37878, 0x18fc12f405727df3, 0x619e0bfac8835309, 0x4a8a667a69245153, 0x12d0203b1f7749a9, 0x30f7420d49855e50, 0x4c429627180fefd6, 0xc2fe493e8351ba3f, 0x3ea3432b59182065, 0xf784fae617501a81, 0xd15d3f724b85c2f7, 0xfe785fb0eb0230f4, 0x6f7fbd8fefbeaae1, 0xe60c5a559cf20bec, 0x613a6b34095485ab, 0xd578a64d713d438b, 0x4bc97b821a9ec602, 0x1b24150631a8a64b]

private theorem rounds75_0 : sixRounds 0 (by decide) absorbed75 = quarter75_1 := by
  decide +kernel

private def quarter75_2 : Vector UInt64 25 :=
  #v[0x1690cc7c34da0af8, 0x77f1f60edce94db8, 0xd095964b6df97dcb, 0x6aba78962ed13a5b, 0x5fa7aebd583f41e9, 0x7aa0cf62babec0a2, 0x4c21b84ff467d95b, 0x5c5590492e2ba7a3, 0x34879e3196e3eb69, 0x85e65e3a453514f8, 0xbdf71f86f63a6e6a, 0x24510a366045608, 0x8783c2bfd08f69ed, 0x747a2514a709a8c0, 0xb23c39840c16688, 0x69f1d9f80cfad0da, 0xfcd845bda9483640, 0x8644710a1adbebc6, 0x1a634b1a97a3459b, 0x84ccaddc2fc7510f, 0x21bd4aaa31ec8f9d, 0x11e8cd836b9693c1, 0x3d577a5f17150a64, 0xb390d3de35363d75, 0xb3f8448520bae02a]

private theorem rounds75_1 : sixRounds 6 (by decide) quarter75_1 = quarter75_2 := by
  decide +kernel

private def quarter75_3 : Vector UInt64 25 :=
  #v[0xa24073231b1a2275, 0xae4a37b6ad7c94a8, 0xf16810ea2bd7eaf1, 0xa068f1e12e9cfefb, 0x887a422ddbcad270, 0x4f199bf3196e141d, 0x2b0f12dbd80033dc, 0x3428f5e990888e19, 0xf34d41be0a8c7f46, 0x5d2945d6d46bd275, 0xeaba22466af323b9, 0xb0ba180fe13e6dcd, 0xdb902c817f0c7ee7, 0x186a9baac8bbb222, 0x52157f60e17feafc, 0x6331e934fc26a03, 0x96ef01f6be0ec245, 0x9ab36850a7c870a0, 0x577bc8acbfbc18fc, 0x4f77c0330189e645, 0x293192149f6ae02f, 0xd94373cd40cddfbd, 0x680c252e520682fa, 0x416cba150db9cdb0, 0xa4194f574a13e862]

private theorem rounds75_2 : sixRounds 12 (by decide) quarter75_2 = quarter75_3 := by
  decide +kernel

private theorem rounds75_3 : sixRounds 18 (by decide) quarter75_3 = state76 := by
  decide +kernel

private theorem perm75 : KECCAK.f1600 absorbed75 = state76 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds75_0, rounds75_1, rounds75_2, rounds75_3]
  rfl

theorem block75 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes75 ++ tail) state75 =
      KECCAK.Bytes.run 0 tail state76 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes75 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb75 ws)) := by
    rfl
  exact (step state75).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words75).trans perm75))

private def absorb76 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x33 0x16 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x57 0xef 0x27 0x61 0x15 0x15 0x14 0x16)) 6 (by decide) (UInt64.ofBytes 0x73 0x0 0x60 0x5b 0xfd 0x80 0x0 0x60)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0x73 0x81 0x16 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x15 0x15 0x15 0x14 0x16 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x2b 0x28 0x61)) 14 (by decide) (UInt64.ofBytes 0x1 0x61 0x0 0x60 0x8 0x60 0x80 0x5b)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x81 0x54 0x81 0xa 0x0)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed76 : Vector UInt64 25 :=
  #v[0xa90396a78c90025a, 0x3f5c08699fb71849, 0x42c405dd4afad450, 0xc4fb86088e4aecb1, 0xddc24c7ebbc2aec4, 0x326a1f5e31be4d4c, 0x3359ff27b3952272, 0xcee5979c06723c2c, 0x268dbdf5f11c99e, 0x907f14cf390929b9, 0x5f44fb776f6762bb, 0xd3751aec554372af, 0xa36b7d5697d5b04, 0xda29dcaeb8661627, 0xdb35a36b91357c83, 0x15e5ef45c4af125, 0xbec9570d94a386dd, 0x69b98f947534a3e9, 0x7e053ed94f70c9e9, 0xb69777a23688289c, 0x817ae8832fa56891, 0xd1f0dacfdcb140ec, 0x65323cd4111dba21, 0x242ded2149e6c34e, 0x689526856edd0015]

private theorem words76 : absorb76 state76 = absorbed76 := by
  decide +kernel

private def quarter76_1 : Vector UInt64 25 :=
  #v[0xff64be54c234efc5, 0x9e7fbc84fe3998b1, 0x8d77c0095693e5df, 0x5dddbcf7cb6d360f, 0xd810325750d09bbc, 0xce5d12549250f775, 0xac32e91a90dbfa67, 0xa49333876252545f, 0x1ddfc24fafe29db6, 0x6966bba0d4c81b3d, 0x74f33b865ab72c1f, 0x8672002023bdcfa, 0x26add41778972f59, 0x44bd72ef2b623711, 0xc1eeb1c2c7022fba, 0xe30ec7a1e1ca8bb3, 0xe4b0bb0fcc2b4356, 0xc909986d006d8a71, 0x421485a824c31c19, 0xabd96cd40289faf, 0x9db3b3ec58181524, 0xe5967fe009d3a819, 0x53e3467b384c6c3f, 0x87c71c2e7c8d43c6, 0xe5cb025dbbbf4116]

private theorem rounds76_0 : sixRounds 0 (by decide) absorbed76 = quarter76_1 := by
  decide +kernel

private def quarter76_2 : Vector UInt64 25 :=
  #v[0xf8fca327a8a964a0, 0x33f53131941c7884, 0x7c8b3070987bfc15, 0x9e567867afdace53, 0xb415f4e3886c888d, 0xb22cfe718b73a801, 0x79cf2828efa2c5fa, 0xba7192b1d70ac4aa, 0x194006ff523e0b1e, 0xdb0f09fa52fc9bfe, 0x8fdcabd7bce6deb0, 0x5d68e15ed977b0d5, 0xb247381dec00c7f4, 0xc81f8db7b0849c1d, 0x3ff2866a19545788, 0xa1af309f72474c69, 0x812cb84ac06d90ab, 0x4f8fd9c0a932f619, 0x2dd053255f456507, 0xd549143c1418fe3, 0x37f07ace45d1ee12, 0x34e07472738949db, 0xfe355e78ea84c4ef, 0x9bd2ffb6fa1a0d20, 0x90dfdbad54c68ec3]

private theorem rounds76_1 : sixRounds 6 (by decide) quarter76_1 = quarter76_2 := by
  decide +kernel

private def quarter76_3 : Vector UInt64 25 :=
  #v[0x22f1206ae92c714b, 0xa787d5af8500c27a, 0x2797470ac3507f42, 0xc8cb21d997fea5b6, 0x7f95ea367e5a9f3a, 0xdff81f3df6c423df, 0xe518faa4e0db784a, 0xca53bfe4fb24a7e6, 0x6b33e0a41323c6c6, 0x97fd4b8bc16218b5, 0x5f2bace67ac331e, 0x8d03bbf2d34a1c7d, 0xc40b11d772aaba49, 0x60ede1bcdc2a5ae6, 0x2b788269d786720a, 0xb0ab27e0d04eb5ee, 0x3fef9ee20ab79cc9, 0x92ac89ae545428d0, 0xedc1c1d802c58f85, 0x71a4f91be286cbff, 0x89f4e9bd5e6adba4, 0x8a38f2dc051dbe70, 0x2c5c81440cd56127, 0xe3c00543a31f3078, 0xc7819a1e06ad5ee5]

private theorem rounds76_2 : sixRounds 12 (by decide) quarter76_2 = quarter76_3 := by
  decide +kernel

private theorem rounds76_3 : sixRounds 18 (by decide) quarter76_3 = state77 := by
  decide +kernel

private theorem perm76 : KECCAK.f1600 absorbed76 = state77 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds76_0, rounds76_1, rounds76_2, rounds76_3]
  rfl

theorem block76 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes76 ++ tail) state76 =
      KECCAK.Bytes.run 0 tail state77 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes76 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb76 ws)) := by
    rfl
  exact (step state76).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words76).trans perm76))

private def absorb77 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x73 0x83 0x90 0x16 0x19 0x2 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x90 0x17 0x2 0x16 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x54 0x90 0x0 0x60 0x8 0x60 0x50 0x55)) 6 (by decide) (UInt64.ofBytes 0x73 0x4 0x90 0xa 0x0 0x1 0x61 0x90)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xa9 0xdf 0x66 0xdb 0x7f 0x16 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xc7 0xaa 0xe9 0x6f 0x22 0xf5 0xb8 0xc6)) 14 (by decide) (UInt64.ofBytes 0xc3 0x4a 0xe9 0x8e 0xae 0x97 0x18 0xe5)) 15 (by decide) (UInt64.ofBytes 0x25 0xb 0x90 0xc9 0xb6 0xb 0xc7 0x1d)) 16 (by decide) (UInt64.ofBytes 0x60 0x51 0x40 0x60 0xe6 0x7 0xb7 0x74))

private def absorbed77 : Vector UInt64 25 :=
  #v[0x4cb7d4dc68b3de17, 0x79eaddaa6afb3a3c, 0xb7fc171d2894b9da, 0x4f414be96bfa1bfe, 0x45a78e03e99d1e9f, 0x26e029679d3aafc9, 0x70a3ffb706ae0b, 0x88a2abda2814f781, 0xa4c5a8af78fa6ac, 0x5eb1714aa813d917, 0x990887eeb6b75d04, 0xe8d1caef8142d520, 0x800f11e6952053da, 0x3758e46b52fd6fde, 0x7ba70dd35e105947, 0x89ff1f268c219e16, 0xb9bd470d2fbe670b, 0x44ae1bd43cfb7d1f, 0x15fc59bc39925dde, 0xd6b9243f664376f2, 0x1bd7d503978e1b05, 0xdc00b03ad6658761, 0x6186e8c7ca1f3e9d, 0xcdbc929f2eb2eded, 0x9414c013ed6d7f8b]

private theorem words77 : absorb77 state77 = absorbed77 := by
  decide +kernel

private def quarter77_1 : Vector UInt64 25 :=
  #v[0xaa10e925f90dbe6, 0x77ec01f667f1d46, 0x4c5d194238c8260c, 0xe57f49eb207339ae, 0x519c935331192a9b, 0xf54e2ce1e869e4b4, 0x389186288d7464de, 0x9481490f76fa110, 0x14346eaf8036523, 0x5ccce8569066aace, 0xb45519f243c0fbf8, 0xf26d8c0eaee9ed59, 0x1a517232c6b1ee1f, 0xb61e7397cb5e8213, 0x5104e24175c59995, 0x4b47d5ed09b9d665, 0xefed7ba8f572531e, 0xb43731d1633a9253, 0xc2934e9c25cbeb3b, 0xecbea76bdf38e89, 0xd70b38424da1fdd3, 0x9729e4404eccb116, 0x9450dd11fbd659fc, 0x48a8fc732f7dbb57, 0xed8de966d064748d]

private theorem rounds77_0 : sixRounds 0 (by decide) absorbed77 = quarter77_1 := by
  decide +kernel

private def quarter77_2 : Vector UInt64 25 :=
  #v[0xc328e264e8719cc4, 0xc508af13a5ca09cb, 0xcd5fa75a24bd55cd, 0xa7dbd8c75b294c00, 0x8fc9928342ae2753, 0x5ef573aaa38d5142, 0xee2a707ae555b841, 0x44af149165c3d6be, 0xe18432c876e0cb8f, 0x75405d8b27228a21, 0x9fc3ece1d472b318, 0xed465e91dbf73c71, 0x19ce569f68574e58, 0xedfa114af1ff5b98, 0x1210bbfd6464e96b, 0xd1864e2b7f49ee5b, 0x38bf0a0312f258e7, 0x39f2d7c4775786df, 0x3b823b877d665c62, 0x3520c54e0c5ce5ef, 0x4978c6a07887597a, 0xa16c4ad37567e1ed, 0xe38c493a30145c59, 0x9b5c80530ebbb2ab, 0x75aec515e7aec8d1]

private theorem rounds77_1 : sixRounds 6 (by decide) quarter77_1 = quarter77_2 := by
  decide +kernel

private def quarter77_3 : Vector UInt64 25 :=
  #v[0x3eb1450e23f11d48, 0x5af7c0b981e6a9b8, 0x55247a89736b3a47, 0x5418d8fccf0056d0, 0xef7470978551162d, 0xb94275add58f73aa, 0x4839c213f9c167ee, 0xdff17b6b1a19e035, 0x9641fe7b2da8656, 0xa3d501e30940866d, 0xf0fbe5af8aa9e2bf, 0x92565ffccb661f9a, 0xee3646662dcb9f29, 0x524c98a056b30be9, 0xf526f70d068363df, 0x1196620117d3171f, 0x21bbdc8fc98d641f, 0xa9f67d34843829e1, 0x69548ddc99e086db, 0x8e70dda0ff1c9752, 0x77c030e2dc8c9112, 0xdd9d2fe0f45d82b7, 0x1bd7023b1e75dd9f, 0x630e95d43c2f84ee, 0x4f58f53078938001]

private theorem rounds77_2 : sixRounds 12 (by decide) quarter77_2 = quarter77_3 := by
  decide +kernel

private theorem rounds77_3 : sixRounds 18 (by decide) quarter77_3 = state78 := by
  decide +kernel

private theorem perm77 : KECCAK.f1600 absorbed77 = state78 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds77_0, rounds77_1, rounds77_2, rounds77_3]
  rfl

theorem block77 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes77 ++ tail) state77 =
      KECCAK.Bytes.run 0 tail state78 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes77 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb77 ws)) := by
    rfl
  exact (step state77).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words77).trans perm77))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
