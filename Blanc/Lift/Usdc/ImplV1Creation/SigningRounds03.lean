import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb18 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x19 0x3 0xa 0x0 0x1 0x61 0x3 0x20)) 1 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x20 0x60 0x52 0x81 0x16)) 2 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x50 0x92 0x50 0x5b)) 3 (by decide) (UInt64.ofBytes 0x34 0x5b 0xf3 0x90 0x3 0x91 0x80 0x51)) 4 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x15 0x9 0x61 0x15 0x80)) 5 (by decide) (UInt64.ofBytes 0x61 0x1e 0x9 0x61 0x50 0x5b 0xfd 0x80)) 6 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x5b 0x56 0x85 0x24)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x82)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x20)) 14 (by decide) (UInt64.ofBytes 0x80 0x34 0x5b 0xf3 0x90 0x3 0x91 0x80)) 15 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x6c 0x9 0x61 0x15)) 16 (by decide) (UInt64.ofBytes 0x4 0x60 0xab 0x9 0x61 0x50 0x5b 0xfd))

private def absorbed18 : Vector UInt64 25 :=
  #v[0xe04b7f6615916f7a, 0xdf202899d1682ef7, 0x68a49d7d63f914dd, 0x2d5c7aa048e0ea61, 0xedad0a8e170e6fa4, 0x7ac4eb1b6ecf567d, 0xa1329114024e0e73, 0x464434a1c74e8034, 0x9a766b7228d664e2, 0xd5fc888064fe77b6, 0xbc37a0aa9d0daad5, 0x787c88897bf03b34, 0x4ac272914a6bf032, 0x469568c549a8c22e, 0xdad424d01d3f955d, 0x1e8f5f93a72d5083, 0x75ffb1e392cb0b5a, 0x987a68327e79c286, 0x9d50f13fcb057c80, 0xbd35678b67f1dc25, 0x1e20d57cc30357ec, 0x71a3c867c1a0cd8f, 0x2e7fc3c3dc05310f, 0xe5c38e5374fe9e92, 0x5d88e0aec2b1728a]

private theorem words18 : absorb18 state18 = absorbed18 := by
  decide +kernel

private def quarter18_1 : Vector UInt64 25 :=
  #v[0xc430e18bd41a3ee7, 0x59d2c2c983c046ff, 0xedeb771f3f5ce402, 0x7d30fe84bd432785, 0xa7d0dc2f4f823d9d, 0xbbfc45729d0a2146, 0xd63f27c0b11e7fe1, 0x11888da63e3379b, 0x1a18f2ec4837f230, 0x54bb9764a75d11f7, 0x52aff7e95b5abc1f, 0xb92a63043fea2f32, 0x538e5b128db58090, 0xf20fe41ccc29c4bf, 0x540f98a4c8379870, 0xec7cb06f0daccb74, 0xa87e52f375f0408b, 0xe4e4b6de1cae6504, 0x9015c0a127c10014, 0x47897eea11f2e153, 0xa1e7211bce4f5031, 0xc8a3d7555103ef76, 0xc6da951ad7f1ef14, 0x80a3574bc458fca4, 0x74c6767c9c6084a1]

private theorem rounds18_0 : sixRounds 0 (by decide) absorbed18 = quarter18_1 := by
  decide +kernel

private def quarter18_2 : Vector UInt64 25 :=
  #v[0x588669e803f17877, 0x8b8a66cd8049ef53, 0x14c46a9a3e858a5a, 0xd8a76ad24abc70c0, 0xde5ee032807f1cc1, 0xbf9959525ebde1cc, 0x7a2233cfc0575674, 0xf884beab954af087, 0xda609c4dd3f8ac57, 0x4388a5b20100dac7, 0xfd956ff13d846e76, 0x18c693adcbf5b08c, 0xa979379620b5f6c8, 0x211b26b7a956ae34, 0x230d8c10a81407af, 0x62ee2d7e8d288824, 0xea0c20e9c364e766, 0x26fa22d292d46641, 0x2365299c1ba4e227, 0x997fcef7a1de7e8c, 0x22f254b6a4f811b8, 0x657c5e3de4d6876b, 0x357938a32c17cbef, 0xce70228fa228e846, 0xaaeb5d4088e575ad]

private theorem rounds18_1 : sixRounds 6 (by decide) quarter18_1 = quarter18_2 := by
  decide +kernel

private def quarter18_3 : Vector UInt64 25 :=
  #v[0xff50bf8091db4dbb, 0x7abb31227cb14e69, 0x4646433b29af3ba2, 0xb85b529c9cdbb162, 0x2a5041e00f0f17be, 0x3f256f7a19089b9d, 0x2ffc2749dd6a8750, 0xbc56334f4e5a2b6e, 0x448a2bf31de3a6d8, 0x9e26ea4a17be9c15, 0x21fc526017db1a7f, 0xf7bd4796057af7d5, 0xfbaa917148196114, 0x5c1feb42faf05fe1, 0x5b3e58e14179524, 0xfeb708519de9e81c, 0x79b16cec9e5c4be5, 0x502676d3f0ffcb86, 0x46186085b97d0c5f, 0x5082e9d2ca201e13, 0xac3437005af3579d, 0x491f1f362dd3fe58, 0x114c1e62db7f1ffa, 0x13cc72ff2f2aeba0, 0x47317bf182092cdf]

private theorem rounds18_2 : sixRounds 12 (by decide) quarter18_2 = quarter18_3 := by
  decide +kernel

private theorem rounds18_3 : sixRounds 18 (by decide) quarter18_3 = state19 := by
  decide +kernel

private theorem perm18 : KECCAK.f1600 absorbed18 = state19 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds18_0, rounds18_1, rounds18_2, rounds18_3]
  rfl

theorem block18 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes18 ++ tail) state18 =
      KECCAK.Bytes.run 0 tail state19 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes18 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb18 ws)) := by
    rfl
  exact (step state18).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words18).trans perm18))

private def absorb19 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x80 0x80 0x90 0x1 0x81 0x3 0x36 0x80)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x35)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x90 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x80 0x90 0x91 0x92 0x90 0x1 0x20 0x60)) 5 (by decide) (UInt64.ofBytes 0x91 0x92 0x90 0x1 0x20 0x60 0x90 0x35)) 6 (by decide) (UInt64.ofBytes 0x56 0xab 0x24 0x61 0x50 0x50 0x50 0x90)) 7 (by decide) (UInt64.ofBytes 0x15 0x15 0x82 0x80 0x51 0x40 0x60 0x5b)) 8 (by decide) (UInt64.ofBytes 0x91 0x1 0x20 0x60 0x52 0x81 0x15 0x15)) 9 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 10 (by decide) (UInt64.ofBytes 0x9 0x61 0x15 0x80 0x34 0x5b 0xf3 0x90)) 11 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0xd1)) 12 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x6 0xa 0x61)) 13 (by decide) (UInt64.ofBytes 0xff 0x73 0x35 0x80 0x80 0x90 0x1 0x81)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x16 0xff 0xff 0xff))

private def absorbed19 : Vector UInt64 25 :=
  #v[0x4f7375b09051198b, 0x8501f6edc77fa311, 0xf76e08260eaf343e, 0xbecf5547a52ecbda, 0x478d4097d6672888, 0x33621f671dfdd7b9, 0xca3e4ef7051bff1a, 0x2288b493c9fb0134, 0x77a828ec8c086473, 0x5609cad8278127d9, 0x3a9316d5b6fac7cd, 0xffdca054ca0646cb, 0x6e22d42e72304ace, 0x594518074ec89876, 0x5dc25e0237e7c755, 0x63493437e56371f4, 0xc50ce660cf45ae3, 0x61971dad5f124a9d, 0x366d44ad4de89c7c, 0x4539182bcc174a2e, 0x6234e777f17d6811, 0x7aece2146af2b377, 0x1cd17fb4e3608f77, 0x8883ad62d97698b5, 0xfd5dda42cf6394c2]

private theorem words19 : absorb19 state19 = absorbed19 := by
  decide +kernel

private def quarter19_1 : Vector UInt64 25 :=
  #v[0x969792ba93cd1b92, 0xb27326e26d0cf75c, 0xf4c0df9ae3b6e123, 0x95589b89f9ec195d, 0x3bd4f4bd1826be2e, 0x23b814871d846847, 0x548a627cfb198756, 0x2a2f67c944aaf401, 0xc2706a58f75a3397, 0x5f3995dc23cfd392, 0x6a753b3747878049, 0x60eddc17cbd718f1, 0xd34ff73f347fb135, 0x13dafc3ed0a47281, 0x5e246b2269f526b9, 0xc96a35f78b6ac061, 0xbc5ea77d9f9fe4f9, 0x3d77eb310d2f6c46, 0x4c225830d9dc0613, 0x98a413bf860c60f4, 0xe3f9969627e4c03e, 0x72a258532f4c1abb, 0x9f9f5f81c51e81f, 0x58c97e39b9fde417, 0x5c0a1020d4736e65]

private theorem rounds19_0 : sixRounds 0 (by decide) absorbed19 = quarter19_1 := by
  decide +kernel

private def quarter19_2 : Vector UInt64 25 :=
  #v[0xf6c101498f7d012b, 0x1a0db68ce2832c23, 0xcca2d3c0afc6ae78, 0x8c95839ac945f47a, 0x3dd1ceb4856273d0, 0x98bda49dfcaa68c3, 0x883a1335973271ca, 0xf5130fee34a7ae5e, 0xbe025eac63e6b40f, 0x5b5548a3967bfa76, 0x45567520881b1818, 0x894c917a11366048, 0xb2af6ae0d99c4776, 0xb0cfc42daab0d5e6, 0x97e69e97499ac396, 0x41ec7154fff076fe, 0x6c2d9b06e6e1a2c9, 0x632aa94da7059a63, 0xe2083389ef8b4ac, 0xcd023f87c800b4b3, 0xd3ef45371d1b9d6e, 0x17c65af9af0a463d, 0xd54697a7b6243552, 0x401ba099eca2125, 0x3da9a06227cbf8af]

private theorem rounds19_1 : sixRounds 6 (by decide) quarter19_1 = quarter19_2 := by
  decide +kernel

private def quarter19_3 : Vector UInt64 25 :=
  #v[0xd40ce1e9328b08c7, 0x3ece1e597e471b3f, 0x99457d75705f7654, 0x97ae67e7d4b77297, 0x5297369a4dd2a0a8, 0xb13c524dc6e7b1b, 0x56299e21128ee058, 0x5343ccd147720aed, 0x709e8d4ef7c38bc8, 0xe6f90f8ecf71c2e0, 0x1d052029fd00fcc0, 0x35f3285b4ab63fa0, 0x13f18c1b6f60188b, 0xfa4bdeadf2e3297a, 0xfa90af384585fc97, 0x3d2f73ec274423fb, 0x4b4176b4496189e0, 0xbdb7a61175485a1b, 0x20e1ddf6ef89aa2d, 0x5f48478290bc471c, 0x83c41b5ddeae8b82, 0x41ec1f64bf300ece, 0x519ffa494eb7234c, 0x7f3902591eaf9d89, 0x62193499e72aa959]

private theorem rounds19_2 : sixRounds 12 (by decide) quarter19_2 = quarter19_3 := by
  decide +kernel

private theorem rounds19_3 : sixRounds 18 (by decide) quarter19_3 = state20 := by
  decide +kernel

private theorem perm19 : KECCAK.f1600 absorbed19 = state20 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds19_0, rounds19_1, rounds19_2, rounds19_3]
  rfl

theorem block19 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes19 ++ tail) state19 =
      KECCAK.Bytes.run 0 tail state20 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes19 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb19 ws)) := by
    rfl
  exact (step state19).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words19).trans perm19))

private def absorb20 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x61 0x50 0x50 0x50 0x90 0x91 0x92 0x90)) 1 (by decide) (UInt64.ofBytes 0x80 0x34 0x5b 0x0 0x5b 0x56 0xae 0x27)) 2 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x14 0xa 0x61 0x15)) 3 (by decide) (UInt64.ofBytes 0x4 0x60 0x49 0xa 0x61 0x50 0x5b 0xfd)) 4 (by decide) (UInt64.ofBytes 0x80 0x80 0x90 0x1 0x81 0x3 0x36 0x80)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x35)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x90 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x50 0x90 0x91 0x92 0x90 0x1 0x20 0x60)) 9 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0xd4 0x28 0x61 0x50 0x50)) 10 (by decide) (UInt64.ofBytes 0x15 0x15 0x15 0x15 0x82 0x80 0x51 0x40)) 11 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x20 0x60 0x52 0x81)) 12 (by decide) (UInt64.ofBytes 0xf3 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 13 (by decide) (UInt64.ofBytes 0x57 0x6f 0xa 0x61 0x15 0x80 0x34 0x5b)) 14 (by decide) (UInt64.ofBytes 0xa 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60)) 15 (by decide) (UInt64.ofBytes 0x1 0x81 0x3 0x36 0x80 0x4 0x60 0xa4)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x80 0x80 0x90))

private def absorbed20 : Vector UInt64 25 :=
  #v[0xf43817ce29908da5, 0x8aecf399caa32bd9, 0x72a24600c277f96a, 0x7d5c254cdbb67901, 0xaa560aabc5a84f40, 0x59901ed580354eee, 0x6d831f26112fb718, 0xd1b04267af686cc4, 0x69783015d57203a, 0x56a289fc8b3b8580, 0x7db4ec3ccb4a6a76, 0xe15b391cbcdf135a, 0xe6cea027bebf6f6a, 0xec9bb4ea2048b925, 0x84e322ba0cf3d7a4, 0x95b1351118d8dcc0, 0xd8ccb7f15f6b3e37, 0xece0cc93db776aac, 0xf107c2111336eb4d, 0x14f07e4be6a28a72, 0x528dbda318b454a9, 0xb7d5def934af8032, 0x858e331d15de9ea0, 0x13f9b08935d35c6c, 0x1a4419c2ecc2ff14]

private theorem words20 : absorb20 state20 = absorbed20 := by
  decide +kernel

private def quarter20_1 : Vector UInt64 25 :=
  #v[0x656c9c688ca5ff49, 0x9dfef2d2b7808b2b, 0x2c68b24c1d1a4612, 0x1619d0e28b9d617b, 0xb7373c4895eadb5b, 0xd1907bd76b8e620, 0xb67f8dc01ca94450, 0xf3597c2221ec23f, 0xd98e6b8cc36cae9e, 0xfabc381e83dcf36d, 0xb15244d94216bc2e, 0x44ec0040d712333, 0x8db2c9387927a1d2, 0x33961f0aa27bedab, 0xed4cbb1f5acdcb46, 0xe966378a75a8d418, 0xf1cefa0189e0592, 0x1cb058207211506c, 0x967c26095789d8c, 0xe13d27830b8a91c, 0x9b0fc927a53013c3, 0x358a9bdc28e2057e, 0x9c0db8ef5c4f59c8, 0xa2df73f4821de1b, 0xd1626155a6072a3f]

private theorem rounds20_0 : sixRounds 0 (by decide) absorbed20 = quarter20_1 := by
  decide +kernel

private def quarter20_2 : Vector UInt64 25 :=
  #v[0x4b6f4081ff0c9db0, 0x42b60f2e02c34ce4, 0x1bfbecc4fba586fa, 0x13a487f8740acec4, 0x2f98a2c8e2c69144, 0x28030e87975462df, 0x7ffeb353e9dd20a, 0x6eaae6e4d42a7529, 0x429091f1a6aa3fb1, 0x1c67d84e14b38af1, 0xe01eabc8bd3a151c, 0xf1f26ed2b4712ee, 0x91e16a2484e622f6, 0x87af839ff8ee1a3d, 0xf541f2cddffa4b5c, 0xe4b1a180a054575d, 0x6802789c270a85c2, 0xc4fee87869b7c716, 0x8f930c97bacffbda, 0x6affc37b89c1428b, 0x212ad6ca1f8c127c, 0x78c060b24c8d5ae5, 0xfb04d639d84eb18b, 0x72e4a6c9b352c4b2, 0xd6ef642326258198]

private theorem rounds20_1 : sixRounds 6 (by decide) quarter20_1 = quarter20_2 := by
  decide +kernel

private def quarter20_3 : Vector UInt64 25 :=
  #v[0x27b43c8ece7a5c49, 0xb0556b8947d4ca45, 0xa25cf1eaed35e8b4, 0xe0c565c085af64c8, 0x688c940509c701a1, 0xdfcb58d461574543, 0x9865320437a6d694, 0x5d7f904eea5a34aa, 0xd9496a17a1ed8b40, 0xccd3887968de0b6, 0x48090097f27ada57, 0xadab5059e980a0dd, 0x5c61a878ab44f44c, 0x8fc26358b706dc10, 0x4605d4aef8c1a744, 0x20ee8adbb16e527b, 0xb6d322528ed54bc4, 0x897e27f65fe457d8, 0x30431ef39c3427eb, 0x55a31d6301692da6, 0x2861c62030b69f89, 0x5ab25fa04d220b0, 0x85040f9b5f50e1ff, 0xaa4a4b3254a997fd, 0xefd0fa4655e36c00]

private theorem rounds20_2 : sixRounds 12 (by decide) quarter20_2 = quarter20_3 := by
  decide +kernel

private theorem rounds20_3 : sixRounds 18 (by decide) quarter20_3 = state21 := by
  decide +kernel

private theorem perm20 : KECCAK.f1600 absorbed20 = state21 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds20_0, rounds20_1, rounds20_2, rounds20_3]
  rfl

theorem block20 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes20 ++ tail) state20 =
      KECCAK.Bytes.run 0 tail state21 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes20 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb20 ws)) := by
    rfl
  exact (step state20).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words20).trans perm20))

private def absorb21 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 3 (by decide) (UInt64.ofBytes 0x2a 0x29 0x61 0x50 0x50 0x50 0x90 0x91)) 4 (by decide) (UInt64.ofBytes 0x61 0x15 0x80 0x34 0x5b 0x0 0x5b 0x56)) 5 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0xb2 0xa)) 6 (by decide) (UInt64.ofBytes 0x56 0x50 0x2a 0x61 0xbb 0xa 0x61 0x50)) 7 (by decide) (UInt64.ofBytes 0xff 0x73 0x82 0x80 0x51 0x40 0x60 0x5b)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x91 0x1 0x20 0x60 0x52 0x81 0x16 0xff)) 14 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 15 (by decide) (UInt64.ofBytes 0xb 0x61 0x15 0x80 0x34 0x5b 0xf3 0x90)) 16 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0x9))

private def absorbed21 : Vector UInt64 25 :=
  #v[0x968c814ca46d6e90, 0xdb410a3567c67e16, 0xcd61bbc6401d80bf, 0x5d35a25d94d5a26d, 0x1e39762a910b6fd2, 0x2769b5a59e3f527c, 0x2a6d3f51a8aebd33, 0x84aefb58279d5dfe, 0x42f15af6a0cee5a3, 0xc134728b49f4fe63, 0xfdeb9c24f05e628c, 0x8d91ed557531e3bb, 0xcc6e8213eb9985c0, 0x1f101e7e55104c9a, 0x6fb2b09ae31e459a, 0xc096400cf2fb7255, 0x7066a3259370dfe1, 0x913139f1ad94804d, 0x4e9d95349fb524d6, 0xb529e5658ae3ed4b, 0x64209735d0e04a88, 0x79267bebbab58f94, 0x7461a714ac573cf3, 0x81443418d1a716f, 0x62fa501948384870]

private theorem words21 : absorb21 state21 = absorbed21 := by
  decide +kernel

private def quarter21_1 : Vector UInt64 25 :=
  #v[0x710c3d3e5c19f553, 0xb4a44f032f4c04a3, 0x9f8f391fc8301a92, 0x289a48d5ccc71c9b, 0x2da0544fb666a590, 0xfdf920b6b8883c2d, 0x7014f01971bced5, 0xbd47c0ea362e8cd6, 0x45a6495adf76124, 0x3ef0d7116f34c683, 0x29103d2122a00526, 0x9fe82b5f2586cbaa, 0xd27363028afc2e82, 0xc794ae7f9a587de0, 0x3937571032cafa1b, 0x6368e4744a5387c4, 0xdf25d2e5a30bc63b, 0xb6d09db5187dcf81, 0xb4c4b3d8db3c8339, 0xf8e7d8a0cfd7b2dd, 0x2aeb69a9dca996a1, 0x98e4dfea0752aee8, 0x5928019726068617, 0xfbd632f620d5f15f, 0xce3f242e966496d]

private theorem rounds21_0 : sixRounds 0 (by decide) absorbed21 = quarter21_1 := by
  decide +kernel

private def quarter21_2 : Vector UInt64 25 :=
  #v[0x2acd42360fdc634, 0x776a24a995c49239, 0x1bd4e15fbc733bc6, 0x33b876cccd6b8ff5, 0xdccdad6cbc790864, 0xfea2ae20985f404f, 0xa9b982f520a9750e, 0x4d49799182e41e92, 0x2c821080c2e59dd4, 0xea3e0b8a6bdb0782, 0xaae48a5eaa1ccb13, 0xf357886209a70d5e, 0x143b8d5be83d06e9, 0x38c9265fa5d1b8fc, 0x297ae2fd407cc010, 0xd843b82c7b196656, 0xa1e8dae6fadad421, 0xf8122d2540456a5c, 0xb529ddbb6e517d5d, 0x700abc33834b4360, 0x3c4352fac5392ec5, 0xe90685afc31a98f2, 0x737a1a479d961019, 0x3fa2822998f02b6b, 0x8e8c3d084b56982a]

private theorem rounds21_1 : sixRounds 6 (by decide) quarter21_1 = quarter21_2 := by
  decide +kernel

private def quarter21_3 : Vector UInt64 25 :=
  #v[0x9f75402c83d2f923, 0xee753b052048b3ee, 0xcb396395d52600f0, 0xb48207a1f8a3f176, 0x90dc5a7f921e6e60, 0xa686c87a2ab2ade2, 0x98a79762ef7d8528, 0x1ab495f248ea629e, 0x8e9c71dcc7d58fa2, 0xe3fc9f802647b11, 0x816f684a1a5210cb, 0x68fc817970136e44, 0xd38a13ba65ab8113, 0x3600d0387f2891f, 0xf1066b46cf0c71ed, 0x48a6756546c8fca4, 0xcd7841fd0fcb43a0, 0x3422fba3b0179c32, 0xe39fe90e69e858b9, 0x16d856e9e7c198f7, 0x56dc2abf809b8c64, 0xba116d5f83e56370, 0xc87ccb199a6373ee, 0xa35ad26cb0591d59, 0xbb123f05053f65af]

private theorem rounds21_2 : sixRounds 12 (by decide) quarter21_2 = quarter21_3 := by
  decide +kernel

private theorem rounds21_3 : sixRounds 18 (by decide) quarter21_3 = state22 := by
  decide +kernel

private theorem perm21 : KECCAK.f1600 absorbed21 = state22 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds21_0, rounds21_1, rounds21_2, rounds21_3]
  rfl

theorem block21 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes21 ++ tail) state21 =
      KECCAK.Bytes.run 0 tail state22 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes21 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb21 ws)) := by
    rfl
  exact (step state21).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words21).trans perm21))

private def absorb22 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x5e 0xb 0x61)) 1 (by decide) (UInt64.ofBytes 0xff 0x73 0x35 0x80 0x80 0x90 0x1 0x81)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x16 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0x73 0x35 0x80 0x90 0x91 0x92 0x90)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x16 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x61 0x50 0x50 0x50 0x90 0x91 0x92 0x90)) 10 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x5b 0x56 0x76 0x2a)) 11 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x20 0x60 0x52 0x81 0x82)) 12 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 13 (by decide) (UInt64.ofBytes 0x80 0xb 0x61 0x15 0x80 0x34 0x5b 0xf3)) 14 (by decide) (UInt64.ofBytes 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 15 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0xfd 0x2a 0x61 0x89 0xb)) 16 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x51 0x40))

private def absorbed22 : Vector UInt64 25 :=
  #v[0x91a61fa0168a78d4, 0xe147df7249d544e2, 0x89806a787a55959a, 0x444ba7db2d69697a, 0x2ef1c0ed8879df72, 0x8c707e7fd4a04a6, 0xd905b62fcdd6042f, 0x19049d727a490cb2, 0xb11f29279ce3c214, 0x151216a7b0bc61b6, 0x637aa040e7a391c2, 0x692eb68d36e23e2c, 0xf34a96cb228e899e, 0xd404c3db256de2b3, 0x346df5e7781216b4, 0x1d963e15d416fc03, 0xdaf674f63a6ec530, 0x1510cd66c27733bd, 0x586ba61430eccebc, 0x248d315a57038193, 0xcdf46134445d6986, 0xa92e38e7eabddbc4, 0x365a7c973f54dc45, 0xe06b1423594a98c7, 0x2a6150021e902a1e]

private theorem words22 : absorb22 state22 = absorbed22 := by
  decide +kernel

private def quarter22_1 : Vector UInt64 25 :=
  #v[0x25ad67eed52b63e, 0x96960372c995258b, 0x22e69ff5f58d8ef9, 0x6fa046615310b331, 0x1cff226692405f62, 0x6263d35a784184db, 0xef11152c7a8bb31d, 0x39dff370d755c55a, 0x9a2ed77ee90f300f, 0x85baac95a0e1b224, 0x507a665fc944c357, 0xcd529b44b94604f4, 0x1446c70b8049d627, 0x73313a0cc54cf844, 0x8b8ada04ddb4c983, 0x52863040ce4b5b98, 0x1953abd06ea3ec4f, 0x8148c4878d72a1d5, 0x634a49890598c22f, 0xe046d4467b6fcfc, 0x3f3c9181507c1453, 0x9881005701261e4c, 0x26d2c3adc2b0ca94, 0xd6ad654424330b7a, 0x6c33f159b7929dfd]

private theorem rounds22_0 : sixRounds 0 (by decide) absorbed22 = quarter22_1 := by
  decide +kernel

private def quarter22_2 : Vector UInt64 25 :=
  #v[0xe4a0f58219c094b2, 0xa3b6779a56d378b9, 0xa4098b978bcecd96, 0xae63ddfba5701542, 0x9808b32fbd72377b, 0x47b6ff9478880733, 0xcfacd9dc9787ffe3, 0x24322352bb5ba015, 0x9ebfb90436f2ba7b, 0x552f803a13bab6db, 0x68f862bfc6598ba, 0xd8130d7e27097111, 0xc053b5012692c4e5, 0xa9436c9ca4f54619, 0xfe88039515acfdfc, 0x7efd48195c416b61, 0xe3dafbff9a08ae96, 0x201463b72f68d3ff, 0xadd659238af29fb5, 0x3b0fc43278ebac1c, 0xb8047432be337db2, 0x81b0461e5ae4803b, 0x8c5c45f7d6bc25c9, 0xf989625daefa519a, 0xcba93d032fe933ff]

private theorem rounds22_1 : sixRounds 6 (by decide) quarter22_1 = quarter22_2 := by
  decide +kernel

private def quarter22_3 : Vector UInt64 25 :=
  #v[0x7060c2566502ce11, 0xb4d5852f7ef74881, 0xf6a5ed0b6d4afd25, 0x32484af61a76afc7, 0xe26efcbd009b1c86, 0x82760b5a18c1350d, 0x5a18c5e83f247e2d, 0x118005b24383ec37, 0xa0c548be42f06c32, 0x41448f171b30da6c, 0xe21729faa63cf0c5, 0xc3d2386b90035773, 0x6ce6cd068803026c, 0x865bdd5b16088d06, 0xa0be88b7d697a772, 0xffc9aea90b04236e, 0x2f33f128e15340d6, 0x1b8af9c8fc5b4ca6, 0x79b9e9453772bb01, 0x511118c6df6403a2, 0xb8c4492b0554aa73, 0x52d26d00136fcb20, 0x7b646e331f3ed697, 0x5b6c839bf56e370, 0x6bb1f6401c2ad440]

private theorem rounds22_2 : sixRounds 12 (by decide) quarter22_2 = quarter22_3 := by
  decide +kernel

private theorem rounds22_3 : sixRounds 18 (by decide) quarter22_3 = state23 := by
  decide +kernel

private theorem perm22 : KECCAK.f1600 absorbed22 = state23 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds22_0, rounds22_1, rounds22_2, rounds22_3]
  rfl

theorem block22 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes22 ++ tail) state22 =
      KECCAK.Bytes.run 0 tail state23 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes22 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb22 ws)) := by
    rfl
  exact (step state22).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words22).trans perm22))

private def absorb23 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x51 0x81 0x81 0x83 0x52 0x82 0x3 0x81)) 1 (by decide) (UInt64.ofBytes 0x80 0x50 0x91 0x1 0x20 0x60 0x52 0x81)) 2 (by decide) (UInt64.ofBytes 0x83 0x80 0x90 0x1 0x20 0x60 0x90 0x51)) 3 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x83 0x5b 0x0 0x60 0x83)) 4 (by decide) (UInt64.ofBytes 0x51 0x1 0x82 0x80 0x57 0xc9 0xb 0x61)) 5 (by decide) (UInt64.ofBytes 0x1 0x81 0x20 0x60 0x52 0x1 0x84 0x81)) 6 (by decide) (UInt64.ofBytes 0x50 0x5b 0x56 0xae 0xb 0x61 0x50 0x90)) 7 (by decide) (UInt64.ofBytes 0x1 0x81 0x90 0x50 0x90 0x50 0x50 0x50)) 8 (by decide) (UInt64.ofBytes 0xb 0x61 0x15 0x80 0x16 0x1f 0x60 0x90)) 9 (by decide) (UInt64.ofBytes 0x60 0x51 0x80 0x3 0x82 0x80 0x57 0xf6)) 10 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x3 0x20 0x60 0x83 0x1)) 11 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x16 0x19 0x3 0xa)) 12 (by decide) (UInt64.ofBytes 0x50 0x50 0x92 0x50 0x5b 0x50 0x91 0x1)) 13 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 14 (by decide) (UInt64.ofBytes 0x10 0xc 0x61 0x15 0x80 0x34 0x5b 0xf3)) 15 (by decide) (UInt64.ofBytes 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 16 (by decide) (UInt64.ofBytes 0x81 0x3 0x36 0x80 0x4 0x60 0x45 0xc))

private def absorbed23 : Vector UInt64 25 :=
  #v[0xcfd3e2cbaaba7b0d, 0x56b51a7529de891a, 0xc9f5719115916580, 0xf30e91726b2f65ac, 0x5ace23a0c88c92d1, 0x171f214f98486415, 0x9116e7962f035990, 0x46c7c96fc3bb5ba5, 0x38ad63d280e40913, 0xfeceec28e75e474d, 0xc9d8a2e7f85a3cc1, 0xab034c3708a39de8, 0x6a9a65f8cb75f0e4, 0x940b883971747b20, 0xcf30f7f0112992f7, 0xd9b530b659dd5934, 0x21de3410bf913d1a, 0xa5aac5426729bf14, 0x9cbf40af1eb8dfc8, 0x20b015f5da441f62, 0x7757e7e771c2a4df, 0x1e3c29eda96f28d5, 0x8974f2d78f4720d8, 0x627b92ba5ad4a5e3, 0xaa30ff6e09214acf]

private theorem words23 : absorb23 state23 = absorbed23 := by
  decide +kernel

private def quarter23_1 : Vector UInt64 25 :=
  #v[0x15d7a948185457a1, 0xf9b17f97ecb1a60b, 0x7e93c9ce73677f1a, 0x82b72bf75eaf43eb, 0x8151b5908c73a238, 0x96da051dd6b444b5, 0x7f0fdc37af901a3c, 0xc4a5518f90c0a6d0, 0x3494dcd01e6ca7f2, 0xb6c9fafe15b02302, 0xeb8e645366119e88, 0xfdf702a982c229b1, 0x8f4df46aacf623c8, 0x8256ce9219eb1c62, 0x169c874d656b6308, 0x47bf8f2dfd75d3eb, 0xd244da7d2f8e8a7f, 0x50b4b2c70c757a17, 0x63ce32f28956b402, 0x72953bdd4564424e, 0x402986630606f356, 0x2d7db593c8271add, 0xbb33f5fee3fd3fd7, 0x529938022807926, 0xa9348ce8d90cd2d0]

private theorem rounds23_0 : sixRounds 0 (by decide) absorbed23 = quarter23_1 := by
  decide +kernel

private def quarter23_2 : Vector UInt64 25 :=
  #v[0xd3ba289aef77b858, 0xbe850f18b5ddb052, 0xe4e11cf26933b0c7, 0xbf3dc5277525c5bc, 0x593f1f4b8d56dc69, 0xd452cc9e0b3c4ca9, 0xef3d5d6282927e6e, 0x823aa2281a83e2be, 0x696e434beabbd747, 0x1e636c602fb95cde, 0x5649741887c21bba, 0xc72bb76c36794a20, 0x8afe26e6e47de11a, 0xb3c1be74e4f5d0ef, 0xf77c7ad6ed24a991, 0x96c020997754f454, 0x5237b5152f4c09f7, 0x3bd8d5a281025f80, 0xea48445d5fdb4758, 0xec01a4765a168809, 0xb3aaacab23cc31f4, 0x6c409a8a473348f0, 0x791cd324f1233897, 0xae3a9f9b1f601444, 0x1f8482369266e7b2]

private theorem rounds23_1 : sixRounds 6 (by decide) quarter23_1 = quarter23_2 := by
  decide +kernel

private def quarter23_3 : Vector UInt64 25 :=
  #v[0xc6707fa39e88dc9f, 0x1106ffa9fdb1b8c4, 0xe0040ee7f189fffd, 0x92bcdded1b0263b5, 0xa72a2c782fb9606d, 0xc8607b7c51b45aef, 0xfe02c124e332eb51, 0x7a0c5e5914f75e75, 0x533661f4593d72bb, 0x5894d861bab37bad, 0xb716c2e6fb41aee3, 0xbc8599e475b16a8d, 0x8f680717ecd14fae, 0xa8fa0b080d5ee91a, 0x30f5fd7c05429e2e, 0xe1aef3fa6aba04bd, 0xf25e8acfc3e448eb, 0x52ff647143a711a7, 0x946580538b56f1a0, 0x5c1c778784c9fbf7, 0xdfdfaa9eb0a52a34, 0xbd7bf82b61bc4cd1, 0xde72ecef9b349d83, 0x283c279aac2fd7b8, 0x5aa5b8311e85d44]

private theorem rounds23_2 : sixRounds 12 (by decide) quarter23_2 = quarter23_3 := by
  decide +kernel

private theorem rounds23_3 : sixRounds 18 (by decide) quarter23_3 = state24 := by
  decide +kernel

private theorem perm23 : KECCAK.f1600 absorbed23 = state24 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds23_0, rounds23_1, rounds23_2, rounds23_3]
  rfl

theorem block23 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes23 ++ tail) state23 =
      KECCAK.Bytes.run 0 tail state24 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes23 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb23 ws)) := by
    rfl
  exact (step state23).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words23).trans perm23))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
