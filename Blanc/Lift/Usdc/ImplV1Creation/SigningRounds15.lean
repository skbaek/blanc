import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb90 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x62 0x65 0xa1 0x0 0x56 0x90 0x5b 0x56)) 1 (by decide) (UInt64.ofBytes 0x88 0x6e 0x20 0x58 0x30 0x72 0x7a 0x7a)) 2 (by decide) (UInt64.ofBytes 0x65 0xbd 0xd9 0xcb 0x8c 0xb3 0x9b 0x30)) 3 (by decide) (UInt64.ofBytes 0x74 0xb8 0xee 0xbe 0x6e 0x42 0x57 0x60)) 4 (by decide) (UInt64.ofBytes 0x26 0x5a 0x54 0xa1 0x16 0xfa 0xc4 0xe7)) 5 (by decide) (UInt64.ofBytes 0x29 0x0 0x43 0x7d 0x2b 0xdf 0xf6 0x74)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x1 0x80 0x80 0x1)) 16 (by decide) ((8 : UInt64) <<< 60))

private def absorbed90 : Vector UInt64 25 :=
  #v[0x93b257a61d229226, 0x53a6e2bbde5fb2b2, 0xf925de96edacefa0, 0x941e3c50b5514976, 0x9f72010bb334400b, 0x4f4682f942e7ea77, 0x83644528963854b1, 0x141ce8b238082b02, 0xb023482b08ec9d87, 0x65097dfbad598529, 0x1606a7d37838d4e5, 0x7fb458f37f4454d2, 0xc3b3fe334da55975, 0x9f3c2944b22f9fcd, 0x388b887a923e2fda, 0xc6d1a69038939ccf, 0x14044a26bfb00157, 0x84c7307074c740ed, 0x24a6eadc08f7c0d8, 0x991ffc15831d0507, 0x3518410b5d9736a, 0xd49fbc25a1c2911a, 0xb79a3ae8b141b30b, 0xf53c11585525c717, 0x6692135f588d9b6e]

private theorem words90 : absorb90 state90 = absorbed90 := by
  decide +kernel

private def quarter90_1 : Vector UInt64 25 :=
  #v[0xab2c7421d76a5983, 0xc70998d50eb9c587, 0x345a9995627681c7, 0x712fff0077c20718, 0x2c2338109f76eae2, 0xf03b43df404f0a08, 0x529ab04f9be01e4b, 0x7fcea2c42954987f, 0x3f4a5961426e2a9c, 0x585360a54bf5fc69, 0x1a49869d48a0deb5, 0xc04d8a7abcedbb39, 0xd6df9546b907bf9f, 0xb411a128b53a6956, 0x81334f2a06c12495, 0x22d6d3ee85cd12db, 0x460d6f33a10922b7, 0xd5811a41e20b10e2, 0x6a4f19e5d4f4d859, 0xd7f27a384a92402f, 0xdcf284bebc4f1b46, 0xdcff352e6f765b48, 0x3776f1352bb9f6e4, 0xa449f1ace9352732, 0xdb1aacf4debefedc]

private theorem rounds90_0 : sixRounds 0 (by decide) absorbed90 = quarter90_1 := by
  decide +kernel

private def quarter90_2 : Vector UInt64 25 :=
  #v[0xd3e2bbddaa66e609, 0xbd17323d9dac18df, 0x59cb7142784da911, 0x590fbfb8682c77ca, 0x46b54f35f4cbc12, 0x355698fe025c0667, 0x2e447747516a210e, 0x13591a5b7e94f3f9, 0x4fa31d6d912393fb, 0x1b47c5088cd83433, 0x4497cc47e82bdf49, 0xdb5c57e0e9439526, 0xb6f0ed9236d161fa, 0x1bc261a4eb71eaf6, 0x89c66c5dc155b36e, 0xdace62a0575c1302, 0x3490a0fcd9248ab0, 0x1c70ef7f2b3c8cab, 0x96e501e781460993, 0x177226b885d943c2, 0xac54f0a83456956f, 0xab01dd53b09be196, 0xa10dad24636c46b, 0xd1a108fc76caea1a, 0xe95276f479666da7]

private theorem rounds90_1 : sixRounds 6 (by decide) quarter90_1 = quarter90_2 := by
  decide +kernel

private def quarter90_3 : Vector UInt64 25 :=
  #v[0x2dc532ce17ae4ccf, 0xcd8540c862715b7b, 0xb23e374456e90449, 0x92e4f933ef9a631, 0x5997fd2d7440eaac, 0x5fea746bbb1e0281, 0x282abf1fe8347d1f, 0xc29e45d6721110f6, 0x103ff351255dbbe8, 0xdf8e7e5d2b9a6f68, 0x83a35e4c768843c5, 0xcae0b8a6537804c8, 0xe7b0776f4f394986, 0xee2775a4eb598093, 0x37594b296829dc33, 0xb2bc0d0183caf6f9, 0xbd761fdaa0a2667a, 0xaee2f298c1735586, 0x8f35a0f4bfda93b7, 0x6073ff5ba99b57b2, 0x9575b1fa9e80e67f, 0x76d48c1f9b50ed66, 0x2dd0087b1869384b, 0x3958ec8c52181472, 0x4671231da009d725]

private theorem rounds90_2 : sixRounds 12 (by decide) quarter90_2 = quarter90_3 := by
  decide +kernel

private theorem rounds90_3 : sixRounds 18 (by decide) quarter90_3 = state91 := by
  decide +kernel

private theorem perm90 : KECCAK.f1600 absorbed90 = state91 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds90_0, rounds90_1, rounds90_2, rounds90_3]
  rfl

private theorem finalDigest : squeeze state91 = (0x3a424731e9075d7b45dcc6ab92455664e56100fbb6419923723a54aa9d5710ad : B256) := by
  decide +kernel

theorem finalHash :
    KECCAK.Bytes.run 0 bytes90 state90 = (0x3a424731e9075d7b45dcc6ab92455664e56100fbb6419923723a54aa9d5710ad : B256) := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 bytes90 ws = squeeze (KECCAK.f1600 (absorb90 ws)) := by
    rfl
  exact (step state90).trans ((congrArg squeeze
    ((congrArg KECCAK.f1600 words90).trans perm90)).trans finalDigest)

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
