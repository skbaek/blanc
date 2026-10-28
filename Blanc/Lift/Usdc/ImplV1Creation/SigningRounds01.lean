import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb06 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0x91)) 1 (by decide) (UInt64.ofBytes 0x5b 0x56 0x53 0xf 0x61 0x9a 0x2 0x61)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x82 0x80 0x51 0x40 0x60)) 3 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x20)) 4 (by decide) (UInt64.ofBytes 0x80 0x34 0x5b 0xf3 0x90 0x3 0x91 0x80)) 5 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xbc 0x2 0x61 0x15)) 6 (by decide) (UInt64.ofBytes 0x4 0x60 0xf1 0x2 0x61 0x50 0x5b 0xfd)) 7 (by decide) (UInt64.ofBytes 0x80 0x80 0x90 0x1 0x81 0x3 0x36 0x80)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x35)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x90 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x50 0x90 0x91 0x92 0x90 0x1 0x20 0x60)) 12 (by decide) (UInt64.ofBytes 0x0 0x5b 0x56 0x5d 0xf 0x61 0x50 0x50)) 13 (by decide) (UInt64.ofBytes 0x57 0xff 0x2 0x61 0x15 0x80 0x34 0x5b)) 14 (by decide) (UInt64.ofBytes 0x3 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60)) 15 (by decide) (UInt64.ofBytes 0x1 0x81 0x3 0x36 0x80 0x4 0x60 0x5e)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x80 0x80 0x90))

private def absorbed06 : Vector UInt64 25 :=
  #v[0x550cf29f8e4eedfd, 0xc5c5544c9ee19cbc, 0xd4340853cb197c06, 0x4613c680b00cf22c, 0x85d22058e1d128b0, 0x57713815b05a2038, 0x3cc74a0aea3592bf, 0x4099bf8354586cc9, 0x247c0106ed2d8f8a, 0xd4bbb526aa42f4d3, 0xce58c9f60ce47d33, 0x657dc91d880599b, 0xdef93099f9e062ba, 0x17596516541af34f, 0x5548b159b1b7582e, 0x5ce8b9b976cceda7, 0x97d16025b7e694aa, 0x2ea72c214ee816f9, 0xcc96fc98c01e7b8e, 0x2bc2147e8f69e39f, 0x3a04556b8222914d, 0xe7e7f46d939f6d12, 0x665b52536d76bd01, 0x7c98d5f722d84234, 0x2e286240eaa603a9]

private theorem words06 : absorb06 state06 = absorbed06 := by
  decide +kernel

private def quarter06_1 : Vector UInt64 25 :=
  #v[0x9ff5dcc4f958d3c, 0xa5822f05503859b3, 0x8b1e5798ef355052, 0x15fd6b0c0189a81a, 0x6b904e5a3c15e60b, 0x6f559127cc282104, 0x68e4fd59ba03412e, 0x7db781cf04346270, 0x79eaa756ab72bb31, 0xdc5ea1bd7560945c, 0x3f6060f823e37aa7, 0x21a8f974ca684833, 0x47bcfa45e0e365d7, 0x6e66d10f0c620558, 0x4e1f71ff0b41fab9, 0xf7cc77dc0bae6e79, 0xdb4462005cc02a65, 0x3be06f996737ee0, 0xa22859c85eb14f5c, 0xde20894eb3b69783, 0x39819dadf6e43940, 0x54ae2abdf765990b, 0x1e08b90f4c40b7e9, 0x5dfd391ef75cdf01, 0x44b82ead322bfeb]

private theorem rounds06_0 : sixRounds 0 (by decide) absorbed06 = quarter06_1 := by
  decide +kernel

private def quarter06_2 : Vector UInt64 25 :=
  #v[0xbe3e45e773134d54, 0x94f1bfe9c6d8e97, 0x7549cd4203c093fd, 0x821bb2a466696636, 0xe9c7d2f4aff03452, 0x66b91629eb86e222, 0x74ec0b60bcd1a610, 0xcfdbc0648c3d2f41, 0x196c742135b84cd7, 0xec46b1b2b6992b5d, 0x6e3a3c869e37b4c2, 0xbd5638f10981ea5b, 0xa9061d99698adfba, 0x42385d8abee10950, 0xd26675c23d093ee3, 0xab46444f0b0bf1f0, 0x95e7c91ea5ccfdfc, 0xdc19f62dc948c4db, 0x3cda3d6f88cb76cb, 0x5092faf8d74746c5, 0xa2519e66386f89c1, 0xaee4d4b1774a384, 0xf9eb96e9961e1da7, 0xc1715f0112314d0c, 0xe7212e5d62cbdb5]

private theorem rounds06_1 : sixRounds 6 (by decide) quarter06_1 = quarter06_2 := by
  decide +kernel

private def quarter06_3 : Vector UInt64 25 :=
  #v[0x35b128badb35415b, 0x2bd2b282fed21c49, 0x86c2ab88ba85604c, 0x517841a58aea2f14, 0x222d70942147b54b, 0x26823f90bcb6247d, 0x5aafe075c25ef3a1, 0x1f929c413c829acf, 0x80ead6f568b24c36, 0x1b3dacd7189a7a4c, 0xcacf03921ad24380, 0x5021af53c3c785cf, 0xe823ace6d183c00a, 0x88a9cdf40359beca, 0x9f4f151ed9e51a7f, 0x6163f6b6ebcd5695, 0x4c799c5c62d381fa, 0x969176d7e3134393, 0xd2a9d05b6a4e377e, 0xbe5c2087a31cdd7, 0xc821d1d5e66c77f7, 0xa23ade99c793fd6, 0x73bff8d94ceec381, 0xffad73205c987038, 0x5b48725d68b35b08]

private theorem rounds06_2 : sixRounds 12 (by decide) quarter06_2 = quarter06_3 := by
  decide +kernel

private theorem rounds06_3 : sixRounds 18 (by decide) quarter06_3 = state07 := by
  decide +kernel

private theorem perm06 : KECCAK.f1600 absorbed06 = state07 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds06_0, rounds06_1, rounds06_2, rounds06_3]
  rfl

theorem block06 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes06 ++ tail) state06 =
      KECCAK.Bytes.run 0 tail state07 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes06 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb06 ws)) := by
    rfl
  exact (step state06).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words06).trans perm06))

private def absorb07 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x80 0x90 0x91)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 7 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x35 0x80 0x90 0x91)) 8 (by decide) (UInt64.ofBytes 0x61 0x50 0x50 0x50 0x90 0x91 0x92 0x90)) 9 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x5b 0x56 0x57 0x10)) 10 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x15 0x15 0x15 0x15 0x82)) 11 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x20)) 12 (by decide) (UInt64.ofBytes 0x80 0x34 0x5b 0xf3 0x90 0x3 0x91 0x80)) 13 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x84 0x3 0x61 0x15)) 14 (by decide) (UInt64.ofBytes 0x4 0x60 0xb9 0x3 0x61 0x50 0x5b 0xfd)) 15 (by decide) (UInt64.ofBytes 0x80 0x80 0x90 0x1 0x81 0x3 0x36 0x80)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x35))

private def absorbed07 : Vector UInt64 25 :=
  #v[0x4d9bd6aa905d6a33, 0x21f69a4a874b1d7b, 0x4116127787c1da5, 0x827fc4901df3cd48, 0xa3760c566df0a2ad, 0xf01471f1360c4737, 0x47bf2aef2f5d39e4, 0xabf402f425198697, 0x71713af5aa78c99b, 0xd4a9e22fa98640cc, 0x23e95bb61f1058d8, 0x71ed026019eb6295, 0xe5a4dfb6919d3362, 0xcf6531267aca6f12, 0xa3d9329d15a463e0, 0xbe7ae1db34654d2b, 0x225e7cc65fa0153b, 0xae687d391523bca, 0x798946fce88cb08a, 0x2832e8e0097bcc11, 0xc211972046d1e8fb, 0x64a154bbb21f2e7f, 0x89f429142d9b8b09, 0xb96ac2d575773e00, 0x3ed624fa3009fe4a]

private theorem words07 : absorb07 state07 = absorbed07 := by
  decide +kernel

private def quarter07_1 : Vector UInt64 25 :=
  #v[0x340dac436fb13830, 0x63110fb4b5d7921c, 0xf2f7900831bba019, 0x2b7459a0b44b79d, 0x65de2e1c9dd02b2a, 0xfe7fff608226833a, 0xbeb741cccb5df51e, 0xe5724ada600cbe14, 0xfa7969a15252ef40, 0x1611f69bb65ee02d, 0x2184080f1adb2021, 0xc0e1ed16efb1d336, 0xcbb0c1f218ba7bac, 0xa2ceba09bbbe5e9f, 0x95df560cecfdb677, 0x93248c9f4c73cd49, 0x6260b20eea0a0a09, 0x10934a3a4c016aec, 0xc8aa315ef9e66870, 0x7ec530300374db81, 0xabc8b4d448448f20, 0x2fc15f1c00d578b9, 0x159326f34371ca43, 0x8905c2d8015116e2, 0xea2acf3a40a17d6f]

private theorem rounds07_0 : sixRounds 0 (by decide) absorbed07 = quarter07_1 := by
  decide +kernel

private def quarter07_2 : Vector UInt64 25 :=
  #v[0xed93278ead83ff1, 0x603a65498983b0, 0xe549c4c9b6bccfb, 0x6d8584d2fa32beb3, 0x17a2da6ab3d228b6, 0x11200cde7c8bc8c8, 0x7080be96930f9f06, 0xe3538def6451a942, 0xde72d2eb4f95bbcc, 0xc97694fdb9729a9, 0x1b3970e8be672c2d, 0xd95a98be41e6d384, 0x2e4564b3c2a331ad, 0xe63e628d47cc2145, 0xba6d2d5847403c2, 0xcd86f0a3586bd1d1, 0x9632e011d96fa62b, 0x8fab39c9a6e115f0, 0x6b9c5bab9dcd359f, 0x6e02db982f189031, 0x648c4c72c366de28, 0x6c33b7d8789b7cb5, 0xc06259ab5f2cc471, 0xcb959d4f7003a2b5, 0xcac682b460ea7607]

private theorem rounds07_1 : sixRounds 6 (by decide) quarter07_1 = quarter07_2 := by
  decide +kernel

private def quarter07_3 : Vector UInt64 25 :=
  #v[0x63928ebadc2bfdee, 0xdee645c64ff4c010, 0xacaf2d9ae0efd06d, 0xd5eb94f6d81b318b, 0x92a00ad6076d6702, 0xc5824f65d740d804, 0x10ec8d190af75200, 0xb1b0d47b77ae24a9, 0xac1b40bcc08b5e5e, 0x4c25c5b9e7e419a9, 0x2a213fecc56318ae, 0x89a2cfb03a38c001, 0x58ec9d4b22db86bf, 0xbe7753dc6c91548e, 0x909fd6229e4e561, 0xe193252660d028ab, 0x33fa6c41a1db62c3, 0xb542b2801b0683e6, 0x52c4a9ee66932517, 0xf4b397ff168c1b5d, 0x79fb90f4100f50ad, 0x45aa13c9fc8545a6, 0xde0eca39249763c9, 0xbcaadf5bd90dd8b6, 0x10ff7be9801f9b2f]

private theorem rounds07_2 : sixRounds 12 (by decide) quarter07_2 = quarter07_3 := by
  decide +kernel

private theorem rounds07_3 : sixRounds 18 (by decide) quarter07_3 = state08 := by
  decide +kernel

private theorem perm07 : KECCAK.f1600 absorbed07 = state08 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds07_0, rounds07_1, rounds07_2, rounds07_3]
  rfl

theorem block07 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes07 ++ tail) state07 =
      KECCAK.Bytes.run 0 tail state08 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes07 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb07 ws)) := by
    rfl
  exact (step state07).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words07).trans perm07))

private def absorb08 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x90 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x50 0x90 0x91 0x92 0x90 0x1 0x20 0x60)) 3 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x56 0x15 0x61 0x50 0x50)) 4 (by decide) (UInt64.ofBytes 0x15 0x15 0x15 0x15 0x82 0x80 0x51 0x40)) 5 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x20 0x60 0x52 0x81)) 6 (by decide) (UInt64.ofBytes 0xf3 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 7 (by decide) (UInt64.ofBytes 0x57 0xdf 0x3 0x61 0x15 0x80 0x34 0x5b)) 8 (by decide) (UInt64.ofBytes 0x3 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60)) 9 (by decide) (UInt64.ofBytes 0x40 0x60 0x5b 0x56 0x9d 0x16 0x61 0xe8)) 10 (by decide) (UInt64.ofBytes 0xff 0x60 0x16 0xff 0x60 0x82 0x80 0x51)) 11 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x20 0x60 0x52 0x81 0x16)) 12 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 13 (by decide) (UInt64.ofBytes 0x10 0x4 0x61 0x15 0x80 0x34 0x5b 0xf3)) 14 (by decide) (UInt64.ofBytes 0x61 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 15 (by decide) (UInt64.ofBytes 0x81 0x3 0x36 0x80 0x4 0x60 0x84 0x5)) 16 (by decide) (UInt64.ofBytes 0x20 0x60 0x90 0x35 0x80 0x80 0x90 0x1))

private def absorbed08 : Vector UInt64 25 :=
  #v[0xcefbf645aca5fa5, 0xcca595b84dfc7819, 0xf477d78bf22cd585, 0x963d0f0b956061b6, 0xfc94bd548adaae66, 0xdc551c0a6442fd92, 0x2e8335f6fc30b6a1, 0xfef2f4903c0e8551, 0x7fc9664bd972c724, 0xfbc5f08b784fa417, 0x46adc6a5f103daf7, 0xba4b2bd36a93b12, 0x8377e66a2ced4fc0, 0x380587539960c669, 0x4cf97928c727d500, 0x1bdea6e6fc5632b8, 0x9becbaab89a783b0, 0x911a0bf11d8c162d, 0x9005e3d29bbf203, 0x5c57695bfea1306d, 0x2229494e2892fdc3, 0xd6642321da40ebeb, 0xc0c794616a5b2e4c, 0xfe6706579baa9598, 0x1531b20e23140f65]

private theorem words08 : absorb08 state08 = absorbed08 := by
  decide +kernel

private def quarter08_1 : Vector UInt64 25 :=
  #v[0xc02f4fce8040b219, 0xe8b0f600ebd5ed9c, 0xcc2793a815b0a226, 0x1aed1849d6993050, 0xcbe683768c552cf, 0x1ae17991eded0dd7, 0x44a9266de3bbb076, 0x977f7db90e322114, 0xf12b2a64512b32c3, 0x5565ba0197c5a3ce, 0x4505469d409c89b7, 0xc04d86b9aed72d33, 0xb4394a27758791e4, 0xa32de9cbdd9b45f1, 0x1d36fcf702490cf5, 0x36187b67bdda6923, 0x120c86fb2c3a3ce3, 0xdde592d52f6ff6f2, 0x7b63c3986a37bb2b, 0x9c65f9c745fb844a, 0xa5bbbafa0b5c4f2d, 0x2b4052a74b496918, 0x777ebb7e183f1df4, 0x3d9363dc9de592c9, 0x656d1c8a581a460f]

private theorem rounds08_0 : sixRounds 0 (by decide) absorbed08 = quarter08_1 := by
  decide +kernel

private def quarter08_2 : Vector UInt64 25 :=
  #v[0xe52616ee7c1a2bf9, 0x3ec47563a5e113d1, 0x8e616908948aa93a, 0xd6714766d587fd1c, 0x61d3b1ad83e27605, 0xe0a96e6464d5297e, 0x992d77f9618fbd32, 0x8b6f23d37e9518e3, 0x320d4b62d290093a, 0x3a4f0ef3ce7627da, 0x69e2c5785c32384f, 0x7cc946fa11b5743d, 0x2c855465b5bfaac7, 0x7ab45ed871939d13, 0xe2770571a7af4126, 0x45013bed94084ea6, 0xde06af115f0ac212, 0x58fb026b1c35ee9, 0xe7276cc9c58f2f69, 0xe7a2072ef373551b, 0xa1e138938ba3ec5d, 0x2dc7f6bc5646ff36, 0xd80aeefc5cd572ec, 0x4cf57e0602e37da6, 0xbaee3e68055e14f]

private theorem rounds08_1 : sixRounds 6 (by decide) quarter08_1 = quarter08_2 := by
  decide +kernel

private def quarter08_3 : Vector UInt64 25 :=
  #v[0x674bc24b34accf9f, 0x4edfe7c1e341452f, 0x8c293499e8f44e35, 0x5e7387467d57d5b3, 0xd676887409e2c5ae, 0xa57ba61f8d225208, 0xd0747482f56cec95, 0x765d7a14dd428a36, 0x16cae22c914dcfdc, 0x769e4bd21658e551, 0xfad7cdf8f2c1319f, 0x540b4b70ac26c801, 0x76fb49bf4bd78fe5, 0x523f694db8a937a1, 0xbc1f5cfbcaa4fe7d, 0xfe48c1e09a758d72, 0x325bec0c25dc5ecb, 0xe296652e6193ed10, 0x7fc7087750aae1f4, 0x6d9e6ae7f84e584a, 0x2d1cf5d7443e959, 0xd53467bd1de12d93, 0xe3d7be0a7651d26d, 0xa1ed1711b5b1bf45, 0x43867dfd58742b23]

private theorem rounds08_2 : sixRounds 12 (by decide) quarter08_2 = quarter08_3 := by
  decide +kernel

private theorem rounds08_3 : sixRounds 18 (by decide) quarter08_3 = state09 := by
  decide +kernel

private theorem perm08 : KECCAK.f1600 absorbed08 = state09 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds08_0, rounds08_1, rounds08_2, rounds08_3]
  rfl

theorem block08 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes08 ++ tail) state08 =
      KECCAK.Bytes.run 0 tail state09 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes08 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb08 ws)) := by
    rfl
  exact (step state08).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words08).trans perm08))

private def absorb09 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x90 0x35 0x80 0x1 0x82 0x90 0x1)) 1 (by decide) (UInt64.ofBytes 0x1 0x1f 0x60 0x80 0x80 0x90 0x1 0x20)) 2 (by decide) (UInt64.ofBytes 0x20 0x60 0x2 0x4 0x91 0x80 0x20 0x60)) 3 (by decide) (UInt64.ofBytes 0x60 0x1 0x81 0x90 0x51 0x40 0x60 0x1)) 4 (by decide) (UInt64.ofBytes 0x81 0x90 0x91 0x92 0x93 0x80 0x52 0x40)) 5 (by decide) (UInt64.ofBytes 0x80 0x83 0x83 0x1 0x20 0x60 0x52 0x81)) 6 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x82 0x37 0x84 0x82)) 7 (by decide) (UInt64.ofBytes 0x92 0x91 0x92 0x91 0x50 0x50 0x50 0x50)) 8 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x90 0x35 0x80 0x90)) 9 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x90 0x35 0x80 0x1 0x82)) 10 (by decide) (UInt64.ofBytes 0x20 0x60 0x1 0x1f 0x60 0x80 0x80 0x90)) 11 (by decide) (UInt64.ofBytes 0x60 0x1 0x20 0x60 0x2 0x4 0x91 0x80)) 12 (by decide) (UInt64.ofBytes 0x52 0x40 0x60 0x1 0x81 0x90 0x51 0x40)) 13 (by decide) (UInt64.ofBytes 0x52 0x81 0x81 0x90 0x91 0x92 0x93 0x80)) 14 (by decide) (UInt64.ofBytes 0x84 0x82 0x80 0x83 0x83 0x1 0x20 0x60)) 15 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x91 0x1 0x82 0x37)) 16 (by decide) (UInt64.ofBytes 0x80 0x90 0x92 0x91 0x92 0x91 0x50 0x50))

private def absorbed09 : Vector UInt64 25 :=
  #v[0x330308ad9dd6169e, 0x9d519d5cb4c861b8, 0xfa77665a7c276dfd, 0x34bee74bb70eba6, 0xa9281e460a577b79, 0x2c111a9320e6e8d4, 0x258c09983dcb9934, 0x6365d863b9172416, 0xb4361a64ec399993, 0x67982abeec00969e, 0x5700778837e1a630, 0x42993266c5094f64, 0xb61ba0085d97895d, 0x6495998a34201957, 0xc282a156e08072a, 0xd75cdb2721c87ff6, 0x592d8b962336ec1c, 0xa3d9be10a2477272, 0xdaf96fa62897f237, 0xdce99ef3cd342cdc, 0x9abb103a7b4d939d, 0x13bc6ee813680967, 0x9bd2062b590db8ad, 0xce49fec583b9e289, 0x7d119c27f56c91e]

private theorem words09 : absorb09 state09 = absorbed09 := by
  decide +kernel

private def quarter09_1 : Vector UInt64 25 :=
  #v[0xc4797b0cfeda8fd, 0xc93568d165f67fc6, 0xbde7d29dcfacbf5a, 0xbdacddfea7ab5c2e, 0xc20fa41339f83074, 0xc3d1c8f928acec53, 0xa6ebc27df37bebcd, 0x60cb043945ae1893, 0x7dcae700373e73df, 0xa4165e06724f120a, 0x7c76627b8c29f430, 0xf1bc14c6f4b28a2c, 0x64a22448b8464d8f, 0x2647fb24eabfee84, 0xc247be7d4c5df6e8, 0x1a57ef3137ad1ace, 0xbb074c6352e67dc0, 0x4c9026276a40bb0f, 0xc205bc00ecf5fed9, 0x82a0eff513db44, 0x3e4aa05a1af1130e, 0x9c770f8892b87541, 0x427e4d69022c7dc9, 0xf4a0a0834ad188fd, 0x247d993233c27c9a]

private theorem rounds09_0 : sixRounds 0 (by decide) absorbed09 = quarter09_1 := by
  decide +kernel

private def quarter09_2 : Vector UInt64 25 :=
  #v[0x6699370b5a2871f7, 0x9cc159bf3ab1c0dc, 0x9a1dc4c4b5eadafa, 0x992fb790635dda1b, 0x6ccdca332d667bcd, 0xf0381ce8f638557c, 0x8d479321624ad1c1, 0x441e4a46263304f6, 0x989dd3b911b44e3f, 0x6e2e923ddc7e3caf, 0xa7f78955e8ccd1cb, 0x75e7ef1279698122, 0xf6a97884925e6bed, 0x26745d22f95647ee, 0x690c21f1de7bc5e9, 0x2ac679c6e1e038d, 0xa1de5ce89bc833d7, 0xd16fccbe96ac3f2e, 0x1fcc8d0cc815090b, 0x91f7617b19b748cb, 0x80355a4e4dc527d0, 0x792465e193eda93d, 0xb12de9ee2d103524, 0xb4f51319db28b72d, 0x3d5545f319d828ca]

private theorem rounds09_1 : sixRounds 6 (by decide) quarter09_1 = quarter09_2 := by
  decide +kernel

private def quarter09_3 : Vector UInt64 25 :=
  #v[0x2b7a69bc932d941e, 0x8399965f9ecd9db, 0x51f2a7b8190a837e, 0xc9ed55b721fda593, 0xa3147984a669bea0, 0xff67021d666255a2, 0x86e8be19191c8208, 0x9f33a0d3793ec83, 0x9ea4deac5e70ce2a, 0xdbb918f2a3371d60, 0xeb49d689aa8c3255, 0xc1159c80e3de5873, 0x5377a16cf0b0e4ea, 0x136c59bcacec98a7, 0x24c03439fdc53c46, 0xa082ba1dc2e1ef53, 0xdb8977292492b64e, 0xe72fbe990d05867d, 0x8d8db11581a1c2df, 0xb5f8f32b4af579ad, 0x195185fa6ccf3f0b, 0xcfeff1a936aff14d, 0xa971e766c617d7e4, 0xac9121c3900d8641, 0xac530065d311a476]

private theorem rounds09_2 : sixRounds 12 (by decide) quarter09_2 = quarter09_3 := by
  decide +kernel

private theorem rounds09_3 : sixRounds 18 (by decide) quarter09_3 = state10 := by
  decide +kernel

private theorem perm09 : KECCAK.f1600 absorbed09 = state10 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds09_0, rounds09_1, rounds09_2, rounds09_3]
  rfl

theorem block09 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes09 ++ tail) state09 =
      KECCAK.Bytes.run 0 tail state10 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes09 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb09 ws)) := by
    rfl
  exact (step state09).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words09).trans perm09))

private def absorb10 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x82 0x90 0x1 0x20 0x60 0x90 0x35)) 1 (by decide) (UInt64.ofBytes 0x80 0x90 0x1 0x20 0x60 0x90 0x35 0x80)) 2 (by decide) (UInt64.ofBytes 0x91 0x80 0x20 0x60 0x1 0x1f 0x60 0x80)) 3 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x1 0x20 0x60 0x2 0x4)) 4 (by decide) (UInt64.ofBytes 0x93 0x80 0x52 0x40 0x60 0x1 0x81 0x90)) 5 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x81 0x90 0x91 0x92)) 6 (by decide) (UInt64.ofBytes 0x82 0x37 0x84 0x82 0x80 0x83 0x83 0x1)) 7 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x50 0x50 0x91 0x1)) 8 (by decide) (UInt64.ofBytes 0x60 0x35 0x80 0x90 0x92 0x91 0x92 0x91)) 9 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x80 0x90 0x91)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x80 0x90 0x91)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed10 : Vector UInt64 25 :=
  #v[0x1a8f2c32197ca921, 0xf8a70d6f7d9b2050, 0x98e4f6092acc2c97, 0xc59ee0a34419988a, 0x64a4a4ce9250a15, 0x597b4ade2d807c58, 0x4edc63b7eace3a2e, 0x3cdfa0c621bc6af, 0x9f68caee511f80ff, 0xd49321e8e7d664e6, 0x1be9c20427b63782, 0xea336fcd73a38a6e, 0xf2a912f1c54d4c06, 0xe0d5a807e1a93b52, 0x5e3d2d512235ce7b, 0xce7e566fe4ae967e, 0x7f0b20f3083ca0e3, 0xe54eb3ded97f6c5, 0x81c804e84bc5e01c, 0xdf60e589559941aa, 0x1555d14eebb2f86a, 0x284fc311e831f448, 0x4588998bc45973c7, 0xe22dc69a20a105d8, 0xac0870d5096d8981]

private theorem words10 : absorb10 state10 = absorbed10 := by
  decide +kernel

private def quarter10_1 : Vector UInt64 25 :=
  #v[0xc57c892a31db7e01, 0x6d8862611a454e4a, 0x4dc16f73035d4c06, 0x584849fcc7064231, 0xd54be3b5eb3ab3f4, 0x24ba6fbf2ee11a7f, 0xb4ddf17ad54ff380, 0xe5901780bd605cb8, 0x408f6f5f4a8703b9, 0xfdc10040fe29b8cb, 0xd41e2b0adadb001f, 0x4af2d2e9d36002a7, 0xd2d5551c7361cbe, 0x853cdc4abc1b1bdd, 0xf9aab757f719911a, 0x40eb0a9e2d09ec9f, 0xbca5c5366e6e9fc9, 0xd30965b63bc17705, 0x90ec401be22ec6e1, 0xf44b86ae026b7754, 0xd9b98bd790d5993f, 0x9348c970b15aca7c, 0x94ad7fc8ab12b114, 0x7fdbb18bceda4f95, 0x3a2675c567d1a609]

private theorem rounds10_0 : sixRounds 0 (by decide) absorbed10 = quarter10_1 := by
  decide +kernel

private def quarter10_2 : Vector UInt64 25 :=
  #v[0xe000fb375aeb7916, 0xacafe8f1fdbcc12a, 0xfa9a2b647bf6b6df, 0xf0e483fdbfaac575, 0xa03ef8a1b3e7eff7, 0x450cb8f00ba611e9, 0x2686f4cdf7cfc300, 0x1fba0300d3cd5943, 0xc8e98c5bc8e80a4a, 0x983ebb2c9b7a53b8, 0x924918e883226dd0, 0xde736ca5f1e4151c, 0x9a00ea36897797b1, 0x5c7b8f204c700006, 0x8d0c7fce45094928, 0xdcff5bdeac16725a, 0xfd2a32c8aa00d755, 0xf7e9fd9ec8e16f79, 0xfd5826c8d21b5894, 0xa3692e3b14f5cb5c, 0x1a21ea73d753bca0, 0x27c3cdc51eb94703, 0xc893ffeefe7a5bb1, 0x50536779e9e23094, 0xf2e1f5161cc379a4]

private theorem rounds10_1 : sixRounds 6 (by decide) quarter10_1 = quarter10_2 := by
  decide +kernel

private def quarter10_3 : Vector UInt64 25 :=
  #v[0x826729c295eee26e, 0xb0af4fd843ead522, 0xbf5e5165a1f8c751, 0xc41471ea8acfd1e1, 0x23b334df7169b738, 0xa0aa27f1e1b95a09, 0xebaf5470020b169d, 0x620f1d6e87bac0f9, 0x7010631eb4a32ad5, 0x664c028a592cdfcd, 0xc1f062885f8e8f51, 0x22dbf70a6c5d275e, 0x506857b5783334b2, 0x7731b3108fb1db56, 0xc20521a9c115b542, 0x48a81f1408f189db, 0xb13d703b06ef2c43, 0x5bc0b2c6a2bd25c6, 0xfd4f90cfaf64894, 0xf582977253f1378b, 0x41b7f552e70649d0, 0x475fb5417703e02b, 0xbc127d9a868816fd, 0xc8e8dabd5dcbd0be, 0x12c048aad5f4dc53]

private theorem rounds10_2 : sixRounds 12 (by decide) quarter10_2 = quarter10_3 := by
  decide +kernel

private theorem rounds10_3 : sixRounds 18 (by decide) quarter10_3 = state11 := by
  decide +kernel

private theorem perm10 : KECCAK.f1600 absorbed10 = state11 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds10_0, rounds10_1, rounds10_2, rounds10_3]
  rfl

theorem block10 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes10 ++ tail) state10 =
      KECCAK.Bytes.run 0 tail state11 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes10 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb10 ws)) := by
    rfl
  exact (step state10).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words10).trans perm10))

private def absorb11 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x80 0x90 0x91)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x35 0x80 0x90 0x91)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x92 0x90 0x1 0x20 0x60 0x90 0x16 0xff)) 9 (by decide) (UInt64.ofBytes 0xb0 0x16 0x61 0x50 0x50 0x50 0x90 0x91)) 10 (by decide) (UInt64.ofBytes 0x61 0x15 0x80 0x34 0x5b 0x0 0x5b 0x56)) 11 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x80 0x0 0x60 0x57 0x92 0x5)) 12 (by decide) (UInt64.ofBytes 0x56 0xd 0x19 0x61 0x9b 0x5 0x61 0x50)) 13 (by decide) (UInt64.ofBytes 0xff 0x73 0x82 0x80 0x51 0x40 0x60 0x5b)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0xff 0xff 0xff))

private def absorbed11 : Vector UInt64 25 :=
  #v[0xa050cccc4fd42b7e, 0xa2ce194bdd4878ce, 0xd874fa974636855f, 0xc8bfb825d25af54d, 0x3b0db781ac9b8aef, 0xa6fe1d026ed5164f, 0x503d4a6526a39f45, 0x18356d4b503dda7a, 0xf45a053d52f4c2b7, 0x59e34189022da853, 0xa1e900f8bb7c6c37, 0x8dd1680025f95a83, 0x72593afb273dcdab, 0xff8534d43821bce3, 0xbd14ec272b6fde8f, 0xa31b5ad7010a1330, 0xca22e2b1950b5aeb, 0xad84e9131e5e604c, 0x2378ade469f45d10, 0x22c82eefb1d84834, 0x332000571d3205bd, 0xfc7362b0c88192ee, 0xa784c29fc8eaa90c, 0x2cce9fa1a10d6025, 0x31bbfbc3d88ef38b]

private theorem words11 : absorb11 state11 = absorbed11 := by
  decide +kernel

private def quarter11_1 : Vector UInt64 25 :=
  #v[0xf44bf5561866d690, 0x6ddb8761cfc0f522, 0xdf99474f0e9d5128, 0x282fa7aace23e0f2, 0x46c1fc0cc165819e, 0xee2beef399277620, 0x616953c492546149, 0xead9f5c1fa0b292a, 0xe2fbbe207f9aaab0, 0x519b96e206aa9507, 0xff0bf08b0ed1a883, 0x65638ff205f21321, 0x5c85b0650463f7e8, 0x17efd36ebc075c78, 0x4831532e9a1043ca, 0x69221dc59fcf9109, 0x1c71544a44a27f8e, 0xe9d26c5ef5f4b3f6, 0x16d46a151369fd00, 0xc46d9b2f9318623c, 0x7ce35eca05ba93d5, 0x84adc19bdf891008, 0x44c1b3b8cc947e52, 0xbb93f8eea05519b, 0x1d3f07be45dd5136]

private theorem rounds11_0 : sixRounds 0 (by decide) absorbed11 = quarter11_1 := by
  decide +kernel

private def quarter11_2 : Vector UInt64 25 :=
  #v[0xc2f12a44bfbc222, 0xea39cf8a307d1ef3, 0x8dc6f2306e20cb19, 0x219ad55cec7000ec, 0xbf874bd6815a8e80, 0x3a4368dbd248766e, 0xda4fb1c252af145f, 0x3619d73f2a39a122, 0x4f67eec3994f513d, 0xd825124d69a487a, 0x6a8d4a6373cc6caf, 0x846f8f990f74a095, 0x363d3fcb050d1bda, 0xe1ad31dd48a002a8, 0xdc44109222c65c71, 0xd81e74e768210c87, 0xc09e3e0abbf20441, 0xe1063a83569d7bf2, 0x42cfc6db977dd5b1, 0x528c9dfa5b7e8e78, 0x216126a09baeb505, 0x977c0ba7703d75cf, 0x693423d62bd02991, 0x3225157e7b1cffa, 0x997ed407001eba56]

private theorem rounds11_1 : sixRounds 6 (by decide) quarter11_1 = quarter11_2 := by
  decide +kernel

private def quarter11_3 : Vector UInt64 25 :=
  #v[0xa7a0c35ed520c03f, 0xc5183c230accad12, 0xff983812bedf1c20, 0x1fe01f7eedf14b5f, 0x9612c80d28c5cb0d, 0xf9bfa328b2978514, 0xa67218c2b4df5fef, 0x541a5c32d83979a9, 0x56f84fc7fe4fcdb6, 0xcf037a6d96a52bf2, 0x5ba9b03f0f2f22f5, 0x912545639878ec07, 0xcc55b9734cbc2a9b, 0xa12bba5797605891, 0x8a67b6d2166cebd8, 0xd8497a21dadce38b, 0x6ef7ac7103c58315, 0xfd4c064c92ac7ea7, 0xd5f7fa1c3ef2519e, 0x4cafdc7169a015d1, 0x1968ddb32db68e53, 0x11a5e19e717de65c, 0xa33a4cd78f9c3a05, 0xeec5c09ee9708201, 0x28e3d29fb3877bae]

private theorem rounds11_2 : sixRounds 12 (by decide) quarter11_2 = quarter11_3 := by
  decide +kernel

private theorem rounds11_3 : sixRounds 18 (by decide) quarter11_3 = state12 := by
  decide +kernel

private theorem perm11 : KECCAK.f1600 absorbed11 = state12 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds11_0, rounds11_1, rounds11_2, rounds11_3]
  rfl

theorem block11 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes11 ++ tail) state11 =
      KECCAK.Bytes.run 0 tail state12 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes11 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb11 ws)) := by
    rfl
  exact (step state11).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words11).trans perm11))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
