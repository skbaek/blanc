import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb030 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x60 0x57 0xe3 0xf 0x61 0x15 0x16 0xff)) 1 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80 0x40)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x60 0x10 0x60 0x52 0x1 0x82 0x4 0x60)) 7 (by decide) (UInt64.ofBytes 0x75 0x61 0x50 0x7f 0x52 0x1 0x82 0x24)) 8 (by decide) (UInt64.ofBytes 0x70 0x20 0x3a 0x65 0x6c 0x62 0x61 0x73)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x64 0x65 0x73 0x75 0x61)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x82 0x44 0x60 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x3 0x90 0x81 0x90 0x51 0x90 0x52 0x1)) 13 (by decide) (UInt64.ofBytes 0x60 0x33 0x5b 0xfd 0x90 0x1 0x64 0x60)) 14 (by decide) (UInt64.ofBytes 0x20 0x60 0x3 0x60 0x52 0x81 0x81 0x0)) 15 (by decide) (UInt64.ofBytes 0xff 0x60 0x54 0x20 0x90 0x40 0x60 0x52)) 16 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x4c 0x10 0x61 0x15 0x16))

private def absorbed030 : Vector UInt64 25 :=
  #v[0x560145aafbd61146, 0x5ecf5a3d37876a6a, 0x1212c8b008315134, 0x7da78236b1103b26, 0x67eed04ea0f798bc, 0x48e9754af7b361e1, 0x81dea7947b2466ec, 0x3bc370149d1da1b1, 0x57dd8b0bfb306ffc, 0xee31a1e03285daa7, 0x8d131eec950dbf94, 0xa3658cb926595397, 0xd4bf76c94bcedbfc, 0x4a0b3c072afdc8ea, 0x79c50ed5894b27c5, 0x4a38b6bd932ed622, 0x44ee01462791acb2, 0x60a2da793bed007c, 0xc9486bbd8e25bf0c, 0x3475ca53397f7bbe, 0x58337e912030b5a9, 0x2bf4b4ea308b3cbe, 0x734a4d054d2f929e, 0xfddfaf1a2549082c, 0xb50762c88b9b7c21]

private theorem words030 : absorb030 state030 = absorbed030 := by
  decide +kernel

private def quarter030_1 : Vector UInt64 25 :=
  #v[0xc33678d83f1e4c65, 0x3a6e6045002f84a5, 0xa613754d20c37111, 0x583e05ddb7e25c0a, 0x9a0040c87ce021b4, 0xbf6b8d9650d62225, 0x383ea3674a17cedd, 0xceb85c90bc7b87f0, 0x19188a55f61ec9c1, 0xef18f14b4e4daaf, 0xeb9021cac1cd2954, 0x5d397b0c9e040a6c, 0xbbe0932a15213653, 0x121003d3221b2a77, 0xfa17e52464112643, 0x8977883542f4749f, 0x43fc15e0c565d50f, 0x9d1d3571d6daa708, 0x4eb66a3b009938d2, 0x9bc6253d72f17e47, 0x6e2af143465e153f, 0x1d8fe0681ee30969, 0x26c80e998371b394, 0x37e636b4f61356e1, 0x384294c6555638d8]

private theorem rounds030_0 : sixRounds 0 (by decide) absorbed030 = quarter030_1 := by
  decide +kernel

private def quarter030_2 : Vector UInt64 25 :=
  #v[0x627bb2a1c45b62a2, 0x918b665eb62cb67f, 0x4be9ada18ea4aaee, 0x2f6d8149762d5894, 0xbe4a49d50fc7ab4b, 0x70136e911796cf6b, 0x7f30649e15617e5d, 0x584a09c0cc6f531d, 0xa3ca6d2ec54bcb40, 0x71a65f63f83b44d9, 0x8ce9f89bc79ebf56, 0x23ce440ca60de2ce, 0x1fbcfe92c0cd014c, 0xdc1c495958fbb48, 0xae918b93f15f9863, 0x8b8c316517f20edf, 0xcec27af6c510c98c, 0xad999504d9a35c5d, 0x4530deacac15ce6c, 0xdd87134154177c8d, 0xc99357aa820c5a2c, 0xdb327a8ed44a74fb, 0xc88037a748e63b2e, 0x3ce4679b3cff6c5b, 0x376e4766cc84eec1]

private theorem rounds030_1 : sixRounds 6 (by decide) quarter030_1 = quarter030_2 := by
  decide +kernel

private def quarter030_3 : Vector UInt64 25 :=
  #v[0xcbe3f4992dfc0614, 0xa577e259bcc1a983, 0x2bab8ccecf97dc7f, 0xc83684cd13204050, 0x8ecb649035e9650d, 0xc7750590064c2c1f, 0x27942be884ccc1b3, 0xfe33be30cd5ee00b, 0x40bec22e3aab50eb, 0x7c2bf8d4545d407e, 0x7d8d9a7a7b5fda7c, 0x457da027bf3f59, 0x8686103d00541b3, 0x609a36d42acbc18e, 0x36a245951e97a686, 0x2c8fd161ebe545d2, 0x10cd2a1a6854caf0, 0x5b0611e1f1490e21, 0xbea3a1a5919e624, 0x11b5a8a9bdff3eee, 0xafbdb4e44cad0356, 0xf5b6bd2265cb773c, 0x276e85fd20166b3b, 0xed2251bcc75871be, 0x4c084c548f49e1a7]

private theorem rounds030_2 : sixRounds 12 (by decide) quarter030_2 = quarter030_3 := by
  decide +kernel

private theorem rounds030_3 : sixRounds 18 (by decide) quarter030_3 = state031 := by
  decide +kernel

private theorem perm030 : KECCAK.f1600 absorbed030 = state031 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds030_0, rounds030_1, rounds030_2, rounds030_3]
  rfl

theorem block030 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes030 ++ tail) state030 =
      KECCAK.Bytes.run 0 tail state031 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes030 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb030 ws)) := by
    rfl
  exact (step state030).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words030).trans perm030))

private def absorb031 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x80 0x1 0x4 0x60 0x52 0x81 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x82 0x3 0x81 0x82 0x1 0x20 0x60 0x80)) 6 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x25 0x60 0x52)) 7 (by decide) (UInt64.ofBytes 0x39 0x91 0x25 0x60 0xc5 0x59 0x61 0x80)) 8 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x40 0x60)) 9 (by decide) (UInt64.ofBytes 0x73 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x0 0x60 0x16 0x84 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x52 0x20 0x60 0x3 0x60 0x52 0x81 0x90)) 14 (by decide) (UInt64.ofBytes 0x60 0x90 0x84 0x54 0x20 0x90 0x40 0x60)) 15 (by decide) (UInt64.ofBytes 0x60 0x57 0xcd 0x10 0x61 0x15 0x16 0xff)) 16 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40))

private def absorbed031 : Vector UInt64 25 :=
  #v[0xaee2ba88c939f2f6, 0xe60d8c521e3ede04, 0xda2da03b8d30928b, 0xb4b056d1df050390, 0xc41ec4d260d70057, 0x33e7948239c2d379, 0xb1ee3aba11f73a00, 0xf559df78b335db7d, 0x970dde9f65fddf42, 0x7b27f8093d279c47, 0x61cb81533253ff53, 0x61502271cb250bf7, 0x7bb6d32add02cda6, 0x3a75630b9d4ad59b, 0xf102ae343076fd0d, 0xc550656ce85d5fe5, 0x1e248c906c9d4361, 0x36dfd1f172226e5a, 0x905edf2a6ea90e88, 0xa50f095802658e2c, 0x30df5f8c90c3c926, 0x51833bfd9f69b234, 0xdc668ee4210f91, 0x59a2ea5d1454d515, 0x72f6e684af1b13d1]

private theorem words031 : absorb031 state031 = absorbed031 := by
  decide +kernel

private def quarter031_1 : Vector UInt64 25 :=
  #v[0xb0015e69b32406d0, 0x237e18c0afb8541c, 0x9ae3ea21020a4a59, 0xe94d6d814a048290, 0x7d372932e7c1b6a1, 0x455e0aab294686a7, 0xfc2221d5e15f29ed, 0x913d9b824d51f65e, 0x9723298ed9996ae7, 0x1515c4cc44e94c71, 0xd7f2a92f9e4aa1ee, 0x8f58207155ae1ece, 0x18324deb76fe1118, 0x6a45ecfaf2772436, 0x441508b6bae81ae, 0xd765ca86a4d69126, 0x4c0a741f47a091b3, 0x266606cbf26bac3a, 0x745cdd4cc845950c, 0x181ccd5fb27dd7a8, 0x2e2fa94fcfd9face, 0x573a9ccf9ed92e03, 0x657629d8eddc073b, 0x7f8533bf5b6b24c0, 0xcb2f94e7462e4bb5]

private theorem rounds031_0 : sixRounds 0 (by decide) absorbed031 = quarter031_1 := by
  decide +kernel

private def quarter031_2 : Vector UInt64 25 :=
  #v[0x88b1a8c575779e65, 0x926ec7ec80e6ab3b, 0xc1567787a7388f4b, 0x9c28ae44e0171a41, 0x664e2345a8c23933, 0xfc886e7f9f983237, 0xf79ff650361a840, 0xa18bd1b320bb2858, 0xd20ebdde453efe95, 0x1358a466057e90bb, 0x4d3f910e3617397d, 0x2673d02c1e887bdf, 0xb0016b33790b5f80, 0x529fc0a9ba56aab8, 0x7919a2ff37bab5c8, 0xe4f760439d0fa90e, 0xc49aa2e30ea076b3, 0xf45b1b8e391f0984, 0xe4d44e453b53a913, 0xdfdbcc9d7184e19, 0x562b104f9097e962, 0xa78e843072c983b2, 0xe7432e267c0faa7e, 0x1065aec99d8426a7, 0x64a85057dfcf85b1]

private theorem rounds031_1 : sixRounds 6 (by decide) quarter031_1 = quarter031_2 := by
  decide +kernel

private def quarter031_3 : Vector UInt64 25 :=
  #v[0xf46f7c0c55279149, 0x76a77c71aa0ca6ea, 0x67146b1c6aeff593, 0xc7d2418f432f52a, 0xd4613fa9b527724c, 0xedd6353840440a51, 0xfe15c5310aaf51e8, 0x92c2e90fd78df0b6, 0x5bc5fedef17c9e1e, 0xa37492a4ce5a95ff, 0xf67ba4f382eaa058, 0xba13f84fa4a65434, 0x32739cab9804afc4, 0xac1b9fd589ddd439, 0xf4deda6e5f1d9c28, 0x818563335ae08776, 0x7b40a9f255197757, 0x5631c457aabd3ec2, 0xe540d6caef104c3d, 0x2fd0b4b187b8d43c, 0xa3c9604968d4801d, 0xfba68c51550d5596, 0x57d33645ce5f5504, 0x294b21225b0c64e9, 0x5ac62236a1e48033]

private theorem rounds031_2 : sixRounds 12 (by decide) quarter031_2 = quarter031_3 := by
  decide +kernel

private theorem rounds031_3 : sixRounds 18 (by decide) quarter031_3 = state032 := by
  decide +kernel

private theorem perm031 : KECCAK.f1600 absorbed031 = state032 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds031_0, rounds031_1, rounds031_2, rounds031_3]
  rfl

theorem block031 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes031 ++ tail) state031 =
      KECCAK.Bytes.run 0 tail state032 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes031 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb031 ws)) := by
    rfl
  exact (step state031).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words031).trans perm031))

private def absorb032 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x1 0x4 0x60 0x52 0x81 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x3 0x81 0x82 0x1 0x20 0x60 0x80 0x80)) 5 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x25 0x60 0x52 0x82)) 6 (by decide) (UInt64.ofBytes 0x91 0x25 0x60 0xc5 0x59 0x61 0x80 0x1)) 7 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x40 0x60 0x39)) 8 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51 0x40)) 9 (by decide) (UInt64.ofBytes 0x3d 0x61 0x86 0x86 0x33 0xd8 0x10 0x61)) 10 (by decide) (UInt64.ofBytes 0x93 0x94 0x1 0x60 0x50 0x5b 0x56 0xb1)) 11 (by decide) (UInt64.ofBytes 0x80 0x7f 0x5b 0x56 0x50 0x50 0x50 0x50)) 12 (by decide) (UInt64.ofBytes 0xf2 0x3e 0x6f 0x79 0x7a 0x40 0x10 0x8c)) 13 (by decide) (UInt64.ofBytes 0xd2 0xa9 0x8e 0x63 0xc0 0x38 0xea 0xc7)) 14 (by decide) (UInt64.ofBytes 0xf5 0xe1 0xa9 0x3c 0x3e 0xc6 0xa1 0xb8)) 15 (by decide) (UInt64.ofBytes 0x81 0x3c 0xf7 0x9d 0xe5 0x4a 0xe8 0x6c)) 16 (by decide) (UInt64.ofBytes 0x5b 0x56 0x90 0x54 0xb 0x60 0x5b 0x56))

private def absorbed032 : Vector UInt64 25 :=
  #v[0x76704f3ef253cac2, 0xff15bc1fd3255651, 0xa5ce0148f6122b3a, 0x2f9474adcb21fdb2, 0xf0b1f8f103878f0f, 0xd44bc32f117ed712, 0x12bc416839e68def, 0x7f03579483643e38, 0xc850def446c95052, 0x3af43b3cd56bc401, 0xbe64c446dd6666cd, 0xd3676393f802cb51, 0xb9689b62c2a9c715, 0xc4be025e230e90fa, 0xb1b04aef9d333d1a, 0xad1172bc6cc697e, 0x4081534b6d763234, 0x6a781f4e180135ef, 0x9050cd5b7c5c0c10, 0x7b34e4491c01538, 0x9d45584e77dbaada, 0x8a09531dabf41857, 0x5bea59edd044961f, 0x7d8d8124bd315736, 0xcbf543107b4b4285]

private theorem words032 : absorb032 state032 = absorbed032 := by
  decide +kernel

private def quarter032_1 : Vector UInt64 25 :=
  #v[0x81c37e9e1b4beb0c, 0x5543c939a08612e0, 0x6f9205781221b06e, 0xc061a9faee45e8b1, 0x5d64a3ba529f16ae, 0xdba7b044b3460672, 0xe67eeb731c493fe4, 0xa26a3b62475a8283, 0x74ff4a117d3a6ab3, 0xfe01a7b5fd9a25dd, 0xe41e7f5752492854, 0x5c9eb642b5042fe2, 0xe2e31a13065ffd0b, 0xc4081ef81555b07, 0xa47e30d92d626a0e, 0x5eaeb4e81a3f37d0, 0xb656e0ac6bd93cbb, 0x1c48144cf3985f2d, 0x4972badd811c2c65, 0x93604746e9bd927, 0xcbcc6c76974ee18c, 0xbb092735b1649cd0, 0xcdb46a09fa2dd843, 0xc4d893f3097254fa, 0xb678a53df8141eb6]

private theorem rounds032_0 : sixRounds 0 (by decide) absorbed032 = quarter032_1 := by
  decide +kernel

private def quarter032_2 : Vector UInt64 25 :=
  #v[0x951006879c2fcac2, 0xf43b7e99c2ed16fd, 0x90fdeb6b954221d5, 0xebd49a8d108f89ed, 0x1fe0e5a8fc31b5e, 0x1f7e5517f89dfe7c, 0x34bf1304def2791e, 0x4b0b83908a3fb3d5, 0x8f73e130b9ea8dc5, 0x52156614d9555334, 0x2bf6325be534fd59, 0x883b0befbe644fd6, 0x588b44e8db19d01, 0x5220c5255dfd8eee, 0x5dc53449ad414da3, 0x8e8eeb64c03df08e, 0xce073f996f8d5505, 0x57fe4fb98d1b133c, 0xb091d7ef4a4b56bf, 0xe86f49986538c925, 0xd79ae733c2721ab3, 0x65e70625785ea4f3, 0x329d800e341822c1, 0x19a87e39a5054a68, 0x98cfd9107767feb1]

private theorem rounds032_1 : sixRounds 6 (by decide) quarter032_1 = quarter032_2 := by
  decide +kernel

private def quarter032_3 : Vector UInt64 25 :=
  #v[0x7635d1c05b755794, 0xd45870eacdd1563e, 0xf09e424cdf78e5b1, 0x77083cfe72b00aa, 0x623a69501a357412, 0x3200560e944caf4, 0x8147f582ee82b8b4, 0xf0294b89eeda45bf, 0x8a3aa190e07b608f, 0x5b3e403844bc2b6b, 0x3fb3cd46228f10f6, 0x2868f6178894d799, 0x82c7c1fbdca4f61a, 0xb969538f1ee267fd, 0x372bff3c4e7f737a, 0xaca020d7d1f0f571, 0xe5637a833be596f2, 0x2362e6fd19539323, 0x138c13b80a90069, 0x4dc8c9bbceab229, 0x7cc08daec9deb6ac, 0x238e0884e3f5433b, 0xc63f699cc22db5ac, 0xc183dfe73ee5df2e, 0xcc27d0e0164b1fc2]

private theorem rounds032_2 : sixRounds 12 (by decide) quarter032_2 = quarter032_3 := by
  decide +kernel

private theorem rounds032_3 : sixRounds 18 (by decide) quarter032_3 = state033 := by
  decide +kernel

private theorem perm032 : KECCAK.f1600 absorbed032 = state033 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds032_0, rounds032_1, rounds032_2, rounds032_3]
  rfl

theorem block032 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes032 ++ tail) state032 =
      KECCAK.Bytes.run 0 tail state033 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes032 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb032 ws)) := by
    rfl
  exact (step state032).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words032).trans perm032))

private def absorb033 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x54 0x2 0x60)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x60 0x57 0x7d 0x11 0x61 0x14 0x33 0x16)) 4 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x1 0x4 0x60 0x52 0x81 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x3 0x81 0x82 0x1 0x20 0x60 0x80 0x80)) 10 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x2c 0x60 0x52 0x82)) 11 (by decide) (UInt64.ofBytes 0x91 0x2c 0x60 0xe2 0x56 0x61 0x80 0x1)) 12 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x40 0x60 0x39)) 13 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51 0x40)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x60 0x16 0x81 0xff 0xff 0xff 0xff 0xff))

private def absorbed033 : Vector UInt64 25 :=
  #v[0x336ded8365754002, 0x32d0c75ec84c9ac5, 0x4ef53722aced3b7c, 0x3cc1823fd8b1000, 0x3f78ec94c336af13, 0x4110e114f411c8e7, 0x70ebd9dc31b1be53, 0x91e11bb13cdd5d5f, 0x988c2b9705a61512, 0xd868912e506777db, 0x4cf62d64158fd645, 0x99c197700fe85dd4, 0x2c2001126e711671, 0x8a62275ce099c66, 0x98cc8b1f12b005f6, 0xb769da813bc91447, 0xe63ba9a1ad52cf1b, 0xf409224997ea788b, 0x2fa7f8c8ac201286, 0x8713def91515d9ff, 0x8d400b165736af7, 0xa09e07a1177861b2, 0x72588d051d626a27, 0x1262f506eaae355a, 0x52cf1949749e7f01]

private theorem words033 : absorb033 state033 = absorbed033 := by
  decide +kernel

private def quarter033_1 : Vector UInt64 25 :=
  #v[0x737bbe45998b96fb, 0x6f7bd82dc7e96ebc, 0x2568b06c6d44ad13, 0x4e552e769e283096, 0xe67ca17205427abb, 0x2498917d385a019e, 0x660c7fc85c47c9a8, 0xef609244318a5d81, 0x37de28795e3b0797, 0x7642e49fc958717c, 0x773f21d7774c0a9e, 0x96ae8c8d19de08dc, 0xb1365fc5f2b1806, 0x359cbeb3da306902, 0x1fbefaf55c90132f, 0x9b653a01181909fa, 0x657035e25bb3d214, 0xc3d4637ddc3a087d, 0x781dc18b9056764d, 0xa2d7de96b2198448, 0xd5e59584cb8e70ba, 0xf7c574c5369431c2, 0x91c5af61f0d86d1c, 0x1ab293a714e4c62d, 0x4e89b9edc1571cff]

private theorem rounds033_0 : sixRounds 0 (by decide) absorbed033 = quarter033_1 := by
  decide +kernel

private def quarter033_2 : Vector UInt64 25 :=
  #v[0x6707b6ab56c708ce, 0xbc8c5e14a0f50ea5, 0x917eb6a99ed6e09f, 0xb94a2bac79a5c2aa, 0x222addd3501b8a1d, 0xdfac74bcfada172d, 0x40812a177727d95f, 0xf1fbf5926da64658, 0xd184af3742aa80b5, 0x4109215e3ca4557b, 0x1ce7bb3ae4bb84ff, 0x3dc51f603f9fe5a8, 0x36cd171704addf58, 0x499f7b443a5638a0, 0xd197d712c5951046, 0x1567d2b2726aab29, 0x8534444028df617d, 0xd7b45184372c921e, 0xbeb8eb94ae457aa7, 0x55c8046e8fb8b192, 0xe596b20eb94f6e24, 0x45d2a8ef6efed894, 0x9e79cdc81a6e5e6e, 0xc6e0d5e3e07eef3d, 0xa24cd0cbce18642f]

private theorem rounds033_1 : sixRounds 6 (by decide) quarter033_1 = quarter033_2 := by
  decide +kernel

private def quarter033_3 : Vector UInt64 25 :=
  #v[0x4dac4352d0f5caf7, 0x133ab8a538547bc3, 0x120354fafe52acc2, 0xd2c0f5b042a8a5b6, 0x18f4d8622a03bb3a, 0x1986563c3eb7619c, 0x2b1f3ec9d2e9cd3b, 0x7d0a1986b214348b, 0xf7ce4b36be6b5965, 0x2435746ed1bceb5, 0x12800f57d21c6e01, 0x9a0256caa5bf1227, 0xc8a54a4a97f36b06, 0x2603d6dded37137, 0x747c6a72b8b87dd8, 0xc6e0c73fc8927f9e, 0x18c07fd3dd17c739, 0xeb381b8a37037262, 0x1ed89c8753384528, 0x574fdcdf05daaa0f, 0x8da7f140b6f1fc99, 0x3a11c36592f2ac56, 0x826256ee39bf1fad, 0xfb28f42506a45ac9, 0x91fb89858b7679d0]

private theorem rounds033_2 : sixRounds 12 (by decide) quarter033_2 = quarter033_3 := by
  decide +kernel

private theorem rounds033_3 : sixRounds 18 (by decide) quarter033_3 = state034 := by
  decide +kernel

private theorem perm033 : KECCAK.f1600 absorbed033 = state034 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds033_0, rounds033_1, rounds033_2, rounds033_3]
  rfl

theorem block033 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes033 ++ tail) state033 =
      KECCAK.Bytes.run 0 tail state034 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes033 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb033 ws)) := by
    rfl
  exact (step state033).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words033).trans perm033))

private def absorb034 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x20 0x60 0x3 0x60 0x52 0x81 0x81 0x0)) 1 (by decide) (UInt64.ofBytes 0x54 0x80 0x20 0x82 0x80 0x40 0x60 0x52)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x7e 0x11 0x7f 0x51 0x55 0x90 0x16 0x0)) 7 (by decide) (UInt64.ofBytes 0xff 0xba 0xd9 0xa7 0x9a 0xbb 0x10 0x32)) 8 (by decide) (UInt64.ofBytes 0xf6 0xc6 0x55 0x2 0x82 0x26 0x20 0x17)) 9 (by decide) (UInt64.ofBytes 0xd8 0x2f 0x1c 0x9d 0x99 0xa8 0xb 0xc3)) 10 (by decide) (UInt64.ofBytes 0x90 0x91 0x4e 0x7c 0x13 0x48 0x28 0x8e)) 11 (by decide) (UInt64.ofBytes 0x60 0x54 0x1 0x60 0x5b 0x56 0x50 0xa2)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x1 0x74 0x90 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x12 0x61 0x15 0x16 0xff 0x60 0x4 0x90)) 16 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x80 0x40 0x60 0x57 0x7e))

private def absorbed034 : Vector UInt64 25 :=
  #v[0x87882a06f42eace1, 0xd2c8d94587b03ec0, 0x5db77234d007b02, 0xb8008da1cf7c6b7d, 0xe2a829ea27c532da, 0x1e3c0e0a87887444, 0x4288b50328b474fe, 0x4942b4af1aba6ccf, 0x656d96653931abea, 0xf6f46cc3f2889f92, 0xd50bd7d905405d13, 0x1be5300652ff9bb2, 0x88faeb0a7c56abe6, 0x32c98d90100892ef, 0x7a061e04b009014b, 0xa8bb05853feb480f, 0x7a8f0dd279024598, 0x4155df73a99b16c2, 0xd78fb98958fbdf87, 0x2a23ee18296ddb3d, 0x81943d6729ffe639, 0xe853ece0c249f884, 0x11fd1051d578e039, 0x6ac1af8e1de3db2f, 0x1e373188e6f1c747]

private theorem words034 : absorb034 state034 = absorbed034 := by
  decide +kernel

private def quarter034_1 : Vector UInt64 25 :=
  #v[0x49ac57777ea01efd, 0xd2964700da7b1eb7, 0x978b3e90f306fa10, 0x75f01341384f0ddd, 0xf96220d8f52826a8, 0x487287d4845a3cce, 0x324bbe4dbe7788eb, 0x66935cfd8b0779ce, 0x45446921aa44d2c9, 0xf046ba11363fc19e, 0x6710cd06cb0ff394, 0x1e0762b1f47337ff, 0x2d43b09e93d7396f, 0x7a39bc40605c9fcf, 0x7d0022db3fd21bbd, 0xbec03419097b40ac, 0xa6ca2151c026e586, 0xc1d68731991ab0f5, 0x59e5adf2e6b1937b, 0x22cb5bf3833dbd19, 0x6061d3f0b6fff83f, 0x9dc7034eff15bdd1, 0xa3beeb8e9e9e9e37, 0x7fb9f8a7ec0469cf, 0x93739b0dac8198be]

private theorem rounds034_0 : sixRounds 0 (by decide) absorbed034 = quarter034_1 := by
  decide +kernel

private def quarter034_2 : Vector UInt64 25 :=
  #v[0x65f5db5157ad9570, 0x4e7c531f50ce4828, 0x30a29d7c2a63af78, 0x4bac3288673fd392, 0xea133af42846035a, 0xee0bb786c4208657, 0x61a359b983d6c12f, 0xa3dd7114a9d2235, 0x63928aed674de4b5, 0x5a550882c0796cd2, 0x4fb590014782ef78, 0x8f735bcc46765783, 0x1f9085885b92bceb, 0xf35f4c90bb636fc9, 0xf8704b380555c9f4, 0xae82c8a2ae00e7b8, 0x45283104d2f7f29b, 0x443e2af41475ca8f, 0x81b1007d20cbd52e, 0xc87d59b3e81680a5, 0x46eb88df26614898, 0x7022c9e185c5ed3c, 0x377671059b30caa5, 0xf9dda3da592bf777, 0x7b27efcc3064502f]

private theorem rounds034_1 : sixRounds 6 (by decide) quarter034_1 = quarter034_2 := by
  decide +kernel

private def quarter034_3 : Vector UInt64 25 :=
  #v[0x6fbdc84135d728ee, 0x240e6b1b6d2c0358, 0x7bfd59eb5b2bd3f6, 0xb9bd3ba17e86c65, 0x8823476bcfa9d376, 0x67fb30c25a89bead, 0x26bfdb3401553e2c, 0xf566fd4e8c3fb5e6, 0xab64a2da6806e494, 0xf32ab747e8649d62, 0x60107c7e94777230, 0xedc9046c22935e3e, 0x66c3e9e78e8d4a5c, 0x14215e2bc29068de, 0xde7f9230a9eb4237, 0xb91aca712a0f968e, 0x54549224a3c6d589, 0x8b00b33c16d7a18, 0xf1f1d03e07dff19d, 0x4a7a84117c1f0b2, 0x84343626a9e499aa, 0xd3fc58ad6bda2584, 0x5a17f106ba0787a5, 0x4e5b371be86ef2b, 0x8ae0ae145a4cd426]

private theorem rounds034_2 : sixRounds 12 (by decide) quarter034_2 = quarter034_3 := by
  decide +kernel

private theorem rounds034_3 : sixRounds 18 (by decide) quarter034_3 = state035 := by
  decide +kernel

private theorem perm034 : KECCAK.f1600 absorbed034 = state035 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds034_0, rounds034_1, rounds034_2, rounds034_3]
  rfl

theorem block034 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes034 ++ tail) state034 =
      KECCAK.Bytes.run 0 tail state035 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes034 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb034 ws)) := by
    rfl
  exact (step state034).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words034).trans perm034))

private def absorb035 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x4 0x60 0x20 0x60 0x52)) 5 (by decide) (UInt64.ofBytes 0x7f 0x52 0x1 0x82 0x24 0x60 0x10 0x60)) 6 (by decide) (UInt64.ofBytes 0x65 0x6c 0x62 0x61 0x73 0x75 0x61 0x50)) 7 (by decide) (UInt64.ofBytes 0x64 0x65 0x73 0x75 0x61 0x70 0x20 0x3a)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x90 0x51 0x90 0x52 0x1 0x82 0x44 0x60)) 11 (by decide) (UInt64.ofBytes 0xfd 0x90 0x1 0x64 0x60 0x3 0x90 0x81)) 12 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x81 0x0 0x60 0x33 0x5b)) 13 (by decide) (UInt64.ofBytes 0x20 0x90 0x40 0x60 0x52 0x20 0x60 0x3)) 14 (by decide) (UInt64.ofBytes 0xe7 0x12 0x61 0x15 0x16 0xff 0x60 0x54)) 15 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0))

private def absorbed035 : Vector UInt64 25 :=
  #v[0x199b347e46b16725, 0x2acd9438e7f27661, 0x6889ccb4c06308df, 0x4e49a04f4ef84d92, 0xc4301ac28094b5dd, 0xdc5177ae5c1cd892, 0x66fec150f19eee77, 0xa457f9474cb3f388, 0xc83fd26ef9dd15b7, 0x3ad64b9cebb99d1e, 0x6d436e9fc7ef4459, 0xd2dde801491a09f6, 0xd1067de96a1bf72b, 0xb920120abcbe2140, 0x70f61193779a3ac1, 0x80d3ee1c3a257b28, 0x9cc5d3d3c5ad9d73, 0x70590f3366de1097, 0xefb640faa657f485, 0xe68aa0560a960e05, 0xa4c357e59f879347, 0x2a607d5eef11d0d2, 0xfe74c08d3ec04d62, 0xf26a755f88c0a9dc, 0xc69315309946276]

private theorem words035 : absorb035 state035 = absorbed035 := by
  decide +kernel

private def quarter035_1 : Vector UInt64 25 :=
  #v[0xb701c11c3a88281f, 0x5debe3d8142dd5cc, 0x217a6332569e8dde, 0xb80ebf52cde5ce90, 0x37d414fed0032bc9, 0x252b0be3d63bfbaf, 0x7c3de8af96650932, 0xbce9a4c4ff7e7f0, 0xb7b7a5cfb0324ff6, 0xf0fabd271c5eb5f8, 0xfc7446eba530b618, 0x239cd5c20f27a23f, 0x1a19b60bb90d5439, 0xdc27e42ef75372ca, 0x960e64d8877956f6, 0x6f0e8fcdb5be6d68, 0xce9263210aba450b, 0x8afd052edd783cbb, 0x6c8d6ffd42d29169, 0x26038b77f902bf92, 0xb8a54cbe51299b59, 0xb5985a3fd57e4601, 0xb84b5be29e769d6e, 0xc8f83d87d4a54395, 0x67251e6343b4c941]

private theorem rounds035_0 : sixRounds 0 (by decide) absorbed035 = quarter035_1 := by
  decide +kernel

private def quarter035_2 : Vector UInt64 25 :=
  #v[0x6834403271c4f071, 0x12cb84ef1f744ef9, 0xece46c6b027a031f, 0xef2f87c8263bb6b4, 0xd89691deee6bfcbf, 0x189ef0532437fa9e, 0xaa273aee55971fd1, 0x348f8192733028ad, 0xa9e273975de9f040, 0xc595a14ab801d517, 0x1805a810f15cb6b9, 0x33451bda428b2171, 0xd7481e0cb489890e, 0xdfc60bdfc403579d, 0xbbf122c9207a6295, 0xc36410952589f095, 0x2e374c06ee568aee, 0x1ed9513f51e11f8, 0x4316e7075e981c6e, 0x4c545850a899d438, 0x46ba68a80857fe4d, 0x10e135b0a1f033b1, 0x8d4d3a57a07fd97d, 0xc1bd5d74851fd038, 0x94ca62e3201b90a9]

private theorem rounds035_1 : sixRounds 6 (by decide) quarter035_1 = quarter035_2 := by
  decide +kernel

private def quarter035_3 : Vector UInt64 25 :=
  #v[0x1bf58f97203d91dd, 0x3a78cd8501d88bf8, 0xa0bab017b14428b0, 0x1ac017f314b6493e, 0x4625f41f0840af2b, 0x33977af84b4fa197, 0x5840e08f757abaf7, 0x846ca7f3093d5098, 0x5076643a3bbed90f, 0x26e6e7e544a8a234, 0x6d994a6c0b1bc8ac, 0x4ed8ecb77fac28f3, 0xadb3f6c0f70bf4f2, 0xece57f979a46ea0e, 0x76abc960bdaa76f1, 0xb3c31d05ed255052, 0x10bb90562a37f51a, 0xc23909e5acd86a80, 0x9882ec3dbfafc592, 0xf017e8e14280e351, 0xf6c32a2a19e9bbfa, 0x9f3077897db8b751, 0x762ba3654e2c78c8, 0x8cb732b8eac756bd, 0xa9bbf59171b6ee2d]

private theorem rounds035_2 : sixRounds 12 (by decide) quarter035_2 = quarter035_3 := by
  decide +kernel

private theorem rounds035_3 : sixRounds 18 (by decide) quarter035_3 = state036 := by
  decide +kernel

private theorem perm035 : KECCAK.f1600 absorbed035 = state036 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds035_0, rounds035_1, rounds035_2, rounds035_3]
  rfl

theorem block035 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes035 ++ tail) state035 =
      KECCAK.Bytes.run 0 tail state036 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes035 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb035 ws)) := by
    rfl
  exact (step state035).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words035).trans perm035))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
