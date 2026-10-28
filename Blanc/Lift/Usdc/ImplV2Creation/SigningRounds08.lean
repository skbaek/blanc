import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb048 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 2 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x2e 0x60 0x52 0x82 0x3)) 3 (by decide) (UInt64.ofBytes 0x2e 0x60 0xd0 0x57 0x61 0x80 0x1 0x20)) 4 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 5 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x16 0x81 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x7f 0x51 0x40 0x60 0x57 0xa2 0x19 0x61)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x60 0x80 0x80 0x1 0x4 0x60 0x52 0x81)) 15 (by decide) (UInt64.ofBytes 0x60 0x52 0x82 0x3 0x81 0x82 0x1 0x20)) 16 (by decide) (UInt64.ofBytes 0x61 0x80 0x1 0x20 0x60 0x52 0x81 0x28))

private def absorbed048 : Vector UInt64 25 :=
  #v[0xe3a022678da1bfe0, 0x9e18cf5112ffd148, 0x5cae23ffdb8d6b3e, 0x297cf45b8ae64d87, 0xe2c37ea39c3e486, 0x9d336e5deeca32f, 0x9f3ef0e9c3f63817, 0xfb9d65c2ecfb5b3, 0xb90c300acf2eab71, 0xd545a3cb4bde1425, 0xcd5cae45190e4c3d, 0xe695c153e9581727, 0x3c68557fce9d9a51, 0xc75a5d757ae201ed, 0x5d41484e10995412, 0x944c05b5796bf0c5, 0x3860474b68931abc, 0x8d1a74776a7f134c, 0x78a5f073ceb2b6c1, 0x8b1310c7194812b, 0xf891a86d0e61176d, 0x84ef8d6ea7f0260b, 0x5584e22c4628aa21, 0x7647a1633f22f3a2, 0x9f8685a9ce057291]

private theorem words048 : absorb048 state048 = absorbed048 := by
  decide +kernel

private def quarter048_1 : Vector UInt64 25 :=
  #v[0xb9a25ba8a3c782c5, 0xd5eb1b332b4cffeb, 0xd27ba1f32b327677, 0x31d922cea9bbb3ba, 0x75dd1d9f4ac96d0, 0xf9bea5fa02cc16cc, 0x10a6b59308fe66a2, 0x895c93497b5a28ef, 0x604fd66c861433b4, 0x696e488ec2b608b2, 0xb5ab9f226505807, 0xbc3cdd4a69776faf, 0x47ace4eb7604a283, 0x92320e22eee04839, 0x32935f4eff2b840, 0x914dee414540e6f3, 0xdbdbc76d15a64ed4, 0xc161fadef307e392, 0xb0299f9c9b0aa935, 0x14fcdc44ce9425c7, 0x2392224a0ed12ac3, 0xe20c1a3671d843ff, 0x271c1c7135b6feb0, 0xf87f3c8554513296, 0x6caf29c14b6586cb]

private theorem rounds048_0 : sixRounds 0 (by decide) absorbed048 = quarter048_1 := by
  decide +kernel

private def quarter048_2 : Vector UInt64 25 :=
  #v[0x80917d9e33d0b589, 0x26a296874cc30a5e, 0x73d301381ffbb240, 0xc44f0af3aa37682a, 0x37378d3d9a23de1, 0xc93f3a0b1d4cf513, 0xdb96e3b46ed49a91, 0x5c665b5f6724c21e, 0x1d974bbe0c17b8ed, 0x5022fdf0001afebe, 0x23fb58714e4dfd4f, 0xb01bbf20dd378622, 0xdb0098562c1d22ee, 0x6381e13c2ccbec37, 0xca1206b9e4d28022, 0xe442277ff1693cf6, 0x84729d922c3f3bf1, 0x279b9f0d0e6ee573, 0xa13b89738b3cc67f, 0x9c23f7adc4a4de33, 0x78cdb2d5d22573d, 0xfbf7b61a9e4739c, 0xfcc6bfede0054c01, 0xe4ddb2f6d60ad5e2, 0xc263e62a9745f5ce]

private theorem rounds048_1 : sixRounds 6 (by decide) quarter048_1 = quarter048_2 := by
  decide +kernel

private def quarter048_3 : Vector UInt64 25 :=
  #v[0xd58cf95b790fb5be, 0xf42c2d41d8df4960, 0x320338176bfa3ad1, 0x44adf06f707e1e91, 0x67b72b6f4a23849a, 0xb1591f758f0ed82b, 0x88e1846fd5b51b91, 0xd29d312c4df31357, 0x90f2b489564b49c, 0x25aee493ab295eda, 0x1d5c8bcd9347f7a6, 0x5b0e3d3ae0e10587, 0x46dac2787a643677, 0x40f4bb28ee2819fd, 0x168f86bce35851f3, 0x99f52395dc407175, 0x5416901b261381f2, 0x94ce673e7bc7c983, 0x4ecf18902ebea032, 0xcf8c801434404917, 0xe198b284bcb6c9b7, 0x9fe5bdf5e2668e3d, 0x65a1dd1c2595149a, 0x9ba059dbe9d0175f, 0xd3e0845404737ec1]

private theorem rounds048_2 : sixRounds 12 (by decide) quarter048_2 = quarter048_3 := by
  decide +kernel

private theorem rounds048_3 : sixRounds 18 (by decide) quarter048_3 = state049 := by
  decide +kernel

private theorem perm048 : KECCAK.f1600 absorbed048 = state049 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds048_0, rounds048_1, rounds048_2, rounds048_3]
  rfl

theorem block048 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes048 ++ tail) state048 =
      KECCAK.Bytes.run 0 tail state049 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes048 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb048 ws)) := by
    rfl
  exact (step state048).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words048).trans perm048))

private def absorb049 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x40 0x60 0x39 0x91 0x28 0x60 0x3d 0x59)) 1 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x91 0x1)) 2 (by decide) (UInt64.ofBytes 0x61 0x51 0x87 0x5b 0xfd 0x90 0x3 0x91)) 3 (by decide) (UInt64.ofBytes 0x20 0x60 0x90 0x4 0x60 0x90 0xb5 0x19)) 4 (by decide) (UInt64.ofBytes 0x5b 0x56 0xc7 0x53 0x61 0x90 0x1 0x8b)) 5 (by decide) (UInt64.ofBytes 0x60 0x90 0xc9 0x19 0x61 0x51 0x86 0x50)) 6 (by decide) (UInt64.ofBytes 0x61 0x90 0x1 0x8a 0x20 0x60 0x90 0x5)) 7 (by decide) (UInt64.ofBytes 0x61 0x51 0x85 0x50 0x5b 0x56 0xc7 0x53)) 8 (by decide) (UInt64.ofBytes 0x20 0x60 0x90 0x7 0x60 0x90 0xdd 0x19)) 9 (by decide) (UInt64.ofBytes 0x5b 0x56 0xc7 0x53 0x61 0x90 0x1 0x89)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0x7f 0x54 0x80 0x6 0x60 0x50)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x60 0x16 0x0 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x8 0x60 0x55 0x90 0x17 0x16 0x87 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x7f 0x54 0x80))

private def absorbed049 : Vector UInt64 25 :=
  #v[0xf84f06c9cf0f9110, 0x385e38ad2b038d1b, 0xfb067ebe81109aef, 0x950f4e7f8f122469, 0xfa67043a0bf0ebb8, 0x99e702b626c16e16, 0xa6c3e54df0470af5, 0xbba88cea9a84729a, 0x1f80d277218db965, 0xce362af923d17082, 0x9a691f8a317bbc1b, 0xec38cbac89da8322, 0xb1ac4d8894c935d9, 0xad4cf9c37851fa90, 0x1aab4f5894f4cfb1, 0xfb41bcbf694718fb, 0xf7dced8993d0bec0, 0x8f69f825c3e036fc, 0x4706dd93be1c880c, 0x11f5ec638b730ebd, 0x531e85482b8930e, 0x259ef724d7a71490, 0xe68d0770fb5f435f, 0x435c6e4d9f0747c9, 0x8b3ea3c491a984a]

private theorem words049 : absorb049 state049 = absorbed049 := by
  decide +kernel

private def quarter049_1 : Vector UInt64 25 :=
  #v[0xfd2a25a897fa05c4, 0xd28f178076730e01, 0x4ea7f7441470aaa1, 0x277af5f0bc30a9d5, 0xdb0c04cf6de2fdde, 0x1b598130bf9360a0, 0x16a3f25c12f396e5, 0x76c004e3a1e40dd2, 0xa88768dca3e16aaf, 0xde1cbd5649b5c919, 0xa392a29af09db9db, 0xa2855105fa5a8e6b, 0x80dc2eab031dfb95, 0x8d1412adddc955e7, 0x52c733cb40e40876, 0x6e18a484d79ac65a, 0x9fbfb9866063d134, 0xa7e190d19d2abb94, 0x391f367881fe432a, 0x12dfb481ecbd17c6, 0xb7bd48d1df7f4a2, 0xb2a45d2eef44f31f, 0x9cf929f604986ac8, 0xe27a66d36a3afab6, 0x92da85216edb6aad]

private theorem rounds049_0 : sixRounds 0 (by decide) absorbed049 = quarter049_1 := by
  decide +kernel

private def quarter049_2 : Vector UInt64 25 :=
  #v[0xa9fcb53cb2058528, 0xa5d1a43bda85ab47, 0xf0d5e3d2e7fdf3d, 0xea01d14df1f93463, 0xcad471a912ef4950, 0x9d13a6e45b06adee, 0x9b11fedd91531728, 0xfef1d3afb2880dfd, 0x18300a9137464cb3, 0x6104c299f4bb3d28, 0x589b8cfcc38133fa, 0xfe2952434ffefd90, 0xec4b2525ac08ad25, 0xa7181a8b78695f14, 0x8d92bf0aad9df6e4, 0xf3d11374e48bc221, 0xbcfa3e6f42c7872b, 0xb2af3fbafcf7bcb1, 0xce5ee3742f3466ea, 0x9501ca5d14301cff, 0xffc83aba9273d792, 0xef7eda60091bed89, 0x950cbf316abc75c8, 0xdafbef92a41ab6e6, 0xa7929cb9d466a8bf]

private theorem rounds049_1 : sixRounds 6 (by decide) quarter049_1 = quarter049_2 := by
  decide +kernel

private def quarter049_3 : Vector UInt64 25 :=
  #v[0x6c5f8cb7b0e3227a, 0x2cd9d8eb1b198924, 0x866203deaf5f4aa7, 0xf58a00f9da237b98, 0xd83136aa21317f, 0x2576a0238c11fe2e, 0x9eb0d96654786ae7, 0xdd87cfa06faa0797, 0xdd9175ebd6b1df5d, 0x9c7cee6f889286ab, 0x5a37a4d45288981d, 0xa00191ef565da4df, 0x40aff52c8e4e764d, 0x6397eb8e854e904c, 0xc27bbd8925ea1105, 0x3fd178224b3b53c, 0xdded3f56e1833934, 0x992b736c696be73a, 0xdbc1101d139bbdac, 0x83be78166cf421fd, 0xe5330ec1b5e236cc, 0x68020a95a3dad584, 0x4ea9c74f57ff171e, 0x1ecd5f821f02bac4, 0x56690b1432013fee]

private theorem rounds049_2 : sixRounds 12 (by decide) quarter049_2 = quarter049_3 := by
  decide +kernel

private theorem rounds049_3 : sixRounds 18 (by decide) quarter049_3 = state050 := by
  decide +kernel

private theorem perm049 : KECCAK.f1600 absorbed049 = state050 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds049_0, rounds049_1, rounds049_2, rounds049_3]
  rfl

theorem block049 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes049 ++ tail) state049 =
      KECCAK.Bytes.run 0 tail state050 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes049 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb049 ws)) := by
    rfl
  exact (step state049).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words049).trans perm049))

private def absorb050 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0x81 0x90 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x90 0x91 0x16 0x81 0x87 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x80 0x1 0x60 0x55 0x92 0x90 0x17 0x91)) 8 (by decide) (UInt64.ofBytes 0x90 0x17 0x16 0x84 0x86 0x16 0x82 0x54)) 9 (by decide) (UInt64.ofBytes 0x16 0x91 0x90 0x54 0x80 0x2 0x60 0x55)) 10 (by decide) (UInt64.ofBytes 0x90 0x17 0x91 0x90 0x91 0x16 0x84 0x91)) 11 (by decide) (UInt64.ofBytes 0x6c 0x41 0x61 0x81 0x77 0x1a 0x61 0x55)) 12 (by decide) (UInt64.ofBytes 0x54 0x80 0x8 0x60 0x50 0x50 0x5b 0x56)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x0 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed050 : Vector UInt64 25 :=
  #v[0xe56b5b6fa026536d, 0x14522d1b20f73abc, 0xa55d73f802792dc9, 0xe3a800d4636b3aa1, 0xcf098cdb74ab89b4, 0x43ad0206d1dc04f8, 0x2b2657b5a0ddea04, 0x89675609c6e749fb, 0x30920fb75e85fe92, 0xcb6f9d5c062ce02a, 0xf0e832ad2e1070ff, 0xb596d2cb12a9682c, 0x98495cc4921876b1, 0xa1c95248bd0724eb, 0x9b16986af21f79e4, 0x2b6fb2d4500f376e, 0x6142570b20673905, 0x2fae8098b6d04452, 0xff5246c6bf6ecba9, 0xdf4815a622dc5bbb, 0x85623a7bef36d23e, 0xd0c5f9fd7312cf0e, 0xbf323108eae43ee3, 0xc546b4533867eab8, 0xe27554c2d7ff31b4]

private theorem words050 : absorb050 state050 = absorbed050 := by
  decide +kernel

private def quarter050_1 : Vector UInt64 25 :=
  #v[0xe55377409c38cb2a, 0x24bad4b417b3bd94, 0x467752a1e4d78fb5, 0xb0216cd9b0af1bca, 0x1343f732ab3e98b3, 0x7a49c8bb1801b647, 0xc5c595564e90d852, 0xef2afe63ed4568d8, 0x181e433e124793b4, 0xe9dee89a949bf9d9, 0x833130ab32187a2b, 0x12e8c3149a7dbec5, 0x1b15e5e86043c153, 0xc1357167e0f8cd59, 0x297396833c791157, 0xabfe91f5497b00eb, 0x9e6377f74a9e6480, 0x6f3862fdc9de0710, 0x2b8a1ca34b15aaef, 0x7657e8b590a8d9bf, 0xd03617ed4b53bab, 0x20df19a81cb4bb90, 0xea090b52e16ed302, 0xd6f26cf4fbd2b218, 0x1c186aa32b36653]

private theorem rounds050_0 : sixRounds 0 (by decide) absorbed050 = quarter050_1 := by
  decide +kernel

private def quarter050_2 : Vector UInt64 25 :=
  #v[0xfa5a7c56547c6c7b, 0x211145abd68e0800, 0x500f22b7f9f71dc8, 0x48b9e58f363d0a25, 0xc69c33f75b53e1d0, 0xca2d3cc53d1a2b6e, 0x2a7720b1df769df3, 0x27ee6836b2146bdb, 0xc78c9e3ad5bb4935, 0x11f4b197211cfd26, 0xe486cd8e95ff650c, 0xb810330431c57416, 0x9cc22390771e167d, 0xe1d06aae16ec1d85, 0x1a5025ce68b90f8b, 0xef45261a15e193ce, 0xa88e7a337f87e7c8, 0x105f291005736ee0, 0x370dadcc6348f572, 0xbad5cd06c7325995, 0xeffb751fa6ea13f3, 0x3284fbc2bcc9bef8, 0x9ff7b9df9d243d4a, 0xc654525c542fa12a, 0x8baf6318be32864d]

private theorem rounds050_1 : sixRounds 6 (by decide) quarter050_1 = quarter050_2 := by
  decide +kernel

private def quarter050_3 : Vector UInt64 25 :=
  #v[0xf50111b2598b31e2, 0x55b499de5d4bda74, 0x5df94ddf4be7b9e6, 0x2f1f5d4339f8f8c2, 0x91cbe9f9d7cfc670, 0x942ce85ebf91fa03, 0xb4e5531d08fde197, 0x6abad4bae009345f, 0x89528292edbe22ce, 0x2d4117f4c212d02e, 0x70e8356143a6aed9, 0x4bfd94776c35b9a8, 0xf59d9a8ad9dc63bf, 0xaee32c583fbbf0df, 0x551f5dbe5c42cdca, 0xbafaa89b9e7764ca, 0x3e409019509e54d7, 0x16258310e364247b, 0x13221ece49375767, 0xa076ff535a4ba51d, 0xb7a71f2727ddbac, 0xb46709e42e87f97d, 0x6af9e5a5ee03befe, 0x4567a705edca4148, 0x8616d177ba314b48]

private theorem rounds050_2 : sixRounds 12 (by decide) quarter050_2 = quarter050_3 := by
  decide +kernel

private theorem rounds050_3 : sixRounds 18 (by decide) quarter050_3 = state051 := by
  decide +kernel

private theorem perm050 : KECCAK.f1600 absorbed050 = state051 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds050_0, rounds050_1, rounds050_2, rounds050_3]
  rfl

theorem block050 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes050 ++ tail) state050 =
      KECCAK.Bytes.run 0 tail state051 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes050 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb050 ws)) := by
    rfl
  exact (step state050).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words050).trans perm050))

private def absorb051 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x1 0x74 0x16 0xff)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x50 0x55 0x90 0x17)) 4 (by decide) (UInt64.ofBytes 0xff 0x73 0x54 0x8 0x60 0x5b 0x56 0x50)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x60 0x5b 0x56 0x81 0x16 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x54 0xe 0x60 0x5b 0x56 0x81 0x54 0xf)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x56 0x90 0x16 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x74 0x90 0x0 0x60 0x54 0x1 0x60 0x5b)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x1)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x60 0x4 0x90 0x0 0x0 0x0 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x60 0x57 0x8b 0x1b 0x61 0x15 0x16 0xff))

private def absorbed051 : Vector UInt64 25 :=
  #v[0xb62e39c919a5cfb6, 0xeedd91ee9f8fbe02, 0x8f7e67afa377eeae, 0x59d90624734fc25, 0x560ddc7f99deea88, 0x3c4bf570ff1a238c, 0x50c78418c38586e0, 0xf4d8fead85c37d6c, 0x72f2116e14c2af58, 0xffa2ee633875a22e, 0x6e68c4a223ed2ec6, 0x20cf3e88edf69efc, 0x67913546599169c6, 0x76dad4921ef156dd, 0x81550bcd1cf7917c, 0xa1288259eec47a9, 0x361b1a70a0d0a11, 0x41faf0ca9633f586, 0x4601f49faaeaa7b5, 0x2a63cf254f03652b, 0x4921c844c3af317f, 0x6eeec309c23840e1, 0x5324816de51203c7, 0xfd29f30c38f4f1c3, 0xc44721c7bfa80302]

private theorem words051 : absorb051 state051 = absorbed051 := by
  decide +kernel

private def quarter051_1 : Vector UInt64 25 :=
  #v[0x56c8a5cf527312f8, 0x5ed0a0af7dd2159a, 0x39464dab72adfc5a, 0xc14b9803b7b69b61, 0x81399a11a4e478a9, 0x794676fe5526bbc1, 0x90d8b8a720642aae, 0x1e4614551046e155, 0xdb3e1e146c750a1f, 0x95912c763c3b3255, 0x1d2b861a7546423b, 0xb37518495e972470, 0x96d553539cd46619, 0x16dabc41ce60f49c, 0x9629a9c7225aab93, 0xaee4785a0dc61d63, 0x4a20c496b05706be, 0x462c03ce93ead6b5, 0xd896cd98d5e5ee46, 0x73d5aa62f0b939e7, 0xc5191853b8445e0d, 0xdd1f275cb680b7ae, 0x57973006546fcc79, 0x5914a7792c4c73e2, 0xb097183fc11c4436]

private theorem rounds051_0 : sixRounds 0 (by decide) absorbed051 = quarter051_1 := by
  decide +kernel

private def quarter051_2 : Vector UInt64 25 :=
  #v[0x76d006bf08884347, 0x9b16744a3134902e, 0x685ce8888eae52a7, 0x9cdb0e2a359db28f, 0x76cfb318879f66d4, 0x95eb12ccc083736a, 0xd6559c2597a3217d, 0x8256356bbfccac72, 0x8b8dadf16c119843, 0x3362484dac90fe19, 0xff138ecf4a221d78, 0x30dcbdab79d56495, 0x330160d9328db5b5, 0x225939f42eaefed4, 0x10d3c42e677e90fa, 0x6b7101e7c13780b0, 0x3a7f86809dbced47, 0x2103f54a55e84080, 0x82c35613fea1b65a, 0x1d60b2b88ca4d7, 0xf863f5ca56a20852, 0x208439b20e3faa99, 0x2d7f253463dff8c6, 0xd094159c9790400a, 0x519d26d679d9e89e]

private theorem rounds051_1 : sixRounds 6 (by decide) quarter051_1 = quarter051_2 := by
  decide +kernel

private def quarter051_3 : Vector UInt64 25 :=
  #v[0x8a051ed9420895a8, 0x44340f438f5b04a7, 0x64326ebfd2d659b6, 0x9403bda11ba7460c, 0x327e08f6221d794f, 0x708f0974c59c7e50, 0x3010c9b12a68a943, 0x4ced11f1d5442c0d, 0x16a1cc883a8927b2, 0xe735ac23eb57f72, 0x8d784387dc777356, 0x13976171e912a618, 0x2bcae8ee844f1203, 0x4bfc30929dc8c27e, 0xe8022fff4022f05e, 0xe1e94d2a477e2638, 0x8c565595e93d38cc, 0xa28a83efb13a6444, 0xc521093de91b3ec, 0xdce94b2d6b30d05d, 0x8514659df88d064f, 0x3e0c197bbefec643, 0xe4419cef4452da8c, 0x48e8c58b17066ce7, 0xa302e47ea64b09ef]

private theorem rounds051_2 : sixRounds 12 (by decide) quarter051_2 = quarter051_3 := by
  decide +kernel

private theorem rounds051_3 : sixRounds 18 (by decide) quarter051_3 = state052 := by
  decide +kernel

private theorem perm051 : KECCAK.f1600 absorbed051 = state052 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds051_0, rounds051_1, rounds051_2, rounds051_3]
  rfl

theorem block051 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes051 ++ tail) state051 =
      KECCAK.Bytes.run 0 tail state052 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes051 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb051 ws)) := by
    rfl
  exact (step state051).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words051).trans perm051))

private def absorb052 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x80 0x40)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x60 0x10 0x60 0x52 0x1 0x82 0x4 0x60)) 6 (by decide) (UInt64.ofBytes 0x75 0x61 0x50 0x7f 0x52 0x1 0x82 0x24)) 7 (by decide) (UInt64.ofBytes 0x70 0x20 0x3a 0x65 0x6c 0x62 0x61 0x73)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x64 0x65 0x73 0x75 0x61)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x82 0x44 0x60 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x3 0x90 0x81 0x90 0x51 0x90 0x52 0x1)) 12 (by decide) (UInt64.ofBytes 0x60 0x33 0x5b 0xfd 0x90 0x1 0x64 0x60)) 13 (by decide) (UInt64.ofBytes 0x20 0x60 0x3 0x60 0x52 0x81 0x81 0x0)) 14 (by decide) (UInt64.ofBytes 0xff 0x60 0x54 0x20 0x90 0x40 0x60 0x52)) 15 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0xf4 0x1b 0x61 0x15 0x16)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51))

private def absorbed052 : Vector UInt64 25 :=
  #v[0x1e87136b51d546f7, 0xaf4ab457ab2468ce, 0x13968dad2a62359e, 0x2395b8befa64570b, 0xee78f794a74f9f8, 0x43b4a3a754b81bd6, 0xb63136e8ed95587a, 0x23ef3e8139ca3b2f, 0x6568837d3559fca7, 0xfd9960caddbf0f73, 0x27f58488ac85507d, 0xedb7dfed5c1727d4, 0x312daaccb3ab9b9e, 0x762f7aa1a42f5efa, 0xd76681fe89c607f3, 0xd1f72b1a0edfdf14, 0xce51eb03dd6d4c4d, 0xbc0e7cf411684a1b, 0x1a192378e5574113, 0xc04b0bddb042e888, 0x5559ad23096f35d1, 0x3f5039ee8b7e5c35, 0x48290312a736f767, 0xfd8d0e98c9a22402, 0xfd1980f73b438614]

private theorem words052 : absorb052 state052 = absorbed052 := by
  decide +kernel

private def quarter052_1 : Vector UInt64 25 :=
  #v[0x8600e2ce7d791c97, 0x3bcc973ab9cabeca, 0x9bfeffbda6f07125, 0xb9bebf6a74b8f065, 0xe54162c13354c5b6, 0x34608f208140a3df, 0xa2566b7cae84d867, 0x4c3fcf8ab23626bc, 0x77b6a0b7ffe8d9de, 0xa97039fd9dca645f, 0x148c66b5aa3a7b45, 0x56792321bea4158f, 0x87ff1e29d28b17dd, 0xe967b4345dce22d9, 0xce7627a70c3b7390, 0x9ec2469c9fd761a6, 0x2c240abe785a22f4, 0x788745ec9d85e84e, 0x7180ce03dad00d93, 0xb7f20591a3c67147, 0x521688dc21760c3c, 0x16e55be89d4b13bc, 0x4677c6b17895c8ff, 0xd045b039656c2c2b, 0xbf772885fbe4cc90]

private theorem rounds052_0 : sixRounds 0 (by decide) absorbed052 = quarter052_1 := by
  decide +kernel

private def quarter052_2 : Vector UInt64 25 :=
  #v[0xf7366003184ed5b6, 0x1eaa744d9121017d, 0xf06967a2055e6dae, 0xb81ae577b3321edc, 0xcea28220c7581143, 0x1e1509f43ef08877, 0x297716b787875d7f, 0xcc58af8f4963d696, 0xeca6204c00f85f78, 0xbb9275677e3404e0, 0x408b59e700fb4bfb, 0x3e5e8019ac621c4, 0xcfcf06e4b7ed6849, 0x41c3ddd7feeb0211, 0xe157e55c22170db8, 0x13ee1024376ecafb, 0x7191708d9cf8d13b, 0xb54c00f751d10b74, 0x99cb3e24bf8fbe6a, 0x453628852b24ce7d, 0xcb8f8e8d099a501c, 0x915ce0f0f3646592, 0x7b2ddc23ef12faf7, 0xe38f02e62c0c7e27, 0x1f812f32a0f341d8]

private theorem rounds052_1 : sixRounds 6 (by decide) quarter052_1 = quarter052_2 := by
  decide +kernel

private def quarter052_3 : Vector UInt64 25 :=
  #v[0xcafbe4b1cf0bba0, 0x2d03ed60b2228ee6, 0xa75c02946e647231, 0xfda8f8720484c151, 0xd715d4deec19eeab, 0x30ecfdeaca7bc991, 0x2d981f62025b0590, 0xb1af18c6aa1f38a8, 0x500184f851ef8972, 0x6336972cf7ab6f9d, 0xe431086ace910ec7, 0xc542e5398ed205e2, 0x3a23fb5cf206d66d, 0x3710e58fb40d874d, 0x973e083da44d2602, 0xa7ed1e955f174945, 0x99c0f7a905a51fcd, 0xc8d7289956abf89a, 0x70968aa9c8bf6aa2, 0xade8b870fc6764d8, 0x30892f8dd9012d90, 0xfc4927c652acdb18, 0xc3ff16959cfd4572, 0x9b85398efb5c247b, 0xd14dd7f2b5bbb2ab]

private theorem rounds052_2 : sixRounds 12 (by decide) quarter052_2 = quarter052_3 := by
  decide +kernel

private theorem rounds052_3 : sixRounds 18 (by decide) quarter052_3 = state053 := by
  decide +kernel

private theorem perm052 : KECCAK.f1600 absorbed052 = state053 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds052_0, rounds052_1, rounds052_2, rounds052_3]
  rfl

theorem block052 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes052 ++ tail) state052 =
      KECCAK.Bytes.run 0 tail state053 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes052 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb052 ws)) := by
    rfl
  exact (step state052).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words052).trans perm052))

private def absorb053 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x80 0x1 0x4 0x60 0x52 0x81 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x82 0x3 0x81 0x82 0x1 0x20 0x60 0x80)) 5 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x25 0x60 0x52)) 6 (by decide) (UInt64.ofBytes 0x39 0x91 0x25 0x60 0xc5 0x59 0x61 0x80)) 7 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x40 0x60)) 8 (by decide) (UInt64.ofBytes 0x73 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x0 0x60 0x16 0x84 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x52 0x20 0x60 0x3 0x60 0x52 0x81 0x90)) 13 (by decide) (UInt64.ofBytes 0x60 0x90 0x84 0x54 0x20 0x90 0x40 0x60)) 14 (by decide) (UInt64.ofBytes 0x60 0x57 0x75 0x1c 0x61 0x15 0x16 0xff)) 15 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed053 : Vector UInt64 25 :=
  #v[0xaed858959716887f, 0x8abe6c3add4618fa, 0xf19523c32213a8aa, 0x756da7da0acadac9, 0x51e0aafc96503be3, 0x155f57bb490db811, 0x150f7e49e0e5572f, 0x1d81502a3d3307aa, 0x70a20c05b47f2025, 0x1ee02e634307d824, 0xe162f68010463d1e, 0x56f66b532b957b4c, 0x8007151780091bd3, 0x967681cb1cb5d988, 0xb997fb4449c0d437, 0x9193ecd2a0b579bf, 0x5926a124421e4c5, 0x979889028f61e31b, 0x528471e02de77abd, 0xd99fc44a0527fd96, 0xb6fbd08c4f7b9b00, 0xac1bb7a23615e094, 0x8e9897d8636edb40, 0x28a562b8dd50831a, 0xccf645bd990a1edc]

private theorem words053 : absorb053 state053 = absorbed053 := by
  decide +kernel

private def quarter053_1 : Vector UInt64 25 :=
  #v[0xa45a657cdd283d77, 0xfc944b2b1fee1b38, 0x8908916648de3c2e, 0x7149341c0ca60fa1, 0x2d3ad791ecff5ff0, 0x84b40b583e859b43, 0xb85988da9aac14b5, 0xe76a1950d31e06f1, 0x3f98961e5cb7b9ad, 0x533572c0847e7d03, 0xe5a15d99c9e8080f, 0x92d5ebaa5386cda3, 0x26392d9eb3c718dc, 0xa75515d31163fd1b, 0xa2c9af4e3fd11a0f, 0x685c44bdd2819f22, 0xa21e4e68ab56f1bd, 0x69ab30571519bbd9, 0xf42d30afdc52c4f1, 0xe7607f4a79d05709, 0x24fe5105cf99f13b, 0x93ce56c72a76cc41, 0x387bb82d17dd783f, 0xeb08bc8fb337e377, 0xa64b562bf7d54b12]

private theorem rounds053_0 : sixRounds 0 (by decide) absorbed053 = quarter053_1 := by
  decide +kernel

private def quarter053_2 : Vector UInt64 25 :=
  #v[0xb34f5b694a512b81, 0xa415f5e629e32e46, 0x8e15205ec55d9bed, 0xc3e6f032c9c57f9c, 0x66a9c34ddd026bc1, 0xd470b7df1f1fb858, 0xc7276d8540b856d, 0xde7f88da728ea6f4, 0xf9d2c13eca0b2075, 0x250a37bdce288cea, 0xbc063d9787dd34e3, 0x65fd1873f18541e6, 0x9e232d150792ef64, 0x65b7df6b846e6aa0, 0x3b0593167b124df3, 0x63481b5765705eaf, 0xae74428d04e43d0, 0xca230aee324bc447, 0x15a36398c95dd65d, 0x94ed9731d364440e, 0x21c2bf4b7862ce14, 0x19ee0dd2999eda52, 0x9883aef738e7c667, 0xadfbd4c6aaedca7e, 0x32d39b5c648b76e2]

private theorem rounds053_1 : sixRounds 6 (by decide) quarter053_1 = quarter053_2 := by
  decide +kernel

private def quarter053_3 : Vector UInt64 25 :=
  #v[0x83e5013f78000a92, 0x8c32a454fff19990, 0x526b381788b22fcf, 0x6421a64236c68bee, 0x1a98444ed0b3319e, 0x1c7ce101961b1579, 0xa755663b94593807, 0x5cdadb907bee2e22, 0x1b6104c135131f96, 0xaa72258388a33407, 0x41a7295fbdfccdbf, 0x5d72dbd09c62bc3c, 0x576e9f3ec5b4351c, 0xe31452f11a1653d7, 0x8dd52502a6796124, 0x8ad9ff0a4152bfc1, 0xad28d6ea5cd4167d, 0xa02868ad4daa0128, 0xfef0b338a1a8e68c, 0x5dc7f48e1aa5c36d, 0xd727ef2c55c3c14f, 0xe39def403d0dfb2e, 0x74bd3913790b97f3, 0x78ea3f221d6682c4, 0x7ee4510915ef3e12]

private theorem rounds053_2 : sixRounds 12 (by decide) quarter053_2 = quarter053_3 := by
  decide +kernel

private theorem rounds053_3 : sixRounds 18 (by decide) quarter053_3 = state054 := by
  decide +kernel

private theorem perm053 : KECCAK.f1600 absorbed053 = state054 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds053_0, rounds053_1, rounds053_2, rounds053_3]
  rfl

theorem block053 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes053 ++ tail) state053 =
      KECCAK.Bytes.run 0 tail state054 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes053 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb053 ws)) := by
    rfl
  exact (step state053).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words053).trans perm053))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
