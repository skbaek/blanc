import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb114 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 1 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x26 0x60 0x52 0x82 0x3)) 2 (by decide) (UInt64.ofBytes 0x26 0x60 0xcf 0x55 0x61 0x80 0x1 0x20)) 3 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 4 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 5 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x54 0x0 0x60 0x5b)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x16 0x83 0x92 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x83 0x20 0x60 0x16 0x83 0x91 0x52 0x81)) 10 (by decide) (UInt64.ofBytes 0x7 0xe0 0x8b 0x7f 0x51 0x80 0x52 0x1)) 11 (by decide) (UInt64.ofBytes 0xcd 0x44 0x13 0x14 0x59 0x16 0x53 0x9c)) 12 (by decide) (UInt64.ofBytes 0x7f 0x49 0x19 0x84 0xf2 0xa4 0xd0 0x1f)) 13 (by decide) (UInt64.ofBytes 0x18 0xb4 0xe3 0xaf 0xda 0xa3 0x22 0x97)) 14 (by decide) (UInt64.ofBytes 0x90 0x81 0x92 0xe0 0x57 0x64 0x6b 0x6f)) 15 (by decide) (UInt64.ofBytes 0x3c 0x61 0xa1 0x90 0x1 0x91 0x90 0x3)) 16 (by decide) (UInt64.ofBytes 0x50 0x5b 0x56 0x6c 0x41 0x61 0x81 0x9c))

private def absorbed114 : Vector UInt64 25 :=
  #v[0x186aecec85b55e4e, 0xf862b8453e916af1, 0x65c5a5cd3cdd2bdf, 0x87c94d6202ba73ea, 0x4914220cf9a51d20, 0x4cc47c76c4375bb, 0x6451b6c9c904b40c, 0x958707244ca503f2, 0x7a02f41c94fd7f47, 0x1fdd2b974e372a25, 0x73e3b4b4725157a2, 0x2ea9e7d714325d8c, 0x9bafb8ada0ac0a68, 0x7376c516d22ad9d1, 0x9e8f64bba3dd37b4, 0x222ddd6df768e05c, 0x965d70de4b7eff56, 0x2069b194a2b6d6e1, 0x14f3f15f3c27f6f8, 0xd3db414c0f72b9, 0xb487675a6724af90, 0xe7a2e5f4ccc28e59, 0x46a3eb92edce12da, 0x538f4cb089175d8d, 0x43c9ffcbea925843]

private theorem words114 : absorb114 state114 = absorbed114 := by
  decide +kernel

private def quarter114_1 : Vector UInt64 25 :=
  #v[0x285f54af80b4a608, 0x5d3b4167f39d29f3, 0xacb3efe7e4e99fbd, 0x9b4aa40f526de125, 0xdb895569e0410fe7, 0xb53683d46a70b6b5, 0xfdd9967aa33cbc44, 0xc6057db2ae3fc3bb, 0x8115bb088166448a, 0x911756479756d000, 0x9826fed28f08d2a3, 0xdf58ce87603b6edb, 0xd257fd82643acbe1, 0x76568951807c13ba, 0x71796c3b46684f0f, 0xee855a2c965b1b9f, 0x2bfca4c48c718833, 0x7f0d83727b9ae156, 0xc174adbd0b5fc0a0, 0x2d237a6986cbe6bc, 0xb99c8926faace61f, 0xafd8ffe11abb55f0, 0x8a8ea6dedd78730d, 0xce78a2ccc92f80c2, 0x57e8a0b61d3b2f80]

private theorem rounds114_0 : sixRounds 0 (by decide) absorbed114 = quarter114_1 := by
  decide +kernel

private def quarter114_2 : Vector UInt64 25 :=
  #v[0x67ef60897ec68db0, 0x7f9823ba6e9d4d0e, 0x32a717d54e715b8b, 0x6dfc6fb62a88225a, 0x29967f9c1f73c5b9, 0x6391248dd6d67252, 0xcc1d748864160eac, 0x2bda8b00e8f3a5da, 0x7369362417727fe1, 0x7dcef6c0d200323f, 0xd13fa9e4de0b58c8, 0x8a1395bc3b6d329b, 0x50e1276fea97f668, 0xc88920f049e2e753, 0x8ead503467ed3837, 0x3df693ab9965cea1, 0xe2b1d8009c333cc3, 0x8e65dd5d59ff7526, 0xf3fa4241c5fc47cb, 0x693ccdc4bf12a253, 0x545175071af72280, 0x1fbc7a1da2b0f674, 0xf6753099e8b47a9e, 0x79c2d00ec7ed70f4, 0xa1acea9507e6fbe]

private theorem rounds114_1 : sixRounds 6 (by decide) quarter114_1 = quarter114_2 := by
  decide +kernel

private def quarter114_3 : Vector UInt64 25 :=
  #v[0x25fc01953e5b171a, 0xf83b3e156ecd82e5, 0x1b2a9c9725462fa6, 0xb63c88e00f3eebfc, 0x677694a90f133d8a, 0x52065249fa2c2b55, 0x2c449bf7f1b9de68, 0xf6adb02b0c96dfe, 0xe6bf30d0cabac03, 0x47c92d42379b5162, 0x5b66bab937c348d7, 0x6cc296cf066555c0, 0xbd745f159cdda118, 0x8416681f421a8fb6, 0x6e81f19d87ce9673, 0x96042bc0fa7548fe, 0x86b5d42cebd3c11, 0x3cb995e5bcc7f653, 0xf9470b3bf32202b1, 0x674f1a49502dde62, 0x290944fd3fa866b4, 0x8c869311105b3d86, 0x7bdc8ff8e1955bda, 0x94d0891a7c999847, 0x812ea018ec62b19f]

private theorem rounds114_2 : sixRounds 12 (by decide) quarter114_2 = quarter114_3 := by
  decide +kernel

private theorem rounds114_3 : sixRounds 18 (by decide) quarter114_3 = state115 := by
  decide +kernel

private theorem perm114 : KECCAK.f1600 absorbed114 = state115 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds114_0, rounds114_1, rounds114_2, rounds114_3]
  rfl

theorem block114 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes114 ++ tail) state114 =
      KECCAK.Bytes.run 0 tail state115 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes114 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb114 ws)) := by
    rfl
  exact (step state114).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words114).trans perm114))

private def absorb115 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x54 0x2 0x60 0x5b 0x56)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xf 0x3d 0x61 0x14 0x33 0x16 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0xa0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x82 0x1 0x20 0x60 0x80 0x80 0x1 0x4)) 10 (by decide) (UInt64.ofBytes 0x52 0x81 0x2c 0x60 0x52 0x82 0x3 0x81)) 11 (by decide) (UInt64.ofBytes 0x60 0xe2 0x56 0x61 0x80 0x1 0x20 0x60)) 12 (by decide) (UInt64.ofBytes 0x50 0x91 0x1 0x40 0x60 0x39 0x91 0x2c)) 13 (by decide) (UInt64.ofBytes 0x90 0x3 0x91 0x80 0x51 0x40 0x60 0x50)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x81 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed115 : Vector UInt64 25 :=
  #v[0xf65072cbfb79ee46, 0x57c3a3fab773c9d5, 0xb22e11f9a43f1e26, 0x820d93ff7ad3df96, 0x6e2775d68d3a7cd0, 0x72e092f84dbec86e, 0x20a50b3ffde42e55, 0x3551377560666860, 0x3f6cb3c8c7485639, 0x1f49b326a9951637, 0xbe3cf6c373c3cbc8, 0x5113d68cade1e34e, 0x8dd274f2046be737, 0x5aacdeb918fac299, 0x6b8c6dc4e0e42f79, 0xbae883c063edf3a5, 0x50b45665d5cfc865, 0xc6525ceca65ecb6b, 0xf54e64d82171744c, 0x666ccf0a050d3eb0, 0xc56b8b03c6d47009, 0xc73017d8ed075ebf, 0x1e12f6660798eaf6, 0x7cc0e56a2cb7ac4a, 0xd26b6f47819842e8]

private theorem words115 : absorb115 state115 = absorbed115 := by
  decide +kernel

private def quarter115_1 : Vector UInt64 25 :=
  #v[0x530f628c66a689b, 0x4d94d4879b6762ea, 0x7cffe687ef73168, 0x5ffdc7e631e8b3a3, 0x5899af3ba441691a, 0xe67937407adce007, 0x5cda55f88a2ffc9, 0x80572730f9a019d4, 0x8e18f1ac7d9af3c3, 0x637c2dc7603b6fc8, 0x2d56cc74ba4e003e, 0x5a840341d588c945, 0xdd17bd8fb232ab19, 0x8d115c9456e92e09, 0xfbc10c72b9ffb6b7, 0x29e39599a8ce0ad9, 0x32209a13b3a28e0b, 0x5ee2c43a1dbd8c88, 0xb1b275c559692c2c, 0x5cd03f788aafdb6c, 0x814044b0669943bf, 0xff420aae40cab622, 0xd93b7670b14bae21, 0x8135ed96c53bd369, 0x7f2a23daccb261e0]

private theorem rounds115_0 : sixRounds 0 (by decide) absorbed115 = quarter115_1 := by
  decide +kernel

private def quarter115_2 : Vector UInt64 25 :=
  #v[0x2273f45a2b870b3c, 0x22d55c87e3002ab7, 0xf8b44064de97ffce, 0x9bef5e2b0b6feff8, 0x5570d80541e7845b, 0x4acbc5190f0a3166, 0x34898bdf77cfa075, 0xc7af9d250b7fb16c, 0x31a8c7e01619700d, 0x2e8783d30b413cb1, 0x4253d9e8081a47c5, 0xb46ebfb7dd0f3e79, 0xde6782a07076401f, 0x914b6c7cb95a9ca2, 0x50085bf6ed3fbaea, 0x1ca3cece2dec223d, 0xf603ec08448111, 0x75f4f1c33db0927c, 0x92ac5034286a2884, 0xe90383e20463a51d, 0xc62e62ba8e9c3a5, 0x8a72ae400021d95a, 0x2e1b2e07b14c13ae, 0x39fb31ece847f77, 0xba079918226b2b98]

private theorem rounds115_1 : sixRounds 6 (by decide) quarter115_1 = quarter115_2 := by
  decide +kernel

private def quarter115_3 : Vector UInt64 25 :=
  #v[0x429f60d1026807c5, 0xa37b57a1c5b20995, 0x60ae0f3caacf031, 0xdea3fd74a695dbe6, 0xc0837bbbf7ba2a1e, 0x72ee8d518585423f, 0xae37e96dc9dbd822, 0x1904257ebb45f49f, 0x43c292f3888f69ea, 0x64d8976af87038ba, 0xc46603b34b307e5c, 0xf0b2e74ab0a1770c, 0xb1b3eb97ca385364, 0xef760d95a358bd61, 0xa53a42883bd8e802, 0x4f28d2ecf6353092, 0xfc724f5e93040e43, 0xf9b4f483b97fba36, 0x22d02650cfb70425, 0x46c6a5f749725b28, 0xb3dd9773bab40b55, 0xf0fd75dcda8494a3, 0x554e5f786f2a0279, 0x84c6c52392c50502, 0xdb9fc6ae4c553ff1]

private theorem rounds115_2 : sixRounds 12 (by decide) quarter115_2 = quarter115_3 := by
  decide +kernel

private theorem rounds115_3 : sixRounds 18 (by decide) quarter115_3 = state116 := by
  decide +kernel

private theorem perm115 : KECCAK.f1600 absorbed115 = state116 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds115_0, rounds115_1, rounds115_2, rounds115_3]
  rfl

theorem block115 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes115 ++ tail) state115 =
      KECCAK.Bytes.run 0 tail state116 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes115 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb115 ws)) := by
    rfl
  exact (step state115).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words115).trans perm115))

private def absorb116 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x3 0x60 0x52 0x81 0x81 0x0 0x60 0x16)) 1 (by decide) (UInt64.ofBytes 0x20 0x82 0x80 0x40 0x60 0x52 0x20 0x60)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x7f 0x54 0x80)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x90 0x17 0x1 0x60 0x16 0x0 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x17 0x18 0xe6 0xa4 0xff 0x7f 0x51 0x55)) 8 (by decide) (UInt64.ofBytes 0x8f 0x52 0x28 0xcf 0x65 0x25 0x69 0x77)) 9 (by decide) (UInt64.ofBytes 0x56 0x6b 0xa8 0x6e 0x51 0xd1 0x8f 0xc8)) 10 (by decide) (UInt64.ofBytes 0xf6 0x5a 0x57 0xfa 0x35 0x52 0x7 0xda)) 11 (by decide) (UInt64.ofBytes 0x56 0x50 0xa2 0x90 0x91 0x55 0xb8 0xa4)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x5b)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x60 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x20 0x60 0x3 0x60 0x52 0x81 0x90 0x0)) 16 (by decide) (UInt64.ofBytes 0xff 0x60 0x54 0x20 0x90 0x40 0x60 0x52))

private def absorbed116 : Vector UInt64 25 :=
  #v[0x287911e0cc1de1dd, 0xb2b1f5a4fa928323, 0x610958f54fffc4c3, 0x3d2fbd54bcaf327c, 0x98f42ccf5b8c6cf9, 0xe0402f21e352d90, 0xbf8ccca536e46a02, 0x1177cf8f37bc7958, 0xd1c595744f68366, 0x51de5a69057fa538, 0x1fae8f4b96a00ade, 0xc9055eea78fb1a83, 0x93b161724ebaef03, 0xc5bfbe1ef28cb60d, 0x4e1f4a5b835e34c0, 0x2f0cb4f7fdf77149, 0x1db6b07e83d4f9bc, 0x102e41b800b89b04, 0x7c0f92519198ae20, 0xcddba07a2a24136b, 0xdc12ca5ac8c66fe0, 0x33d3901b85355cce, 0x603a5c82d848076a, 0x7d4a746d7ae3bf1f, 0x84ce690d21d17394]

private theorem words116 : absorb116 state116 = absorbed116 := by
  decide +kernel

private def quarter116_1 : Vector UInt64 25 :=
  #v[0x3e8a2b4462eab33c, 0x5428a55ebe0be73c, 0xa179d4d6cd814587, 0xbc0985f2d29c27a7, 0x68fd13cb1cb71405, 0x262443cfa2d26fb3, 0x47e1eeb4df56d794, 0xd93de0fa60c345b8, 0x68dd055efda1248d, 0xdd3fd85ca37180f4, 0xccc5ed5bc6a0374f, 0x36c72a13e3945ab0, 0x96be2647bf34d41f, 0xfc4de71bc843e390, 0xc1420529cebf701, 0x4d2c6c507311bca2, 0xf94fd2e7499c85b, 0x4e867a124d84c768, 0x312c23a62507e2de, 0x6c1c7b978a1d08c, 0xff15958dc8665304, 0xa185e6c2d668ec73, 0x1cad38c5b1c3ebc5, 0xb1729a3282c713da, 0xa4a7097bd9cb663]

private theorem rounds116_0 : sixRounds 0 (by decide) absorbed116 = quarter116_1 := by
  decide +kernel

private def quarter116_2 : Vector UInt64 25 :=
  #v[0x630b56477a936e2, 0x79af9309aa3d1d7d, 0xfae7f9e240b0064d, 0xca896cbb86e55618, 0xcff8b085f6b93b02, 0x19c9eaf3f7e7f519, 0xef8884d809a99df, 0xfe36c3f7b2932c45, 0x11f8d3d9c4d9e7a7, 0xfef55e243f97541f, 0xc84a06ba493c7ec4, 0x17086b13784179f0, 0x59346081bf8c84bf, 0xc7b60b7f5d9465c8, 0x7238dfc8fe49b285, 0x1c4707e5f37c14e9, 0x6d00651288380259, 0x42ce7af733ec3111, 0xb6e99b9cc827b58d, 0x8d85e91ca753522b, 0x8ba418ab5ed12247, 0xa47482ec1ee29055, 0x8a0c5ee82a45568b, 0x5c31a12d15876e36, 0xc1f712b133bbc874]

private theorem rounds116_1 : sixRounds 6 (by decide) quarter116_1 = quarter116_2 := by
  decide +kernel

private def quarter116_3 : Vector UInt64 25 :=
  #v[0xd3fb4d0ea406bca7, 0xc37daf28f00442c, 0x71e787f8b3d46715, 0x613050aa8cb09e34, 0xd11db7e8f123b961, 0x8eb5a2001cbb28a5, 0xe2c61075ab386529, 0xe8f8b4877343bfc6, 0x6f4ebcb7ae48ecf3, 0xdfd06a383dfe7fde, 0x718506f6c59e446, 0x509df5fa9b1c38f5, 0x830647f7631333ba, 0x298d78473b07ce9c, 0x97154a093fb1eb81, 0x1f4cb47e7debcffd, 0xaec723ec09bf5337, 0xee4f55183e4cb4de, 0x581f67d46c3808f4, 0x56326bc49149c106, 0x7f661eab172429bb, 0xc66a55302ac2e909, 0xae6941da4aa76fd1, 0xdab513e3d3a9d15b, 0xf86930bcd0a0dec7]

private theorem rounds116_2 : sixRounds 12 (by decide) quarter116_2 = quarter116_3 := by
  decide +kernel

private theorem rounds116_3 : sixRounds 18 (by decide) quarter116_3 = state117 := by
  decide +kernel

private theorem perm116 : KECCAK.f1600 absorbed116 = state117 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds116_0, rounds116_1, rounds116_2, rounds116_3]
  rfl

theorem block116 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes116 ++ tail) state116 =
      KECCAK.Bytes.run 0 tail state117 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes116 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb116 ws)) := by
    rfl
  exact (step state116).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words116).trans perm116))

private def absorb117 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0x56 0x90 0x16)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x60 0x57 0x1d 0x3e 0x61 0x16 0x83 0xff)) 4 (by decide) (UInt64.ofBytes 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x1 0x4 0x60 0x52 0x81 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x3 0x81 0x82 0x1 0x20 0x60 0x80 0x80)) 10 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x24 0x60 0x52 0x82)) 11 (by decide) (UInt64.ofBytes 0x91 0x24 0x60 0x79 0x58 0x61 0x80 0x1)) 12 (by decide) (UInt64.ofBytes 0x60 0x50 0x50 0x91 0x1 0x40 0x60 0x39)) 13 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51 0x40)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x61 0x16 0x82 0xff 0xff 0xff 0xff 0xff))

private def absorbed117 : Vector UInt64 25 :=
  #v[0xa529100a05c4b143, 0x5ddd19cd1d3e354c, 0x30d57a722ea8c55f, 0x7c2b36a06e8dc787, 0x9318584fdebe18b3, 0x7f03b6aa9efe0465, 0x779f8be7fddb0f2c, 0x1e734bfbe6255ddc, 0x71773202917a4516, 0xa52bea26fc39a48a, 0xfd8b690992091651, 0xc3deb5bae5b037a4, 0x39f5553fdafd9fbb, 0x9720c1a23e84b065, 0x70574f937686386a, 0x88aa09a2db4f7211, 0x90721cf598130a, 0xdce0801b1fccb012, 0x577a7df2ee3668b, 0x171c2ded054d542f, 0x426ad49d9b2fbc56, 0x4bf0993d378dbc52, 0x9364cc988b0ae968, 0xc712d4c1ba8e5f8f, 0xaa1143e6c5087ef]

private theorem words117 : absorb117 state117 = absorbed117 := by
  decide +kernel

private def quarter117_1 : Vector UInt64 25 :=
  #v[0x231af8e8bec8c6a7, 0x951992a5943c103d, 0xcc9767e22d5e517a, 0xa2d2d47fa18c0b6e, 0x822fea8fb4b54683, 0x4dee13b7179b6528, 0x791d865efc770ed4, 0xd8fafc05a3302a03, 0x370e36a8b71965db, 0x7fa904728bdddd64, 0xff0470e784990d18, 0x932407b041af61ea, 0x775d50e5f0ae5c68, 0xf0885c3d53e984e6, 0xd426ea89db1dd0d3, 0x216f2c2f66e251, 0xeab3a5fea52052a7, 0xc06f34384f671955, 0xe9398ec838b56cd4, 0x5ff2733ffbac52d, 0xca1fcf8915a1d520, 0x1aa81ba3551de875, 0xfc3fe6c8d04c1a9, 0x4e87b07ce9f11379, 0xbbf98e491c11283d]

private theorem rounds117_0 : sixRounds 0 (by decide) absorbed117 = quarter117_1 := by
  decide +kernel

private def quarter117_2 : Vector UInt64 25 :=
  #v[0x8963b242d50da013, 0x133ab1babe41af5b, 0xa7fd429381fc1a57, 0x31e0fe038a232fce, 0x1b67584eec50a2c8, 0x9b9c9e70f9bf8381, 0x99ccec39a5d18205, 0x3367a883d01bff4e, 0x25d4dcb0424ad22a, 0x6de406ae474c063c, 0x5de69e31f55eec2c, 0xee7dce4adc5bb251, 0x2123964a36a8514f, 0x7aef66a6d6c16a6, 0xa552e13902ba7d88, 0xbad8c5c48b370d38, 0x2b765c9df6467b57, 0x3736d4b92f04bb56, 0x6e4c931a88aed132, 0x61e69d5e2bcb1334, 0x45bf7b1590f4af36, 0xafd4dfa7dd0f067f, 0xc7a9c1443dec706e, 0xcb15974a3ef2e04b, 0xb7f2d4b68c443e03]

private theorem rounds117_1 : sixRounds 6 (by decide) quarter117_1 = quarter117_2 := by
  decide +kernel

private def quarter117_3 : Vector UInt64 25 :=
  #v[0x977ce34a109f8caf, 0x8d223a5221aa271b, 0x494b4f9b0aa0c60d, 0x57fc3745fadd5d1f, 0x1bcc0197cb076660, 0x7d1ad1779a262aae, 0xba15633132e58b6e, 0x4b6a8ed033993489, 0xc5f0926bb4c3bf58, 0x39c7bdbb05f723ad, 0x4a974fe48cabbcd6, 0xcd242798b96036e7, 0xd9d95ca569aa1144, 0x61882742982ac450, 0x2c11a74e5a55802b, 0xec67900593850882, 0x61c9db12bcefa399, 0x45ba052f69e85af9, 0x9f5cdc9cd4cc59b6, 0xa17d380882171b05, 0x962bfd7394423f7b, 0x27f9ae6521fdceed, 0x52f91d6232365b8f, 0x78907751fb1c158b, 0x8db92a35ba28ac4]

private theorem rounds117_2 : sixRounds 12 (by decide) quarter117_2 = quarter117_3 := by
  decide +kernel

private theorem rounds117_3 : sixRounds 18 (by decide) quarter117_3 = state118 := by
  decide +kernel

private theorem perm117 : KECCAK.f1600 absorbed117 = state118 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds117_0, rounds117_1, rounds117_2, rounds117_3]
  rfl

theorem block117 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes117 ++ tail) state117 =
      KECCAK.Bytes.run 0 tail state118 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes117 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb117 ws)) := by
    rfl
  exact (step state117).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words117).trans perm117))

private def absorb118 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x8 0x7f 0x51 0x40 0x60 0x57 0x89 0x3e)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x81 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x20 0x60 0x80 0x80 0x1 0x4 0x60 0x52)) 6 (by decide) (UInt64.ofBytes 0x22 0x60 0x52 0x82 0x3 0x81 0x82 0x1)) 7 (by decide) (UInt64.ofBytes 0x55 0x61 0x80 0x1 0x20 0x60 0x52 0x81)) 8 (by decide) (UInt64.ofBytes 0x1 0x40 0x60 0x39 0x91 0x22 0x60 0xf5)) 9 (by decide) (UInt64.ofBytes 0x91 0x80 0x51 0x40 0x60 0x50 0x50 0x91)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90 0x3)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x81 0x81 0x0 0x60 0x16 0x84 0x80 0xff)) 14 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x20 0x60 0xa 0x60 0x52)) 15 (by decide) (UInt64.ofBytes 0x16 0x87 0x94 0x20 0x83 0x80 0x40 0x60)) 16 (by decide) (UInt64.ofBytes 0x82 0x91 0x52 0x82 0x94 0x52 0x84 0x80))

private def absorbed118 : Vector UInt64 25 :=
  #v[0x395a67ca643a7592, 0x3eab092224a309f6, 0xfa735bde989463b, 0x9bd03b75d5ec3193, 0x13df1b6ef3231fc1, 0xa1569b293812708c, 0x2719d501bb0f0464, 0x6052921f020cee4d, 0xf583354c7af5e649, 0x52d0aade5bd49655, 0xd3496dd9591aea64, 0x3c57a7f5ba98f15a, 0x3b627be04e6383f1, 0xd6aecf4a33d710e4, 0xda545118597eab4f, 0x54da005dfec28372, 0x56998a92827c8a80, 0xf3380b24322d892d, 0x92ca635c52896c28, 0xf1d442f40bb7590a, 0x9bdda325006f3e36, 0x4a460bd8007e55ae, 0x7943c367729fad7f, 0x85ec22b6b70a319f, 0x89f79f7c95539452]

private theorem words118 : absorb118 state118 = absorbed118 := by
  decide +kernel

private def quarter118_1 : Vector UInt64 25 :=
  #v[0xe500747baf1adc06, 0x3a1736b850f95ad9, 0x2e9327594b0e17, 0xdde3a9f269fb7d26, 0xf7cf4993c9468f06, 0x3ecaa45c04290c3, 0x39e4059edfbcf73a, 0xece5ae029a753d54, 0xc26f0db0c1460c9d, 0x94a7d81674febcbb, 0xda8fd93b60608e10, 0xa8db97df1fd7df7c, 0xbe9ec9f4e4beffcc, 0x685b985d11972a6c, 0x15acf526c7e807e9, 0x548a65cdcb191be8, 0x2f69e1e4d672cf8, 0x1ca6de675892a85b, 0x8dc6ba6437179325, 0xe9542f1a25c388a0, 0x4f5d6915870631bd, 0x8678136e1dfd8217, 0xadd0ef8c97c2ddf7, 0x9a2c3991fafc89b7, 0xd90d455e017bdb1]

private theorem rounds118_0 : sixRounds 0 (by decide) absorbed118 = quarter118_1 := by
  decide +kernel

private def quarter118_2 : Vector UInt64 25 :=
  #v[0x5d280260e97413d8, 0x1fe690269cead6c, 0x768a52ba7d259cb4, 0xc808de5cea17fddf, 0xb02f57e71bbc1263, 0x5c4ff80ddb6f9b7e, 0x41cfbaf1c549dc61, 0xeb2f191faf7a3f1f, 0x14c80f9be7d41262, 0x33c3be604f42d6d6, 0x3bd842d539297cbc, 0x3fcc1612b9b97061, 0x2c3df850a58015ce, 0x56d850e0463cb014, 0xa01abac7f0769247, 0x3ec3f25e38563552, 0x769fd93b951993e5, 0xe092139de8c82283, 0x3ca58da3d6075c2b, 0xc80135d21b56327f, 0x1be265432691bb9b, 0x38098d5113325e3f, 0x5ad27592e6b9740a, 0xc4a44871f22efed7, 0x73b5c5d9d457992f]

private theorem rounds118_1 : sixRounds 6 (by decide) quarter118_1 = quarter118_2 := by
  decide +kernel

private def quarter118_3 : Vector UInt64 25 :=
  #v[0xb4b40ba96608ed1b, 0xc49a8cd483a45be7, 0xb9beb8e76374ef81, 0x88aff1fa9d0d3de9, 0xd75ac5cd7b8c5d0f, 0x54d64a8a367fd6ea, 0xcafbdf79446dd52b, 0x50db633d80fc7752, 0xd3142cede7e6d7bc, 0x1301eed916fb4fdb, 0x7679c3bb866b8f4f, 0x8817a70115f375ba, 0x2912413a25a2480c, 0x93f7ca295dcf1f08, 0xcb6945bf8ac8297e, 0xc7f5b7412cef89af, 0x989bb84573fdfcdb, 0xa6db166e6f962389, 0x598d2bec2335c30c, 0x8dcaff6db4198738, 0xe052501bcbb9fa20, 0xf21bc3384db7cc56, 0x87781135e9acbad3, 0x8241172003fbf0d3, 0x6bad5545688063ce]

private theorem rounds118_2 : sixRounds 12 (by decide) quarter118_2 = quarter118_3 := by
  decide +kernel

private theorem rounds118_3 : sixRounds 18 (by decide) quarter118_3 = state119 := by
  decide +kernel

private theorem perm118 : KECCAK.f1600 absorbed118 = state119 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds118_0, rounds118_1, rounds118_2, rounds118_3]
  rfl

theorem block118 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes118 ++ tail) state118 =
      KECCAK.Bytes.run 0 tail state119 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes118 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb118 ws)) := by
    rfl
  exact (step state118).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words118).trans perm118))

private def absorb119 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x85 0x51 0x81 0x55 0x90 0x85 0x20 0x90)) 1 (by decide) (UInt64.ofBytes 0xe1 0x5b 0x8c 0x7f 0x51 0x91 0x52 0x81)) 2 (by decide) (UInt64.ofBytes 0x71 0x4f 0xd1 0x5b 0x7d 0xec 0xeb 0xe5)) 3 (by decide) (UInt64.ofBytes 0x14 0x3 0xdd 0xf3 0x84 0x1e 0x7d 0x42)) 4 (by decide) (UInt64.ofBytes 0xa 0x20 0x5b 0x1e 0x29 0xb2 0xf7 0xc0)) 5 (by decide) (UInt64.ofBytes 0x90 0x81 0x92 0x25 0xb9 0xc3 0xc7 0xc8)) 6 (by decide) (UInt64.ofBytes 0x50 0x50 0xa3 0x90 0x1 0x91 0x90 0x3)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0x56 0x50)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0x64 0x3f 0x61 0x16 0x83)) 11 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 12 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 13 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 14 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x80 0x1 0x4 0x60 0x52 0x81 0x0 0x0)) 16 (by decide) (UInt64.ofBytes 0x82 0x3 0x81 0x82 0x1 0x20 0x60 0x80))

private def absorbed119 : Vector UInt64 25 :=
  #v[0x613f3f9b2f696d16, 0xf7602aa250d0db3d, 0x18b68dd7b779adaa, 0xf161d9c4f88a5254, 0x6ab46971531b2946, 0xdd4534f636af76f, 0x660fce44aea36187, 0x9b40a6292ed0f65b, 0xcc4b31290621a934, 0x49a6cfdae1c676ab, 0xc3e4f3cb0b029e71, 0xbe17003ccfa7cb63, 0x4d538f820c549a77, 0xdc72986033bc0485, 0x2306b76f403a1eb1, 0xb05edf33308269d5, 0x1dcff125fa198fda, 0xcdcbaf9ce6daf464, 0x95966565cadf56d, 0x74c74976ebf656b7, 0x9869ebcb2fbed951, 0xc7f4e3a9f8c28fa, 0x74171809b884d23a, 0xe51299df7cdd9659, 0x296b2ffe4ab5ad09]

private theorem words119 : absorb119 state119 = absorbed119 := by
  decide +kernel

private def quarter119_1 : Vector UInt64 25 :=
  #v[0x46f44e0cd298f2f5, 0x52e1c91e6e4974d1, 0x1b000994e823a23b, 0x34c4a83783fbc5d, 0xf1de609cee70ccbb, 0x3e4de0dd3965f836, 0x2ab6de2c76da054d, 0x8aaad44db0534214, 0x74f354c9c67882e0, 0xcb53371f12da20a2, 0x6492c6dabf5445a, 0xc6b3426dffe6b3dd, 0xaeb52a0c017d30b2, 0xad578cb328b1fb5, 0xf9393356011b0464, 0x63cda8a3cd1c9b3c, 0xbbb6c18c1a83e637, 0xfd2047bc912832a8, 0xe44f0aabe9684f1e, 0x5c73815b5ac447ee, 0x62cf66a458fba20b, 0x7ae14eec003ad491, 0xeb65eff34b57698a, 0x495126b17a5885e0, 0x9192ffd063ca9c01]

private theorem rounds119_0 : sixRounds 0 (by decide) absorbed119 = quarter119_1 := by
  decide +kernel

private def quarter119_2 : Vector UInt64 25 :=
  #v[0x974446c5c5b28ed7, 0x6a761f345409b00b, 0xa4cb7ad901bd1e8e, 0xda988ee947384e0b, 0x2e93122a0a687bdb, 0xf363a7263397913d, 0x47a517c354ff22ce, 0xde499594524ba2cb, 0x330cdffa00dc592b, 0x6859a6bcebf42da8, 0x5d38c55d7014cca6, 0x64f8f7d0ee610e12, 0x29ed08514e036cc4, 0xb85792d548327b1f, 0x39f5a741b7b2b900, 0xbedc48805599f4a6, 0x94237dad59abcd71, 0x962c90d21fc62350, 0x5a0b05aa4491a0bb, 0x6221def767d35eb3, 0x7d404c24ffea2c07, 0xd27c09429528dbf3, 0x3f46f9958eca59b5, 0x4653dc7d64154fd8, 0x5e5311ca774048bd]

private theorem rounds119_1 : sixRounds 6 (by decide) quarter119_1 = quarter119_2 := by
  decide +kernel

private def quarter119_3 : Vector UInt64 25 :=
  #v[0x8f673a13af72986f, 0x909556bf40807033, 0xc99454a2a5dd4f0, 0x7fecc8a120431b09, 0x5f13ed4c6da93d98, 0xb191e0fee3c6df04, 0x81652536cd86257b, 0x11e8e401709249b4, 0x2e04401e46edc299, 0x7015b0ca14245f3c, 0x494ae6d88c8e1e56, 0x2eb1d1368c22b7b3, 0xb523a2f7a9fe1b0f, 0x70c89545048ebe7a, 0xbfa527b1aa8e404d, 0x9f222f31049fc1ee, 0x69ab99c7c0ebcca2, 0x6a735beffb860952, 0x949fcc0e3d9dd992, 0xe3c71af60a12a66d, 0x69f932f2abfc1d9, 0xfa2746606b8227e3, 0xd4b645f8ed42477e, 0xc13161498c393f85, 0x96dc236a29a2f66e]

private theorem rounds119_2 : sixRounds 12 (by decide) quarter119_2 = quarter119_3 := by
  decide +kernel

private theorem rounds119_3 : sixRounds 18 (by decide) quarter119_3 = state120 := by
  decide +kernel

private theorem perm119 : KECCAK.f1600 absorbed119 = state120 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds119_0, rounds119_1, rounds119_2, rounds119_3]
  rfl

theorem block119 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes119 ++ tail) state119 =
      KECCAK.Bytes.run 0 tail state120 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes119 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb119 ws)) := by
    rfl
  exact (step state119).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words119).trans perm119))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
