import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb150 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x90 0x91 0x92 0x90 0xb8 0x51 0x61 0x16)) 1 (by decide) (UInt64.ofBytes 0x5b 0x56 0x16 0xff 0xff 0xff 0xff 0x63)) 2 (by decide) (UInt64.ofBytes 0x32 0x61 0x15 0x50 0x91 0x90 0x51 0x80)) 3 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x80 0x80 0x57 0x6e)) 4 (by decide) (UInt64.ofBytes 0x4f 0x61 0x15 0x10 0x81 0x20 0x60 0x51)) 5 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0x64)) 6 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x57 0x6e 0x32 0x61 0x51)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x80 0x80 0x1 0x4 0x60 0x52 0x81 0x0)) 12 (by decide) (UInt64.ofBytes 0x52 0x82 0x3 0x81 0x82 0x1 0x20 0x60)) 13 (by decide) (UInt64.ofBytes 0x80 0x1 0x20 0x60 0x52 0x81 0x2a 0x60)) 14 (by decide) (UInt64.ofBytes 0x60 0x39 0x91 0x2a 0x60 0x13 0x59 0x61)) 15 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x91 0x1 0x40)) 16 (by decide) (UInt64.ofBytes 0x0 0x60 0x5b 0xfd 0x90 0x3 0x91 0x80))

private def absorbed150 : Vector UInt64 25 :=
  #v[0x9a880d4f0d0afe41, 0x1f8828ca034d9147, 0x8f894d99f7b94b04, 0xacd1a6630a6e9115, 0x83d1e00f69ccf93d, 0xce286c44af7194eb, 0x4bd26b5c1f46dfc9, 0x2edc42ef9d94f467, 0x7e11db0fa3b6b9e0, 0x2b49f9e1ace57aa3, 0x9f93e09dbabc9d18, 0x3a13907907ff4300, 0x2a7a4053ed13e292, 0xee702594a5ab958c, 0x1d76c22082dd90f3, 0x88838a7572ad192e, 0x6edeca55e6a34247, 0xdeb1fc5165150660, 0x13c0e1e238a7cb54, 0xd813d6a54fb88dfd, 0x35c3b8d9de084191, 0x4f375569855371ba, 0xe9d8db49cb77cbdd, 0x1317e8485868a93e, 0xf742df34abab6a99]

private theorem words150 : absorb150 state150 = absorbed150 := by
  decide +kernel

private def quarter150_1 : Vector UInt64 25 :=
  #v[0x61922d9c9fc3b87f, 0x9daa2dcb43dae890, 0x4501867a1553375d, 0xbc1d6779703e5f31, 0x4a566a9a28a2d09, 0x646af9c82f97fc06, 0x3702bd1580d80818, 0x7e06624368e8a73e, 0x1d23ad78b6289d64, 0xd2429feaf7a03e4f, 0x65598212471911f6, 0x6e7df4b4b6c81f01, 0xa5d99bbf7e36221, 0x5ad54e580e1a8579, 0xa93357a981a2b956, 0x5008dc84fa8c4815, 0x2c071f3b753c507b, 0x5ec69dc735599fe4, 0xf088415d845b0a14, 0xa00d618c01199dfc, 0x4e360f0a6c9021d1, 0xc2f90b8258a13ae8, 0xe388826ca9d00fab, 0xd2184c826cd871c7, 0x7af9ceba7b57f572]

private theorem rounds150_0 : sixRounds 0 (by decide) absorbed150 = quarter150_1 := by
  decide +kernel

private def quarter150_2 : Vector UInt64 25 :=
  #v[0x7c95caf50abac9, 0x10b7081b4793600d, 0xecdf556608957d34, 0xa2dc51e75f62f251, 0x387f1b98d29982da, 0x300d20270f99a30a, 0x27eca0bd7b3cea5b, 0xafd51a8457d442ca, 0x79d974f32794c981, 0x50f6e53899904fc, 0xb240779ae028adf, 0x68c9aac0de1208d, 0x8aaf587faccd26cb, 0x57e430dc79d9fa25, 0x2fd58a0156b1c1d0, 0xb8309757906af37b, 0x2e4bf866f1e6fa4c, 0x92fab3de6a77c04d, 0xfbf089e301395021, 0x4c4b0ee70fb43389, 0x6520becb05b5052e, 0x5f37cf51b8c329cc, 0xb2571a3afa3318b5, 0x4cb1e3b5a92af921, 0x92e5a10de6dc1be5]

private theorem rounds150_1 : sixRounds 6 (by decide) quarter150_1 = quarter150_2 := by
  decide +kernel

private def quarter150_3 : Vector UInt64 25 :=
  #v[0xc08f32b1ccc1e172, 0xc150e055c4e64778, 0x36fd560fa01c963b, 0x794e374150f9df3, 0xbbd23aa4c88ab8ef, 0xfe43c133de14cb98, 0x59301aca7bce0d86, 0xc03453ae72772f2f, 0x9413db46dc0f2778, 0x9b2bf8709d9cde19, 0xb3af879da6424050, 0x2b36a14b2e349521, 0x6b6c859b85098066, 0x916243d639cc182c, 0x6ff32e090e6d013, 0xa30893cf56c51053, 0x4fab85c72977c83a, 0x1938031f51d6f08, 0x77e6aa111075114a, 0xf62886d21dc946ee, 0xd01a9fa2d9612fe4, 0x329069ef5592479a, 0xb434850bb2ead595, 0x58b5cf99c06bb90a, 0xf06d4d4e2355419a]

private theorem rounds150_2 : sixRounds 12 (by decide) quarter150_2 = quarter150_3 := by
  decide +kernel

private theorem rounds150_3 : sixRounds 18 (by decide) quarter150_3 = state151 := by
  decide +kernel

private theorem perm150 : KECCAK.f1600 absorbed150 = state151 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds150_0, rounds150_1, rounds150_2, rounds150_3]
  rfl

theorem block150 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes150 ++ tail) state150 =
      KECCAK.Bytes.run 0 tail state151 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes150 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb150 ws)) := by
    rfl
  exact (step state150).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words150).trans perm150))

private def absorb151 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x7f 0x7f)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x50 0xa4 0x57 0x73 0x6e 0x57 0x5d 0xff)) 3 (by decide) (UInt64.ofBytes 0x20 0x1b 0x68 0x46 0x2f 0xe9 0xdf 0x1d)) 4 (by decide) (UInt64.ofBytes 0x57 0x36 0x50 0x61 0x15 0x11 0x82 0xa0)) 5 (by decide) (UInt64.ofBytes 0xa0 0x79 0xc3 0x8 0x7f 0x51 0x40 0x60)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x81 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x81 0x82 0x1 0x20 0x60 0x80 0x80 0x1)) 11 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x26 0x60 0x52 0x82 0x3)) 12 (by decide) (UInt64.ofBytes 0x26 0x60 0xed 0x58 0x61 0x80 0x1 0x20)) 13 (by decide) (UInt64.ofBytes 0x50 0x50 0x91 0x1 0x40 0x60 0x39 0x91)) 14 (by decide) (UInt64.ofBytes 0xfd 0x90 0x3 0x91 0x80 0x51 0x40 0x60)) 15 (by decide) (UInt64.ofBytes 0x14 0x1b 0x60 0x16 0xff 0x60 0x83 0x5b)) 16 (by decide) (UInt64.ofBytes 0x50 0x57 0x4e 0x50 0x61 0x15 0x80 0x15))

private def absorbed151 : Vector UInt64 25 :=
  #v[0xa33afd2c745d5291, 0xb888456cb3430219, 0xfc66c65c3f3c4c0a, 0x1b930910651a90b2, 0x672ec4d7073c0def, 0xa3113cf9fb5f033c, 0xfae7719b0823de98, 0x6c78b7a8c2587972, 0xe237fce0b4e73cf9, 0x39c8f3a10bb13176, 0x3c25a29b7d80acaf, 0x25e616eb33c5404d, 0xdf18d5e16943c612, 0xc98915837f1f1feb, 0x200a831083e4a895, 0x28c70b840cb9f379, 0x9401aecc0774a5d7, 0xa558bf538a236c2a, 0x4c3b4dd2a6a152ea, 0x7fd8faa45dfc7b0a, 0x31aa9232d2ac5fe0, 0xa8cf40ea51dbfe20, 0xbeef41d28f2a3449, 0x39091737524746dd, 0x82c99e2f738d61ad]

private theorem words151 : absorb151 state151 = absorbed151 := by
  decide +kernel

private def quarter151_1 : Vector UInt64 25 :=
  #v[0x74a56025b80ff1e8, 0x1b3f6e47c5048ef6, 0xd8da247d43135a45, 0x55081feee6a83262, 0x8ecc2d5685042147, 0x93b9b7cd75b4c4f0, 0x336dec419845fb68, 0x7800af58c87676f2, 0x8ccce83c3e18a46f, 0xa0449f01e79407ab, 0x895a518d2fc852b1, 0xa92493609c0e6a1b, 0x976aead9dc54c5b4, 0x3da9e254e9e9ff68, 0xff6314fd2b792f6c, 0xf7d7ac39bb3aadaf, 0x663366e0dbf47516, 0xdbc9e37b5485cb83, 0x334b3f8c2ee62a0c, 0x8581d065b62d4312, 0x56197b2e72d00fc, 0x22cec2d97cdd320, 0x135d6da644a142a2, 0x29cb82fd4b2f5773, 0x65b76c61fba617d6]

private theorem rounds151_0 : sixRounds 0 (by decide) absorbed151 = quarter151_1 := by
  decide +kernel

private def quarter151_2 : Vector UInt64 25 :=
  #v[0x2adc6aa57cc44e4b, 0x3e4d8d26501b0114, 0xf2fca12253515cc3, 0xd2f66cfd4b7b5693, 0x1ac52a61818357a7, 0x58d324413a732eeb, 0x9d1ff5d9d291558a, 0x948afd32776defa9, 0xf87014d802c5459, 0x313611dc8f2f20cc, 0x804a185fd1237182, 0x54eca660f2c5b957, 0x27ae20cab77a762, 0x9d8751c2a21ed476, 0x8f75405dab779f00, 0xca1d4e56e092d1f7, 0xab216306756325d0, 0x2fa8cf3a2fb98aa7, 0x88b7ae5ed40aaa8b, 0xea250c6670f30042, 0x7aa3758e39f6cc18, 0xf9a13bc7ae2e50a4, 0xa526046bad1b721c, 0x897166508c4c1054, 0x6ccbe1fd3013cdbf]

private theorem rounds151_1 : sixRounds 6 (by decide) quarter151_1 = quarter151_2 := by
  decide +kernel

private def quarter151_3 : Vector UInt64 25 :=
  #v[0x6d29c0ef59946ed1, 0x9ef05139f60db621, 0x4a9dd6f303384cce, 0xf8b542dca5ce8f9a, 0xece04b9b586e805a, 0x523cee8db3ddd53e, 0x44494d1add12bee2, 0x833a63c93a3732eb, 0xde2f95a8840a2a62, 0xfabe7907904234ec, 0xd0083b9a273397e1, 0x785b17efd67961f2, 0x755e06959c4fc2e1, 0x81826be43903c759, 0xa8c772f18df824fa, 0xcbd9f5f761aa722e, 0x1f170308c8cdd7a7, 0x4faa2efb5abefe2c, 0xa521b6b24f2c1fec, 0x15e40cb1f83551e6, 0xb7ddb381c796497, 0x570f05f2fc608bbf, 0x1d475a8b4be198c1, 0x590227cd71b98b84, 0x5ca5286e745183f7]

private theorem rounds151_2 : sixRounds 12 (by decide) quarter151_2 = quarter151_3 := by
  decide +kernel

private theorem rounds151_3 : sixRounds 18 (by decide) quarter151_3 = state152 := by
  decide +kernel

private theorem perm151 : KECCAK.f1600 absorbed151 = state152 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds151_0, rounds151_1, rounds151_2, rounds151_3]
  rfl

theorem block151 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes151 ++ tail) state151 =
      KECCAK.Bytes.run 0 tail state152 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes151 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb151 ws)) := by
    rfl
  exact (step state151).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words151).trans perm151))

private def absorb152 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x15 0x14 0x1c 0x60 0x16 0xff 0x60 0x83)) 1 (by decide) (UInt64.ofBytes 0x40 0x60 0x57 0xa4 0x50 0x61 0x15 0x5b)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f 0x51)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 6 (by decide) (UInt64.ofBytes 0x80 0x1 0x4 0x60 0x52 0x81 0x0 0x0)) 7 (by decide) (UInt64.ofBytes 0x82 0x3 0x81 0x82 0x1 0x20 0x60 0x80)) 8 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x26 0x60 0x52)) 9 (by decide) (UInt64.ofBytes 0x39 0x91 0x26 0x60 0xa9 0x55 0x61 0x80)) 10 (by decide) (UInt64.ofBytes 0x40 0x60 0x50 0x50 0x91 0x1 0x40 0x60)) 11 (by decide) (UInt64.ofBytes 0x60 0x5b 0xfd 0x90 0x3 0x91 0x80 0x51)) 12 (by decide) (UInt64.ofBytes 0x60 0x86 0x86 0x86 0x86 0x1 0x60 0x0)) 13 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x0 0x60 0x51 0x40)) 14 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x52 0x40 0x60 0x1)) 15 (by decide) (UInt64.ofBytes 0x60 0x84 0x1 0x20 0x60 0x52 0x81 0x85)) 16 (by decide) (UInt64.ofBytes 0x83 0x1 0x20 0x60 0x52 0x81 0x16 0xff))

private def absorbed152 : Vector UInt64 25 :=
  #v[0x582f93e9b20b4ac8, 0x78c34bd0605f4924, 0x3c5cee740171f711, 0xbbc4e3f44622d65f, 0x59936b3fa3875ceb, 0xa688d72ff2a79207, 0x5a16c3a650c94a8e, 0x3fe1a0fa773ea609, 0x49b344b241b7d5b, 0x197846d4788321f1, 0x1bcdb436ee769751, 0x1c376cdd52a05a37, 0xba887c3608229853, 0x267011a9c806bf00, 0xf2577ba6a4437477, 0x609ef49d5571e727, 0x7879ea095c227a9e, 0xb2482e37b8587b43, 0x45cb0f75c6e8bd71, 0x8c4bca04ca2a353c, 0xc820d2eb1406221d, 0x9c51a035554137a4, 0x3240d3ea1049beef, 0xce66f1b51c9d20a2, 0x5f8f8bd0945714d0]

private theorem words152 : absorb152 state152 = absorbed152 := by
  decide +kernel

private def quarter152_1 : Vector UInt64 25 :=
  #v[0xa8fe32fc8014c6d6, 0x8bfdc92cf8499dfb, 0xcb988d79c0c71862, 0xbc209c0987b79d55, 0xc22db4aefd30983c, 0x849ee2fd9df2195f, 0x8b093d237d2c7619, 0x23a556dabed59cef, 0xfb5c0c438bc101f1, 0xaa981f10b71fa592, 0x94c7d4a5706ff573, 0xa8ae49c3d6daccee, 0xcc017a4b3c2029eb, 0xa48424f9aec6147d, 0xb3dd78125f6ca6cb, 0xb8b1e0141c215de8, 0xb7ac5f05fe9fadbe, 0xc9a46fbce0ff631e, 0xd064aca075cfb6e, 0x25280be00c7db270, 0x8f42ae86b8a67260, 0xc9a4d21ab9c60d7f, 0x1a0d3f1acb62a6fe, 0x5800f0ea2817cb69, 0xfd07d1f24a4f60c7]

private theorem rounds152_0 : sixRounds 0 (by decide) absorbed152 = quarter152_1 := by
  decide +kernel

private def quarter152_2 : Vector UInt64 25 :=
  #v[0x1d69f94f5df326e1, 0xcbd645c65874ce53, 0xa3ed26d7a88bfd45, 0xfc9e1d7a68585469, 0xc84ee6f004a84b4f, 0x88d5607b7a7a9e5b, 0xed824ad225fa60c1, 0x44edd3b9c8dbacf6, 0x33f3cc2242067d45, 0xc13560ae293a2343, 0x7d1449e7c21441bb, 0xa26bea28173ca405, 0xc4065b5a0a48b996, 0xeb1a4914b63c4625, 0xe550b80a29747d7e, 0x5bcd15ee54f5560c, 0x5b2a372c2e6398a3, 0x8ab8e8ceee7b8a7a, 0x95ef47b30cdb5f16, 0xbde71fb881f5717f, 0xced0e9fe6baa91a9, 0x87618125f7e68d73, 0x147e75fe6e666bdd, 0xaa33686c891b98ef, 0xe5179d4752857d45]

private theorem rounds152_1 : sixRounds 6 (by decide) quarter152_1 = quarter152_2 := by
  decide +kernel

private def quarter152_3 : Vector UInt64 25 :=
  #v[0xda558ed9e7bf732d, 0xecbee6c82d775767, 0x5163a0eb271e054b, 0xa04bda9cba728ba1, 0xae540c4690bb2585, 0xbf58d46ad38d99f9, 0xb908c461e8a08ffc, 0xfb9fe54baf56734c, 0x13291286137bb266, 0x3cafd0d8e3266071, 0x151663a9b5d06434, 0x8c3af3c4f46badc6, 0xbc938d4b95c1fd6, 0x19f6e9d34755fd65, 0x11ae2b5bea995ad3, 0xa24687910d97936a, 0x9b6d16de12456905, 0xae499f5e67b84547, 0xa00a01dcd1bcefb7, 0x1f1386b2b6848668, 0xb197ddaf980a6642, 0xe8f38a0bdabc44b0, 0x9b8bcad92559ac80, 0x7f13d1e727080231, 0xa35c5ca3bbc076fe]

private theorem rounds152_2 : sixRounds 12 (by decide) quarter152_2 = quarter152_3 := by
  decide +kernel

private theorem rounds152_3 : sixRounds 18 (by decide) quarter152_3 = state153 := by
  decide +kernel

private theorem perm152 : KECCAK.f1600 absorbed152 = state153 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds152_0, rounds152_1, rounds152_2, rounds152_3]
  rfl

theorem block152 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes152 ++ tail) state152 =
      KECCAK.Bytes.run 0 tail state153 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes152 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb152 ws)) := by
    rfl
  exact (step state152).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words152).trans perm152))

private def absorb153 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x81 0x82 0x1 0x20 0x60 0x52 0x81)) 1 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x50 0x94 0x1 0x20 0x60)) 2 (by decide) (UInt64.ofBytes 0x20 0x60 0x51 0x40 0x60 0x20 0x60 0x50)) 3 (by decide) (UInt64.ofBytes 0x85 0x90 0x3 0x84 0x80 0x90 0x3 0x81)) 4 (by decide) (UInt64.ofBytes 0x0 0x51 0x61 0x15 0x80 0x15 0xfa 0x5a)) 5 (by decide) (UInt64.ofBytes 0x60 0x3d 0x3e 0x80 0x0 0x60 0x3d 0x57)) 6 (by decide) (UInt64.ofBytes 0x51 0x40 0x60 0x50 0x50 0x5b 0xfd 0x0)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x7f)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0x73 0x50 0x50 0x91 0x51 0x1 0xe0)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xad 0x51 0x61 0x16 0x81 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x80 0x40 0x60 0x57)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79))

private def absorbed153 : Vector UInt64 25 :=
  #v[0xf20b40c3e68f5c24, 0x2b22525fc385aa77, 0x70eb37fea15168d8, 0x9a2a711a434b645d, 0x68eaf2ae38ae163e, 0xbe8c4153832f650, 0x63300701b2193346, 0x6a4d2a9d25c5f0ce, 0xf57136be6b5f1239, 0x1b890050e8173acb, 0xabe6400ed0f35c67, 0x24bf1c6bfadbcee1, 0xb2e827f8764f3465, 0x617bb34b6d033857, 0xb6f3a984ef42b91f, 0x667d47a7cbf2b06, 0x278195bf7669da6e, 0x81b8fa3b779dbe28, 0x2ea035827ba1a8da, 0x646bb2bf3c76687e, 0xe2e862a05655dd72, 0x95e7077a36d36d87, 0xf92c3bcd6436ecfa, 0xf5ae3db30e971f89, 0xeffff2d6ce6f6293]

private theorem words153 : absorb153 state153 = absorbed153 := by
  decide +kernel

private def quarter153_1 : Vector UInt64 25 :=
  #v[0x345dd920219057a0, 0x57ef6598a625dd87, 0xdd85bf8162f098a6, 0x33717cc6de7fe12b, 0xed49c6db17358df4, 0x6eadf6fa6bbf3dc1, 0x5ee8fb09a44e00f3, 0x8fe9d9492ee523f8, 0x18020a788294d991, 0x78196c3c2313e5fd, 0xeb2767ff7c3a0e04, 0x7914eaf5a11c7cec, 0x1d5928b23ee8a9b8, 0xfb0d9ecba6327ea6, 0x4666abfd0a234c5c, 0x6a9bac7b2e2437c0, 0x9f04ebd20c9c9ab4, 0x93d6a5861780a152, 0x18a95565f81d22ac, 0x429f6d67db867318, 0x31a6cf1f9e4677f, 0x14268722b0324f35, 0xc51ec710787b9e43, 0x317a02748fabe967, 0xc25e61f7c9949554]

private theorem rounds153_0 : sixRounds 0 (by decide) absorbed153 = quarter153_1 := by
  decide +kernel

private def quarter153_2 : Vector UInt64 25 :=
  #v[0x45c51c3d0491de06, 0x68a4f269902ed7c7, 0xca1c591703c8577b, 0xdafa4fec75ef8ba1, 0xa7cde1253c437d18, 0xeaeacf28f1ee0e7, 0x9b32879f77db3af1, 0xb3993e265d3eac2a, 0x2af584be44b82745, 0x7d8e782d053ac07b, 0x60fc08fcf62bd353, 0xef9b74bc3cd43e57, 0xfeb4c1bdf03e0b87, 0xf3cdfb7382e73902, 0x95f97d76005d6fa6, 0xa226a34aa0097e79, 0x1827f4b21ed9c4da, 0x6ed10519c7a50fc9, 0x4c93cb5b08242b2f, 0xcd5ea2c51d5f3f9e, 0xf4559e7426b73837, 0x1205e8cb2333c244, 0x9e6836be83868368, 0xa13b3e647e5b4961, 0xfbadb5e7c44b66b1]

private theorem rounds153_1 : sixRounds 6 (by decide) quarter153_1 = quarter153_2 := by
  decide +kernel

private def quarter153_3 : Vector UInt64 25 :=
  #v[0x4b6079d4fd2bce5a, 0xf00c61056ae9ae48, 0xda1fea19d7e8abed, 0x3a4647682f5d636a, 0x8b478cd38bcd8cc8, 0x1c33552cc2fc7894, 0x2951d77bfd086e01, 0xc4b598520779c20d, 0x77fe5f9f7036032b, 0x1557b1bc7ab823e3, 0xc0d6156c78a674f3, 0x32df36fd5b260db0, 0x1d447a001edbb9e1, 0xc01aed54fe5dc495, 0xe4f00d0186c115d9, 0xab31d869ef01f4af, 0xc73e0ad46afee8fe, 0x43b1cf50e276281, 0x64cb8fa6fd8b7965, 0xc24c0b4a58c0a456, 0xe51f9fe09dfeff0c, 0xf90659f381315593, 0xcb7532f9ae10f98b, 0xe7bed45d6e76393b, 0x9a357b178302959d]

private theorem rounds153_2 : sixRounds 12 (by decide) quarter153_2 = quarter153_3 := by
  decide +kernel

private theorem rounds153_3 : sixRounds 18 (by decide) quarter153_3 = state154 := by
  decide +kernel

private theorem perm153 : KECCAK.f1600 absorbed153 = state154 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds153_0, rounds153_1, rounds153_2, rounds153_3]
  rfl

theorem block153 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes153 ++ tail) state153 =
      KECCAK.Bytes.run 0 tail state154 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes153 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb153 ws)) := by
    rfl
  exact (step state153).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words153).trans perm153))

private def absorb154 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x60 0x52 0x1 0x82 0x4 0x60 0x20 0x60)) 4 (by decide) (UInt64.ofBytes 0x45 0x7f 0x52 0x1 0x82 0x24 0x60 0x1c)) 5 (by decide) (UInt64.ofBytes 0x72 0x65 0x76 0x6f 0x63 0x65 0x52 0x43)) 6 (by decide) (UInt64.ofBytes 0x69 0x6c 0x61 0x76 0x6e 0x69 0x20 0x3a)) 7 (by decide) (UInt64.ofBytes 0x74 0x61 0x6e 0x67 0x69 0x73 0x20 0x64)) 8 (by decide) (UInt64.ofBytes 0x60 0x0 0x0 0x0 0x0 0x65 0x72 0x75)) 9 (by decide) (UInt64.ofBytes 0x81 0x90 0x51 0x90 0x52 0x1 0x82 0x44)) 10 (by decide) (UInt64.ofBytes 0x5b 0xfd 0x90 0x1 0x64 0x60 0x3 0x90)) 11 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x93 0x94 0x5b 0x50 0x90)) 12 (by decide) (UInt64.ofBytes 0xb0 0x51 0x61 0x60 0x60 0x5b 0x56 0x50)) 13 (by decide) (UInt64.ofBytes 0x61 0x60 0x60 0x85 0x0 0x60 0x84 0x84)) 14 (by decide) (UInt64.ofBytes 0x5b 0x56 0x8e 0x53 0x61 0x85 0xcd 0x51)) 15 (by decide) (UInt64.ofBytes 0x51 0x80 0x40 0x60 0x57 0x38 0x52 0x61)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8 0x7f))

private def absorbed154 : Vector UInt64 25 :=
  #v[0xcfa07908b4163907, 0x9e13cd0d376a227b, 0x1a8dec9a7857648, 0x496e56c99317266c, 0xd1c4518ca4743669, 0xf56153ecda24c843, 0x3e545ff21e301739, 0x120ae93b915cf23b, 0x54f6a76357ef509e, 0x4f2dcdc018b9264f, 0x96748e05145e3aba, 0x82d943fc00ebc2d5, 0xb77531f8ef1558b2, 0x110e2194a1009acf, 0x1f2eec8cf583240b, 0x34bf703de26c21ff, 0xc3500d5659d8fec5, 0x1380bb4d6e886c69, 0xbc483d5a555bae7c, 0x2cbcd3e58a9d5f36, 0x8d7b4331a3c39194, 0x47c3042fe858b5e0, 0x4c348c01e4b6ead3, 0xfcbb5ae0f248bd60, 0x73c059a6cddaac95]

private theorem words154 : absorb154 state154 = absorbed154 := by
  decide +kernel

private def quarter154_1 : Vector UInt64 25 :=
  #v[0x6509521ad9b45717, 0x39b93245a9a8e220, 0x35044ff1da5b3c22, 0x36b2fb12498294cb, 0x726b50a0726d5d9c, 0x14011813c07cc188, 0xa9b79c2510fd0738, 0x66a96cd93a5766e4, 0xf2b46b816678aaaf, 0xa1c74053224d18de, 0xcdae08a64de3d2e3, 0x8030d6db437a9bed, 0x920740e9d0d83946, 0x2825c18ff67d5bd6, 0xd1f2a0c05cc99f2a, 0xcfb9eeb0f7a16ae5, 0xf1e36e7517f79dcf, 0x540fd2d45029e6d2, 0x524f8aefcd398d83, 0x5801fcf67baa2ea8, 0x601166029d37633f, 0x83698e0238d340c, 0xc07292e7a817b472, 0x8d83dc24aa8d240b, 0xf43e51df6d5e1424]

private theorem rounds154_0 : sixRounds 0 (by decide) absorbed154 = quarter154_1 := by
  decide +kernel

private def quarter154_2 : Vector UInt64 25 :=
  #v[0xcc2dadf7b34928e3, 0x11d53116ff25f876, 0x27ed0d1fdf159d5d, 0x34a38afd024e7a61, 0xdb358a5a487bbbfd, 0x658065e77fff42b8, 0xa884017b14676146, 0x6f7c59813e6ec955, 0x37ecb0204dd951a7, 0xc86170c65998f2d2, 0xc971611666b231d9, 0x8748ddc044f21a6, 0xbc638f8fcc013ae1, 0xa679b72c5837ab67, 0x503d6f317525bc52, 0xec0e452b0ad0927f, 0xbedd7a117e464696, 0x58de8e0873046772, 0xcabf9a4dcc39ad5e, 0x44a32fa6a8ff709c, 0xff26c1e7f832b980, 0x3b1a6abe0e5f5ea7, 0x7389a464e2cf1ed4, 0xffdc7696deb52070, 0xa1cbfdf927a073b7]

private theorem rounds154_1 : sixRounds 6 (by decide) quarter154_1 = quarter154_2 := by
  decide +kernel

private def quarter154_3 : Vector UInt64 25 :=
  #v[0x73f8ec3f321787e8, 0xb6df3cbba4e1a260, 0x7bea775023251d56, 0x9b5f63e377704b4b, 0x5a9b2d8dcb0fe627, 0x4bec7867cf71834f, 0x8d43419b7bf68272, 0x6d19d97d99394053, 0xf63e3d2afd592a22, 0xa9fb34b81d3851da, 0x89afcfadfde856ef, 0xe4531265fe0142c1, 0xba3ab49a25ed2f13, 0x3329085c7967aa91, 0x9918f6cf994ce58a, 0xa18122778d26ffd6, 0x20bb28ccea1608ac, 0x253109374fc011bf, 0xbfa14fb0570be7aa, 0x70a668eb057b8adb, 0x77187dbc7f2da7b, 0x225ce6ccae1b640a, 0xd2d28d9047fc3837, 0x8f1ec9dab2e52d74, 0x1b1b37ff6764dec5]

private theorem rounds154_2 : sixRounds 12 (by decide) quarter154_2 = quarter154_3 := by
  decide +kernel

private theorem rounds154_3 : sixRounds 18 (by decide) quarter154_3 = state155 := by
  decide +kernel

private theorem perm154 : KECCAK.f1600 absorbed154 = state155 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds154_0, rounds154_1, rounds154_2, rounds154_3]
  rfl

theorem block154 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes154 ++ tail) state154 =
      KECCAK.Bytes.run 0 tail state155 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes154 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb154 ws)) := by
    rfl
  exact (step state154).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words154).trans perm154))

private def absorb155 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 1 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 3 (by decide) (UInt64.ofBytes 0x82 0x4 0x60 0x20 0x60 0x52 0x81 0x0)) 4 (by decide) (UInt64.ofBytes 0x1 0x82 0x24 0x60 0x1d 0x60 0x52 0x1)) 5 (by decide) (UInt64.ofBytes 0x73 0x65 0x72 0x64 0x64 0x41 0x7f 0x52)) 6 (by decide) (UInt64.ofBytes 0x20 0x6c 0x6c 0x61 0x63 0x20 0x3a 0x73)) 7 (by decide) (UInt64.ofBytes 0x63 0x2d 0x6e 0x6f 0x6e 0x20 0x6f 0x74)) 8 (by decide) (UInt64.ofBytes 0x0 0x74 0x63 0x61 0x72 0x74 0x6e 0x6f)) 9 (by decide) (UInt64.ofBytes 0x90 0x52 0x1 0x82 0x44 0x60 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x1 0x64 0x60 0x3 0x90 0x81 0x90 0x51)) 11 (by decide) (UInt64.ofBytes 0x86 0x60 0x60 0x0 0x60 0x5b 0xfd 0x90)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x87 0x85 0x16 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x90 0x51 0x80 0x82 0x80 0x51 0x40 0x60)) 16 (by decide) (UInt64.ofBytes 0x5b 0x83 0x83 0x80 0x90 0x1 0x20 0x60))

private def absorbed155 : Vector UInt64 25 :=
  #v[0x4ffa2d50fb47d35, 0xe79ebd2e7c3d7bff, 0x583e8d18de6260df, 0x40467fab33f68b33, 0xbfdd16dae6bb3656, 0xa7e08d2fc94e1d2c, 0x5ea5b9d95a61ffba, 0x2c6d36e3e5cbb046, 0xb664c00943782443, 0x397382cebd0829f9, 0x1ef052d672171371, 0x96acd40b8830bc56, 0x89dd4077448915e5, 0xf367f5fefb6407f7, 0x3877ccd81ad6d205, 0x65bb9f6490c0d691, 0x473f6135ca245982, 0x845851d4118f5490, 0xef332c37bb99fcee, 0x321dc9442eac9d0c, 0xa0a195a2124bd0a, 0x17d0f6207b06f15, 0xe2bc32e4c08d3011, 0xfa657dadf56b9246, 0xfcc37b0d06fc158f]

private theorem words155 : absorb155 state155 = absorbed155 := by
  decide +kernel

private def quarter155_1 : Vector UInt64 25 :=
  #v[0xa0315b42c6a775cc, 0x3720b9487a017644, 0xf1466a8468f062ab, 0xa6cae6a1cb53c9c8, 0x514def6aedf4e1a9, 0xb9ad9c1b912c9dae, 0x745c0abd617f544b, 0x54f99b8fc6dd0095, 0xf5baa474df1c7582, 0xaaae109cd1d24c4d, 0x5ad9e2eca4541f9, 0x688dbab872496711, 0x1dc737e08bfd8e5a, 0xbf5a3077bc1232e, 0xbb0da0f7250aa585, 0x6bcdcc3f3c1501d2, 0xde6fe69c5b218535, 0x6602245ea0ff8dae, 0x7b08b6d1ba009889, 0x8de6a96ba90a4ef6, 0x5444931807e441a4, 0x58a79d4fe42b7257, 0xc420b80bc40af37c, 0xf3039f26afb7e508, 0xb7d549da0603419f]

private theorem rounds155_0 : sixRounds 0 (by decide) absorbed155 = quarter155_1 := by
  decide +kernel

private def quarter155_2 : Vector UInt64 25 :=
  #v[0x8bd12042c755e922, 0xd9ff5dcde1424f85, 0x720d93acfa5e58ad, 0xc91c992fa31d2b83, 0xce310b09d4f9b7b1, 0xf065b9aff19fb4c7, 0xcf5c762df33a8d8a, 0xba736a9ab2e38178, 0x90b3ebfd1a8dea23, 0x9b31fdae91c16c5a, 0x116a7db3b56a7a90, 0xf97c48aa1af154ea, 0xf22e67c441c023f, 0xe93e000e92ac92d3, 0xae9f2eacf857ba7b, 0x982086cdf57be0c, 0xdd47e107202d6887, 0xb687501e9929fbd, 0x69999233c1c29a1c, 0xcd7238f7740ae3f4, 0xceb7a83baa2d693a, 0x7a3f1838bd77d981, 0xe670015dcbcf35a8, 0xab5b8bffe78e04ac, 0xb3f98e1ba6320c6e]

private theorem rounds155_1 : sixRounds 6 (by decide) quarter155_1 = quarter155_2 := by
  decide +kernel

private def quarter155_3 : Vector UInt64 25 :=
  #v[0xfc61b457a5b7438f, 0x95ac1a76ba555f16, 0x5e8936dde04091de, 0xc108c414280d003d, 0x46c49f3153940b73, 0xa52535065e2bf865, 0xe7ee6311e253de4a, 0x755e2dbff3f55044, 0x5c5f4674f773ce5d, 0x53e6de4e5533fac8, 0x701361cc1e39112, 0xb97045d9e5393dff, 0xc6453dcdd1fd2331, 0x941fe915f7beaec6, 0x8c702a69bbdf1e1a, 0x67f215ea7108d82f, 0x41f833bba966e1c4, 0x3ac31fe2e71e8a41, 0x5ca95cef7c2dfe8, 0x8877345392f33667, 0x71a4f26b7426c37b, 0x6b9316a9525a388d, 0x791bf661d2242254, 0xb10a2969a6bc0143, 0x629fb4ce9595cb81]

private theorem rounds155_2 : sixRounds 12 (by decide) quarter155_2 = quarter155_3 := by
  decide +kernel

private theorem rounds155_3 : sixRounds 18 (by decide) quarter155_3 = state156 := by
  decide +kernel

private theorem perm155 : KECCAK.f1600 absorbed155 = state156 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds155_0, rounds155_1, rounds155_2, rounds155_3]
  rfl

theorem block155 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes155 ++ tail) state155 =
      KECCAK.Bytes.run 0 tail state156 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes155 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb155 ws)) := by
    rfl
  exact (step state155).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words155).trans perm155))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
