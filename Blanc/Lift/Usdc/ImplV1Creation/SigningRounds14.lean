import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb84 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x18 0x2c 0x61 0x15 0x15 0x15 0x14 0x16)) 3 (by decide) (UInt64.ofBytes 0x8b 0x7f 0x5b 0xfd 0x80 0x0 0x60 0x57)) 4 (by decide) (UInt64.ofBytes 0x13 0x14 0x59 0x16 0x53 0x9c 0x7 0xe0)) 5 (by decide) (UInt64.ofBytes 0x19 0x84 0xf2 0xa4 0xd0 0x1f 0xcd 0x44)) 6 (by decide) (UInt64.ofBytes 0xe3 0xaf 0xda 0xa3 0x22 0x97 0x7f 0x49)) 7 (by decide) (UInt64.ofBytes 0x61 0xe0 0x57 0x64 0x6b 0x6f 0x18 0xb4)) 8 (by decide) (UInt64.ofBytes 0x82 0x5b 0x56 0xbe 0x23 0x61 0x41 0x2c)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x83 0x80 0x51 0x40 0x60)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x16 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x73 0x82 0x1 0x20 0x60 0x52 0x81 0x16)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed84 : Vector UInt64 25 :=
  #v[0xba407a84708f3eae, 0xef123e8ecf49051e, 0xbd4f9feab6cc9319, 0xd78a151757e4fc97, 0x133ac4580cf9ffbe, 0xbf035a43c8cdec31, 0x423d06d62ea241f8, 0xe66fa04d7e9d5a9c, 0x4547cb73112deab4, 0x337f02653741a027, 0x7771de2227906d2d, 0x64392725b409c9c6, 0x8068b2d72bcb1df2, 0x5409997cd96ce9b, 0x3184e8b680f3684, 0xe86ec451e0e3d6d1, 0x1d93acc85f41aa46, 0xd6638ef8202adce9, 0xb58937f02cd9e103, 0xf6b02c9814057cd2, 0x425707302957c55f, 0x30980b868428f6c1, 0xab025c105a92e660, 0x6a30b48d034ed690, 0x6d2a22486beebff0]

private theorem words84 : absorb84 state84 = absorbed84 := by
  decide +kernel

private def quarter84_1 : Vector UInt64 25 :=
  #v[0x385f726b921f4fc2, 0x7e918b8563e895fc, 0xc76b6e056e1ea090, 0x661e7b33d8820a8a, 0x6a653f89fe667af5, 0xeeb529af6f69aed1, 0x291731c1982962bb, 0x63264ca43e74fc53, 0xed85f850dd1add0f, 0xa25e64f4bbf60c6a, 0x6d919103301db18c, 0xde03b0a604926700, 0xb3967729207e13e6, 0xc42b660f84b3311, 0x3ffedd513a8afc48, 0x5f46e47b087b7ba4, 0xa9526fdc2bf15d6a, 0x1705bfb90aace3c8, 0x42e2c67f5fba5d24, 0x3f514d637a80b2d9, 0xccd65f833dc122e9, 0xd49070dbd2a81ef2, 0x8c4584ab6bdb58c4, 0x9def627656e282d, 0x8f6f4a31e6763cf8]

private theorem rounds84_0 : sixRounds 0 (by decide) absorbed84 = quarter84_1 := by
  decide +kernel

private def quarter84_2 : Vector UInt64 25 :=
  #v[0x316ccfd031e6c310, 0xa8d45dcb761ecfde, 0xc7eaac8f1b686822, 0x39c2a3daeae81bea, 0x1ab3cc15304e4497, 0x631c4c6e9513e0dd, 0xa5e5a59e1578f1c5, 0x6b47d61971547a85, 0xc47b4cff9845cc4d, 0xadc2948c48e32366, 0x2ce4ed5dc0c8d961, 0x985373c0d1a1a6b9, 0x26effe93ca078539, 0x5c440e9b6663c4ae, 0x6f559ff9036a45b0, 0x3c5eb25928382e32, 0xa81a8fe12a6d53b7, 0x8abfda57365305f2, 0x179d575da37ffaee, 0xe24ece9bdf9b4f34, 0x4d5a56c8e403740d, 0x3d253720f362b8ee, 0xd7bdc13aa598e297, 0x942a762d3cd59e07, 0x33f576610c93e771]

private theorem rounds84_1 : sixRounds 6 (by decide) quarter84_1 = quarter84_2 := by
  decide +kernel

private def quarter84_3 : Vector UInt64 25 :=
  #v[0x2570b65ea008c8ed, 0x74fbab72216cc91b, 0x55f57cf06ac1a1b9, 0x77ea9bdac1060244, 0x24f64ddde7792d8c, 0x8d3f2f4cf962b145, 0xd862732cd5a4b2bf, 0x6934564d80ce9ee1, 0x10f760485b806749, 0x88cf98ea52d12a9c, 0xc002fdbcc50e8b72, 0xeb70b3afbffec1e6, 0xb28715897e4020e3, 0x697b6130e03c4bf6, 0x380637ae8be487bc, 0x41d80a90dd215ca8, 0x12033b9617f60c15, 0xc8cc65d0c2d665d, 0xc94d02690c682b9e, 0x5b62436e892463d, 0x8f20a320cd52967b, 0xd22903f2a77c38c0, 0xea17013531365bf2, 0x60bad4449d4b5c7a, 0xd96e526714c5e18b]

private theorem rounds84_2 : sixRounds 12 (by decide) quarter84_2 = quarter84_3 := by
  decide +kernel

private theorem rounds84_3 : sixRounds 18 (by decide) quarter84_3 = state85 := by
  decide +kernel

private theorem perm84 : KECCAK.f1600 absorbed84 = state85 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds84_0, rounds84_1, rounds84_2, rounds84_3]
  rfl

theorem block84 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes84 ++ tail) state84 =
      KECCAK.Bytes.run 0 tail state85 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes84 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb84 ws)) := by
    rfl
  exact (step state84).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words84).trans perm84))

private def absorb85 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x16 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x80 0x51 0x40 0x60 0x50 0x50 0x50 0x92)) 6 (by decide) (UInt64.ofBytes 0x81 0xbf 0x2c 0x61 0xa1 0x90 0x3 0x91)) 7 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x5b 0x56 0x47 0x2e 0x61)) 8 (by decide) (UInt64.ofBytes 0x61 0x90 0x54 0x90 0x0 0x60 0x2 0x60)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x4 0x90 0xa 0x0 0x1)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x16 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x33 0x16)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed85 : Vector UInt64 25 :=
  #v[0x866f4ea28fb7a095, 0xf5c891ac41626323, 0x75150d062c12b435, 0xef4746b8f51bdd2f, 0x607740acb5ed834e, 0x2d25f9313cb8c54f, 0x41f7a6f9effd75a, 0x5b3d2ad1aef33c82, 0x647f5139e97777b1, 0xf79256ddcff9f9cd, 0x291af0ee6c63fc08, 0x7379afce829439fb, 0xc8911786a3dab24b, 0xfe4b8d15ff1290a0, 0x44f711bb8e9a6ac5, 0x5a37a1b69ac28a05, 0xd46fea1983b69bad, 0xd97ecd668bf286c4, 0x9ccee9357c1221e7, 0xcffa883b789ec81f, 0x2fa62bd4eb80406e, 0x57af8d9efa2eb9f4, 0x27d7d3fbd9bd2972, 0x7aa46faa6a32d49d, 0xb1c6aa05866ca62e]

private theorem words85 : absorb85 state85 = absorbed85 := by
  decide +kernel

private def quarter85_1 : Vector UInt64 25 :=
  #v[0x8f93078292a84417, 0x8d6437612182eadb, 0x8e71675900c9f78c, 0xfe9af7da10583744, 0x4c0c9064fc273340, 0xaa174838ce468813, 0x11f71160fc8964a5, 0x62a9c68a0a135ecd, 0xd4a79d27ee2b5834, 0xb528207c49b61e6, 0xf41e824b83c773af, 0x18738ca3758af551, 0x36e45711dea1cae, 0xff8f9b671e41b602, 0xf4598ca336778bed, 0x4e8ad21d5d27b7bc, 0xf759620775cc1722, 0xb5131aad8fa6881c, 0x41ece3d4a08f59fa, 0x5783dbe8e4a997e8, 0x9c44a056b59baaa0, 0x4c304f05a880da8b, 0x3a97a212cf9e0f81, 0x1fb430b0f0f67389, 0xd77dd5453f041348]

private theorem rounds85_0 : sixRounds 0 (by decide) absorbed85 = quarter85_1 := by
  decide +kernel

private def quarter85_2 : Vector UInt64 25 :=
  #v[0xe40197fa23397010, 0xbacdb10d6d57c647, 0xdda39b5c7d369165, 0x4cdefec3d29d147, 0xbce2bae500a119a7, 0x8fe56062f3f52661, 0x45ebe14d1f945076, 0x51b8749217cb219d, 0x76d9c33598383f3, 0x4cee05f7e6e345b2, 0xf6d4b3b326eaff8c, 0x911f55a9b9a709e, 0x283412b34e396117, 0x80521c3eb546ff34, 0xf2459ccc07623a99, 0x1777f4268de33235, 0xed16ab1fc0d93fad, 0x1bda3a2b0d9e5ada, 0x7832b3c186e9ff63, 0xab4d2517a2b057a, 0xae5b8018ad366712, 0x4d521be462c64856, 0x2805a9ee972f171f, 0xcbac7f2bf1ca6d9a, 0xdd7e5ac3c9ebd818]

private theorem rounds85_1 : sixRounds 6 (by decide) quarter85_1 = quarter85_2 := by
  decide +kernel

private def quarter85_3 : Vector UInt64 25 :=
  #v[0x20c1c78fd0e95c10, 0xd3f21d68e8888344, 0xc31602323ecbfcc3, 0xa546472079ee1d52, 0x7505d3562fbc78ca, 0x11f1a4193ab975e8, 0xfd9f71d11f37a41e, 0xd0756a987d8aa0f1, 0x8fc55665882bd9c9, 0x25de65dc21424751, 0x564d76b7721e0be5, 0xa9fe6849df0bdc43, 0xdafabb3daca85fc8, 0xc5d59993d0426426, 0x8afe7ca70744a415, 0x987b00cabcf3d7f3, 0x66a5f0792f7651ee, 0x66b29d843e9a95ef, 0xc8429b1bef512065, 0x2c78dc6ce987f586, 0xb20678956d154547, 0x1a000c5ba7b333f9, 0x843bbd6ec92ef321, 0x77a7e1d639f23337, 0x1e2bc8e2e4cf5bee]

private theorem rounds85_2 : sixRounds 12 (by decide) quarter85_2 = quarter85_3 := by
  decide +kernel

private theorem rounds85_3 : sixRounds 18 (by decide) quarter85_3 = state86 := by
  decide +kernel

private theorem perm85 : KECCAK.f1600 absorbed85 = state86 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds85_0, rounds85_1, rounds85_2, rounds85_3]
  rfl

theorem block85 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes85 ++ tail) state85 =
      KECCAK.Bytes.run 0 tail state86 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes85 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb85 ws)) := by
    rfl
  exact (step state85).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words85).trans perm85))

private def absorb86 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x60 0x57 0x1e 0x2d 0x61 0x15 0x15 0x14)) 2 (by decide) (UInt64.ofBytes 0x3 0x60 0x1 0x60 0x5b 0xfd 0x80 0x0)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x83 0x0 0x60)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x16)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x81 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x90 0x1 0x20 0x60 0x52)) 10 (by decide) (UInt64.ofBytes 0x61 0x0 0x60 0x20 0x0 0x60 0x1 0x20)) 11 (by decide) (UInt64.ofBytes 0xff 0x60 0x81 0x54 0x81 0xa 0x0 0x1)) 12 (by decide) (UInt64.ofBytes 0x2 0x15 0x15 0x83 0x90 0x16 0x19 0x2)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x80 0x50 0x55 0x90 0x17)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x18 0xe6 0xa4 0xff 0x7f 0x16 0xff 0xff))

private def absorbed86 : Vector UInt64 25 :=
  #v[0x9a5afea72effd8ef, 0xe053f28207df72c0, 0xf5dceed35ebe3f9b, 0x161678fb414bd53e, 0xb5c354ff0906ff92, 0x8fb121745f633679, 0x5bf4536ae73325be, 0xdb1c73e5af3d5430, 0x76352509602f8044, 0x92b27ff3f58db596, 0x9a238e30b7708d47, 0xd61d4c4e3d464dc0, 0x8eaeaef969efc1f4, 0x3a1b7587759ae6c2, 0xf0b0e338cded6c0d, 0xbda8f83bd9e79372, 0xec09d6b980cd6107, 0x5904cee081b3a903, 0x206c8f2e721d16e0, 0xfaac8233288dee9, 0x41d79da9b74c6cc8, 0x162415c1418eeb6d, 0x49b709a7a5bf5dac, 0x6318a108b59d048d, 0xe4ab6d146dd990e6]

private theorem words86 : absorb86 state86 = absorbed86 := by
  decide +kernel

private def quarter86_1 : Vector UInt64 25 :=
  #v[0xd843218fc8cad836, 0xe28a6b61ceb8f52d, 0xf941efc5af183c5b, 0xffbeb14aa1245ab9, 0xef024a8430dee180, 0xcefccb7c7593d9a6, 0xb0e04047a3a9e52a, 0x52aa063988327a59, 0x4e2bd8fdba1f1306, 0x9cf13d5ac565bf49, 0x700eaf232576fb22, 0xc015f37e8ab9ff16, 0x9912a1720b628682, 0x22523976137114ec, 0x29095e15990e56b2, 0xda9db01189e0d13e, 0x22790bfc5bfc1e46, 0xeca8ccbb69a749af, 0x5278eb5f84b7edce, 0xdae876f9b4b6227c, 0xb509cbeef6c47720, 0x25ce27bd6cf9b282, 0xe24c858d8b9ad976, 0xc6446db7f9daaca4, 0xdd7a4e6ab5da1cc0]

private theorem rounds86_0 : sixRounds 0 (by decide) absorbed86 = quarter86_1 := by
  decide +kernel

private def quarter86_2 : Vector UInt64 25 :=
  #v[0xc90af2d8c71da770, 0xa08a33a4f8b85f7c, 0xbfbfede1e82fd9f9, 0x745bb2dd88c379bc, 0x8224861b5befcfeb, 0xdf818acb8c4eb182, 0x192655cb76b7b18b, 0xa85c788c874081ed, 0x11fe1ac9d23c7ede, 0x8fc5818f989e7bc8, 0xbc4767924568e841, 0xd9a15a7bd4260b4d, 0x12330beaadecc3bb, 0xb46fc1eea88983e2, 0x7f0847ca5bf7cb35, 0xdf108380b398992e, 0xc77eb21ccaa50437, 0x2563efc4a5817f0a, 0xbc7176c5180a4b2d, 0xa25ae22d186e68d1, 0x21666c157a4ad6a3, 0xc45c3b2fe4cd75af, 0x6854d66e2fda8a5c, 0x35a3a30f8e51a584, 0xb1b2aef0e6e3d7c5]

private theorem rounds86_1 : sixRounds 6 (by decide) quarter86_1 = quarter86_2 := by
  decide +kernel

private def quarter86_3 : Vector UInt64 25 :=
  #v[0x41e6f1152cc81832, 0x55395f7d2ce5c79a, 0x9a82cfb01051b0bc, 0x4539abf62893e3d4, 0xd825ed1af798411e, 0x71a4a1dc612424ef, 0x93bcea09360f2dc7, 0x4fda2558403777cd, 0x54e2dbc43ed20fe2, 0x8bb0bf1898831ba, 0x8c9dd8a869ad1779, 0x36678f56ce1e4fc0, 0x33d0e578f5d2fb56, 0x840c60e33de407f5, 0x4bd12a089efc03a0, 0x4963413dacff958b, 0x13b3f8d447fd292b, 0xaf8611711e8a97a9, 0xda72d01cadee6789, 0x4c17bc3074f9e86c, 0x88df5b21403d5cff, 0x44a854ef65795947, 0x9417015c75bdcb11, 0x97a1acbfd34e05df, 0x75cf3142931663c8]

private theorem rounds86_2 : sixRounds 12 (by decide) quarter86_2 = quarter86_3 := by
  decide +kernel

private theorem rounds86_3 : sixRounds 18 (by decide) quarter86_3 = state87 := by
  decide +kernel

private theorem perm86 : KECCAK.f1600 absorbed86 = state87 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds86_0, rounds86_1, rounds86_2, rounds86_3]
  rfl

theorem block86 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes86 ++ tail) state86 =
      KECCAK.Bytes.run 0 tail state87 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes86 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb86 ws)) := by
    rfl
  exact (step state86).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words86).trans perm86))

private def absorb87 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x52 0x28 0xcf 0x65 0x25 0x69 0x77 0x17)) 1 (by decide) (UInt64.ofBytes 0x6b 0xa8 0x6e 0x51 0xd1 0x8f 0xc8 0x8f)) 2 (by decide) (UInt64.ofBytes 0x5a 0x57 0xfa 0x35 0x52 0x7 0xda 0x56)) 3 (by decide) (UInt64.ofBytes 0x60 0x51 0x40 0x60 0x55 0xb8 0xa4 0xf6)) 4 (by decide) (UInt64.ofBytes 0x50 0xa2 0x90 0x3 0x91 0x80 0x51 0x40)) 5 (by decide) (UInt64.ofBytes 0x0 0x60 0x3 0x60 0x0 0x60 0x5b 0x56)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x83)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x90 0x1 0x20)) 13 (by decide) (UInt64.ofBytes 0x90 0x54 0x90 0x0 0x60 0x20 0x0 0x60)) 14 (by decide) (UInt64.ofBytes 0xff 0x60 0x4 0x90 0xa 0x0 0x1 0x61)) 15 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x90 0x91 0x50 0x90 0x16)) 16 (by decide) (UInt64.ofBytes 0x15 0x15 0x15 0x11 0x82 0x82 0x0 0x60))

private def absorbed87 : Vector UInt64 25 :=
  #v[0xfd3a267c3a0a64b, 0xdb2ffd303f551fc0, 0x3d72b94b84a9cfea, 0x3e37b834b70e72bf, 0x5b0e61eb2522deeb, 0xdd79ae9c5e0b52af, 0xebb6a38ad3da1aca, 0x311dabe0ba5dccba, 0x875ee14845265f95, 0x541408835da288f5, 0xbed95f9929d1c70b, 0xfef3712c09ed970b, 0x8cda12727c77cb36, 0x68ab7e16658d786e, 0xec21a959b5856c9e, 0x2a5ad35dda8e6047, 0xffdf8fc29b1b5817, 0xd48167c6b64334fb, 0xb95e1fcdfb272c5f, 0x9c499b43359db89, 0x941d5b6148ea839c, 0xdee6cc19eda7f594, 0x434048c825f77fe5, 0xde5fc980ee2fcd08, 0x4a24500f3450d4aa]

private theorem words87 : absorb87 state87 = absorbed87 := by
  decide +kernel

private def quarter87_1 : Vector UInt64 25 :=
  #v[0xdfde5b1ed95078aa, 0xf3854d19d5873bc7, 0x3d5f53898ec62431, 0x96bf331ce7eaa2e5, 0xce4bc15e7d3bb55d, 0xb592acaaa6dd8f66, 0x9d56055d6b57f90c, 0x367fd5f636e62e2a, 0x2cf41559fd98b70e, 0xbe3307dd645426ee, 0xbcd7b889c854807f, 0x2bf0af4734536cc7, 0x17670b6582011fe3, 0xdd95b0b8272bafd3, 0x10644662c444e2bb, 0xfc5f4b978be11fcf, 0xc83830933cf1d2, 0x60c1b07bf339782b, 0x196228e97162fa7a, 0x483a5629b1a13e76, 0x2f8d64209411567e, 0x4d60fc109cd2262b, 0x7a728b8c020e497, 0x74ab1317e8a22b11, 0x58087b4a4febd4d4]

private theorem rounds87_0 : sixRounds 0 (by decide) absorbed87 = quarter87_1 := by
  decide +kernel

private def quarter87_2 : Vector UInt64 25 :=
  #v[0xa159124ee8ed9af5, 0x528eca166ed2bfe, 0x526470e4ddf516db, 0x8d7a953f93306ce1, 0x336ace2810393667, 0x27f7025bee215fa3, 0xec96ab25eb686f77, 0xb21c9e2381d33fdd, 0x7c0f682f244fffd3, 0xdfabd21fc24d4ad2, 0xd91a996f6443b1b0, 0xa63d1f85f260a04c, 0xbc32a92e63951e19, 0xc2f816c371c001bc, 0x17d1b39a3f399751, 0x278c7d12881c1971, 0x1ef0b64408788ed5, 0x15c53f22a3748f0d, 0x13f8aadfe0b8abab, 0xefaaf2ad66fcba26, 0x753c1f60ba3aec9, 0x35778517da3cc111, 0x9de1b138b6c5783d, 0xb153d441ec7a83e6, 0x72c400ac7ec2e884]

private theorem rounds87_1 : sixRounds 6 (by decide) quarter87_1 = quarter87_2 := by
  decide +kernel

private def quarter87_3 : Vector UInt64 25 :=
  #v[0xeff01f723b6abf35, 0x38437056b2628fc5, 0x2a8f9c859f8ebcc7, 0xdedfe6604664a1dc, 0x95b27f6585ed9b59, 0x5cd54c75d0c7a879, 0x9b1a9ea9ce3c8f96, 0xb27964487ae185fd, 0x775060b378bb6187, 0x4d7d601aa265d04a, 0x396a5b4724054b50, 0x31da31c9be96a0c5, 0xdd75357e222e04da, 0x7cfeb700cf2b340d, 0xfadb657178444e0, 0xccf9b256cdf271b9, 0xc0d325a27fb1cbef, 0x831ab537940b667d, 0xa678d31fb3bc84f6, 0xa2a7161b8d794447, 0x7fa2e41b8999437, 0xa7ada36efa30ff93, 0xdf198ceb555e281a, 0xdf49f3fa8cdb1795, 0x4bc4a2d6618186e2]

private theorem rounds87_2 : sixRounds 12 (by decide) quarter87_2 = quarter87_3 := by
  decide +kernel

private theorem rounds87_3 : sixRounds 18 (by decide) quarter87_3 = state88 := by
  decide +kernel

private theorem perm87 : KECCAK.f1600 absorbed87 = state88 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds87_0, rounds87_1, rounds87_2, rounds87_3]
  rfl

theorem block87 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes87 ++ tail) state87 =
      KECCAK.Bytes.run 0 tail state88 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes87 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb87 ws)) := by
    rfl
  exact (step state87).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words87).trans perm87))

private def absorb88 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x83 0x81 0x5b 0xfe 0x57 0x20 0x2e 0x61)) 1 (by decide) (UInt64.ofBytes 0x56 0x50 0x50 0x91 0x92 0x50 0x90 0x3)) 2 (by decide) (UInt64.ofBytes 0x50 0x90 0x1 0x83 0x81 0x0 0x60 0x5b)) 3 (by decide) (UInt64.ofBytes 0x2e 0x61 0x15 0x15 0x15 0x10 0x81 0x82)) 4 (by decide) (UInt64.ofBytes 0x92 0x50 0x90 0x80 0x5b 0xfe 0x57 0x3e)) 5 (by decide) (UInt64.ofBytes 0x0 0x60 0x80 0x5b 0x56 0x50 0x50 0x91)) 6 (by decide) (UInt64.ofBytes 0x81 0x54 0x81 0xa 0x0 0x1 0x61 0x80)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x16 0x19 0x2 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x83 0x90)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x5b 0x56 0x50 0x50 0x55 0x90 0x17 0x2)) 14 (by decide) (UInt64.ofBytes 0x1 0x60 0x81 0x1 0x60 0x54 0x80 0x82)) 15 (by decide) (UInt64.ofBytes 0x16 0x3 0x2 0x0 0x1 0x61 0x15 0x16)) 16 (by decide) (UInt64.ofBytes 0x52 0x0 0x60 0x90 0x4 0x90 0x2 0x60))

private def absorbed88 : Vector UInt64 25 :=
  #v[0x4e5ae2c4f3df644b, 0xe883d67c6c685acd, 0xf64a2a4ae4a8065, 0x8797bfbada2eb78f, 0xe508008ae700ab6f, 0xfb41ad8ba015e4cf, 0xc3ff82d72019c969, 0xe8963e802dec699b, 0x6d77f3a9734fb5cf, 0x6632a77d09cbd993, 0x1cbf31b38beb2fa9, 0xe69052e71c8b083, 0xa0e85e4062c06922, 0x69fcf40cad3a8369, 0x2389a4f4db9a1a0d, 0x8cae227625b34490, 0xadb2afc3682a2b77, 0x869dcc8ca8959202, 0x718753288aa216fb, 0xc31a829089fbd450, 0x1826b06e5d10302, 0xf62785c12903dd1d, 0x1d1400170ddbcc83, 0x9cc37e27a24e6792, 0xd1c3663cea707cbc]

private theorem words88 : absorb88 state88 = absorbed88 := by
  decide +kernel

private def quarter88_1 : Vector UInt64 25 :=
  #v[0xfea6f48520dfe9b3, 0x37d60b94d300f5a7, 0x4791ebda5c93e7fb, 0x127633eb92a195ff, 0x838b974d7a248b26, 0x84a31dbe29c6fb62, 0xa4de2993987fa357, 0x7065f63818035e07, 0x1fd089fdbbcc546, 0x32f5403843c818de, 0x26dd22972239c1c3, 0x877159a0915f0ab1, 0xa24951ddde027460, 0x3446be5b627d189a, 0x64e1de1bce560e87, 0x2057abd29da66ddc, 0x90e83e9ba3891c3e, 0x48e63996d622f85b, 0xd0f2e06542fd4cad, 0x273083c2e6156226, 0xc7d30d024b5a4fd5, 0x4c457b11eb972810, 0xe7b9b945d8d373fb, 0x50dd964af942e8cb, 0xd395fd9b7be43fc8]

private theorem rounds88_0 : sixRounds 0 (by decide) absorbed88 = quarter88_1 := by
  decide +kernel

private def quarter88_2 : Vector UInt64 25 :=
  #v[0x40b7be85b956e713, 0x3055667a5b7e7c2f, 0x53fb4394a7f33f3b, 0xb63584862801fd3a, 0xbea804951d36e637, 0x1d908392620a3259, 0xb84f5969bf9fae37, 0xb3be27c798545ff8, 0x1ff8ac2f485bf3c6, 0x59fd23f1c1c0bd18, 0x58ba92cc3b9fb7f7, 0x5b87ef1c55e47055, 0x4e8f297b74a85432, 0x62e34afbc000b0ae, 0x47d4e6e91b56b595, 0x3665cc139a42e480, 0x9ebb8e098ca03046, 0x9cf69e81da44a8cb, 0xe2b4acd1c69c1e48, 0x2aed7594155b1c05, 0x3297f81eb181af6d, 0xeb15de8cda010a37, 0x37df4f7b2fc62491, 0xb38ffb5543b11d14, 0xce3c402764ecaa35]

private theorem rounds88_1 : sixRounds 6 (by decide) quarter88_1 = quarter88_2 := by
  decide +kernel

private def quarter88_3 : Vector UInt64 25 :=
  #v[0x31f98d2204a21c00, 0x1255648f4d369a2b, 0xf1f52a24ed632892, 0x3b67d4cc096aeb95, 0x77b6b34b137c9558, 0x1c873a1583c97e45, 0x20007f400f4aa2c9, 0x87c40185469dffa6, 0x3f961bb85ea73b74, 0xef99b603eb70d8a9, 0x51eeb3f4dec3e3c7, 0x8d8cc37e525cb662, 0x6ac4ab44eb700a, 0xa972eca115b39221, 0xfed6e6886b25143b, 0xa68f1d639fc61880, 0x91b8c36b58f2b7bd, 0x838c07ee307e8751, 0xbf978b1699a6e0ec, 0xf5fed992f94ba78f, 0x10a0802eff445fc9, 0x40f026c218bed39d, 0x6f1ecddf362b8bc1, 0xee697448dd4b323c, 0x29cbdbc3391eb213]

private theorem rounds88_2 : sixRounds 12 (by decide) quarter88_2 = quarter88_3 := by
  decide +kernel

private theorem rounds88_3 : sixRounds 18 (by decide) quarter88_3 = state89 := by
  decide +kernel

private theorem perm88 : KECCAK.f1600 absorbed88 = state89 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds88_0, rounds88_1, rounds88_2, rounds88_3]
  rfl

theorem block88 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes88 ++ tail) state88 =
      KECCAK.Bytes.run 0 tail state89 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes88 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb88 ws)) := by
    rfl
  exact (step state88).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words88).trans perm88))

private def absorb89 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1f 0x60 0x90 0x20 0x0 0x60 0x20 0x60)) 1 (by decide) (UInt64.ofBytes 0x92 0x1 0x81 0x4 0x90 0x20 0x60 0x1)) 2 (by decide) (UInt64.ofBytes 0x57 0xcb 0x2e 0x61 0x10 0x1f 0x60 0x82)) 3 (by decide) (UInt64.ofBytes 0x80 0x83 0x16 0x19 0xff 0x60 0x51 0x80)) 4 (by decide) (UInt64.ofBytes 0x56 0xf9 0x2e 0x61 0x55 0x85 0x17 0x1)) 5 (by decide) (UInt64.ofBytes 0x85 0x1 0x1 0x60 0x1 0x80 0x82 0x5b)) 6 (by decide) (UInt64.ofBytes 0x91 0x57 0xf9 0x2e 0x61 0x15 0x82 0x55)) 7 (by decide) (UInt64.ofBytes 0x61 0x15 0x11 0x81 0x82 0x5b 0x1 0x82)) 8 (by decide) (UInt64.ofBytes 0x91 0x55 0x82 0x51 0x82 0x57 0xf8 0x2e)) 9 (by decide) (UInt64.ofBytes 0x1 0x1 0x60 0x90 0x91 0x1 0x20 0x60)) 10 (by decide) (UInt64.ofBytes 0x50 0x5b 0x5b 0x56 0xdd 0x2e 0x61 0x90)) 11 (by decide) (UInt64.ofBytes 0x61 0x90 0x91 0x6 0x2f 0x61 0x50 0x90)) 12 (by decide) (UInt64.ofBytes 0x5b 0x56 0x90 0x50 0x5b 0x56 0xa 0x2f)) 13 (by decide) (UInt64.ofBytes 0x82 0x80 0x5b 0x90 0x91 0x2c 0x2f 0x61)) 14 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x28 0x2f 0x61 0x15 0x11)) 15 (by decide) (UInt64.ofBytes 0x1 0x60 0x50 0x55 0x90 0x0 0x60 0x81)) 16 (by decide) (UInt64.ofBytes 0x90 0x50 0x5b 0x56 0x10 0x2f 0x61 0x1))

private def absorbed89 : Vector UInt64 25 :=
  #v[0x37b97ea9b4f864be, 0x49001f4f348f18dc, 0xb3d77e068256c85d, 0xfefd059ccd45531f, 0x976751f20cc2a2ea, 0xe89151cd590363c5, 0xd04fa121f975ddb8, 0xe5ead382958da341, 0xfbaa5bacdcdf3751, 0x711de378875a3807, 0xac6e20060c3e82d6, 0x9b5c770288b596c1, 0x5fd7ff451114a7dc, 0x3a5bf5e943f7c589, 0x7a1f8eb16dd74303, 0x9a0a9ed9fbe305a0, 0x87918638eb11da64, 0xded32d3edeab6e63, 0x636b16ba05ba8076, 0x285f3c1f3cdd5cd6, 0x6bca954535549adc, 0x144810faf8d9720a, 0x4d3e53d792bdd93c, 0xb8d204c4a3ceb96, 0xa25e2723e20fbbc8]

private theorem words89 : absorb89 state89 = absorbed89 := by
  decide +kernel

private def quarter89_1 : Vector UInt64 25 :=
  #v[0xf203a0ddd32a689f, 0xc218c16747cf97c0, 0x833bd4c4285d49e8, 0x9c26a6a9a8a1121d, 0x3d6613d97fe900dd, 0xe5a34244346408aa, 0x18b47775d79fe200, 0x444793020c92c3a7, 0xef97e2e5fa749844, 0x4853efe6d9065bbc, 0x3f4483516ca24319, 0x623e2ff32c3ff347, 0x41a33b322eea7a8e, 0xfef886ec3c0f9481, 0x7d7450929fdda9c4, 0x4326a83d9991b6d9, 0x4558567679bf908e, 0xe24c23d0d4a98de6, 0x36d5638e460671c7, 0x3c7e797b61bc9564, 0x84b4a209e3022a65, 0xaced19221b09e7a7, 0xa3106feb8aa3bc6d, 0x2e23b45c1476be1d, 0xe948b9f38974f48b]

private theorem rounds89_0 : sixRounds 0 (by decide) absorbed89 = quarter89_1 := by
  decide +kernel

private def quarter89_2 : Vector UInt64 25 :=
  #v[0xbc259a490acc9229, 0x3dfd75b74b7e5070, 0x3427e0f5eb08b762, 0x19a175b2375366a2, 0xe33b031748e243e7, 0x638a5fce7404bb2e, 0x58989487873d4888, 0x9643ad20f033873f, 0xeda244cd7aaebfea, 0x9066bab9f5fcb2bc, 0xa732b660d73ee77a, 0x7774bb402b938913, 0xc39bdc5b3c0b699e, 0xe99952b61da841c0, 0xa2532009c8d0090f, 0x8d76df720fa1cc19, 0xc7cc6d321bee0e3b, 0xbd18425bb522f952, 0xa519f7224be0d3d2, 0xf5875d48ec45b99f, 0x7200578edb34ff0d, 0x2dbf16c6981602ac, 0x8f9cadd40e5e0041, 0x9fb6cdc285da584b, 0x41ebca047a411ce8]

private theorem rounds89_1 : sixRounds 6 (by decide) quarter89_1 = quarter89_2 := by
  decide +kernel

private def quarter89_3 : Vector UInt64 25 :=
  #v[0xae33369682a2a14b, 0x1d51c6ab34364e9c, 0x97476c1d5946aa66, 0x792db2a11f752d6c, 0x491debafd875b89d, 0xf5d9c04729de2173, 0xe11913045118805b, 0xe3f9dd8a448e7ead, 0x507f7a23547d9cbc, 0xf6f73533321393d1, 0xbebb01942af438b7, 0x2612b08d7506215a, 0x5c033aeaf7cfc3f, 0x775236713a66a140, 0x9027bdd6edc2a05d, 0x7414e7c5ab604030, 0x120acfb9d24b104b, 0x69080dc84946c734, 0x3b6422d9290f86b2, 0xb0c0b10ba7c4aec1, 0xfbc89e220e6b92c7, 0xa5dc9e37aacc4e78, 0x44cae32a30b2de31, 0x88bbd695c201f1b9, 0x84e1a200a7345adf]

private theorem rounds89_2 : sixRounds 12 (by decide) quarter89_2 = quarter89_3 := by
  decide +kernel

private theorem rounds89_3 : sixRounds 18 (by decide) quarter89_3 = state90 := by
  decide +kernel

private theorem perm89 : KECCAK.f1600 absorbed89 = state90 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds89_0, rounds89_1, rounds89_2, rounds89_3]
  rfl

theorem block89 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes89 ++ tail) state89 =
      KECCAK.Bytes.run 0 tail state90 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes89 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb89 ws)) := by
    rfl
  exact (step state89).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words89).trans perm89))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
