import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb30 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x56 0x50 0x50 0x91 0x92 0x50 0x50 0x50)) 1 (by decide) (UInt64.ofBytes 0x50 0x90 0x54 0xb 0x60 0x0 0x60 0x5b)) 2 (by decide) (UInt64.ofBytes 0x90 0x0 0x60 0x2 0x60 0x5b 0x56 0x90)) 3 (by decide) (UInt64.ofBytes 0x4 0x90 0xa 0x0 0x1 0x61 0x90 0x54)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0x73 0x16 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x33 0x16 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xf 0x61 0x15 0x15 0x14 0x16 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x60 0x5b 0xfd 0x80 0x0 0x60 0x57 0xb9)) 14 (by decide) (UInt64.ofBytes 0xff 0x73 0x83 0x0 0x60 0x3 0x60 0x0)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed30 : Vector UInt64 25 :=
  #v[0x1b6b77fbce6f56dc, 0x43fa6612988f5b15, 0xc43e943ed0f8d309, 0x6b535a27fdaf0a69, 0x1408d2f0c08242aa, 0x51c0333ec07621b, 0x2fb42d582f124fc9, 0x2371a895df38c2bc, 0xa19d5a9d92a652f7, 0x5fa59df574142f4b, 0xbfba050f8c0b9b10, 0xf5cab15870b59e21, 0xe80e3dd48d18a8e7, 0x5fee75cc0d053e05, 0x81ff280636c96649, 0x415acbcce8814100, 0x117c0a728fc60f54, 0x9cc932562bf2e9b8, 0x8f62c1d7ef8731dc, 0xab0d4936e9377d18, 0xfaabe3f30349a04b, 0x84d6288b3e4f136, 0xed1f20a9e77e4073, 0x3af175b3a5ba4e4e, 0xd445146f1ddafccd]

private theorem words30 : absorb30 state30 = absorbed30 := by
  decide +kernel

private def quarter30_1 : Vector UInt64 25 :=
  #v[0x87d32f732e5819cf, 0x435c6fe678344d09, 0x1dcca3686882f060, 0xb7942e5aef24235, 0x9ef0b3f12322215c, 0x838de1797f6319c9, 0x8e9e5e1fc18ea2c1, 0x11f3cf754bb2472d, 0x69874b95a53b86fc, 0xb31f28fd63290674, 0x17928112e2413c72, 0x3f2c138e132a2738, 0x3c7d7b29b7637a1c, 0xe240534e23d7ca91, 0x9ee547b3fb492201, 0x427e6f809e2228f2, 0x419d02cfff3d73c, 0x884c70d20ae17b3c, 0xcb055c59f56017e1, 0xa2ea64c17afb7835, 0xfcfcc2ba17ee7e7f, 0x6a199f79e7b3e517, 0x66370a5b355d0bb9, 0xd8043ff53138a6d7, 0x6ddf87749d230a73]

private theorem rounds30_0 : sixRounds 0 (by decide) absorbed30 = quarter30_1 := by
  decide +kernel

private def quarter30_2 : Vector UInt64 25 :=
  #v[0x47d3e6292a60c37c, 0xc88f1a526a5bc54b, 0x5e10a8e5816e8b1d, 0x88c223fd926885ee, 0xdfc5c5e5f6474854, 0x168f01dd4d1ab72b, 0x727f7c32df594e5b, 0xa1163aa6d966582d, 0x54d34730cbcdfe6c, 0xb5cbe10d83ccba9c, 0xeae9a18ec9b4eaf5, 0x464539735b710f6a, 0x5ad4cd0f61844056, 0x79276fd626d301ef, 0xb35f755a1b21f1a3, 0xbb88dcd30d133b9b, 0x7e8e83bf87cb5c88, 0xcfdd3ec784474057, 0xd0f09c5ea06d4513, 0x8177a183c57e34c0, 0x13140c64f2b37fe5, 0x362550b035e29e65, 0x15c006eaaf4995d1, 0x343896e9a78b4946, 0x5d6fc0c64de7d52]

private theorem rounds30_1 : sixRounds 6 (by decide) quarter30_1 = quarter30_2 := by
  decide +kernel

private def quarter30_3 : Vector UInt64 25 :=
  #v[0x17c608a942f55490, 0x3aeb45b378330731, 0x3d7d99f0201d2250, 0xe64581e77fed8afb, 0x45a49b9178a7ed1, 0x3751201c71abd641, 0x55a103749eaea17c, 0xb07f73961cf56d70, 0xeaae9ff2c9f3fe65, 0x1b75d55a9d1ac9bc, 0x439297da7cd7e46f, 0xb9a7c39f7c612a12, 0xcd358593b3dbe75f, 0xb7886617d2f0bbaf, 0x8c92e12e0260573a, 0x25051744a8fe249a, 0x13ead9fb5b2d634c, 0xdcb8bb2e954a95ab, 0xfdb13ffd941cf3f5, 0xa6793a6b09e75240, 0x6e55e3149af0b8c0, 0x1188744ec1fbe8e9, 0xd19e04f3217555e7, 0x55789a4f1d78c956, 0x5febf3d9b52f3610]

private theorem rounds30_2 : sixRounds 12 (by decide) quarter30_2 = quarter30_3 := by
  decide +kernel

private theorem rounds30_3 : sixRounds 18 (by decide) quarter30_3 = state31 := by
  decide +kernel

private theorem perm30 : KECCAK.f1600 absorbed30 = state31 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds30_0, rounds30_1, rounds30_2, rounds30_3]
  rfl

theorem block30 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes30 ++ tail) state30 =
      KECCAK.Bytes.run 0 tail state31 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes30 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb30 ws)) := by
    rfl
  exact (step state30).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words30).trans perm30))

private def absorb31 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x16 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x90 0x1 0x20 0x60 0x52 0x81 0x16 0xff)) 4 (by decide) (UInt64.ofBytes 0x20 0x0 0x60 0x1 0x20 0x60 0x52 0x81)) 5 (by decide) (UInt64.ofBytes 0x54 0x81 0xa 0x0 0x1 0x61 0x0 0x60)) 6 (by decide) (UInt64.ofBytes 0x83 0x90 0x16 0x19 0x2 0xff 0x60 0x81)) 7 (by decide) (UInt64.ofBytes 0x80 0x50 0x55 0x90 0x17 0x2 0x15 0x15)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x11 0x7f 0x16 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xba 0xd9 0xa7 0x9a 0xbb 0x10 0x32 0x7e)) 12 (by decide) (UInt64.ofBytes 0xc6 0x55 0x2 0x82 0x26 0x20 0x17 0xff)) 13 (by decide) (UInt64.ofBytes 0x2f 0x1c 0x9d 0x99 0xa8 0xb 0xc3 0xf6)) 14 (by decide) (UInt64.ofBytes 0x60 0x4e 0x7c 0x13 0x48 0x28 0x8e 0xd8)) 15 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x51 0x40)) 16 (by decide) (UInt64.ofBytes 0x60 0x0 0x60 0x5b 0x56 0x50 0xa2 0x90))

private def absorbed31 : Vector UInt64 25 :=
  #v[0xe8dd1596c42d9ebc, 0x2648fa9ee2eebaf6, 0xb52576170857615e, 0x4b8524a41159f912, 0xf23e4a1d3682839c, 0x8b1b29ac19624238, 0xf7e05745a1c97411, 0x1fa1cd3825285172, 0x13799450ca1a0f07, 0xb2a67963f48d3076, 0x585de962422952e2, 0x331df1e8d3bb7500, 0xf4018ad6c09b3bc8, 0x8723c8c71a85e35d, 0xd6c417b4f20e84d4, 0xbdd2f113ae24c2c3, 0x3f6e2788d4a28a59, 0xbbd9fc9692b2d26b, 0xe5d5ab22cdef534b, 0x142f46909d56082f, 0x3af9de602cdf7be4, 0x1f27d9aa11dc61f2, 0x628f5434aa8d9c07, 0x4d3182cfe2a89fb3, 0x21c4e4f308892680]

private theorem words31 : absorb31 state31 = absorbed31 := by
  decide +kernel

private def quarter31_1 : Vector UInt64 25 :=
  #v[0x91c03c2bf1001d7d, 0x5827d4dcafa6f7f7, 0xd7cd6eaa48d91ed9, 0xc275caade2197d32, 0x96d0b8ca1f24bcd1, 0x9fa98e0582accd3d, 0x8200b552ea1c78b4, 0x14682cbcb3dbe854, 0x28800e305c535eed, 0x9d665e564d75650c, 0x4e2efed1ea8b3197, 0xe12eef57b9633410, 0x1a920769aacfedd, 0xc0f419102332478a, 0x3ff31a966595bd3f, 0x7e12d2235713c08e, 0x3ca2616435240b4, 0x6e5b461bc8e36541, 0xd19c24ec4ed65c3e, 0xc983cb68a2955366, 0xb99916c402f37b88, 0x3692413d786b5ff0, 0xd1c5d7b5b981eb39, 0x19e1a614d5d95545, 0x637779b99048cd6d]

private theorem rounds31_0 : sixRounds 0 (by decide) absorbed31 = quarter31_1 := by
  decide +kernel

private def quarter31_2 : Vector UInt64 25 :=
  #v[0xfe5776e9a5d1487e, 0xac9d4a0510d62b6, 0x664efdeb770cb959, 0xcbc21c0714170ad4, 0x9f0728c350100272, 0xcb882d78731e7aa7, 0x7ab2c2eca9879a71, 0x41daedc9b0d5f085, 0xc3cbdb933ecebca2, 0x5921965b9ad2ab04, 0x6194fdf7d6067e0a, 0x80bb2edf2cda08d3, 0x4222b44857b0d607, 0x62493c6f75c50dba, 0x78c824678cd0bc37, 0x9aac23ecc0b2ed41, 0x9d109582c76c1382, 0x716efc09bad5b5e, 0xa807beae2ca7cb89, 0xeb1f34a3b74af06b, 0x966881bcc5488a8, 0xc04c3fc9499140da, 0x26cb03150742d50a, 0x91d9ddf1ef20c037, 0x5d0d0bb6b39cedb5]

private theorem rounds31_1 : sixRounds 6 (by decide) quarter31_1 = quarter31_2 := by
  decide +kernel

private def quarter31_3 : Vector UInt64 25 :=
  #v[0x6ac4dc1a53564642, 0xecd2ef9c89b6e22a, 0x27209a4203185a96, 0x505ecf94a8a34b84, 0x213a69c9d792741, 0x2e35e6f8b8ac7449, 0x78307e2ee1e862c8, 0x861986e679d45275, 0xfce231ad81023073, 0x6bfe47fd43f59eea, 0x48e94c35a6535f9a, 0xcbe5aa7297571df0, 0x35481a37158ea8b9, 0xbb75796cd1a5732d, 0x716fe0fd855db4a4, 0xbe1ecbfaa657a215, 0x611ba8e7ab8f8f27, 0x6b50f5e9b966c9f2, 0xf07ba5fd457e8590, 0xf7c0bdc2ff4661e6, 0x15de1ca18728354f, 0x39884e49132cccca, 0x51b92c8da01abb79, 0xc951caebe573fc91, 0x5d6183effccdabf0]

private theorem rounds31_2 : sixRounds 12 (by decide) quarter31_2 = quarter31_3 := by
  decide +kernel

private theorem rounds31_3 : sixRounds 18 (by decide) quarter31_3 = state32 := by
  decide +kernel

private theorem perm31 : KECCAK.f1600 absorbed31 = state32 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds31_0, rounds31_1, rounds31_2, rounds31_3]
  rfl

theorem block31 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes31 ++ tail) state31 =
      KECCAK.Bytes.run 0 tail state32 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes31 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb31 ws)) := by
    rfl
  exact (step state31).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words31).trans perm31))

private def absorb32 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x1 0x61 0x90 0x54 0x90 0x14 0x60 0x1)) 1 (by decide) (UInt64.ofBytes 0x15 0x16 0xff 0x60 0x4 0x90 0xa 0x0)) 2 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x75 0x10 0x61 0x15 0x15)) 3 (by decide) (UInt64.ofBytes 0x15 0x15 0x0 0x60 0x82 0x5b 0xfd 0x80)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x83 0x0 0x60 0x3 0x60)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x16 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x81 0x90 0x1 0x20 0x60 0x52 0x81 0x16)) 11 (by decide) (UInt64.ofBytes 0x60 0x20 0x0 0x60 0x1 0x20 0x60 0x52)) 12 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x90 0x54 0x90 0x0)) 13 (by decide) (UInt64.ofBytes 0x14 0x15 0x15 0x16 0xff 0x60 0x4 0x90)) 14 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0xd5 0x10 0x61 0x15 0x15)) 15 (by decide) (UInt64.ofBytes 0x15 0x15 0x0 0x60 0x33 0x5b 0xfd 0x80)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x83 0x0 0x60 0x3 0x60))

private def absorbed32 : Vector UInt64 25 :=
  #v[0x4fa30cc61526ee48, 0xd72d7f4a2cbccd5e, 0x90d49c116280b780, 0x1d3abba22f96f1a3, 0x6afc6d716696279, 0xe8a27cee818c6206, 0x75ef59f87e219309, 0xbc1bd06a53c71a45, 0xf5512fc80fb64e7, 0x3570b083aac98344, 0xea568b184c0f9ee, 0xd6e7333af8a66945, 0x8159204f69f55418, 0xa9a0dc1ae4791b9e, 0x80521b58b8b5e9ed, 0x6315fc808a604306, 0x949fb04554dae945, 0x6003b1c492f6be2b, 0xe511d58fdb2a7f51, 0x8c1697de79e6f6d0, 0x93fbff1443816ae6, 0x238424fb067ee46d, 0x5712bb4806c0fc00, 0xa71ab673dfaf2a48, 0x8e41fb526336cc3d]

private theorem words32 : absorb32 state32 = absorbed32 := by
  decide +kernel

private def quarter32_1 : Vector UInt64 25 :=
  #v[0x5219f6371b799dbb, 0x17a16150bd76bbb0, 0x17a04f57f781af60, 0xca96235b9c42c01e, 0x1f3bf542f16091b6, 0x3d516df13f3214a7, 0xe46712d70ede680a, 0x5871fe447b50978e, 0x74ef7ffb252b126f, 0x60353ef8a4f532b, 0x3183978d3d7d9520, 0xfaf1d9584dc50d6a, 0x8e19933cc2b7321d, 0x924193a9fa034542, 0x74db16846c11472, 0xd4c035de81ab1297, 0x8767198b6b5b9b3a, 0xafbb2b48b29fbca4, 0xbf77d05905895ed, 0x5b3229af8759d0f7, 0xb3e922c70822cf20, 0xf7ac891721dc6c8d, 0xcfd6ea6dbafa82dd, 0x998928e84bf268df, 0x3540b456c6ddfcb0]

private theorem rounds32_0 : sixRounds 0 (by decide) absorbed32 = quarter32_1 := by
  decide +kernel

private def quarter32_2 : Vector UInt64 25 :=
  #v[0xfdf4f07a848d7326, 0x2c870cbe4d591dc6, 0x5556fa9afd17b019, 0x87dbac453f5c24ea, 0xbfbb55f1404e5c83, 0xedc24572c81d1a20, 0x4ff2adcf409827a9, 0x539843ced06ac479, 0xc62fe4caed126092, 0xb0b3acb871e2c3aa, 0xd3ff46a40778c7f1, 0x7fb99df9c2d11138, 0xe5fd614763fc32a7, 0xc2119318d556dce5, 0xf14d7f3afaaff153, 0x82b086b739c254e5, 0x40215214b78fb275, 0x16bec5d262292de6, 0xd01bb0521291f366, 0x39d37ee5c8a7bc5c, 0x262b4b63924cfddb, 0x1ca7703e07cfee4b, 0xde2b86ed80bcd39e, 0xf87ba2246a63a5d7, 0x6214b13d8d17f592]

private theorem rounds32_1 : sixRounds 6 (by decide) quarter32_1 = quarter32_2 := by
  decide +kernel

private def quarter32_3 : Vector UInt64 25 :=
  #v[0x3246980a0d6a63eb, 0x89cf2702af9e8e31, 0x2ba793521581a14d, 0x774a1279c3388e0, 0x1c7ce4ec8f87f9c8, 0x83dfb5d367e69fac, 0x37f7fb9d60dff76e, 0x4920cc963dd22ab8, 0xecb9b996af10b9b5, 0x364e6c7a47bc4089, 0xe75409b4824e784f, 0x661da9f10bd5188f, 0xe8bf27c5da71eb78, 0x310a25648877ffbf, 0x9c8c5772b0a0b617, 0xb49c1fc4129aa20, 0x2d098eef45e55c4e, 0x2832651a551cf956, 0x396c579271540c92, 0x8dee5d8080cce20f, 0xeaaa856126667251, 0x33139df1f2824c45, 0x1ab2677c74a2eec7, 0x7920827b155bca33, 0x11e836d354d88bf]

private theorem rounds32_2 : sixRounds 12 (by decide) quarter32_2 = quarter32_3 := by
  decide +kernel

private theorem rounds32_3 : sixRounds 18 (by decide) quarter32_3 = state33 := by
  decide +kernel

private theorem perm32 : KECCAK.f1600 absorbed32 = state33 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds32_0, rounds32_1, rounds32_2, rounds32_3]
  rfl

theorem block32 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes32 ++ tail) state32 =
      KECCAK.Bytes.run 0 tail state33 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes32 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb32 ws)) := by
    rfl
  exact (step state32).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words32).trans perm32))

private def absorb33 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x16 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x81 0x90 0x1 0x20 0x60 0x52 0x81 0x16)) 6 (by decide) (UInt64.ofBytes 0x60 0x20 0x0 0x60 0x1 0x20 0x60 0x52)) 7 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x90 0x54 0x90 0x0)) 8 (by decide) (UInt64.ofBytes 0x14 0x15 0x15 0x16 0xff 0x60 0x4 0x90)) 9 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x35 0x11 0x61 0x15 0x15)) 10 (by decide) (UInt64.ofBytes 0x15 0x15 0x0 0x60 0x85 0x5b 0xfd 0x80)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x83 0x0 0x60 0x3 0x60)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x16 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed33 : Vector UInt64 25 :=
  #v[0x179daafeebc12e79, 0x2353a7d19ff8680, 0x82860283a01fce97, 0x86799511e880873e, 0xc5a0ff7d55f4e0c0, 0x6a1fac0d533b46d, 0x22b15df1c22712cc, 0x26a18963f9d42139, 0x2af7b1bd761f175a, 0x1ad5c263e3227e98, 0x936cb2fc269f1fd7, 0x7a91e212c6ca33c5, 0xa10c85bfd2ba37db, 0xc552c82b763d4450, 0xa7fc25395b97e7a1, 0xd2464fb573d1db57, 0xee0da3df4f44b4e7, 0x7f65dce7b073f5d1, 0xb4c8a7904f130b33, 0x9cd0aa1c148b8be6, 0x4aec0fc5da5f416a, 0xcda133f690958a3, 0x341ad79c7bce4a08, 0x5a58d7325fc11fa0, 0xf28d5e9971e662b4]

private theorem words33 : absorb33 state33 = absorbed33 := by
  decide +kernel

private def quarter33_1 : Vector UInt64 25 :=
  #v[0xef034a38480fea12, 0x19c7d5f4ba575dfc, 0x93548c7bbd1ade16, 0xc122226191998ea9, 0xfeb13518313ccefc, 0x6e07933394e55235, 0x3f1702a41c2cbadd, 0x792e8568cab1c7b, 0xaecaa5b7c7a7d485, 0x30bb8a025473f2d3, 0x147d5182deb3b128, 0xa55b16b7ef7b95e7, 0xbeb261e18c0711e6, 0xcaed6eb75cf0307a, 0x6ffb3fd92cca404c, 0xf26c0d5a11ed5d77, 0x4473cdfdcc9366d7, 0x3726f63b97732d59, 0x1ab19e78458703e0, 0x7f810c88dbb5ac48, 0x2e2f6b29ae0a3407, 0x9690573f8a99a1ef, 0x5bfbe82ca8151d4e, 0x6c89114b922a571d, 0xf7bb5c47ff0f3a1e]

private theorem rounds33_0 : sixRounds 0 (by decide) absorbed33 = quarter33_1 := by
  decide +kernel

private def quarter33_2 : Vector UInt64 25 :=
  #v[0x556bb205e2170b4d, 0xd609519b299c2767, 0xdd2d81d9a5f51fe8, 0xdf061cb32e605613, 0xccd0463e8cc03381, 0x490c5bb6abe2fcf7, 0xd69d2bc2111eda5c, 0xb62ebcc8fbaf8245, 0x7e5c5957846c4ea1, 0x286fcdefcdf557b2, 0x5083616cdbd79a63, 0xf2d542ab4542d4cf, 0x2a6c6c235b8c8055, 0x4b5170fa2a14548f, 0xe6e478d4edbc977c, 0x30435ad6877a05dc, 0x680ae816087eddbe, 0xbb3051f5a5e69635, 0xc57c9f01d5677243, 0xd1d923160124395c, 0xea67e8694468f534, 0x807d3a19b5ab6a66, 0x40a028c8a19f2d9c, 0x81630becdfa42220, 0xb2f5d7796b721246]

private theorem rounds33_1 : sixRounds 6 (by decide) quarter33_1 = quarter33_2 := by
  decide +kernel

private def quarter33_3 : Vector UInt64 25 :=
  #v[0x14e132a49196c56a, 0xe681fc687fcb63d9, 0x6365fa23ab7c4753, 0xafe2229678c96bc3, 0x813b81c333444bb4, 0xbb36a55e69672a67, 0x80407473a7b2b2c1, 0x8cb9c71320695662, 0x3a3365a0ff3feac1, 0xae1b6dab53ad993a, 0xe173aa13027ced86, 0xda372169b24d717a, 0x92db08d524b70920, 0xcd63b78a8b0db4ba, 0x3335901779f55f5c, 0xfe012c700dab0145, 0x3523ecad693c80d2, 0xdd541103e735570a, 0xd164ab102b2b40f1, 0x982eb38f48d8f1e, 0xe2477135e101b508, 0xeb99a45df993f484, 0xa3645a68d2c27888, 0x16deecc0ea83f60c, 0x8aaae6129c665836]

private theorem rounds33_2 : sixRounds 12 (by decide) quarter33_2 = quarter33_3 := by
  decide +kernel

private theorem rounds33_3 : sixRounds 18 (by decide) quarter33_3 = state34 := by
  decide +kernel

private theorem perm33 : KECCAK.f1600 absorbed33 = state34 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds33_0, rounds33_1, rounds33_2, rounds33_3]
  rfl

theorem block33 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes33 ++ tail) state33 =
      KECCAK.Bytes.run 0 tail state34 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes33 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb33 ws)) := by
    rfl
  exact (step state33).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words33).trans perm33))

private def absorb34 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x81 0x90 0x1 0x20 0x60 0x52 0x81 0x16)) 1 (by decide) (UInt64.ofBytes 0x60 0x20 0x0 0x60 0x1 0x20 0x60 0x52)) 2 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x90 0x54 0x90 0x0)) 3 (by decide) (UInt64.ofBytes 0x14 0x15 0x15 0x16 0xff 0x60 0x4 0x90)) 4 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x95 0x11 0x61 0x15 0x15)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x0 0x60 0x5b 0xfd 0x80)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x86 0x16 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x11 0x61 0x15 0x15 0x15 0x14 0x16 0xff)) 12 (by decide) (UInt64.ofBytes 0x60 0x5b 0xfd 0x80 0x0 0x60 0x57 0xd1)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x88 0x0 0x60 0x9)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x16 0xff))

private def absorbed34 : Vector UInt64 25 :=
  #v[0x50f379d7b5070cd4, 0x1d798f67f0ec683c, 0xdef7427e8142a5b3, 0x487f65a0e55c38b4, 0x2dde693183d08448, 0x51be47aaba048fd1, 0xe679bdb297c79248, 0x9519a8f4968fa866, 0xead1584e77e89353, 0xa96dfdf9b0159593, 0xe48ff0f883efd2eb, 0x7e56ee5d97799105, 0xca6703b7920394cc, 0xdcb8b5f5bc8020e8, 0xb4b7e55aaea4f40d, 0x20678ef6ce492ee2, 0x721d5cb4e752d549, 0xfa11a191a7932cdb, 0x5569fdcc72cbd005, 0xe5ad0c1191708ead, 0x49a7be06935bce2e, 0xaa38f49945cb0d52, 0xd88d6d41118a151, 0x344247b0b7351abd, 0x25777122045b91b7]

private theorem words34 : absorb34 state34 = absorbed34 := by
  decide +kernel

private def quarter34_1 : Vector UInt64 25 :=
  #v[0x2e69818547965b86, 0xf481b8de7e3ebcdf, 0x647ae01d7a915778, 0x34a6e647215ca4e1, 0xa232dae5f3ab4d09, 0x90b034bd60be19cd, 0xcd85a6599591b513, 0x28f45b258f9e20d2, 0x837e59026a7a70c7, 0x22733b63e3bc38ac, 0x2b9fca380f21efd1, 0xc8588d7edce510ef, 0x70001b92972b87f5, 0x828e621a446eac4c, 0xa8ecf49533734078, 0x7ee98d37b0cebaf3, 0x1e55229d812b93ff, 0xc4f478a8d65cb79a, 0x675d19510897291a, 0xa99be87eea353195, 0x5cffe45f721334ca, 0x9338a0e7addf2b89, 0xde2530776633c85d, 0xdff5d597b3c79b31, 0x1929a6120737e676]

private theorem rounds34_0 : sixRounds 0 (by decide) absorbed34 = quarter34_1 := by
  decide +kernel

private def quarter34_2 : Vector UInt64 25 :=
  #v[0x2fdc13be5ff6103, 0x4f7adef55eb0dd5b, 0x6758a8115c615cb8, 0xe66bed34bcb42165, 0x56809c77452b2c11, 0xc7d71313c42b0733, 0xb519b0e2e1da653f, 0xbc621960e24da8eb, 0xf1a656f62b1795ea, 0xb9d469dc122fdee7, 0xed72f81e88e3cb14, 0x2f7ed98007df8cb0, 0x8a60c629518d82b, 0xa9179797f0fcf4b7, 0xc2349c5509f9aafd, 0x3aababf89f064a6, 0x284793977256686, 0xb06b1fdf19aabdd2, 0x937632700302bb5, 0xf684622e7ff38007, 0x662afbaeb278b2e8, 0x289bc765f28f1c2f, 0x4b3f8e31a755085e, 0xa446e327943d4ba, 0xb7130d2e73dbb8ad]

private theorem rounds34_1 : sixRounds 6 (by decide) quarter34_1 = quarter34_2 := by
  decide +kernel

private def quarter34_3 : Vector UInt64 25 :=
  #v[0xed95ed3e0777a700, 0x139d83ff4f98957d, 0x383456ff2ad8827b, 0x1e15a67d12cd2886, 0xd5a4d9b2fe348a0b, 0x6d45c35f02aa6760, 0x9f02a2499175cd8, 0xe219823f960dde93, 0x1891155970440f9, 0xbfcce721aba70dcd, 0x64c2805b039097c9, 0x4cf26fadfb3b967a, 0x7dbba7d91cd5272c, 0x955264c75f928dd1, 0xc0efa99836ac6dbe, 0x164927c7afe7a040, 0x45271244e78e2974, 0x65c5170147e9f743, 0x88536d99f8e26344, 0x44ad3f994977bef8, 0xccbebccefc71bb0b, 0x2043693f9dc2b4a6, 0x608453b701ed2280, 0xb12f61fdd576fba7, 0x3c48098e862b1d96]

private theorem rounds34_2 : sixRounds 12 (by decide) quarter34_2 = quarter34_3 := by
  decide +kernel

private theorem rounds34_3 : sixRounds 18 (by decide) quarter34_3 = state35 := by
  decide +kernel

private theorem perm34 : KECCAK.f1600 absorbed34 = state35 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds34_0, rounds34_1, rounds34_2, rounds34_3]
  rfl

theorem block34 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes34 ++ tail) state34 =
      KECCAK.Bytes.run 0 tail state35 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes34 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb34 ws)) := by
    rfl
  exact (step state34).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words34).trans perm34))

private def absorb35 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x52 0x81 0x90 0x1 0x20 0x60 0x52 0x81)) 3 (by decide) (UInt64.ofBytes 0x85 0x54 0x20 0x0 0x60 0x1 0x20 0x60)) 4 (by decide) (UInt64.ofBytes 0x57 0x1f 0x12 0x61 0x15 0x15 0x15 0x11)) 5 (by decide) (UInt64.ofBytes 0x60 0xa 0x60 0x5b 0xfd 0x80 0x0 0x60)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x88 0x0)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0x52 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x20 0x60 0x52 0x81 0x90 0x1 0x20 0x60)) 13 (by decide) (UInt64.ofBytes 0x73 0x33 0x0 0x60 0x20 0x0 0x60 0x1)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0x73 0x16 0xff 0xff 0xff 0xff))

private def absorbed35 : Vector UInt64 25 :=
  #v[0x9c80a5e570c2169d, 0x178915ff8aa9cded, 0x65b6b1017125f303, 0xa1168e5443dc4abb, 0xe24be37cf1b09fdb, 0x5ac5b0a9f35a99c2, 0x3f11489649285902, 0x1339a72f7d0e1052, 0x5579ef49b2fd697, 0xb8e283ffe42c0e0b, 0xf3697d6c3b98c4c, 0x75321cdc85b23c53, 0xa14cf362a143a5aa, 0x23edf7296be26b4c, 0xf9d5059c95b7eb36, 0x78db8aafdb36527e, 0x28868030240d17d1, 0xb7998f7f14204c34, 0x1d5fd5cb048efd22, 0xcc73d095b613f35e, 0x8630fa1230a63d1c, 0xb2bb79eaea2decc5, 0x1434f90bdf5d880f, 0xb5a4f962082d4fe2, 0xe0e0e07d86438f8]

private theorem words35 : absorb35 state35 = absorbed35 := by
  decide +kernel

private def quarter35_1 : Vector UInt64 25 :=
  #v[0xd56549acba6c89cf, 0x35d419170a8fc57b, 0x6df4667c942b33bf, 0xc52bd8c18fb8af00, 0x189a34ed5af6678c, 0x843b323ed3ca0b56, 0xdc7ef08d39cc85ae, 0xf0281a14c1137317, 0xee4c0246e9c55db3, 0x16bf749d34cee8c1, 0xe0ac675d1b806e87, 0x18ec195658c51344, 0xea5b2b166af90da3, 0x42356f1013329fdc, 0x63adf50cd19ffb0, 0x7a5ec283df43f729, 0xa6a9bd9dc2634f02, 0xa8670bb209b03c1, 0xc095ed12c0617927, 0xb5e4d5d573f94417, 0xae9873dfe32f58b1, 0x2eb303e1f6e7b71c, 0x4b543fe354a15729, 0x654c540c7fcd5792, 0x67f1127242ac7ece]

private theorem rounds35_0 : sixRounds 0 (by decide) absorbed35 = quarter35_1 := by
  decide +kernel

private def quarter35_2 : Vector UInt64 25 :=
  #v[0x6fe626b84ad472f9, 0x873fa7077934480c, 0xfcf3102fb6c033ce, 0x874f8fe0f48915d6, 0xe24b7433310cd667, 0xa0bc40aa08fe09e3, 0x934d30a2bb11885a, 0xd25da1900034f1d7, 0xde660cce162e7e46, 0x608b6526b94483a6, 0x4cb1476c7c454680, 0x4e16084fb25c7856, 0xf62f96989a6aefb4, 0x16b89085e5790a62, 0xe7cf164a7b79a7, 0x2621e2bd66e3d673, 0xd4191bf181e24011, 0x8108f440c6ff21bd, 0x5952d07e16c681e7, 0xa87a56264d7b12c5, 0x6bdbcf930ad0947d, 0x83fb92db7953b789, 0xa9189b505db6d38a, 0x34fe896053ac8f43, 0xdb86ba3759b2a64d]

private theorem rounds35_1 : sixRounds 6 (by decide) quarter35_1 = quarter35_2 := by
  decide +kernel

private def quarter35_3 : Vector UInt64 25 :=
  #v[0xc253b1ff9d253413, 0xa0da525090e7f6bf, 0xc2a58df2ef77f91e, 0x667777b6860c7046, 0xcad3507aaa1ac505, 0x1970b274168e4847, 0xd6546c9f31e13174, 0x87f75019809ad956, 0xe0fb020420794925, 0x64ff3e98d4f6f799, 0xc3ccbfbc388f568a, 0x8248bf1095e3731b, 0x69897991bbfe6182, 0xf9dc701fcd597a74, 0xa4db34435999e753, 0x281db9cef80fab50, 0x6209f5a621929097, 0xdd849b880943b130, 0x7d742fc69254e974, 0x3af6fe8b437e7d0a, 0x4294c613e5a631c4, 0x58ac5538e0ad3cf8, 0xa4776279da88106e, 0x99e3bc720a5cc7e4, 0x97b52be7349f109f]

private theorem rounds35_2 : sixRounds 12 (by decide) quarter35_2 = quarter35_3 := by
  decide +kernel

private theorem rounds35_3 : sixRounds 18 (by decide) quarter35_3 = state36 := by
  decide +kernel

private theorem perm35 : KECCAK.f1600 absorbed35 = state36 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds35_0, rounds35_1, rounds35_2, rounds35_3]
  rfl

theorem block35 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes35 ++ tail) state35 =
      KECCAK.Bytes.run 0 tail state36 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes35 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb35 ws)) := by
    rfl
  exact (step state35).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words35).trans perm35))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
