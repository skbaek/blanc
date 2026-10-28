import Blanc.Lift.Usdc.ImplV1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb42 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xb4 0x15 0x61 0x15)) 1 (by decide) (UInt64.ofBytes 0x0 0x60 0xc 0x60 0x0 0x60 0x5b 0xfd)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x84)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x90 0x1 0x20)) 9 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x0 0x60 0x20 0x0 0x60)) 10 (by decide) (UInt64.ofBytes 0x19 0x2 0xff 0x60 0x81 0x54 0x81 0xa)) 11 (by decide) (UInt64.ofBytes 0x90 0x17 0x2 0x15 0x15 0x83 0x90 0x16)) 12 (by decide) (UInt64.ofBytes 0x0 0x60 0xd 0x60 0x0 0x60 0x50 0x55)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x84)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x73 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed42 : Vector UInt64 25 :=
  #v[0x265c564115b0e08a, 0x89655495133b7127, 0xd2c73e12874d64ee, 0x7bbd3508149f8368, 0x1e10947218f70654, 0x592e6bdba12bf6de, 0x664ae910bae8e56e, 0xb4c53df77d635901, 0x6eb9c26b879a2b88, 0x69246f7872f9cd5, 0x18d193bae3b9cc9, 0x95cd7696add0609b, 0xb15188675943ecd3, 0x5646211d3b01805f, 0x78cc97ef48162d66, 0x6644ba63d450df31, 0xfb5545749762edb2, 0x953c676074781a70, 0xc5e7328925fa0dca, 0xfd7c761d86b247f3, 0x65ac110262409893, 0xbdbc8827fe5fc0c2, 0x73a432360d73d023, 0xb6b843324fd177b0, 0x634a1d6c6c182f4c]

private theorem words42 : absorb42 state42 = absorbed42 := by
  decide +kernel

private def quarter42_1 : Vector UInt64 25 :=
  #v[0x4d3af30b456c6094, 0xaafd3417164bce2c, 0x6e6aa47fa0c4b50a, 0x456e1ae98afb178, 0x2b423fa491ac37b1, 0x8c6ef3db26ed1d67, 0xc337e5c6ab012973, 0xf7b993a686d5e88c, 0x84f19acea13c821e, 0x983183278264d993, 0x1ebfe835f52e4af7, 0x57c59046e46bd1e0, 0xda357f615c5f0fd0, 0x7f154fd87e630ac7, 0x9d53a444a179171d, 0x42b3cc887e1c8977, 0xf6994b16c6e70f07, 0xe9cb6dbb4846d068, 0xab2fc5a6f7f12419, 0x18b2cd048362b81f, 0xcb1a5e8fd6d49c46, 0xc6161ad571bc0476, 0xb55032e6d31fa93c, 0x5876dc92a49e6fb7, 0x3e0c3041dd7ea0d8]

private theorem rounds42_0 : sixRounds 0 (by decide) absorbed42 = quarter42_1 := by
  decide +kernel

private def quarter42_2 : Vector UInt64 25 :=
  #v[0x76fdca4895675c55, 0xcdf3f39a378b3ce2, 0x8e1dce31d075c578, 0x72f8306e9da2e40a, 0x56eaf13115616d39, 0xce0d28cdf9a6e82e, 0x12f2db1d120a02db, 0x9810303597c24eda, 0xa96c995b6664cd3f, 0x9600e441f553f981, 0xf26d976b167c7075, 0x91e45dff942d90fb, 0xdf822fb9f4a6b1b3, 0x4c8067d916034efa, 0xffa27eb21533ac97, 0x5c62bc8c31a545bd, 0xcc3b418a84918272, 0x6c671c0c593e9ec, 0x920e826d5df3d925, 0xd7e6c3c2a5498e2e, 0xd4e3297b364b5a18, 0x4e75634253fc7e59, 0x1da2a2df34fcd41e, 0xfc11fe3f0094cbd6, 0x610676ea82e6b42e]

private theorem rounds42_1 : sixRounds 6 (by decide) quarter42_1 = quarter42_2 := by
  decide +kernel

private def quarter42_3 : Vector UInt64 25 :=
  #v[0xb07289087c65e5e8, 0x7bf4950d720611c0, 0x441947cb57c7e757, 0x4f0bde1f99c391c7, 0xd74b61e1fd420606, 0x3cfd72dadc5a9cd0, 0xf9ed11e7571dfe44, 0x66bc4dadc30887ab, 0xcc04507b9ea0f1b6, 0x762556e3a6e9714f, 0x227031b98327ba09, 0x55cdaa9c1ec784b0, 0xf75346ba033e5991, 0xe063346aa1f0fbda, 0x61d0962132b5f5da, 0xb2522ea949fe8960, 0x1fa34e85e5461606, 0x91acaaff5ef7de56, 0xa5c6e34622a10655, 0x757cc56a9a8abc22, 0xfe7d1ed834fee22a, 0x63bb0e7610c720b5, 0xbebc3af447d67c45, 0xde1d9b09cd5b2300, 0xdac059c731e1842f]

private theorem rounds42_2 : sixRounds 12 (by decide) quarter42_2 = quarter42_3 := by
  decide +kernel

private theorem rounds42_3 : sixRounds 18 (by decide) quarter42_3 = state43 := by
  decide +kernel

private theorem perm42 : KECCAK.f1600 absorbed42 = state43 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds42_0, rounds42_1, rounds42_2, rounds42_3]
  rfl

theorem block42 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes42 ++ tail) state42 =
      KECCAK.Bytes.run 0 tail state43 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes42 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb42 ws)) := by
    rfl
  exact (step state42).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words42).trans perm42))

private def absorb43 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x60 0x52 0x81 0x16 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x52 0x81 0x90 0x1 0x20)) 3 (by decide) (UInt64.ofBytes 0x81 0x50 0x55 0x90 0x81 0x20 0x0 0x60)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xe9 0x7f 0x16 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xc7 0x2c 0x95 0xe1 0xf7 0xa9 0x79 0x44)) 8 (by decide) (UInt64.ofBytes 0xc1 0xad 0x78 0xb6 0xaa 0x6b 0x2d 0x8f)) 9 (by decide) (UInt64.ofBytes 0xef 0x3d 0x58 0xc6 0x36 0xd9 0x72 0xb7)) 10 (by decide) (UInt64.ofBytes 0x60 0x92 0x66 0xb6 0x4c 0x52 0x9e 0x48)) 11 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x51 0x40)) 12 (by decide) (UInt64.ofBytes 0x90 0x91 0x50 0x90 0x1 0x60 0xa2 0x90)) 13 (by decide) (UInt64.ofBytes 0x90 0x0 0x60 0x6 0x60 0x5b 0x56 0x50)) 14 (by decide) (UInt64.ofBytes 0x4 0x90 0xa 0x0 0x1 0x61 0x90 0x54)) 15 (by decide) (UInt64.ofBytes 0x8 0x60 0x5b 0x56 0x81 0x16 0xff 0x60)) 16 (by decide) (UInt64.ofBytes 0x0 0x1 0x61 0x90 0x54 0x90 0x14 0x60))

private def absorbed43 : Vector UInt64 25 :=
  #v[0x6cd182e3602dcc80, 0xced9683da484393f, 0x1579e71b8c3971be, 0x9970ed575b67f0f8, 0xa209c54336af9dec, 0x1509af56168993b, 0xbd53d94f5b20c7de, 0x3807af7d8d58c07f, 0x1c4fc8c94e368ef0, 0x74a198591401a546, 0x88273708377a744c, 0x1b71b62d34873772, 0x21993fff87e16f9d, 0x99c37074f4c804c, 0x454fde1f4f219c85, 0x50f209cc22d4085d, 0x3b04440684bbad15, 0xdcda5c4e5e65034, 0xd5dd15bd003e6440, 0xc1a63a9cb469c226, 0x9cb766a0ba329b93, 0x9c08ab2dad606781, 0x594ac70c340ab333, 0xd2417d3719bc56, 0x4e824641ea055a6f]

private theorem words43 : absorb43 state43 = absorbed43 := by
  decide +kernel

private def quarter43_1 : Vector UInt64 25 :=
  #v[0x17439361e33d7a1, 0x17b0338642b35319, 0xcc0661edf773dd1f, 0xacae7a124a4e580d, 0xfbd1f2080039dbd5, 0x95fa1ecd51cc2991, 0x8716211373dc86e5, 0xb6f40162a9113278, 0x99b93740e0329746, 0x212189f4f8c6806e, 0xa5686f73dd11079f, 0x93ba3cb935aacae, 0xd19cb75e4996d2d, 0xdc7cd5e8d66cfe85, 0xe03ffcbd1e8b33b9, 0x115f2bd685f1930f, 0xd5aab462e0ba7196, 0xfa340e7078ca62d9, 0x65f12fab93b0e8ab, 0xf564328fe9ac082a, 0xa283919eebbb2862, 0x2afc50c195154556, 0xba365befad06a684, 0xacef743152afb83f, 0xad8e39cbed78b3e3]

private theorem rounds43_0 : sixRounds 0 (by decide) absorbed43 = quarter43_1 := by
  decide +kernel

private def quarter43_2 : Vector UInt64 25 :=
  #v[0xdeac89dec25bebc4, 0x216f00eed4ac3227, 0xeb8cb3753b9394b4, 0x224af525cd665648, 0xa51155a861b26b44, 0x5d9e5b6a43e4ef9c, 0x45534e096cf6396b, 0x417bf7448c033aa, 0x9e4f170c0a8f22dd, 0x48e9c5355ff88a3c, 0xa49b95b4eda9fc1f, 0xbe4959476644dd1, 0xed16638226359564, 0x4cae6b65d22f817f, 0x6d75792210b022eb, 0x7225786073a5e044, 0x30e9b28c5b84afc2, 0x8b86c8bbcb74a0e5, 0x6b8b08a4766e73b5, 0x8ecbf557a98162d4, 0x8ae4f6f0f2f2b606, 0xd3bb326ea786f66, 0x23fcf943e83f3abf, 0xfeb3b4c452c5a7ba, 0x131062729605d83]

private theorem rounds43_1 : sixRounds 6 (by decide) quarter43_1 = quarter43_2 := by
  decide +kernel

private def quarter43_3 : Vector UInt64 25 :=
  #v[0x907bb0427ede143a, 0x23f89fcd4cfe17ee, 0xf6eb4e466176814f, 0x2e7883313ca0e42c, 0x3adb3c8013eac8ea, 0x91a38d8e123603fd, 0x4886c58c21187d99, 0x780daeebb3f117de, 0xc97f82b98aa26783, 0xb184d0055b121730, 0x63058097241d989, 0x21099260a3a6d121, 0x701c0adefeaedc56, 0xa8611f79917ec0b6, 0x90e91e1412391028, 0xd6a07dc113a91438, 0xc1348dc52f7129c5, 0x6176c715bf0aacbe, 0x536c5a5915ba28c0, 0x9d86825979a60648, 0x89612cd1edb50377, 0xe90b19766955efd4, 0x2a6df34a5c82a87f, 0xb141cf2d4b7c4298, 0x2dca1c237c139c5b]

private theorem rounds43_2 : sixRounds 12 (by decide) quarter43_2 = quarter43_3 := by
  decide +kernel

private theorem rounds43_3 : sixRounds 18 (by decide) quarter43_3 = state44 := by
  decide +kernel

private theorem perm43 : KECCAK.f1600 absorbed43 = state44 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds43_0, rounds43_1, rounds43_2, rounds43_3]
  rfl

theorem block43 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes43 ++ tail) state43 =
      KECCAK.Bytes.run 0 tail state44 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes43 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb43 ws)) := by
    rfl
  exact (step state43).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words43).trans perm43))

private def absorb44 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x15 0x15 0x16 0xff 0x60 0x4 0x90 0xa)) 1 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xcc 0x16 0x61 0x15)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x0 0x60 0x5b 0xfd)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x84 0x16 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x8 0x17 0x61 0x15 0x15 0x15 0x14 0x16)) 9 (by decide) (UInt64.ofBytes 0x0 0x60 0x5b 0xfd 0x80 0x0 0x60 0x57)) 10 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0x73 0x83 0x16 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0x15 0x15 0x14 0x16 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0x44 0x17 0x61 0x15))

private def absorbed44 : Vector UInt64 25 :=
  #v[0xac997fd1c4f386f9, 0x12cdb65c82366ec1, 0x841b0badb639ffa0, 0xd40304985f7199af, 0x5d23d8f829601b3c, 0xc034fc2e4dc03637, 0x513c62194fad83a9, 0xf6abab6f0aa2f80c, 0xa178d2d53a81a2fd, 0xd93ac10f636f212a, 0xa99f6fa43d28c466, 0x6cf6e7659314f7e, 0x1d1f155b44aa8789, 0x673b76b1c7caa65c, 0x2d8b3687263c4deb, 0xf4bb7fbefeaeff1e, 0xfaf6a5b6a382b6dc, 0x286b4d8ff0fd9f15, 0xd67ec3216ee29d65, 0x3732c21ac710201c, 0x4d2b9deb4bd96c27, 0x298c614c1e6ead67, 0x1d9efd31bcf21114, 0xe19d190b2fb9f249, 0x504dbb429035f728]

private theorem words44 : absorb44 state44 = absorbed44 := by
  decide +kernel

private def quarter44_1 : Vector UInt64 25 :=
  #v[0x697bf310cbb35446, 0xa202815172c6a5f1, 0xb16b0f13003db98a, 0x4c09ea1bae9e9fb5, 0xdc75aaad697f66e3, 0x4633ec8ebd76d99b, 0x12308463f81b61f8, 0x5afba52ecf2ce596, 0x13785455fbfc9811, 0x185d2231932128a4, 0x6991b654dbec8a72, 0x9be2db370562b83d, 0x92853dee9452bc0f, 0x3c91a6b9024e9c1b, 0xa2ed2b73448f8446, 0x8b6603050b87bca3, 0x21b2692630ab2d5f, 0x7f8a3b424439cacb, 0xe1edb68fd63eb79e, 0xf5a101d76b6c55fc, 0x418be1dccb1bb55, 0x7894ae2654925ab3, 0xd273be5c6d46b37a, 0x44b0cfcb15b8b0af, 0x3f2372bc8e51b4d4]

private theorem rounds44_0 : sixRounds 0 (by decide) absorbed44 = quarter44_1 := by
  decide +kernel

private def quarter44_2 : Vector UInt64 25 :=
  #v[0x3b0413fad2078f43, 0xd2bd398607e99058, 0x9392cbd9605da152, 0xf4ca5f013ed76989, 0xf9bab8b8d76ca2c1, 0xab0574e24c91127c, 0xd946f37fe8247c9c, 0xaffcf8ee7df8c37d, 0xff138930285ef114, 0x839e0522f50266a7, 0x87f0c511d6967031, 0xd31ea9050b1ea82f, 0xc3a40b053b3c0fb9, 0xcb6354f9106acfcb, 0x2c34684e505de4c5, 0x115259531b61a4e2, 0xf9c14897b2ed951b, 0x3bf94baf8f761e72, 0x83422913b3cb10a8, 0xc0adfdffb26b5880, 0xd331edd24ffc47d0, 0xe9e52a54ee52a4ea, 0xa4e9428da7a6d197, 0x5576aab6711f0952, 0x9e323cf31201dba]

private theorem rounds44_1 : sixRounds 6 (by decide) quarter44_1 = quarter44_2 := by
  decide +kernel

private def quarter44_3 : Vector UInt64 25 :=
  #v[0x67a75d2f6c916102, 0x91c3cd1bf5612a30, 0xb799b9f3beb33970, 0xa3b03c376a9d327e, 0x4be96b82f4ab7835, 0x420b49a50263f112, 0x826b2f58a93588eb, 0x7d2dca63f4103817, 0x262f576dd56ab6d0, 0x71cbccddb6c2df34, 0x7fb95b7e44a8a47c, 0xefe1e7bb4dc184fe, 0x66a94a2f09d88beb, 0xbf059fd5435e5eb6, 0x19734ed9e990a614, 0x46a23f930f075859, 0x3de031a9ce7cfc5c, 0x113096ae4ea2355a, 0x790caccda642a912, 0x1236427eb3a66ec, 0x6fc66007dd421b8b, 0x145955693cc93992, 0xcfbbfeb27ddccedb, 0x556f092a48d27a2d, 0xcb0445df16f6bea1]

private theorem rounds44_2 : sixRounds 12 (by decide) quarter44_2 = quarter44_3 := by
  decide +kernel

private theorem rounds44_3 : sixRounds 18 (by decide) quarter44_3 = state45 := by
  decide +kernel

private theorem perm44 : KECCAK.f1600 absorbed44 = state45 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds44_0, rounds44_1, rounds44_2, rounds44_3]
  rfl

theorem block44 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes44 ++ tail) state44 =
      KECCAK.Bytes.run 0 tail state45 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes44 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb44 ws)) := by
    rfl
  exact (step state44).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words44).trans perm44))

private def absorb45 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x0 0x60 0x5b 0xfd)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x82 0x16 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0x80 0x17 0x61 0x15 0x15 0x15 0x14 0x16)) 7 (by decide) (UInt64.ofBytes 0x0 0x60 0x5b 0xfd 0x80 0x0 0x60 0x57)) 8 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 9 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 10 (by decide) (UInt64.ofBytes 0x73 0x81 0x16 0xff 0xff 0xff 0xff 0xff)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x15 0x15 0x14 0x16 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x80 0x0 0x60 0x57 0xbc 0x17 0x61 0x15)) 15 (by decide) (UInt64.ofBytes 0x51 0x80 0x90 0x4 0x60 0x87 0x5b 0xfd)) 16 (by decide) (UInt64.ofBytes 0xd2 0x17 0x61 0x90 0x1 0x20 0x60 0x90))

private def absorbed45 : Vector UInt64 25 :=
  #v[0xcf44953141a200ab, 0x93aa0f10eb4240b0, 0x475b6da6ab396ec5, 0x3e1ccaee8923ce95, 0xf2bea8a8dea66868, 0xd0c34619cceab7c4, 0x4fd8373dbc42810d, 0x93f45e2b17b0cd5, 0x407afb191ad868f1, 0xf60728c2e143da9f, 0xe20e54417eb660cb, 0x41c157adfc473c8a, 0x31ffdb213372fda3, 0x466bffd012f5ffcc, 0x7c0a4902b1d979fa, 0x6bdc19f45c9d68da, 0xc2c558c1bbf2fab2, 0x9c85cd2fa0e74bd8, 0x2940aca95100d9da, 0x4831421113796e0e, 0x146feb366572e15b, 0x30ae3174cc5a0f81, 0x9e1b9ff11f33f2fa, 0x31c8e56a6534f961, 0x6c7d4e83d67291a4]

private theorem words45 : absorb45 state45 = absorbed45 := by
  decide +kernel

private def quarter45_1 : Vector UInt64 25 :=
  #v[0xdc95911a810dc08, 0x46989593ab0233cf, 0x52aa76a5c1154b07, 0x79e47c4191492363, 0xfc2b0783f713d65e, 0x61227363344e0880, 0x8b7ea82e1e2f05be, 0x40a93d7d0ce2f4b3, 0xe77cc0eb4ba5d721, 0xf56ed42635b72aa4, 0x19e5ff2a6fd04c6c, 0xe3154846075c2e95, 0xe746a4b34ec0b877, 0xcb0026237c6875ca, 0x6f6e3bb53882ab52, 0x1efe22849ea20da9, 0x578d662556f7b318, 0x987a7e67448c199c, 0x6e5dd5f6d69e2282, 0x9fa09f7b1f835f6, 0xeee8eab4c8a55d02, 0xeca55c267c25485, 0xfe68ee31630b3dac, 0x18cfdaded2903c58, 0x37478f25752877d6]

private theorem rounds45_0 : sixRounds 0 (by decide) absorbed45 = quarter45_1 := by
  decide +kernel

private def quarter45_2 : Vector UInt64 25 :=
  #v[0x2c4557d676b07a6, 0x23bc717bd5d28648, 0x51ee9f4be8ead87e, 0xcc94447502307971, 0xa707d5b673f16d8b, 0xb91f4ed8283f1e20, 0x6b6ce0c359707aa6, 0x89604dd1fa5937ef, 0xbb77c5cb09cad9fa, 0x5c36287ef89695b0, 0xcc56b7bbb7a5ba44, 0xa02ff3f245a865d3, 0xcc312174b1beb87, 0x45208da8976b7637, 0xb86ada5db7e723e3, 0x5b1fba9ab503f9f1, 0x49170483095194f0, 0xac900d9c41f97079, 0x6f502299cf61fa3d, 0x5f16e1f0f10f555d, 0xefa35d837262de85, 0x9a8fc13ad860382e, 0xd8b66e69f1549aa3, 0xcd4ccc858cf22026, 0x677f45aafcd358ab]

private theorem rounds45_1 : sixRounds 6 (by decide) quarter45_1 = quarter45_2 := by
  decide +kernel

private def quarter45_3 : Vector UInt64 25 :=
  #v[0x273b293f811e0dfb, 0x59bbc943a09d4059, 0x1feb7db7698566d8, 0x16c640523fe24f3e, 0x7578656ae6cee20b, 0xfdb82453bae81e4a, 0x84d80ddcaff7b47b, 0x95b29e1cb215689, 0x6b303d2bd0ed7f9, 0x1cba8d8bcf18e223, 0x161d0e4503744b80, 0xb7ccd56887641fc9, 0xb7141680413336f6, 0x473e9f042960ac11, 0xf5fe97e33b049152, 0xfb03989cfd87cf2b, 0x8541bb04d57fe3ac, 0x3d7cf2d93cd4a6a9, 0xb60c98fe7a0a9dda, 0xa5b7c24397151e03, 0x7d9ebbc567b8e0ce, 0xf3aa2a7a6a023a5b, 0x5de3deb5ffe7e03f, 0xc82df151041c463b, 0xd564a71ca0333d3b]

private theorem rounds45_2 : sixRounds 12 (by decide) quarter45_2 = quarter45_3 := by
  decide +kernel

private theorem rounds45_3 : sixRounds 18 (by decide) quarter45_3 = state46 := by
  decide +kernel

private theorem perm45 : KECCAK.f1600 absorbed45 = state46 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds45_0, rounds45_1, rounds45_2, rounds45_3]
  rfl

theorem block45 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes45 ++ tail) state45 =
      KECCAK.Bytes.run 0 tail state46 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes45 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb45 ws)) := by
    rfl
  exact (step state45).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words45).trans perm45))

private def absorb46 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x5b 0x56 0x8a 0x2e 0x61 0x90 0x91 0x92)) 1 (by decide) (UInt64.ofBytes 0x90 0x51 0x80 0x90 0x5 0x60 0x86 0x50)) 2 (by decide) (UInt64.ofBytes 0x92 0xe9 0x17 0x61 0x90 0x1 0x20 0x60)) 3 (by decide) (UInt64.ofBytes 0x50 0x5b 0x56 0x8a 0x2e 0x61 0x90 0x91)) 4 (by decide) (UInt64.ofBytes 0x60 0x90 0x51 0x80 0x90 0x7 0x60 0x85)) 5 (by decide) (UInt64.ofBytes 0x91 0x92 0x0 0x18 0x61 0x90 0x1 0x20)) 6 (by decide) (UInt64.ofBytes 0x84 0x50 0x5b 0x56 0x8a 0x2e 0x61 0x90)) 7 (by decide) (UInt64.ofBytes 0xa 0x0 0x1 0x61 0x0 0x60 0x6 0x60)) 8 (by decide) (UInt64.ofBytes 0x16 0x19 0x2 0xff 0x60 0x81 0x54 0x81)) 9 (by decide) (UInt64.ofBytes 0x90 0x17 0x2 0x16 0xff 0x60 0x83 0x90)) 10 (by decide) (UInt64.ofBytes 0x61 0x0 0x60 0x8 0x60 0x83 0x50 0x55)) 11 (by decide) (UInt64.ofBytes 0xff 0x73 0x81 0x54 0x81 0xa 0x0 0x1)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x83 0x90 0x16 0x19 0x2 0xff 0xff 0xff)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed46 : Vector UInt64 25 :=
  #v[0x2e923377b4c36cb2, 0x4a7ab42056c4d73c, 0xbf04e655bdd8a47d, 0xdeb1fb2d39d1545, 0xe0b6494ca70a1f3a, 0xacd483e460fde159, 0x8ab7d92937b1fb0f, 0x5c140bfa14d87af5, 0xda1a71673227a3ae, 0xc01972c546bd4e1c, 0xe4c2346a79fb84a9, 0x8fe849557c28bd36, 0xda91b93d099a7675, 0x3abef98e8b77ac5c, 0x12bbf15432194abe, 0xf764f4d14791acf6, 0xc47d043f716fff8e, 0xb51765e4d9728aad, 0x360f8b164199471a, 0x8c684e917326d336, 0xa5b5845cf9b10884, 0xa31c65f2a93516fb, 0x432d48d1d50e7359, 0xf516dab25bf806b9, 0xe02e762fb8cef734]

private theorem words46 : absorb46 state46 = absorbed46 := by
  decide +kernel

private def quarter46_1 : Vector UInt64 25 :=
  #v[0xa920bae17608d38e, 0x85948e5c1e7577e5, 0x5d60826179c98b24, 0x2c50fec5715dfab4, 0xa444a6e5c8768ff4, 0x5b8e2764ccec9c92, 0x4768dbd042192136, 0x5dd36348059a2d34, 0x8611bc6baeb98a0b, 0xc0c1edf156831db5, 0x1993e64b1e4337f4, 0xd081af0eea2d9f1b, 0x785ded7362816d93, 0x614ebabc2f4e794a, 0x9c9777889d274d55, 0x9f74695126816a19, 0xb4aefb13074273d3, 0x4472cd5ef73c53b2, 0x38ae82cb0978a07a, 0x13be2171623f58c3, 0xc5128bfc79982785, 0x3c836efb0d1c4340, 0xa9580596f02abdaa, 0x4e45bd1b47704ad8, 0x7c6b93b6d1399efc]

private theorem rounds46_0 : sixRounds 0 (by decide) absorbed46 = quarter46_1 := by
  decide +kernel

private def quarter46_2 : Vector UInt64 25 :=
  #v[0xbfd4669f9a1d2dce, 0xddb07991c3eb97c0, 0x5032927e9ea9b6ef, 0x773594c1dbbaf549, 0xe47b676a9b923c9c, 0x54742583199167ed, 0xa38111278bbd2958, 0x2c7ef4e316f27d46, 0x3cae665e8b99d8b2, 0xa4d79276cfad6321, 0x4ea1f09bd9cfc21a, 0x6777d4d35d58fb6d, 0xd54a568894d284f3, 0xcf41b33f920c13b8, 0xd04fdb01b7941f0e, 0x9616d440259aec15, 0xbb529fee9c5240fc, 0xb90d2f575b2be46f, 0xd328afaa5fe1f86f, 0x67c39f2881a60d35, 0xd1d55d1a7850f9a0, 0xa6161f9564dada97, 0x9f1912ee7797b637, 0x357a653b0928aac0, 0xda49017e1d3f0cd3]

private theorem rounds46_1 : sixRounds 6 (by decide) quarter46_1 = quarter46_2 := by
  decide +kernel

private def quarter46_3 : Vector UInt64 25 :=
  #v[0x40dc7cf76a7e48cb, 0xc9d7e9247e3f9b0c, 0x20e5a06078ca414b, 0x34c86b036735b27, 0xd3ac6d27a62dd360, 0x87c0c0ac7af6d1fa, 0xe352fc9778e3f497, 0x7fd057640e0483e4, 0xbaa764b4589ce91c, 0xd071fddc104e47a6, 0x61dcaa17f45bd427, 0xc756a6809fd89172, 0xd5f9dc4f3bf57b6f, 0xc23ea19f0dbee767, 0x89d25d508f984e7b, 0x435beb8818ac9908, 0x7933c2331931a718, 0x65ee7d9a9e86f716, 0x57d36178a313f1ef, 0x14f3de478ffa0305, 0x4e05ef5777dcf1ba, 0xe3f70dbad1e2f5e0, 0xec789d3d65c4b936, 0xff58945b385ff860, 0x88a3b3fff62e2129]

private theorem rounds46_2 : sixRounds 12 (by decide) quarter46_2 = quarter46_3 := by
  decide +kernel

private theorem rounds46_3 : sixRounds 18 (by decide) quarter46_3 = state47 := by
  decide +kernel

private theorem perm46 : KECCAK.f1600 absorbed46 = state47 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds46_0, rounds46_1, rounds46_2, rounds46_3]
  rfl

theorem block46 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes46 ++ tail) state46 =
      KECCAK.Bytes.run 0 tail state47 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes46 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb46 ws)) := by
    rfl
  exact (step state46).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words46).trans perm46))

private def absorb47 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x17 0x2 0x16 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x0 0x60 0x1 0x60 0x82 0x50 0x55 0x90)) 2 (by decide) (UInt64.ofBytes 0x73 0x81 0x54 0x81 0xa 0x0 0x1 0x61)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 5 (by decide) (UInt64.ofBytes 0x90 0x16 0x19 0x2 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0x73 0x83)) 7 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 8 (by decide) (UInt64.ofBytes 0x2 0x16 0xff 0xff 0xff 0xff 0xff 0xff)) 9 (by decide) (UInt64.ofBytes 0x60 0x2 0x60 0x81 0x50 0x55 0x90 0x17)) 10 (by decide) (UInt64.ofBytes 0x81 0x54 0x81 0xa 0x0 0x1 0x61 0x0)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x16 0x19 0x2 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x83 0x90)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 16 (by decide) (UInt64.ofBytes 0x16 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed47 : Vector UInt64 25 :=
  #v[0xe289d0429d8fb877, 0x98c065bd542d19f8, 0x8d78d48f749ff115, 0x36905011b4268812, 0xb45c36ddcc134bb0, 0x422b8903e008b56c, 0x8a2d92f4738677c9, 0x1e329ceae9864697, 0xb1d44e5ce3c8a2ee, 0x8a0220cb603f54ed, 0x6d6c0608fabd7bec, 0xbf959bd5776d3f0, 0xaba0f05294ac98f6, 0x6a7dcf7d0eb4ade8, 0x5eeff6d648427d05, 0x81612d7aec74873, 0x5b9392ec056e6962, 0xb73b62857d2caa25, 0xf758aaef74ea1ae6, 0xdde8653f57e9ab44, 0x20059e6ab56f78a9, 0x99915c6bf30cc5ef, 0x1e60018bc238683, 0xf2db048e2ef41854, 0x4ba51c6b28d23274]

private theorem words47 : absorb47 state47 = absorbed47 := by
  decide +kernel

private def quarter47_1 : Vector UInt64 25 :=
  #v[0x487f18ae5b24b84f, 0x13db5eca939f4b9b, 0x7a2e32c628dc216c, 0x9cef13ab3ac2f43b, 0x4686637e64f3356b, 0x69b409aebc0205fa, 0x72895e10db883e8c, 0x1aa9d034f1dc6737, 0x5c24fbfa90ec93c6, 0xb7ff05b3e683be8f, 0xcbaf51d40d1092b6, 0x65cd247ab4223290, 0x4867ac734fa3c040, 0xeda2ce3cf19d2658, 0xbcbc45ac8d4c8c0f, 0x7369c4fbc9f2b3b9, 0x5ed74da01b041ea6, 0x93a894621ae9ba74, 0x918ea3b8d5268d28, 0x5c699e694b33cdfc, 0xd39c54ee4f11408b, 0x4314b2bdf53acdd7, 0xcd6be91b2b01d027, 0x70015c3a9be1c6e6, 0x6a34418d00e2bc41]

private theorem rounds47_0 : sixRounds 0 (by decide) absorbed47 = quarter47_1 := by
  decide +kernel

private def quarter47_2 : Vector UInt64 25 :=
  #v[0x9625f76756e20d72, 0xa792dd843094b979, 0xe230036a04af66eb, 0x50d03f0ce57d4e36, 0xc0d550ce0e3d1e6b, 0x76fb6a3e51b16f4f, 0xa5f18d0a74d16e3c, 0x60c09eafd7fc041, 0xadd57683583fe39a, 0x721315c48307849, 0x9feddf4d66f36512, 0x82ca07a7f18c0d5a, 0x12a2a7184b1008ea, 0x21c0f821b70a0d3c, 0x19ddd28322f5f759, 0xd76f7dbfbc6abb45, 0x5a7bc9cd2c07deae, 0x9bfb4b6c347738dc, 0x12cf8d739da9e119, 0x714f0fb8bde16798, 0xc661334ce06e2301, 0x9403d0841d0b0a83, 0xf3a78e6c3a96974a, 0x3de32e57a208771e, 0x1a9588d4b2178972]

private theorem rounds47_1 : sixRounds 6 (by decide) quarter47_1 = quarter47_2 := by
  decide +kernel

private def quarter47_3 : Vector UInt64 25 :=
  #v[0xc4a1dd4980513b76, 0x1456d8f674261372, 0x5377d8c7b3233554, 0x1eaa9ff3aad8d10f, 0x73d618f61941965f, 0xa2f63d4442cf664f, 0x53255efa773a7992, 0x63f32585b0dc2764, 0xb620e80ca93370, 0xfc460652f8fd79a9, 0x72677389ee0ffd8, 0x37da3cd999a9b5d0, 0xefdb93a3dedb6534, 0xd0786a4ce5d559b3, 0xf07785942c5c7969, 0x3bf350b44c0083b, 0x47fc103f3088e562, 0x674af1305a52968c, 0x65f3cc17dd6d6fe2, 0x3b6fa2878fa98979, 0xfac5ee6ed9009415, 0xea65a4426d03c6d4, 0xef9f3ef6112126e6, 0x91ce233a2eb16aec, 0xc759ffae06723e7d]

private theorem rounds47_2 : sixRounds 12 (by decide) quarter47_2 = quarter47_3 := by
  decide +kernel

private theorem rounds47_3 : sixRounds 18 (by decide) quarter47_3 = state48 := by
  decide +kernel

private theorem perm47 : KECCAK.f1600 absorbed47 = state48 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds47_0, rounds47_1, rounds47_2, rounds47_3]
  rfl

theorem block47 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes47 ++ tail) state47 =
      KECCAK.Bytes.run 0 tail state48 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes47 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb47 ws)) := by
    rfl
  exact (step state47).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words47).trans perm47))

end Blanc.Lift.Usdc.ImplV1Creation.SigningBlocks
