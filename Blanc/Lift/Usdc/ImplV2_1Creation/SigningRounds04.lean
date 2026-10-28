import Blanc.Lift.Usdc.ImplV2_1Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_1Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb024 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x91 0x90 0x35 0x1 0x81 0x20 0x60 0x91)) 1 (by decide) (UInt64.ofBytes 0x90 0x35 0x1 0x81 0x40 0x60 0x90 0x16)) 2 (by decide) (UInt64.ofBytes 0x80 0x60 0x90 0x35 0x1 0x81 0x60 0x60)) 3 (by decide) (UInt64.ofBytes 0x1 0x81 0xa0 0x60 0x90 0x35 0x1 0x81)) 4 (by decide) (UInt64.ofBytes 0x1 0x82 0xc0 0x60 0xff 0x60 0x90 0x35)) 5 (by decide) (UInt64.ofBytes 0x35 0x1 0x81 0xe0 0x60 0x90 0x16 0x35)) 6 (by decide) (UInt64.ofBytes 0x33 0x61 0x35 0x1 0x0 0x1 0x61 0x90)) 7 (by decide) (UInt64.ofBytes 0x35 0x61 0x43 0x3 0x61 0x5b 0x56 0x7d)) 8 (by decide) (UInt64.ofBytes 0x4 0x60 0xf1 0x3 0x61 0x5b 0x56 0x27)) 9 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x40 0x60 0x3 0x36 0x80)) 10 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x9e 0xc 0x61)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0x73 0x50 0x5b)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x81 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x61 0x35 0x1 0x20 0x60 0x90 0x16 0x35)) 15 (by decide) (UInt64.ofBytes 0x60 0x52 0x4 0x61 0x5b 0x56 0xa0 0x35)) 16 (by decide) (UInt64.ofBytes 0x81 0x20 0x1 0x61 0x3 0x36 0x80 0x4))

private def absorbed024 : Vector UInt64 25 :=
  #v[0x7c97e12c87df4578, 0x38b52c9a017da6c9, 0xd9a2f8081922b48, 0x81084488d6bdea54, 0x6093a3e9673b7c1e, 0x6bea0db459fc613, 0x23e350a47944b961, 0x6aa18c194abbb621, 0x312b353d6d2322c2, 0xc1af544a2fb40f7e, 0xf28b1d26333e78ff, 0x6fe36bc68eec3357, 0x4f15c3d0180732ed, 0x47bab46b3c3fdf78, 0xaafe4e379d2cabe9, 0xdce9cbbade12bbf1, 0x6e43e1d3b1a80a6e, 0x1171a5afcbeb9156, 0x7e7917479f2c796b, 0xc91b0df2f98b3464, 0x2fbbcf758f4ea203, 0xe099353ec78bfb5b, 0x984a8efb97c9156d, 0xa3af1c76de76b9b6, 0x9be57642da4ed893]

private theorem words024 : absorb024 state024 = absorbed024 := by
  decide +kernel

private def quarter024_1 : Vector UInt64 25 :=
  #v[0x8fb15248cf2cd5e6, 0x3c16c761932abdbd, 0xcd2df2ab2a189d40, 0xec6293e437ba8c93, 0xad3e708915849a7f, 0xc0f6fe348940b7d7, 0xc0f0ff2d3a6c5a32, 0x45dc4201372a60c2, 0x5fe893ead4a690b5, 0x8e7e401abf4071b3, 0x2808d5a385bd91a7, 0x4485c011c28cadb7, 0xe2fc019f598c45a3, 0xf5c23f1f9f513f1d, 0xf03e0e9146514bc7, 0xddae455c14a8e5e2, 0x3a0616bf567aa1e6, 0xb695cb5284294b39, 0xe73874abb5ccbe4c, 0xe738703d8b9e8615, 0x61e1c9d572bda64a, 0x2be856cd035d91ca, 0xd9cf1e787b1b6f5f, 0x7845c61da7e08c4a, 0x6ce681f090d7cdc7]

private theorem rounds024_0 : sixRounds 0 (by decide) absorbed024 = quarter024_1 := by
  decide +kernel

private def quarter024_2 : Vector UInt64 25 :=
  #v[0x28a48ea87c9fdc1, 0xed4940c9a1d80ad, 0xac2e0c90909bad31, 0xdb9456ebe9fa8dfc, 0xeae281c52df25452, 0x66dbb06a069626ab, 0x57afc4c96f03d1d, 0x871210efc4de49ef, 0xf36966c34ed71aa1, 0x10a3b32f5701f4aa, 0xc5cd0945cc51d7c1, 0x276df37eb08060fb, 0xc695de9b513dad7, 0xa5fb67a677cce0b9, 0x1a20f066a43235ee, 0x172ea94b2f8eea, 0x7b9aff9522f3a8b7, 0x3429f0c02b3ecf8a, 0x7e3aaecf2cdbe6f7, 0x892468c5c053b13e, 0x4ccb18a3752dba76, 0x76ddc820f8eeca8a, 0x707fade50d6b6c76, 0xa47c212e309d666b, 0x72a5d91c3f4b54f2]

private theorem rounds024_1 : sixRounds 6 (by decide) quarter024_1 = quarter024_2 := by
  decide +kernel

private def quarter024_3 : Vector UInt64 25 :=
  #v[0x7842dde1d7935786, 0x4015b5bc826a0454, 0xa71d54fde2c24a52, 0xc69acde8deb4010d, 0x630dcb68870662e, 0x57fa1efe6eddfb83, 0xd3f33d5f64609497, 0xa78deb69894f28fd, 0xc92d49cd6482fd42, 0xcf8f6624be3b51d4, 0x845a2271c90a453e, 0xe8efb6a94e2ea971, 0xea0725df668ee774, 0xc615151abe62a3ee, 0x42b28e6170fe0eb4, 0x97c1566710dd56d7, 0x366edc4c6c1ce575, 0xdbad3b1fa90b9734, 0x38a5e7dcef040aa6, 0x6f68d44fe9fba8c2, 0xe4bac6758188e0ed, 0x8c4386ba218f173a, 0xb8658ecdfe3bd030, 0x23e1fe0fb8c08037, 0x31991db07e1e5340]

private theorem rounds024_2 : sixRounds 12 (by decide) quarter024_2 = quarter024_3 := by
  decide +kernel

private theorem rounds024_3 : sixRounds 18 (by decide) quarter024_3 = state025 := by
  decide +kernel

private theorem perm024 : KECCAK.f1600 absorbed024 = state025 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds024_0, rounds024_1, rounds024_2, rounds024_3]
  rfl

theorem block024 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes024 ++ tail) state024 =
      KECCAK.Bytes.run 0 tail state025 := by
  exact run_block_of_step bytes024 tail absorb024 state024 absorbed024
    state025 (fun _ => rfl) words024 perm024

private def absorb025 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0xd8 0xc 0x61 0x15 0x10)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0x73 0x50 0x5b 0xfd 0x80)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x20 0x60 0x91 0x16 0x81 0x35 0x81 0xff)) 5 (by decide) (UInt64.ofBytes 0x60 0x90 0x16 0x91 0x90 0x35 0x1 0x81)) 6 (by decide) (UInt64.ofBytes 0x81 0x60 0x60 0x90 0x35 0x1 0x81 0x40)) 7 (by decide) (UInt64.ofBytes 0x35 0x1 0x81 0x80 0x60 0x90 0x35 0x1)) 8 (by decide) (UInt64.ofBytes 0x60 0x90 0x35 0x1 0x81 0xa0 0x60 0x90)) 9 (by decide) (UInt64.ofBytes 0x90 0x16 0x35 0x1 0x82 0xc0 0x60 0xff)) 10 (by decide) (UInt64.ofBytes 0x1 0x61 0x90 0x35 0x1 0x81 0xe0 0x60)) 11 (by decide) (UInt64.ofBytes 0x5b 0x56 0xd8 0x35 0x61 0x35 0x1 0x0)) 12 (by decide) (UInt64.ofBytes 0x3 0x36 0x80 0x4 0x60 0x52 0x4 0x61)) 13 (by decide) (UInt64.ofBytes 0x43 0xd 0x61 0x15 0x10 0x81 0x20 0x60)) 14 (by decide) (UInt64.ofBytes 0x35 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0x73)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed025 : Vector UInt64 25 :=
  #v[0x3ad498e258665e76, 0xa1c85e5560ae2e52, 0xdcf77898758d37a9, 0x1ceae55a010b7fd0, 0x251273d6dbb6bb05, 0x93f0722bdab66a37, 0x482a3821f9c1085f, 0x9d92f4eaea84a4e1, 0xd76f98c3c412f442, 0x71ba0589ca94db8f, 0xa59ab776b80af5e3, 0x4bac785b49f6886e, 0x5f213acc3a08aa01, 0x7886fe00b7925094, 0x7ddc10bb92de2291, 0x6af5dfb1ac30ded6, 0x41048044e6029b40, 0x8aa4e8991587ae94, 0x76d9867a524e3038, 0x300399d9ced9e46, 0x334ab618c605ad9, 0x696782173d4943f5, 0x228686d609c2fdd6, 0x7d54c39faba8a5bc, 0x99668d4bbff4f10e]

private theorem words025 : absorb025 state025 = absorbed025 := by
  decide +kernel

private def quarter025_1 : Vector UInt64 25 :=
  #v[0x81701a3057543fe, 0x53435f128e3de9f8, 0x365e31226b9e4b3e, 0x2df72493ffd7bff4, 0xb473563e04ccb887, 0x804dd6875423eb46, 0xfb991e000a594071, 0xd3469f2a2367b379, 0x2b24965577531021, 0xc47f9083c0bf7b9d, 0x2be212f32426552c, 0xf5ad62d22a9cc308, 0xd3447270f2bb07ad, 0xcf770a2858444c34, 0x5b21c0fe433b68a7, 0xfbd8b8d316b84442, 0x8b243f76a2e8c14e, 0x75a95f8a614c0d3b, 0x5ed85bb0c2352e00, 0xd4d7cc51a1955870, 0xc06d31767f1b578a, 0x45961f9c3dd5edce, 0x75ae17ac76005d5c, 0x8837d2b8a32cc4ed, 0x6ea5a7878469c5ae]

private theorem rounds025_0 : sixRounds 0 (by decide) absorbed025 = quarter025_1 := by
  decide +kernel

private def quarter025_2 : Vector UInt64 25 :=
  #v[0x43e03850d01b1ea2, 0x83ae474f1e4686f5, 0x4b913e9c8dee33ae, 0x42b259b43fad119f, 0xcc8883e41ab0afb1, 0xe11381d6368c6403, 0xecb1fba44f65fe9f, 0x6e901331c0da5a38, 0x1c0c87b5c654362d, 0xeb8faad2ef548af4, 0x2e6f1c36dc97fbba, 0xf1f1052d2c0665cc, 0xc4a22223d200ea63, 0x2133c93d745b5ef3, 0x9179e3b56b952fe0, 0x3c5534ee03dd7439, 0xe3c2cb577daa28e6, 0x77db8bd9ff8ab482, 0x90e39385bd3cd3a8, 0xcb07ac7fa893d1a7, 0x21ecace27f549e36, 0xdcfea7df81ee0950, 0xf5d7371649633a95, 0x2a2aee72579dabc5, 0x2cdc15248d49b3c3]

private theorem rounds025_1 : sixRounds 6 (by decide) quarter025_1 = quarter025_2 := by
  decide +kernel

private def quarter025_3 : Vector UInt64 25 :=
  #v[0xa6d5f03799ab97da, 0xfc2ee99bc606a78d, 0x29e9ff245972caf2, 0xc8ebaf8297d7aef8, 0x7cba51067419177, 0x31d6e427419e632, 0x9bd8481dfc2cf47d, 0x32839f233a727aeb, 0x24dd4e7a27f7807b, 0xa8009838d608ae01, 0x313b6baeadda35a3, 0xec0b3bfbce67e225, 0xa1ec0fde7b3f887d, 0xb1e77f3193352bdb, 0x4a9b812ae169bfc1, 0x170ab30f0a8d8ea2, 0xd29f88daf7b1926c, 0x156403dfa7dbe897, 0xecdcce4e51835f62, 0xabe487ff375b187e, 0x16250660b7a3dfb1, 0x60dce12ba64ca17a, 0xce58b6e412b8c90c, 0xfa615a591258a48d, 0x668ed4543e630453]

private theorem rounds025_2 : sixRounds 12 (by decide) quarter025_2 = quarter025_3 := by
  decide +kernel

private theorem rounds025_3 : sixRounds 18 (by decide) quarter025_3 = state026 := by
  decide +kernel

private theorem perm025 : KECCAK.f1600 absorbed025 = state026 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds025_0, rounds025_1, rounds025_2, rounds025_3]
  rfl

theorem block025 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes025 ++ tail) state025 =
      KECCAK.Bytes.run 0 tail state026 := by
  exact run_block_of_step bytes025 tail absorb025 state025 absorbed025
    state026 (fun _ => rfl) words025 perm025

private def absorb026 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x37 0x61 0x16 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0x4 0x60 0x52 0x4 0x61 0x5b 0x56 0x75)) 2 (by decide) (UInt64.ofBytes 0x15 0x10 0x81 0x20 0x60 0x3 0x36 0x80)) 3 (by decide) (UInt64.ofBytes 0xfd 0x80 0x0 0x60 0x57 0x76 0xd 0x61)) 4 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x35 0x50 0x5b)) 5 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 6 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 7 (by decide) (UInt64.ofBytes 0x3 0x61 0x5b 0x56 0xc8 0x38 0x61 0x16)) 8 (by decide) (UInt64.ofBytes 0x20 0x60 0x3 0x36 0x80 0x4 0x60 0xf1)) 9 (by decide) (UInt64.ofBytes 0x60 0x57 0xa9 0xd 0x61 0x15 0x10 0x81)) 10 (by decide) (UInt64.ofBytes 0xff 0x73 0x35 0x50 0x5b 0xfd 0x80 0x0)) 11 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 12 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 13 (by decide) (UInt64.ofBytes 0x56 0xaf 0x39 0x61 0x16 0xff 0xff 0xff)) 14 (by decide) (UInt64.ofBytes 0x80 0x40 0x60 0x54 0x80 0x4 0x60 0x5b)) 15 (by decide) (UInt64.ofBytes 0x85 0x1 0x60 0x2 0x60 0x20 0x60 0x51)) 16 (by decide) (UInt64.ofBytes 0xff 0x7f 0x2 0x0 0x1 0x61 0x15 0x16))

private def absorbed026 : Vector UInt64 25 :=
  #v[0x437228e4ec888fa3, 0x3db021c1d56e4181, 0x216794769a8639b5, 0xc8f46c6c698a4e75, 0x1756e316343c0821, 0x942f641ec1bde70e, 0x621bbfb3fd9317ee, 0xa2ba8e870af2594d, 0x7743bb19b9fd63c4, 0xc60022148e184d6e, 0xfe412bec72476192, 0xa4e19ab035270dd6, 0xfe4a4ac85eb0eb95, 0x27d915a443285c50, 0x1321a81a053c24a, 0x664dc04ea392da35, 0xaf1ff698fa5826df, 0xc3f923cb7a697a58, 0x40d536d3d26ed201, 0x82b8d5f460ee2b3a, 0x4ce157b5ced947b4, 0xfce1bb6a9949f19c, 0x414e467e4a5cbc26, 0x21076ed4093d765a, 0x1dc3d2536b985107]

private theorem words026 : absorb026 state026 = absorbed026 := by
  decide +kernel

private def quarter026_1 : Vector UInt64 25 :=
  #v[0x60dab47a1a0c3e1e, 0x2e394ee056102ef6, 0xe9a918c25e45ed7e, 0xc4a60031c50b3015, 0x1798637efbb8211b, 0xf7814de2fcb4e67a, 0x2c544fa007df3da1, 0x3f37e4ece5855dee, 0x4bce8065f75e8a15, 0xb6ab7f651bb11d25, 0xd44225792fb04aad, 0x1267202ddf54c1ee, 0xaf7abe76cb7b6f6c, 0x86849602319e6e14, 0xf2d6273459aa9fd1, 0x646fe10fafacfd23, 0x2f91c2f85d159445, 0xf236bb7ea80042e5, 0x1b6d5f321287cf2c, 0xd3d04e80bc31ee32, 0xedf899543da5c0d0, 0x2a9d9d2e5cf3672c, 0x60ea224cfbd5cdca, 0xb33e968f3de26e37, 0xe116eaad5e16a3c2]

private theorem rounds026_0 : sixRounds 0 (by decide) absorbed026 = quarter026_1 := by
  decide +kernel

private def quarter026_2 : Vector UInt64 25 :=
  #v[0xc52e2309324ad0da, 0x85c9f9b85b85351c, 0x7cef94a0d1ae1124, 0x5323f96fa57c50e8, 0x55782026b4f7f0ca, 0xede52d16aea38da6, 0xcd2e8bae5bba3944, 0xedb5bb5f552d3771, 0xd24e86bd2b9cccfe, 0x5898430b91c6cdd5, 0x86d7fc9c7309cf81, 0x622c55cd8a0f92d2, 0x741556c2e8ad3a4f, 0x47162e7226684661, 0xdc1bbee6c627b720, 0xa9ee02f617201bac, 0x3fa00f1a967b3c57, 0x7ad044a8fe3afb62, 0x2b69bf07f30cb8e7, 0xcad8394c1db12e80, 0xe697bad72125d77e, 0xa80a03a89adb86c1, 0x80471875d45141cb, 0xdfe7d56d8924ddc9, 0x1455330299993406]

private theorem rounds026_1 : sixRounds 6 (by decide) quarter026_1 = quarter026_2 := by
  decide +kernel

private def quarter026_3 : Vector UInt64 25 :=
  #v[0x3f32074f71f34ad2, 0xb45c0fe6e566ea41, 0x602726d9d2b96d9f, 0x7d2d430be9e2ce01, 0x792a9fc09aba9797, 0xfd6768fa17fbf92c, 0x97a31a32a4811a75, 0x9ba0ad64a632c69b, 0x8ab78d943efdd1d6, 0x13f35cf1bb80ae91, 0xb64f671366af3d58, 0xd4f1ed1ffa7a44fb, 0x78012e98c752e037, 0x953dbdecbfbaeb18, 0x9eac6e90a7534129, 0xb656d0b991d9fe16, 0x8b0a1c1bd8e780c6, 0x8daaf30d05ae8a25, 0xf252c290c3c192c0, 0x1b5558c0c46d6557, 0x4df88aacf05e3112, 0x503788f7216e1b0a, 0x31ac19c13988b4ac, 0xa4f19f9434859e93, 0x72016d652ee2a991]

private theorem rounds026_2 : sixRounds 12 (by decide) quarter026_2 = quarter026_3 := by
  decide +kernel

private theorem rounds026_3 : sixRounds 18 (by decide) quarter026_3 = state027 := by
  decide +kernel

private theorem perm026 : KECCAK.f1600 absorbed026 = state027 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds026_0, rounds026_1, rounds026_2, rounds026_3]
  rfl

theorem block026 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes026 ++ tail) state026 =
      KECCAK.Bytes.run 0 tail state027 := by
  exact run_block_of_step bytes026 tail absorb026 state026 absorbed026
    state027 (fun _ => rfl) words026 perm026

private def absorb027 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 1 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 2 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 3 (by decide) (UInt64.ofBytes 0x1 0xff 0xff 0xff 0xff 0xff 0xff 0xff)) 4 (by decide) (UInt64.ofBytes 0x60 0x4 0x93 0x90 0x93 0x16 0x94 0x90)) 5 (by decide) (UInt64.ofBytes 0x2 0x84 0x4 0x90 0x84 0x1 0x81 0x1f)) 6 (by decide) (UInt64.ofBytes 0x81 0x52 0x92 0x90 0x1 0x84 0x1 0x82)) 7 (by decide) (UInt64.ofBytes 0x82 0x82 0x1 0x83 0x91 0x92 0x52 0x81)) 8 (by decide) (UInt64.ofBytes 0x60 0x80 0x57 0x6a 0xe 0x61 0x15 0x80)) 9 (by decide) (UInt64.ofBytes 0x1 0x61 0x57 0x3f 0xe 0x61 0x10 0x1f)) 10 (by decide) (UInt64.ofBytes 0x52 0x83 0x2 0x4 0x54 0x83 0x80 0x0)) 11 (by decide) (UInt64.ofBytes 0x6a 0xe 0x61 0x91 0x1 0x20 0x60 0x91)) 12 (by decide) (UInt64.ofBytes 0x0 0x60 0x90 0x91 0x1 0x82 0x5b 0x56)) 13 (by decide) (UInt64.ofBytes 0x5b 0x90 0x20 0x0 0x60 0x20 0x60 0x52)) 14 (by decide) (UInt64.ofBytes 0x1 0x1 0x60 0x90 0x52 0x81 0x54 0x81)) 15 (by decide) (UInt64.ofBytes 0x61 0x11 0x83 0x80 0x1 0x20 0x60 0x90)) 16 (by decide) (UInt64.ofBytes 0x1f 0x60 0x3 0x90 0x82 0x57 0x4d 0xe))

private def absorbed027 : Vector UInt64 25 :=
  #v[0x373e25b371266ff0, 0x18b917554bb56660, 0x209fdb94c5b097db, 0x8516adc0da1ac2ec, 0x9fb15e7fa6bef453, 0xb5452e8185685a7e, 0x984d9ebf8b725576, 0xc0217a8a4fc30d55, 0x83a8d96a573cd58, 0x9b601a6ad8af4e42, 0xcf6cd80124ee16f4, 0xcee8768b452d1e72, 0x80f702594062201a, 0x15ab41a544b4edff, 0x5dd286e7262d11f0, 0xfd54d791b22b7d76, 0x971bff3f6537e502, 0x4fdd3e1b9f448ff0, 0x239ca535b913f9c5, 0xfbc0f6e7d75cb40f, 0x17469d139c85594f, 0x827f1656d4158695, 0xbeb9b4ea14eef295, 0xcf747ea9bcc40ae, 0xc19100e5a4700dc9]

private theorem words027 : absorb027 state027 = absorbed027 := by
  decide +kernel

private def quarter027_1 : Vector UInt64 25 :=
  #v[0x7c3c1dabc89fbc5e, 0xa4d8087e19861ec2, 0x3a8d6e560b4a86af, 0x1c1c2645b767ffc8, 0x9cfcb1063107e653, 0x33450c4bc81f55fc, 0x91dfceb7025d862d, 0x2559c766b16a4e65, 0xff339b1315a45c56, 0xc1e582851c190b69, 0xbc4710f5be924fc9, 0x66b12e7283712f7f, 0x5d55f3067480e74f, 0x77725b2bd60d9b7f, 0xbccc0b8217a68225, 0x98fe0dbbdaa8ac4d, 0xde9e933e33cdc777, 0xbc5fac00b9fb5916, 0x2c6fced16a951bf6, 0xf0d56b60ba440eb3, 0x1677b22670f73d38, 0x381f8cd4c0aa0d8d, 0x7947b775b372d7d8, 0xda34c10ef5350fc7, 0x215de838e9d2d28e]

private theorem rounds027_0 : sixRounds 0 (by decide) absorbed027 = quarter027_1 := by
  decide +kernel

private def quarter027_2 : Vector UInt64 25 :=
  #v[0x9c8c1d4e059ad857, 0xb91bde50e812fa99, 0xc007640e16015130, 0x852755007a28ebe, 0x653adb66755e4ded, 0x6559d62b514f20e8, 0xd054511125f58efa, 0x64ad142d95f71498, 0xfd5f11ab5518b762, 0x8235112327f45458, 0xe77e993e4cd8368d, 0xd595c2b196ed1519, 0xffcb433e247b15e7, 0x536fe74c879eeb1d, 0x4830e743a4373091, 0x51f4089303afeec4, 0x593a49c4fb94fe0a, 0x4100b27fa972a685, 0x21fe47a4c2e44688, 0xde613465c32e39bb, 0x357a8f4c94be21b9, 0x210100c04a20b573, 0xf5d508be26cc41d2, 0x19012230d76df508, 0xac6f75003816aa6d]

private theorem rounds027_1 : sixRounds 6 (by decide) quarter027_1 = quarter027_2 := by
  decide +kernel

private def quarter027_3 : Vector UInt64 25 :=
  #v[0x2f3677420f82f47d, 0xf8082f1f19c38247, 0x7f66e74970074ac0, 0x6ee5425f17f2b9f1, 0x2d28b61fd0fe4813, 0x3a05480daa20c7e8, 0xf0836e5fec41ec93, 0xf52880d87d9cd629, 0x14ed0444711a70c0, 0x3003324dc92e334f, 0xb91cee46e0d8c01e, 0x7dd85ec46daecda0, 0xef38d625a025187c, 0x6ae872b0ad031457, 0x4b5415af91ae64ef, 0xfe8499f8019f584c, 0xb50e294d6ef063bd, 0x44975702b8f22219, 0x1447ef8d373a5ddd, 0xabd31a99184f0162, 0x8f0dc2b341078446, 0x16b6a4cd6b06b540, 0xec6752194e913762, 0x41023520f13a9d39, 0x35bff47d2b3d5a45]

private theorem rounds027_2 : sixRounds 12 (by decide) quarter027_2 = quarter027_3 := by
  decide +kernel

private theorem rounds027_3 : sixRounds 18 (by decide) quarter027_3 = state028 := by
  decide +kernel

private theorem perm027 : KECCAK.f1600 absorbed027 = state028 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds027_0, rounds027_1, rounds027_2, rounds027_3]
  rfl

theorem block027 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes027 ++ tail) state027 =
      KECCAK.Bytes.run 0 tail state028 := by
  exact run_block_of_step bytes027 tail absorb027 state027 absorbed027
    state028 (fun _ => rfl) words027 perm027

private def absorb028 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x50 0x50 0x50 0x5b 0x91 0x1 0x82 0x16)) 1 (by decide) (UInt64.ofBytes 0x54 0x1 0x60 0x5b 0x56 0x81 0x50 0x50)) 2 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x1 0x74 0x90 0x0 0x60)) 3 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 4 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 5 (by decide) (UInt64.ofBytes 0x61 0x15 0x16 0xff 0x60 0x4 0x90 0x0)) 6 (by decide) (UInt64.ofBytes 0x7f 0x51 0x80 0x40 0x60 0x57 0xff 0xe)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0xa0 0x79 0xc3 0x8)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 11 (by decide) (UInt64.ofBytes 0x1 0x82 0x4 0x60 0x20 0x60 0x52 0x81)) 12 (by decide) (UInt64.ofBytes 0x52 0x1 0x82 0x24 0x60 0x10 0x60 0x52)) 13 (by decide) (UInt64.ofBytes 0x6c 0x62 0x61 0x73 0x75 0x61 0x50 0x7f)) 14 (by decide) (UInt64.ofBytes 0x65 0x73 0x75 0x61 0x70 0x20 0x3a 0x65)) 15 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x64)) 16 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0))

private def absorbed028 : Vector UInt64 25 :=
  #v[0x5b89cd45a3d11e6d, 0x78583f058d3844c1, 0x718611a658dc7e3b, 0xd2660130d76f0aa0, 0xe0df2b6029299ef1, 0x5e92c79847bbb2b2, 0x1619b6922d7198e6, 0x64e536a85cfb33d4, 0x279272bbb36c00fd, 0xf4e84436fb690d93, 0xc73d9cf20df0f603, 0x75c4c1c0998c9ebc, 0x92e74aa8163561fb, 0x7784ee3f3eaf9d4, 0x619212a296f4ad74, 0x1430dece3dba1e90, 0x5b976a66420c5739, 0xa31a723fc81e85d8, 0x8510f3e427e6205a, 0xfb5163f0dc432c5c, 0xf4c89a951d8236ee, 0xc41f9f35f94e2b51, 0xfe5cedc2df51b2dc, 0xfd55ddeddba07aed, 0xbc06d958a4255041]

private theorem words028 : absorb028 state028 = absorbed028 := by
  decide +kernel

private def quarter028_1 : Vector UInt64 25 :=
  #v[0xd6b3abd1851fe00, 0x5b6ea431c157105c, 0x156c1536d8270ce7, 0x7ef912e81e30b879, 0x6a57f904fbd4b831, 0xcbab263eac80515a, 0x15791baf68943c55, 0x2d8694dad2922262, 0x6c9fc868e99a3b51, 0xbbb89fc628dc57cd, 0xde7d4d973ffc9ce, 0xa8ede408f82bf12, 0x27ce197260c1d11a, 0xaa2bc693cea20beb, 0x5d250f890845626d, 0x5401d1a5d49547a7, 0x6bccdef41f5ddfce, 0x852786fca70922aa, 0x2a40d4f99495ead7, 0x6796cee1852fd2fe, 0xaf9cfc9e63dc9ac2, 0xd7de217124c616d1, 0x30e67d4231e1cef0, 0x2061fda286ed57ef, 0x12e4353a60c188d9]

private theorem rounds028_0 : sixRounds 0 (by decide) absorbed028 = quarter028_1 := by
  decide +kernel

private def quarter028_2 : Vector UInt64 25 :=
  #v[0x15c62473d5ffc601, 0x5b66eff0b6eaaa08, 0xcc03a95162ec37f5, 0x266a38f9653fb165, 0x2fa42f154d834961, 0xbf5bd82b7f335128, 0x6b09a902764ef947, 0xbe2a24136c066e5d, 0x82e438daafc8abb5, 0x4690617106a58152, 0x1425d831e336a7dd, 0xb1f7fc11e1a59545, 0x90f1cb98a145706b, 0xa8dc01c74ff90623, 0x337e79b10ecfedfb, 0x7799914acee083e3, 0xc13bf0513e4d4c18, 0x6d24c3233021f1b9, 0xa0d4bdd8b4e6073f, 0x9eb978a5183551f0, 0x3b65d6d6651c09c9, 0x3b085d992ecd3b90, 0x5ba6905bfcff3476, 0xe3d067e1382de8dd, 0xfeaa708ccdd82639]

private theorem rounds028_1 : sixRounds 6 (by decide) quarter028_1 = quarter028_2 := by
  decide +kernel

private def quarter028_3 : Vector UInt64 25 :=
  #v[0x2a390393ef7956fe, 0x67e9368b41d30117, 0x7a759742da418666, 0x3baf182e829f7954, 0x9c74029f1d40989c, 0xb975854ec153d85b, 0xd4da1312729e04c7, 0x55cbbfaec5b8f9f0, 0x8eed506b5be1ca87, 0x504e7b20c23d1833, 0x40715b4cd720f7eb, 0xff0f802db1fc271, 0xf83f47347c86cbc, 0xca6621e2d2490ee5, 0x16b375f83be5a1d5, 0xa8b49cffad7ff1fa, 0xa940afebd2c4ffe5, 0xcc8018f5682d94df, 0x7a2410a982d9baa4, 0x5da8e98f26dce1c, 0xd5317d7aedada994, 0x43d843c4e6e743a2, 0x4d9f1490f6b822fe, 0x834e8ce7c9c95fcb, 0xb50eae605603a8e0]

private theorem rounds028_2 : sixRounds 12 (by decide) quarter028_2 = quarter028_3 := by
  decide +kernel

private theorem rounds028_3 : sixRounds 18 (by decide) quarter028_3 = state029 := by
  decide +kernel

private theorem perm028 : KECCAK.f1600 absorbed028 = state029 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds028_0, rounds028_1, rounds028_2, rounds028_3]
  rfl

theorem block028 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes028 ++ tail) state028 =
      KECCAK.Bytes.run 0 tail state029 := by
  exact run_block_of_step bytes028 tail absorb028 state028 absorbed028
    state029 (fun _ => rfl) words028 perm028

private def absorb029 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x51 0x90 0x52 0x1 0x82 0x44 0x60 0x0)) 1 (by decide) (UInt64.ofBytes 0x90 0x1 0x64 0x60 0x3 0x90 0x81 0x90)) 2 (by decide) (UInt64.ofBytes 0x52 0x81 0x81 0x0 0x60 0x33 0x5b 0xfd)) 3 (by decide) (UInt64.ofBytes 0x90 0x40 0x60 0x52 0x20 0x60 0x3 0x60)) 4 (by decide) (UInt64.ofBytes 0xf 0x61 0x15 0x16 0xff 0x60 0x54 0x20)) 5 (by decide) (UInt64.ofBytes 0xc3 0x8 0x7f 0x51 0x40 0x60 0x57 0x68)) 6 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0xa0 0x79)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 8 (by decide) (UInt64.ofBytes 0x0 0x0 0x0 0x0 0x0 0x0 0x0 0x0)) 9 (by decide) (UInt64.ofBytes 0x52 0x81 0x0 0x0 0x0 0x0 0x0 0x0)) 10 (by decide) (UInt64.ofBytes 0x1 0x20 0x60 0x80 0x80 0x1 0x4 0x60)) 11 (by decide) (UInt64.ofBytes 0x81 0x25 0x60 0x52 0x82 0x3 0x81 0x82)) 12 (by decide) (UInt64.ofBytes 0x47 0x53 0x61 0x80 0x1 0x20 0x60 0x52)) 13 (by decide) (UInt64.ofBytes 0x91 0x1 0x40 0x60 0x39 0x91 0x25 0x60)) 14 (by decide) (UInt64.ofBytes 0x3 0x91 0x80 0x51 0x40 0x60 0x50 0x50)) 15 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0x73 0x5b 0xfd 0x90)) 16 (by decide) (UInt64.ofBytes 0xff 0xff 0xff 0xff 0xff 0xff 0xff 0xff))

private def absorbed029 : Vector UInt64 25 :=
  #v[0xfa6d1ce4020a0cfc, 0x7a9749649013c981, 0x1e3e7f1e417ea3ee, 0xb3b636d8cd4f7552, 0x8da481f45357d24f, 0xd303d65f3bf7081c, 0xfada6a8083a2dc9d, 0xbf046ff23d5229ca, 0xb838439ea07f8111, 0xf134ccf214f278ef, 0x1c4833c1978bcfe1, 0xcc4be3ffc74b5877, 0x98c1ba841d4ca0a4, 0xedffd65c5f1f1b9d, 0x4e6a22f52a71503f, 0x61ceb70862c73268, 0x1e7b8f9d4ff94b56, 0xfb0d16850406bfe9, 0x29b5b3cb81eaf1cf, 0x1ff674bd62428013, 0x126963b9dc9551b1, 0x41f5cda5ccd8e4e6, 0x1a3ec4a094c3fdfd, 0x86a9fce368ac550c, 0x3aa350b84f037f4]

private theorem words029 : absorb029 state029 = absorbed029 := by
  decide +kernel

private def quarter029_1 : Vector UInt64 25 :=
  #v[0xab85ba9856a3b145, 0xe26eb0e2c3624eaf, 0x6b202fc87472fe04, 0x69084aa527bb4b70, 0xfd284a74452f68c7, 0xb1d3e1de44ba9c2f, 0xb28bd3dbd134b503, 0xc8d86e80d7764ad8, 0xb21bd2796b88eafa, 0xa8a76eeae6e6a607, 0x20bb1fa635b12278, 0x430d2b7b0f99ab05, 0x73d6067e97653af0, 0xe78eb1c4058293e7, 0xd067811b78776693, 0x5c367c3bd9e3d297, 0x8369e4d2ce4a54d4, 0x9521d604daf5771d, 0x7d7ebfe6098ad4f4, 0x90662454129b2408, 0x81366fb744aaa1c8, 0xd50d4b9dde67e261, 0xb74bd0babdb5f8c5, 0xae43b85cc30370ea, 0xdab48f67e7f5c093]

private theorem rounds029_0 : sixRounds 0 (by decide) absorbed029 = quarter029_1 := by
  decide +kernel

private def quarter029_2 : Vector UInt64 25 :=
  #v[0x4e6743a095c53359, 0xccdd4cdd58329e3e, 0xe5d5f64658bea67b, 0x221dc1d9c4a880ab, 0x3693f29ecdb4c3f, 0xf99029e1ab2aa212, 0xb6eb062e3d1a1515, 0x68ff1818c3509ef5, 0x9dd0622c0ad002d7, 0xd9983d2b2957c22b, 0x5e1fbc711200adc0, 0x2801510e8c44562f, 0x12d09a283ec829b7, 0x5ab5bef75f29d347, 0xe7c119fa37663d90, 0xf80cd919829a96c1, 0x71782894b7e061ee, 0xec41e7a9acd107d8, 0xa83d43ec6a63eef5, 0x86d4e6280832b520, 0x1d7f4fe915ab5c04, 0xb97de8885ad73fab, 0xded5421170aea2b2, 0x6eb6da9edfd3143d, 0x97730b32b5a850ec]

private theorem rounds029_1 : sixRounds 6 (by decide) quarter029_1 = quarter029_2 := by
  decide +kernel

private def quarter029_3 : Vector UInt64 25 :=
  #v[0xa1e926c11c8e9bd8, 0x4700dc164000c5ae, 0xbaea8f7780f78cb2, 0x7e4fe0a1eaa34b8f, 0x499dae7405e52983, 0x2160298960f03fd5, 0x5608604779e0c7a9, 0x735c0644a6df00fd, 0x5ac610a0fc53ae3c, 0x6e3cc66977b7a604, 0x2653bdd1595edaf3, 0x2fa58d9c7468e024, 0x478c7afcbecaf81e, 0x2f0e44546779067d, 0x198f154ef15d4ec, 0x78d7ec29abd653b, 0x8bf38f5adbad77db, 0x7b7fed000cf1d78e, 0xb150dbcf66381e32, 0x6d3cf02d8a896705, 0x8111b848eab5117c, 0x7f6c2e7d0053d07e, 0x6be57ac28f74dd49, 0x68ddcf54942594f5, 0x1e30764d6181f7ca]

private theorem rounds029_2 : sixRounds 12 (by decide) quarter029_2 = quarter029_3 := by
  decide +kernel

private theorem rounds029_3 : sixRounds 18 (by decide) quarter029_3 = state030 := by
  decide +kernel

private theorem perm029 : KECCAK.f1600 absorbed029 = state030 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds029_0, rounds029_1, rounds029_2, rounds029_3]
  rfl

theorem block029 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes029 ++ tail) state029 =
      KECCAK.Bytes.run 0 tail state030 := by
  exact run_block_of_step bytes029 tail absorb029 state029 absorbed029
    state030 (fun _ => rfl) words029 perm029

end Blanc.Lift.Usdc.ImplV2_1Creation.SigningBlocks
