import Blanc.Lift.Usdc.ImplV2_2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2_2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2_2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb168 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x65 0x6e 0x20 0x3a 0x6e 0x65 0x6b 0x6f)) 1 (by decide) (UInt64.ofBytes 0x72 0x65 0x74 0x73 0x61 0x6d 0x20 0x77)) 2 (by decide) (UInt64.ofBytes 0x69 0x20 0x72 0x65 0x74 0x6e 0x69 0x4d)) 3 (by decide) (UInt64.ofBytes 0x65 0x7a 0x20 0x65 0x68 0x74 0x20 0x73)) 4 (by decide) (UInt64.ofBytes 0x65 0x72 0x64 0x64 0x61 0x20 0x6f 0x72)) 5 (by decide) (UInt64.ofBytes 0x61 0x75 0x63 0x73 0x65 0x52 0x73 0x73)) 6 (by decide) (UInt64.ofBytes 0x6c 0x61 0x63 0x20 0x3a 0x65 0x6c 0x62)) 7 (by decide) (UInt64.ofBytes 0x6e 0x20 0x73 0x69 0x20 0x72 0x65 0x6c)) 8 (by decide) (UInt64.ofBytes 0x72 0x20 0x65 0x68 0x74 0x20 0x74 0x6f)) 9 (by decide) (UInt64.ofBytes 0x52 0x45 0x72 0x65 0x75 0x63 0x73 0x65)) 10 (by decide) (UInt64.ofBytes 0x61 0x72 0x74 0x20 0x3a 0x30 0x32 0x43)) 11 (by decide) (UInt64.ofBytes 0x6d 0x61 0x20 0x72 0x65 0x66 0x73 0x6e)) 12 (by decide) (UInt64.ofBytes 0x63 0x78 0x65 0x20 0x74 0x6e 0x75 0x6f)) 13 (by decide) (UInt64.ofBytes 0x6c 0x6c 0x61 0x20 0x73 0x64 0x65 0x65)) 14 (by decide) (UInt64.ofBytes 0x69 0x46 0x65 0x63 0x6e 0x61 0x77 0x6f)) 15 (by decide) (UInt64.ofBytes 0x3a 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61)) 16 (by decide) (UInt64.ofBytes 0x61 0x6c 0x62 0x20 0x77 0x65 0x6e 0x20))

private def absorbed168 : Vector UInt64 25 :=
  #v[0x2580c5d5a1894b2f, 0x330eac2ae1d2f7df, 0xaf63759db7d4ca09, 0x4a97cebc81f4d805, 0x970f21a8bb790cb1, 0xd484d04484d613e, 0xab9561bd76ed7a0b, 0xe52c791a1dead307, 0x539d93c38f279fef, 0x88e2e76f7a4a1175, 0x4ac8d6f6c3d7d0e, 0x4d94b11d94d1fb89, 0x317a02a5fde1f17b, 0xbfb9184aec634be9, 0xb564e891b47d6c78, 0xef9983e452876798, 0xd88f2977d8acbda3, 0x658380cce6db97e6, 0x533896cb5c379a4e, 0x5bb041a1459e3e4c, 0x2b680b830dad53b6, 0x51fc473c8f2678d7, 0x5155060cd806944c, 0x795ecabe0cab112c, 0xcc0c6d835009641d]

private theorem words168 : absorb168 state168 = absorbed168 := by
  decide +kernel

private def quarter168_1 : Vector UInt64 25 :=
  #v[0x38928b0ad82d9f3a, 0xcce11c1015c7af0d, 0xb799a1dd6f07f6e, 0xb9e72becc031ddca, 0x4707ff0b47461986, 0xc7ef7a316e6dd36b, 0x2b3f1718217a7bad, 0x7bcfe1660badd87c, 0xd9325ea7d3378d50, 0xcf001d914293cad1, 0x90b0a5f3c2fd01af, 0xc7c5c24fddccddf9, 0xbcb182c35b153abf, 0x4e7bc74fdc34775a, 0xde290c5ecc00f70f, 0x9e4e6e8ab18d9d49, 0x34e2db3d18b1e908, 0xf48e72c9a5360dde, 0x1882abd9d6cbc16d, 0x4b58b9bda62ce191, 0x88475966b75953f8, 0x49ffb89eaf7f62f1, 0x18b7a51cf15a0d65, 0x66c73e3de8b7b9d4, 0xde55276cb769dcc8]

private theorem rounds168_0 : sixRounds 0 (by decide) absorbed168 = quarter168_1 := by
  decide +kernel

private def quarter168_2 : Vector UInt64 25 :=
  #v[0x2d2653670f6a3eb2, 0x89c6f626dab929fb, 0x27bbfa6ecd20ca7d, 0x3f0efdea5e8ec270, 0xf908264a2305abf1, 0x4f6ed9a344c9fb76, 0x5c3cf14863002bf4, 0x1ad64b9447285384, 0x4256fc1ee6d65ec8, 0xbf747076446a3b67, 0xfd3ca1476b821ed, 0x2fb35b9b51560c2b, 0xbe1fe3fec98095cb, 0xcc9c2fcb59b4dc59, 0x7d492913a8f36fc7, 0x2f9664183cbd9c10, 0xd459c47145820aa5, 0x966790b181381246, 0x3797519914ad45ad, 0x2d792342467ac01, 0x4bddc642361e6da, 0xa6437180e364882d, 0x3eca59b7cb167026, 0x34c9d4bf8f0b2b46, 0x1e5829d74d84ad7c]

private theorem rounds168_1 : sixRounds 6 (by decide) quarter168_1 = quarter168_2 := by
  decide +kernel

private def quarter168_3 : Vector UInt64 25 :=
  #v[0x69bd143a56423f3a, 0x6ca41bfcf0f6dd2e, 0x73674d28fdd16ad7, 0xd4cda3fbf3263ab1, 0x285e5807e0e502cd, 0x67567bf3a1801ea1, 0xf3339b3955f7e0b5, 0xf0d6fb95931ed6cb, 0x67774e1d4ba0f635, 0xc3d1e68872807218, 0x6b8041597f21a294, 0x75e303004ad7a8c3, 0xf7800b197d3a0af0, 0xc2aada8f078a415, 0xb4d128a90c429198, 0x91880f66e067d909, 0x457379042c4bf322, 0x1892658662ae4c72, 0xecb8f4d00b853d9d, 0x5ae5851fc84e0885, 0x683f4117553c94d0, 0x2a1e6eff7094914, 0xc11a402b40ac6be4, 0xe487697167bad70e, 0xcad552ca0d8f2658]

private theorem rounds168_2 : sixRounds 12 (by decide) quarter168_2 = quarter168_3 := by
  decide +kernel

private theorem rounds168_3 : sixRounds 18 (by decide) quarter168_3 = state169 := by
  decide +kernel

private theorem perm168 : KECCAK.f1600 absorbed168 = state169 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds168_0, rounds168_1, rounds168_2, rounds168_3]
  rfl

private def absorb169 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x72 0x65 0x74 0x73 0x69 0x6c 0x6b 0x63)) 1 (by decide) (UInt64.ofBytes 0x20 0x65 0x68 0x74 0x20 0x73 0x69 0x20)) 2 (by decide) (UInt64.ofBytes 0x64 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a)) 3 (by decide) (UInt64.ofBytes 0x74 0x61 0x69 0x46 0x73 0x73 0x65 0x72)) 4 (by decide) (UInt64.ofBytes 0x3a 0x32 0x56 0x6e 0x65 0x6b 0x6f 0x54)) 5 (by decide) (UInt64.ofBytes 0x20 0x72 0x65 0x6c 0x6c 0x61 0x63 0x20)) 6 (by decide) (UInt64.ofBytes 0x20 0x65 0x62 0x20 0x74 0x73 0x75 0x6d)) 7 (by decide) (UInt64.ofBytes 0x65 0x79 0x61 0x70 0x20 0x65 0x68 0x74)) 8 (by decide) (UInt64.ofBytes 0x6b 0x6f 0x54 0x74 0x61 0x69 0x46 0x65)) 9 (by decide) (UInt64.ofBytes 0x74 0x6e 0x6f 0x63 0x20 0x3a 0x6e 0x65)) 10 (by decide) (UInt64.ofBytes 0x20 0x73 0x69 0x20 0x74 0x63 0x61 0x72)) 11 (by decide) (UInt64.ofBytes 0x20 0x79 0x64 0x61 0x65 0x72 0x6c 0x61)) 12 (by decide) (UInt64.ofBytes 0x69 0x6c 0x61 0x69 0x74 0x69 0x6e 0x69)) 13 (by decide) (UInt64.ofBytes 0x30 0x32 0x43 0x52 0x45 0x64 0x65 0x7a)) 14 (by decide) (UInt64.ofBytes 0x66 0x73 0x6e 0x61 0x72 0x74 0x20 0x3a)) 15 (by decide) (UInt64.ofBytes 0x20 0x6d 0x6f 0x72 0x66 0x20 0x72 0x65)) 16 (by decide) (UInt64.ofBytes 0x6f 0x72 0x65 0x7a 0x20 0x65 0x68 0x74))

private def absorbed169 : Vector UInt64 25 :=
  #v[0x4c73f77456cb71b9, 0x7d2883b3e1c12dd, 0x60935dab48873c1f, 0x5c79673bff2511e1, 0x513d24a339fd90e2, 0x1780314445bbea35, 0x2d08630811cf4483, 0x5d4c00195efe6265, 0x915af065a70b7c7f, 0xd3f62fcc5177eceb, 0xf5edb70914bccf9e, 0x3d39fc5404c714e3, 0x928dca49a6bdf274, 0x2f02dbe5bdb88400, 0xe3cbf31ff12b0911, 0xa129e3d0283e8285, 0x15e3efe73d9e046, 0x8c9d8b151c1c2721, 0xc5060c418a083438, 0xbce4633f553105c3, 0xe571c3c5132e5cd7, 0x92d7be2b6d9b4243, 0x5f3657aa59bf75c0, 0x8814732efdf6e17f, 0xa535286215ea98a7]

private theorem words169 : absorb169 state169 = absorbed169 := by
  decide +kernel

private def quarter169_1 : Vector UInt64 25 :=
  #v[0xa4d166e41781359b, 0x9308c571fff1acd5, 0xcceb53df768e60a5, 0xd1e6f5731b7c177a, 0x2d1837f55e9420ae, 0x7bbc172d1325bca7, 0x85f8fc10b550f8b9, 0x8576c8c3147abe34, 0x391668df5206017, 0x4635b7b3e89e1fd4, 0xe5a904d824bf9d07, 0xaa3c580f45bfb74b, 0xf5b650a9276510de, 0x907f6e163727870, 0x5e2c467d302205c6, 0xa1140d82c0b3cf9a, 0x1e3d2ae7143ade9, 0x5dc840db0a703371, 0x1e4c7254a9c847e1, 0x1be000bde7eba4a1, 0xb29859c28c4c9cd, 0x900f3fe5b29ab205, 0x7bcc476c6a7b882f, 0xb3f1fc022c6e8a08, 0x450b4bcbaff191db]

private theorem rounds169_0 : sixRounds 0 (by decide) absorbed169 = quarter169_1 := by
  decide +kernel

private def quarter169_2 : Vector UInt64 25 :=
  #v[0x988d3a72a1718fd, 0xec1b0ab368eb9ea4, 0xa7fa3e00bd40dbe, 0x6aae010c09ff51c, 0x44dca54646d2481a, 0x119cc2c1c6efc378, 0x74145e290fe27867, 0x61efaf9da109a727, 0xb7d794ab9c05520d, 0x5d9cccb2b848e571, 0x45023f358c63d2e, 0xf957163eed163ef3, 0x7f240a819b27e7b3, 0x792409615f147628, 0xca1e41eefbb80743, 0xc07135a67f05eec2, 0xd75afa6392ee27d6, 0x2c15d46c303b75db, 0xb86047f0078c9ce8, 0xc75edd5963abfd6b, 0x5fefaff11cdc27a2, 0x74589a0082ca5da5, 0x5703f2e6a7eb1d63, 0x7a36d480c80d0ccf, 0xdf30a61fbf06a3ed]

private theorem rounds169_1 : sixRounds 6 (by decide) quarter169_1 = quarter169_2 := by
  decide +kernel

private def quarter169_3 : Vector UInt64 25 :=
  #v[0x11b1bb645c30e853, 0xc277dd87ac1a2b75, 0x7e3345431e185e9f, 0x6d31d47644fdd26c, 0x7676eecd8b6e36c5, 0xf4dac101b787e0ec, 0x3471a4ec2131c506, 0x34e9abf9385f01e7, 0x777fefc6bfc945f, 0xdbc387b18bf6cdcc, 0x39405dcd3edb1cb2, 0xdc7add2c171457b9, 0xb8f4822ecd788dc6, 0x88af928fb9623ed3, 0xc6f8ea06db59fcc, 0x283bc9d56fa69da9, 0x6f2b69a765f01d1f, 0x3801daac8073ef0e, 0xf1a2aa9565b68095, 0x153a5e199d444a54, 0x56e5d0f5b96d71a1, 0xd2dfd85a4714bc38, 0x5165742de9694b11, 0x26e1906230d275a9, 0x82e7795973f2029e]

private theorem rounds169_2 : sixRounds 12 (by decide) quarter169_2 = quarter169_3 := by
  decide +kernel

private theorem rounds169_3 : sixRounds 18 (by decide) quarter169_3 = state170 := by
  decide +kernel

private theorem perm169 : KECCAK.f1600 absorbed169 = state170 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds169_0, rounds169_1, rounds169_2, rounds169_3]
  rfl

private def absorb170 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x73 0x73 0x65 0x72 0x64 0x64 0x61 0x20)) 1 (by decide) (UInt64.ofBytes 0x61 0x20 0x3a 0x30 0x32 0x43 0x52 0x45)) 2 (by decide) (UInt64.ofBytes 0x66 0x20 0x65 0x76 0x6f 0x72 0x70 0x70)) 3 (by decide) (UInt64.ofBytes 0x20 0x65 0x68 0x74 0x20 0x6d 0x6f 0x72)) 4 (by decide) (UInt64.ofBytes 0x64 0x64 0x61 0x20 0x6f 0x72 0x65 0x7a)) 5 (by decide) (UInt64.ofBytes 0x74 0x61 0x69 0x46 0x73 0x73 0x65 0x72)) 6 (by decide) (UInt64.ofBytes 0x6d 0x20 0x3a 0x6e 0x65 0x6b 0x6f 0x54)) 7 (by decide) (UInt64.ofBytes 0x75 0x6f 0x6d 0x61 0x20 0x74 0x6e 0x69)) 8 (by decide) (UInt64.ofBytes 0x65 0x65 0x63 0x78 0x65 0x20 0x74 0x6e)) 9 (by decide) (UInt64.ofBytes 0x65 0x74 0x6e 0x69 0x6d 0x20 0x73 0x64)) 10 (by decide) (UInt64.ofBytes 0x6e 0x61 0x77 0x6f 0x6c 0x6c 0x41 0x72)) 11 (by decide) (UInt64.ofBytes 0x62 0x61 0x73 0x75 0x61 0x50 0x65 0x63)) 12 (by decide) (UInt64.ofBytes 0x6c 0x6c 0x61 0x63 0x20 0x3a 0x65 0x6c)) 13 (by decide) (UInt64.ofBytes 0x6f 0x6e 0x20 0x73 0x69 0x20 0x72 0x65)) 14 (by decide) (UInt64.ofBytes 0x61 0x70 0x20 0x65 0x68 0x74 0x20 0x74)) 15 (by decide) (UInt64.ofBytes 0x65 0x66 0x61 0x53 0x72 0x65 0x73 0x75)) 16 (by decide) (UInt64.ofBytes 0x45 0x20 0x3a 0x30 0x32 0x43 0x52 0x45))

private def absorbed170 : Vector UInt64 25 :=
  #v[0xe05ee594d797c429, 0x9b6fcde2120e30a5, 0x4ccd89d1fb16b1c3, 0x40eaa617403fd40a, 0x2ea679200979512b, 0x867bf528f520994a, 0x67795955007339bd, 0xb7c65b8ef83e8fbe, 0xadf72404c585db15, 0xa445577d2d841454, 0x18dbe77e155d911e, 0x4dea246ee4c19a38, 0x5c21f08d632d3df1, 0x1425371581ee201c, 0x70fe7e2d5a4b52ad, 0x90c1e0d7a74f448e, 0x17757ed6983068e8, 0xb2b84cc47c41d3c5, 0x6ef2e9e684b18a24, 0x2c93387b4b26c371, 0x755fac4c43fc93d0, 0xdd8f8eec5a370f71, 0x4594f1be4086aea7, 0x74bffee76b5d71ac, 0xd94369a7c18c762c]

private theorem words170 : absorb170 state170 = absorbed170 := by
  decide +kernel

private def quarter170_1 : Vector UInt64 25 :=
  #v[0xff639fef2de79394, 0x4722cf694d9dc96d, 0x689e75e9be6b9cb3, 0x12aac97c7aed94d2, 0x959e2813f28df4c0, 0x8582f6aa0c720f67, 0x1d28d874bd8a5a13, 0xb9517fe80b2ab38b, 0x4469bf54e6621f9f, 0x3eb4db37dea7432f, 0x996f892c4d2d4815, 0x57f1884a16d87a15, 0x530cce095b9f1cc2, 0xd3b7d08dad084963, 0xb9ccc20a1bc6f2a8, 0x65c56141fb48946b, 0x855983d6d8d828be, 0xa55bcebd126d4700, 0xcf97e23c6d537ada, 0xc5467a09132422f6, 0x804ac5771b332b75, 0xb45cd8522560c3d5, 0xa1eab8d9cb727b1e, 0xc240e28c44405546, 0x97f812cdc8057a98]

private theorem rounds170_0 : sixRounds 0 (by decide) absorbed170 = quarter170_1 := by
  decide +kernel

private def quarter170_2 : Vector UInt64 25 :=
  #v[0xf31863dd02ad4a, 0x54fdf7d43665019a, 0x62a3ad1af53b8b7e, 0x2d56e1f4bd4d729a, 0xbe68a8176c5819db, 0x9c8c6a1e8d340136, 0xfab84f3827359e34, 0xc2b39cf52c3e04a3, 0x6272683cbb2fdd10, 0x90acc376b63c50bb, 0x1e7f5c58f58db816, 0xfcc43fa6493d1e18, 0x9211b91c74188ec8, 0xc160d7b1e677d6b2, 0xd1edbedc5d000587, 0x9056aecf7029fb68, 0x7cfae097bae56bca, 0x755571ff330d9720, 0x17b288b465eb4433, 0xa71250913aa00a2d, 0x8d8284488ee45e8, 0x16d16c5d198053ec, 0x48c79d7b0085a7dc, 0x928ce7ee98ab5a2f, 0xdde25e48ba65a814]

private theorem rounds170_1 : sixRounds 6 (by decide) quarter170_1 = quarter170_2 := by
  decide +kernel

private def quarter170_3 : Vector UInt64 25 :=
  #v[0x9c68fe21c4a1cd71, 0x6dd433e2d1a2b68, 0x59a2babeede060d5, 0xf9bcb65f62a3d849, 0xadb86032ba49f1dd, 0x1549d339ed047e4a, 0x492cdc86b2fc5d85, 0xaf372ac21009ed65, 0xa81757a2b053d832, 0xc926909378c4c2eb, 0x4bfc0ed7289c9633, 0x32cbac63b73f91a0, 0x9fb80277eea50890, 0x1b9ad776eb91ed5f, 0xb311de40d395fb00, 0xc6e35397e600acde, 0xaa8a6ebfcda2eb7b, 0xd901fda92254e5a1, 0xfdc7b4a720f08ac9, 0x3bd36314fd9ef65, 0xf103b55e7fa00713, 0xda2acf2c0050e767, 0xc81d3f5550ba944e, 0xb74ba4f81f6a34de, 0x1fcf8799f7a48f92]

private theorem rounds170_2 : sixRounds 12 (by decide) quarter170_2 = quarter170_3 := by
  decide +kernel

private theorem rounds170_3 : sixRounds 18 (by decide) quarter170_3 = state171 := by
  decide +kernel

private theorem perm170 : KECCAK.f1600 absorbed170 = state171 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds170_0, rounds170_1, rounds170_2, rounds170_3]
  rfl

private def absorb171 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x65 0x70 0x6f 0x20 0x30 0x32 0x43 0x52)) 1 (by decide) (UInt64.ofBytes 0x64 0x20 0x6e 0x6f 0x69 0x74 0x61 0x72)) 2 (by decide) (UInt64.ofBytes 0x73 0x20 0x74 0x6f 0x6e 0x20 0x64 0x69)) 3 (by decide) (UInt64.ofBytes 0x69 0x46 0x64 0x65 0x65 0x63 0x63 0x75)) 4 (by decide) (UInt64.ofBytes 0x3a 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61)) 5 (by decide) (UInt64.ofBytes 0x6e 0x77 0x6f 0x20 0x77 0x65 0x6e 0x20)) 6 (by decide) (UInt64.ofBytes 0x68 0x74 0x20 0x73 0x69 0x20 0x72 0x65)) 7 (by decide) (UInt64.ofBytes 0x61 0x20 0x6f 0x72 0x65 0x7a 0x20 0x65)) 8 (by decide) (UInt64.ofBytes 0x69 0x46 0x73 0x73 0x65 0x72 0x64 0x64)) 9 (by decide) (UInt64.ofBytes 0x56 0x6e 0x65 0x6b 0x6f 0x54 0x74 0x61)) 10 (by decide) (UInt64.ofBytes 0x6f 0x68 0x74 0x75 0x61 0x20 0x3a 0x32)) 11 (by decide) (UInt64.ofBytes 0x6e 0x6f 0x69 0x74 0x61 0x7a 0x69 0x72)) 12 (by decide) (UInt64.ofBytes 0x64 0x65 0x73 0x75 0x20 0x73 0x69 0x20)) 13 (by decide) (UInt64.ofBytes 0x63 0x6e 0x61 0x63 0x20 0x72 0x6f 0x20)) 14 (by decide) (UInt64.ofBytes 0x63 0x61 0x6c 0x42 0x64 0x65 0x6c 0x65)) 15 (by decide) (UInt64.ofBytes 0x6c 0x62 0x61 0x74 0x73 0x69 0x6c 0x6b)) 16 (by decide) (UInt64.ofBytes 0x62 0x20 0x77 0x65 0x6e 0x20 0x3a 0x65))

private def absorbed171 : Vector UInt64 25 :=
  #v[0xfbfd73a09368781d, 0xf283b8835b45ed6a, 0x4007ce722e725e74, 0x44f19071ac511ce5, 0x3256348cb1bce87b, 0x934582fbf4af4635, 0xb38b97e9dc5544e, 0x50b8fa861b975047, 0x1f279999f0077984, 0x57bef529305142d2, 0x587db47fc5a47341, 0xcec58cb2df33d3fc, 0xc4f48ad367a5c1b2, 0x746cbc64480e5700, 0x4ca48157bd7c2a8a, 0x755a2cde98da08d4, 0xc6b3fe20e63be2c7, 0xf7033e2cc0adabf0, 0x6e50ae65a992e2b4, 0xd04688fe4920ba93, 0x1cdb5bec73c53cd3, 0x5ae734532764c265, 0xe75eecddfa1568d6, 0xd5c26a5875aef3b4, 0x102912c98b6b1eea]

private theorem words171 : absorb171 state171 = absorbed171 := by
  decide +kernel

private def quarter171_1 : Vector UInt64 25 :=
  #v[0x35cffe2e1acfb71f, 0xbca3663213705145, 0x5437251aba3d3581, 0x8cd6d96b3f83c6d7, 0x3d10f746b663483c, 0x592286632c86cdf, 0x3fe34edd2bfef884, 0x6d0b8929721f3d51, 0x40924d5385bf3d63, 0xd69826d31f4af543, 0x75c90d54d30327cb, 0x928f6362940e8c96, 0xcde06d48e277686f, 0xd8ec5f273de72f62, 0x7a3bacc9a70bf14e, 0xf5c12d7ee17ae615, 0x675586c61269d3fd, 0x24efa35a9ca35460, 0x4b48e11a03983fc1, 0x8edb45592c54a30c, 0x5ba95c2e61bbff48, 0x91db413862fd4cc5, 0xe9c34be8b1ce7886, 0xaec8c831a90e37a8, 0x1eae2678357ab492]

private theorem rounds171_0 : sixRounds 0 (by decide) absorbed171 = quarter171_1 := by
  decide +kernel

private def quarter171_2 : Vector UInt64 25 :=
  #v[0x389119eed9649dbd, 0x3d419d72b913cd56, 0xf457ae7b0e2c3878, 0xabfe8510d88c30ce, 0x7e27c548bde00d8, 0x4f622b7873f4e807, 0x70aa79bf6b40ce55, 0xb77cd816e27f6a03, 0xfd2060727a761ef8, 0xebf04215efb0cdf2, 0x8bef47c69d053e81, 0xbd73a9594845e55e, 0xf357a27c8dc581fe, 0xa34d262c805261e6, 0xf196b1bc45649894, 0xb39a8645acefe151, 0xa391b2a839e3f294, 0x2a659f730f1b1834, 0xe01b1f908ee11df6, 0x7b0f6cf8199454c0, 0x9122d6c2deccf684, 0x1d9a4d41167a341e, 0x487a3f89e064bdda, 0x2bb03860996c3e29, 0x86707a931e69c7de]

private theorem rounds171_1 : sixRounds 6 (by decide) quarter171_1 = quarter171_2 := by
  decide +kernel

private def quarter171_3 : Vector UInt64 25 :=
  #v[0xa1c07c1211dc1990, 0x8d9b2753ed52ba89, 0x53c8fe8ad67142ae, 0x54848abb40d9e4c6, 0xbe0096a92f8e179, 0x1d1f24081c43424, 0xbc38b03e50ff8a75, 0xb300b0a1d1e424b5, 0x54e83b867849884a, 0x957e7ff8ccaae1f, 0x1e94be378715a555, 0xf459d9d3900f49f9, 0x2771e90ac2c649c, 0xfe62f40cbbc4d97d, 0xa4acc59cfc16d362, 0x8cf3fdc149583cee, 0x76ff0adbcdae2298, 0xc771cd39764cf570, 0xe81c0d4e87e977, 0x636ad658113d95b8, 0x49a8760c5dd63ccf, 0xed8776cb59fd4717, 0x61fbeec8dfe01ce2, 0xc43d87877c9b1159, 0x367362a7e1f56580]

private theorem rounds171_2 : sixRounds 12 (by decide) quarter171_2 = quarter171_3 := by
  decide +kernel

private theorem rounds171_3 : sixRounds 18 (by decide) quarter171_3 = state172 := by
  decide +kernel

private theorem perm171 : KECCAK.f1600 absorbed171 = state172 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds171_0, rounds171_1, rounds171_2, rounds171_3]
  rfl

private def absorb172 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x74 0x73 0x69 0x6c 0x6b 0x63 0x61 0x6c)) 1 (by decide) (UInt64.ofBytes 0x68 0x74 0x20 0x73 0x69 0x20 0x72 0x65)) 2 (by decide) (UInt64.ofBytes 0x61 0x20 0x6f 0x72 0x65 0x7a 0x20 0x65)) 3 (by decide) (UInt64.ofBytes 0x6c 0x42 0x73 0x73 0x65 0x72 0x64 0x64)) 4 (by decide) (UInt64.ofBytes 0x61 0x74 0x73 0x69 0x6c 0x6b 0x63 0x61)) 5 (by decide) (UInt64.ofBytes 0x63 0x63 0x61 0x20 0x3a 0x65 0x6c 0x62)) 6 (by decide) (UInt64.ofBytes 0x20 0x73 0x69 0x20 0x74 0x6e 0x75 0x6f)) 7 (by decide) (UInt64.ofBytes 0x73 0x69 0x6c 0x6b 0x63 0x61 0x6c 0x62)) 8 (by decide) (UInt64.ofBytes 0x54 0x74 0x61 0x69 0x46 0x64 0x65 0x74)) 9 (by decide) (UInt64.ofBytes 0x20 0x3a 0x32 0x56 0x6e 0x65 0x6b 0x6f)) 10 (by decide) (UInt64.ofBytes 0x7a 0x69 0x72 0x6f 0x68 0x74 0x75 0x61)) 11 (by decide) (UInt64.ofBytes 0x73 0x69 0x20 0x6e 0x6f 0x69 0x74 0x61)) 12 (by decide) (UInt64.ofBytes 0x64 0x65 0x72 0x69 0x70 0x78 0x65 0x20)) 13 (by decide) (UInt64.ofBytes 0x64 0x20 0x3a 0x30 0x32 0x43 0x52 0x45)) 14 (by decide) (UInt64.ofBytes 0x64 0x65 0x73 0x61 0x65 0x72 0x63 0x65)) 15 (by decide) (UInt64.ofBytes 0x6e 0x61 0x77 0x6f 0x6c 0x6c 0x61 0x20)) 16 (by decide) (UInt64.ofBytes 0x77 0x6f 0x6c 0x65 0x62 0x20 0x65 0x63))

private def absorbed172 : Vector UInt64 25 :=
  #v[0xbfb5d83a80e5ae5a, 0x78d9400a26a3cd59, 0x91d721379d80cece, 0xda695defe3ab7a47, 0x81c841cdb315a666, 0xbef15a565b8bf386, 0x9c0839795209c5f, 0x1d3f1c35e76a417d, 0x855735f9f4c8a340, 0x7cee84a07334ab45, 0x7d34446f8c2adee0, 0x2c53d82ee4428d59, 0xc8fc00a4f854f59e, 0x8953224d13df3161, 0x19421b3f72a50b64, 0x5af9943f567b64cd, 0x50478a9ca40f237b, 0x791e8633ff0425d9, 0xc9748ac05173fecb, 0x2ddcad39b708ff48, 0x52a684385824caee, 0xceae792e74479919, 0x8679f283397262f5, 0x3f653f7459a6db4f, 0xc655e7071c231409]

private theorem words172 : absorb172 state172 = absorbed172 := by
  decide +kernel

private def quarter172_1 : Vector UInt64 25 :=
  #v[0x8e02619fe992acb1, 0xb7f36c71d37ad2f, 0x633a12d713197ed3, 0x219518cb2471ec09, 0x630391ef35cca67f, 0x73bc1874cfe65845, 0x23db957eebe34741, 0x4e4463fdcaeb44aa, 0xc62af60f8abc7510, 0xdd29d8e760dfbe5f, 0xd71c0457a66c655, 0x34d440b1e3868ab2, 0xa26060ed348cca97, 0xed09c5d2627d8ae3, 0x4f016ace8ba22c1a, 0xb1cd78ad148efa2, 0x2629772638d2794f, 0x2f42aeda4f094ce4, 0xc4bfd88d22ec542f, 0xee541cdbf84436fe, 0xdfa7dfa62a648f61, 0xc71921fb22ca901b, 0xfae2f49c3c034dc8, 0x7390ee779a29c6cc, 0xd23aeff5e5baa0a]

private theorem rounds172_0 : sixRounds 0 (by decide) absorbed172 = quarter172_1 := by
  decide +kernel

private def quarter172_2 : Vector UInt64 25 :=
  #v[0x4d4fa44501106d3c, 0x8418116f37c479e8, 0x508d4a44819bc05c, 0x3226ddf5ddca5e79, 0x36b040f4285392b1, 0xc52b8a9fdb5bf434, 0x34d9b457d258213d, 0xd5db08cc35fb6084, 0x16df06630c801c9f, 0x5824f84af02c8258, 0xad2802fe19ee266d, 0x63b2297f2e21c12c, 0xbd18032c87be7a69, 0x3876792d160b72b2, 0xb932105a5a1771ef, 0x4d42f0dcfba6e8dc, 0xe702af4a8e7cdbc3, 0x921726af3f873db3, 0xdeb742b5189b9da2, 0xde507f7841ff10ba, 0x1ae475ada4fa4389, 0x96cd9d63570e419f, 0x9860961af12bc05f, 0x5a9f4533655377a6, 0x93e1a36d56bf15d7]

private theorem rounds172_1 : sixRounds 6 (by decide) quarter172_1 = quarter172_2 := by
  decide +kernel

private def quarter172_3 : Vector UInt64 25 :=
  #v[0x7ff58632be23129e, 0x7c7f36a34ecc6393, 0x1fc5ad09f89dde13, 0x56feb5823444c14c, 0x3f51eb8651d4937c, 0x2747703d36473b65, 0xe9d1a178cd17caa3, 0xabb860539fcae103, 0xb2eade899021fc36, 0x13b331a6068a365e, 0xb972dfbef2650d36, 0xf9e30e676fd33ff, 0xabd7171fa24aa68d, 0x238caf709f6cdeb8, 0xa206ad6763e64196, 0x4f68f6adbe3d82b6, 0x6f806d448339c522, 0x5e644a5ce5f10f90, 0xd3e7a8b076181b75, 0x1baa7291edad4388, 0xb8b6892831b8a25, 0x56834b29762fbbf1, 0xa7b9bd86e98e3a83, 0x174ecd01f72cf147, 0x439a9569781534fa]

private theorem rounds172_2 : sixRounds 12 (by decide) quarter172_2 = quarter172_3 := by
  decide +kernel

private theorem rounds172_3 : sixRounds 18 (by decide) quarter172_3 = state173 := by
  decide +kernel

private theorem perm172 : KECCAK.f1600 absorbed172 = state173 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds172_0, rounds172_1, rounds172_2, rounds172_3]
  rfl

private def absorb173 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x69 0x64 0xa2 0x6f 0x72 0x65 0x7a 0x20)) 1 (by decide) (UInt64.ofBytes 0x5 0x20 0x12 0x22 0x58 0x73 0x66 0x70)) 2 (by decide) (UInt64.ofBytes 0xe0 0x49 0xb1 0xf4 0x19 0x39 0x7c 0x67)) 3 (by decide) (UInt64.ofBytes 0xb0 0x2f 0x9e 0xaa 0x3b 0x98 0xa5 0x65)) 4 (by decide) (UInt64.ofBytes 0x42 0x6 0xcd 0x3c 0x46 0xb5 0xca 0x99)) 5 (by decide) (UInt64.ofBytes 0x64 0xdf 0x9b 0x8d 0x2d 0xb3 0x70 0x9f)) 6 (by decide) (UInt64.ofBytes 0xc 0x6 0x0 0x43 0x63 0x6c 0x6f 0x73)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x1 0x80 0x80 0x1 0x33 0x0)) 16 (by decide) ((8 : UInt64) <<< 60))

private def absorbed173 : Vector UInt64 25 :=
  #v[0xe20535f806e6f675, 0xb3c3779107b200dc, 0x1a9edc4ca34bfa09, 0x1f044092b1130402, 0x7ea0dab315b1c404, 0x837ffe60a717efa6, 0x99b77497701da5b, 0x3747f37549ceb989, 0xd63d615a5383ef39, 0x9cf607da3822396e, 0xfb952373dbd975d, 0x56665c6b943b346a, 0xd10cd716c16aec8c, 0x3903ccffc7024f26, 0xbaf695045dac0efe, 0x44e7417c1145843b, 0xe6d5dab25912f636, 0x6a52ce2148f85043, 0x86ade37d013df16c, 0x4c356268e9f5d66, 0xb2de22b9819b454e, 0x60f30d801d56f11d, 0x7a60e5aa8b165505, 0x22b8e678b3dcf62d, 0x14664e6b29940d63]

private theorem words173 : absorb173 state173 = absorbed173 := by
  decide +kernel

private def quarter173_1 : Vector UInt64 25 :=
  #v[0x72c172fd3486a63, 0xcbcaf745d95882da, 0x5bda2b5ff3e01ae5, 0x16fa81dc6d9aef22, 0x1ce4ca782ec0b63, 0xf21369b65ef9483d, 0xbb676904337592d6, 0x6d616fc961a64c29, 0x2dfcaf0d630d043d, 0x95dcbac20f3dd14f, 0x729bf11954ce4f8b, 0xdd14f4c9eae5d3b0, 0x49cea62b49c9d95a, 0xa2d8afa31d54d958, 0x9a9d2ef2053e53a1, 0xea15e7de2fd47982, 0x193c329ee6ae3e93, 0x1bc2aae8f354ba8c, 0xdbb98989e3fd4d4d, 0x37644e9cad87323f, 0xe7c9d47e00aa4460, 0x5d476801bcd2eb67, 0x7b4fcee3075929cc, 0xfce495a60d85b855, 0x3305756b3daffaf9]

private theorem rounds173_0 : sixRounds 0 (by decide) absorbed173 = quarter173_1 := by
  decide +kernel

private def quarter173_2 : Vector UInt64 25 :=
  #v[0x93aad72bdabc3598, 0x206331ef707f551b, 0x83dcab7558960715, 0x106913718cf2e05, 0x457062617a316d2a, 0x705fa4fea695242b, 0xe69d76588c6ea408, 0x8f043fc1365207e7, 0xca619363e908f21, 0xfe925d496302eddb, 0xb562a0511af066cb, 0x99af21fa7037fa0f, 0xc44edaaa4602ff79, 0xda886141eed110f0, 0x73364e8ea1e92ff, 0xc0986501ffcf482a, 0x933f69bbc1c6a1f0, 0x453dfefa893f091a, 0x963be235bb528d8b, 0x1ed2a73760cbad3d, 0x3216401b169bee5e, 0xfcddabbaa822be6b, 0x108ddf611479888b, 0x9aa9fa23f2d2f9d7, 0x8e83ae8511cb54e3]

private theorem rounds173_1 : sixRounds 6 (by decide) quarter173_1 = quarter173_2 := by
  decide +kernel

private def quarter173_3 : Vector UInt64 25 :=
  #v[0xf008eac70924aa94, 0x51780ffdaf188e1e, 0x46017e700a7c6dfd, 0x2976491ed7432296, 0xa7a9118efa36f894, 0x29b1edb68ea224c4, 0xe761def69c05efdc, 0x3e28b6775e562ba0, 0xfcfc711978efd2f8, 0xc7c8475a82038659, 0xd41131f197745593, 0x78d403183a943556, 0xfaacfbc5318ab989, 0x66c50ec815a31e48, 0xa3e45d4fed9f0938, 0xa57ecd5a00e6af1e, 0x89a30227d8d4ed48, 0xf33eaa0034aa1412, 0x4c3f78a61886fd39, 0xa5c9fee46a8ab8e, 0xd865def76e4d8678, 0x9843233edd9a4df5, 0xd604a84894e3888b, 0xb600a185712b16f2, 0x12b405cdeffadaaf]

private theorem rounds173_2 : sixRounds 12 (by decide) quarter173_2 = quarter173_3 := by
  decide +kernel

private theorem rounds173_3 : sixRounds 18 (by decide) quarter173_3 = state174 := by
  decide +kernel

private theorem perm173 : KECCAK.f1600 absorbed173 = state174 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds173_0, rounds173_1, rounds173_2, rounds173_3]
  rfl

private theorem finalDigest : squeeze state174 = (0x343519a45eb48ace5cbe7daeab09d33857ada1ea478e7f513955b7e5b1db3dc5 : B256) := by
  decide +kernel

theorem finalHash :
    KECCAK.Bytes.run 0 bytes173 state173 = (0x343519a45eb48ace5cbe7daeab09d33857ada1ea478e7f513955b7e5b1db3dc5 : B256) := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 bytes173 ws = squeeze (KECCAK.f1600 (absorb173 ws)) := by
    rfl
  exact (step state173).trans ((congrArg squeeze
    ((congrArg KECCAK.f1600 words173).trans perm173)).trans finalDigest)

theorem blocks28 :
    KECCAK.Bytes.run 0 (bytes168 ++ (bytes169 ++ (bytes170 ++ (bytes171 ++ (bytes172 ++ (bytes173)))))) state168 =
      (0x343519a45eb48ace5cbe7daeab09d33857ada1ea478e7f513955b7e5b1db3dc5 : B256) := by
  rw [run_block_of_step bytes168 _ absorb168 state168 absorbed168
    state169 (fun _ => rfl) words168 perm168]
  rw [run_block_of_step bytes169 _ absorb169 state169 absorbed169
    state170 (fun _ => rfl) words169 perm169]
  rw [run_block_of_step bytes170 _ absorb170 state170 absorbed170
    state171 (fun _ => rfl) words170 perm170]
  rw [run_block_of_step bytes171 _ absorb171 state171 absorbed171
    state172 (fun _ => rfl) words171 perm171]
  rw [run_block_of_step bytes172 _ absorb172 state172 absorbed172
    state173 (fun _ => rfl) words172 perm172]
  exact finalHash

end Blanc.Lift.Usdc.ImplV2_2Creation.SigningBlocks
