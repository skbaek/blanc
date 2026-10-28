import Blanc.Lift.Usdc.ImplV2Creation.SigningBytes
import Blanc.Lift.Usdc.ImplV2Creation.SigningStates

/-! Bounded kernel checks against the existing Keccak permutation. -/
namespace Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
open Jaune Blanc.KeccakBlocks

private def absorb000 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0xb2 0xec 0x22 0x85 0x1f 0xe0 0x5a 0xf9)) 1 (by decide) (UInt64.ofBytes 0x80 0x80 0x80 0x58 0x4f 0x83 0x0 0x5c)) 2 (by decide) (UInt64.ofBytes 0x52 0x40 0x60 0x80 0x60 0xd0 0x5a 0xb9)) 3 (by decide) (UInt64.ofBytes 0xa0 0x60 0xff 0x60 0x54 0x80 0x1 0x60)) 4 (by decide) (UInt64.ofBytes 0x60 0x0 0x60 0x55 0x90 0x16 0x19 0x1b)) 5 (by decide) (UInt64.ofBytes 0x0 0x0 0x62 0x15 0x80 0x34 0x55 0xb)) 6 (by decide) (UInt64.ofBytes 0x50 0x5b 0xfd 0x80 0x0 0x60 0x57 0x23)) 7 (by decide) (UInt64.ofBytes 0x0 0x0 0x62 0x33 0x2f 0x0 0x0 0x62)) 8 (by decide) (UInt64.ofBytes 0x56 0x57 0x0 0x0 0x62 0x5b 0x56 0x35)) 9 (by decide) (UInt64.ofBytes 0x60 0x1 0x60 0x54 0x80 0x0 0x60 0x5b)) 10 (by decide) (UInt64.ofBytes 0x60 0x16 0x19 0x3 0x1b 0xa0 0x60 0x1)) 11 (by decide) (UInt64.ofBytes 0x92 0x3 0x1b 0xa0 0x60 0x1 0x60 0x1)) 12 (by decide) (UInt64.ofBytes 0x90 0x17 0x91 0x90 0x91 0x16 0x92 0x90)) 13 (by decide) (UInt64.ofBytes 0x62 0x80 0x69 0x5a 0x61 0x5b 0x56 0x55)) 14 (by decide) (UInt64.ofBytes 0x0 0x60 0x39 0x0 0x60 0x67 0x0 0x0)) 15 (by decide) (UInt64.ofBytes 0x34 0x52 0x40 0x60 0x80 0x60 0xfe 0xf3)) 16 (by decide) (UInt64.ofBytes 0x0 0x60 0x57 0x10 0x0 0x61 0x15 0x80))

private def absorbed000 : Vector UInt64 25 :=
  #v[0xb2ec22851fe05af9, 0x808080584f83005c, 0x5240608060d05ab9, 0xa060ff6054800160, 0x600060559016191b, 0x62158034550b, 0x505bfd8000605723, 0x62332f000062, 0x56570000625b5635, 0x600160548000605b, 0x601619031ba06001, 0x92031ba060016001, 0x9017919091169290, 0x6280695a615b5655, 0x60390060670000, 0x345240608060fef3, 0x60571000611580, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

private theorem words000 : absorb000 state000 = absorbed000 := by
  decide +kernel

private def quarter000_1 : Vector UInt64 25 :=
  #v[0xd1ae0d5e1aaf5641, 0xa706e99512ef0821, 0x3c317d312dd4f638, 0x5a553828f05cd627, 0x479a0df7b7c9c9dc, 0xf16ca5cd5c998296, 0xf78fbd7f47fa22d2, 0xfa5eb5ead1dd00d8, 0xe613f57fe5985f67, 0x6e8cd93f73219960, 0x41a7c987ff1711bb, 0xfa84b1988d0dd73b, 0xeb4c1f2494af046c, 0x23e19cafdf3d39e, 0x26ea948ae9def49f, 0x8ed1e89cfdc1dda3, 0x3a24e73c962465c2, 0xa64bb6eb1d2ef466, 0x2428f43d50bfdf66, 0x2b09db889d706bdc, 0xe434afb9e15430bc, 0x77ae7611d26524da, 0x1c90a56e751ea777, 0x13aa8b53f49dfb72, 0x7258a34e792cfb70]

private theorem rounds000_0 : sixRounds 0 (by decide) absorbed000 = quarter000_1 := by
  decide +kernel

private def quarter000_2 : Vector UInt64 25 :=
  #v[0xe25b4e9f31766e2, 0xf1d117d7aa717cf9, 0x194f8250ceaa3c2d, 0x10b8c11f7ebb824a, 0x76ee51eedcc57632, 0x1dbed8ebf4c8f34, 0xe1eba91f93ccd627, 0x49cf976cef8f1e0d, 0x121deae86ebf80af, 0xd43ce2511525c319, 0xeee9890aeecb15fb, 0x6bcd76893f14b4b8, 0xe75e348a257fc6b9, 0x25d407f5107b6b5e, 0x77630153a87a3423, 0xd82e4f8dc60a7aac, 0xb1f5d98975b8bdc1, 0x8bc585db2bcdf9df, 0x7e83c1e343304fe, 0xbd54e53140a7902b, 0xce479380de656630, 0xacc40f98e20f740, 0x55ae5222249b753e, 0x43213ec512a64467, 0x7aafa08cdaf8c3fb]

private theorem rounds000_1 : sixRounds 6 (by decide) quarter000_1 = quarter000_2 := by
  decide +kernel

private def quarter000_3 : Vector UInt64 25 :=
  #v[0xfad3b7a43227e7a3, 0xdccb03e5443aa47b, 0xe7d7dceea77195b5, 0x2f01e6b68244140d, 0x7675521d152a4d60, 0x961c99b6f5e0ce41, 0xfe03ff1797eb8940, 0x8ecc7e2500b6141, 0xed4e5bc0fcd92586, 0xce5b419e3a8150a4, 0x128f3046b0beb03e, 0xf10109029e7266e3, 0x924c672ece877eb6, 0x5197c783020eccf5, 0x51006707b4b3f6f4, 0x1f4aa4cf8cc5e210, 0x6ae34f0628c419a8, 0xb69c9e39bfdd0642, 0xbbc10ba29cbb091f, 0xd7818286af30a0e, 0x49d90d27de03a3bb, 0xb0d23bbb0deb4e83, 0x2c5da4fb7a738ae6, 0xf16610648a10a556, 0x8861bd02ff12c35b]

private theorem rounds000_2 : sixRounds 12 (by decide) quarter000_2 = quarter000_3 := by
  decide +kernel

private theorem rounds000_3 : sixRounds 18 (by decide) quarter000_3 = state001 := by
  decide +kernel

private theorem perm000 : KECCAK.f1600 absorbed000 = state001 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds000_0, rounds000_1, rounds000_2, rounds000_3]
  rfl

theorem block000 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes000 ++ tail) state000 =
      KECCAK.Bytes.run 0 tail state001 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes000 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb000 ws)) := by
    rfl
  exact (step state000).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words000).trans perm000))

private def absorb001 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x10 0x36 0x4 0x60 0x50 0x5b 0xfd 0x80)) 1 (by decide) (UInt64.ofBytes 0x60 0x35 0x0 0x60 0x57 0x4c 0x3 0x61)) 2 (by decide) (UInt64.ofBytes 0xc3 0xb9 0x6d 0x8a 0x63 0x80 0x1c 0xe0)) 3 (by decide) (UInt64.ofBytes 0xc2 0x63 0x80 0x57 0xbd 0x1 0x61 0x11)) 4 (by decide) (UInt64.ofBytes 0x57 0xf9 0x0 0x61 0x11 0x8f 0x10 0x37)) 5 (by decide) (UInt64.ofBytes 0x61 0x11 0xd3 0xf 0x56 0xe1 0x63 0x80)) 6 (by decide) (UInt64.ofBytes 0x1 0x4a 0xe9 0x63 0x80 0x57 0xa2 0x0)) 7 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0x7c 0x0 0x61 0x11 0x2)) 8 (by decide) (UInt64.ofBytes 0xb7 0xd 0x61 0x14 0x2 0x1 0x4a 0xe9)) 9 (by decide) (UInt64.ofBytes 0x14 0x8b 0xe3 0xfd 0xf2 0x63 0x80 0x57)) 10 (by decide) (UInt64.ofBytes 0xf9 0xf9 0x63 0x80 0x57 0x11 0xe 0x61)) 11 (by decide) (UInt64.ofBytes 0x80 0x57 0x44 0xe 0x61 0x14 0xe4 0x2b)) 12 (by decide) (UInt64.ofBytes 0xe 0x61 0x14 0x87 0x5a 0x57 0xfe 0x63)) 13 (by decide) (UInt64.ofBytes 0x80 0x5b 0x56 0x4c 0x3 0x61 0x57 0x77)) 14 (by decide) (UInt64.ofBytes 0xc 0x61 0x14 0xd3 0xf 0x56 0xe1 0x63)) 15 (by decide) (UInt64.ofBytes 0xe 0x16 0xee 0xe3 0x63 0x80 0x57 0xd7)) 16 (by decide) (UInt64.ofBytes 0xe5 0x63 0x80 0x57 0x43 0xd 0x61 0x14))

private def absorbed001 : Vector UInt64 25 :=
  #v[0x72ea5f41457a7ee3, 0xffa006c302dc394d, 0x368009661eb7bce8, 0x9a2b829fa0b7bd7a, 0xc1351d2e5eca19c0, 0x142c7fc557a098a6, 0xbbc5df6c82b5b693, 0x4c0df9755d9289e5, 0x887d40e3a65d95cf, 0x362f0b80c28a07ec, 0x2ee79de8e0f55553, 0xc619b9c94691553b, 0x73707e64b26bfd36, 0x1eb27bdfd4a151c1, 0x806cda26ee441e69, 0x59c2111c95375d3a, 0xe60ef859ec8ede4b, 0x19d6392539bf6da1, 0x1c63584409eb7a6f, 0xa9582d3f9d27c14, 0xe2e3504adcaa8200, 0xccb1b0f6c8b7d2ec, 0xc76473398f0e5ea, 0x3b92df9507922d86, 0xc9a14b857dd932f7]

private theorem words001 : absorb001 state001 = absorbed001 := by
  decide +kernel

private def quarter001_1 : Vector UInt64 25 :=
  #v[0xf16c726a22424376, 0xc96ad97edb60379, 0xc5e9b11b8f66c010, 0xe15ac8e2908d164d, 0x82ef2ee8510c05a0, 0x296882450bcb053d, 0x24e3ca711656b41a, 0x6a9b509311026fad, 0x44689e2b7f4f5a3a, 0xbb0fad3ac4ca0195, 0xe6d18654e6cebf92, 0x3fdefea816b54cb1, 0x8d0d9ab515e4ff0b, 0x46a1250af7e4671c, 0x8d75a6271c23bf8d, 0x1271bc32214c863, 0x1a22f76b00615bb4, 0x6e1ba802bc9dab3a, 0x946c35cc5b995fd, 0x9f3097af0bdf1836, 0x389d42a8386a3ebf, 0xd348fe283e4cc03a, 0x6a753e52690f66ce, 0xfdff13f9408756a9, 0xb1a3deab7d03a3da]

private theorem rounds001_0 : sixRounds 0 (by decide) absorbed001 = quarter001_1 := by
  decide +kernel

private def quarter001_2 : Vector UInt64 25 :=
  #v[0x261d45ec5fceade7, 0x767aa0246ed6ea05, 0x6b1fb89c02d1afce, 0x31b78a4e5d4d4f75, 0xdb5157d854cc8433, 0xb7055d3661c5a3a0, 0x3041730fcf4cf968, 0xfb274aa14487087, 0x557b2be1029260f6, 0x37f39f3efecb7117, 0x6c676e2d2c46fc28, 0xc95ea14f76fa7e17, 0x1ec3102b4c3759d0, 0x4c8df81cbff8bb25, 0xebf710d7ef424300, 0x8f342caee698340, 0x1d3f27a865e2cbc1, 0xf26de1cb51e782, 0xe4674a068ab50436, 0xb8d6e00ef6ba8623, 0xe386021ef6ce4788, 0x89471ef67b0380fd, 0x5b9facc5e77f187c, 0x30039d1dc0fe0ca1, 0x9b54cef4f4fb94d6]

private theorem rounds001_1 : sixRounds 6 (by decide) quarter001_1 = quarter001_2 := by
  decide +kernel

private def quarter001_3 : Vector UInt64 25 :=
  #v[0x505b2146dd830cfd, 0xff671f9153b4fbe0, 0xc80b55c12b351dd7, 0xceb4bbf7b848a947, 0x3acb14b96eb37578, 0x9651e55ff23f3f36, 0x362850786a0852a7, 0x269f02f404071905, 0xcaa55d08c9a7a3f8, 0x73dc9a43b43fb02, 0x2cb5d3a5d260f99a, 0x4a46c8e124b35de2, 0xbb5d310c7cb4a013, 0x685cfda81daaf16d, 0x11e4bfedd925e771, 0xc0c150824c0289dd, 0xe7082d96a655286, 0xfb9a17811abfe075, 0x59c96c2b73309357, 0xf05997e7a34ad95d, 0xaa6fc36dda72bb46, 0x4ac232430c5c8c94, 0x39a1ca58a7656d36, 0xda10ba54d9f3a95c, 0xcf7df9dbfc614f99]

private theorem rounds001_2 : sixRounds 12 (by decide) quarter001_2 = quarter001_3 := by
  decide +kernel

private theorem rounds001_3 : sixRounds 18 (by decide) quarter001_3 = state002 := by
  decide +kernel

private theorem perm001 : KECCAK.f1600 absorbed001 = state002 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds001_0, rounds001_1, rounds001_2, rounds001_3]
  rfl

theorem block001 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes001 ++ tail) state001 =
      KECCAK.Bytes.run 0 tail state002 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes001 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb001 ws)) := by
    rfl
  exact (step state001).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words001).trans perm001))

private def absorb002 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x57 0xaf 0xd 0x61 0x14 0xf 0xb1 0xa6)) 1 (by decide) (UInt64.ofBytes 0xd6 0x63 0x80 0x5b 0x56 0x4c 0x3 0x61)) 2 (by decide) (UInt64.ofBytes 0x57 0xd3 0x0 0x61 0x11 0x64 0xea 0x8)) 3 (by decide) (UInt64.ofBytes 0x61 0x14 0x64 0xea 0x8 0xd6 0x63 0x80)) 4 (by decide) (UInt64.ofBytes 0x94 0x16 0xd9 0x63 0x80 0x57 0x24 0xc)) 5 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0x94 0xc 0x61 0x14 0x87)) 6 (by decide) (UInt64.ofBytes 0x9c 0xc 0x61 0x14 0x3e 0xed 0x62 0xdd)) 7 (by decide) (UInt64.ofBytes 0x63 0x80 0x5b 0x56 0x4c 0x3 0x61 0x57)) 8 (by decide) (UInt64.ofBytes 0x52 0xb 0x61 0x14 0x8f 0x10 0x37 0xc2)) 9 (by decide) (UInt64.ofBytes 0x14 0x8d 0x4f 0xb8 0xc7 0x63 0x80 0x57)) 10 (by decide) (UInt64.ofBytes 0x5 0xd5 0x63 0x80 0x57 0xbe 0xb 0x61)) 11 (by decide) (UInt64.ofBytes 0x61 0x57 0xc6 0xb 0x61 0x14 0xcf 0xac)) 12 (by decide) (UInt64.ofBytes 0x5 0xa9 0x63 0x80 0x5b 0x56 0x4c 0x3)) 13 (by decide) (UInt64.ofBytes 0x80 0x57 0x66 0x1 0x61 0x11 0xbb 0x9c)) 14 (by decide) (UInt64.ofBytes 0x1 0x61 0x11 0x22 0xbf 0x38 0xad 0x63)) 15 (by decide) (UInt64.ofBytes 0x22 0xbf 0x38 0xad 0x63 0x80 0x57 0x40)) 16 (by decide) (UInt64.ofBytes 0xb0 0x63 0x80 0x57 0x68 0xa 0x61 0x14))

private def absorbed002 : Vector UInt64 25 :=
  #v[0xec146f427190c903, 0x8fc68a6a92664f1e, 0x712061d1cbc31c3c, 0xc625724a557efb54, 0x3140c92222433a7e, 0x5135c993a3559c2, 0x26b61ca3408028af, 0xd5508cf5c99f4a5, 0x5dffeba6d1ab36ce, 0x9dea0dbf989104c, 0x32445d8d7f0eeb25, 0x7985011895c44bfc, 0xc8a9ecfe12f464ad, 0x915c10b9f6bfd517, 0x5129265ceb0e475b, 0x2dc8e39a75ad6c58, 0xfe506d70966f2e35, 0x8c3c217951efdd63, 0x5e2ae97f0db87e5, 0x99e9c004d6628df9, 0x607538bc918a6800, 0xdc43c0667cf2853e, 0x5e8221e1bce1a738, 0xfd26463f168b31b1, 0x96d0f6389138b62]

private theorem words002 : absorb002 state002 = absorbed002 := by
  decide +kernel

private def quarter002_1 : Vector UInt64 25 :=
  #v[0x800f985970bfa062, 0xd2cad8ef51889618, 0x49d46dae517227bc, 0xbc86b5059c3377b, 0x9cfdf59f94385ac5, 0x1eb87418e2c68312, 0xe3a6128631c7c180, 0x75a5207644b65972, 0x4c0205de8516f566, 0x620baa997636c57, 0x53e53c76c180763d, 0x5c563969a9551af4, 0x8f5f646def051334, 0x23a3c396048f710b, 0xad6afda75acdb59c, 0xcffdd828f691e707, 0x56c60294c2456684, 0x19c3ba34eb73899d, 0x2e3d1b8128642fc0, 0x1b3a2be1179cc3a9, 0xa323da967ea6399a, 0xffd463211dda5780, 0x8dfc78960841aef1, 0x68778a244142f74a, 0x50c0c6537de7757b]

private theorem rounds002_0 : sixRounds 0 (by decide) absorbed002 = quarter002_1 := by
  decide +kernel

private def quarter002_2 : Vector UInt64 25 :=
  #v[0xcf9460621b80353a, 0xed713d399bdf80ce, 0x60bfdbdc94c5b916, 0xa1b58caa81809c18, 0xaab93f45af183f28, 0xced3067ce2d0e9ac, 0x1e23ec53d07b97ca, 0xcf31e48573a26792, 0xad98968dc2cf14d6, 0x40409a5b3ff3e5b, 0xe405f1a61842bb23, 0xccad71492f92a886, 0xb02784fc747ee663, 0xee5301b7d335963f, 0x7172c34e9b6d393c, 0xaf6025abbfad51ea, 0x318ff9d452356c6, 0xa642172af330a236, 0x3c215c936704b99b, 0x75b8e24fbca483ef, 0x2daf355a0f12f2ac, 0x8c215271c581a037, 0xf5001a0f26ecd7cc, 0x17fb89a8832aa10f, 0xb3b9ff2aee22bd57]

private theorem rounds002_1 : sixRounds 6 (by decide) quarter002_1 = quarter002_2 := by
  decide +kernel

private def quarter002_3 : Vector UInt64 25 :=
  #v[0xe408e241da34e244, 0x86012f1d77712043, 0x15b9d3a64d922bd5, 0xdd28a02dc5b6d285, 0x3bd81cb2f0c138ca, 0x5e0b543b08103a0, 0x2f4f25805eca7802, 0xb98e4a600099be35, 0x8618f0a109635ca6, 0x9911a26c499566c9, 0xb6bda1f030f65278, 0x46ce2400291c5267, 0x6ec2f0b6f23f42bd, 0x4dd3e5c12da3a19d, 0xbcbcb35b2e26f445, 0xdfde95f7a76799da, 0x56e8e774345f3b37, 0x7a273bec41227b0f, 0x244701aa2377332c, 0xf902a0e41cf0de86, 0x7c39cf3683c8dd25, 0xc3ce34e73a59ece9, 0x966604a035f9525d, 0x28ad4d9015bfb205, 0x622faefd64e474ac]

private theorem rounds002_2 : sixRounds 12 (by decide) quarter002_2 = quarter002_3 := by
  decide +kernel

private theorem rounds002_3 : sixRounds 18 (by decide) quarter002_3 = state003 := by
  decide +kernel

private theorem perm002 : KECCAK.f1600 absorbed002 = state003 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds002_0, rounds002_1, rounds002_2, rounds002_3]
  rfl

theorem block002 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes002 ++ tail) state002 =
      KECCAK.Bytes.run 0 tail state003 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes002 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb002 ws)) := by
    rfl
  exact (step state002).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words002).trans perm002))

private def absorb003 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x57 0x9b 0xa 0x61 0x14 0x95 0x60 0x8)) 1 (by decide) (UInt64.ofBytes 0x61 0x14 0x8d 0x8a 0x11 0xb2 0x63 0x80)) 2 (by decide) (UInt64.ofBytes 0x24 0x10 0xbd 0x63 0x80 0x57 0x7 0xb)) 3 (by decide) (UInt64.ofBytes 0x3 0x61 0x57 0x4a 0xb 0x61 0x14 0x30)) 4 (by decide) (UInt64.ofBytes 0x9c 0x5 0xa9 0x63 0x80 0x5b 0x56 0x4c)) 5 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0xc9 0x9 0x61 0x14 0xbb)) 6 (by decide) (UInt64.ofBytes 0x2 0xa 0x61 0x14 0xe4 0xe1 0x20 0xaa)) 7 (by decide) (UInt64.ofBytes 0x14 0x1a 0x1e 0x27 0xaa 0x63 0x80 0x57)) 8 (by decide) (UInt64.ofBytes 0x56 0x4c 0x3 0x61 0x57 0x35 0xa 0x61)) 9 (by decide) (UInt64.ofBytes 0x11 0x6d 0x50 0xd0 0x9f 0x63 0x80 0x5b)) 10 (by decide) (UInt64.ofBytes 0xd0 0x9f 0x63 0x80 0x57 0x97 0x1 0x61)) 11 (by decide) (UInt64.ofBytes 0x80 0x57 0x80 0x9 0x61 0x14 0x6d 0x50)) 12 (by decide) (UInt64.ofBytes 0x9 0x61 0x14 0x68 0x6a 0xcc 0xa0 0x63)) 13 (by decide) (UInt64.ofBytes 0xd7 0xc2 0x57 0xa4 0x63 0x80 0x57 0x88)) 14 (by decide) (UInt64.ofBytes 0x4c 0x3 0x61 0x57 0x90 0x9 0x61 0x14)) 15 (by decide) (UInt64.ofBytes 0xc3 0xb9 0x6d 0x8a 0x63 0x80 0x5b 0x56)) 16 (by decide) (UInt64.ofBytes 0x8d 0x63 0x80 0x57 0x3d 0x9 0x61 0x14))

private def absorbed003 : Vector UInt64 25 :=
  #v[0x6bf20597d2b5d83f, 0xac4094a699e49bb, 0x83edbb6cd80992e, 0x35b457cacd4d53cf, 0x58d9106687c683fa, 0xe92e0b701cd099ff, 0xcc8af04a877af59, 0x6c8df6ade5fb723, 0xfb69f7d54c9cd995, 0xd88cbb19aca919a3, 0x9c41c39bee61245, 0x19d5df07054058ec, 0xd170c05d560daf88, 0xf33c6d819857dfbb, 0xe65ce4ab7b69efbe, 0x3f3d6dce51fa22be, 0x239d2cb1e55d9dcc, 0x842098222e9b5e39, 0xc74e5299b14e5f1b, 0xfad371d2a9c5d05, 0xf75f312795a83e3c, 0x7455832d0099a355, 0xeb240ecf669d4b19, 0x7fd7aac13b1dabaf, 0x9f265a474087cb26]

private theorem words003 : absorb003 state003 = absorbed003 := by
  decide +kernel

private def quarter003_1 : Vector UInt64 25 :=
  #v[0x4b1c60ef6c2ee794, 0x5967a73d7771e77, 0xc6b915a4b319f836, 0x711c3adc0fe6b1c9, 0xb603cde6020526cb, 0xd6608449bc001fbe, 0x67ffa3de4740324b, 0xee33aad6cbae311, 0xdf34c4706366d05, 0x3cad2b0288480cb3, 0x7bd1412d7c048851, 0xa9d6d1394aa41cd1, 0x7d8e8cfd94dbb217, 0xfbd8de5e63d0a22d, 0x71f473750ef860f4, 0x6ece022baaff6c4b, 0x752b8727ace77bb1, 0x56f04a40236f9df1, 0xb9964261752bc4e, 0x7d1fb0919fd45bfd, 0xdcc807f8c88bba35, 0x858ca06a4216ee, 0x1150af978ed744b8, 0x9e5b9a84a630d669, 0x7a2b99aae763af1d]

private theorem rounds003_0 : sixRounds 0 (by decide) absorbed003 = quarter003_1 := by
  decide +kernel

private def quarter003_2 : Vector UInt64 25 :=
  #v[0x3e40c5c56d6da5a7, 0xd9cfe3fc723ce35b, 0xadc9b55dce1bf2da, 0x73fd19b81284651c, 0x8dfa3d81ac8e388f, 0x22d6bd82031b6d24, 0xbbb5a9a9b9285998, 0x838e02301fefa194, 0x910a1708fa750075, 0xddc5fcf28b4cd4fb, 0xf1a3f40ed2a73338, 0x9449f2a6439b6515, 0x15f3335ad33f213f, 0x3365a5d53c0a43e6, 0xb428f2314cae279a, 0x89f154c0721787d2, 0x24480db7a64bd7ef, 0xbee971d5e576374b, 0x823afc9166af7930, 0x3c5f696b95df93a4, 0x2638fc8c5f6f90ef, 0xf43336ec66c5540d, 0x95d6ffcf7cb19ab6, 0x1a0287a07a32daac, 0xe3f204d1769aebf]

private theorem rounds003_1 : sixRounds 6 (by decide) quarter003_1 = quarter003_2 := by
  decide +kernel

private def quarter003_3 : Vector UInt64 25 :=
  #v[0x1610c941cf19be5, 0xd44abefbec420adc, 0x22e3cafe60adc962, 0xfcffa436bdb4908e, 0xa351454c34b463b9, 0x923081b3aa41263, 0x9bc5beb1247a6eda, 0x7f238bc49298425a, 0x19a57b9ca39da193, 0x4db49e1be99121d, 0xc4884e8ffb01d82a, 0x91f83a6dd91edfea, 0xfde8d8ed9c184c45, 0xa5977ba2fd68ac7f, 0x45475bd9a32cebf9, 0x366416541e6417ab, 0x486efe1beb784008, 0x71bfed8c9bd785e1, 0xff520975a0d44aa4, 0x3f2caa9a8b6e360a, 0x80901cef08086800, 0xf3c98d9be50f44fd, 0x74f41d6464683cf6, 0xa6f436797583cf8a, 0x6a66c6f4b4704a0a]

private theorem rounds003_2 : sixRounds 12 (by decide) quarter003_2 = quarter003_3 := by
  decide +kernel

private theorem rounds003_3 : sixRounds 18 (by decide) quarter003_3 = state004 := by
  decide +kernel

private theorem perm003 : KECCAK.f1600 absorbed003 = state004 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds003_0, rounds003_1, rounds003_2, rounds003_3]
  rfl

theorem block003 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes003 ++ tail) state003 =
      KECCAK.Bytes.run 0 tail state004 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes003 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb003 ws)) := by
    rfl
  exact (step state003).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words003).trans perm003))

private def absorb004 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x57 0x70 0x9 0x61 0x14 0x5b 0xcb 0xa5)) 1 (by decide) (UInt64.ofBytes 0x61 0x14 0x41 0x9b 0xd8 0x95 0x63 0x80)) 2 (by decide) (UInt64.ofBytes 0x5b 0x56 0x4c 0x3 0x61 0x57 0x78 0x9)) 3 (by decide) (UInt64.ofBytes 0x61 0x11 0x83 0x31 0xa6 0x38 0x63 0x80)) 4 (by decide) (UInt64.ofBytes 0xd9 0x44 0x4e 0x63 0x80 0x57 0x8c 0x2)) 5 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0x35 0x2 0x61 0x11 0x56)) 6 (by decide) (UInt64.ofBytes 0xf 0x2 0x61 0x11 0xbb 0x5a 0x97 0x5c)) 7 (by decide) (UInt64.ofBytes 0x14 0xbb 0x5a 0x97 0x5c 0x63 0x80 0x57)) 8 (by decide) (UInt64.ofBytes 0xa0 0x70 0x63 0x80 0x57 0xc7 0x8 0x61)) 9 (by decide) (UInt64.ofBytes 0x80 0x57 0xcf 0x8 0x61 0x14 0x31 0x82)) 10 (by decide) (UInt64.ofBytes 0x9 0x61 0x14 0x0 0xbe 0xce 0x7e 0x63)) 11 (by decide) (UInt64.ofBytes 0x59 0xcb 0x56 0x84 0x63 0x80 0x57 0x2)) 12 (by decide) (UInt64.ofBytes 0x4c 0x3 0x61 0x57 0x35 0x9 0x61 0x14)) 13 (by decide) (UInt64.ofBytes 0x56 0xd9 0x44 0x4e 0x63 0x80 0x5b 0x56)) 14 (by decide) (UInt64.ofBytes 0x55 0x63 0x80 0x57 0xd 0x8 0x61 0x14)) 15 (by decide) (UInt64.ofBytes 0x57 0x46 0x8 0x61 0x14 0x3c 0xab 0x4b)) 16 (by decide) (UInt64.ofBytes 0x61 0x14 0x70 0x9a 0x4 0x5a 0x63 0x80))

private def absorbed004 : Vector UInt64 25 :=
  #v[0xe2c1eeb716b4a156, 0x3694f508146138c1, 0x6b780aa5cc41870f, 0x4e526c1e6c45ba63, 0xc2acc296c86b6fa3, 0x49ab4abbab56935f, 0x9d9d56955a9cfc49, 0xc1d9b82f10543370, 0xcc364f0d96f4163a, 0x8771f0298601c526, 0x4082095adc881176, 0xbfc1f13a86cb44ab, 0x77878cbb6ecb757a, 0xcccad5cb98cec893, 0x91788d667a9b1a3f, 0x1ddffe3955d4dcf5, 0x3936ca77a7c91a38, 0x391fb70491ef314f, 0xb4a64e02ef04e9d, 0x8820617ed9071010, 0x1fc8acb52908fed2, 0xb93eb54f91fd02df, 0xd97302c0eee2d6b3, 0xf2af4f199d10885d, 0x5f23080af4c7b285]

private theorem words004 : absorb004 state004 = absorbed004 := by
  decide +kernel

private def quarter004_1 : Vector UInt64 25 :=
  #v[0xd061ca36c6fd0553, 0xaa3b064fa1c2f163, 0x58c0664cdc6e7d06, 0x31395130b8c83e79, 0x1827ea43d6a5b76d, 0x9b68afec92e15d, 0x9d25b22224dac2fa, 0x2d9a0bb3948f2b82, 0x45fc1316b70aaafa, 0x440ef1d06efe0edc, 0x4130fb905336ce27, 0x187388043ee99172, 0x9516922cc4f66ef8, 0x7d18b93d92d822e9, 0x7e00001c5c6fb0f4, 0x622c9a1c92937eb7, 0x279bf2e57d73b5a2, 0xc61a1bb216e96943, 0x16ef9fbf268f1428, 0xc035dcfc83cb368, 0x26b62e639596c4b3, 0xe21d683657a9ef4b, 0xc2c4ebc25fb54b1f, 0x579dc847e3612674, 0x77434ca62e49ec35]

private theorem rounds004_0 : sixRounds 0 (by decide) absorbed004 = quarter004_1 := by
  decide +kernel

private def quarter004_2 : Vector UInt64 25 :=
  #v[0x467491131545da0d, 0x1e686890677b124f, 0x5d87cff88476b3e8, 0x42bea2bf90e615ca, 0x5e2412cd129793b, 0xfb335b2c12cb77fb, 0x3b7a9bcc930f5d41, 0x17a5801af1b4e504, 0x9df34798603bed4, 0xdaf976f0b31c8b64, 0xaca3cab8272981a3, 0x153928c7cb44be63, 0xb6660050411dcd6a, 0x28b768ecc438b4b5, 0x7ea9bc28ff2b920a, 0xdc54f64a2b0596f, 0x974e38627cfd568b, 0xb88dd6b51d0c0dc3, 0xc77b47a686055982, 0xa289e52a16047a96, 0x2cad1a9750944d92, 0x16a3a936ca02c7bc, 0x87358c205dd95da8, 0x566bd05fb5f95179, 0xd6eb12d2efda4dae]

private theorem rounds004_1 : sixRounds 6 (by decide) quarter004_1 = quarter004_2 := by
  decide +kernel

private def quarter004_3 : Vector UInt64 25 :=
  #v[0x5af3aaf5cd78d25c, 0xb6516c49a361bb2, 0x38d8e67a9a3f3739, 0xf5bdde434ca97ce1, 0x6ad09cb383361fb1, 0xb4f46550620fc21a, 0xf3a5875c39033575, 0xc509e7ddf121ea21, 0x3c4e68be8d334b9e, 0x7bedbe4feeadaefc, 0x70da098f0ccbd482, 0x77a92d55f4f84b05, 0xf5573e48dc9ee80a, 0x5d0c15489dad9d6b, 0x23fc0357876396cf, 0xd50980c5fd29ebb, 0xa26f2bc7dadb6de3, 0xcaf6cb216ad24e15, 0x490913dfd5b9c5e1, 0xee51f655f75d5445, 0x5d4e833c29431427, 0x5bee49b1d9c32f4b, 0x99a07fba85c4d387, 0x9a9de2242f40975, 0xc6942b75c45f6b3]

private theorem rounds004_2 : sixRounds 12 (by decide) quarter004_2 = quarter004_3 := by
  decide +kernel

private theorem rounds004_3 : sixRounds 18 (by decide) quarter004_3 = state005 := by
  decide +kernel

private theorem perm004 : KECCAK.f1600 absorbed004 = state005 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds004_0, rounds004_1, rounds004_2, rounds004_3]
  rfl

theorem block004 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes004 ++ tail) state004 =
      KECCAK.Bytes.run 0 tail state005 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes004 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb004 ws)) := by
    rfl
  exact (step state004).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words004).trans perm004))

private def absorb005 (ws : Vector UInt64 25) : Vector UInt64 25 :=
  (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane (KECCAK.xorLane ws 0 (by decide) (UInt64.ofBytes 0x5b 0x56 0x4c 0x3 0x61 0x57 0x79 0x8)) 1 (by decide) (UInt64.ofBytes 0x61 0x11 0x19 0xf 0xc1 0x40 0x63 0x80)) 2 (by decide) (UInt64.ofBytes 0xf 0xc1 0x40 0x63 0x80 0x57 0x66 0x2)) 3 (by decide) (UInt64.ofBytes 0x63 0x80 0x57 0xaf 0x7 0x61 0x14 0x19)) 4 (by decide) (UInt64.ofBytes 0xe8 0x7 0x61 0x14 0x68 0x6c 0x96 0x42)) 5 (by decide) (UInt64.ofBytes 0x14 0xc3 0xf5 0x71 0x4b 0x63 0x80 0x57)) 6 (by decide) (UInt64.ofBytes 0x56 0x4c 0x3 0x61 0x57 0x5 0x8 0x61)) 7 (by decide) (UInt64.ofBytes 0x14 0x83 0x31 0xa6 0x38 0x63 0x80 0x5b)) 8 (by decide) (UInt64.ofBytes 0x50 0x39 0x63 0x80 0x57 0x66 0x7 0x61)) 9 (by decide) (UInt64.ofBytes 0x80 0x57 0x6e 0x7 0x61 0x14 0x51 0x93)) 10 (by decide) (UInt64.ofBytes 0x7 0x61 0x14 0x3a 0xa8 0x4b 0x3f 0x63)) 11 (by decide) (UInt64.ofBytes 0x80 0x5b 0x56 0x4c 0x3 0x61 0x57 0xa7)) 12 (by decide) (UInt64.ofBytes 0x2 0x61 0x11 0x45 0x0 0xb6 0x2a 0x63)) 13 (by decide) (UInt64.ofBytes 0x67 0xe5 0x3c 0x31 0x63 0x80 0x57 0xf9)) 14 (by decide) (UInt64.ofBytes 0x31 0x63 0x80 0x57 0xd3 0x2 0x61 0x11)) 15 (by decide) (UInt64.ofBytes 0x57 0x23 0x5 0x61 0x14 0x67 0xe5 0x3c)) 16 (by decide) (UInt64.ofBytes 0x61 0x14 0x2b 0x16 0x57 0x33 0x63 0x80))

private def absorbed005 : Vector UInt64 25 :=
  #v[0xef84c25c63444c52, 0xb7b8f9412ab7caf1, 0xa70c2ca806faad36, 0xc9699b2f6aec627a, 0x2b8d976ede2499f2, 0x6a23a81848679204, 0x2b8d1b9e7197e0ba, 0xabd6506ac04f88a1, 0xd6c0604968d36bd5, 0xfd3ff3e50b0334a5, 0x23e96b1494fbd523, 0xe26450473282053f, 0x97f5efb8d09eb846, 0x9da3b17aef45ee46, 0xe3597eb1c9740139, 0xb9affa0cad44a9b, 0xbb287001d3c1e54b, 0x55a8b4e5ed38d312, 0x8b96be88aa1451ec, 0xeddbd61f9f7410f5, 0x4b083c760872d31c, 0xe5af761bbc1fe4cb, 0xcafb630e56dce924, 0xf7a3d7a735134385, 0x2583f7082b472c2e]

private theorem words005 : absorb005 state005 = absorbed005 := by
  decide +kernel

private def quarter005_1 : Vector UInt64 25 :=
  #v[0xc3862519cd1ad3f8, 0x483e8b117ee56bfa, 0xc8b215c5f2aab3b7, 0xb507550d9a816f85, 0x9d91a625be1adad2, 0xd0440e17875bee80, 0x5d43ad36c19130ea, 0x6c6e680f34f276e8, 0x1d108f5dedc73d76, 0xe4cadd851a0b8efb, 0xa3d33898d1cbf75a, 0xabdac5cd4da020d5, 0xc6c3589206b18f28, 0x69a08e0e905f9272, 0xdd1aed1d30a15d80, 0xe2a989354e8a5dfc, 0x20c18cb1486b93ac, 0xfd633c3d1eac57e1, 0xcf44476bc112b501, 0xaba1307f7dc51e60, 0x2f2db04b2e1bf6f3, 0xbc59e9ee59dc7be9, 0xe3768a05364a52e2, 0xec9ea1cc5e0748a3, 0x789cbe1223b1ceb7]

private theorem rounds005_0 : sixRounds 0 (by decide) absorbed005 = quarter005_1 := by
  decide +kernel

private def quarter005_2 : Vector UInt64 25 :=
  #v[0x2b0fd5ddd5f6aa5b, 0x7193a3aae2cb1c70, 0xbbc3099916184e1a, 0x5657036e2dd16f2, 0x24b73118b271b974, 0x39549d4eac22a346, 0x44daaff19f3e6020, 0x114e8134ba5f26ef, 0xdf17afeac419f8a, 0x36c3d9407fa31db8, 0xdd614378697f1117, 0x402c977d92164bb1, 0x99df42f5e6adc536, 0xf0d7551c17a7239b, 0x9b1a23fc52048a9f, 0x168330fdcf12d28d, 0x5ff459b193aa9162, 0xb0f64a034109a5d7, 0xab122f6e8d7a424, 0xd05256442283bf30, 0x69f64d56fec0187e, 0x1b15be2039a58b2, 0x94e5ba9af1edfd74, 0xbebf475180908fc5, 0x96909ee373ee0224]

private theorem rounds005_1 : sixRounds 6 (by decide) quarter005_1 = quarter005_2 := by
  decide +kernel

private def quarter005_3 : Vector UInt64 25 :=
  #v[0xe9e5b248fd00414c, 0x8a4a18dfcffd398e, 0x7674487f9707fbb0, 0x5cd7d3dcf71bdf04, 0x14470926d7320e63, 0x6a2e15fef2503370, 0x9d0f21ec4901ca07, 0x5cffb4672866a607, 0x2cd8e6359203d908, 0x496072d3eb62b608, 0x986ba23a0c9bd333, 0x3cc463d9d371ab29, 0xc2c0c89d1a16d0a9, 0x9612d5348400682a, 0xf88082dae9c4bcd6, 0x8ab45a6eb17b502, 0x75d4361c4a3e9182, 0xc07d6050fbbe5c22, 0x4331d008a1598b09, 0x2f595f3ca0df5e4a, 0x12298220bebff651, 0x2f596e192de20e56, 0x2f303cd275bcb454, 0xec29b162266f55e7, 0x898a5023a8aa3b4c]

private theorem rounds005_2 : sixRounds 12 (by decide) quarter005_2 = quarter005_3 := by
  decide +kernel

private theorem rounds005_3 : sixRounds 18 (by decide) quarter005_3 = state006 := by
  decide +kernel

private theorem perm005 : KECCAK.f1600 absorbed005 = state006 := by
  rewrite [f1600_sixRounds]
  rewrite [rounds005_0, rounds005_1, rounds005_2, rounds005_3]
  rfl

theorem block005 (tail : Bytes) :
    KECCAK.Bytes.run 0 (bytes005 ++ tail) state005 =
      KECCAK.Bytes.run 0 tail state006 := by
  have step (ws : Vector UInt64 25) :
      KECCAK.Bytes.run 0 (bytes005 ++ tail) ws =
        KECCAK.Bytes.run 0 tail (KECCAK.f1600 (absorb005 ws)) := by
    rfl
  exact (step state005).trans (congrArg (fun ws => KECCAK.Bytes.run 0 tail ws)
    ((congrArg KECCAK.f1600 words005).trans perm005))

end Blanc.Lift.Usdc.ImplV2Creation.SigningBlocks
