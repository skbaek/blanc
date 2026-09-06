-- GENERATED FILE — do not edit by hand.
-- Regenerate: python3 scripts/gen-drip-stack-certificate.py --write
-- Runtime SHA-256: f7680a271f9634409f54800453c40d3e432d94cfc02774381090b67f77f27993
-- 735 decoded instructions across 1762 bytes; abstract maximum 8.
-- Data only: semantic validity is checked against actual Drip.code in Lean.

import Blanc.AbstractStackCertificate

namespace Blanc.Drip.StackSafety

open AbstractStackSafety

/-- Exact balanced subtree: 11 rows, PCs 0 through 13. -/
def subtree7 : Table :=
  (.node 7 []
    (.node 2 [none]
      (.node 1 []
        (.node 0 []
          .empty
          .empty)
        .empty)
      (.node 6 []
        (.node 5 [some 7, none]
          .empty
          .empty)
        .empty))
    (.node 10 [none]
      (.node 9 [some 0]
        (.node 8 []
          .empty
          .empty)
        .empty)
      (.node 13 [none]
        (.node 12 [some 224, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 19 through 40. -/
def subtree30 : Table :=
  (.node 30 [some 3062408035, none, none]
    (.node 23 [some 243, none, none]
      (.node 20 [none, none]
        (.node 19 [some 2674363594, none, none]
          .empty
          .empty)
        .empty)
      (.node 25 [none, none]
        (.node 24 [none]
          .empty
          .empty)
        .empty))
    (.node 35 [none]
      (.node 34 [some 197, none, none]
        (.node 31 [none, none]
          .empty
          .empty)
        .empty)
      (.node 40 [some 3062408035, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 0 through 40. -/
def subtree14 : Table :=
  .node 14 [none, none] subtree7 subtree30

/-- Exact balanced subtree: 11 rows, PCs 44 through 57. -/
def subtree49 : Table :=
  (.node 49 []
    (.node 46 [some 0]
      (.node 45 []
        (.node 44 [some 48, none]
          .empty
          .empty)
        .empty)
      (.node 48 []
        (.node 47 [some 0, some 0]
          .empty
          .empty)
        .empty))
    (.node 53 [none]
      (.node 52 [none, some 4]
        (.node 51 [some 4]
          .empty
          .empty)
        .empty)
      (.node 57 []
        (.node 56 [some 60, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 59 through 87. -/
def subtree65 : Table :=
  (.node 65 [some 64, none, none]
    (.node 61 []
      (.node 60 []
        (.node 59 [some 0, some 0]
          .empty
          .empty)
        .empty)
      (.node 63 [none, none]
        (.node 62 [none]
          .empty
          .empty)
        .empty))
    (.node 84 [none]
      (.node 83 [some 340282366920938463463374607431768211455, none]
        (.node 66 [none]
          .empty
          .empty)
        .empty)
      (.node 87 [some 193, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 44 through 87. -/
def subtree58 : Table :=
  .node 58 [some 0] subtree49 subtree65

/-- Exact balanced subtree: 45 rows, PCs 0 through 87. -/
def subtree41 : Table :=
  .node 41 [none] subtree14 subtree58

/-- Exact balanced subtree: 11 rows, PCs 89 through 150. -/
def subtree111 : Table :=
  (.node 111 [some 340282366920938463463374607431768211455, none]
    (.node 91 [none, none]
      (.node 90 [none]
        (.node 89 [none]
          .empty
          .empty)
        .empty)
      (.node 94 [none]
        (.node 93 [some 96, none, none]
          .empty
          .empty)
        .empty))
    (.node 116 []
      (.node 115 [some 189, none]
        (.node 112 [none]
          .empty
          .empty)
        .empty)
      (.node 150 [none]
        (.node 149 [some 115792089237316195423570985008687907853269984665640564039457584007913129639933]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 153 through 184. -/
def subtree176 : Table :=
  (.node 176 []
    (.node 171 [some 340282366920938463463374607431768211455, none]
      (.node 154 [none]
        (.node 153 [some 128, none, none]
          .empty
          .empty)
        .empty)
      (.node 175 [some 185, none]
        (.node 172 [none]
          .empty
          .empty)
        .empty))
    (.node 181 []
      (.node 180 [some 32, some 5]
        (.node 178 [some 5]
          .empty
          .empty)
        .empty)
      (.node 184 [some 628]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 89 through 184. -/
def subtree151 : Table :=
  .node 151 [none, none] subtree111 subtree176

/-- Exact balanced subtree: 11 rows, PCs 186 through 196. -/
def subtree191 : Table :=
  (.node 191 [some 0]
    (.node 188 [some 0, some 0]
      (.node 187 [some 0]
        (.node 186 []
          .empty
          .empty)
        .empty)
      (.node 190 []
        (.node 189 []
          .empty
          .empty)
        .empty))
    (.node 194 []
      (.node 193 []
        (.node 192 [some 0, some 0]
          .empty
          .empty)
        .empty)
      (.node 196 [some 0, some 0]
        (.node 195 [some 0]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 198 through 213. -/
def subtree209 : Table :=
  (.node 209 [some 0]
    (.node 204 [none]
      (.node 203 [some 2674363594, none]
        (.node 198 [none]
          .empty
          .empty)
        .empty)
      (.node 208 []
        (.node 207 [some 211, none]
          .empty
          .empty)
        .empty))
    (.node 212 []
      (.node 211 []
        (.node 210 [some 0, some 0]
          .empty
          .empty)
        .empty)
      (.node 213 [none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 186 through 213. -/
def subtree197 : Table :=
  .node 197 [none] subtree191 subtree209

/-- Exact balanced subtree: 45 rows, PCs 89 through 213. -/
def subtree185 : Table :=
  .node 185 [] subtree151 subtree197

/-- Exact balanced subtree: 91 rows, PCs 0 through 213. -/
def subtree88 : Table :=
  .node 88 [] subtree41 subtree185

/-- Exact balanced subtree: 11 rows, PCs 217 through 230. -/
def subtree222 : Table :=
  (.node 222 []
    (.node 219 [some 0]
      (.node 218 []
        (.node 217 [some 221, none]
          .empty
          .empty)
        .empty)
      (.node 221 []
        (.node 220 [some 0, some 0]
          .empty
          .empty)
        .empty))
    (.node 226 [none]
      (.node 225 [none, some 4]
        (.node 224 [some 4]
          .empty
          .empty)
        .empty)
      (.node 230 []
        (.node 229 [some 233, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 232 through 245. -/
def subtree239 : Table :=
  (.node 239 []
    (.node 234 []
      (.node 233 []
        (.node 232 [some 0, some 0]
          .empty
          .empty)
        .empty)
      (.node 238 [some 32, some 4]
        (.node 236 [some 4]
          .empty
          .empty)
        .empty))
    (.node 244 [none]
      (.node 243 [none]
        (.node 242 [some 628]
          .empty
          .empty)
        .empty)
      (.node 245 [none, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 217 through 245. -/
def subtree231 : Table :=
  .node 231 [some 0] subtree222 subtree239

/-- Exact balanced subtree: 11 rows, PCs 251 through 269. -/
def subtree264 : Table :=
  (.node 264 [some 268, none]
    (.node 255 [none]
      (.node 254 [some 333, none, none]
        (.node 251 [none, none]
          .empty
          .empty)
        .empty)
      (.node 261 [none]
        (.node 260 [some 2452034714, none]
          .empty
          .empty)
        .empty))
    (.node 267 [some 0, some 0]
      (.node 266 [some 0]
        (.node 265 []
          .empty
          .empty)
        .empty)
      (.node 269 []
        (.node 268 []
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 271 through 283. -/
def subtree278 : Table :=
  (.node 278 []
    (.node 275 []
      (.node 274 [some 278, none]
        (.node 271 [none]
          .empty
          .empty)
        .empty)
      (.node 277 [some 0, some 0]
        (.node 276 [some 0]
          .empty
          .empty)
        .empty))
    (.node 282 [none, some 36]
      (.node 281 [some 36]
        (.node 279 []
          .empty
          .empty)
        .empty)
      (.node 283 [none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 251 through 283. -/
def subtree270 : Table :=
  .node 270 [none] subtree264 subtree278

/-- Exact balanced subtree: 45 rows, PCs 217 through 283. -/
def subtree250 : Table :=
  .node 250 [some 2452034714, none, none] subtree231 subtree270

/-- Exact balanced subtree: 11 rows, PCs 287 through 315. -/
def subtree293 : Table :=
  (.node 293 [some 4]
    (.node 289 [some 0, some 0]
      (.node 288 [some 0]
        (.node 287 []
          .empty
          .empty)
        .empty)
      (.node 291 []
        (.node 290 []
          .empty
          .empty)
        .empty))
    (.node 297 [some 64, none, none]
      (.node 295 [none, none]
        (.node 294 [none]
          .empty
          .empty)
        .empty)
      (.node 315 [some 340282366920938463463374607431768211455, none]
        (.node 298 [none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 319 through 332. -/
def subtree328 : Table :=
  (.node 328 [some 628]
    (.node 322 [some 3]
      (.node 320 []
        (.node 319 [some 329, none]
          .empty
          .empty)
        .empty)
      (.node 325 []
        (.node 324 [some 32, some 3]
          .empty
          .empty)
        .empty))
    (.node 331 [some 0]
      (.node 330 []
        (.node 329 []
          .empty
          .empty)
        .empty)
      (.node 332 [some 0, some 0]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 287 through 332. -/
def subtree316 : Table :=
  .node 316 [none] subtree293 subtree328

/-- Exact balanced subtree: 11 rows, PCs 334 through 356. -/
def subtree345 : Table :=
  (.node 345 [none]
    (.node 340 [some 2139513249, none, none]
      (.node 335 [none, none]
        (.node 334 [none]
          .empty
          .empty)
        .empty)
      (.node 344 [some 549, none, none]
        (.node 341 [none, none]
          .empty
          .empty)
        .empty))
    (.node 354 [some 358, none]
      (.node 351 [none]
        (.node 350 [some 2139513249, none]
          .empty
          .empty)
        .empty)
      (.node 356 [some 0]
        (.node 355 []
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 358 through 369. -/
def subtree365 : Table :=
  (.node 365 []
    (.node 360 [none]
      (.node 359 []
        (.node 358 []
          .empty
          .empty)
        .empty)
      (.node 364 [some 368, none]
        (.node 361 [none]
          .empty
          .empty)
        .empty))
    (.node 368 []
      (.node 367 [some 0, some 0]
        (.node 366 [some 0]
          .empty
          .empty)
        .empty)
      (.node 369 []
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 334 through 369. -/
def subtree357 : Table :=
  .node 357 [some 0, some 0] subtree345 subtree365

/-- Exact balanced subtree: 45 rows, PCs 287 through 369. -/
def subtree333 : Table :=
  .node 333 [none] subtree316 subtree357

/-- Exact balanced subtree: 91 rows, PCs 217 through 369. -/
def subtree286 : Table :=
  .node 286 [some 290, none] subtree250 subtree333

/-- Exact balanced subtree: 183 rows, PCs 0 through 369. -/
def subtree214 : Table :=
  .node 214 [none] subtree88 subtree286

/-- Exact balanced subtree: 11 rows, PCs 372 through 385. -/
def subtree379 : Table :=
  (.node 379 [some 0, some 0]
    (.node 376 [some 380, none]
      (.node 373 [none]
        (.node 372 [none, some 36]
          .empty
          .empty)
        .empty)
      (.node 378 [some 0]
        (.node 377 []
          .empty
          .empty)
        .empty))
    (.node 383 [some 4]
      (.node 381 []
        (.node 380 []
          .empty
          .empty)
        .empty)
      (.node 385 [none, none]
        (.node 384 [none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 388 through 416. -/
def subtree411 : Table :=
  (.node 411 [none]
    (.node 406 [none]
      (.node 405 [some 340282366920938463463374607431768211455, none]
        (.node 388 [none]
          .empty
          .empty)
        .empty)
      (.node 410 []
        (.node 409 [some 545, none]
          .empty
          .empty)
        .empty))
    (.node 415 [some 96, none, none]
      (.node 413 [none, none]
        (.node 412 [none]
          .empty
          .empty)
        .empty)
      (.node 416 [none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 372 through 416. -/
def subtree387 : Table :=
  .node 387 [some 64, none, none] subtree379 subtree411

/-- Exact balanced subtree: 11 rows, PCs 434 through 497. -/
def subtree473 : Table :=
  (.node 473 [none, none]
    (.node 438 []
      (.node 437 [some 541, none]
        (.node 434 [none]
          .empty
          .empty)
        .empty)
      (.node 472 [none]
        (.node 471 [some 115792089237316195423570985008687907853269984665640564039457584007913129639933]
          .empty
          .empty)
        .empty))
    (.node 493 [some 340282366920938463463374607431768211455, none]
      (.node 476 [none]
        (.node 475 [some 128, none, none]
          .empty
          .empty)
        .empty)
      (.node 497 [some 537, none]
        (.node 494 [none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 500 through 514. -/
def subtree508 : Table :=
  (.node 508 [some 533, none]
    (.node 503 [some 96, none]
      (.node 501 [none]
        (.node 500 [some 64]
          .empty
          .empty)
        .empty)
      (.node 505 [none]
        (.node 504 [none, none]
          .empty
          .empty)
        .empty))
    (.node 512 [none]
      (.node 511 [some 64]
        (.node 509 []
          .empty
          .empty)
        .empty)
      (.node 514 [some 128, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 434 through 514. -/
def subtree498 : Table :=
  .node 498 [] subtree473 subtree508

/-- Exact balanced subtree: 45 rows, PCs 372 through 514. -/
def subtree433 : Table :=
  .node 433 [some 340282366920938463463374607431768211455, none] subtree387 subtree498

/-- Exact balanced subtree: 11 rows, PCs 516 through 532. -/
def subtree525 : Table :=
  (.node 525 []
    (.node 520 []
      (.node 519 [some 529, none]
        (.node 516 [none]
          .empty
          .empty)
        .empty)
      (.node 524 [some 32, some 2]
        (.node 522 [some 2]
          .empty
          .empty)
        .empty))
    (.node 530 []
      (.node 529 []
        (.node 528 [some 628]
          .empty
          .empty)
        .empty)
      (.node 532 [some 0, some 0]
        (.node 531 [some 0]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 534 through 543. -/
def subtree539 : Table :=
  (.node 539 [some 0]
    (.node 536 [some 0, some 0]
      (.node 535 [some 0]
        (.node 534 []
          .empty
          .empty)
        .empty)
      (.node 538 []
        (.node 537 []
          .empty
          .empty)
        .empty))
    (.node 542 []
      (.node 541 []
        (.node 540 [some 0, some 0]
          .empty
          .empty)
        .empty)
      (.node 543 [some 0]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 516 through 543. -/
def subtree533 : Table :=
  .node 533 [] subtree525 subtree539

/-- Exact balanced subtree: 11 rows, PCs 545 through 561. -/
def subtree550 : Table :=
  (.node 550 [none]
    (.node 547 [some 0]
      (.node 546 []
        (.node 545 []
          .empty
          .empty)
        .empty)
      (.node 549 [none]
        (.node 548 [some 0, some 0]
          .empty
          .empty)
        .empty))
    (.node 559 [some 563, none]
      (.node 556 [none]
        (.node 555 [some 128110906, none]
          .empty
          .empty)
        .empty)
      (.node 561 [some 0]
        (.node 560 []
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 563 through 574. -/
def subtree570 : Table :=
  (.node 570 []
    (.node 565 [none]
      (.node 564 []
        (.node 563 []
          .empty
          .empty)
        .empty)
      (.node 569 [some 573, none]
        (.node 566 [none]
          .empty
          .empty)
        .empty))
    (.node 573 []
      (.node 572 [some 0, some 0]
        (.node 571 [some 0]
          .empty
          .empty)
        .empty)
      (.node 574 []
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 545 through 574. -/
def subtree562 : Table :=
  .node 562 [some 0, some 0] subtree550 subtree570

/-- Exact balanced subtree: 45 rows, PCs 516 through 574. -/
def subtree544 : Table :=
  .node 544 [some 0, some 0] subtree533 subtree562

/-- Exact balanced subtree: 91 rows, PCs 372 through 574. -/
def subtree515 : Table :=
  .node 515 [none, none] subtree433 subtree544

/-- Exact balanced subtree: 11 rows, PCs 577 through 590. -/
def subtree584 : Table :=
  (.node 584 [some 0, some 0]
    (.node 581 [some 585, none]
      (.node 578 [none]
        (.node 577 [none, some 36]
          .empty
          .empty)
        .empty)
      (.node 583 [some 0]
        (.node 582 []
          .empty
          .empty)
        .empty))
    (.node 588 [some 4]
      (.node 586 []
        (.node 585 []
          .empty
          .empty)
        .empty)
      (.node 590 [none, none]
        (.node 589 [none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 593 through 624. -/
def subtree617 : Table :=
  (.node 617 [some 1]
    (.node 611 [none]
      (.node 610 [some 340282366920938463463374607431768211455, none]
        (.node 593 [none]
          .empty
          .empty)
        .empty)
      (.node 615 []
        (.node 614 [some 624, none]
          .empty
          .empty)
        .empty))
    (.node 623 [some 628]
      (.node 620 []
        (.node 619 [some 32, some 1]
          .empty
          .empty)
        .empty)
      (.node 624 []
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 577 through 624. -/
def subtree592 : Table :=
  .node 592 [some 64, none, none] subtree584 subtree617

/-- Exact balanced subtree: 11 rows, PCs 626 through 682. -/
def subtree663 : Table :=
  (.node 663 [none]
    (.node 628 []
      (.node 627 [some 0, some 0]
        (.node 626 [some 0]
          .empty
          .empty)
        .empty)
      (.node 662 [some 115792089237316195423570985008687907853269984665640564039457584007913129639935]
        (.node 629 []
          .empty
          .empty)
        .empty))
    (.node 679 [some 1000000000000000000000000000]
      (.node 666 []
        (.node 665 [some 160, none]
          .empty
          .empty)
        .empty)
      (.node 682 [none, some 1000000000000000000000000000]
        (.node 681 [some 160, some 1000000000000000000000000000]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 686 through 715. -/
def subtree708 : Table :=
  (.node 708 [none]
    (.node 689 [some 160]
      (.node 687 []
        (.node 686 [some 947, none]
          .empty
          .empty)
        .empty)
      (.node 707 [some 340282366920938463463374607431768211455, none]
        (.node 690 [none]
          .empty
          .empty)
        .empty))
    (.node 713 [none]
      (.node 712 []
        (.node 711 [some 943, none]
          .empty
          .empty)
        .empty)
      (.node 715 [some 192, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 626 through 715. -/
def subtree683 : Table :=
  .node 683 [none] subtree663 subtree708

/-- Exact balanced subtree: 45 rows, PCs 577 through 715. -/
def subtree625 : Table :=
  .node 625 [] subtree592 subtree683

/-- Exact balanced subtree: 11 rows, PCs 749 through 763. -/
def subtree755 : Table :=
  (.node 755 [none, none]
    (.node 751 [none, none]
      (.node 750 [none]
        (.node 749 [some 115792089237316195423570985008687907853269984665640564039457584007913129639934]
          .empty
          .empty)
        .empty)
      (.node 754 [none, none, none]
        (.node 753 [some 192, none, none]
          .empty
          .empty)
        .empty))
    (.node 761 [some 192, none]
      (.node 759 [none]
        (.node 758 [some 939, none, none]
          .empty
          .empty)
        .empty)
      (.node 763 [none]
        (.node 762 [none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 765 through 793. -/
def subtree776 : Table :=
  (.node 776 [some 935, none]
    (.node 767 [none]
      (.node 766 [some 0]
        (.node 765 []
          .empty
          .empty)
        .empty)
      (.node 773 [none]
        (.node 772 [some 4294967295, none]
          .empty
          .empty)
        .empty))
    (.node 791 [some 1000000001547125957863212448, some 1000000001547125957863212448]
      (.node 790 [some 1000000001547125957863212448]
        (.node 777 []
          .empty
          .empty)
        .empty)
      (.node 793 [some 224, some 1000000001547125957863212448, some 1000000001547125957863212448]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 749 through 793. -/
def subtree764 : Table :=
  .node 764 [some 0, none] subtree755 subtree776

/-- Exact balanced subtree: 11 rows, PCs 795 through 810. -/
def subtree802 : Table :=
  (.node 802 [none]
    (.node 799 []
      (.node 798 [some 896, none]
        (.node 795 [none]
          .empty
          .empty)
        .empty)
      (.node 801 [none]
        (.node 800 [some 0]
          .empty
          .empty)
        .empty))
    (.node 807 [some 0]
      (.node 806 []
        (.node 805 [some 874, none]
          .empty
          .empty)
        .empty)
      (.node 810 [some 1, none]
        (.node 808 [none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 814 through 838. -/
def subtree833 : Table :=
  (.node 833 [some 0]
    (.node 828 [some 1000000000000000000000000000]
      (.node 815 []
        (.node 814 [some 844, none]
          .empty
          .empty)
        .empty)
      (.node 832 []
        (.node 831 [some 256, some 1000000000000000000000000000]
          .empty
          .empty)
        .empty))
    (.node 837 [none, some 2]
      (.node 836 [some 2, none]
        (.node 834 [none]
          .empty
          .empty)
        .empty)
      (.node 838 [none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 795 through 838. -/
def subtree811 : Table :=
  .node 811 [none] subtree802 subtree833

/-- Exact balanced subtree: 45 rows, PCs 749 through 838. -/
def subtree794 : Table :=
  .node 794 [some 1000000001547125957863212448] subtree764 subtree811

/-- Exact balanced subtree: 91 rows, PCs 577 through 838. -/
def subtree716 : Table :=
  .node 716 [] subtree625 subtree794

/-- Exact balanced subtree: 183 rows, PCs 372 through 838. -/
def subtree576 : Table :=
  .node 576 [some 36] subtree515 subtree716

/-- Exact balanced subtree: 367 rows, PCs 0 through 838. -/
def subtree371 : Table :=
  .node 371 [some 36] subtree214 subtree576

/-- Exact balanced subtree: 11 rows, PCs 840 through 867. -/
def subtree861 : Table :=
  (.node 861 [some 256, some 1000000001547125957863212448]
    (.node 844 []
      (.node 843 [some 951]
        (.node 840 []
          .empty
          .empty)
        .empty)
      (.node 858 [some 1000000001547125957863212448]
        (.node 845 []
          .empty
          .empty)
        .empty))
    (.node 864 [none]
      (.node 863 [some 0]
        (.node 862 []
          .empty
          .empty)
        .empty)
      (.node 867 [none, some 2]
        (.node 866 [some 2, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 869 through 896. -/
def subtree888 : Table :=
  (.node 888 [some 1000000000000000000000000000]
    (.node 873 [some 951]
      (.node 870 []
        (.node 869 [some 0, none]
          .empty
          .empty)
        .empty)
      (.node 875 []
        (.node 874 []
          .empty
          .empty)
        .empty))
    (.node 895 [some 1141]
      (.node 892 []
        (.node 891 [some 256, some 1000000000000000000000000000]
          .empty
          .empty)
        .empty)
      (.node 896 []
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 840 through 896. -/
def subtree868 : Table :=
  .node 868 [none] subtree861 subtree888

/-- Exact balanced subtree: 11 rows, PCs 898 through 914. -/
def subtree905 : Table :=
  (.node 905 [some 0]
    (.node 900 [none]
      (.node 899 [none]
        (.node 898 [some 0]
          .empty
          .empty)
        .empty)
      (.node 904 []
        (.node 903 [some 913, none]
          .empty
          .empty)
        .empty))
    (.node 912 [some 1141]
      (.node 909 []
        (.node 908 [some 256, some 0]
          .empty
          .empty)
        .empty)
      (.node 914 []
        (.node 913 []
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 930 through 941. -/
def subtree937 : Table :=
  (.node 937 [some 0]
    (.node 934 [some 1141]
      (.node 931 []
        (.node 930 [some 256, some 1000000000000000000000000000]
          .empty
          .empty)
        .empty)
      (.node 936 []
        (.node 935 []
          .empty
          .empty)
        .empty))
    (.node 940 [none]
      (.node 939 [none]
        (.node 938 [some 0, some 0]
          .empty
          .empty)
        .empty)
      (.node 941 [some 0, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 898 through 941. -/
def subtree927 : Table :=
  .node 927 [some 1000000000000000000000000000] subtree905 subtree937

/-- Exact balanced subtree: 45 rows, PCs 840 through 941. -/
def subtree897 : Table :=
  .node 897 [] subtree868 subtree927

/-- Exact balanced subtree: 11 rows, PCs 943 through 953. -/
def subtree948 : Table :=
  (.node 948 []
    (.node 945 [some 0]
      (.node 944 []
        (.node 943 []
          .empty
          .empty)
        .empty)
      (.node 947 []
        (.node 946 [some 0, some 0]
          .empty
          .empty)
        .empty))
    (.node 951 []
      (.node 950 [some 0, some 0]
        (.node 949 [some 0]
          .empty
          .empty)
        .empty)
      (.node 953 [some 0]
        (.node 952 []
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 955 through 967. -/
def subtree963 : Table :=
  (.node 963 [none, none]
    (.node 959 []
      (.node 958 [some 1030, none]
        (.node 955 [none]
          .empty
          .empty)
        .empty)
      (.node 962 [none]
        (.node 961 [some 224]
          .empty
          .empty)
        .empty))
    (.node 966 [none, none, none]
      (.node 965 [none, none]
        (.node 964 [none, none, none]
          .empty
          .empty)
        .empty)
      (.node 967 [none, none, none, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 943 through 967. -/
def subtree954 : Table :=
  .node 954 [none] subtree948 subtree963

/-- Exact balanced subtree: 11 rows, PCs 969 through 993. -/
def subtree976 : Table :=
  (.node 976 [some 1026, none, none]
    (.node 971 [none, none, none]
      (.node 970 [none, none, none]
        (.node 969 [none, none, none]
          .empty
          .empty)
        .empty)
      (.node 973 [none, none]
        (.node 972 [none, none]
          .empty
          .empty)
        .empty))
    (.node 991 [some 500000000000000000000000000, none, none]
      (.node 978 [none, none]
        (.node 977 [none]
          .empty
          .empty)
        .empty)
      (.node 993 [none, none, none]
        (.node 992 [none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 995 through 1021. -/
def subtree1014 : Table :=
  (.node 1014 [none, some 1000000000000000000000000000]
    (.node 999 [some 1022, none, none]
      (.node 996 [none, none]
        (.node 995 [none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1013 [some 1000000000000000000000000000, none]
        (.node 1000 [none]
          .empty
          .empty)
        .empty))
    (.node 1018 []
      (.node 1017 [some 224, none]
        (.node 1015 [none]
          .empty
          .empty)
        .empty)
      (.node 1021 [some 1035]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 969 through 1021. -/
def subtree994 : Table :=
  .node 994 [none, none, none] subtree976 subtree1014

/-- Exact balanced subtree: 45 rows, PCs 943 through 1021. -/
def subtree968 : Table :=
  .node 968 [none, none, none, none] subtree954 subtree994

/-- Exact balanced subtree: 91 rows, PCs 840 through 1021. -/
def subtree942 : Table :=
  .node 942 [some 0, some 0, none] subtree897 subtree968

/-- Exact balanced subtree: 11 rows, PCs 1023 through 1035. -/
def subtree1028 : Table :=
  (.node 1028 [some 0, none]
    (.node 1025 [some 0, some 0, none]
      (.node 1024 [some 0, none]
        (.node 1023 [none]
          .empty
          .empty)
        .empty)
      (.node 1027 [none]
        (.node 1026 [none]
          .empty
          .empty)
        .empty))
    (.node 1031 []
      (.node 1030 []
        (.node 1029 [some 0, some 0, none]
          .empty
          .empty)
        .empty)
      (.node 1035 []
        (.node 1034 [some 1141]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1037 through 1053. -/
def subtree1045 : Table :=
  (.node 1045 []
    (.node 1040 [some 1, none]
      (.node 1038 [none]
        (.node 1037 [some 0]
          .empty
          .empty)
        .empty)
      (.node 1044 [some 1049, none]
        (.node 1041 [none]
          .empty
          .empty)
        .empty))
    (.node 1050 []
      (.node 1049 []
        (.node 1048 [some 1128]
          .empty
          .empty)
        .empty)
      (.node 1053 [some 256]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1023 through 1053. -/
def subtree1036 : Table :=
  .node 1036 [] subtree1028 subtree1045

/-- Exact balanced subtree: 11 rows, PCs 1056 through 1069. -/
def subtree1062 : Table :=
  (.node 1062 [none, none, none]
    (.node 1058 [none]
      (.node 1057 [none, none]
        (.node 1056 [some 224, none]
          .empty
          .empty)
        .empty)
      (.node 1061 [some 224, none, none]
        (.node 1059 [none, none]
          .empty
          .empty)
        .empty))
    (.node 1067 [some 256, none, none]
      (.node 1064 [none, none]
        (.node 1063 [none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1069 [none, none]
        (.node 1068 [none, none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1073 through 1096. -/
def subtree1090 : Table :=
  (.node 1090 [none, none, none]
    (.node 1075 [none, none]
      (.node 1074 [none]
        (.node 1073 [some 1124, none, none]
          .empty
          .empty)
        .empty)
      (.node 1089 [none, none]
        (.node 1088 [some 500000000000000000000000000, none, none]
          .empty
          .empty)
        .empty))
    (.node 1093 [none, none]
      (.node 1092 [none, none, none]
        (.node 1091 [none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1096 [some 1120, none, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1056 through 1096. -/
def subtree1070 : Table :=
  .node 1070 [none, none] subtree1062 subtree1090

/-- Exact balanced subtree: 45 rows, PCs 1023 through 1096. -/
def subtree1054 : Table :=
  .node 1054 [none] subtree1036 subtree1070

/-- Exact balanced subtree: 11 rows, PCs 1110 through 1124. -/
def subtree1119 : Table :=
  (.node 1119 [some 1128]
    (.node 1112 [none]
      (.node 1111 [none, some 1000000000000000000000000000]
        (.node 1110 [some 1000000000000000000000000000, none]
          .empty
          .empty)
        .empty)
      (.node 1116 []
        (.node 1115 [some 256, none]
          .empty
          .empty)
        .empty))
    (.node 1122 [some 0, none]
      (.node 1121 [none]
        (.node 1120 [none]
          .empty
          .empty)
        .empty)
      (.node 1124 [none]
        (.node 1123 [some 0, some 0, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1126 through 1136. -/
def subtree1131 : Table :=
  (.node 1131 [none]
    (.node 1128 []
      (.node 1127 [some 0, some 0, none]
        (.node 1126 [some 0, none]
          .empty
          .empty)
        .empty)
      (.node 1130 [some 0]
        (.node 1129 []
          .empty
          .empty)
        .empty))
    (.node 1135 [none]
      (.node 1134 [none, some 2]
        (.node 1133 [some 2, none]
          .empty
          .empty)
        .empty)
      (.node 1136 [some 0, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1110 through 1136. -/
def subtree1125 : Table :=
  .node 1125 [none] subtree1119 subtree1131

/-- Exact balanced subtree: 11 rows, PCs 1140 through 1155. -/
def subtree1148 : Table :=
  (.node 1148 [some 256, none]
    (.node 1142 []
      (.node 1141 []
        (.node 1140 [some 951]
          .empty
          .empty)
        .empty)
      (.node 1145 [none]
        (.node 1144 [some 160]
          .empty
          .empty)
        .empty))
    (.node 1151 [none, none]
      (.node 1150 [none]
        (.node 1149 [none, none]
          .empty
          .empty)
        .empty)
      (.node 1155 [none, none, none]
        (.node 1154 [some 256, none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1157 through 1181. -/
def subtree1165 : Table :=
  (.node 1165 [some 1212, none, none]
    (.node 1160 [none, none, none]
      (.node 1159 [some 160, none, none]
        (.node 1157 [none, none]
          .empty
          .empty)
        .empty)
      (.node 1162 [none, none]
        (.node 1161 [none, none]
          .empty
          .empty)
        .empty))
    (.node 1180 [none, some 1000000000000000000000000000]
      (.node 1179 [some 1000000000000000000000000000, none]
        (.node 1166 [none]
          .empty
          .empty)
        .empty)
      (.node 1181 [none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1140 through 1181. -/
def subtree1156 : Table :=
  .node 1156 [none, none, none] subtree1148 subtree1165

/-- Exact balanced subtree: 45 rows, PCs 1110 through 1181. -/
def subtree1137 : Table :=
  .node 1137 [] subtree1125 subtree1156

/-- Exact balanced subtree: 91 rows, PCs 1023 through 1181. -/
def subtree1097 : Table :=
  .node 1097 [none] subtree1054 subtree1137

/-- Exact balanced subtree: 183 rows, PCs 840 through 1181. -/
def subtree1022 : Table :=
  .node 1022 [none] subtree942 subtree1097

/-- Exact balanced subtree: 11 rows, PCs 1199 through 1213. -/
def subtree1208 : Table :=
  (.node 1208 [none]
    (.node 1203 [some 1208, none, none]
      (.node 1200 [none, none]
        (.node 1199 [some 340282366920938463463374607431768211455, none, none]
          .empty
          .empty)
        .empty)
      (.node 1207 [some 1216, none]
        (.node 1204 [none]
          .empty
          .empty)
        .empty))
    (.node 1211 [some 0, some 0, none]
      (.node 1210 [some 0, none]
        (.node 1209 [none]
          .empty
          .empty)
        .empty)
      (.node 1213 [none]
        (.node 1212 [none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1215 through 1228. -/
def subtree1221 : Table :=
  (.node 1221 [none, none, none]
    (.node 1217 [none]
      (.node 1216 [none]
        (.node 1215 [some 0, some 0, none]
          .empty
          .empty)
        .empty)
      (.node 1220 [none, none]
        (.node 1219 [some 32, none]
          .empty
          .empty)
        .empty))
    (.node 1227 [some 1735, none, none, none]
      (.node 1224 [none, none, none]
        (.node 1223 [some 1, none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1228 [none, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1199 through 1228. -/
def subtree1214 : Table :=
  .node 1214 [some 0, none] subtree1208 subtree1221

/-- Exact balanced subtree: 11 rows, PCs 1231 through 1247. -/
def subtree1239 : Table :=
  (.node 1239 [some 3, none, none, none]
    (.node 1235 [some 1568, none, none, none]
      (.node 1232 [none, none, none]
        (.node 1231 [some 2, none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1237 [none, none, none]
        (.node 1236 [none, none]
          .empty
          .empty)
        .empty))
    (.node 1244 [none, none]
      (.node 1243 [some 1542, none, none, none]
        (.node 1240 [none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1247 [some 4, none, none, none]
        (.node 1245 [none, none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1251 through 1263. -/
def subtree1259 : Table :=
  (.node 1259 [none]
    (.node 1254 [some 5, none, none]
      (.node 1252 [none, none]
        (.node 1251 [some 1462, none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1258 [some 1262, none, none]
        (.node 1255 [none, none]
          .empty
          .empty)
        .empty))
    (.node 1262 [none]
      (.node 1261 [some 0, some 0, none]
        (.node 1260 [some 0, none]
          .empty
          .empty)
        .empty)
      (.node 1263 [none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1231 through 1263. -/
def subtree1248 : Table :=
  .node 1248 [none, none, none] subtree1239 subtree1259

/-- Exact balanced subtree: 45 rows, PCs 1199 through 1263. -/
def subtree1229 : Table :=
  .node 1229 [none, none, none] subtree1214 subtree1248

/-- Exact balanced subtree: 11 rows, PCs 1266 through 1289. -/
def subtree1283 : Table :=
  (.node 1283 [none, none]
    (.node 1280 [none, none]
      (.node 1279 [some 1000000000000000000000000000, none, none]
        (.node 1266 [none, none]
          .empty
          .empty)
        .empty)
      (.node 1282 [none, none, none]
        (.node 1281 [none, none, none]
          .empty
          .empty)
        .empty))
    (.node 1287 [none, none, none, none]
      (.node 1286 [some 96, none, none, none]
        (.node 1284 [none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1289 [none, none, none, none]
        (.node 1288 [none, none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1307 through 1335. -/
def subtree1315 : Table :=
  (.node 1315 [none, none, none, none, none]
    (.node 1311 [none, none, none]
      (.node 1310 [some 1458, none, none, none, none]
        (.node 1307 [none, none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1314 [none, none, none, none]
        (.node 1313 [some 128, none, none, none]
          .empty
          .empty)
        .empty))
    (.node 1334 [some 340282366920938463463374607431768211455, none, none, none, none, none]
      (.node 1317 [none, none, none, none, none]
        (.node 1316 [none, none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1335 [none, none, none, none, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1266 through 1335. -/
def subtree1306 : Table :=
  .node 1306 [some 340282366920938463463374607431768211455, none, none, none, none] subtree1283 subtree1315

/-- Exact balanced subtree: 11 rows, PCs 1339 through 1414. -/
def subtree1377 : Table :=
  (.node 1377 [none, none, none, none]
    (.node 1373 [some 115792089237316195423570985008687907853269984665640564039457584007913129639935, none, none, none, none]
      (.node 1340 [none, none, none, none]
        (.node 1339 [none, none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1376 [some 192, none, none, none]
        (.node 1374 [none, none, none]
          .empty
          .empty)
        .empty))
    (.node 1412 [none, none, none, none]
      (.node 1411 [none, none, none]
        (.node 1410 [some 115792089237316195423570985008687907853269984665640564039457584007913129639934, none, none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1414 [none, none]
        (.node 1413 [none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1448 through 1458. -/
def subtree1454 : Table :=
  (.node 1454 [none, none, none, none]
    (.node 1450 []
      (.node 1449 [some 0, none]
        (.node 1448 [none]
          .empty
          .empty)
        .empty)
      (.node 1453 [some 0, some 32]
        (.node 1452 [some 32]
          .empty
          .empty)
        .empty))
    (.node 1457 [some 0, some 0, none, none, none, none]
      (.node 1456 [some 0, none, none, none, none]
        (.node 1455 [none, none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1458 [none, none, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1339 through 1458. -/
def subtree1447 : Table :=
  .node 1447 [some 115792089237316195423570985008687907853269984665640564039457584007913129639933, none, none] subtree1377 subtree1454

/-- Exact balanced subtree: 45 rows, PCs 1266 through 1458. -/
def subtree1338 : Table :=
  .node 1338 [some 1454, none, none, none, none, none] subtree1306 subtree1447

/-- Exact balanced subtree: 91 rows, PCs 1199 through 1458. -/
def subtree1265 : Table :=
  .node 1265 [some 64, none] subtree1229 subtree1338

/-- Exact balanced subtree: 11 rows, PCs 1460 through 1535. -/
def subtree1465 : Table :=
  (.node 1465 [none, none]
    (.node 1462 [none, none]
      (.node 1461 [some 0, some 0, none, none, none]
        (.node 1460 [some 0, none, none, none]
          .empty
          .empty)
        .empty)
      (.node 1464 [none]
        (.node 1463 [none, none]
          .empty
          .empty)
        .empty))
    (.node 1501 [some 192, none]
      (.node 1499 [none]
        (.node 1498 [some 115792089237316195423570985008687907853269984665640564039457584007913129639935, none, none]
          .empty
          .empty)
        .empty)
      (.node 1535 [some 115792089237316195423570985008687907853269984665640564039457584007913129639934, none, none]
        (.node 1502 [none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1537 through 1560. -/
def subtree1543 : Table :=
  (.node 1543 [none, none]
    (.node 1540 [some 32]
      (.node 1538 []
        (.node 1537 [some 0, none]
          .empty
          .empty)
        .empty)
      (.node 1542 [none, none]
        (.node 1541 [some 0, some 32]
          .empty
          .empty)
        .empty))
    (.node 1547 [none, none]
      (.node 1546 [some 64, none]
        (.node 1544 [none]
          .empty
          .empty)
        .empty)
      (.node 1560 [some 1000000000000000000000000000, none, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1460 through 1560. -/
def subtree1536 : Table :=
  .node 1536 [none] subtree1465 subtree1543

/-- Exact balanced subtree: 11 rows, PCs 1562 through 1574. -/
def subtree1568 : Table :=
  (.node 1568 [none, none]
    (.node 1564 []
      (.node 1563 [some 0, none]
        (.node 1562 [none]
          .empty
          .empty)
        .empty)
      (.node 1567 [some 0, some 32]
        (.node 1566 [some 32]
          .empty
          .empty)
        .empty))
    (.node 1572 [some 64, none]
      (.node 1570 [none]
        (.node 1569 [none, none]
          .empty
          .empty)
        .empty)
      (.node 1574 [none, none, none]
        (.node 1573 [none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1588 through 1662. -/
def subtree1625 : Table :=
  (.node 1625 [none]
    (.node 1590 [none, none]
      (.node 1589 [none, some 1000000000000000000000000000, none]
        (.node 1588 [some 1000000000000000000000000000, none, none]
          .empty
          .empty)
        .empty)
      (.node 1624 [some 115792089237316195423570985008687907853269984665640564039457584007913129639935, none, none]
        (.node 1591 [none, none]
          .empty
          .empty)
        .empty))
    (.node 1661 [some 115792089237316195423570985008687907853269984665640564039457584007913129639934, none, none]
      (.node 1628 [none, none]
        (.node 1627 [some 192, none]
          .empty
          .empty)
        .empty)
      (.node 1662 [none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1562 through 1662. -/
def subtree1575 : Table :=
  .node 1575 [none, none] subtree1568 subtree1625

/-- Exact balanced subtree: 45 rows, PCs 1460 through 1662. -/
def subtree1561 : Table :=
  .node 1561 [none, none] subtree1536 subtree1575

/-- Exact balanced subtree: 11 rows, PCs 1665 through 1678. -/
def subtree1671 : Table :=
  (.node 1671 [none]
    (.node 1668 [none, none, none]
      (.node 1667 [some 96, none, none]
        (.node 1665 [none, none]
          .empty
          .empty)
        .empty)
      (.node 1670 [none, none, none]
        (.node 1669 [none, none]
          .empty
          .empty)
        .empty))
    (.node 1676 [some 128, none, none]
      (.node 1674 [none, none]
        (.node 1673 [some 64, none]
          .empty
          .empty)
        .empty)
      (.node 1678 [none, none]
        (.node 1677 [none, none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1712 through 1721. -/
def subtree1717 : Table :=
  (.node 1717 [some 0, some 0, some 0, some 0, none, none]
    (.node 1714 [some 0, none, none]
      (.node 1713 [none, none]
        (.node 1712 [none]
          .empty
          .empty)
        .empty)
      (.node 1716 [some 0, some 0, some 0, none, none]
        (.node 1715 [some 0, some 0, none, none]
          .empty
          .empty)
        .empty))
    (.node 1720 [none, none, none, some 0, some 0, some 0, some 0, none]
      (.node 1719 [none, none, some 0, some 0, some 0, some 0, none]
        (.node 1718 [none, some 0, some 0, some 0, some 0, none]
          .empty
          .empty)
        .empty)
      (.node 1721 [none, none]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1665 through 1721. -/
def subtree1711 : Table :=
  .node 1711 [some 115792089237316195423570985008687907853269984665640564039457584007913129639933, none, none] subtree1671 subtree1717

/-- Exact balanced subtree: 11 rows, PCs 1725 through 1736. -/
def subtree1730 : Table :=
  (.node 1730 [some 0, none]
    (.node 1727 [some 0, some 0, none]
      (.node 1726 [some 0, none]
        (.node 1725 [none]
          .empty
          .empty)
        .empty)
      (.node 1729 [none]
        (.node 1728 [none]
          .empty
          .empty)
        .empty))
    (.node 1734 [some 0, some 32]
      (.node 1733 [some 32]
        (.node 1731 []
          .empty
          .empty)
        .empty)
      (.node 1736 [none, none]
        (.node 1735 [none, none]
          .empty
          .empty)
        .empty)))

/-- Exact balanced subtree: 10 rows, PCs 1739 through 1761. -/
def subtree1756 : Table :=
  (.node 1756 [none]
    (.node 1741 [none]
      (.node 1740 [none, none]
        (.node 1739 [some 64, none]
          .empty
          .empty)
        .empty)
      (.node 1755 [none, some 1000000000000000000000000000]
        (.node 1754 [some 1000000000000000000000000000, none]
          .empty
          .empty)
        .empty))
    (.node 1760 [some 32]
      (.node 1758 []
        (.node 1757 [some 0, none]
          .empty
          .empty)
        .empty)
      (.node 1761 [some 0, some 32]
        .empty
        .empty)))

/-- Exact balanced subtree: 22 rows, PCs 1725 through 1761. -/
def subtree1737 : Table :=
  .node 1737 [none] subtree1730 subtree1756

/-- Exact balanced subtree: 45 rows, PCs 1665 through 1761. -/
def subtree1724 : Table :=
  .node 1724 [some 1728, none, none] subtree1711 subtree1737

/-- Exact balanced subtree: 91 rows, PCs 1460 through 1761. -/
def subtree1664 : Table :=
  .node 1664 [some 64, none] subtree1561 subtree1724

/-- Exact balanced subtree: 183 rows, PCs 1199 through 1761. -/
def subtree1459 : Table :=
  .node 1459 [none, none, none] subtree1265 subtree1664

/-- Exact balanced subtree: 367 rows, PCs 840 through 1761. -/
def subtree1182 : Table :=
  .node 1182 [none, none] subtree1022 subtree1459

/-- Exact balanced subtree: 735 rows, PCs 0 through 1761. -/
def subtree839 : Table :=
  .node 839 [some 0, none] subtree371 subtree1182

/-- Conservative whole-stack patterns, including both conditional arms.
Every successor check uses this complete table across named subtrees. -/
def table : Table := subtree839

end Blanc.Drip.StackSafety
