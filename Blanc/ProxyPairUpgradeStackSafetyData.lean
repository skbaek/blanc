-- GENERATED FILE — do not edit by hand.
-- Regenerate: python3 scripts/gen-proxy-pair-stack-certificate.py --write
-- Compiler bytes SHA-256: af0533540c8159d1b20094177ccbaa9175701fe4131acbdd334d10af4ce6b394
-- 47 reachable instructions across 74 bytes; maximum 3.
-- Source: Blanc.ProxyPair.Upgrade.v1Bytes (actual Prog.compile result).
-- Untrusted data only: Lean checks it against the actual compiler result.

import Blanc.AbstractStackCertificate

namespace Blanc.ProxyPair.Upgrade.StackSafetyData

open AbstractStackSafety

/-- Balanced pack: 11 rows, PCs 0 through 17. -/
def pack6 : Table :=
  (.node 6 [none]
    (.node 2 [some 0]
      (.node 1 []
        (.node 0 []
          .empty
          .empty)
        .empty)
      (.node 5 [some 224, none]
        (.node 3 [none]
          .empty
          .empty)
        .empty))
    (.node 13 [none, none]
      (.node 12 [some 1067774533, none, none]
        (.node 7 [none, none]
          .empty
          .empty)
        .empty)
      (.node 17 [none]
        (.node 16 [some 49, none, none]
          .empty
          .empty)
        .empty)))

/-- Balanced pack: 11 rows, PCs 23 through 39. -/
def pack32 : Table :=
  (.node 32 []
    (.node 27 []
      (.node 26 [some 31, none]
        (.node 23 [none]
          .empty
          .empty)
        .empty)
      (.node 31 []
        (.node 30 [some 0]
          .empty
          .empty)
        .empty))
    (.node 37 [some 41, none]
      (.node 34 [none]
        (.node 33 [none]
          .empty
          .empty)
        .empty)
      (.node 39 [some 0]
        (.node 38 []
          .empty
          .empty)
        .empty)))

/-- Balanced pack: 23 rows, PCs 0 through 39. -/
def pack22 : Table :=
  .node 22 [some 1428426871, none] pack6 pack32

/-- Balanced pack: 11 rows, PCs 41 through 53. -/
def pack48 : Table :=
  (.node 48 []
    (.node 44 [some 4]
      (.node 42 []
        (.node 41 []
          .empty
          .empty)
        .empty)
      (.node 47 [some 7, none]
        (.node 45 [none]
          .empty
          .empty)
        .empty))
    (.node 51 []
      (.node 50 [none]
        (.node 49 [none]
          .empty
          .empty)
        .empty)
      (.node 53 [none]
        (.node 52 [none]
          .empty
          .empty)
        .empty)))

/-- Balanced pack: 11 rows, PCs 57 through 69. -/
def pack63 : Table :=
  (.node 63 [some 7]
    (.node 59 [some 0, some 0]
      (.node 58 [some 0]
        (.node 57 []
          .empty
          .empty)
        .empty)
      (.node 61 []
        (.node 60 []
          .empty
          .empty)
        .empty))
    (.node 66 []
      (.node 65 [some 0, none]
        (.node 64 [none]
          .empty
          .empty)
        .empty)
      (.node 69 [some 0, some 32]
        (.node 68 [some 32]
          .empty
          .empty)
        .empty)))

/-- Balanced pack: 23 rows, PCs 41 through 69. -/
def pack56 : Table :=
  .node 56 [some 60, none] pack48 pack63

/-- Balanced pack: 47 rows, PCs 0 through 69. -/
def pack40 : Table :=
  .node 40 [some 0, some 0] pack22 pack56

/-- Complete generated candidate. Every pack checks successors in this table. -/
def table : Table := pack40

/-- Negative-control data: the same rows with only entry row zero removed. -/
def tableWithoutEntry : Table :=
  (.node 41 []
    (.node 23 [none]
      (.node 7 [none, none]
        (.node 3 [none]
          (.node 2 [some 0]
            (.node 1 []
              .empty
              .empty)
            .empty)
          (.node 6 [none]
            (.node 5 [some 224, none]
              .empty
              .empty)
            .empty))
        (.node 16 [some 49, none, none]
          (.node 13 [none, none]
            (.node 12 [some 1067774533, none, none]
              .empty
              .empty)
            .empty)
          (.node 22 [some 1428426871, none]
            (.node 17 [none]
              .empty
              .empty)
            .empty)))
      (.node 33 [none]
        (.node 30 [some 0]
          (.node 27 []
            (.node 26 [some 31, none]
              .empty
              .empty)
            .empty)
          (.node 32 []
            (.node 31 []
              .empty
              .empty)
            .empty))
        (.node 38 []
          (.node 37 [some 41, none]
            (.node 34 [none]
              .empty
              .empty)
            .empty)
          (.node 40 [some 0, some 0]
            (.node 39 [some 0]
              .empty
              .empty)
            .empty))))
    (.node 57 []
      (.node 49 [none]
        (.node 45 [none]
          (.node 44 [some 4]
            (.node 42 []
              .empty
              .empty)
            .empty)
          (.node 48 []
            (.node 47 [some 7, none]
              .empty
              .empty)
            .empty))
        (.node 52 [none]
          (.node 51 []
            (.node 50 [none]
              .empty
              .empty)
            .empty)
          (.node 56 [some 60, none]
            (.node 53 [none]
              .empty
              .empty)
            .empty)))
      (.node 64 [none]
        (.node 60 []
          (.node 59 [some 0, some 0]
            (.node 58 [some 0]
              .empty
              .empty)
            .empty)
          (.node 63 [some 7]
            (.node 61 []
              .empty
              .empty)
            .empty))
        (.node 68 [some 32]
          (.node 66 []
            (.node 65 [some 0, none]
              .empty
              .empty)
            .empty)
          (.node 69 [some 0, some 32]
            .empty
            .empty)))))

end Blanc.ProxyPair.Upgrade.StackSafetyData
