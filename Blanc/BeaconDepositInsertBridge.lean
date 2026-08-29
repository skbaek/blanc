import Blanc.BeaconDepositInsertIterHeight
import Blanc.BeaconDepositInsertIterKeys
import Blanc.BeaconDepositInsertIterNode
import Blanc.BeaconDepositInsertIterSize

/-!
# Beacon deposit insertion bridge

Compatibility import for the projection-level bridges between the compiled
insertion fold and the pure first-live model.  Each projection has a separate
owner so elaboration never constructs one monolithic state equality.
-/
