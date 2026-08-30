-- Emit the exact Blanc OssifiableProxy artifacts consumed by the generated
-- artifact owner and by later differential/performance tooling.
--
-- This evaluator is not a second artifact owner.  Both rows are read from the
-- production `Blanc.ProxyPair` definitions.  The creation-prefix bytes are
-- deliberately not emitted as a third public row: the generator derives them
-- by checking that the returned runtime is an exact suffix of the creation
-- template.

import Blanc.ProxyPairOssifiableDeploy

namespace Blanc.ProxyPair

open Jaune

private def emitBytes (label : String) (code : Bytes) : IO Unit :=
  IO.println s!"{label} {code.length} {code.toHex}"

/-!
The labels and order below are a consumer API.  Keep them synchronized with
`scripts/lido-ossifiable-proxy-artifacts.py` and the offline execution runner.
-/
#eval show IO Unit from do
  emitBytes "creation-template" ossifiableCreationTemplate
  emitBytes "returned-runtime" runtimeBaselineBytes

end Blanc.ProxyPair
