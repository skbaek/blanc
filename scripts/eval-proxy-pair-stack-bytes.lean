-- Emit the actual `Prog.compile` result used by the stack-table producer.

import Blanc.ProxyPairUpgradePrograms

namespace Blanc.ProxyPair.Upgrade

open Jaune

#eval show IO Unit from do
  IO.println s!"v1 {v1Bytes.length} {v1Bytes.toHex}"

end Blanc.ProxyPair.Upgrade
