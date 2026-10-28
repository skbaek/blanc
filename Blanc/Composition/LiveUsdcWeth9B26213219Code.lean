import Blanc.Composition.LiveUsdcWeth9B26213219Data.Data
import Blanc.Lift.Weth9.Cert
import Blanc.Lift.Usdc.Lib.Cert
import Blanc.Lift.Usdc.Proxy.Cert
import Blanc.Lift.Usdc.Impl.Cert
import Blanc.Lift.UniswapV2Pair.Cert
import Blanc.Lift.UniswapV2Factory.Cert

/-! Byte-for-byte identities of supplied B26213219 runtimes.
These compare the actual generated literals with the certified code. They do
not authenticate the fetched evidence or adopt its historical observations. -/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc.Lift LiveUsdcWeth9B26213219Data

theorem weth_code : weth9Code = Weth9.code.data.toList := by
  decide +kernel

theorem usdc_library_code : usdcLibraryCode = Usdc.Lib.code.data.toList := by
  decide +kernel

theorem usdc_proxy_code : usdcProxyCode = Usdc.Proxy.code.data.toList := by
  decide +kernel

theorem pair_code : pairCode = UniswapV2Pair.code.data.toList := by
  decide +kernel

theorem usdc_implementation_code : usdcImplementationCode = Usdc.Impl.code.data.toList := by
  decide +kernel

theorem factory_code : factoryCode = UniswapV2Factory.code.data.toList := by
  decide +kernel

end Blanc.Composition.LiveUsdcWeth9B26213219
