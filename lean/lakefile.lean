import Lake
open Lake DSL

package «formech» {
}

@[default_target]
lean_lib «formech» {
  roots := #[`formech, `single_item_fixed_price]
}

require "leanprover-community" / "mathlib" @ git "v4.33.0"
