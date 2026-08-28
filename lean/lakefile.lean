import Lake
open Lake DSL

package «formech» {
  -- add package configuration options here
}

@[default_target]
lean_lib «formech» {
  roots := #[`formech, `single_item_fixed_price]
}

--require llmlean from git
--  "https://github.com/jiajunma/llmlean.git"@"main"-/

--require LeanCodePrompts from git "https://github.com/siddhartha-gadgil/LeanAide"@"main"

require "leanprover-community" / "mathlib" @ git "v4.33.0"
