import Lake
open Lake DSL

package «hodge-conjecture» where
  -- Project version
  version := v!"0.1.0"

  -- Lean compiler options
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Link to mathlib4 with specific version for reproducibility
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.0"

-- Link to Recognition Ledger foundation (commented out until available)
-- require recognition from git
--   "https://github.com/jonwashburn/recognition-ledger.git"

-- Library configuration
@[default_target]
lean_lib «Hodge» where
  -- Module structure
  roots := #[`Hodge]
  -- Include all submodules
  globs := #[.submodules `Hodge]
