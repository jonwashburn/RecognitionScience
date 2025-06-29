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

-- Link to mathlib4
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Link to Recognition Ledger foundation
require recognition from git
  "https://github.com/jonwashburn/recognition-ledger.git"

-- Library configuration
@[default_target]
lean_lib «Hodge» where
  -- Module structure
  roots := #[`Hodge]
  -- Include all submodules
  globs := #[.submodules `Hodge]
