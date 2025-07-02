/-
  Recognition Science: Foundation Main
  ===================================

  Main entry point for the foundation module.
  Re-exports all foundation components.

  Author: Jonathan Washburn & Claude
  Recognition Science Institute

  Requires: A1 (Discrete Recognition), A4 (Unitary Evolution)
  Imports Constants: φ, E_coh, τ₀, lambda_rec, c
  Purpose: Provide a single import hub so downstream layers can write
           `import foundation.Main` and obtain the core constants.
-/

-- Import parameter constants
import foundation.Parameters.RealConstants

namespace foundation

-- Re-export key definitions (constants)
export RecognitionScience.Constants (φ E_coh τ₀ lambda_rec c h_bar k_B T_CMB T_room)

end foundation
