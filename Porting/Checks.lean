import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-! Porting checks: ensures key symbols exist and typecheck. -/

-- Core
#check IndisputableMonolith.MP
#check IndisputableMonolith.mp_holds
#check IndisputableMonolith.Recognition
#check IndisputableMonolith.RecognitionStructure
#check IndisputableMonolith.Chain

-- Constants
#check IndisputableMonolith.Constants.phi
#check IndisputableMonolith.Constants.phi_pos
#check IndisputableMonolith.Constants.RSUnits.RSUnits
#check IndisputableMonolith.Constants.RSUnits.c
#check IndisputableMonolith.Constants.RSUnits.ell0_div_tau0_eq_c

-- Cost
#check IndisputableMonolith.Jlog

/-! Add new checks here as modules are ported. -/


