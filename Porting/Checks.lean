import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.URC.RouteB
import IndisputableMonolith.Ledger
import IndisputableMonolith.ParityEight
import IndisputableMonolith.Causality
import IndisputableMonolith.LedgerUnits
import IndisputableMonolith.LightCone
import IndisputableMonolith.UnitMapping
import IndisputableMonolith.URC.RouteA
import IndisputableMonolith.MaxwellDEC
import IndisputableMonolith.Complexity.VertexCover
import IndisputableMonolith.Complexity.RSVC

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

-- Route B
#check IndisputableMonolith.URCGenerators.VerifiedGenerators
#check IndisputableMonolith.URCGenerators.determination_by_generators
#check IndisputableMonolith.URCGenerators.routeB_report

-- Ledger/T2/T3
#check IndisputableMonolith.Ledger
#check IndisputableMonolith.AtomicTick
#check IndisputableMonolith.T2_atomicity
#check IndisputableMonolith.T3_continuity

-- Parity/Eight
#check IndisputableMonolith.Pattern
#check IndisputableMonolith.CompleteCover
#check IndisputableMonolith.eight_tick_min
#check IndisputableMonolith.period_exactly_8

-- Causality/ConeBound
#check IndisputableMonolith.Causality.Kinematics
#check IndisputableMonolith.Causality.ReachN
#check IndisputableMonolith.Causality.ballP
#check IndisputableMonolith.ConeBound.ballFS
#check IndisputableMonolith.ConeBound.ballFS_card_le_geom

-- LedgerUnits
#check IndisputableMonolith.LedgerUnits.DeltaSub
#check IndisputableMonolith.LedgerUnits.equiv_delta_one
#check IndisputableMonolith.LedgerUnits.fromZ
#check IndisputableMonolith.LedgerUnits.toZ
#check IndisputableMonolith.LedgerUnits.rungOf
#check IndisputableMonolith.LedgerUnits.kOf

-- LightCone StepBounds
#check IndisputableMonolith.LightCone.StepBounds
#check IndisputableMonolith.LightCone.StepBounds.reach_time_eq
#check IndisputableMonolith.LightCone.StepBounds.reach_rad_le
#check IndisputableMonolith.LightCone.StepBounds.cone_bound

-- UnitMapping
#check IndisputableMonolith.UnitMapping.AffineMapZ
#check IndisputableMonolith.UnitMapping.mapDelta
#check IndisputableMonolith.UnitMapping.mapDeltaCharge
#check IndisputableMonolith.UnitMapping.mapDeltaTime
#check IndisputableMonolith.UnitMapping.mapDeltaAction

-- Route A
#check IndisputableMonolith.URC.BridgeAxioms.MeasurementAxioms
#check IndisputableMonolith.URC.BridgeAxioms.bridge_inevitability
#check IndisputableMonolith.URC.BridgeAxioms.Manifest.bridge
#check IndisputableMonolith.URCAdapters.routeA_end_to_end_demo

-- Maxwell DEC
#check IndisputableMonolith.MaxwellDEC.Simplex
#check IndisputableMonolith.MaxwellDEC.DForm
#check IndisputableMonolith.MaxwellDEC.HasCoboundary
#check IndisputableMonolith.MaxwellDEC.HasHodge
#check IndisputableMonolith.MaxwellDEC.Medium
#check IndisputableMonolith.MaxwellDEC.Sources
#check IndisputableMonolith.MaxwellDEC.Equations

-- Complexity
#check IndisputableMonolith.Complexity.VertexCover.Instance
#check IndisputableMonolith.Complexity.VertexCover.HasCover
#check IndisputableMonolith.Complexity.RSVC.ConstraintInstance
#check IndisputableMonolith.Complexity.RSVC.rs_preserving_RS2VC

/-! Add new checks here as modules are ported. -/
