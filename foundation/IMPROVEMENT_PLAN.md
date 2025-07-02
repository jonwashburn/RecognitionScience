# Foundation Layer – Improvement Plan (2025-07)

(identical content as earlier)

## 1  Clarify First-Principle Lineage
• Add a metadata comment to every `.lean` file listing required RS axioms, imported constants, and key theorems proved.

## 2  Single Source-of-Truth Constants
• Ensure all modules import `foundation/Parameters/Constants.lean` and remove numeric literals.
• Provide `@[simp]` lemmas for identities such as `φ² = φ + 1`, `8 * τ₀ = log φ⁻¹`, …

## 3  Duplicate Helper Consolidation
• Merge the three `InfoTheory.lean` files into one (keep the `foundation/Helpers` copy) and update imports.

## 4  Turn Admits into Explicit TODOs
• Replace `sorry`/`admit` with clearly-tagged `TODO` blocks that mention the intended proof approach.

## 5  Lint & Namespace Hygiene
• Standardise on `namespace RecognitionScience.Foundation …`.
• Add a CI step (`lake lint` or `lake build -K`) to keep warnings at zero.

## 6  Proof Readability Pass
• Convert long `have`/`show` chains into `calc` or `simp` blocks.
• Use `by linarith`, `ring`, etc. for trivial numerics.

## 7  Philosophical Coherence Hooks
• Introduce `foundation/Philosophy/Meaning.lean` to link minimised ledger cost with existential statements, keeping metaphysical reasoning separate from core math.

### Suggested Timeline (≈ 1 week)
| Day | Focus |
|-----|-------|
| 1 | Constants sweep |
| 2 | Metadata headers & namespace cleanup |
| 3 | Helper consolidation |
| 4 | Replace admits with TODOs |
| 5 | Readability & linter pass |
| 6–7 | Philosophy module + polish |

*(Former "Millennium wrappers" step intentionally omitted as requested.)* 