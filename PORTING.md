### Porting Plan

This repository is incrementally porting the monolith `IndisputableMonolith.lean` into structured modules.

- Source of truth for porting: `/Users/jonathanwashburn/Documents/T9 Copy - August 29/Cursor-Active/dna-lean/IndisputableMonolith.lean` (root, not the copy under `RS/`).

- IndisputableMonolith.Core: MP, Recognition, Chain basics — DONE
- IndisputableMonolith.Constants: phi, phi_pos; RSUnits (tau0, ell0, c) — DONE
- IndisputableMonolith.Cost: Jlog (trimmed) — DONE
- Next candidates: URCAdapters, RouteA/RouteB hooks, EightBeat proof slice

Checklist
- Keep builds green (`lake build` from `RS/`)
- Add a `#check` for each new symbol in `Porting/Checks.lean`
- Update `PORTING.md` as modules land

How to add a check
- Add `#check Namespace.symbol` in `RS/Porting/Checks.lean`
- Build with `lake build`

Inventory files
- `Porting/inventory.txt`: outline of namespaces/symbols found in the root monolith
- `Porting/namespaces.txt`: namespace list

Confirmation excerpt from source monolith:
```17:23:/Users/jonathanwashburn/Documents/T9 Copy - August 29/Cursor-Active/dna-lean/IndisputableMonolith.lean
namespace IndisputableMonolith
/-! ###############################################################
     URC Route B: Generators ⇒ Bridge (single-file embedding)
     Minimal certs, Verified, bundle, determination, local→global, demo
############################################################### -/
namespace URCGenerators
```
