### Porting Plan

This repository is incrementally porting the monolith `IndisputableMonolith.lean` into structured modules.

- IndisputableMonolith.Core: MP, Recognition, Chain basics — DONE
- IndisputableMonolith.Constants: phi, phi_pos; RSUnits (tau0, ell0, c) — DONE
- IndisputableMonolith.Cost: Jlog (trimmed) — DONE
- Next candidates: URCAdapters, RouteA/RouteB skeletons, EightBeat proof slice

Checklist
- Keep builds green (`lake build` from `RS/`)
- Add a `#check` for each new symbol in `Porting/Checks.lean`
- Update `PORTING.md` as modules land

How to add a check
- Add `#check Namespace.symbol` in `RS/Porting/Checks.lean`
- Build with `lake build`

Inventory files
- `Porting/inventory.txt`: outline of namespaces/symbols found in the monolith
- `Porting/namespaces.txt`: namespace list
