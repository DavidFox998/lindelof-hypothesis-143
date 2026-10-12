# PROVENANCE — recovered Siegel elementary proof

## Source
- Recovered 2026-10-11 from the Replit workspace `Beacon-Fix-Deploy` (locked
  agent task "Bring the excluded Arakelov proof sections..."), via archive
  `rh-math-recovery-2026-10-11.zip`, itself built from the workspace's
  preserved git snapshot `8f5b3b7` (2026-08-30).
- File installed byte-identical from the archive; no content was authored,
  edited, or reworded here.

## Why this file
- `Siegel/SiegelZeroFreeElementary.lean` is the one file from the recovery
  whose content is NOT already on GitHub. Fourteen sibling files from the
  same recovery are byte-identical to
  `riemann-hypothesis-four-routes/upstream/RouteD/` and needed no install.
- The four-routes copy of this file contains only the preliminary eta
  lemmas; the installed copy contains the full proof (Steps A–D, the eta
  identity, `ZetaRealSign`, `zeta_no_real_zero`,
  `siegel_repulsion_from_threshold`).
- Triage bar applied: zero `sorry`/`admit`/`axiom` (verified by grep), and
  non-vacuous proofs. Nine sibling files were excluded for containing
  sorrys or axioms; three more were excluded as trivial (vacuous bounds,
  pure re-exports, definition aliases).

## Status notes (honest)
- The proof has NOT been machine-checked here: no Lean build was run on
  this branch. Textual sorry-count is zero, but elaboration is unverified.
- The theorem proved (zeta has no real zero in (0,1), via the Dirichlet
  eta function) is classical; the value of this file is the formalization.
- Imports are Mathlib-only, so the file is in principle buildable
  standalone; a proving agent should verify it before any merge to main.

## Branch
- `recovery-siegel-2026-10-11` — recovery install only. Nothing here has
  been merged to `main`.
