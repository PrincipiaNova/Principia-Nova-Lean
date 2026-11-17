# Principia Nova — Kernel-Certified Theorem Roster

[![CI](https://github.com/PrincipiaNova/Principia-Nova-Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/PrincipiaNova/Principia-Nova-Lean/actions/workflows/ci.yml)

Machine-checked Lean 4 proofs accompanying *Principia Nova*. Every file compiles with **zero `sorry`**, and every theorem audits to Lean's standard classical foundation — `[propext, Classical.choice, Quot.sound]`, the same three axioms all of mathlib rests on — **or fewer**. Several theorems audit to a single axiom, and five to **no axioms at all**. The repository contains no `axiom` declarations: every assumption enters as a named hypothesis in a theorem's own statement.

Each proof file is standalone: it imports its library (mathlib, or PhysLean for the four files in `physlean/`) and nothing else of this repository, so every certificate can be read, checked, and challenged independently.

## What a certificate here is — and is not

The kernel answers one question: *if the framework starts here, does it reach there?* Every assumption a theorem needs is a **named hypothesis in its own statement**, where any reader — human or machine — can see exactly what was assumed. Whether nature instantiates the premises is a question for observation and experiment; the book's falsification criteria keep that question open on purpose.

## Verifying it yourself

With [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get   # fetch the mathlib build cache (minutes, not hours)
lake build --wfail   # compile every PN/ file; any warning — including a `sorry` — fails the build
```

The toolchain (`lean-toolchain`) and every dependency (`lake-manifest.json`) are pinned, so the build is reproducible from pinned sources. The CI workflow in `.github/workflows/ci.yml` runs exactly these steps on every push — the badge above is the receipt.

**Build scope, stated exactly:** `lake build` covers the 29 files in `PN/` — the mathlib roster. The four `physlean/` files were certified on a PhysLean workspace (their headers record it) and sit outside this build; the PhysLean workspace pin will be recorded here when that workspace is rebuilt, at which point they gain their own build job. Until then their verification route is the same as every file's original one: open the file, read the statements, compile it against the toolchain its header names.

Axiom audit: each file ends with `#print axioms` directives; their outputs appear in the build log.

**Toolchain history:** each file's header records the toolchain current at its certification date (the earliest file was certified on Lean 4.21.0 core). The repository pins one unified rebuild toolchain (`lean-toolchain`, v4.36.0, mathlib `6201aea8`), and CI compiles every `PN/` file against it.

## Layout

- `PN/` — the certified proof files (Lean 4 + mathlib). Two of these files (`PN_LEAN_ZN1_PROOF_10292026.lean`, `PN_LEAN_ZN2_TIER1_PROOF_11022026.lean`) use no mathlib at all — pure core Lean, with their algebraic assumptions stated in full as hypotheses.
- `physlean/` — four proof files that additionally consume [PhysLean](https://physlean.com)'s formalized physics (the variational-calculus and Standard-Model-Higgs modules); kept apart so the main `lake build` stays mathlib-only (see build scope above).
- `results/` — plain-language results records per proof file (what each theorem states, its fences, and its place in the program). Being prepared for publication.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` — the pinned build.

## Naming

Files are named `PN_LEAN_<CAMPAIGN>_<PART>_<MMDDYYYY>.lean` by certification date. The companion volume's closing section ("References and Lean Certs") carries the full roster — titled *Lean Certs — The Kernel Record* — listing every theorem with its claim and its named fences, organized by the book's own chapters.

## License

© 2026. All rights reserved. The proofs are published for verification and scholarly review; reproduction terms will be stated here in a later revision.
