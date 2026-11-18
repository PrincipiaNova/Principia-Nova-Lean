# Results record: Z-N.1 drift law, Tier 2 (analysis)

*Appendix Z §24, Z-N.1*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_ZN1_TIER2_PROOF_11022026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 3 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The same three claims as Tier 1, now for real functions of time. Every derivative is mathlib's `HasDerivAt`, so the chain, product and quotient rules are theorems that get used, not laws that get assumed. Division is real division, licensed by N > 0. The energy is E(t) = v(t)²/(2N(t)) + N(t)·V(q(t)).

## Theorems

- `drift_law`: E′(t) = (Ṅ(t)/N(t))·E(t). *Named assumptions: N > 0 everywhere; q has derivative v; v has derivative a at t; N has derivative Ṅ at t; V has derivative V′; the Euler–Lagrange equation at t in cleared form, N·a = v·Ṅ − N³·V′(q).*
- `flat_clock`: if Ṅ(t) = 0 then E′(t) = 0. *Named assumptions: as for `drift_law`.*
- `substrate_conservation`: (E/N)′(t) = 0. The energy divided by the lapse is exactly conserved, which is the drift law read in the substrate's own clock. *Named assumptions: as for `drift_law`, with N differentiable at every time.*

## Not certified

- The Euler–Lagrange equation, which is still a hypothesis here. Tier 3 derives it from the action principle.
- Any numeric result.
