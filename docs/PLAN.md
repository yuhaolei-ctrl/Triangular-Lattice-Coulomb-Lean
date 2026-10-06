# Formalization plan

This document maps the manuscript *The triangular lattice minimizes the two-dimensional Coulomb
renormalized energy* (Y. Lei) to the Lean development. It is the reference for contributors: each
module below lists the results it must provide and the part of the paper it follows. Section and
equation numbers refer to the LaTeX source (`v2_current`).

The compared statements are in [`Challenge.lean`](../Challenge.lean); their definitions are copied
verbatim into `TriangularLattice/Statement.lean` by `scripts/sync-statement.py`.

## Overall route

```
Theorem 1.1 (Challenge)
 ├── value  W_U(E_Λ) = π R_Λ ........ Green function of Λ, energy per cell (layers 1–2)
 └── bound  W_U(E) ≥ π R_Λ
      ├── localization (layer 6): tile the plateau of χ_R by squares Q, close E in each square
      │   by an explicit boundary-layer field, project onto the Coulomb energy of a compactly
      │   supported neutral charge ρ_Q
      └── whole-plane Theorem A (layer 4) + certificate (layer 5):
          Coulomb energy of ρ_Q ≥ π R_Λ · #(points in Q) − (boundary error = o(|Q|))
```

**Deviation from the manuscript's architecture.** The manuscript proves Theorem A for periodic
configurations and passes to arbitrary fields with the periodic approximation theorem of
Sandier–Serfaty [SS12, Theorem 1] (screening). The formalization instead proves Theorem A for
finite configurations in the plane with a background charge, allowing boundary error terms of
order o(area); the local arguments of §§5–9 are unchanged, sums over a period become finite sums,
torus Fourier series become the Fourier transform on ℝ². The passage to arbitrary fields then needs
neither screening nor the existence of minimizers: in a square `Q` whose boundary carries little
energy (chosen by averaging over offsets of the tiling), the field `F = E·1_Q + Y`, with `Y` an
explicit field in a layer of width `w` outside `Q` matching the normal flux of `E`
(`Y = g(y) (1 − s/w) n`, energy `(w/3) ∮_{∂Q} g²`), has divergence `2π ρ_Q` for a compactly
supported neutral `ρ_Q`, and the projection onto gradient fields bounds its renormalized energy
below by the Coulomb energy of `ρ_Q`. Tori are needed only for `Λ` and its dilates (the value
`W_U(E_Λ)`, the Robin decomposition and the zero-stress identity).

The development is allowed to deviate from the manuscript's internal route (constants, the
auxiliary function `q`, individual arguments) as long as the compared statements are unchanged.
Every deviation is recorded in `formalization.yaml` (`fidelity.divergences`).

## Layer 1: foundations (Mathlib gaps)

| Module | Content | Paper |
|---|---|---|
| `Basic/Lattice` | Lattices `Γ = ℤ b₀ + ℤ b₁` in `Plane`, covolume, dual lattice, fundamental parallelogram, counting `#(Γ ∩ B_r) ≤ C (1 + r)²`, summability of lattice sums of decaying functions. The triangular lattice: covolume one, `Λ* = ` rotation of `Λ` by `π/6`, shells `ℓ² (a² + ab + b²)`. | §2.1 |
| `Basic/Torus` | Integrals of `Γ`-periodic functions over a cell, unfolding `∫_cell ∑_v f(·+v) = ∫ f`, Fourier coefficients on `ℝ²/Γ`, Parseval, Fourier series of functions with summable coefficients (by transport from `UnitAddTorus (Fin 2)`). | §2.1, §2.3 |
| `Fourier/Poisson` | Poisson summation (2.1) for functions with Gaussian decay together with their transforms. | (2.1) |
| `Fourier/Gaussian` | Transforms of `|x|^{2m} e^{-π|x|²}`; the involution `T` on polynomials with `𝓕[e^{-π|x|²} P(2π|x|²)] = e^{-π|k|²} (TP)(2π|k|²)` (the Laguerre identity (2.2), stated in the monomial basis). | (2.2) |
| `Special/ExpIntegral` | `q₀(x) = ½ E₁(π|x|²) = ½ ∫₁^∞ e^{-π u |x|²} du/u`: positivity, smoothness off `0`, Gaussian decay, `q₀(x) + log|x| → c₀`, transform `(1 - e^{-t/2})/t`. | Prop 3.2(a,b) |

## Layer 2: Green function, canonical fields, periodic energy

| Module | Content | Paper |
|---|---|---|
| `Green/Ewald` | `G_Γ(x) = ∑_v q₀(x+v) - 1/(2N) + N⁻¹ ∑_{k≠0} e^{-t/2}/t · e^{2πik·x}` (absolutely convergent). Periodic, smooth off `Γ`, mean zero, `-ΔG_Γ = 2π(δ_Γ - 1/N)` weakly, `G_Γ(x) = -log|x| + R_Γ + O(|x|)`, scaling `G_{sΓ}(x) = G_Γ(x/s)`. Uniqueness of the Green function among periodic distributional solutions (via Fourier coefficients). | (2.3), Prop 3.3 |
| `Energy/LocalRegularity` | An admissible field near a charge is `(x-p)/|x-p|² - π(x-p) + ∇h`, `h` harmonic (Weyl's lemma for div-curl-free `L¹_loc` fields, via mollification and the mean value property). Existence of the limit (1.2) and the core formula (11.finitepart). | §2.4 |
| `Energy/Periodic` | Canonical field `E_P = -∇Φ_P`; a periodic admissible field differs from it by a constant; energy per cell `π [N R_Γ + ∑_{i≠j} G_Γ(p_i - p_j)] + ½ N |b|²` (Lemma 2.4, by smooth integration by parts on the torus and explicit radial integrals); `W_U(E) = ω/N` for every cutoff family (Lemma 11.periodic-cutoff). | Def 2.3, Lemma 2.4, §11.4 |

Layer 2 proves the first three compared statements: `G_Λ` and `E_Λ = -∇G_Λ` exist, and
`W_U(E_Λ) = π R_Λ`.

## Layer 3: linear-programming framework (§3)

| Module | Content |
|---|---|
| `LP/Admissible` | The class of admissible pairs `(q, χ)` (Definition 3.1, (A1)–(A5)) and Proposition 3.2. |
| `LP/Decomposition` | Proposition 3.3 for `Λ` and admissible `q` (Robin decomposition (3.robin-decomp), `R_Λ = c_q − ½ + K₀(0) + t_V`). |
| `LP/WholePlane` | The whole-plane analogue of Proposition 3.4: for a finite configuration `P` with background `b` and neutral `ρ = ∑ δ_p − b`, the renormalized Coulomb energy equals `n (c_q − ½ + K₀(0)) + 𝓛(ρ) + T_V(ρ)` up to background terms supported near the boundary; `−log|x| = q(x) + ∫ a(k) (e^{2πik·x} − 1) dk + const` (Ewald). |
| `LP/ZeroStress` | Proposition 3.5, `∑_{λ≠0} |λ| V'(|λ|) = 0`. |

## Layer 4: the rigidity theorem (Theorem A, §§4–9, Appendix B), whole-plane version

Statement shape: for an admissible pair `(q, χ)` with `C_* K ≤ γ`, a finite configuration `P` in a
square `Q` and a background `b` equal to one on `Q` away from its boundary,
`|T_V(ρ) − n t_V| ≤ ½ 𝓛(ρ) + C · (boundary terms)`, where the boundary terms are bounded by a
constant times the perimeter of `Q` times powers of the filter scale. The local lemmas of §§5, 7, 8
are stated for arbitrary point sets in the plane.

| Module | Content |
|---|---|
| `Rigidity/Defects` | §5: bad pairs, retained set, counts (5.badcounts); three-shell test; slots and directional errors; disjoint hexagonal cells (5.kappasum); holes; occupancy. Local plane geometry, independent of Fourier analysis. |
| `Rigidity/Kernel` | Appendix B: bounds (5.58) on `K_{θ,R}`. |
| `Rigidity/Coverage` | §6: the filter `η`, separated-point estimates, hole mass, removed mass, the orientation remainder, the coverage identity, and Proposition 6.lineardefect / 4.defect. |
| `Rigidity/Development` | §7: local development onto the lattice (Lemma 7.1) and the counting corollary. |
| `Rigidity/Tail` | §8: dyadic localization, chord coefficients, expansion at good anchors, exact cancellation, `Γ_j = τ_j / (3ℓ)`, summation over scales (Lemma 8.tail). |
| `Rigidity/Assembly` | §9: restoring removed particles, Proposition 4.tailquad, Theorem A. |

## Layer 5: the auxiliary function and the periodic theorem (§10, Appendix A)

The manuscript's certificate solves two 200×200 Hermite systems at 13312 bits in Arb. Lean's kernel
(without `native_decide`, which Palomar forbids) is far slower, and the independent kernels used by
the comparator must replay the same computation. The certificate is therefore redesigned:

1. fewer prescribed shells, using the slack of about 10⁷⁷ in Appendix C;
2. a representation of `P`, `A`, `B` that needs much lower precision than the monomial basis;
3. verified dyadic interval arithmetic in Lean, evaluated with `decide +kernel`, with soundness
   theorems proved once.

| Module | Content |
|---|---|
| `Certificate/Interval` | Dyadic intervals, soundness of `+ - × ÷`, enclosures of `π`, `√3`, `exp`, `E₁`. |
| `Certificate/Construction` | The polynomial `P` as the solution of the Hermite systems, `q`, `a`, `χ`. |
| `Certificate/Verify` | Lemma 10.1 (nonsingularity, positivity, near-contact bound, tail size) by kernel computation. |
| `Periodic` | Corollary 10.admissible and Theorem 10.periodic. |

## Layer 6: from finite configurations to arbitrary fields (replaces §11)

| Module | Content |
|---|---|
| `Nonperiodic/Truncation` | Smeared fields `E_η`; the excision limit dominates the truncated energy (monotonicity, with the close-pair term), with weights; the renormalized energy of `E` on a region is at least `−C · #(charges)`. |
| `Nonperiodic/Discrepancy` | For `limsup W(E, χ_R)/|U_R| < ∞`: `∫_{U_R} |E_η|² = O(R² |log η|)`, charge discrepancy `o(R²)` in discs and squares, `o(R²)` charges in boundary strips. |
| `Nonperiodic/Tiling` | Tiling of the plateau of `χ_R` by squares of side `s`, an offset whose grid lines avoid the charges and carry boundary energy `≤ (2/s) ∫ |E_η|²` (averaging), additivity of the excision limit over the tiles. |
| `Nonperiodic/Closure` | The layer field `Y`, the closed field `F = E·1_Q + Y`, its divergence `2π ρ_Q`, and the projection inequality (renormalized energy of `F` ≥ renormalized Coulomb energy of `ρ_Q`). |
| `Nonperiodic/Main` | Theorem 1.1, the lower bound, by combining the above with layer 4 and letting `R → ∞`, then `s → ∞`. |

## Conventions

* Lean v4.35.0-rc3, Mathlib `c55e6e7` (tag `v4.35.0-rc3`), the module system in every file.
* No `sorry` outside `Challenge.lean` in a finished module, no `axiom`, no `native_decide`,
  `implemented_by` or `Lean.ofReduceBool`; the compared theorems use only `propext`,
  `Classical.choice` and `Quot.sound`.
* No `set_option maxHeartbeats` raises; split slow proofs into lemmas.
* Mathlib naming and style; docstrings on public declarations; files under 1500 lines.
