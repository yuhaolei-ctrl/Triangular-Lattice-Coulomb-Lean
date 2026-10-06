/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The triangular lattice minimizes the two-dimensional Coulomb renormalized energy

This file states Theorem 1.1 of Y. Lei, *The triangular lattice minimizes the two-dimensional
Coulomb renormalized energy*. Let `C ⊂ ℝ²` be a locally finite set and `E : ℝ² → ℝ²` a vector
field with

`div E = 2π (∑_{p ∈ C} δ_p - 1)`,   `curl E = 0`,   `sup_{R > 1} #(C ∩ B_R) / |B_R| < ∞`      (1.1)

in the sense of distributions. For a compactly supported Lipschitz weight `χ ≥ 0`, the
renormalized energy of Sandier and Serfaty is

`W(E, χ) = lim_{η ↓ 0} [ ½ ∫_{ℝ² ∖ ⋃_p B(p, η)} χ |E|² + π log η ∑_p χ(p) ]`,            (1.2)

and, for the family `U_R` of discs `B_R` or of squares `(-R/2, R/2)²`, with cutoffs `χ_R`
supported in `U_R`, equal to one at distance at least `L` from `∂U_R`, with values in `[0, 1]`
and uniformly bounded gradients,

`W_U(E) = limsup_{R → ∞} W(E, χ_R) / |U_R|`.                                                (1.3)

Let `ℓ = (2/√3)^{1/2}` and `Λ = ℓ [ℤ (1, 0) + ℤ (1/2, √3/2)]`, the triangular lattice of
covolume one, with canonical field `E_Λ` and Robin constant `R_Λ`.

**Theorem 1.1.** For discs or squares and every fixed cutoff width `L > 0`, every field `E`
satisfying (1.1) obeys `W_U(E) ≥ W_U(E_Λ) = π R_Λ`.

Equation numbers refer to the LaTeX source of the paper.

## Conventions

* The plane is `EuclideanSpace ℝ (Fin 2)`, so `‖·‖` is the Euclidean norm and `volume` is
  Lebesgue measure. Coordinates are `x 0` and `x 1`.
* A test function is a smooth real function with compact support. The distributional identities
  (1.1) are stated by integrating against the partial derivatives of test functions:
  `⟨div E, φ⟩ = -∫ E · ∇φ` and `⟨curl E, φ⟩ = ∫ (E x 0 · ∂₁φ - E x 1 · ∂₀φ)`, with coordinates and
  partial derivatives indexed by `Fin 2`. Sums over the locally finite
  set `C` are `finsum`s; they have finitely many nonzero terms because `φ` and `χ` have compact
  support.
* The limit in (1.2) is `limUnder (𝓝[>] 0)`, and the `limsup` in (1.3) is taken in `EReal`, so
  that `W_U(E) = +∞` is allowed. The cutoff family is a function `χ : ℝ → ℝ² → ℝ` of the size
  parameter `R`; the uniform gradient bound is a common Lipschitz constant.
* The canonical field `E_Λ` (Definition 2.1) is characterized as a `Λ`-periodic field satisfying
  (1.1) for the configuration `C = Λ` with zero average over a period cell; such fields differ
  only on null sets, which do not affect `W`. The Green function `G_Λ` of the torus `ℝ²/Λ`
  (equation (2.3)) is characterized as the `Λ`-periodic locally integrable function, continuous
  off `Λ`, with zero average over a period cell and `-ΔG_Λ = 2π (∑_{λ ∈ Λ} δ_λ - 1)` in the sense
  of distributions. The Robin constant is `R_Λ = lim_{x → 0} (G_Λ(x) + log |x|)`.
* The theorem is split into four statements: the existence of `E_Λ` and of `G_Λ`, the value
  `W_U(E_Λ) = π R_Λ`, and the lower bound `W_U(E) ≥ W_U(E_Λ)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set Real
open scoped ContDiff Laplacian

namespace TriangularLattice

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The partial derivative `∂ᵢ φ` of a function on the plane. -/
noncomputable def partialDeriv (i : Fin 2) (φ : Plane → ℝ) (x : Plane) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- A test function: a smooth real function with compact support. -/
def IsTestFunction (φ : Plane → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

/-- A set of points is locally finite if it meets every compact set in a finite set. -/
def IsLocallyFinite (C : Set Plane) : Prop :=
  ∀ K : Set Plane, IsCompact K → (C ∩ K).Finite

/-- The density bound of (1.1): `sup_{R > 1} #(C ∩ B_R) / |B_R| < ∞`. -/
def HasBoundedDensity (C : Set Plane) : Prop :=
  ∃ M : ℝ, ∀ R : ℝ, 1 < R → ((C ∩ ball 0 R).ncard : ℝ) ≤ M * (π * R ^ 2)

/-- **Admissible fields (1.1).** The field `E` is the electric field of unit charges at the points
of the locally finite set `C` in a neutralizing background of density one:
`div E = 2π (∑_{p ∈ C} δ_p - 1)` and `curl E = 0` in the sense of distributions, and `C` has
bounded density. -/
structure IsAdmissible (C : Set Plane) (E : Plane → Plane) : Prop where
  locallyFinite : IsLocallyFinite C
  boundedDensity : HasBoundedDensity C
  locallyIntegrable : LocallyIntegrable E volume
  div_eq : ∀ φ : Plane → ℝ, IsTestFunction φ →
    -∫ x, (E x 0 * partialDeriv 0 φ x + E x 1 * partialDeriv 1 φ x) =
      2 * π * ((∑ᶠ p ∈ C, φ p) - ∫ x, φ x)
  curl_eq : ∀ φ : Plane → ℝ, IsTestFunction φ →
    ∫ x, (E x 0 * partialDeriv 1 φ x - E x 1 * partialDeriv 0 φ x) = 0

/-- The truncated energy inside the limit (1.2):
`½ ∫_{ℝ² ∖ ⋃_p B(p, η)} χ |E|² + π log η ∑_p χ(p)`. -/
noncomputable def truncatedEnergy (C : Set Plane) (E : Plane → Plane) (χ : Plane → ℝ)
    (η : ℝ) : ℝ :=
  (1 / 2) * (∫ x in (⋃ p ∈ C, ball p η)ᶜ, χ x * ‖E x‖ ^ 2) + π * Real.log η * ∑ᶠ p ∈ C, χ p

/-- **The renormalized energy with weight `χ` (1.2)**, `W(E, χ)`, the limit of the truncated
energy as `η ↓ 0`. -/
noncomputable def renormalizedEnergy (C : Set Plane) (E : Plane → Plane) (χ : Plane → ℝ) : ℝ :=
  limUnder (𝓝[>] 0) (truncatedEnergy C E χ)

/-- The open disc `B_R` of radius `R` centred at the origin. -/
def discRegion (R : ℝ) : Set Plane :=
  ball 0 R

/-- The open square `(-R/2, R/2)²` of side `R` centred at the origin. -/
def squareRegion (R : ℝ) : Set Plane :=
  {x | |x 0| < R / 2 ∧ |x 1| < R / 2}

/-- **Cutoff families of width `L` (before (1.3)).** For every size `R`, `χ R` is supported in
`U R`, equals one at distance at least `L` from `∂(U R)`, and takes values in `[0, 1]`; the
functions `χ R` have a common Lipschitz constant, that is, uniformly bounded gradients. -/
structure IsCutoffFamily (U : ℝ → Set Plane) (L : ℝ) (χ : ℝ → Plane → ℝ) : Prop where
  lipschitz : ∃ K, ∀ R, LipschitzWith K (χ R)
  nonneg : ∀ R x, 0 ≤ χ R x
  le_one : ∀ R x, χ R x ≤ 1
  tsupport_subset : ∀ R, tsupport (χ R) ⊆ U R
  eq_one : ∀ R, ∀ x ∈ U R, L ≤ infDist x (frontier (U R)) → χ R x = 1

/-- **The renormalized energy per unit area (1.3)**,
`W_U(E) = limsup_{R → ∞} W(E, χ_R) / |U_R|`, computed with the cutoff family `χ` adapted to the
regions `U`, with values in `EReal`. -/
noncomputable def energyPerArea (U : ℝ → Set Plane) (χ : ℝ → Plane → ℝ) (C : Set Plane)
    (E : Plane → Plane) : EReal :=
  limsup (fun R : ℝ => ((renormalizedEnergy C E (χ R) / volume.real (U R) : ℝ) : EReal)) atTop

/-- The lattice spacing `ℓ = (2/√3)^{1/2}`, for which the triangular lattice has covolume one. -/
noncomputable def latticeSpacing : ℝ :=
  √(2 / √3)

/-- **The triangular lattice of covolume one**, `Λ = ℓ [ℤ (1, 0) + ℤ (1/2, √3/2)]`. -/
noncomputable def triangularLattice : Set Plane :=
  {x | ∃ a b : ℤ, x = latticeSpacing • !₂[(a : ℝ) + b / 2, b * √3 / 2]}

/-- The fundamental cell `{ℓ (s (1, 0) + t (1/2, √3/2)) : 0 ≤ s, t < 1}` of `Λ`. -/
noncomputable def fundamentalCell : Set Plane :=
  {x | ∃ s ∈ Ico (0 : ℝ) 1, ∃ t ∈ Ico (0 : ℝ) 1, x = latticeSpacing • !₂[s + t / 2, t * √3 / 2]}

/-- **The canonical field of the triangular lattice (Definition 2.1).** A `Λ`-periodic field
satisfying (1.1) for the configuration `Λ`, with zero average over a period cell. -/
structure IsCanonicalField (E : Plane → Plane) : Prop where
  admissible : IsAdmissible triangularLattice E
  periodic : ∀ v ∈ triangularLattice, ∀ x, E (x + v) = E x
  average_eq_zero : ∫ x in fundamentalCell, E x = 0

/-- **The Green function of the triangular torus (2.3).** A `Λ`-periodic locally integrable
function, continuous off `Λ`, with zero average over a period cell and
`-ΔG = 2π (∑_{λ ∈ Λ} δ_λ - 1)` in the sense of distributions. -/
structure IsGreenFunction (G : Plane → ℝ) : Prop where
  locallyIntegrable : LocallyIntegrable G volume
  continuousOn : ContinuousOn G triangularLatticeᶜ
  periodic : ∀ v ∈ triangularLattice, ∀ x, G (x + v) = G x
  average_eq_zero : ∫ x in fundamentalCell, G x = 0
  laplacian_eq : ∀ φ : Plane → ℝ, IsTestFunction φ →
    -∫ x, G x * Δ φ x = 2 * π * ((∑ᶠ v ∈ triangularLattice, φ v) - ∫ x, φ x)

/-- **The Robin constant** `R_Λ = lim_{x → 0} (G(x) + log |x|)` of the Green function `G`. -/
noncomputable def robinConstant (G : Plane → ℝ) : ℝ :=
  limUnder (𝓝[≠] 0) fun x => G x + Real.log ‖x‖

/-- The canonical field of the triangular lattice exists. -/
theorem exists_isCanonicalField : ∃ E : Plane → Plane, IsCanonicalField E := by
  sorry

/-- The Green function of the triangular torus exists. -/
theorem exists_isGreenFunction : ∃ G : Plane → ℝ, IsGreenFunction G := by
  sorry

/-- **Theorem 1.1, value.** For discs or squares and every cutoff family of width `L > 0`, the
renormalized energy per unit area of the canonical field is `W_U(E_Λ) = π R_Λ`. -/
theorem energyPerArea_canonicalField (U : ℝ → Set Plane) (hU : U = discRegion ∨ U = squareRegion)
    (L : ℝ) (hL : 0 < L) (χ : ℝ → Plane → ℝ) (hχ : IsCutoffFamily U L χ)
    (E₀ : Plane → Plane) (hE₀ : IsCanonicalField E₀) (G : Plane → ℝ) (hG : IsGreenFunction G) :
    energyPerArea U χ triangularLattice E₀ = ((π * robinConstant G : ℝ) : EReal) := by
  sorry

/-- **Theorem 1.1, the triangular lattice minimizes the renormalized energy.** For discs or
squares and every cutoff family of width `L > 0`, every field `E` satisfying (1.1) obeys
`W_U(E) ≥ W_U(E_Λ)`. -/
theorem energyPerArea_canonicalField_le (U : ℝ → Set Plane)
    (hU : U = discRegion ∨ U = squareRegion) (L : ℝ) (hL : 0 < L) (χ : ℝ → Plane → ℝ)
    (hχ : IsCutoffFamily U L χ) (E₀ : Plane → Plane) (hE₀ : IsCanonicalField E₀)
    (C : Set Plane) (E : Plane → Plane) (hE : IsAdmissible C E) :
    energyPerArea U χ triangularLattice E₀ ≤ energyPerArea U χ C E := by
  sorry

end TriangularLattice
