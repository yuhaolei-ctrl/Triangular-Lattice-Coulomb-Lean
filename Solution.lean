/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice

/-!
# Solution: the triangular lattice minimizes the Coulomb renormalized energy

The statements of `Challenge.lean`, proved from the development in `TriangularLattice`. The
definitions they mention come from `TriangularLattice.Statement`, a verbatim copy of those of
`Challenge.lean`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set Real

namespace TriangularLattice

/-- The canonical field of the triangular lattice exists. -/
theorem exists_isCanonicalField : ∃ E : Plane → Plane, IsCanonicalField E :=
  exists_isCanonicalField_main

/-- The Green function of the triangular torus exists. -/
theorem exists_isGreenFunction : ∃ G : Plane → ℝ, IsGreenFunction G :=
  exists_isGreenFunction_main

/-- **Theorem 1.1, value.** For discs or squares and every cutoff family of width `L > 0`, the
renormalized energy per unit area of the canonical field is `W_U(E_Λ) = π R_Λ`. -/
theorem energyPerArea_canonicalField (U : ℝ → Set Plane) (hU : U = discRegion ∨ U = squareRegion)
    (L : ℝ) (hL : 0 < L) (χ : ℝ → Plane → ℝ) (hχ : IsCutoffFamily U L χ)
    (E₀ : Plane → Plane) (hE₀ : IsCanonicalField E₀) (G : Plane → ℝ) (hG : IsGreenFunction G) :
    energyPerArea U χ triangularLattice E₀ = ((π * robinConstant G : ℝ) : EReal) :=
  energyPerArea_canonicalField_main U hU L hL χ hχ E₀ hE₀ G hG

/-- **Theorem 1.1, the triangular lattice minimizes the renormalized energy.** For discs or
squares and every cutoff family of width `L > 0`, every field `E` satisfying (1.1) obeys
`W_U(E) ≥ W_U(E_Λ)`. -/
theorem energyPerArea_canonicalField_le (U : ℝ → Set Plane)
    (hU : U = discRegion ∨ U = squareRegion) (L : ℝ) (hL : 0 < L) (χ : ℝ → Plane → ℝ)
    (hχ : IsCutoffFamily U L χ) (E₀ : Plane → Plane) (hE₀ : IsCanonicalField E₀)
    (C : Set Plane) (E : Plane → Plane) (hE : IsAdmissible C E) :
    energyPerArea U χ triangularLattice E₀ ≤ energyPerArea U χ C E :=
  energyPerArea_canonicalField_le_main U hU L hL χ hχ E₀ hE₀ C E hE

end TriangularLattice
