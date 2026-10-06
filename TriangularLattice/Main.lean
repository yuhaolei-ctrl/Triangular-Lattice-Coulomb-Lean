/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Statement

/-!
# Theorem 1.1

The four statements of `Challenge.lean`. This file assembles results of the development; while
the development is in progress, the missing steps are marked with `sorry`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set Real

namespace TriangularLattice

theorem exists_isCanonicalField_main : ∃ E : Plane → Plane, IsCanonicalField E := by
  sorry

theorem exists_isGreenFunction_main : ∃ G : Plane → ℝ, IsGreenFunction G := by
  sorry

theorem energyPerArea_canonicalField_main (U : ℝ → Set Plane)
    (hU : U = discRegion ∨ U = squareRegion) (L : ℝ) (hL : 0 < L) (χ : ℝ → Plane → ℝ)
    (hχ : IsCutoffFamily U L χ) (E₀ : Plane → Plane) (hE₀ : IsCanonicalField E₀)
    (G : Plane → ℝ) (hG : IsGreenFunction G) :
    energyPerArea U χ triangularLattice E₀ = ((π * robinConstant G : ℝ) : EReal) := by
  sorry

theorem energyPerArea_canonicalField_le_main (U : ℝ → Set Plane)
    (hU : U = discRegion ∨ U = squareRegion) (L : ℝ) (hL : 0 < L) (χ : ℝ → Plane → ℝ)
    (hχ : IsCutoffFamily U L χ) (E₀ : Plane → Plane) (hE₀ : IsCanonicalField E₀)
    (C : Set Plane) (E : Plane → Plane) (hE : IsAdmissible C E) :
    energyPerArea U χ triangularLattice E₀ ≤ energyPerArea U χ C E := by
  sorry

end TriangularLattice
