/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Rigidity.Directions

/-!
# The regular hexagon of unit area

The hexagon `H_θ` of Section 5.3 of the manuscript: the regular hexagon centred at `0` with
outward face normals `e_{θ + jπ/3}`, `j = 0, …, 5`, apothem `ℓ/2` and circumradius `ℓ/√3`. It is
defined as the open set

`H_θ = {x | ⟪x, e_{θ + jπ/3}⟫ < ℓ/2 for j = 0, …, 5}`,

and `hexCell c r θ = c + r H_θ`.

## Main definitions

* `TriangularLattice.hexagon θ`: the open hexagon `H_θ`.
* `TriangularLattice.hexCell c r θ`: the scaled translate `c + r H_θ`.

## Main results

* `TriangularLattice.norm_lt_of_forall_inner_lt`: the circumradius bound `|x| < ℓ/√3` on `H_θ`.
* `TriangularLattice.mem_hexCell_iff`: membership in `c + r H_θ` by the six face inequalities.
* `TriangularLattice.inner_sub_lt_of_mem_hexCell`: the support function of `c + r H_θ` in a
  direction `u` near the face normal `n` is less than `r (ℓ/2 + (ℓ/√3) |u - n|)`.
-/

@[expose] public section

open Real InnerProductGeometry
open scoped RealInnerProductSpace Pointwise

namespace TriangularLattice

/-- The regular hexagon `H_θ` of unit area centred at `0`, with outward face normals
`e_{θ + jπ/3}` (`j = 0, …, 5`) and apothem `ℓ/2`, as an open set. -/
noncomputable def hexagon (θ : ℝ) : Set Plane :=
  {x | ∀ j : Fin 6, ⟪x, unitVec (slotAngle θ j)⟫ < latticeSpacing / 2}

/-- The scaled translated hexagon `c + r H_θ`. -/
noncomputable def hexCell (c : Plane) (r θ : ℝ) : Set Plane :=
  c +ᵥ r • hexagon θ

theorem mem_hexagon {x : Plane} {θ : ℝ} :
    x ∈ hexagon θ ↔ ∀ j : Fin 6, ⟪x, unitVec (slotAngle θ j)⟫ < latticeSpacing / 2 :=
  Iff.rfl

/-- The inner product with a slot vector in the frame `(e_θ, e_{θ + π/2})`. -/
theorem inner_unitVec_slotAngle (x : Plane) (θ : ℝ) (j : Fin 6) :
    ⟪x, unitVec (slotAngle θ j)⟫ =
      slotCos j * ⟪x, unitVec θ⟫ + slotSin j * ⟪x, unitVec (θ + π / 2)⟫ := by
  rw [unitVec_slotAngle, inner_add_right, inner_smul_right, inner_smul_right]

/-- The squared norm in the orthonormal frame `(e_θ, e_{θ + π/2})`. -/
theorem norm_sq_eq_inner_sq_add_inner_sq (x : Plane) (θ : ℝ) :
    ‖x‖ ^ 2 = ⟪x, unitVec θ⟫ ^ 2 + ⟪x, unitVec (θ + π / 2)⟫ ^ 2 := by
  rw [norm_sq_eq_coord, inner_eq_coord, inner_eq_coord]
  simp only [unitVec_apply_zero, unitVec_apply_one, Real.cos_add_pi_div_two,
    Real.sin_add_pi_div_two]
  linear_combination (x 0 ^ 2 + x 1 ^ 2) * (Real.cos_sq_add_sin_sq θ).symm

private theorem sq_sub_mul_add_sq_lt {u v a : ℝ} (hu : |u| < a) (hv : |v| < a)
    (huv : |u - v| < a) : u ^ 2 - u * v + v ^ 2 < a ^ 2 := by
  rw [abs_lt] at hu hv huv
  rcases le_total 0 (u * v) with h | h
  · rcases le_total |v| |u| with h' | h'
    · have : v ^ 2 ≤ u * v := by
        have := abs_mul_abs_self v
        have := abs_mul_abs_self u
        nlinarith [abs_nonneg u, abs_nonneg v, abs_mul u v, abs_of_nonneg h]
      nlinarith
    · have : u ^ 2 ≤ u * v := by
        nlinarith [abs_nonneg u, abs_nonneg v, abs_mul u v, abs_of_nonneg h,
          abs_mul_abs_self v, abs_mul_abs_self u]
      nlinarith
  · nlinarith

/-- **Circumradius.** If all six face inequalities `⟪x, e_{θ + jπ/3}⟫ < a` hold, then
`‖x‖ < 2a/√3`. For `a = ℓ/2` this says that `H_θ` lies in the open disc of radius `ℓ/√3`. -/
theorem norm_lt_of_forall_inner_lt {x : Plane} {θ a : ℝ}
    (h : ∀ j : Fin 6, ⟪x, unitVec (slotAngle θ j)⟫ < a) : ‖x‖ < 2 * a / √3 := by
  set A := ⟪x, unitVec θ⟫
  set B := ⟪x, unitVec (θ + π / 2)⟫
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 : 0 < √3 := by positivity
  have hc := fun j => (inner_unitVec_slotAngle x θ j).symm ▸ h j
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3' := hc 3
  have h4 := hc 4
  have h5 := hc 5
  simp only [slotCos, slotSin] at h0 h1 h2 h3' h4 h5
  norm_num at h0 h1 h2 h3' h4 h5
  set P := A / 2 + √3 / 2 * B with hP
  set M := -A / 2 + √3 / 2 * B with hM
  have hPa : |P| < a := abs_lt.2 ⟨by linarith, by linarith⟩
  have hMa : |M| < a := abs_lt.2 ⟨by linarith, by linarith⟩
  have hPMa : |P - M| < a := abs_lt.2 ⟨by linarith, by linarith⟩
  have ha : 0 < a := (abs_nonneg _).trans_lt hPa
  have key := sq_sub_mul_add_sq_lt hPa hMa hPMa
  have hnorm : 3 * ‖x‖ ^ 2 = 4 * (P ^ 2 - P * M + M ^ 2) := by
    rw [norm_sq_eq_inner_sq_add_inner_sq x θ, hP, hM]
    linear_combination (-B ^ 2) * h3
  have hlt : ‖x‖ ^ 2 < (2 * a / √3) ^ 2 := by
    rw [div_pow, mul_pow, h3]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

theorem norm_lt_of_mem_hexagon {x : Plane} {θ : ℝ} (hx : x ∈ hexagon θ) :
    ‖x‖ < latticeSpacing / √3 := by
  have := norm_lt_of_forall_inner_lt hx
  rwa [mul_div_cancel₀ _ two_ne_zero] at this

theorem zero_mem_hexagon (θ : ℝ) : (0 : Plane) ∈ hexagon θ := by
  intro j
  simp [latticeSpacing]

/-- Membership in `c + r H_θ`, for `r > 0`, by the six face inequalities. -/
theorem mem_hexCell_iff {c x : Plane} {r θ : ℝ} (hr : 0 < r) :
    x ∈ hexCell c r θ ↔
      ∀ j : Fin 6, ⟪x - c, unitVec (slotAngle θ j)⟫ < r * (latticeSpacing / 2) := by
  rw [hexCell, Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne',
    mem_hexagon, vadd_eq_add, neg_add_eq_sub]
  refine forall_congr' fun j => ?_
  rw [inner_smul_left, conj_trivial, inv_mul_lt_iff₀ hr]

/-- Points of `c + r H_θ` lie within `r ℓ/√3` of `c`. -/
theorem norm_sub_lt_of_mem_hexCell {c x : Plane} {r θ : ℝ} (hr : 0 < r)
    (hx : x ∈ hexCell c r θ) : ‖x - c‖ < r * (latticeSpacing / √3) := by
  have := norm_lt_of_forall_inner_lt ((mem_hexCell_iff hr).1 hx)
  rwa [show 2 * (r * (latticeSpacing / 2)) / √3 = r * (latticeSpacing / √3) by ring] at this

/-- The support function of `c + r H_θ` in a direction `u` close to the face normal
`e_{θ + jπ/3}`. -/
theorem inner_sub_lt_of_mem_hexCell {c x : Plane} {r θ : ℝ} (hr : 0 < r)
    (hx : x ∈ hexCell c r θ) (j : Fin 6) (u : Plane) :
    ⟪x - c, u⟫ <
      r * (latticeSpacing / 2 + latticeSpacing / √3 * ‖u - unitVec (slotAngle θ j)‖) := by
  have h1 := (mem_hexCell_iff hr).1 hx j
  have h2 := norm_sub_lt_of_mem_hexCell hr hx
  have h3 : ⟪x - c, u - unitVec (slotAngle θ j)⟫ ≤
      ‖x - c‖ * ‖u - unitVec (slotAngle θ j)‖ := real_inner_le_norm _ _
  have h4 : ‖x - c‖ * ‖u - unitVec (slotAngle θ j)‖ ≤
      r * (latticeSpacing / √3) * ‖u - unitVec (slotAngle θ j)‖ :=
    mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)
  have : ⟪x - c, u⟫ = ⟪x - c, unitVec (slotAngle θ j)⟫ +
      ⟪x - c, u - unitVec (slotAngle θ j)⟫ := by
    rw [inner_sub_right]
    ring
  rw [this]
  nlinarith

end TriangularLattice
