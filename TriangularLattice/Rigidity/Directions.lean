/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import TriangularLattice.Statement

/-!
# Directions in the plane

Elementary plane geometry used in Section 5: unit vectors `e_φ = (cos φ, sin φ)`, directions of
vectors as elements of `Real.Angle`, the slot directions `θ + jπ/3`, and the conversion of
estimates on cosines into estimates on angles.

## Representation of angles

A direction is an element of `Real.Angle = ℝ / 2πℤ`. This group carries the quotient norm, and
`‖θ‖ = |θ.toReal|` is the unoriented angle represented by `θ`, so that the unoriented angle
`InnerProductGeometry.angle v w` between nonzero vectors equals `‖dir v - dir w‖`
(`angle_eq_norm_dir_sub`). The triangle inequality for this norm is used for all angular
estimates. Orientations `θ_p` are real numbers, and slot `j : Fin 6` at orientation `θ` has the
direction `slotAngle θ j = θ + jπ/3`.

## Main definitions

* `TriangularLattice.toComplex`: the isometry `ℝ² ≃ ℂ`, `x ↦ x 0 + x 1 i`.
* `TriangularLattice.unitVec φ`: the unit vector `e_φ = (cos φ, sin φ)`.
* `TriangularLattice.vecArg v`, `TriangularLattice.dir v`: the argument of `v` in `(-π, π]` and
  the direction of `v` in `Real.Angle`.
* `TriangularLattice.slotAngle θ j`: the slot direction `θ + jπ/3`.

## Main results

* `TriangularLattice.angle_eq_norm_dir_sub`: `∠(v, w) = ‖dir v - dir w‖`.
* `TriangularLattice.norm_unitVec_sub_unitVec_le`: chord length is at most arc length.
* `TriangularLattice.abs_sub_le_of_abs_cos_sub_le`, `TriangularLattice.pi_sub_le_of_cos_le`:
  angles from cosines near `π/3`, `2π/3` and `π`.
-/

@[expose] public section

open Real InnerProductGeometry
open scoped RealInnerProductSpace

/-! ### The norm on `Real.Angle` -/

namespace Real.Angle

/-- The norm of an angle is the absolute value of its representative in `(-π, π]`. -/
theorem norm_eq_abs_toReal (θ : Angle) : ‖θ‖ = |θ.toReal| := by
  conv_lhs => rw [← θ.coe_toReal]
  refine (AddCircle.norm_coe_eq_abs_iff (2 * π) (by positivity)).2 ?_
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  linarith [θ.abs_toReal_le_pi]

/-- The norm of the angle represented by a real number is at most its absolute value. -/
theorem norm_coe_le_abs (x : ℝ) : ‖(x : Angle)‖ ≤ |x| :=
  QuotientAddGroup.norm_mk_le_norm

/-- The norm of the angle represented by `x` is `|x|` when `|x| ≤ π`. -/
theorem norm_coe_of_abs_le {x : ℝ} (hx : |x| ≤ π) : ‖(x : Angle)‖ = |x| := by
  refine (AddCircle.norm_coe_eq_abs_iff (2 * π) (by positivity)).2 ?_
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  linarith

/-- The norm of an angle is at most `π`. -/
theorem norm_le_pi (θ : Angle) : ‖θ‖ ≤ π := by
  rw [norm_eq_abs_toReal]
  exact θ.abs_toReal_le_pi

/-- The cosine of the norm of an angle is the cosine of the angle. -/
theorem cos_norm (θ : Angle) : Real.cos ‖θ‖ = θ.cos := by
  rw [norm_eq_abs_toReal, Real.cos_abs, cos_toReal]

end Real.Angle

namespace TriangularLattice

/-! ### Unit vectors and directions -/

/-- The identification of the plane with `ℂ`, `x ↦ x 0 + x 1 i`. -/
noncomputable def toComplex : Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

@[simp]
theorem toComplex_apply (x : Plane) : toComplex x = x 0 + x 1 * Complex.I := by
  simp [toComplex]

/-- The unit vector `e_φ = (cos φ, sin φ)`. -/
noncomputable def unitVec (φ : ℝ) : Plane :=
  !₂[Real.cos φ, Real.sin φ]

@[simp]
theorem unitVec_apply_zero (φ : ℝ) : unitVec φ 0 = Real.cos φ := by
  simp [unitVec]

@[simp]
theorem unitVec_apply_one (φ : ℝ) : unitVec φ 1 = Real.sin φ := by
  simp [unitVec]

/-- The inner product on the plane in coordinates. -/
theorem inner_eq_coord (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The squared norm on the plane in coordinates. -/
theorem norm_sq_eq_coord (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

theorem toComplex_unitVec (φ : ℝ) : toComplex (unitVec φ) = Complex.exp (φ * Complex.I) := by
  rw [Complex.exp_mul_I, toComplex_apply, unitVec_apply_zero, unitVec_apply_one,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

@[simp]
theorem norm_unitVec (φ : ℝ) : ‖unitVec φ‖ = 1 := by
  rw [← toComplex.norm_map, toComplex_unitVec, Complex.norm_exp_ofReal_mul_I]

theorem unitVec_ne_zero (φ : ℝ) : unitVec φ ≠ 0 := by
  intro h
  simpa [h] using norm_unitVec φ

theorem inner_unitVec_unitVec (α β : ℝ) :
    ⟪unitVec α, unitVec β⟫ = Real.cos (α - β) := by
  rw [inner_eq_coord, Real.cos_sub]
  simp

/-- `e_{α + β} = cos β e_α + sin β e_{α + π/2}`. -/
theorem unitVec_add (α β : ℝ) :
    unitVec (α + β) = Real.cos β • unitVec α + Real.sin β • unitVec (α + π / 2) := by
  ext i
  fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring

theorem unitVec_add_pi (φ : ℝ) : unitVec (φ + π) = -unitVec φ := by
  ext i
  fin_cases i <;> simp

/-- `e_φ` depends only on the angle represented by `φ`. -/
theorem unitVec_eq_of_coe_eq {α β : ℝ} (h : (α : Angle) = β) : unitVec α = unitVec β := by
  ext i
  fin_cases i
  · simpa using congrArg Angle.cos h
  · simpa using congrArg Angle.sin h

/-- The argument of a vector of the plane, in `(-π, π]`. -/
noncomputable def vecArg (v : Plane) : ℝ :=
  Complex.arg (toComplex v)

/-- The direction of a vector of the plane, as an angle (`0` for the zero vector). -/
noncomputable def dir (v : Plane) : Angle :=
  (vecArg v : Angle)

/-- Polar decomposition: `v = ‖v‖ e_{arg v}`. -/
theorem norm_smul_unitVec_vecArg (v : Plane) : ‖v‖ • unitVec (vecArg v) = v := by
  apply toComplex.injective
  rw [map_smul, toComplex_unitVec, vecArg, ← toComplex.norm_map, Complex.real_smul,
    Complex.norm_mul_exp_arg_mul_I]

theorem dir_smul_unitVec {r : ℝ} (hr : 0 < r) (φ : ℝ) : dir (r • unitVec φ) = φ := by
  rw [dir, vecArg, map_smul, toComplex_unitVec, Complex.real_smul, Complex.arg_real_mul _ hr,
    Complex.arg_exp_mul_I, Angle.coe_toIocMod]

@[simp]
theorem dir_unitVec (φ : ℝ) : dir (unitVec φ) = φ := by
  simpa using dir_smul_unitVec one_pos φ

theorem dir_smul_of_pos {r : ℝ} (hr : 0 < r) (v : Plane) : dir (r • v) = dir v := by
  conv_lhs => rw [← norm_smul_unitVec_vecArg v, smul_smul]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact dir_smul_unitVec (mul_pos hr (norm_pos_iff.2 hv)) _

theorem dir_neg {v : Plane} (hv : v ≠ 0) : dir (-v) = dir v + π := by
  rw [dir, dir, vecArg, vecArg, map_neg,
    Complex.arg_neg_coe_angle (by rwa [Ne, LinearIsometryEquiv.map_eq_zero_iff])]

/-- If `v = r e_φ` with `r > 0` then the direction of `v` is `φ`. -/
theorem dir_eq_of_eq_smul {v : Plane} {r φ : ℝ} (hr : 0 < r) (h : v = r • unitVec φ) :
    dir v = φ := by
  rw [h, dir_smul_unitVec hr]

/-- The unoriented angle between nonzero vectors is the norm of the difference of their
directions. -/
theorem angle_eq_norm_dir_sub {v w : Plane} (hv : v ≠ 0) (hw : w ≠ 0) :
    angle v w = ‖dir v - dir w‖ := by
  have hv' : toComplex v ≠ 0 := by rwa [Ne, LinearIsometryEquiv.map_eq_zero_iff]
  have hw' : toComplex w ≠ 0 := by rwa [Ne, LinearIsometryEquiv.map_eq_zero_iff]
  rw [← toComplex.toLinearIsometry.angle_map, LinearIsometryEquiv.coe_toLinearIsometry,
    Complex.angle_eq_abs_arg hv' hw', dir, dir, vecArg, vecArg,
    ← Complex.arg_div_coe_angle hv' hw', Angle.norm_coe_of_abs_le (Complex.abs_arg_le_pi _)]

theorem angle_unitVec_unitVec (α β : ℝ) :
    angle (unitVec α) (unitVec β) = ‖(α : Angle) - β‖ := by
  rw [angle_eq_norm_dir_sub (unitVec_ne_zero α) (unitVec_ne_zero β), dir_unitVec, dir_unitVec]

theorem angle_unitVec_right {v : Plane} (hv : v ≠ 0) (φ : ℝ) :
    angle v (unitVec φ) = ‖dir v - φ‖ := by
  rw [angle_eq_norm_dir_sub hv (unitVec_ne_zero φ), dir_unitVec]

/-- Chord length is at most arc length: `‖e_α - e_β‖ ≤ ‖α - β‖`. -/
theorem norm_unitVec_sub_unitVec_le (α β : ℝ) :
    ‖unitVec α - unitVec β‖ ≤ ‖(α : Angle) - β‖ := by
  rw [← angle_unitVec_unitVec, ← toComplex.norm_map, map_sub,
    ← toComplex.toLinearIsometry.angle_map, LinearIsometryEquiv.coe_toLinearIsometry]
  exact Complex.norm_sub_le_angle (by simp) (by simp)

/-- `‖r e_φ - ℓ e_ψ‖ ≤ |r - ℓ| + ℓ ‖φ - ψ‖` for `ℓ ≥ 0`. -/
theorem norm_smul_unitVec_sub_le {r s : ℝ} (hs : 0 ≤ s) (φ ψ : ℝ) :
    ‖r • unitVec φ - s • unitVec ψ‖ ≤ |r - s| + s * ‖(φ : Angle) - ψ‖ := by
  have : r • unitVec φ - s • unitVec ψ = (r - s) • unitVec φ + s • (unitVec φ - unitVec ψ) := by
    simp only [sub_smul, smul_sub]
    abel
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, norm_unitVec, mul_one, Real.norm_eq_abs]
  · rw [norm_smul, Real.norm_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (norm_unitVec_sub_unitVec_le φ ψ) hs

/-! ### Slot directions -/

/-- The direction `θ + jπ/3` of slot `j` at orientation `θ`. -/
noncomputable def slotAngle (θ : ℝ) (j : Fin 6) : ℝ :=
  θ + (j : ℕ) * (π / 3)

/-- The cosines `cos (jπ/3)` of the slot offsets. -/
noncomputable def slotCos : Fin 6 → ℝ :=
  ![1, 1 / 2, -1 / 2, -1, -1 / 2, 1 / 2]

/-- The sines `sin (jπ/3)` of the slot offsets. -/
noncomputable def slotSin : Fin 6 → ℝ :=
  ![0, √3 / 2, √3 / 2, 0, -(√3 / 2), -(√3 / 2)]

theorem cos_slotOffset (j : Fin 6) : Real.cos ((j : ℕ) * (π / 3)) = slotCos j := by
  fin_cases j
  · norm_num [slotCos]
  · norm_num [slotCos]
  · rw [show ((2 : ℕ) : ℝ) * (π / 3) = π - π / 3 by push_cast; ring, Real.cos_pi_sub]
    norm_num [slotCos]
  · rw [show ((3 : ℕ) : ℝ) * (π / 3) = π by push_cast; ring]
    norm_num [slotCos]
  · rw [show ((4 : ℕ) : ℝ) * (π / 3) = π / 3 + π by push_cast; ring, Real.cos_add_pi]
    norm_num [slotCos]
  · rw [show ((5 : ℕ) : ℝ) * (π / 3) = -(π / 3) + 2 * π by push_cast; ring,
      Real.cos_add_two_pi, Real.cos_neg]
    norm_num [slotCos]

theorem sin_slotOffset (j : Fin 6) : Real.sin ((j : ℕ) * (π / 3)) = slotSin j := by
  fin_cases j
  · simp [slotSin]
  · simp [slotSin]
  · rw [show ((2 : ℕ) : ℝ) * (π / 3) = π - π / 3 by push_cast; ring, Real.sin_pi_sub]
    simp [slotSin]
  · rw [show ((3 : ℕ) : ℝ) * (π / 3) = π by push_cast; ring]
    simp [slotSin]
  · rw [show ((4 : ℕ) : ℝ) * (π / 3) = π / 3 + π by push_cast; ring, Real.sin_add_pi]
    simp [slotSin]
  · rw [show ((5 : ℕ) : ℝ) * (π / 3) = -(π / 3) + 2 * π by push_cast; ring,
      Real.sin_add_two_pi, Real.sin_neg]
    simp [slotSin]

/-- The slot vector `e_{θ + jπ/3}` in the frame `(e_θ, e_{θ + π/2})`. -/
theorem unitVec_slotAngle (θ : ℝ) (j : Fin 6) :
    unitVec (slotAngle θ j) = slotCos j • unitVec θ + slotSin j • unitVec (θ + π / 2) := by
  rw [slotAngle, unitVec_add, cos_slotOffset, sin_slotOffset]

/-- Consecutive slot directions differ by `π/3`, also from slot `5` to slot `0`. -/
theorem coe_slotAngle_add_one (θ : ℝ) (j : Fin 6) :
    (slotAngle θ (j + 1) : Angle) = slotAngle θ j + (π / 3 : ℝ) := by
  rw [← Angle.coe_add, Angle.angle_eq_iff_two_pi_dvd_sub]
  fin_cases j
  · exact ⟨0, by simp [slotAngle]⟩
  · exact ⟨0, by simp [slotAngle]; ring⟩
  · exact ⟨0, by simp [slotAngle]; ring⟩
  · exact ⟨0, by simp [slotAngle]; ring⟩
  · exact ⟨0, by simp [slotAngle]; ring⟩
  · exact ⟨-1, by simp [slotAngle]; ring⟩

/-- `slotAngle θ 0 = θ`. -/
@[simp]
theorem slotAngle_zero (θ : ℝ) : slotAngle θ 0 = θ := by
  simp [slotAngle]

/-- The slot directions of distinct slots are distinct angles. -/
theorem coe_slotAngle_ne {θ : ℝ} {i j : Fin 6} (hij : i ≠ j) :
    (slotAngle θ i : Angle) ≠ slotAngle θ j := by
  intro h
  rw [Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  have hk' : ((i : ℕ) : ℝ) - (j : ℕ) = 6 * k := by
    have h0 : (((i : ℕ) : ℝ) - (j : ℕ) - 6 * k) * π = 0 := by
      simp only [slotAngle] at hk
      linear_combination 3 * hk
    rcases mul_eq_zero.1 h0 with h0 | h0
    · linarith
    · exact absurd h0 Real.pi_ne_zero
  have hk'' : ((i : ℕ) : ℤ) - (j : ℕ) = 6 * k := by exact_mod_cast hk'
  have hi := i.isLt
  have hj := j.isLt
  apply hij
  ext
  omega

/-- Every integer multiple of `π/3` added to `θ` is a slot direction. -/
theorem exists_slotAngle_eq (θ : ℝ) (s : ℤ) :
    ∃ j : Fin 6, (slotAngle θ j : Angle) = (θ + s * (π / 3) : ℝ) := by
  refine ⟨⟨(s % 6).toNat, by omega⟩, ?_⟩
  rw [Angle.angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-(s / 6), ?_⟩
  have h1 : ((s % 6).toNat : ℤ) = s % 6 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have h2 : s % 6 + 6 * (s / 6) = s := Int.emod_add_mul_ediv s 6
  have h3 : (((s % 6).toNat : ℕ) : ℝ) = (s : ℝ) - 6 * ((s / 6 : ℤ) : ℝ) := by
    have : (((s % 6).toNat : ℕ) : ℤ) = s - 6 * (s / 6) := by omega
    exact_mod_cast this
  simp only [slotAngle, h3]
  push_cast
  ring

/-- If `|ψ|` is within `η` of `kπ/3` with `k ∈ ℕ`, then `θ + ψ` is within `η` of a slot direction
at orientation `θ`. -/
theorem exists_norm_coe_sub_slotAngle_le (θ ψ η : ℝ) (k : ℕ)
    (h : |(|ψ| - k * (π / 3))| ≤ η) :
    ∃ j : Fin 6, ‖((θ + ψ : ℝ) : Angle) - slotAngle θ j‖ ≤ η := by
  rcases le_or_gt 0 ψ with hψ | hψ
  · obtain ⟨j, hj⟩ := exists_slotAngle_eq θ k
    refine ⟨j, ?_⟩
    rw [hj, ← Angle.coe_sub]
    refine (Angle.norm_coe_le_abs _).trans ?_
    rw [abs_of_nonneg hψ] at h
    convert h using 2
    push_cast
    ring
  · obtain ⟨j, hj⟩ := exists_slotAngle_eq θ (-k)
    refine ⟨j, ?_⟩
    rw [hj, ← Angle.coe_sub]
    refine (Angle.norm_coe_le_abs _).trans ?_
    rw [abs_of_neg hψ, ← abs_neg] at h
    convert h using 2
    push_cast
    ring

/-! ### Angles from cosines -/

/-- If `cos d` is within `δ ≤ 1/100` of `cos d₀`, where `sin d₀ = √3/2` and `|cos d₀| ≤ 1/2`
(that is, `d₀ = π/3` or `2π/3`), then `d` is within `3δ/2` of `d₀`. -/
theorem abs_sub_le_of_abs_cos_sub_le {d d₀ δ : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ π)
    (hs : Real.sin d₀ = √3 / 2) (hc : |Real.cos d₀| ≤ 1 / 2) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 100)
    (hlo : 0 ≤ d₀ - 3 / 2 * δ) (hhi : d₀ + 3 / 2 * δ ≤ π)
    (h : |Real.cos d - Real.cos d₀| ≤ δ) : |d - d₀| ≤ 3 / 2 * δ := by
  set t := 3 / 2 * δ with ht
  have ht0 : 0 ≤ t := by positivity
  have hsqrt : (1.732 : ℝ) < √3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hcos : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
  have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
  have hsin : t - t ^ 3 / 6 ≤ Real.sin t := Real.sin_ge_sub_cube ht0
  have hcd : |Real.cos d₀ * Real.cos t - Real.cos d₀| ≤ t ^ 2 / 4 := by
    rw [← mul_sub_one, abs_mul]
    calc |Real.cos d₀| * |Real.cos t - 1| ≤ 1 / 2 * (t ^ 2 / 2) := by
          gcongr
          rw [abs_of_nonpos (by linarith)]
          linarith
      _ = t ^ 2 / 4 := by ring
  have hpoly : 0 ≤ t - t ^ 3 / 6 := by nlinarith
  have hsin' : 0.866 * (t - t ^ 3 / 6) ≤ √3 / 2 * Real.sin t :=
    calc 0.866 * (t - t ^ 3 / 6) ≤ √3 / 2 * (t - t ^ 3 / 6) :=
          mul_le_mul_of_nonneg_right (by linarith) hpoly
      _ ≤ √3 / 2 * Real.sin t := mul_le_mul_of_nonneg_left hsin (by positivity)
  have key : δ ≤ 0.866 * (t - t ^ 3 / 6) - t ^ 2 / 4 := by
    rw [ht]
    nlinarith [mul_nonneg hδ₀ hδ₀, mul_nonneg (mul_nonneg hδ₀ hδ₀) hδ₀]
  rw [abs_le] at h hcd
  rw [abs_le]
  constructor
  · by_contra hlt
    push Not at hlt
    have hlt' : Real.cos (d₀ - t) < Real.cos d :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hd₀ (by linarith) (by linarith)
    rw [Real.cos_sub, hs] at hlt'
    linarith
  · by_contra hlt
    push Not at hlt
    have hlt' : Real.cos d < Real.cos (d₀ + t) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) hd₁ (by linarith)
    rw [Real.cos_add, hs] at hlt'
    linarith

/-- If `cos d ≤ -1 + δ` with `δ < t²/2 - 5t⁴/96` and `0 ≤ t ≤ 1`, then `d ≥ π - t`. -/
theorem pi_sub_le_of_cos_le {d δ t : ℝ} (hd₀ : 0 ≤ d) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hδ : δ < t ^ 2 / 2 - 5 / 96 * t ^ 4) (h : Real.cos d ≤ -1 + δ) : π - d ≤ t := by
  by_contra hlt
  push Not at hlt
  have hlt' : Real.cos (π - t) < Real.cos d :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hd₀ (by linarith) (by linarith)
  rw [Real.cos_pi_sub] at hlt'
  have hb := Real.cos_bound (x := t) (by rw [abs_of_nonneg ht₀]; exact ht₁)
  rw [abs_of_nonneg ht₀, abs_le] at hb
  nlinarith

end TriangularLattice
