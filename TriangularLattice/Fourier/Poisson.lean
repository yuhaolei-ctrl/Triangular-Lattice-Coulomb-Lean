/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Basic.Torus
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Poisson summation over a lattice in the plane

For a lattice `Γ` of covolume `N` in the plane, Poisson summation (2.1) of the manuscript reads
`∑_{k ∈ Γ*} 𝓕 f(k) e^{2πi⟪x, k⟫} = N ∑_{v ∈ Γ} f(x + v)`.

## Main results

* `PlaneLattice.hasSum_fourierChar_smul_fourier`: Poisson summation for integrable `f` whose
  periodization is continuous and whose Fourier transform is summable over `Γ*`.
* `PlaneLattice.hasSum_fourierChar_smul_fourier_of_locallyBounded`: the same when `f` is
  continuous and the periodization converges absolutely and locally uniformly (Weierstrass bounds
  on discs).
* `PlaneLattice.hasSum_fourierChar_smul_fourier_of_decay`: the same when `f` and `𝓕 f` decay like
  `(1 + ‖·‖)^(-s)` with `s > 2`.
* `PlaneLattice.hasSum_fourierChar_smul_fourier_of_gaussian`: the same when `f` and `𝓕 f` have
  Gaussian decay, `‖f y‖ ≤ A e^{-c‖y‖²}` (this covers Gaussians times polynomials).
-/

@[expose] public section

open MeasureTheory Metric Set Module Filter Topology
open scoped RealInnerProductSpace FourierTransform

namespace TriangularLattice

/-- Gaussian decay implies polynomial decay: `e^{-c r²} ≤ 8 (1 + 2/c²) (1 + r)^(-4)`. -/
theorem exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    Real.exp (-c * r ^ 2) ≤ 8 * (1 + 2 / c ^ 2) * (1 + r) ^ (-(4 : ℝ)) := by
  have h₁ : (1 + r) ^ 4 ≤ 8 * (1 + r ^ 4) := by
    have : 0 ≤ 7 * r ^ 2 + 10 * r + 7 := by positivity
    nlinarith [mul_nonneg (sq_nonneg (r - 1)) this]
  have h₂ : 1 + r ^ 4 ≤ (1 + 2 / c ^ 2) * Real.exp (c * r ^ 2) := by
    have he := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ c * r ^ 2)
    have hc2 : 0 < c ^ 2 := by positivity
    calc 1 + r ^ 4 ≤ (1 + 2 / c ^ 2) * (1 + c * r ^ 2 + (c * r ^ 2) ^ 2 / 2) := by
          field_simp
          nlinarith [sq_nonneg r, mul_pos hc hc2, pow_nonneg hr 4]
      _ ≤ (1 + 2 / c ^ 2) * Real.exp (c * r ^ 2) := by gcongr
  rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _)]
  nlinarith [Real.exp_pos (c * r ^ 2)]

namespace PlaneLattice

variable (Γ : PlaneLattice)

/-- **Poisson summation (2.1).** Let `f` be integrable, with continuous periodization
`x ↦ ∑_{v ∈ Γ} f(x + v)` and Fourier transform summable over `Γ*`. Then
`∑_{k ∈ Γ*} 𝓕 f(k) 𝐞 ⟪x, k⟫ = covolume Γ · ∑_{v ∈ Γ} f(x + v)` for every `x`. -/
theorem hasSum_fourierChar_smul_fourier {f : Plane → ℂ} (hf : Integrable f)
    (hcont : Continuous fun x ↦ ∑' v : Γ.points, f (x + v))
    (hsum : Summable fun k : Γ.dual.points ↦ 𝓕 f k) (x : Plane) :
    HasSum (fun k : Γ.dual.points ↦ 𝐞 ⟪x, (k : Plane)⟫ • 𝓕 f k)
      (Γ.covolume • ∑' v : Γ.points, f (x + v)) := by
  have hcoeff (k : Γ.dual.points) :
      Γ.fourierCoeff (fun x ↦ ∑' v : Γ.points, f (x + v)) k = 𝓕 f k :=
    Γ.fourierCoeff_tsum_comp_add hf k.2
  have h := (Γ.hasSum_fourierCoeff_smul_fourierChar hcont (Γ.isPeriodic_tsum_comp_add f)
    (hsum.congr fun k ↦ (hcoeff k).symm) x).const_smul Γ.covolume
  simp only [hcoeff, smul_inv_smul₀ Γ.covolume_ne_zero] at h
  exact h

/-- The periodization of a continuous function is continuous if it converges absolutely and
uniformly on every disc. -/
theorem continuous_tsum_comp_add_of_locallyBounded {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {f : Plane → E} (hc : Continuous f)
    (hloc : ∀ R : ℝ, ∃ u : Γ.points → ℝ, Summable u ∧
      ∀ v : Γ.points, ∀ x ∈ closedBall (0 : Plane) R, ‖f (x + v)‖ ≤ u v) :
    Continuous fun x ↦ ∑' v : Γ.points, f (x + v) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  obtain ⟨u, hu, hfu⟩ := hloc (‖x‖ + 1)
  exact (continuousOn_tsum (fun v ↦ (hc.comp (continuous_id.add continuous_const)).continuousOn)
    hu fun v y hy ↦ hfu v y hy).continuousAt (closedBall_mem_nhds_of_mem (by simp))

/-- **Poisson summation** for a continuous integrable `f` whose periodization converges absolutely
and locally uniformly, and whose Fourier transform is summable over `Γ*`. -/
theorem hasSum_fourierChar_smul_fourier_of_locallyBounded {f : Plane → ℂ} (hc : Continuous f)
    (hf : Integrable f)
    (hloc : ∀ R : ℝ, ∃ u : Γ.points → ℝ, Summable u ∧
      ∀ v : Γ.points, ∀ x ∈ closedBall (0 : Plane) R, ‖f (x + v)‖ ≤ u v)
    (hsum : Summable fun k : Γ.dual.points ↦ 𝓕 f k) (x : Plane) :
    HasSum (fun k : Γ.dual.points ↦ 𝐞 ⟪x, (k : Plane)⟫ • 𝓕 f k)
      (Γ.covolume • ∑' v : Γ.points, f (x + v)) :=
  Γ.hasSum_fourierChar_smul_fourier hf (Γ.continuous_tsum_comp_add_of_locallyBounded hc hloc)
    hsum x

/-- A continuous function with `‖f y‖ ≤ A (1 + ‖y‖)^(-s)`, `s > 2`, is integrable. -/
theorem integrable_of_le_one_add_norm_rpow {E : Type*} [NormedAddCommGroup E] {f : Plane → E}
    (hc : Continuous f) {A s : ℝ} (hs : 2 < s) (hf : ∀ y, ‖f y‖ ≤ A * (1 + ‖y‖) ^ (-s)) :
    Integrable f :=
  ((integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; exact_mod_cast hs)).const_mul
    A).mono' hc.aestronglyMeasurable (Eventually.of_forall hf)

/-- **Poisson summation** for a continuous `f` such that `f` and `𝓕 f` decay like
`(1 + ‖·‖)^(-s)` and `(1 + ‖·‖)^(-t)` with `s, t > 2`. -/
theorem hasSum_fourierChar_smul_fourier_of_decay {f : Plane → ℂ} (hc : Continuous f) {A s : ℝ}
    (hs : 2 < s) (hf : ∀ y, ‖f y‖ ≤ A * (1 + ‖y‖) ^ (-s)) {B t : ℝ} (ht : 2 < t)
    (hF : ∀ k, ‖𝓕 f k‖ ≤ B * (1 + ‖k‖) ^ (-t)) (x : Plane) :
    HasSum (fun k : Γ.dual.points ↦ 𝐞 ⟪x, (k : Plane)⟫ • 𝓕 f k)
      (Γ.covolume • ∑' v : Γ.points, f (x + v)) := by
  have hsum : Summable fun k : Γ.dual.points ↦ 𝓕 f k := by
    simpa using Γ.dual.summable_comp_add ht hF 0
  exact Γ.hasSum_fourierChar_smul_fourier (integrable_of_le_one_add_norm_rpow hc hs hf)
    (Γ.continuous_tsum_comp_add hc hs hf) hsum x

/-- Gaussian decay `‖f y‖ ≤ A e^{-c‖y‖²}` implies the decay `‖f y‖ ≤ A' (1 + ‖y‖)^(-4)`. -/
theorem le_one_add_norm_rpow_of_gaussian {E : Type*} [NormedAddCommGroup E] {f : Plane → E}
    {A c : ℝ} (hc : 0 < c) (hf : ∀ y, ‖f y‖ ≤ A * Real.exp (-c * ‖y‖ ^ 2)) (y : Plane) :
    ‖f y‖ ≤ A * (8 * (1 + 2 / c ^ 2)) * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hf 0)
    simpa using this
  rw [mul_assoc]
  exact (hf y).trans (mul_le_mul_of_nonneg_left (exp_neg_mul_sq_le hc (norm_nonneg y)) hA)

/-- **Poisson summation for functions with Gaussian decay.** If `f` is continuous,
`‖f y‖ ≤ A e^{-c‖y‖²}` and `‖𝓕 f k‖ ≤ B e^{-c'‖k‖²}` with `c, c' > 0`, then
`∑_{k ∈ Γ*} 𝓕 f(k) 𝐞 ⟪x, k⟫ = covolume Γ · ∑_{v ∈ Γ} f(x + v)` for every `x`. -/
theorem hasSum_fourierChar_smul_fourier_of_gaussian {f : Plane → ℂ} (hc : Continuous f)
    {A c : ℝ} (hc₀ : 0 < c) (hf : ∀ y, ‖f y‖ ≤ A * Real.exp (-c * ‖y‖ ^ 2)) {B c' : ℝ}
    (hc'₀ : 0 < c') (hF : ∀ k, ‖𝓕 f k‖ ≤ B * Real.exp (-c' * ‖k‖ ^ 2)) (x : Plane) :
    HasSum (fun k : Γ.dual.points ↦ 𝐞 ⟪x, (k : Plane)⟫ • 𝓕 f k)
      (Γ.covolume • ∑' v : Γ.points, f (x + v)) :=
  Γ.hasSum_fourierChar_smul_fourier_of_decay hc (by norm_num)
    (le_one_add_norm_rpow_of_gaussian hc₀ hf) (by norm_num)
    (le_one_add_norm_rpow_of_gaussian hc'₀ hF) x

/-- **Poisson summation at the origin** for functions with Gaussian decay:
`∑_{k ∈ Γ*} 𝓕 f(k) = covolume Γ · ∑_{v ∈ Γ} f(v)`. -/
theorem tsum_fourier_eq_of_gaussian {f : Plane → ℂ} (hc : Continuous f)
    {A c : ℝ} (hc₀ : 0 < c) (hf : ∀ y, ‖f y‖ ≤ A * Real.exp (-c * ‖y‖ ^ 2)) {B c' : ℝ}
    (hc'₀ : 0 < c') (hF : ∀ k, ‖𝓕 f k‖ ≤ B * Real.exp (-c' * ‖k‖ ^ 2)) :
    ∑' k : Γ.dual.points, 𝓕 f k = Γ.covolume • ∑' v : Γ.points, f v := by
  simpa using (Γ.hasSum_fourierChar_smul_fourier_of_gaussian hc hc₀ hf hc'₀ hF 0).tsum_eq

end PlaneLattice

end TriangularLattice
