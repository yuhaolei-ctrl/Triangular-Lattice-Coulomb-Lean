/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Special.ExpIntegral
public import TriangularLattice.Statement
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Ewald kernel

The Ewald kernel `q₀(x) = ½ E₁(π |x|²) = ½ ∫₁^∞ e^{-π u |x|²} du / u` on the plane. It is the
auxiliary function of Definition 3.1 (A1) with `P = 0`, and the real-space part of the Ewald
decomposition of the Green function of a torus.

## Main results

* `ewaldKernel_pos`, `ewaldKernel_le`: `0 < q₀(x) ≤ e^{-π|x|²} / (2π|x|²)` for `x ≠ 0`.
* `integral_mul_ewaldKernel`: Fubini in the variable `u`, for bounded continuous weights.
* `integral_ewaldKernel`: `∫ q₀ = ½`.
* `fourier_ewaldKernel`: `𝓕 q₀ (k) = (1 - e^{-π|k|²}) / (2π |k|²)` for `k ≠ 0`.
* `tendsto_ewaldKernel_add_log`: `q₀(x) + log |x| → ewaldConst` as `x → 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real Complex
open scoped FourierTransform ContDiff

namespace TriangularLattice

/-- The Ewald kernel `q₀(x) = ½ E₁(π |x|²)`. -/
noncomputable def ewaldKernel (x : Plane) : ℝ :=
  expIntegral (π * ‖x‖ ^ 2) / 2

lemma ewaldKernel_pos {x : Plane} (hx : x ≠ 0) : 0 < ewaldKernel x :=
  half_pos (expIntegral_pos (by positivity))

lemma ewaldKernel_nonneg (x : Plane) : 0 ≤ ewaldKernel x :=
  div_nonneg (expIntegral_nonneg _) zero_le_two

/-- `q₀(x) ≤ e^{-π|x|²} / (2π|x|²)`. -/
lemma ewaldKernel_le {x : Plane} (hx : x ≠ 0) :
    ewaldKernel x ≤ Real.exp (-(π * ‖x‖ ^ 2)) / (2 * (π * ‖x‖ ^ 2)) := by
  have hy : 0 < π * ‖x‖ ^ 2 := by positivity
  calc ewaldKernel x ≤ Real.exp (-(π * ‖x‖ ^ 2)) / (π * ‖x‖ ^ 2) / 2 :=
        div_le_div_of_nonneg_right (expIntegral_le hy) zero_le_two
    _ = _ := by rw [div_div, mul_comm (π * ‖x‖ ^ 2)]

/-- Gaussians `x ↦ e^{-a|x|²}` (`a > 0`) are integrable on the plane. -/
lemma integrable_exp_neg_mul_sq_norm {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Plane => Real.exp (-a * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Plane)
    (b := (a : ℂ)) (by simpa using ha) 0 0).norm
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  norm_cast

/-- `∫ e^{-a|x|²} dx = π / a` on the plane. -/
lemma integral_exp_neg_mul_sq_norm {a : ℝ} (ha : 0 < a) :
    ∫ x : Plane, Real.exp (-a * ‖x‖ ^ 2) = π / a := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm ha, finrank_euclideanSpace_fin]
  norm_num

/-- The integrand of `q₀` as a function of `(x, u)`. -/
lemma measurable_ewaldIntegrand :
    Measurable (fun z : Plane × ℝ => Real.exp (-(π * ‖z.1‖ ^ 2 * z.2)) / z.2) := by
  fun_prop

/-- **Fubini for the Ewald kernel.** For a continuous weight `g` with `|g| ≤ 1`,
`∫ g q₀ = ½ ∫₁^∞ u⁻¹ ∫ g(x) e^{-π u |x|²} dx du`. -/
lemma integral_mul_ewaldKernel {g : Plane → ℂ} (hg : Continuous g) (hg1 : ∀ x, ‖g x‖ ≤ 1) :
    ∫ x, g x * (ewaldKernel x : ℂ) =
      (1 / 2 : ℂ) * ∫ u in Ioi (1 : ℝ),
        (u : ℂ)⁻¹ * ∫ x : Plane, g x * (Real.exp (-(π * u) * ‖x‖ ^ 2) : ℂ) := by
  set F : Plane → ℝ → ℂ := fun x u => g x * ((Real.exp (-(π * ‖x‖ ^ 2 * u)) / u : ℝ) : ℂ)
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi (1 : ℝ)))) := by
    have hmeas : Measurable (Function.uncurry F) :=
      (hg.measurable.comp measurable_fst).mul
        (Complex.measurable_ofReal.comp measurable_ewaldIntegrand)
    refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu : (1 : ℝ) < u := hu
      refine ((integrable_exp_neg_mul_sq_norm (mul_pos pi_pos (zero_lt_one.trans hu))).div_const
        u).mono' (hmeas.comp measurable_prodMk_right).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      simp only [Function.uncurry_apply_pair, F, norm_mul, Complex.norm_real, norm_div,
        norm_of_nonneg (exp_pos _).le, norm_of_nonneg (zero_lt_one.trans hu).le]
      calc ‖g x‖ * (Real.exp (-(π * ‖x‖ ^ 2 * u)) / u)
          ≤ 1 * (Real.exp (-(π * ‖x‖ ^ 2 * u)) / u) := by gcongr; exact hg1 x
        _ = Real.exp (-(π * u) * ‖x‖ ^ 2) / u := by rw [one_mul]; ring_nf
    · refine Integrable.mono' (g := fun u : ℝ => u ^ (-2 : ℝ))
        (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)
        (hmeas.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu : (1 : ℝ) < u := hu
      have hu0 : 0 < u := zero_lt_one.trans hu
      rw [norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ x, ‖Function.uncurry F (x, u)‖
          ≤ ∫ x : Plane, Real.exp (-(π * u) * ‖x‖ ^ 2) / u := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((integrable_exp_neg_mul_sq_norm (mul_pos pi_pos hu0)).div_const u)
              (Eventually.of_forall fun x => ?_)
            simp only [Function.uncurry_apply_pair, F, norm_mul, Complex.norm_real, norm_div,
              norm_of_nonneg (exp_pos _).le, norm_of_nonneg hu0.le]
            calc ‖g x‖ * (Real.exp (-(π * ‖x‖ ^ 2 * u)) / u)
                ≤ 1 * (Real.exp (-(π * ‖x‖ ^ 2 * u)) / u) := by gcongr; exact hg1 x
              _ = Real.exp (-(π * u) * ‖x‖ ^ 2) / u := by rw [one_mul]; ring_nf
        _ = u ^ (-2 : ℝ) := by
            rw [integral_div, integral_exp_neg_mul_sq_norm (mul_pos pi_pos hu0),
              rpow_neg hu0.le, rpow_two]
            field_simp
  have hq : ∀ x : Plane, (ewaldKernel x : ℂ) =
      (1 / 2 : ℂ) * ∫ u in Ioi (1 : ℝ), ((Real.exp (-(π * ‖x‖ ^ 2 * u)) / u : ℝ) : ℂ) := by
    intro x
    rw [ewaldKernel, expIntegral, integral_complex_ofReal]
    push_cast
    ring
  have h1 : ∫ x, g x * (ewaldKernel x : ℂ) = (1 / 2 : ℂ) * ∫ x, ∫ u in Ioi (1 : ℝ), F x u := by
    simp_rw [hq, ← integral_const_mul, F]
    congr 1
    funext x
    congr 1
    funext u
    ring
  rw [h1, integral_integral_swap hF]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hu).ne'
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [F]
  push_cast
  field_simp

/-- `∫ q₀ = ½`. -/
lemma integral_ewaldKernel : ∫ x, ewaldKernel x = 1 / 2 := by
  have h := integral_mul_ewaldKernel (g := fun _ => 1) continuous_const (fun _ => by simp)
  simp only [one_mul] at h
  have hin : ∀ u ∈ Ioi (1 : ℝ), (u : ℂ)⁻¹ * ∫ x : Plane, (Real.exp (-(π * u) * ‖x‖ ^ 2) : ℂ) =
      ((u ^ (-2 : ℝ) : ℝ) : ℂ) := by
    intro u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    rw [integral_complex_ofReal, integral_exp_neg_mul_sq_norm (mul_pos pi_pos hu0),
      rpow_neg hu0.le, rpow_two]
    push_cast
    field_simp
  have hreal : ∫ u in Ioi (1 : ℝ), ((u ^ (-2 : ℝ) : ℝ) : ℂ) =
      ((∫ u in Ioi (1 : ℝ), u ^ (-2 : ℝ) : ℝ) : ℂ) := integral_complex_ofReal
  rw [setIntegral_congr_fun measurableSet_Ioi hin, hreal,
    integral_Ioi_rpow_of_lt (by norm_num) one_pos, integral_complex_ofReal] at h
  have h' : ((∫ x, ewaldKernel x : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    rw [h]
    norm_num
  exact_mod_cast h'

/-- `∫₁^∞ u⁻² e^{-c/u} du = (1 - e^{-c}) / c` for `c > 0`. -/
lemma integral_Ioi_rpow_neg_two_mul_exp {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (1 : ℝ), u ^ (-2 : ℝ) * Real.exp (-c / u) = (1 - Real.exp (-c)) / c := by
  have hderiv : ∀ u ∈ Ioi (1 : ℝ),
      HasDerivAt (fun u : ℝ => Real.exp (-c / u) / c) (u ^ (-2 : ℝ) * Real.exp (-c / u)) u := by
    intro u hu
    have hu0 : u ≠ 0 := (zero_lt_one.trans hu).ne'
    have := (((hasDerivAt_inv hu0).const_mul (-c)).exp).div_const c
    convert this using 1
    · funext v
      simp [div_eq_mul_inv]
    · rw [rpow_neg (zero_lt_one.trans hu).le, rpow_two]
      field_simp
  have hint : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ) * Real.exp (-c / u)) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos).mono' ?_ ?_
    · exact (ContinuousOn.mul (continuousOn_id.rpow_const fun u hu =>
        Or.inl (zero_lt_one.trans hu).ne') ((Real.continuous_exp.comp_continuousOn
          (continuousOn_const.div continuousOn_id fun u hu =>
            (zero_lt_one.trans hu).ne')))).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := zero_lt_one.trans hu
      rw [norm_mul, norm_of_nonneg (rpow_nonneg hu0.le _), norm_of_nonneg (exp_pos _).le]
      refine mul_le_of_le_one_right (rpow_nonneg hu0.le _) (exp_le_one_iff.2 ?_)
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hc.le) hu0.le
  have hlim : Tendsto (fun u : ℝ => Real.exp (-c / u) / c) atTop (𝓝 (1 / c)) := by
    have : Tendsto (fun u : ℝ => -c / u) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using ((Real.continuous_exp.tendsto 0).comp this).div_const c
  have hcont : ContinuousWithinAt (fun u : ℝ => Real.exp (-c / u) / c) (Ici 1) 1 :=
    ((Real.continuous_exp.continuousAt.comp
      (continuousAt_const.div continuousAt_id one_ne_zero)).div_const c).continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim, div_one]
  ring

/-- **The Fourier transform of the Ewald kernel.** `𝓕 q₀ (k) = (1 - e^{-π|k|²}) / (2π|k|²)` for
`k ≠ 0`. -/
lemma fourier_ewaldKernel {k : Plane} (hk : k ≠ 0) :
    𝓕 (fun x => (ewaldKernel x : ℂ)) k =
      (((1 - Real.exp (-(π * ‖k‖ ^ 2))) / (2 * (π * ‖k‖ ^ 2)) : ℝ) : ℂ) := by
  have hc : 0 < π * ‖k‖ ^ 2 := by positivity
  set g : Plane → ℂ := fun v => (𝐞 (-inner ℝ v k) : ℂ)
  have hg : Continuous g := by fun_prop
  have hg1 : ∀ v, ‖g v‖ ≤ 1 := fun v => by simp [g]
  have hF : 𝓕 (fun x => (ewaldKernel x : ℂ)) k = ∫ x, g x * (ewaldKernel x : ℂ) := by
    simp only [fourier_eq, Circle.smul_def, smul_eq_mul, g]
  have hin : ∀ u ∈ Ioi (1 : ℝ),
      (u : ℂ)⁻¹ * ∫ x : Plane, g x * (Real.exp (-(π * u) * ‖x‖ ^ 2) : ℂ) =
        ((u ^ (-2 : ℝ) * Real.exp (-(π * ‖k‖ ^ 2) / u) : ℝ) : ℂ) := by
    intro u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    have hgauss := fourier_gaussian_innerProductSpace (V := Plane)
      (b := ((π * u : ℝ) : ℂ)) (by simpa using mul_pos pi_pos hu0) k
    rw [fourier_eq] at hgauss
    simp only [Circle.smul_def, smul_eq_mul] at hgauss
    have hrw : ∀ x : Plane, g x * (Real.exp (-(π * u) * ‖x‖ ^ 2) : ℂ) =
        (𝐞 (-inner ℝ x k) : ℂ) * Complex.exp (-((π * u : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
      intro x
      simp only [g, Complex.ofReal_exp]
      push_cast
      ring_nf
    simp_rw [hrw, hgauss, finrank_euclideanSpace_fin]
    rw [rpow_neg hu0.le, rpow_two]
    have hpu : (π : ℂ) * u ≠ 0 := by exact_mod_cast (mul_pos pi_pos hu0).ne'
    push_cast
    have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast pi_pos.ne'
    rw [show (2 : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]
    have hexp : -(π : ℂ) ^ 2 * (‖k‖ : ℂ) ^ 2 / (π * u) = -(π * (‖k‖ : ℂ) ^ 2) / u := by
      field_simp
    rw [hexp]
    field_simp
  have hreal : ∫ u in Ioi (1 : ℝ), ((u ^ (-2 : ℝ) * Real.exp (-(π * ‖k‖ ^ 2) / u) : ℝ) : ℂ) =
      ((∫ u in Ioi (1 : ℝ), u ^ (-2 : ℝ) * Real.exp (-(π * ‖k‖ ^ 2) / u) : ℝ) : ℂ) :=
    integral_complex_ofReal
  rw [hF, integral_mul_ewaldKernel hg hg1, setIntegral_congr_fun measurableSet_Ioi hin, hreal,
    integral_Ioi_rpow_neg_two_mul_exp hc]
  push_cast
  ring

/-- The constant `c₀ = lim_{x → 0} (q₀(x) + log |x|)` of the Ewald kernel. -/
noncomputable def ewaldConst : ℝ :=
  (expIntegralConst - Real.log π) / 2

lemma ewaldKernel_add_log_eq {x : Plane} (hx : x ≠ 0) :
    ewaldKernel x + Real.log ‖x‖ - ewaldConst =
      (expIntegral (π * ‖x‖ ^ 2) + Real.log (π * ‖x‖ ^ 2) - expIntegralConst) / 2 := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [ewaldKernel, ewaldConst, Real.log_mul pi_pos.ne' (by positivity), Real.log_pow]
  push_cast
  ring

/-- The quantitative form: `0 ≤ q₀(x) + log |x| - c₀ ≤ π |x|² / 2`. -/
lemma ewaldKernel_add_log_sub_mem_Icc {x : Plane} (hx : x ≠ 0) :
    ewaldKernel x + Real.log ‖x‖ - ewaldConst ∈ Icc 0 (π * ‖x‖ ^ 2 / 2) := by
  have h := expIntegral_add_log_sub_mem_Icc (y := π * ‖x‖ ^ 2) (by positivity)
  rw [ewaldKernel_add_log_eq hx]
  exact ⟨div_nonneg h.1 zero_le_two, div_le_div_of_nonneg_right h.2 zero_le_two⟩

/-- `q₀(x) + log |x| → c₀` as `x → 0`. -/
lemma tendsto_ewaldKernel_add_log :
    Tendsto (fun x : Plane => ewaldKernel x + Real.log ‖x‖) (𝓝[≠] 0) (𝓝 ewaldConst) := by
  have hup : Tendsto (fun x : Plane => ewaldConst + π * ‖x‖ ^ 2 / 2) (𝓝[≠] 0)
      (𝓝 ewaldConst) := by
    have : Continuous (fun x : Plane => ewaldConst + π * ‖x‖ ^ 2 / 2) := by fun_prop
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (this.tendsto 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    linarith [(ewaldKernel_add_log_sub_mem_Icc hx).1]
  · filter_upwards [self_mem_nhdsWithin] with x hx
    linarith [(ewaldKernel_add_log_sub_mem_Icc hx).2]

/-- The Ewald kernel is smooth off the origin. -/
lemma contDiffOn_ewaldKernel : ContDiffOn ℝ ∞ ewaldKernel {0}ᶜ := by
  have h : ContDiffOn ℝ ∞ (fun x : Plane => π * ‖x‖ ^ 2) {0}ᶜ :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffOn
  refine (contDiffOn_expIntegral.comp h fun x hx => ?_).div_const 2
  have hx : x ≠ 0 := hx
  show 0 < π * ‖x‖ ^ 2
  positivity

lemma continuousOn_ewaldKernel : ContinuousOn ewaldKernel {0}ᶜ :=
  contDiffOn_ewaldKernel.continuousOn

end TriangularLattice
