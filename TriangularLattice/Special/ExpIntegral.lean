/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The exponential integral

The exponential integral `E₁(y) = ∫₁^∞ e^{-y u} u⁻¹ du` for `y > 0`. With `y = π |x|²` it gives the
Ewald kernel `q₀(x) = ½ E₁(π |x|²)`, the auxiliary function of the manuscript with `P = 0`
(Definition 3.1 (A1)), studied in `TriangularLattice.Special.EwaldKernel`.

## Main results

* `expIntegral_pos`, `expIntegral_le`: `0 < E₁(y) ≤ e^{-y} / y`.
* `expIntegral_eq_integral_Ioi`: `E₁(y) = ∫_y^∞ e^{-v} v⁻¹ dv`.
* `hasDerivAt_expIntegral`: `E₁' (y) = -e^{-y} / y`.
* `tendsto_expIntegral_add_log`: `E₁(y) + log y` has a limit as `y → 0⁺`, with an explicit error
  bound `expIntegral_add_log_sub_le`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real
open scoped ContDiff

namespace TriangularLattice

/-- The exponential integral `E₁(y) = ∫₁^∞ e^{-y u} / u du` (meaningful for `y > 0`). -/
noncomputable def expIntegral (y : ℝ) : ℝ :=
  ∫ u in Ioi (1 : ℝ), Real.exp (-(y * u)) / u

lemma integrableOn_exp_neg_mul_div {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u : ℝ => Real.exp (-(y * u)) / u) (Ioi 1) := by
  refine (exp_neg_integrableOn_Ioi 1 hy).mono' ?_ ?_
  · exact ((continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.div
      continuousOn_id fun u hu => (zero_lt_one.trans hu).ne').aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu : (1 : ℝ) < u := hu
    rw [norm_div, norm_of_nonneg (exp_pos _).le, norm_of_nonneg (zero_lt_one.trans hu).le,
      neg_mul]
    exact div_le_self (exp_pos _).le hu.le

lemma expIntegral_pos {y : ℝ} (hy : 0 < y) : 0 < expIntegral y := by
  rw [expIntegral, integral_pos_iff_support_of_nonneg_ae]
  · simp only [Function.support, ne_eq, div_eq_zero_iff, exp_ne_zero, false_or]
    rw [Measure.restrict_apply' measurableSet_Ioi]
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioi 1) fun u hu => ⟨?_, hu⟩)
    · simp
    · exact (zero_lt_one.trans hu).ne'
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    exact div_nonneg (exp_pos _).le (zero_lt_one.trans hu).le
  · exact integrableOn_exp_neg_mul_div hy

lemma expIntegral_nonneg (y : ℝ) : 0 ≤ expIntegral y := by
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  exact div_nonneg (exp_pos _).le (zero_lt_one.trans hu).le

/-- `E₁(y) ≤ e^{-y} / y`. -/
lemma expIntegral_le {y : ℝ} (hy : 0 < y) : expIntegral y ≤ Real.exp (-y) / y := by
  calc expIntegral y ≤ ∫ u in Ioi (1 : ℝ), Real.exp (-y * u) := by
        refine setIntegral_mono_on (integrableOn_exp_neg_mul_div hy)
          (exp_neg_integrableOn_Ioi 1 hy) measurableSet_Ioi fun u hu => ?_
        have hu : (1 : ℝ) < u := hu
        rw [neg_mul]
        exact div_le_self (exp_pos _).le hu.le
    _ = Real.exp (-y) / y := by
        rw [integral_exp_mul_Ioi (neg_lt_zero.2 hy), mul_one, div_neg, neg_div, neg_neg]

lemma integrableOn_exp_neg_div_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun v : ℝ => Real.exp (-v) / v) (Ioi c) := by
  refine ((integrableOn_exp_neg_Ioi c).const_mul c⁻¹).mono' ?_ ?_
  · exact ((continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      fun v hv => (hc.trans hv).ne').aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    have hv : c < v := hv
    rw [norm_div, norm_of_nonneg (exp_pos _).le, norm_of_nonneg (hc.trans hv).le, div_eq_mul_inv,
      mul_comm]
    gcongr

/-- `E₁(y) = ∫_y^∞ e^{-v} / v dv`. -/
lemma expIntegral_eq_integral_Ioi {y : ℝ} (hy : 0 < y) :
    expIntegral y = ∫ v in Ioi y, Real.exp (-v) / v := by
  have h := integral_comp_mul_left_Ioi (fun v : ℝ => Real.exp (-v) / v) 1 hy
  rw [mul_one, smul_eq_mul] at h
  have h' : ∀ u : ℝ, Real.exp (-(y * u)) / u = y * (Real.exp (-(y * u)) / (y * u)) := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · field_simp
  simp_rw [expIntegral, h', integral_const_mul, h, ← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul]

/-- For `y > 0`, `E₁(y) = E₁(1) - ∫₁^y e^{-v} / v dv`. -/
lemma expIntegral_eq_sub {y : ℝ} (hy : 0 < y) :
    expIntegral y = expIntegral 1 - ∫ v in (1 : ℝ)..y, Real.exp (-v) / v := by
  rw [expIntegral_eq_integral_Ioi hy, expIntegral_eq_integral_Ioi one_pos,
    ← intervalIntegral.integral_interval_add_Ioi (integrableOn_exp_neg_div_Ioi hy)
      (integrableOn_exp_neg_div_Ioi one_pos), intervalIntegral.integral_symm]
  ring

lemma continuousOn_exp_neg_div : ContinuousOn (fun v : ℝ => Real.exp (-v) / v) (Ioi 0) :=
  (continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id fun _ hv => hv.ne'

/-- `E₁' (y) = -e^{-y} / y` for `y > 0`. -/
lemma hasDerivAt_expIntegral {y : ℝ} (hy : 0 < y) :
    HasDerivAt expIntegral (-(Real.exp (-y) / y)) y := by
  have hint : ∀ b : ℝ, 0 < b → IntervalIntegrable (fun v : ℝ => Real.exp (-v) / v) volume 1 b :=
    fun b hb => (continuousOn_exp_neg_div.mono fun x hx =>
      (lt_inf_iff.2 ⟨one_pos, hb⟩).trans_le hx.1).intervalIntegrable
  have hderiv : HasDerivAt (fun b => ∫ v in (1 : ℝ)..b, Real.exp (-v) / v) (Real.exp (-y) / y) y :=
    intervalIntegral.integral_hasDerivAt_right (hint y hy)
      (continuousOn_exp_neg_div.stronglyMeasurableAtFilter isOpen_Ioi y hy)
      (continuousOn_exp_neg_div.continuousAt (Ioi_mem_nhds hy))
  refine ((hderiv.const_sub (expIntegral 1)).congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [Ioi_mem_nhds hy] with b hb using expIntegral_eq_sub hb

lemma one_sub_exp_neg_div_mem_Icc {v : ℝ} (hv : 0 ≤ v) : (1 - Real.exp (-v)) / v ∈ Icc 0 1 := by
  rcases hv.eq_or_lt with rfl | hv
  · simp
  refine ⟨div_nonneg (sub_nonneg.2 (exp_le_one_iff.2 (neg_nonpos.2 hv.le))) hv.le, ?_⟩
  rw [div_le_one hv]
  linarith [add_one_le_exp (-v)]

lemma intervalIntegrable_one_sub_exp_neg_div {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun v : ℝ => (1 - Real.exp (-v)) / v) volume 0 b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb]
  refine Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne ?_ ?_
  · exact ((measurable_const.sub (measurable_exp.comp measurable_neg)).div
      measurable_id).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun v hv => ?_)
    have h := one_sub_exp_neg_div_mem_Icc hv.1
    rw [norm_of_nonneg h.1]
    exact h.2

/-- The constant `lim_{y → 0⁺} (E₁(y) + log y)` (which equals `-γ`, Euler's constant; this is not
needed). -/
noncomputable def expIntegralConst : ℝ :=
  expIntegral 1 - ∫ v in (0 : ℝ)..1, (1 - Real.exp (-v)) / v

lemma expIntegral_add_log {y : ℝ} (hy : 0 < y) :
    expIntegral y + Real.log y =
      expIntegralConst + ∫ v in (0 : ℝ)..y, (1 - Real.exp (-v)) / v := by
  have h0 : (0 : ℝ) ∉ uIcc 1 y := fun h => (lt_inf_iff.2 ⟨one_pos, hy⟩).not_ge h.1
  have hlog : Real.log y = ∫ v in (1 : ℝ)..y, v⁻¹ := by
    rw [integral_inv h0, div_one]
  have hcont : ContinuousOn (fun v : ℝ => (1 - Real.exp (-v)) / v) (uIcc 1 y) :=
    (continuous_const.sub (continuous_exp.comp continuous_neg)).continuousOn.div continuousOn_id
      fun v hv h => h0 (h ▸ hv)
  have hsub : ∫ v in (1 : ℝ)..y, (1 - Real.exp (-v)) / v =
      (∫ v in (1 : ℝ)..y, v⁻¹) - ∫ v in (1 : ℝ)..y, Real.exp (-v) / v := by
    rw [← intervalIntegral.integral_sub
      (continuousOn_inv₀.mono fun v hv h => h0 (h ▸ hv)).intervalIntegrable
      (continuousOn_exp_neg_div.mono fun v hv =>
        (lt_inf_iff.2 ⟨one_pos, hy⟩).trans_le hv.1).intervalIntegrable]
    congr 1
    funext v
    ring
  rw [expIntegral_eq_sub hy, hlog, expIntegralConst,
    ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_one_sub_exp_neg_div zero_le_one) hcont.intervalIntegrable, hsub]
  ring

/-- The quantitative form: `0 ≤ E₁(y) + log y - c ≤ y` for `y > 0`. -/
lemma expIntegral_add_log_sub_mem_Icc {y : ℝ} (hy : 0 < y) :
    expIntegral y + Real.log y - expIntegralConst ∈ Icc 0 y := by
  rw [expIntegral_add_log hy, add_sub_cancel_left]
  refine ⟨intervalIntegral.integral_nonneg hy.le fun v hv =>
    (one_sub_exp_neg_div_mem_Icc hv.1).1, ?_⟩
  calc ∫ v in (0 : ℝ)..y, (1 - Real.exp (-v)) / v ≤ ∫ v in (0 : ℝ)..y, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hy.le (intervalIntegrable_one_sub_exp_neg_div hy.le)
          intervalIntegrable_const fun v hv => (one_sub_exp_neg_div_mem_Icc hv.1).2
    _ = y := by simp

lemma tendsto_expIntegral_add_log :
    Tendsto (fun y => expIntegral y + Real.log y) (𝓝[>] 0) (𝓝 expIntegralConst) := by
  have h : Tendsto (fun y : ℝ => expIntegralConst + y) (𝓝[>] 0) (𝓝 expIntegralConst) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_const_add expIntegralConst).tendsto 0))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    linarith [(expIntegral_add_log_sub_mem_Icc hy).1]
  · filter_upwards [self_mem_nhdsWithin] with y hy
    linarith [(expIntegral_add_log_sub_mem_Icc hy).2]

lemma deriv_expIntegral {y : ℝ} (hy : 0 < y) : deriv expIntegral y = -(Real.exp (-y) / y) :=
  (hasDerivAt_expIntegral hy).deriv

/-- `E₁` is smooth on `(0, ∞)`. -/
lemma contDiffOn_expIntegral : ContDiffOn ℝ ∞ expIntegral (Ioi 0) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun y hy => (hasDerivAt_expIntegral hy).differentiableAt.differentiableWithinAt, ?_⟩
  refine ContDiffOn.congr (f := fun y : ℝ => -(Real.exp (-y) / y)) ?_ fun y hy =>
    deriv_expIntegral hy
  exact ((Real.contDiff_exp.comp contDiff_neg).contDiffOn.div contDiffOn_id
    fun y hy => (show (0 : ℝ) < y from hy).ne').neg

end TriangularLattice
