/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Basic.Lattice
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Periodic functions and Fourier series on the torus `ℝ²/Γ`

For a lattice `Γ` of covolume `N` in the plane, this file develops integration and Fourier
analysis of `Γ`-periodic functions (§2.1 and §2.3 of the manuscript).

The Fourier coefficients of `f` are `f̂(k) = ∫_cell f(x) e^{-2πi⟪x, k⟫} dx` for `k` in the dual
lattice `Γ*`, so that `f = N⁻¹ ∑_k f̂(k) e^{2πi⟪x, k⟫}` and `∑_k |f̂(k)|² = N ∫_cell |f|²`. The
character `x ↦ e^{2πi⟪x, k⟫}` is written `𝐞 ⟪x, k⟫`, as in Mathlib's Fourier transform `𝓕`.

## Main definitions

* `PlaneLattice.IsPeriodic`: `Γ`-periodic functions.
* `PlaneLattice.fourierCoeff`: the Fourier coefficient `f̂(k) = ∫_cell 𝐞 (-⟪x, k⟫) • f x`.
* `PlaneLattice.torusSection`: the map from the standard torus `UnitAddTorus (Fin 2)` to the
  plane, `θ ↦ t₀ b₀ + t₁ b₁` with `t ∈ (0, 1]²` the representative of `θ`. It transports Mathlib's
  Fourier analysis on `UnitAddTorus (Fin 2)` to `ℝ²/Γ`.

## Main results

* `PlaneLattice.IsPeriodic.setIntegral_cell_comp_add`: `∫_cell f(x + y) dx = ∫_cell f`.
* `PlaneLattice.integral_cell_tsum_comp_add`, `PlaneLattice.lintegral_cell_tsum_comp_add`:
  unfolding, `∫_cell ∑_{v ∈ Γ} f(x + v) dx = ∫ f`.
* `PlaneLattice.integral_cell_fourierChar`: orthogonality of the characters.
* `PlaneLattice.hasSum_fourierCoeff_smul_fourierChar`,
  `PlaneLattice.hasSumUniformly_fourierCoeff_smul_fourierChar`: Fourier inversion, pointwise and
  uniform, for continuous periodic functions with summable coefficients.
* `PlaneLattice.hasSum_sq_norm_fourierCoeff`, `PlaneLattice.hasSum_conj_mul_fourierCoeff`:
  Parseval's identity.
* `PlaneLattice.fourierCoeff_tsum_comp_add`: the coefficients of the periodization of an integrable
  function are the values of its Fourier transform on `Γ*`.
-/

@[expose] public section

open MeasureTheory Metric Set Module Filter Topology UnitAddTorus
open scoped RealInnerProductSpace FourierTransform ENNReal ComplexConjugate

/-- As in `Mathlib.Analysis.Fourier.AddCircleMulti`, the measure on `ℝ / ℤ` is normalised to have
total volume one, so that `volume` on `UnitAddTorus (Fin 2)` is the Haar probability measure used
by `UnitAddTorus.mFourierCoeff` and `UnitAddTorus.mFourierBasis`. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

namespace TriangularLattice

/-- The Fourier character is trivial on the integers: `𝐞 n = 1`. -/
theorem fourierChar_intCast (n : ℤ) : 𝐞 (n : ℝ) = 1 := by
  rw [Real.fourierChar_apply', Circle.exp_two_pi_mul_int]

namespace PlaneLattice

variable (Γ : PlaneLattice)

/-! ### Periodic functions -/

/-- A function on the plane is `Γ`-periodic if `f (x + v) = f x` for every `v ∈ Γ`. -/
def IsPeriodic {α : Type*} (f : Plane → α) : Prop :=
  ∀ v ∈ Γ.points, ∀ x, f (x + v) = f x

namespace IsPeriodic

variable {Γ} {α β : Type*} {f : Plane → α}

/-- A periodic function is invariant under subtraction of lattice vectors. -/
theorem sub_eq (hf : Γ.IsPeriodic f) {v : Plane} (hv : v ∈ Γ.points) (x : Plane) :
    f (x - v) = f x := by
  rw [← hf v hv (x - v), sub_add_cancel]

/-- A periodic function is invariant under translation by lattice vectors on the left. -/
theorem add_left_eq (hf : Γ.IsPeriodic f) {v : Plane} (hv : v ∈ Γ.points) (x : Plane) :
    f (v + x) = f x := by
  rw [add_comm, hf v hv x]

/-- Composing a periodic function with any function gives a periodic function. -/
theorem comp (hf : Γ.IsPeriodic f) (g : α → β) : Γ.IsPeriodic (g ∘ f) :=
  fun v hv x ↦ by simp only [Function.comp_apply, hf v hv x]

/-- Translates of periodic functions are periodic. -/
theorem comp_add (hf : Γ.IsPeriodic f) (y : Plane) : Γ.IsPeriodic fun x ↦ f (x + y) :=
  fun v hv x ↦ by
    change f (x + v + y) = f (x + y)
    rw [add_right_comm, hf v hv]

/-- A periodic function only depends on the reduction of its argument modulo `Γ`. -/
theorem apply_fract (hf : Γ.IsPeriodic f) (x : Plane) : f (Γ.fract x) = f x := by
  conv_rhs => rw [← add_sub_cancel (Γ.fract x) x]
  exact (hf _ (Γ.sub_fract_mem_points x) _).symm

/-- Two points that differ by a lattice vector have the same value. -/
theorem apply_eq_of_sub_mem (hf : Γ.IsPeriodic f) {x y : Plane} (h : x - y ∈ Γ.points) :
    f x = f y := by
  rw [← sub_add_cancel x y, add_comm, hf _ h]

end IsPeriodic

/-- The lattice sum `x ↦ ∑_{v ∈ Γ} f (x + v)` is `Γ`-periodic. -/
theorem isPeriodic_tsum_comp_add {E : Type*} [NormedAddCommGroup E] (f : Plane → E) :
    Γ.IsPeriodic fun x ↦ ∑' v : Γ.points, f (x + v) :=
  fun _ hw x ↦ Γ.tsum_comp_add_add x hw

/-- The character `𝐞 ⟪·, k⟫` is invariant under translations by `Γ` when `k ∈ Γ*`. -/
theorem fourierChar_inner_add {v k : Plane} (hv : v ∈ Γ.points) (hk : k ∈ Γ.dual.points)
    (x : Plane) : 𝐞 ⟪x + v, k⟫ = 𝐞 ⟪x, k⟫ := by
  obtain ⟨n, hn⟩ := Γ.exists_int_inner_eq hv hk
  rw [inner_add_left, hn, AddChar.map_add_eq_mul, fourierChar_intCast, mul_one]

/-- The character `𝐞 ⟪·, k⟫` is `Γ`-periodic when `k ∈ Γ*`. -/
theorem isPeriodic_fourierChar {k : Plane} (hk : k ∈ Γ.dual.points) :
    Γ.IsPeriodic fun x ↦ 𝐞 ⟪x, k⟫ :=
  fun _ hv x ↦ Γ.fourierChar_inner_add hv hk x

/-! ### Integrals over the cell -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral of a periodic function over any fundamental domain of `Γ` equals its integral
over the cell. -/
theorem IsPeriodic.setIntegral_eq_of_isAddFundamentalDomain {Γ : PlaneLattice} {f : Plane → E}
    (hf : Γ.IsPeriodic f) {t : Set Plane} (ht : IsAddFundamentalDomain Γ.points t) :
    ∫ x in t, f x = ∫ x in Γ.cell, f x :=
  ht.setIntegral_eq Γ.isAddFundamentalDomain_cell fun g x ↦ by
    rw [Submodule.vadd_def, vadd_eq_add, hf.add_left_eq g.2]

/-- The translate `cell - y` of the cell is a fundamental domain of `Γ`. -/
theorem isAddFundamentalDomain_preimage_add (y : Plane) :
    IsAddFundamentalDomain Γ.points ((· + y) ⁻¹' Γ.cell) :=
  Γ.isAddFundamentalDomain_cell.preimage_of_equiv
    (measurePreserving_add_right volume y).quasiMeasurePreserving Function.bijective_id
    fun g x ↦ by simp [Submodule.vadd_def, add_assoc]

/-- **Translation invariance.** The integral over the cell of a periodic function is invariant
under translation: `∫_cell f(x + y) dx = ∫_cell f`. -/
theorem IsPeriodic.setIntegral_cell_comp_add {Γ : PlaneLattice} {f : Plane → E}
    (hf : Γ.IsPeriodic f) (y : Plane) : ∫ x in Γ.cell, f (x + y) = ∫ x in Γ.cell, f x := by
  rw [← (hf.comp_add y).setIntegral_eq_of_isAddFundamentalDomain
    (Γ.isAddFundamentalDomain_preimage_add y)]
  exact (measurePreserving_add_right volume y).setIntegral_preimage_emb
    (MeasurableEquiv.addRight y).measurableEmbedding f Γ.cell

/-- **Unfolding** for nonnegative functions (Tonelli):
`∫⁻_cell ∑_{v ∈ Γ} f(x + v) dx = ∫⁻ f`. -/
theorem lintegral_cell_tsum_comp_add {f : Plane → ℝ≥0∞} (hf : AEMeasurable f) :
    ∫⁻ x in Γ.cell, ∑' v : Γ.points, f (x + v) = ∫⁻ x, f x := by
  rw [lintegral_tsum fun v ↦ ?_, Γ.isAddFundamentalDomain_cell.lintegral_eq_tsum'' f]
  · simp [Submodule.vadd_def, add_comm]
  · exact (hf.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (v : Plane)).quasiMeasurePreserving).restrict

omit [NormedSpace ℝ E] in
/-- The unfolding identity `∑_{v ∈ Γ} ∫⁻_cell ‖f(x + v)‖ = ∫⁻ ‖f‖`. -/
theorem tsum_lintegral_cell_enorm_comp_add (f : Plane → E) :
    ∑' v : Γ.points, ∫⁻ x in Γ.cell, ‖f (x + v)‖ₑ = ∫⁻ x, ‖f x‖ₑ := by
  rw [Γ.isAddFundamentalDomain_cell.lintegral_eq_tsum'' fun x ↦ ‖f x‖ₑ]
  simp [Submodule.vadd_def, add_comm]

/-- **Unfolding.** For an integrable function, `∫_cell ∑_{v ∈ Γ} f(x + v) dx = ∫ f`. -/
theorem integral_cell_tsum_comp_add {f : Plane → E} (hf : Integrable f) :
    ∫ x in Γ.cell, ∑' v : Γ.points, f (x + v) = ∫ x, f x := by
  rw [integral_tsum (fun v ↦ ?_) ?_, Γ.isAddFundamentalDomain_cell.integral_eq_tsum'' f hf]
  · simp [Submodule.vadd_def, add_comm]
  · rw [Γ.tsum_lintegral_cell_enorm_comp_add f]
    exact hf.2.ne
  · exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (v : Plane)).quasiMeasurePreserving).restrict

omit [NormedSpace ℝ E] in
/-- For an integrable function, the lattice sum `∑_{v ∈ Γ} ‖f(x + v)‖` converges for almost every
`x` in the cell. -/
theorem ae_summable_norm_comp_add {f : Plane → E} (hf : Integrable f) :
    ∀ᵐ x ∂volume.restrict Γ.cell, Summable fun v : Γ.points ↦ ‖f (x + v)‖ := by
  have hfin : ∫⁻ x in Γ.cell, ∑' v : Γ.points, ‖f (x + v)‖ₑ < ∞ := by
    rw [Γ.lintegral_cell_tsum_comp_add hf.aestronglyMeasurable.enorm]
    exact hf.2
  have hmeas : AEMeasurable (fun x ↦ ∑' v : Γ.points, ‖f (x + v)‖ₑ) (volume.restrict Γ.cell) :=
    AEMeasurable.tsum fun v ↦ (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (v : Plane)).quasiMeasurePreserving).enorm.restrict
  filter_upwards [ae_lt_top' hmeas hfin.ne] with x hx
  simp_rw [← ofReal_norm] at hx
  exact (ENNReal.summable_toReal hx.ne).congr fun v ↦ ENNReal.toReal_ofReal (norm_nonneg _)

end Integral

/-! ### Transport to the standard torus -/

/-- The linear isomorphism `t ↦ t 0 • b₀ + t 1 • b₁` maps Lebesgue measure on `ℝ²` to
`covolume⁻¹ • volume`. -/
theorem map_equivFun_symm_volume :
    Measure.map Γ.equivFun.symm volume = ENNReal.ofReal Γ.covolume⁻¹ • volume := by
  let T := Γ.equivFun.symm.toContinuousLinearEquiv
  have hb : (Pi.basisFun ℝ (Fin 2)).map T.toLinearEquiv = Γ.basis :=
    Basis.eq_of_apply_eq fun i ↦ by fin_cases i <;> simp [T]
  have h₁ : (Pi.basisFun ℝ (Fin 2)).addHaar = volume := by
    rw [Basis.addHaar_def, Basis.parallelepiped_basisFun, addHaarMeasure_eq_volume_pi]
  have h₂ : volume = ENNReal.ofReal Γ.covolume • Γ.basis.addHaar := by
    rw [Basis.addHaar_def]
    conv_lhs => rw [Measure.addHaarMeasure_unique volume Γ.basis.parallelepiped]
    rw [Basis.coe_parallelepiped,
      ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Γ.basis volume),
      ← cell_eq_fundamentalDomain, volume_cell]
  have h₃ : Measure.map Γ.equivFun.symm volume = Γ.basis.addHaar := by
    rw [← hb, ← Basis.map_addHaar, h₁]
    rfl
  rw [h₃, ENNReal.ofReal_inv_of_pos Γ.covolume_pos]
  conv_rhs => rw [h₂, smul_smul]
  rw [ENNReal.inv_mul_cancel (by simpa using Γ.covolume_pos) ENNReal.ofReal_ne_top, one_smul]

/-- The linear isomorphism `t ↦ t 0 • b₀ + t 1 • b₁` is measure preserving onto
`covolume⁻¹ • volume`. -/
theorem measurePreserving_equivFun_symm :
    MeasurePreserving Γ.equivFun.symm volume (ENNReal.ofReal Γ.covolume⁻¹ • volume) :=
  ⟨(LinearMap.continuous_of_finiteDimensional Γ.equivFun.symm.toLinearMap).measurable,
    Γ.map_equivFun_symm_volume⟩

/-- The map `t ↦ t 0 • b₀ + t 1 • b₁` is a measurable embedding. -/
theorem measurableEmbedding_equivFun_symm : MeasurableEmbedding Γ.equivFun.symm :=
  Γ.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

/-- The image of the cube `(0, 1]²` under `t ↦ t 0 • b₀ + t 1 • b₁` agrees with the cell up to a
null set. -/
theorem image_cubeIoc_ae_eq_cell :
    Γ.equivFun.symm '' {t : Fin 2 → ℝ | ∀ i, t i ∈ Ioc (0 : ℝ) 1} =ᵐ[volume] Γ.cell := by
  have hcell : Γ.cell = Γ.equivFun.symm '' {t : Fin 2 → ℝ | ∀ i, t i ∈ Ico (0 : ℝ) 1} := by
    ext x
    rw [Γ.equivFun.symm.image_eq_preimage_symm, mem_preimage, mem_cell_iff]
    simp [Fin.forall_fin_two]
  have hQ : {t : Fin 2 → ℝ | ∀ i, t i ∈ Ioc (0 : ℝ) 1} =ᵐ[volume]
      {t : Fin 2 → ℝ | ∀ i, t i ∈ Ico (0 : ℝ) 1} := by
    have h₁ := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin 2 ↦ (volume : Measure ℝ))
      (f := fun _ ↦ 0) (g := fun _ ↦ 1)
    have h₂ := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin 2 ↦ (volume : Measure ℝ))
      (f := fun _ ↦ 0) (g := fun _ ↦ 1)
    simp only [← volume_pi] at h₁ h₂
    convert h₁.trans h₂.symm using 1 <;> ext <;> simp
  have key : ∀ s : Set (Fin 2 → ℝ), volume s = 0 → volume (Γ.equivFun.symm '' s) = 0 := by
    intro s hs
    have h := Γ.measurableEmbedding_equivFun_symm.map_apply volume (Γ.equivFun.symm '' s)
    rw [Γ.map_equivFun_symm_volume, Set.preimage_image_eq _ Γ.equivFun.symm.injective, hs,
      Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h
    exact h.resolve_left (by simpa using Γ.covolume_pos)
  rw [hcell, ← measure_symmDiff_eq_zero_iff, ← Set.image_symmDiff Γ.equivFun.symm.injective]
  exact key _ (measure_symmDiff_eq_zero_iff.mpr hQ)

/-- The section `θ ↦ t₀ b₀ + t₁ b₁` of the projection to the torus, where `t ∈ (0, 1]²` is the
representative of `θ ∈ UnitAddTorus (Fin 2)`. -/
noncomputable def torusSection (θ : UnitAddTorus (Fin 2)) : Plane :=
  Γ.equivFun.symm fun i ↦ (AddCircle.equivIoc 1 0 (θ i) : ℝ)

/-- The section of the torus factors through Mathlib's `measurableEquivPiIoc`. -/
theorem torusSection_eq :
    Γ.torusSection = Γ.equivFun.symm ∘ Subtype.val ∘ measurableEquivPiIoc (0 : Fin 2 → ℝ) :=
  rfl

/-- The section of the torus is a measurable embedding. -/
theorem measurableEmbedding_torusSection : MeasurableEmbedding Γ.torusSection := by
  have hQ : MeasurableSet
      {t : Fin 2 → ℝ | ∀ i, t i ∈ Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)} :=
    MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ioc
  exact Γ.measurableEmbedding_equivFun_symm.comp
    ((MeasurableEmbedding.subtype_coe hQ).comp (measurableEquivPiIoc 0).measurableEmbedding)

/-- The section of the torus maps the Haar probability measure of `UnitAddTorus (Fin 2)` to the
normalized Lebesgue measure `covolume⁻¹ • volume` on the cell. -/
theorem measurePreserving_torusSection :
    MeasurePreserving Γ.torusSection volume
      (ENNReal.ofReal Γ.covolume⁻¹ • volume.restrict Γ.cell) := by
  set Q := {t : Fin 2 → ℝ | ∀ i, t i ∈ Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)}
  have hQ : MeasurableSet Q := MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ioc
  have hQ' : Q = {t : Fin 2 → ℝ | ∀ i, t i ∈ Ioc (0 : ℝ) 1} := by
    ext t
    simp [Q]
  have h₁ := measurePreserving_equivPiIoc (d := Fin 2) 0
  have h₂ : MeasurePreserving (Subtype.val : Q → Fin 2 → ℝ) (Measure.comap Subtype.val volume)
      (volume.restrict Q) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe hQ volume⟩
  have h₃ : MeasurePreserving Γ.equivFun.symm (volume.restrict Q)
      (ENNReal.ofReal Γ.covolume⁻¹ • volume.restrict Γ.cell) := by
    have := Γ.measurePreserving_equivFun_symm.restrict_preimage_emb
      Γ.measurableEmbedding_equivFun_symm (Γ.equivFun.symm '' Q)
    rwa [Set.preimage_image_eq _ Γ.equivFun.symm.injective, Measure.restrict_smul,
      show Γ.equivFun.symm '' Q = Γ.equivFun.symm '' {t | ∀ i, t i ∈ Ioc (0 : ℝ) 1} by rw [hQ'],
      Measure.restrict_congr_set Γ.image_cubeIoc_ae_eq_cell] at this
  exact h₃.comp (h₂.comp h₁)

/-- Integrals over the standard torus of functions pulled back along the section are integrals
over the cell: `∫ f (torusSection θ) dθ = covolume⁻¹ • ∫_cell f`. -/
theorem integral_comp_torusSection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Plane → E) :
    ∫ θ, f (Γ.torusSection θ) = Γ.covolume⁻¹ • ∫ x in Γ.cell, f x := by
  rw [Γ.measurePreserving_torusSection.integral_comp Γ.measurableEmbedding_torusSection,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr Γ.covolume_pos.le)]

/-- The first coordinate of `t 0 • b₀ + t 1 • b₁` is `t 0`. -/
@[simp]
theorem inner_equivFun_symm_dual_b₀ (t : Fin 2 → ℝ) : ⟪Γ.equivFun.symm t, Γ.dual.b₀⟫ = t 0 := by
  simp [inner_add_left, real_inner_smul_left]

/-- The second coordinate of `t 0 • b₀ + t 1 • b₁` is `t 1`. -/
@[simp]
theorem inner_equivFun_symm_dual_b₁ (t : Fin 2 → ℝ) : ⟪Γ.equivFun.symm t, Γ.dual.b₁⟫ = t 1 := by
  simp [inner_add_left, real_inner_smul_left]

/-- The pairing of `t 0 • b₀ + t 1 • b₁` with the dual lattice point `m b₀* + n b₁*` is
`t 0 * m + t 1 * n`. -/
theorem inner_equivFun_symm_dual_point (t : Fin 2 → ℝ) (p : ℤ × ℤ) :
    ⟪Γ.equivFun.symm t, Γ.dual.point p⟫ = t 0 * p.1 + t 1 * p.2 := by
  simp only [point, inner_add_right, real_inner_smul_right, inner_equivFun_symm_dual_b₀,
    inner_equivFun_symm_dual_b₁]
  ring

/-- If `s ≡ t` modulo `ℤ²`, then `s 0 • b₀ + s 1 • b₁ ≡ t 0 • b₀ + t 1 • b₁` modulo `Γ`. -/
theorem equivFun_symm_sub_mem_points {s t : Fin 2 → ℝ}
    (h : ∀ i, (s i : UnitAddCircle) = t i) :
    Γ.equivFun.symm s - Γ.equivFun.symm t ∈ Γ.points := by
  have key (i : Fin 2) : ∃ n : ℤ, s i - t i = n := by
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := s i - t i)).mp
      (by rw [AddCircle.coe_sub, h i, sub_self])
    exact ⟨n, by rw [← hn, zsmul_one]⟩
  obtain ⟨m, hm⟩ := key 0
  obtain ⟨n, hn⟩ := key 1
  rw [mem_points_iff_inner]
  exact ⟨⟨m, by rw [inner_sub_left, inner_equivFun_symm_dual_b₀, inner_equivFun_symm_dual_b₀, hm]⟩,
    n, by rw [inner_sub_left, inner_equivFun_symm_dual_b₁, inner_equivFun_symm_dual_b₁, hn]⟩

/-- A periodic function takes the same value at `s 0 • b₀ + s 1 • b₁` and `t 0 • b₀ + t 1 • b₁`
when `s ≡ t` modulo `ℤ²`. -/
theorem IsPeriodic.apply_equivFun_symm_eq {Γ : PlaneLattice} {α : Type*} {f : Plane → α}
    (hf : Γ.IsPeriodic f) {s t : Fin 2 → ℝ} (h : ∀ i, (s i : UnitAddCircle) = t i) :
    f (Γ.equivFun.symm s) = f (Γ.equivFun.symm t) :=
  hf.apply_eq_of_sub_mem (Γ.equivFun_symm_sub_mem_points h)

/-- For a periodic function, `f (torusSection (t mod 1)) = f (t 0 • b₀ + t 1 • b₁)`. -/
theorem IsPeriodic.apply_torusSection_coe {Γ : PlaneLattice} {α : Type*} {f : Plane → α}
    (hf : Γ.IsPeriodic f) (t : Fin 2 → ℝ) :
    f (Γ.torusSection fun i ↦ (t i : UnitAddCircle)) = f (Γ.equivFun.symm t) :=
  hf.apply_equivFun_symm_eq fun _ ↦ AddCircle.coe_equivIoc

/-- For a periodic function, `f (torusSection (coordinates of x mod 1)) = f x`. -/
theorem IsPeriodic.apply_torusSection_equivFun {Γ : PlaneLattice} {α : Type*} {f : Plane → α}
    (hf : Γ.IsPeriodic f) (x : Plane) :
    f (Γ.torusSection fun i ↦ (Γ.equivFun x i : UnitAddCircle)) = f x := by
  rw [hf.apply_torusSection_coe, LinearEquiv.symm_apply_apply]

/-- A continuous periodic function on the plane descends to a continuous function on the
standard torus. -/
theorem IsPeriodic.continuous_comp_torusSection {Γ : PlaneLattice} {X : Type*}
    [TopologicalSpace X] {f : Plane → X} (hf : Γ.IsPeriodic f) (hc : Continuous f) :
    Continuous (f ∘ Γ.torusSection) := by
  refine continuous_iff_continuousAt.mpr fun θ₀ ↦ ?_
  let a : Fin 2 → ℝ := fun i ↦ (AddCircle.equivIoc 1 0 (θ₀ i) : ℝ) + 1 / 2
  have ha (i : Fin 2) : θ₀ i ≠ (a i : UnitAddCircle) := by
    intro h
    have hcoe : ((a i : ℝ) : UnitAddCircle) = θ₀ i + ((1 / 2 : ℝ) : UnitAddCircle) := by
      simp only [a, AddCircle.coe_add, AddCircle.coe_equivIoc]
    rw [hcoe, left_eq_add] at h
    have := (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ)) (a := 1 / 2)
      ⟨by norm_num, by norm_num⟩).mp h
    norm_num at this
  have heq : f ∘ Γ.torusSection =
      fun θ ↦ f (Γ.equivFun.symm fun i ↦ (AddCircle.equivIoc 1 (a i) (θ i) : ℝ)) := by
    funext θ
    exact hf.apply_equivFun_symm_eq fun i ↦ by simp only [AddCircle.coe_equivIoc]
  rw [heq]
  have hrep : ContinuousAt
      (fun θ : UnitAddTorus (Fin 2) ↦ fun i ↦ (AddCircle.equivIoc 1 (a i) (θ i) : ℝ)) θ₀ :=
    continuousAt_pi.mpr fun i ↦ continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIoc 1 (a i) (ha i)).comp
        (f := fun θ : UnitAddTorus (Fin 2) ↦ θ i) (continuous_apply i).continuousAt)
  exact hc.continuousAt.comp
    (Γ.equivFun.symm.toContinuousLinearEquiv.continuous.continuousAt.comp hrep)

/-- The characters of the standard torus are the characters `𝐞 ⟪·, k⟫`, `k ∈ Γ*`, of the plane:
`mFourier n (t mod 1) = 𝐞 ⟪t 0 • b₀ + t 1 • b₁, n 0 b₀* + n 1 b₁*⟫`. -/
theorem mFourier_coe (n : Fin 2 → ℤ) (t : Fin 2 → ℝ) :
    mFourier n (fun i ↦ (t i : UnitAddCircle)) =
      (𝐞 ⟪Γ.equivFun.symm t, Γ.dual.point (n 0, n 1)⟫ : ℂ) := by
  rw [inner_equivFun_symm_dual_point, Real.fourierChar_apply]
  simp only [mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two, fourier_coe_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The characters of the standard torus along the section of the torus. -/
theorem mFourier_eq_fourierChar_torusSection (n : Fin 2 → ℤ) (θ : UnitAddTorus (Fin 2)) :
    mFourier n θ = (𝐞 ⟪Γ.torusSection θ, Γ.dual.point (n 0, n 1)⟫ : ℂ) := by
  have hθ : θ = fun i ↦ ((AddCircle.equivIoc 1 0 (θ i) : ℝ) : UnitAddCircle) :=
    funext fun _ ↦ AddCircle.coe_equivIoc.symm
  conv_lhs => rw [hθ]
  exact Γ.mFourier_coe n _

/-- The bijection `ℤ² ≃ Γ*`, `n ↦ n 0 b₀* + n 1 b₁*`, indexing the characters of the standard
torus by the dual lattice. -/
noncomputable def dualIndexEquiv : (Fin 2 → ℤ) ≃ Γ.dual.points :=
  (piFinTwoEquiv fun _ ↦ ℤ).trans Γ.dual.pointEquiv

/-- The dual lattice point indexed by `n` is `n 0 b₀* + n 1 b₁*`. -/
@[simp]
theorem coe_dualIndexEquiv (n : Fin 2 → ℤ) :
    (Γ.dualIndexEquiv n : Plane) = Γ.dual.point (n 0, n 1) :=
  rfl

/-- The dual lattice point indexed by `n` vanishes iff `n = 0`. -/
theorem coe_dualIndexEquiv_eq_zero {n : Fin 2 → ℤ} : (Γ.dualIndexEquiv n : Plane) = 0 ↔ n = 0 := by
  rw [coe_dualIndexEquiv, ← Γ.dual.point_zero, Γ.dual.point_injective.eq_iff, Prod.mk_eq_zero,
    funext_iff, Fin.forall_fin_two, Pi.zero_apply, Pi.zero_apply]

/-! ### Fourier coefficients -/

section FourierCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Fourier coefficient `f̂(k) = ∫_cell e^{-2πi⟪x, k⟫} f(x) dx` of a function on the torus
`ℝ²/Γ`, for `k` (in applications) in the dual lattice. -/
noncomputable def fourierCoeff (f : Plane → E) (k : Plane) : E :=
  ∫ x in Γ.cell, 𝐞 (-⟪x, k⟫) • f x

/-- Unfolding lemma for `PlaneLattice.fourierCoeff`. -/
theorem fourierCoeff_def (f : Plane → E) (k : Plane) :
    Γ.fourierCoeff f k = ∫ x in Γ.cell, 𝐞 (-⟪x, k⟫) • f x :=
  rfl

/-- The zeroth Fourier coefficient is the integral over the cell. -/
theorem fourierCoeff_zero (f : Plane → E) : Γ.fourierCoeff f 0 = ∫ x in Γ.cell, f x := by
  simp [fourierCoeff]

/-- The Fourier coefficients of `f` are those of the function `f ∘ torusSection` on the standard
torus, up to the factor `covolume`. -/
theorem mFourierCoeff_comp_torusSection (f : Plane → E) (n : Fin 2 → ℤ) :
    mFourierCoeff (f ∘ Γ.torusSection) n =
      Γ.covolume⁻¹ • Γ.fourierCoeff f (Γ.dual.point (n 0, n 1)) := by
  rw [mFourierCoeff, fourierCoeff, ← Γ.integral_comp_torusSection]
  congr 1 with θ
  rw [Γ.mFourier_eq_fourierChar_torusSection, Function.comp_apply, Circle.smul_def]
  simp only [Pi.neg_apply, ← Prod.neg_mk, point_neg, inner_neg_right]

/-- The Fourier coefficients are bounded by the `L¹` norm on the cell. -/
theorem norm_fourierCoeff_le (f : Plane → E) (k : Plane) :
    ‖Γ.fourierCoeff f k‖ ≤ ∫ x in Γ.cell, ‖f x‖ :=
  (norm_integral_le_integral_norm _).trans_eq (by simp)

/-- The Fourier coefficients are additive. -/
theorem fourierCoeff_add {f g : Plane → E} (hf : IntegrableOn f Γ.cell)
    (hg : IntegrableOn g Γ.cell) (k : Plane) :
    Γ.fourierCoeff (f + g) k = Γ.fourierCoeff f k + Γ.fourierCoeff g k := by
  simp only [fourierCoeff, Pi.add_apply, smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff k).mpr hf)
    ((Real.fourierIntegral_convergent_iff k).mpr hg)

/-- The Fourier coefficients commute with negation. -/
theorem fourierCoeff_neg (f : Plane → E) (k : Plane) :
    Γ.fourierCoeff (-f) k = -Γ.fourierCoeff f k := by
  simp [fourierCoeff, integral_neg]

/-- The Fourier coefficients are subtractive. -/
theorem fourierCoeff_sub {f g : Plane → E} (hf : IntegrableOn f Γ.cell)
    (hg : IntegrableOn g Γ.cell) (k : Plane) :
    Γ.fourierCoeff (f - g) k = Γ.fourierCoeff f k - Γ.fourierCoeff g k := by
  rw [sub_eq_add_neg, Γ.fourierCoeff_add hf hg.neg, fourierCoeff_neg, sub_eq_add_neg]

/-- The Fourier coefficients are `ℂ`-linear. -/
theorem fourierCoeff_const_smul (c : ℂ) (f : Plane → E) (k : Plane) :
    Γ.fourierCoeff (c • f) k = c • Γ.fourierCoeff f k := by
  simp only [fourierCoeff, Pi.smul_apply, Circle.smul_def, smul_comm _ c]
  exact integral_smul c _

/-- The character `𝐞 (-⟪·, k⟫)` is invariant under translations by `Γ` when `k ∈ Γ*`. -/
theorem fourierChar_neg_inner_add {v k : Plane} (hv : v ∈ Γ.points) (hk : k ∈ Γ.dual.points)
    (x : Plane) : 𝐞 (-⟪x + v, k⟫) = 𝐞 (-⟪x, k⟫) := by
  simpa only [inner_neg_right] using Γ.fourierChar_inner_add hv (neg_mem hk) x

/-- The Fourier coefficients of a translate: `(f(· + y))^(k) = 𝐞 ⟪y, k⟫ f̂(k)` for periodic `f`. -/
theorem IsPeriodic.fourierCoeff_comp_add {f : Plane → E} (hf : Γ.IsPeriodic f) (y : Plane)
    {k : Plane} (hk : k ∈ Γ.dual.points) :
    Γ.fourierCoeff (fun x ↦ f (x + y)) k = 𝐞 ⟪y, k⟫ • Γ.fourierCoeff f k := by
  set F : Plane → E := fun x ↦ 𝐞 (-⟪x - y, k⟫) • f x
  have hF : Γ.IsPeriodic F := fun v hv x ↦ by
    simp only [F, sub_eq_add_neg, add_right_comm x v, Γ.fourierChar_neg_inner_add hv hk,
      hf v hv]
  have h := hF.setIntegral_cell_comp_add y
  simp only [F, add_sub_cancel_right] at h
  rw [fourierCoeff, h, fourierCoeff, Circle.smul_def, ← integral_smul]
  congr 1 with x
  rw [Circle.smul_def, Circle.smul_def, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
    inner_sub_left]
  ring_nf

end FourierCoeff

/-! ### Orthogonality of the characters -/

/-- The integral of a character of the standard torus. -/
theorem integral_mFourier (n : Fin 2 → ℤ) :
    ∫ θ, mFourier n θ = if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin 2))) 0 n
  simp only [mFourierLp, ContinuousMap.inner_toLp, mFourier_zero] at h
  simpa [eq_comm] using h

/-- **Orthogonality of the characters.** For `k ∈ Γ*`,
`∫_cell 𝐞 ⟪x, k⟫ dx = covolume Γ` if `k = 0` and `0` otherwise. -/
theorem integral_cell_fourierChar {k : Plane} (hk : k ∈ Γ.dual.points) :
    ∫ x in Γ.cell, (𝐞 ⟪x, k⟫ : ℂ) = if k = 0 then (Γ.covolume : ℂ) else 0 := by
  obtain ⟨n, hn⟩ := Γ.dualIndexEquiv.surjective ⟨k, hk⟩
  obtain rfl : k = Γ.dual.point (n 0, n 1) := by rw [← coe_dualIndexEquiv, hn]
  have h := Γ.integral_comp_torusSection fun x ↦ (𝐞 ⟪x, Γ.dual.point (n 0, n 1)⟫ : ℂ)
  simp only [← Γ.mFourier_eq_fourierChar_torusSection, integral_mFourier] at h
  rw [eq_comm, inv_smul_eq_iff₀ Γ.covolume_ne_zero] at h
  rw [h]
  by_cases hn0 : n = 0
  · subst hn0
    have h0 : Γ.dual.point (0, 0) = 0 := Γ.dual.point_zero
    simp [h0]
  · have : Γ.dual.point (n 0, n 1) ≠ 0 := by
      rwa [← coe_dualIndexEquiv, Ne, coe_dualIndexEquiv_eq_zero]
    simp [hn0, this]

/-- **Orthogonality of the characters.** For `k, k' ∈ Γ*`, the `k'`-th Fourier coefficient of the
character `𝐞 ⟪·, k⟫` is `covolume Γ` if `k = k'` and `0` otherwise. -/
theorem fourierCoeff_fourierChar {k k' : Plane} (hk : k ∈ Γ.dual.points)
    (hk' : k' ∈ Γ.dual.points) :
    Γ.fourierCoeff (fun x ↦ (𝐞 ⟪x, k⟫ : ℂ)) k' = if k = k' then (Γ.covolume : ℂ) else 0 := by
  have h (x : Plane) : 𝐞 (-⟪x, k'⟫) • (𝐞 ⟪x, k⟫ : ℂ) = (𝐞 ⟪x, k - k'⟫ : ℂ) := by
    rw [Circle.smul_def, smul_eq_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_sub_right,
      neg_add_eq_sub]
  simp only [fourierCoeff, h]
  rw [Γ.integral_cell_fourierChar (sub_mem hk hk')]
  simp [sub_eq_zero]

/-! ### Fourier inversion -/

/-- The Fourier coefficients of a function on the standard torus pulled back from a function on
the plane, indexed by the dual lattice. -/
theorem mFourierCoeff_comp_torusSection_eq (f : Plane → ℂ) (n : Fin 2 → ℤ) :
    mFourierCoeff (f ∘ Γ.torusSection) n =
      Γ.covolume⁻¹ • Γ.fourierCoeff f (Γ.dualIndexEquiv n) :=
  Γ.mFourierCoeff_comp_torusSection f n

/-- Summability of the Fourier coefficients transfers to the standard torus. -/
theorem summable_mFourierCoeff_comp_torusSection {f : Plane → ℂ}
    (hs : Summable fun k : Γ.dual.points ↦ Γ.fourierCoeff f k) :
    Summable (mFourierCoeff (f ∘ Γ.torusSection)) := by
  rw [funext (Γ.mFourierCoeff_comp_torusSection_eq f)]
  exact (Γ.dualIndexEquiv.summable_iff.mpr hs).const_smul _

/-- **Fourier inversion.** A continuous `Γ`-periodic function with summable Fourier coefficients is
the sum of its Fourier series: `f x = N⁻¹ ∑_{k ∈ Γ*} f̂(k) 𝐞 ⟪x, k⟫`. -/
theorem hasSum_fourierCoeff_smul_fourierChar {f : Plane → ℂ} (hc : Continuous f)
    (hf : Γ.IsPeriodic f) (hs : Summable fun k : Γ.dual.points ↦ Γ.fourierCoeff f k)
    (x : Plane) :
    HasSum (fun k : Γ.dual.points ↦ Γ.covolume⁻¹ • 𝐞 ⟪x, (k : Plane)⟫ • Γ.fourierCoeff f k)
      (f x) := by
  let F : C(UnitAddTorus (Fin 2), ℂ) := ⟨f ∘ Γ.torusSection, hf.continuous_comp_torusSection hc⟩
  have h := hasSum_mFourier_series_apply_of_summable (f := F)
    (Γ.summable_mFourierCoeff_comp_torusSection hs) (fun i ↦ (Γ.equivFun x i : UnitAddCircle))
  have hx : F (fun i ↦ (Γ.equivFun x i : UnitAddCircle)) = f x :=
    hf.apply_torusSection_equivFun x
  rw [hx] at h
  rw [← Γ.dualIndexEquiv.hasSum_iff]
  have e : (fun k : Γ.dual.points ↦ Γ.covolume⁻¹ • 𝐞 ⟪x, (k : Plane)⟫ • Γ.fourierCoeff f k) ∘
      Γ.dualIndexEquiv = fun n ↦ mFourierCoeff (f ∘ Γ.torusSection) n •
        mFourier n (fun i ↦ (Γ.equivFun x i : UnitAddCircle)) := by
    funext n
    rw [Γ.mFourierCoeff_comp_torusSection_eq, Γ.mFourier_coe, LinearEquiv.symm_apply_apply,
      Function.comp_apply, coe_dualIndexEquiv, Circle.smul_def, smul_eq_mul, smul_eq_mul,
      smul_mul_assoc, mul_comm]
  rw [e]
  exact h

/-- **Fourier inversion, uniform version.** The Fourier series of a continuous `Γ`-periodic
function with summable Fourier coefficients converges uniformly to it. -/
theorem hasSumUniformly_fourierCoeff_smul_fourierChar {f : Plane → ℂ} (hc : Continuous f)
    (hf : Γ.IsPeriodic f) (hs : Summable fun k : Γ.dual.points ↦ Γ.fourierCoeff f k) :
    HasSumUniformly
      (fun (k : Γ.dual.points) (x : Plane) ↦ Γ.covolume⁻¹ • 𝐞 ⟪x, (k : Plane)⟫ • Γ.fourierCoeff f k)
      f := by
  let F : C(UnitAddTorus (Fin 2), ℂ) := ⟨f ∘ Γ.torusSection, hf.continuous_comp_torusSection hc⟩
  have h := hasSum_mFourier_series_of_summable (f := F)
    (Γ.summable_mFourierCoeff_comp_torusSection hs)
  have hU := (ContinuousMap.tendsto_iff_tendstoUniformly.mp h).comp
    (fun x : Plane ↦ fun i ↦ (Γ.equivFun x i : UnitAddCircle))
  have hF : (⇑F ∘ fun x : Plane ↦ fun i ↦ (Γ.equivFun x i : UnitAddCircle)) = f :=
    funext fun x ↦ hf.apply_torusSection_equivFun x
  rw [hF] at hU
  have e : (fun (s : Finset (Fin 2 → ℤ)) (x : Plane) ↦ ∑ n ∈ s,
      Γ.covolume⁻¹ • 𝐞 ⟪x, (Γ.dualIndexEquiv n : Plane)⟫ • Γ.fourierCoeff f (Γ.dualIndexEquiv n))
      = fun s ↦ (fun θ ↦ (∑ n ∈ s, mFourierCoeff F n • mFourier n) θ) ∘
        fun x : Plane ↦ fun i ↦ (Γ.equivFun x i : UnitAddCircle) := by
    funext s x
    simp only [Function.comp_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.coe_smul, Pi.smul_apply]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    change _ = mFourierCoeff (f ∘ Γ.torusSection) n • _
    rw [Γ.mFourierCoeff_comp_torusSection_eq, Γ.mFourier_coe, LinearEquiv.symm_apply_apply,
      coe_dualIndexEquiv, Circle.smul_def, smul_eq_mul, smul_eq_mul, smul_mul_assoc, mul_comm]
  have key : HasSumUniformly (fun (n : Fin 2 → ℤ) (x : Plane) ↦
      Γ.covolume⁻¹ • 𝐞 ⟪x, (Γ.dualIndexEquiv n : Plane)⟫ • Γ.fourierCoeff f (Γ.dualIndexEquiv n))
      f := by
    rw [hasSumUniformly_iff_tendstoUniformly, e]
    exact hU
  exact (Γ.dualIndexEquiv.hasSum_iff).mp key

/-- **Uniqueness of Fourier coefficients.** A continuous periodic function whose Fourier
coefficients vanish on `Γ*` is zero. -/
theorem eq_zero_of_fourierCoeff_eq_zero {f : Plane → ℂ} (hc : Continuous f) (hf : Γ.IsPeriodic f)
    (h : ∀ k ∈ Γ.dual.points, Γ.fourierCoeff f k = 0) : f = 0 := by
  have h' (k : Γ.dual.points) : Γ.fourierCoeff f k = 0 := h k k.2
  funext x
  have := Γ.hasSum_fourierCoeff_smul_fourierChar hc hf (by simp only [h']; exact summable_zero) x
  simp only [h', smul_zero] at this
  exact this.unique hasSum_zero

/-! ### Parseval's identity -/

/-- A function square integrable on the cell pulls back to a square integrable function on the
standard torus. -/
theorem memLp_comp_torusSection {E : Type*} [NormedAddCommGroup E] {f : Plane → E} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict Γ.cell)) : MemLp (f ∘ Γ.torusSection) p volume :=
  (hf.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving Γ.measurePreserving_torusSection

/-- **Parseval's identity.** For `f, g` square integrable on the cell,
`∑_{k ∈ Γ*} conj (f̂(k)) ĝ(k) = N ∫_cell conj (f x) g x`. -/
theorem hasSum_conj_mul_fourierCoeff {f g : Plane → ℂ} (hf : MemLp f 2 (volume.restrict Γ.cell))
    (hg : MemLp g 2 (volume.restrict Γ.cell)) :
    HasSum (fun k : Γ.dual.points ↦ conj (Γ.fourierCoeff f k) * Γ.fourierCoeff g k)
      (Γ.covolume * ∫ x in Γ.cell, conj (f x) * g x) := by
  have hf' := Γ.memLp_comp_torusSection hf
  have hg' := Γ.memLp_comp_torusSection hg
  have h := hasSum_prod_mFourierCoeff (hf'.toLp _) (hg'.toLp _)
  have e₁ (n : Fin 2 → ℤ) : mFourierCoeff (hf'.toLp _) n = mFourierCoeff (f ∘ Γ.torusSection) n :=
    integral_congr_ae (hf'.coeFn_toLp.mono fun θ hθ ↦ by simp only [hθ])
  have e₂ (n : Fin 2 → ℤ) : mFourierCoeff (hg'.toLp _) n = mFourierCoeff (g ∘ Γ.torusSection) n :=
    integral_congr_ae (hg'.coeFn_toLp.mono fun θ hθ ↦ by simp only [hθ])
  have e₃ : ∫ θ, conj ((hf'.toLp _) θ) * (hg'.toLp _) θ =
      Γ.covolume⁻¹ • ∫ x in Γ.cell, conj (f x) * g x := by
    rw [← Γ.integral_comp_torusSection fun x ↦ conj (f x) * g x]
    exact integral_congr_ae ((hf'.coeFn_toLp.and hg'.coeFn_toLp).mono fun θ hθ ↦ by
      simp only [hθ.1, hθ.2, Function.comp_apply])
  simp only [e₁, e₂, e₃, mFourierCoeff_comp_torusSection_eq] at h
  have h' := h.mul_left ((Γ.covolume : ℂ) ^ 2)
  have hN : (Γ.covolume : ℂ) ≠ 0 := by exact_mod_cast Γ.covolume_ne_zero
  rw [← Γ.dualIndexEquiv.hasSum_iff]
  convert h' using 1
  · funext n
    simp only [Function.comp_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    push_cast
    field_simp
  · rw [Complex.real_smul]
    push_cast
    field_simp

/-- **Parseval's identity.** For `f` square integrable on the cell,
`∑_{k ∈ Γ*} |f̂(k)|² = N ∫_cell |f|²`. -/
theorem hasSum_sq_norm_fourierCoeff {f : Plane → ℂ} (hf : MemLp f 2 (volume.restrict Γ.cell)) :
    HasSum (fun k : Γ.dual.points ↦ ‖Γ.fourierCoeff f k‖ ^ 2)
      (Γ.covolume * ∫ x in Γ.cell, ‖f x‖ ^ 2) := by
  have h := Γ.hasSum_conj_mul_fourierCoeff hf hf
  simp only [Complex.conj_mul', ← Complex.ofReal_pow] at h
  rw [integral_complex_ofReal, ← Complex.ofReal_mul] at h
  exact Complex.hasSum_ofReal.mp h

/-- **Uniqueness of Fourier coefficients.** A function square integrable on the cell whose
Fourier coefficients vanish on `Γ*` vanishes almost everywhere on the cell. -/
theorem ae_eq_zero_of_fourierCoeff_eq_zero {f : Plane → ℂ}
    (hf : MemLp f 2 (volume.restrict Γ.cell)) (h : ∀ k ∈ Γ.dual.points, Γ.fourierCoeff f k = 0) :
    f =ᵐ[volume.restrict Γ.cell] 0 := by
  have hP := Γ.hasSum_sq_norm_fourierCoeff hf
  simp only [h _ (Subtype.mem _), norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hP
  have h0 : ∫ x in Γ.cell, ‖f x‖ ^ 2 = 0 := by
    have := hasSum_zero.unique hP
    exact (mul_eq_zero.mp this.symm).resolve_left Γ.covolume_ne_zero
  have hint : Integrable (fun x ↦ ‖f x‖ ^ 2) (volume.restrict Γ.cell) :=
    (hf : MemLp f (2 : ℕ) _).integrable_norm_pow two_ne_zero
  rw [integral_eq_zero_iff_of_nonneg (fun x ↦ by positivity) hint] at h0
  filter_upwards [h0] with x hx
  simpa using hx

/-! ### Periodizations and absolutely convergent Fourier series -/

/-- **The Fourier coefficients of a periodization are the values of the Fourier transform.**
For integrable `f` and `k ∈ Γ*`, the `k`-th Fourier coefficient of `∑_{v ∈ Γ} f(· + v)` is
`𝓕 f k`. -/
theorem fourierCoeff_tsum_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : Plane → E} (hf : Integrable f) {k : Plane} (hk : k ∈ Γ.dual.points) :
    Γ.fourierCoeff (fun x ↦ ∑' v : Γ.points, f (x + v)) k = 𝓕 f k := by
  rw [Real.fourier_eq, ← Γ.integral_cell_tsum_comp_add
    ((Real.fourierIntegral_convergent_iff k).mpr hf), fourierCoeff]
  congr 1 with x
  rw [Circle.smul_def, ← tsum_const_smul'']
  congr 1 with v
  rw [Circle.smul_def, Γ.fourierChar_neg_inner_add v.2 hk x]

/-- The sum of an absolutely convergent Fourier series is periodic. -/
theorem isPeriodic_tsum_smul_fourierChar (c : Γ.dual.points → ℂ) :
    Γ.IsPeriodic fun x ↦ ∑' k : Γ.dual.points, 𝐞 ⟪x, (k : Plane)⟫ • c k :=
  fun v hv x ↦ by simp only [Γ.fourierChar_inner_add hv (Subtype.mem _)]

/-- The sum of an absolutely convergent Fourier series is continuous. -/
theorem continuous_tsum_smul_fourierChar {c : Γ.dual.points → ℂ} (hc : Summable c) :
    Continuous fun x ↦ ∑' k : Γ.dual.points, 𝐞 ⟪x, (k : Plane)⟫ • c k :=
  continuous_tsum (fun k ↦ by fun_prop) hc.norm fun k x ↦ by simp

/-- **The Fourier coefficients of an absolutely convergent Fourier series.** For summable `c`
and `k' ∈ Γ*`, the `k'`-th Fourier coefficient of `∑_{k ∈ Γ*} c k 𝐞 ⟪·, k⟫` is `N c k'`. -/
theorem fourierCoeff_tsum_smul_fourierChar {c : Γ.dual.points → ℂ} (hc : Summable c)
    (k' : Γ.dual.points) :
    Γ.fourierCoeff (fun x ↦ ∑' k : Γ.dual.points, 𝐞 ⟪x, (k : Plane)⟫ • c k) k' =
      Γ.covolume * c k' := by
  have hfin : volume Γ.cell < ∞ := by rw [volume_cell]; exact ENNReal.ofReal_lt_top
  simp only [fourierCoeff, Circle.smul_def, ← tsum_const_smul'']
  rw [integral_tsum (fun k ↦ by fun_prop) ?_]
  · simp only [← Circle.smul_def]
    have h (k : Γ.dual.points) : ∫ x in Γ.cell, 𝐞 (-⟪x, (k' : Plane)⟫) • 𝐞 ⟪x, (k : Plane)⟫ • c k =
        (if (k : Plane) = k' then (Γ.covolume : ℂ) else 0) * c k := by
      rw [← Γ.fourierCoeff_fourierChar k.2 k'.2, fourierCoeff, ← integral_mul_const]
      congr 1 with x
      simp [Circle.smul_def, mul_assoc]
    simp only [h, Subtype.coe_inj]
    rw [tsum_eq_single k' fun k hk ↦ by simp [hk]]
    simp
  · have h (k : Γ.dual.points) : ∫⁻ x in Γ.cell, ‖(𝐞 (-⟪x, (k' : Plane)⟫) : ℂ) •
        (𝐞 ⟪x, (k : Plane)⟫ : ℂ) • c k‖ₑ = ‖c k‖ₑ * volume Γ.cell := by
      simp
    simp only [h]
    rw [ENNReal.tsum_mul_right]
    refine ENNReal.mul_ne_top ?_ hfin.ne
    simp only [enorm_eq_nnnorm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr
      (NNReal.summable_coe.mp (by simpa only [coe_nnnorm] using hc.norm))

end PlaneLattice

end TriangularLattice
