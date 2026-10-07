/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Rigidity.FullVertex
public import TriangularLattice.Rigidity.Hexagon

/-!
# Disjoint hexagonal cells

Section 5.3 of the manuscript: the shrinking factors `κ_p = 4 (s_p + a_p)` (5.kappa), the cells
`cell(p) = p + (1 - κ_p) H_{θ_p}`, Lemma 5.6 (`lem:cells`) on their disjointness, and the
pointwise estimates behind (5.kappasum).

Since `H_θ` is open, the cells are open, and cells of distinct retained points are disjoint (not
only their interiors).

## Main definitions

* `TriangularLattice.kappa` (`κ_p`), `TriangularLattice.cell` (`cell(p)`).

## Main results

* `TriangularLattice.IsSlotAssignment.kappa_lt`: `0 ≤ κ_p < 10⁻²`.
* `TriangularLattice.IsOrientation.disjoint_cell`: cells of distinct retained points are disjoint
  (Lemma 5.6).
* `TriangularLattice.kappa_sq_le`, `TriangularLattice.IsSlotAssignment.dirErrMax_sq_le_of_isFull`,
  `TriangularLattice.IsSlotAssignment.dirErrMax_sq_le`, `TriangularLattice.orientDiff_sq_le`,
  `TriangularLattice.IsSlotAssignment.norm_endpointErr_sq_le_of_isFull`,
  `TriangularLattice.IsSlotAssignment.norm_endpointErr_sq_le`: the pointwise bounds behind
  (5.kappasum): `κ_p² ≤ 32 (s_p² + a_p²)`, `a_p² ≤ A_dir² e_p` at full vertices, `a_p² ≤ 36 ε`,
  `Δ_pq² ≤ 2 (a_p² + a_q²)`, `|err_{p,s}|² ≤ ℓ² (1 + A_dir)² e_p` at full vertices and
  `|err_{p,s}|² ≤ ℓ² (1 + A'_dir)² ε`.
-/

@[expose] public section

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace TriangularLattice

variable {ε : ℝ} {X : Set Plane} {p q : Plane} {θ : ℝ} {σ : Plane → Fin 6} {j : Fin 6}

/-- The shrinking factor `κ_p = 4 (s_p + a_p)` of (5.kappa). -/
noncomputable def kappa (ε : ℝ) (X : Set Plane) (p : Plane) (θ : ℝ) (σ : Plane → Fin 6) : ℝ :=
  4 * (strainMax ε X p + dirErrMax ε X p θ σ)

/-- The cell `cell(p) = p + (1 - κ_p) H_θ` of (5.kappa). -/
noncomputable def cell (ε : ℝ) (X : Set Plane) (p : Plane) (θ : ℝ) (σ : Plane → Fin 6) :
    Set Plane :=
  hexCell p (1 - kappa ε X p θ σ) θ

theorem kappa_nonneg : 0 ≤ kappa ε X p θ σ := by
  have := strainMax_nonneg (ε := ε) (X := X) (p := p)
  have := dirErrMax_nonneg (ε := ε) (X := X) (p := p) (θ := θ) (σ := σ)
  unfold kappa
  positivity

namespace IsSlotAssignment

/-- `κ_p ≤ 4 (ε + 4√ε)` at every vertex (in particular `κ_p ≤ 4 (ε + 6√ε)`). -/
theorem kappa_le (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ) :
    kappa ε X p θ σ ≤ 4 * (ε + 4 * √ε) := by
  have := hX.strainMax_le_eps (p := p)
  have := h.dirErrMax_le hX
  unfold kappa
  linarith

/-- `κ_p ≤ 4 (ε + 300 ε)` at a full vertex. -/
theorem kappa_le_of_isFull (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) : kappa ε X p θ σ ≤ 4 * (ε + 300 * ε) := by
  have := hX.strainMax_le_eps (p := p)
  have := (h.dirErrMax_le_of_isFull hX hp).2
  unfold kappa
  linarith

/-- `0 ≤ κ_p < 10⁻²`. -/
theorem kappa_lt (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ) :
    kappa ε X p θ σ < 1 / 100 := by
  have := h.kappa_le hX
  have := hX.sqrt_le
  have := hX.le_small
  linarith

theorem one_sub_kappa_pos (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ) :
    0 < 1 - kappa ε X p θ σ := by
  linarith [h.kappa_lt hX]

theorem mem_cell_iff (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ) {x : Plane} :
    x ∈ cell ε X p θ σ ↔ ∀ j : Fin 6,
      ⟪x - p, unitVec (slotAngle θ j)⟫ < (1 - kappa ε X p θ σ) * (latticeSpacing / 2) :=
  mem_hexCell_iff (h.one_sub_kappa_pos hX)

/-- Points of `cell(p)` lie within the circumradius `ℓ/√3` of `p`. -/
theorem norm_sub_lt_of_mem_cell (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    {x : Plane} (hx : x ∈ cell ε X p θ σ) : ‖x - p‖ < latticeSpacing / √3 := by
  have h1 := norm_sub_lt_of_mem_hexCell (h.one_sub_kappa_pos hX) hx
  have h2 : 0 ≤ latticeSpacing / √3 := by have := latticeSpacing_pos; positivity
  have := kappa_nonneg (ε := ε) (X := X) (p := p) (θ := θ) (σ := σ)
  nlinarith

end IsSlotAssignment

/-! ### Disjointness of the cells -/

/-- The half-width of `cell(p)` along a nearest edge. -/
private theorem half_width_le {s a ℓ : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (hℓ : 0 < ℓ) :
    (1 - 4 * (s + a)) * (ℓ / 2 + ℓ / √3 * a) ≤ ℓ * (1 / 2 - 2 * s - a) := by
  have h3 : 1 ≤ √3 := by rw [Real.one_le_sqrt]; norm_num
  have hc : ℓ / √3 * a ≤ ℓ * a := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hℓ.le ha]
  have hc0 : 0 ≤ ℓ / √3 * a := by positivity
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (add_nonneg hs ha)) hc0]

/-- The unit vector along `q - p` is `e_{arg (q - p)}`. -/
private theorem smul_sub_eq_unitVec {v : Plane} (hv : v ≠ 0) :
    ‖v‖⁻¹ • v = unitVec (vecArg v) := by
  calc ‖v‖⁻¹ • v = ‖v‖⁻¹ • (‖v‖ • unitVec (vecArg v)) := by rw [norm_smul_unitVec_vecArg]
    _ = unitVec (vecArg v) := by
        rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv), one_smul]

/-- **Lemma 5.6.** Cells of distinct retained points are disjoint. -/
theorem IsOrientation.disjoint_cell {θ : Plane → ℝ} {σ : Plane → Plane → Fin 6}
    (hX : IsRetainedSet ε X) (h : IsOrientation ε X θ σ) (hp : p ∈ X) (hq : q ∈ X)
    (hpq : p ≠ q) : Disjoint (cell ε X p (θ p) (σ p)) (cell ε X q (θ q) (σ q)) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  have hℓ := latticeSpacing_pos
  have hε := hX.le_small
  have hε0 := hX.pos
  have h3 := sqrt_three_lt
  have h3' := lt_sqrt_three
  have hs3 : 0 < √3 := by positivity
  by_cases hnb : q ∈ nbrs ε X p
  · -- `p` and `q` are nearest neighbors: the cells are separated by a strip.
    have hqp : p ∈ nbrs ε X q := mem_nbrs_comm hp hnb
    have hv : q - p ≠ 0 := hX.sub_ne_zero_of_mem_nbrs hnb
    have hv' : p - q ≠ 0 := hX.sub_ne_zero_of_mem_nbrs hqp
    set u := ‖q - p‖⁻¹ • (q - p) with hu
    have hu' : -u = unitVec (vecArg (p - q)) := by
      rw [← smul_sub_eq_unitVec hv', hu, ← smul_neg, neg_sub, norm_sub_rev]
    have hup : ‖u - unitVec (slotAngle (θ p) (σ p q))‖ ≤ dirErrMax ε X p (θ p) (σ p) := by
      rw [hu, smul_sub_eq_unitVec hv]
      refine (norm_unitVec_sub_unitVec_le _ _).trans ?_
      have := slotError_le_dirErrMax (θ := θ p) (σ := σ p) hnb
      rwa [slotError, angle_slotAngle_eq_norm hX hnb] at this
    have huq : ‖-u - unitVec (slotAngle (θ q) (σ q p))‖ ≤ dirErrMax ε X q (θ q) (σ q) := by
      rw [hu']
      refine (norm_unitVec_sub_unitVec_le _ _).trans ?_
      have := slotError_le_dirErrMax (θ := θ q) (σ := σ q) hqp
      rwa [slotError, angle_slotAngle_eq_norm hX hqp] at this
    have hrp := (h p hp).one_sub_kappa_pos hX
    have hrq := (h q hq).one_sub_kappa_pos hX
    have h1 := inner_sub_lt_of_mem_hexCell hrp hxp (σ p q) u
    have h2 := inner_sub_lt_of_mem_hexCell hrq hxq (σ q p) (-u)
    have hsum : ⟪x - p, u⟫ + ⟪x - q, -u⟫ = ‖q - p‖ := by
      rw [inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left,
        show x - p - (x - q) = q - p by abel, hu, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [norm_ne_zero_iff.2 hv]
    -- the two half-widths
    set ap := dirErrMax ε X p (θ p) (σ p)
    set aq := dirErrMax ε X q (θ q) (σ q)
    set sp := strainMax ε X p
    set sq := strainMax ε X q
    have hap : 0 ≤ ap := dirErrMax_nonneg
    have haq : 0 ≤ aq := dirErrMax_nonneg
    have hsp : 0 ≤ sp := strainMax_nonneg
    have hsq : 0 ≤ sq := strainMax_nonneg
    have hw1 : (1 - kappa ε X p (θ p) (σ p)) *
        (latticeSpacing / 2 + latticeSpacing / √3 * ‖u - unitVec (slotAngle (θ p) (σ p q))‖) ≤
        latticeSpacing * (1 / 2 - 2 * sp - ap) := by
      refine le_trans ?_ (half_width_le hsp hap hℓ)
      refine mul_le_mul_of_nonneg_left ?_ hrp.le
      gcongr
    have hw2 : (1 - kappa ε X q (θ q) (σ q)) *
        (latticeSpacing / 2 + latticeSpacing / √3 * ‖-u - unitVec (slotAngle (θ q) (σ q p))‖) ≤
        latticeSpacing * (1 / 2 - 2 * sq - aq) := by
      refine le_trans ?_ (half_width_le hsq haq hℓ)
      refine mul_le_mul_of_nonneg_left ?_ hrq.le
      gcongr
    have hlen : latticeSpacing * (1 - sp) ≤ ‖q - p‖ := by
      have := le_strainMax hnb
      rw [abs_le] at this
      have h' : 1 - sp ≤ ‖q - p‖ / latticeSpacing := by linarith
      rwa [le_div_iff₀ hℓ, mul_comm] at h'
    nlinarith
  · -- otherwise the circumdiscs are disjoint
    have hfar := hX.le_norm_sub_of_not_mem_nbrs hp hq hpq.symm hnb
    have h1 := (h p hp).norm_sub_lt_of_mem_cell hX hxp
    have h2 := (h q hq).norm_sub_lt_of_mem_cell hX hxq
    have htri : ‖q - p‖ ≤ ‖x - p‖ + ‖x - q‖ := by
      rw [show q - p = (x - p) - (x - q) by abel]
      exact norm_sub_le _ _
    have hkey : latticeSpacing / √3 * 2 < (√3 - ε) * latticeSpacing := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hs3]
      have : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
      have e : (√3 - ε) * latticeSpacing * √3 = latticeSpacing * (3 - ε * √3) := by
        linear_combination latticeSpacing * this
      rw [e]
      exact mul_lt_mul_of_pos_left (by nlinarith) hℓ
    linarith

/-! ### Pointwise estimates behind (5.kappasum) -/

/-- `κ_p² ≤ 32 (s_p² + a_p²)`. -/
theorem kappa_sq_le :
    kappa ε X p θ σ ^ 2 ≤ 32 * (strainMax ε X p ^ 2 + dirErrMax ε X p θ σ ^ 2) := by
  unfold kappa
  nlinarith [sq_nonneg (strainMax ε X p - dirErrMax ε X p θ σ)]

namespace IsSlotAssignment

/-- `a_p² ≤ A_dir² e_p` at a full vertex, `A_dir = 140`. -/
theorem dirErrMax_sq_le_of_isFull (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) : dirErrMax ε X p θ σ ^ 2 ≤ 140 ^ 2 * strainEnergy ε X p σ := by
  have h1 := (h.dirErrMax_le_of_isFull hX hp).1
  have h0 := dirErrMax_nonneg (ε := ε) (X := X) (p := p) (θ := θ) (σ := σ)
  have he := Real.sq_sqrt (strainEnergy_nonneg (ε := ε) (X := X) (p := p) (σ := σ))
  calc dirErrMax ε X p θ σ ^ 2 ≤ (140 * √(strainEnergy ε X p σ)) ^ 2 := by gcongr
    _ = 140 ^ 2 * strainEnergy ε X p σ := by rw [mul_pow, he]

/-- `a_p² ≤ A'_dir² ε = 36 ε` (at every vertex, in particular at deficient ones). -/
theorem dirErrMax_sq_le (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ) :
    dirErrMax ε X p θ σ ^ 2 ≤ 36 * ε := by
  have h1 := h.dirErrMax_le hX
  have h0 := dirErrMax_nonneg (ε := ε) (X := X) (p := p) (θ := θ) (σ := σ)
  have he := Real.sq_sqrt hX.pos.le
  calc dirErrMax ε X p θ σ ^ 2 ≤ (4 * √ε) ^ 2 := by gcongr
    _ = 16 * ε := by rw [mul_pow, he]; norm_num
    _ ≤ 36 * ε := by linarith [hX.pos]

/-- `|err_{p,s}| ≤ ℓ (1 + A_dir) √e_p` at a full vertex (Lemma 5.5(e)). -/
theorem norm_endpointErr_le_of_isFull (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (j : Fin 6) :
    ‖endpointErr ε X p θ σ j‖ ≤ latticeSpacing * (1 + 140) * √(strainEnergy ε X p σ) := by
  have h1 := norm_endpointErr_le (θ := θ) hX (h.isOccupied_of_isFull hX hp j)
  have h2 := h.strainMax_le_sqrt_strainEnergy hX
  have h3 := (h.dirErrMax_le_of_isFull hX hp).1
  have hℓ := latticeSpacing_pos
  calc _ ≤ latticeSpacing * (strainMax ε X p + dirErrMax ε X p θ σ) := h1
    _ ≤ latticeSpacing * (√(strainEnergy ε X p σ) + 140 * √(strainEnergy ε X p σ)) := by
        gcongr
    _ = _ := by ring

/-- `|err_{p,s}| ≤ ℓ (1 + A'_dir) √ε` (Lemma 5.5(e), at every vertex). -/
theorem norm_endpointErr_le_sqrt (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hj : IsOccupied ε X p σ j) :
    ‖endpointErr ε X p θ σ j‖ ≤ latticeSpacing * (1 + 6) * √ε := by
  have h1 := norm_endpointErr_le (θ := θ) hX hj
  have h2 := hX.strainMax_le_eps (p := p)
  have h3 := h.dirErrMax_le hX
  have h4 := hX.eps_le_sqrt
  have hℓ := latticeSpacing_pos
  have := Real.sqrt_nonneg ε
  calc _ ≤ latticeSpacing * (strainMax ε X p + dirErrMax ε X p θ σ) := h1
    _ ≤ latticeSpacing * (√ε + 6 * √ε) := by gcongr <;> linarith
    _ = _ := by ring

/-- `|err_{p,s}|² ≤ ℓ² (1 + A_dir)² e_p` at a full vertex. -/
theorem norm_endpointErr_sq_le_of_isFull (hX : IsRetainedSet ε X)
    (h : IsSlotAssignment ε X p θ σ) (hp : IsFull ε X p) (j : Fin 6) :
    ‖endpointErr ε X p θ σ j‖ ^ 2 ≤
      latticeSpacing ^ 2 * (1 + 140) ^ 2 * strainEnergy ε X p σ := by
  have h1 := h.norm_endpointErr_le_of_isFull hX hp j
  have he := Real.sq_sqrt (strainEnergy_nonneg (ε := ε) (X := X) (p := p) (σ := σ))
  calc _ ≤ (latticeSpacing * (1 + 140) * √(strainEnergy ε X p σ)) ^ 2 := by gcongr
    _ = _ := by rw [mul_pow, he, mul_pow]

/-- `|err_{p,s}|² ≤ ℓ² (1 + A'_dir)² ε`. -/
theorem norm_endpointErr_sq_le (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hj : IsOccupied ε X p σ j) :
    ‖endpointErr ε X p θ σ j‖ ^ 2 ≤ latticeSpacing ^ 2 * (1 + 6) ^ 2 * ε := by
  have h1 := h.norm_endpointErr_le_sqrt hX hj
  have he := Real.sq_sqrt hX.pos.le
  calc _ ≤ (latticeSpacing * (1 + 6) * √ε) ^ 2 := by gcongr
    _ = _ := by rw [mul_pow, he, mul_pow]

end IsSlotAssignment

/-- `Δ_pq² ≤ 2 (a_p² + a_q²)` from `|Δ_pq| ≤ a_p + a_q`. -/
theorem orientDiff_sq_le (hX : IsRetainedSet ε X) (hp : p ∈ X) (hq : q ∈ nbrs ε X p)
    (θ : Plane → ℝ) (σ : Plane → Plane → Fin 6) :
    orientDiff (θ p) (θ q) ^ 2 ≤
      2 * (dirErrMax ε X p (θ p) (σ p) ^ 2 + dirErrMax ε X q (θ q) (σ q) ^ 2) := by
  have h1 := abs_orientDiff_le hX hp hq θ σ
  have h0 := abs_nonneg (orientDiff (θ p) (θ q))
  have h2 : orientDiff (θ p) (θ q) ^ 2 ≤
      (dirErrMax ε X p (θ p) (σ p) + dirErrMax ε X q (θ q) (σ q)) ^ 2 := by
    rw [← sq_abs]
    gcongr
  nlinarith [sq_nonneg (dirErrMax ε X p (θ p) (σ p) - dirErrMax ε X q (θ q) (σ q))]

end TriangularLattice
