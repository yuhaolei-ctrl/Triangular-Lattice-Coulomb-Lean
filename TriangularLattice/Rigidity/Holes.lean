/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Rigidity.Cells

/-!
# Deficient vertices produce holes

Lemma 5.7 (`lem:holes`) of the manuscript. For a retained point `p`, an unoccupied slot `j`
(such a slot exists exactly when `p` is deficient), `v = e_{θ_p + jπ/3}` and `z = p + ℓ v`, the
disc `B(z, h)` with `h = (1/√3 - 1/2) ℓ > 1/16` meets no cell. Every point of the plane lies in at
most `m_hole = 96` such discs.

## Deviations from the manuscript

* The multiplicity bound is `m_hole = 96 = 16 · 6` instead of `60 = 10 · 6`: the number of
  retained points within distance `ℓ + h < 7/5` of a point is bounded by `16` by a pigeonhole
  argument on a grid of squares of side `7/10` (`encard_inter_ball_le_sixteen`), instead of the
  area argument giving `10`. Only the existence of a universal constant matters downstream
  (it enters `c_hole`).
* The proof that `B(z, h)` misses `cell(p)` uses that `v` is a face normal of `H_{θ_p}`, and the
  proof for a neighbor `q` uses the endpoint error of `q`, instead of the angle computations of
  the manuscript.

## Main definitions

* `TriangularLattice.holeRadius` (`h`), `TriangularLattice.holeCenter p θ j` (`z`).

## Main results

* `TriangularLattice.one_div_sixteen_lt_holeRadius`: `h > 1/16`.
* `TriangularLattice.IsOrientation.disjoint_ball_holeCenter_cell`: holes miss all cells.
* `TriangularLattice.IsRetainedSet.encard_holes_le`: the multiplicity bound.
* `TriangularLattice.IsSlotAssignment.exists_not_isOccupied`: a deficient vertex has an
  unoccupied slot (proved in `TriangularLattice.Rigidity.Slots`).
-/

@[expose] public section

open Real InnerProductGeometry Metric
open scoped RealInnerProductSpace

namespace TriangularLattice

variable {ε : ℝ} {X : Set Plane} {p q y : Plane} {θ : ℝ} {σ : Plane → Fin 6} {j : Fin 6}

/-- The hole radius `h = (1/√3 - 1/2) ℓ` of (5.h). -/
noncomputable def holeRadius : ℝ :=
  (1 / √3 - 1 / 2) * latticeSpacing

/-- The hole center `z = p + ℓ e_{θ + jπ/3}` of the slot `j` at `p`. -/
noncomputable def holeCenter (p : Plane) (θ : ℝ) (j : Fin 6) : Plane :=
  p + latticeSpacing • unitVec (slotAngle θ j)

theorem one_div_sqrt_three_lt : 1 / √3 < 0.5774 := by
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [lt_sqrt_three]

theorem lt_one_div_sqrt_three : 0.5773 < 1 / √3 := by
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [sqrt_three_lt]

/-- `h > 1/16`. -/
theorem one_div_sixteen_lt_holeRadius : 1 / 16 < holeRadius := by
  unfold holeRadius
  nlinarith [lt_one_div_sqrt_three, lt_latticeSpacing]

theorem holeRadius_pos : 0 < holeRadius :=
  lt_trans (by norm_num) one_div_sixteen_lt_holeRadius

/-- The inner product of distinct slot vectors is at most `1/2`. -/
theorem inner_unitVec_slotAngle_le (θ : ℝ) {i j : Fin 6} (hij : i ≠ j) :
    ⟪unitVec (slotAngle θ i), unitVec (slotAngle θ j)⟫ ≤ 1 / 2 := by
  rw [inner_unitVec_unitVec, show slotAngle θ i - slotAngle θ j =
    (i : ℕ) * (π / 3) - (j : ℕ) * (π / 3) by simp only [slotAngle]; ring, Real.cos_sub,
    cos_slotOffset, cos_slotOffset, sin_slotOffset, sin_slotOffset]
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;> simp [slotCos, slotSin] at hij ⊢ <;> nlinarith

/-- Distinct slot vectors are at distance at least `1`. -/
theorem one_le_norm_unitVec_slotAngle_sub (θ : ℝ) {i j : Fin 6} (hij : i ≠ j) :
    1 ≤ ‖unitVec (slotAngle θ i) - unitVec (slotAngle θ j)‖ := by
  have h := inner_unitVec_slotAngle_le θ hij
  have hsq : ‖unitVec (slotAngle θ i) - unitVec (slotAngle θ j)‖ ^ 2 =
      2 - 2 * ⟪unitVec (slotAngle θ i), unitVec (slotAngle θ j)⟫ := by
    rw [norm_sub_sq_real, norm_unitVec, norm_unitVec]
    ring
  nlinarith [norm_nonneg (unitVec (slotAngle θ i) - unitVec (slotAngle θ j))]

/-- **Lemma 5.7, holes.** For a retained point `p` and an unoccupied slot `j` at `p`, the disc
`B(z, h)` around `z = p + ℓ e_{θ_p + jπ/3}` is disjoint from every cell. -/
theorem IsOrientation.disjoint_ball_holeCenter_cell {θ : Plane → ℝ} {σ : Plane → Plane → Fin 6}
    (hX : IsRetainedSet ε X) (h : IsOrientation ε X θ σ) (hp : p ∈ X)
    (hj : ¬IsOccupied ε X p (σ p) j) (hq : q ∈ X) :
    Disjoint (ball (holeCenter p (θ p) j) holeRadius) (cell ε X q (θ q) (σ q)) := by
  rw [Set.disjoint_left]
  intro x hxz hxq
  rw [mem_ball] at hxz
  set z := holeCenter p (θ p) j
  have hℓ := latticeSpacing_pos
  have hℓ' := lt_latticeSpacing
  have hε := hX.le_small
  have hε0 := hX.pos
  have hsq := hX.sqrt_le
  have ht := one_div_sqrt_three_lt
  have ht' := lt_one_div_sqrt_three
  have hc : ‖x - q‖ < 1 / √3 * latticeSpacing := by
    have := (h q hq).norm_sub_lt_of_mem_cell hX hxq
    rwa [div_eq_mul_one_div, mul_comm] at this
  have hxz' : ‖x - z‖ < (1 / √3 - 1 / 2) * latticeSpacing := by
    rw [← dist_eq_norm]
    exact hxz
  have htri : ‖q - z‖ ≤ ‖x - q‖ + ‖x - z‖ := by
    rw [show q - z = (x - z) - (x - q) by abel, add_comm]
    exact norm_sub_le _ _
  by_cases hqp : q = p
  · -- the cell of `p` itself: `e_{θ_p + jπ/3}` is a face normal
    subst hqp
    have h1 := ((h q hp).mem_cell_iff hX).1 hxq j
    have hk := kappa_nonneg (ε := ε) (X := X) (p := q) (θ := θ q) (σ := σ q)
    have h2 : ⟪x - q, unitVec (slotAngle (θ q) j)⟫ =
        latticeSpacing + ⟪x - z, unitVec (slotAngle (θ q) j)⟫ := by
      rw [show x - q = (x - z) + latticeSpacing • unitVec (slotAngle (θ q) j) by
          simp only [z, holeCenter]; abel,
        inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, norm_unitVec, conj_trivial,
        one_pow, mul_one, add_comm]
    have h3 : -‖x - z‖ ≤ ⟪x - z, unitVec (slotAngle (θ q) j)⟫ := by
      have := abs_real_inner_le_norm (x - z) (unitVec (slotAngle (θ q) j))
      rw [norm_unitVec, mul_one] at this
      linarith [neg_abs_le ⟪x - z, unitVec (slotAngle (θ q) j)⟫]
    nlinarith
  by_cases hnb : q ∈ nbrs ε X p
  · -- a nearest neighbor of `p` occupies another slot `j'`
    set j' := σ p q
    have hj' : j' ≠ j := fun he => hj ⟨q, hnb, he⟩
    have hocc : IsOccupied ε X p (σ p) j' := isOccupied_slot hnb
    have herr := (h p hp).norm_endpointErr_le_sqrt hX hocc
    have hoq : occupant ε X p (σ p) j' = q := (h p hp).occupant_slot hX hnb
    have hchord := one_le_norm_unitVec_slotAngle_sub (θ p) hj'
    have hdecomp : q - z = endpointErr ε X p (θ p) (σ p) j' +
        latticeSpacing • (unitVec (slotAngle (θ p) j') - unitVec (slotAngle (θ p) j)) := by
      simp only [endpointErr, hoq, z, holeCenter, smul_sub]
      abel
    have hlow : latticeSpacing - latticeSpacing * (1 + 6) * √ε ≤ ‖q - z‖ := by
      rw [hdecomp]
      have := norm_sub_norm_le
        (latticeSpacing • (unitVec (slotAngle (θ p) j') - unitVec (slotAngle (θ p) j)))
        (-endpointErr ε X p (θ p) (σ p) j')
      rw [sub_neg_eq_add, norm_neg, norm_smul, Real.norm_of_nonneg hℓ.le, add_comm] at this
      nlinarith
    nlinarith
  · -- any other retained point is far from `p`
    have hfar := hX.le_norm_sub_of_not_mem_nbrs hp hq hqp hnb
    have hzp : ‖z - p‖ = latticeSpacing := by
      simp only [z, holeCenter, add_sub_cancel_left, norm_smul, norm_unitVec, mul_one,
        Real.norm_of_nonneg hℓ.le]
    have htri' : ‖q - p‖ ≤ ‖q - z‖ + ‖z - p‖ := by
      rw [show q - p = (q - z) + (z - p) by abel]
      exact norm_add_le _ _
    have ha : 1.732 * latticeSpacing ≤ √3 * latticeSpacing :=
      mul_le_mul_of_nonneg_right lt_sqrt_three.le hℓ.le
    have hb : 1 / √3 * latticeSpacing ≤ 0.5774 * latticeSpacing :=
      mul_le_mul_of_nonneg_right ht.le hℓ.le
    have hc' : ε * latticeSpacing ≤ 1 / 10 ^ 8 * 2 := by
      nlinarith [latticeSpacing_lt]
    rw [sub_mul] at hfar
    rw [sub_mul] at hxz'
    linarith

/-- **Packing.** A set of points with mutual distances greater than `1` has at most `16` points
in an open disc of radius `7/5`. -/
theorem encard_inter_ball_le_sixteen {S : Set Plane}
    (hS : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → 1 < ‖x - x'‖) (c : Plane) :
    (S ∩ ball c (7 / 5)).encard ≤ 16 := by
  classical
  let g : Plane → ℤ × ℤ := fun x => (⌊(x 0 - c 0) / (7 / 10)⌋, ⌊(x 1 - c 1) / (7 / 10)⌋)
  have hcoord : ∀ x : Plane, |x 0| ≤ ‖x‖ ∧ |x 1| ≤ ‖x‖ := by
    intro x
    have h := norm_sq_eq_coord x
    exact ⟨abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (x 1)]) (norm_nonneg _),
      abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (x 0)]) (norm_nonneg _)⟩
  have hmaps : Set.MapsTo g (S ∩ ball c (7 / 5))
      (↑(Finset.Icc (-2 : ℤ) 1 ×ˢ Finset.Icc (-2 : ℤ) 1) : Set (ℤ × ℤ)) := by
    rintro x ⟨-, hx⟩
    rw [mem_ball, dist_eq_norm] at hx
    have h0 := (hcoord (x - c)).1
    have h1 := (hcoord (x - c)).2
    simp only [PiLp.sub_apply] at h0 h1
    rw [abs_le] at h0 h1
    simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc, g]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [Int.le_floor]; push_cast; rw [le_div_iff₀ (by norm_num)]; linarith
    · rw [Int.floor_le_iff]; push_cast; rw [div_lt_iff₀ (by norm_num)]; linarith
    · rw [Int.le_floor]; push_cast; rw [le_div_iff₀ (by norm_num)]; linarith
    · rw [Int.floor_le_iff]; push_cast; rw [div_lt_iff₀ (by norm_num)]; linarith
  have hinj : Set.InjOn g (S ∩ ball c (7 / 5)) := by
    rintro x ⟨hxS, -⟩ x' ⟨hx'S, -⟩ hgx
    by_contra hne
    have h1 := hS x hxS x' hx'S hne
    simp only [g, Prod.mk.injEq] at hgx
    have e0 := Int.abs_sub_lt_one_of_floor_eq_floor hgx.1
    have e1 := Int.abs_sub_lt_one_of_floor_eq_floor hgx.2
    rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 10),
      div_lt_one (by norm_num)] at e0 e1
    have hsq := norm_sq_eq_coord (x - x')
    simp only [PiLp.sub_apply] at hsq
    rw [show x 0 - c 0 - (x' 0 - c 0) = x 0 - x' 0 by ring] at e0
    rw [show x 1 - c 1 - (x' 1 - c 1) = x 1 - x' 1 by ring] at e1
    have : ‖x - x'‖ ^ 2 < 1 := by
      rw [hsq]
      nlinarith [abs_nonneg (x 0 - x' 0), abs_nonneg (x 1 - x' 1), sq_abs (x 0 - x' 0),
        sq_abs (x 1 - x' 1)]
    nlinarith [norm_nonneg (x - x')]
  calc (S ∩ ball c (7 / 5)).encard
      ≤ (↑(Finset.Icc (-2 : ℤ) 1 ×ˢ Finset.Icc (-2 : ℤ) 1) : Set (ℤ × ℤ)).encard :=
        Set.encard_le_encard_of_injOn hmaps hinj
    _ = 16 := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_product, Int.card_Icc]
        rfl

/-- **Lemma 5.7, multiplicity.** Every point of the plane lies in at most `m_hole = 96` of the
discs `B(z, h)`, over all retained points `p` and all unoccupied slots `j` at `p`. -/
theorem IsRetainedSet.encard_holes_le (hX : IsRetainedSet ε X) (θ : Plane → ℝ)
    (σ : Plane → Plane → Fin 6) (y : Plane) :
    {pj : Plane × Fin 6 | pj.1 ∈ X ∧ ¬IsOccupied ε X pj.1 (σ pj.1) pj.2 ∧
      y ∈ ball (holeCenter pj.1 (θ pj.1) pj.2) holeRadius}.encard ≤ 96 := by
  classical
  set T := {pj : Plane × Fin 6 | pj.1 ∈ X ∧ ¬IsOccupied ε X pj.1 (σ pj.1) pj.2 ∧
      y ∈ ball (holeCenter pj.1 (θ pj.1) pj.2) holeRadius}
  set S := X ∩ ball y (7 / 5)
  have hsep : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → 1 < ‖x - x'‖ :=
    fun x hx x' hx' hne => hX.one_lt_norm_sub hx hx' hne
  obtain ⟨F, hF, hFcard⟩ : ∃ F : Finset Plane, (↑F : Set Plane) = S ∧ F.card ≤ 16 := by
    have hfin : S.Finite := Set.finite_of_encard_le_coe
      (encard_inter_ball_le_sixteen hsep y)
    refine ⟨hfin.toFinset, hfin.coe_toFinset, ?_⟩
    have := encard_inter_ball_le_sixteen hsep y
    change S.encard ≤ 16 at this
    rw [← hfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at this
    exact_mod_cast this
  have hsub : T ⊆ ↑(F ×ˢ (Finset.univ : Finset (Fin 6))) := by
    rintro ⟨p, j⟩ ⟨hpX, -, hy⟩
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, and_true, hF]
    refine ⟨hpX, ?_⟩
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have hzp : ‖holeCenter p (θ p) j - p‖ = latticeSpacing := by
      simp only [holeCenter, add_sub_cancel_left, norm_smul, norm_unitVec, mul_one,
        Real.norm_of_nonneg latticeSpacing_pos.le]
    have htri : ‖p - y‖ ≤ ‖y - holeCenter p (θ p) j‖ + ‖holeCenter p (θ p) j - p‖ := by
      rw [norm_sub_rev p y, show y - p = (y - holeCenter p (θ p) j) +
        (holeCenter p (θ p) j - p) by abel]
      exact norm_add_le _ _
    have ht := one_div_sqrt_three_lt
    have hℓ := latticeSpacing_lt
    unfold holeRadius at hy
    nlinarith [latticeSpacing_pos]
  calc T.encard ≤ (↑(F ×ˢ (Finset.univ : Finset (Fin 6))) : Set (Plane × Fin 6)).encard :=
        Set.encard_le_encard hsub
    _ = (F.card * 6 : ℕ) := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_product, Finset.card_univ,
          Fintype.card_fin]
    _ ≤ 96 := by
        have : F.card * 6 ≤ 96 := by omega
        exact_mod_cast this

end TriangularLattice
