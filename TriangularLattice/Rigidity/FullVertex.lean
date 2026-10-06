/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Rigidity.Slots
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Full vertices

The second half of Lemma 5.3 (`lem:threeshell`) and parts (a), (c) of Lemma 5.5
(`lem:directional`).

Let `p` be a full retained vertex with an orientation and slot assignment `(θ, σ)` and let `q_j`
be the occupant of slot `j`. The signed offsets `δ_j = (dir (q_j - p) - (θ + jπ/3)).toReal`
satisfy `|δ_j| ≤ 4√ε` and `δ_0 = 0`, and the gap `∠ q_j p q_{j+1}` equals `π/3 + δ_{j+1} - δ_j`;
so the slot order is the counterclockwise order of the neighbors, consecutive neighbors are
nearest neighbors of each other, and the gap estimate (5.gap) applies. Telescoping gives the
bound `|δ_j| ≤ 140 √e_p` on the directional errors, where `e_p` is the strain energy (5.ep).

## Main definitions

* `TriangularLattice.slotOffset`: the signed offset `δ_j`.
* `TriangularLattice.strainEnergy` (`e_p`, (5.ep)).
* `TriangularLattice.strainEdges`: the twelve edges whose strains form `e_p`.
* `TriangularLattice.edgeStrain`: the strain `(|e|/ℓ - 1)²` of an edge.

## Main results

* `TriangularLattice.IsSlotAssignment.angle_occupant_succ`, `.occupant_succ_mem_nbrs`,
  `.abs_angle_occupant_succ_sub_le`, `.abs_angle_occupant_succ_sub_le_gap`: Lemma 5.3 for six
  neighbors.
* `TriangularLattice.IsSlotAssignment.slotError_le_of_isFull`,
  `TriangularLattice.IsSlotAssignment.dirErrMax_le_of_isFull`: Lemma 5.5(a), with
  `A_dir = 140`.
* `TriangularLattice.IsRetainedSet.encard_setOf_mem_strainEdges_le`: each nearest edge occurs in
  `e_p` for at most `m_e = 4` vertices `p` (the multiplicity behind Lemma 5.5(c)).
* `TriangularLattice.IsSlotAssignment.strainEnergy_eq_sum`: `e_p` is the sum of the strains of
  its twelve (distinct) edges.
-/

@[expose] public section

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace TriangularLattice

variable {ε : ℝ} {X : Set Plane} {p q q' u w : Plane} {θ : ℝ} {σ : Plane → Fin 6} {j : Fin 6}

/-- The signed offset `δ_j` from the direction of slot `j` to the direction of its occupant. -/
noncomputable def slotOffset (ε : ℝ) (X : Set Plane) (p : Plane) (θ : ℝ) (σ : Plane → Fin 6)
    (j : Fin 6) : ℝ :=
  (dir (occupant ε X p σ j - p) - (slotAngle θ j : Angle)).toReal

/-- The strain energy (5.ep) of a vertex,
`e_p = ∑_j (|q_j - p|/ℓ - 1)² + ∑_j (|q_{j+1} - q_j|/ℓ - 1)²`, `q_j` the occupant of slot `j`
(meaningful at full vertices). -/
noncomputable def strainEnergy (ε : ℝ) (X : Set Plane) (p : Plane) (σ : Plane → Fin 6) : ℝ :=
  ∑ j : Fin 6, (‖occupant ε X p σ j - p‖ / latticeSpacing - 1) ^ 2 +
    ∑ j : Fin 6, (‖occupant ε X p σ (j + 1) - occupant ε X p σ j‖ / latticeSpacing - 1) ^ 2

/-- The strain `(|a - b|/ℓ - 1)²` of the edge `{a, b}`. -/
noncomputable def edgeStrain (e : Sym2 Plane) : ℝ :=
  Sym2.lift ⟨fun a b => (‖a - b‖ / latticeSpacing - 1) ^ 2, fun a b => by
    dsimp only
    rw [norm_sub_rev]⟩ e

@[simp]
theorem edgeStrain_mk (a b : Plane) :
    edgeStrain s(a, b) = (‖a - b‖ / latticeSpacing - 1) ^ 2 :=
  rfl

open Classical in
/-- The twelve edges `{p, q_j}` and `{q_j, q_{j+1}}` whose strains form `e_p`. -/
noncomputable def strainEdges (ε : ℝ) (X : Set Plane) (p : Plane) (σ : Plane → Fin 6) :
    Finset (Sym2 Plane) :=
  Finset.univ.image (fun j : Fin 6 => s(p, occupant ε X p σ j)) ∪
    Finset.univ.image (fun j : Fin 6 => s(occupant ε X p σ j, occupant ε X p σ (j + 1)))

theorem strainEnergy_nonneg : 0 ≤ strainEnergy ε X p σ := by
  unfold strainEnergy
  positivity

theorem fin_succ_ne (j : Fin 6) : j + 1 ≠ j := by
  fin_cases j <;> decide

theorem dir_occupant (j : Fin 6) :
    dir (occupant ε X p σ j - p) = ((slotAngle θ j + slotOffset ε X p θ σ j : ℝ) : Angle) := by
  rw [Angle.coe_add, slotOffset, Angle.coe_toReal, add_sub_cancel]

theorem abs_slotOffset (hX : IsRetainedSet ε X) (hj : IsOccupied ε X p σ j) :
    |slotOffset ε X p θ σ j| = slotError p θ σ (occupant ε X p σ j) := by
  rw [slotOffset, ← Angle.norm_eq_abs_toReal, slotError, slot_occupant hj,
    angle_slotAngle_eq_norm hX (occupant_mem_nbrs hj)]

namespace IsSlotAssignment

theorem abs_slotOffset_le (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hj : IsOccupied ε X p σ j) : |slotOffset ε X p θ σ j| ≤ 4 * √ε := by
  rw [abs_slotOffset hX hj]
  exact h.slotError_le hX (occupant_mem_nbrs hj)

/-- Slot `0` is occupied by the anchor and has offset `0`. -/
theorem slotOffset_zero (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hne : (nbrs ε X p).Nonempty) :
    IsOccupied ε X p σ 0 ∧ slotOffset ε X p θ σ 0 = 0 := by
  obtain ⟨q₀, hq₀, hdir⟩ := h.exists_dir_eq hX hne
  have h0 : σ q₀ = 0 := h.slot_eq_zero hX hq₀ hdir
  have hocc : occupant ε X p σ 0 = q₀ := h0 ▸ h.occupant_slot hX hq₀
  refine ⟨h0 ▸ isOccupied_slot hq₀, ?_⟩
  rw [slotOffset, hocc, hdir, slotAngle_zero, sub_self, Angle.toReal_zero]

theorem occupant_succ_ne (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (j : Fin 6) : occupant ε X p σ j ≠ occupant ε X p σ (j + 1) := by
  intro he
  exact fin_succ_ne j (eq_of_occupant_eq (h.isOccupied_of_isFull hX hp _)
    (h.isOccupied_of_isFull hX hp _) he.symm)

/-- **Gaps at a full vertex.** The angle between consecutive occupants is
`π/3 + δ_{j+1} - δ_j`. -/
theorem angle_occupant_succ (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (j : Fin 6) :
    angle (occupant ε X p σ j - p) (occupant ε X p σ (j + 1) - p) =
      π / 3 + slotOffset ε X p θ σ (j + 1) - slotOffset ε X p θ σ j := by
  have h1 := h.abs_slotOffset_le hX (h.isOccupied_of_isFull hX hp j)
  have h2 := h.abs_slotOffset_le hX (h.isOccupied_of_isFull hX hp (j + 1))
  have hsq := hX.sqrt_le
  have hπ := Real.pi_gt_three
  rw [abs_le] at h1 h2
  rw [angle_eq_norm_dir_sub
      (hX.sub_ne_zero_of_mem_nbrs (occupant_mem_nbrs (h.isOccupied_of_isFull hX hp j)))
      (hX.sub_ne_zero_of_mem_nbrs (occupant_mem_nbrs (h.isOccupied_of_isFull hX hp (j + 1)))),
    dir_occupant, dir_occupant, ← Angle.coe_sub]
  have e : (((slotAngle θ j + slotOffset ε X p θ σ j) -
      (slotAngle θ (j + 1) + slotOffset ε X p θ σ (j + 1)) : ℝ) : Angle) =
      ((-(π / 3 + slotOffset ε X p θ σ (j + 1) - slotOffset ε X p θ σ j) : ℝ) : Angle) := by
    rw [Angle.coe_sub, Angle.coe_add, Angle.coe_add, coe_slotAngle_add_one, Angle.coe_neg,
      Angle.coe_sub, Angle.coe_add]
    abel
  rw [e, Angle.norm_coe_of_abs_le (by rw [abs_neg, abs_le]; constructor <;> linarith),
    abs_neg, abs_of_pos (by linarith)]

/-- The slot order is counterclockwise: the oriented angle from `q_j - p` to `q_{j+1} - p` is
the (positive) unoriented gap. -/
theorem toReal_dir_occupant_succ_sub (hX : IsRetainedSet ε X)
    (h : IsSlotAssignment ε X p θ σ) (hp : IsFull ε X p) (j : Fin 6) :
    (dir (occupant ε X p σ (j + 1) - p) - dir (occupant ε X p σ j - p)).toReal =
      angle (occupant ε X p σ j - p) (occupant ε X p σ (j + 1) - p) := by
  have h1 := h.abs_slotOffset_le hX (h.isOccupied_of_isFull hX hp j)
  have h2 := h.abs_slotOffset_le hX (h.isOccupied_of_isFull hX hp (j + 1))
  have hsq := hX.sqrt_le
  have hπ := Real.pi_gt_three
  rw [abs_le] at h1 h2
  have e : dir (occupant ε X p σ (j + 1) - p) - dir (occupant ε X p σ j - p) =
      ((π / 3 + slotOffset ε X p θ σ (j + 1) - slotOffset ε X p θ σ j : ℝ) : Angle) := by
    rw [dir_occupant, dir_occupant, Angle.coe_add, Angle.coe_add, coe_slotAngle_add_one,
      Angle.coe_sub, Angle.coe_add]
    abel
  rw [e, h.angle_occupant_succ hX hp, Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩]

/-- **Lemma 5.3 for six neighbors.** At a full vertex, consecutive occupants are nearest
neighbors of each other and the gap between them is within `8ε` of `π/3`. -/
theorem occupant_succ_mem_nbrs_and (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (j : Fin 6) :
    occupant ε X p σ (j + 1) ∈ nbrs ε X (occupant ε X p σ j) ∧
      |angle (occupant ε X p σ j - p) (occupant ε X p σ (j + 1) - p) - π / 3| ≤ 8 * ε := by
  have hj := h.isOccupied_of_isFull hX hp j
  have hj' := h.isOccupied_of_isFull hX hp (j + 1)
  have h1 := h.abs_slotOffset_le hX hj
  have h2 := h.abs_slotOffset_le hX hj'
  have hang := h.angle_occupant_succ hX hp j
  have hsq := hX.sqrt_le
  have hε := hX.le_small
  have hε0 := hX.pos
  have hπ := Real.pi_gt_three
  rw [abs_le] at h1 h2
  rcases hX.threeShell (occupant_mem_nbrs hj) (occupant_mem_nbrs hj')
      (h.occupant_succ_ne hX hp j) with ⟨hc, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩
  · refine ⟨⟨(occupant_mem_nbrs hj').1, ?_⟩, ha⟩
    rwa [norm_sub_rev] at hc
  · rw [hang, abs_le] at ha
    exfalso
    linarith
  · rw [hang] at ha
    exfalso
    linarith

theorem occupant_succ_mem_nbrs (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (j : Fin 6) :
    occupant ε X p σ (j + 1) ∈ nbrs ε X (occupant ε X p σ j) :=
  (h.occupant_succ_mem_nbrs_and hX hp j).1

/-- The gap bounds of Lemma 5.3: `∠ q_j p q_{j+1} ∈ [π/3 - 20ε, π/3 + 100ε]`. -/
theorem angle_occupant_succ_mem_Icc (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (j : Fin 6) :
    angle (occupant ε X p σ j - p) (occupant ε X p σ (j + 1) - p) ∈
      Set.Icc (π / 3 - 20 * ε) (π / 3 + 100 * ε) := by
  have := abs_le.1 (h.occupant_succ_mem_nbrs_and hX hp j).2
  have hε0 := hX.pos
  constructor <;> linarith

/-- **The gap estimate (5.gap) at a full vertex.** -/
theorem abs_angle_occupant_succ_sub_le (hX : IsRetainedSet ε X)
    (h : IsSlotAssignment ε X p θ σ) (hp : IsFull ε X p) (j : Fin 6) :
    |angle (occupant ε X p σ j - p) (occupant ε X p σ (j + 1) - p) - π / 3| ≤
      20 * (|‖occupant ε X p σ j - p‖ / latticeSpacing - 1| +
        |‖occupant ε X p σ (j + 1) - p‖ / latticeSpacing - 1| +
        |‖occupant ε X p σ (j + 1) - occupant ε X p σ j‖ / latticeSpacing - 1|) :=
  hX.abs_angle_sub_pi_div_three_le (occupant_mem_nbrs (h.isOccupied_of_isFull hX hp j))
    (occupant_mem_nbrs (h.isOccupied_of_isFull hX hp (j + 1)))
    (h.occupant_succ_mem_nbrs hX hp j).2

/-- Telescoping: `|δ_j| ≤ ∑_i |δ_{i+1} - δ_i|`. -/
theorem abs_slotOffset_le_sum (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (j : Fin 6) :
    |slotOffset ε X p θ σ j| ≤
      ∑ i : Fin 6, |slotOffset ε X p θ σ (i + 1) - slotOffset ε X p θ σ i| := by
  set F : ℕ → ℝ := fun n => slotOffset ε X p θ σ ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩ with hF
  have hne : (nbrs ε X p).Nonempty :=
    ⟨_, occupant_mem_nbrs (h.isOccupied_of_isFull hX hp 0)⟩
  have hF0 : F 0 = 0 := (h.slotOffset_zero hX hne).2
  have hFj : F j = slotOffset ε X p θ σ j := by
    simp only [hF]
    congr 1
    ext
    exact Nat.mod_eq_of_lt j.isLt
  have hFs : ∀ i : Fin 6, F (i + 1) = slotOffset ε X p θ σ (i + 1) := by
    intro i
    simp only [hF]
    congr 1
  have hFi : ∀ i : Fin 6, F i = slotOffset ε X p θ σ i := by
    intro i
    simp only [hF]
    congr 1
    ext
    exact Nat.mod_eq_of_lt i.isLt
  have htel : F j - F 0 = ∑ i ∈ Finset.range j, (F (i + 1) - F i) :=
    (Finset.sum_range_sub F j).symm
  calc |slotOffset ε X p θ σ j| = |∑ i ∈ Finset.range j, (F (i + 1) - F i)| := by
        rw [← htel, hF0, sub_zero, hFj]
    _ ≤ ∑ i ∈ Finset.range j, |F (i + 1) - F i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range 6, |F (i + 1) - F i| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 j.isLt.le)
          (fun _ _ _ => abs_nonneg _)
    _ = ∑ i : Fin 6, |slotOffset ε X p θ σ (i + 1) - slotOffset ε X p θ σ i| := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => |F (i + 1) - F i|)]
        exact Finset.sum_congr rfl fun i _ => by rw [hFs, hFi]

/-- **Lemma 5.5(a), signed form.** At a full vertex `|δ_j| ≤ 140 √e_p` and `|δ_j| ≤ 300 ε`. -/
theorem abs_slotOffset_le_of_isFull (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (j : Fin 6) :
    |slotOffset ε X p θ σ j| ≤ 140 * √(strainEnergy ε X p σ) ∧
      |slotOffset ε X p θ σ j| ≤ 300 * ε := by
  set A : Fin 6 → ℝ := fun i => |‖occupant ε X p σ i - p‖ / latticeSpacing - 1| with hA
  set C : Fin 6 → ℝ := fun i =>
    |‖occupant ε X p σ (i + 1) - occupant ε X p σ i‖ / latticeSpacing - 1| with hC
  have hsum := h.abs_slotOffset_le_sum hX hp j
  have hgap : ∀ i : Fin 6,
      |slotOffset ε X p θ σ (i + 1) - slotOffset ε X p θ σ i| ≤ 20 * (A i + A (i + 1) + C i) := by
    intro i
    have := h.abs_angle_occupant_succ_sub_le hX hp i
    rw [h.angle_occupant_succ hX hp i] at this
    convert this using 2
    ring
  have hgap' : ∀ i : Fin 6,
      |slotOffset ε X p θ σ (i + 1) - slotOffset ε X p θ σ i| ≤ 8 * ε := by
    intro i
    have := (h.occupant_succ_mem_nbrs_and hX hp i).2
    rw [h.angle_occupant_succ hX hp i] at this
    convert this using 2
    ring
  constructor
  · have hshift : ∑ i : Fin 6, A (i + 1) = ∑ i : Fin 6, A i :=
      Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
    have hA0 : ∀ i, 0 ≤ A i := fun _ => abs_nonneg _
    have hC0 : ∀ i, 0 ≤ C i := fun _ => abs_nonneg _
    have hSA : (∑ i : Fin 6, A i) ^ 2 ≤ 6 * ∑ i : Fin 6,
        (‖occupant ε X p σ i - p‖ / latticeSpacing - 1) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := A)
      simpa [hA, sq_abs] using this
    have hSC : (∑ i : Fin 6, C i) ^ 2 ≤ 6 * ∑ i : Fin 6,
        (‖occupant ε X p σ (i + 1) - occupant ε X p σ i‖ / latticeSpacing - 1) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := C)
      simpa [hC, sq_abs] using this
    have hpos1 : 0 ≤ ∑ i : Fin 6, A i := Finset.sum_nonneg fun i _ => hA0 i
    have hpos2 : 0 ≤ ∑ i : Fin 6, C i := Finset.sum_nonneg fun i _ => hC0 i
    have hCS : ∑ i : Fin 6, A i + ∑ i : Fin 6, C i ≤ √12 * √(strainEnergy ε X p σ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      have hsq2 : (∑ i : Fin 6, A i + ∑ i : Fin 6, C i) ^ 2 ≤
          2 * ((∑ i : Fin 6, A i) ^ 2 + (∑ i : Fin 6, C i) ^ 2) := by
        nlinarith [sq_nonneg (∑ i : Fin 6, A i - ∑ i : Fin 6, C i)]
      have := Real.abs_le_sqrt (x := ∑ i : Fin 6, A i + ∑ i : Fin 6, C i)
        (y := 12 * strainEnergy ε X p σ) (by unfold strainEnergy; linarith)
      rwa [abs_of_nonneg (by positivity)] at this
    have h12 : √12 ≤ 3.5 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hsqrt := Real.sqrt_nonneg (strainEnergy ε X p σ)
    calc |slotOffset ε X p θ σ j|
        ≤ ∑ i : Fin 6, |slotOffset ε X p θ σ (i + 1) - slotOffset ε X p θ σ i| := hsum
      _ ≤ ∑ i : Fin 6, 20 * (A i + A (i + 1) + C i) := Finset.sum_le_sum fun i _ => hgap i
      _ = 20 * (2 * ∑ i : Fin 6, A i + ∑ i : Fin 6, C i) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, hshift]
          ring
      _ ≤ 40 * (√12 * √(strainEnergy ε X p σ)) := by nlinarith
      _ ≤ 140 * √(strainEnergy ε X p σ) := by nlinarith
  · calc |slotOffset ε X p θ σ j|
        ≤ ∑ i : Fin 6, |slotOffset ε X p θ σ (i + 1) - slotOffset ε X p θ σ i| := hsum
      _ ≤ ∑ _i : Fin 6, 8 * ε := Finset.sum_le_sum fun i _ => hgap' i
      _ ≤ 300 * ε := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have := hX.pos
          push_cast
          linarith

/-- **Lemma 5.5(a).** At a full vertex every directional error is at most `140 √e_p` and at most
`300 ε`. -/
theorem slotError_le_of_isFull (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (hq : q ∈ nbrs ε X p) :
    slotError p θ σ q ≤ 140 * √(strainEnergy ε X p σ) ∧ slotError p θ σ q ≤ 300 * ε := by
  have := h.abs_slotOffset_le_of_isFull hX hp (σ q)
  rwa [abs_slotOffset hX (isOccupied_slot hq), h.occupant_slot hX hq] at this

theorem dirErrMax_le_of_isFull (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) :
    dirErrMax ε X p θ σ ≤ 140 * √(strainEnergy ε X p σ) ∧ dirErrMax ε X p θ σ ≤ 300 * ε :=
  ⟨TriangularLattice.dirErrMax_le (by positivity)
      fun _ hq => (h.slotError_le_of_isFull hX hp hq).1,
    TriangularLattice.dirErrMax_le (by linarith [hX.pos])
      fun _ hq => (h.slotError_le_of_isFull hX hp hq).2⟩

/-- `s_p ≤ √e_p` (meaningful at full vertices). -/
theorem strainMax_le_sqrt_strainEnergy (hX : IsRetainedSet ε X)
    (h : IsSlotAssignment ε X p θ σ) :
    strainMax ε X p ≤ √(strainEnergy ε X p σ) := by
  refine strainMax_le (Real.sqrt_nonneg _) fun q hq => Real.abs_le_sqrt ?_
  rw [← h.occupant_slot hX hq]
  unfold strainEnergy
  have h1 := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 6 => (‖occupant ε X p σ j - p‖ / latticeSpacing - 1) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ (σ q))
  have h2 : 0 ≤ ∑ j : Fin 6,
      (‖occupant ε X p σ (j + 1) - occupant ε X p σ j‖ / latticeSpacing - 1) ^ 2 := by
    positivity
  linarith

/-- The strain energy is the sum of the strains of the twelve distinct edges of `strainEdges`. -/
theorem strainEnergy_eq_sum (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) :
    strainEnergy ε X p σ = ∑ e ∈ strainEdges ε X p σ, edgeStrain e := by
  classical
  have hocc := h.isOccupied_of_isFull hX hp
  have hinj : ∀ i j : Fin 6, occupant ε X p σ i = occupant ε X p σ j → i = j :=
    fun i j hij => eq_of_occupant_eq (hocc i) (hocc j) hij
  have hne : ∀ j : Fin 6, occupant ε X p σ j ≠ p :=
    fun j => hX.ne_of_mem_nbrs (occupant_mem_nbrs (hocc j))
  have hdisj : Disjoint (Finset.univ.image (fun j : Fin 6 => s(p, occupant ε X p σ j)))
      (Finset.univ.image (fun j : Fin 6 => s(occupant ε X p σ j, occupant ε X p σ (j + 1)))) := by
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at he he'
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, hj⟩ := he'
    rw [Sym2.eq_iff] at hj
    rcases hj with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hne j h1
    · exact hne (j + 1) h2
  have hinj1 : Set.InjOn (fun j : Fin 6 => s(p, occupant ε X p σ j))
      (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)) := by
    intro i _ j _ hij
    exact hinj i j (Sym2.congr_right.1 hij)
  have hinj2 : Set.InjOn (fun j : Fin 6 => s(occupant ε X p σ j, occupant ε X p σ (j + 1)))
      (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)) := by
    intro i _ j _ hij
    simp only [Sym2.eq_iff] at hij
    rcases hij with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hinj i j h1
    · have e1 := hinj _ _ h1
      have e2 := hinj _ _ h2
      subst e1
      revert e2
      fin_cases j <;> decide
  unfold strainEdges strainEnergy
  convert (Finset.sum_union hdisj).symm using 1
  rw [Finset.sum_image hinj1, Finset.sum_image hinj2]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [edgeStrain_mk, norm_sub_rev]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [edgeStrain_mk, norm_sub_rev]

end IsSlotAssignment

/-! ### Multiplicity of the edges in `e_p` -/

/-- If `q, q'` are nearest neighbors of `p` and of each other, the angle `∠ q p q'` is within
`8ε` of `π/3`. -/
theorem IsRetainedSet.abs_angle_sub_pi_div_three_le_of_mem_nbrs (hX : IsRetainedSet ε X)
    (hq : q ∈ nbrs ε X p) (hq' : q' ∈ nbrs ε X p) (hqq' : q' ∈ nbrs ε X q) :
    |angle (q - p) (q' - p) - π / 3| ≤ 8 * ε := by
  have hc : |‖q - q'‖ / latticeSpacing - 1| ≤ ε := by
    rw [norm_sub_rev]
    exact hqq'.2
  have hε := hX.le_small
  have h3 := lt_sqrt_three
  rcases hX.threeShell hq hq' (hX.ne_of_mem_nbrs hqq').symm with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · rw [abs_le] at h hc
    exfalso
    linarith
  · rw [abs_le] at h hc
    exfalso
    linarith

/-- **Common neighbors.** Two nearest neighbors `u, w` have at most two common nearest
neighbors. -/
theorem IsRetainedSet.encard_commonNbrs_le_two (hX : IsRetainedSet ε X)
    (hw : w ∈ nbrs ε X u) :
    {p | p ∈ X ∧ u ∈ nbrs ε X p ∧ w ∈ nbrs ε X p}.encard ≤ 2 := by
  set S := {p | p ∈ X ∧ u ∈ nbrs ε X p ∧ w ∈ nbrs ε X p}
  set ψ : Plane → ℝ := fun p => (dir (p - u) - dir (w - u)).toReal with hψ
  have key : ∀ p ∈ S, p ∈ nbrs ε X u ∧ |(|ψ p| - π / 3)| ≤ 8 * ε := by
    rintro p ⟨hpX, hup, hwp⟩
    have hpu : p ∈ nbrs ε X u := mem_nbrs_comm hpX hup
    refine ⟨hpu, ?_⟩
    have := hX.abs_angle_sub_pi_div_three_le_of_mem_nbrs hpu hw hwp
    rwa [angle_eq_norm_dir_sub (hX.sub_ne_zero_of_mem_nbrs hpu) (hX.sub_ne_zero_of_mem_nbrs hw),
      Angle.norm_eq_abs_toReal] at this
  have hinj : Set.InjOn (fun p => decide (0 < ψ p)) S := by
    intro p hp p' hp' hpp'
    by_contra hne
    obtain ⟨hpu, h1⟩ := key p hp
    obtain ⟨hp'u, h2⟩ := key p' hp'
    have hsign : (0 < ψ p ↔ 0 < ψ p') := by simpa using hpp'
    have hdiff : |ψ p - ψ p'| ≤ 16 * ε := by
      rw [abs_le] at h1 h2 ⊢
      rcases lt_or_ge 0 (ψ p) with hpos | hnpos
      · have hpos' := hsign.1 hpos
        rw [abs_of_pos hpos] at h1
        rw [abs_of_pos hpos'] at h2
        constructor <;> linarith
      · have hnpos' : ψ p' ≤ 0 := not_lt.1 fun h => hnpos.not_gt (hsign.2 h)
        rw [abs_of_nonpos hnpos] at h1
        rw [abs_of_nonpos hnpos'] at h2
        constructor <;> linarith
    have hnorm : ‖dir (p - u) - dir (p' - u)‖ ≤ 16 * ε := by
      have e : dir (p - u) - dir (p' - u) = ((ψ p - ψ p' : ℝ) : Angle) := by
        simp only [hψ, Angle.coe_sub, Angle.coe_toReal]
        abel
      rw [e]
      exact (Angle.norm_coe_le_abs _).trans hdiff
    have := hX.pi_div_three_sub_le_angle hpu hp'u hne
    rw [angle_eq_norm_dir_sub (hX.sub_ne_zero_of_mem_nbrs hpu)
      (hX.sub_ne_zero_of_mem_nbrs hp'u)] at this
    have hε := hX.le_small
    have hπ := Real.pi_gt_three
    linarith
  calc S.encard ≤ (Set.univ : Set Bool).encard :=
        Set.encard_le_encard_of_injOn (fun _ _ => Set.mem_univ _) hinj
    _ = 2 := by rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool]; rfl

/-- **Multiplicity behind Lemma 5.5(c).** A nearest edge `{u, w}` occurs among the edges of
`e_p` for at most `m_e = 4` vertices `p`, for any slot assignments `σ p`. -/
theorem IsRetainedSet.encard_setOf_mem_strainEdges_le (hX : IsRetainedSet ε X)
    (σ : Plane → Plane → Fin 6) (hw : w ∈ nbrs ε X u) :
    {p | p ∈ X ∧ s(u, w) ∈ strainEdges ε X p (σ p)}.encard ≤ 4 := by
  classical
  set S := {p | p ∈ X ∧ u ∈ nbrs ε X p ∧ w ∈ nbrs ε X p}
  have hsub : {p | p ∈ X ∧ s(u, w) ∈ strainEdges ε X p (σ p)} ⊆ {u, w} ∪ S := by
    rintro p ⟨hpX, hmem⟩
    simp only [strainEdges, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      at hmem
    rcases hmem with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      rw [Sym2.eq_iff] at hj
      rcases hj with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    · rw [Sym2.eq_iff] at hj
      have ha := occupant_mem_nbrs_or_eq (ε := ε) (X := X) (p := p) (σ := σ p) j
      have hb := occupant_mem_nbrs_or_eq (ε := ε) (X := X) (p := p) (σ := σ p) (j + 1)
      have : (u ∈ nbrs ε X p ∨ u = p) ∧ (w ∈ nbrs ε X p ∨ w = p) := by
        rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1] at ha
          rw [h2] at hb
          exact ⟨ha, hb⟩
        · rw [h1] at ha
          rw [h2] at hb
          exact ⟨hb, ha⟩
      rcases this with ⟨hu' | rfl, hw' | rfl⟩
      · exact Or.inr ⟨hpX, hu', hw'⟩
      · simp
      · simp
      · simp
  have hpair : ({u, w} : Set Plane).encard ≤ 2 := by
    refine (Set.encard_insert_le _ _).trans ?_
    rw [Set.encard_singleton]
    rfl
  calc _ ≤ ({u, w} ∪ S).encard := Set.encard_le_encard hsub
    _ ≤ ({u, w} : Set Plane).encard + S.encard := Set.encard_union_le _ _
    _ ≤ 2 + 2 := add_le_add hpair (hX.encard_commonNbrs_le_two hw)
    _ = 4 := rfl

end TriangularLattice
