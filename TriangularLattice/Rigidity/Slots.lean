/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Rigidity.ThreeShell

/-!
# Orientations and slots

Definition 5.4 (`def:slots`) of the manuscript and the parts of Lemma 5.5 (`lem:directional`)
that hold at every vertex.

An orientation and slot assignment at a retained point `p` is a pair `(θ, σ)` of a real number
`θ` and a map `σ : Plane → Fin 6` (only its values on the nearest neighbors matter) such that

* `θ` is the direction of `q₀ - p` for some nearest neighbor `q₀` (if `p` has one), and
* every nearest neighbor `q` is assigned a slot `σ q` whose direction `θ + (σ q) π/3` is closest
  to that of `q - p`.

This is `IsSlotAssignment`; a family of such choices for all `p ∈ X` is an `IsOrientation`. Both
exist (`exists_isSlotAssignment`, `exists_isOrientation`) and are compatible with translations
preserving `X` (`IsSlotAssignment.add_vec`), so that choices can be made once per orbit. All
estimates are proved for every valid choice.

For full vertices the manuscript lists the six neighbors counterclockwise starting from `q₀`; here
the slot order is the counterclockwise order (`TriangularLattice.FullVertex`), so the two
definitions agree.

## Main definitions

* `TriangularLattice.slotError p θ σ q`: the directional error `∠(q - p, e_{θ + σ(q) π/3})`.
* `TriangularLattice.IsSlotAssignment`, `TriangularLattice.IsOrientation`.
* `TriangularLattice.IsFull`: `p` has six nearest neighbors; `TriangularLattice.IsOccupied`,
  `TriangularLattice.occupant`: occupancy of slots.
* `TriangularLattice.dirErrMax` (`a_p`), `TriangularLattice.strainMax` (`s_p`).
* `TriangularLattice.orientDiff θ θ'` (`Δ_pq`): the representative of `θ - θ'` modulo `π/3` of
  least absolute value.
* `TriangularLattice.endpointErr` (`err_{p,s}`).

## Main results

* `TriangularLattice.IsSlotAssignment.slotError_le`: every directional error is at most `4√ε`
  (in particular at most `A'_dir √ε = 6√ε`, Lemma 5.5(b)).
* `TriangularLattice.IsSlotAssignment.injOn`: distinct neighbors receive distinct slots.
* `TriangularLattice.IsRetainedSet.encard_nbrs_le_six`: at most six nearest neighbors (Lemma 5.3).
* `TriangularLattice.abs_orientDiff_le`: `|Δ_pq| ≤ a_p + a_q` (Lemma 5.5(d)).
* `TriangularLattice.norm_endpointErr_le`: `|err_{p,s}| ≤ ℓ (s_p + a_p)`, the
  estimate behind Lemma 5.5(e).
-/

@[expose] public section

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace TriangularLattice

variable {ε : ℝ} {X : Set Plane} {p q q' v : Plane} {θ : ℝ} {σ : Plane → Fin 6} {j : Fin 6}

/-! ### Definitions -/

/-- The directional error of the neighbor `q` of `p`: the angle between `q - p` and the direction
`e_{θ + σ(q) π/3}` of its slot. -/
noncomputable def slotError (p : Plane) (θ : ℝ) (σ : Plane → Fin 6) (q : Plane) : ℝ :=
  angle (q - p) (unitVec (slotAngle θ (σ q)))

/-- **Orientation and slot assignment at a vertex** (Definition 5.4). The orientation `θ` is the
direction of `q₀ - p` for a nearest neighbor `q₀` (if there is one), and every nearest neighbor
`q` is assigned to a slot `σ q` whose direction is closest to that of `q - p`. -/
structure IsSlotAssignment (ε : ℝ) (X : Set Plane) (p : Plane) (θ : ℝ) (σ : Plane → Fin 6) :
    Prop where
  anchor : (nbrs ε X p).Nonempty → ∃ q₀ ∈ nbrs ε X p, q₀ - p = ‖q₀ - p‖ • unitVec θ
  closest : ∀ q ∈ nbrs ε X p, ∀ j : Fin 6,
    angle (q - p) (unitVec (slotAngle θ (σ q))) ≤ angle (q - p) (unitVec (slotAngle θ j))

/-- An orientation of `X`: an orientation and slot assignment `(θ p, σ p)` at every `p ∈ X`. -/
def IsOrientation (ε : ℝ) (X : Set Plane) (θ : Plane → ℝ) (σ : Plane → Plane → Fin 6) : Prop :=
  ∀ p ∈ X, IsSlotAssignment ε X p (θ p) (σ p)

/-- A vertex is full if it has six nearest neighbors; a retained vertex which is not full is
deficient. -/
def IsFull (ε : ℝ) (X : Set Plane) (p : Plane) : Prop :=
  (nbrs ε X p).encard = 6

/-- Slot `j` at `p` is occupied for the slot assignment `σ` if some nearest neighbor is assigned
to it. -/
def IsOccupied (ε : ℝ) (X : Set Plane) (p : Plane) (σ : Plane → Fin 6) (j : Fin 6) : Prop :=
  ∃ q ∈ nbrs ε X p, σ q = j

open Classical in
/-- The occupant of slot `j` at `p` (by convention `p` itself if the slot is unoccupied). -/
noncomputable def occupant (ε : ℝ) (X : Set Plane) (p : Plane) (σ : Plane → Fin 6) (j : Fin 6) :
    Plane :=
  if h : IsOccupied ε X p σ j then h.choose else p

/-- The largest directional error `a_p` at `p` (`0` if `p` has no nearest neighbor). -/
noncomputable def dirErrMax (ε : ℝ) (X : Set Plane) (p : Plane) (θ : ℝ) (σ : Plane → Fin 6) :
    ℝ :=
  sSup (slotError p θ σ '' nbrs ε X p)

/-- The largest relative length error `s_p = max_q ||q - p|/ℓ - 1|` over the nearest neighbors
(`0` if there is none). -/
noncomputable def strainMax (ε : ℝ) (X : Set Plane) (p : Plane) : ℝ :=
  sSup ((fun q => |‖q - p‖ / latticeSpacing - 1|) '' nbrs ε X p)

/-- The representative `Δ` of `θ - θ'` modulo `π/3` of least absolute value. -/
noncomputable def orientDiff (θ θ' : ℝ) : ℝ :=
  θ - θ' - round ((θ - θ') / (π / 3)) * (π / 3)

/-- The endpoint error `err_{p,j} = q_j - p - ℓ e_{θ + jπ/3}` of slot `j`, `q_j` its occupant. -/
noncomputable def endpointErr (ε : ℝ) (X : Set Plane) (p : Plane) (θ : ℝ) (σ : Plane → Fin 6)
    (j : Fin 6) : Plane :=
  occupant ε X p σ j - p - latticeSpacing • unitVec (slotAngle θ j)

/-! ### Existence and translations -/

/-- Orientations and slot assignments exist at every point. -/
theorem exists_isSlotAssignment (ε : ℝ) (X : Set Plane) (p : Plane) :
    ∃ θ σ, IsSlotAssignment ε X p θ σ := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, (nbrs ε X p).Nonempty →
      ∃ q₀ ∈ nbrs ε X p, q₀ - p = ‖q₀ - p‖ • unitVec θ := by
    by_cases h : (nbrs ε X p).Nonempty
    · obtain ⟨q₀, hq₀⟩ := h
      exact ⟨vecArg (q₀ - p), fun _ => ⟨q₀, hq₀, (norm_smul_unitVec_vecArg _).symm⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  have hσ : ∀ q : Plane, ∃ j : Fin 6, ∀ k : Fin 6,
      angle (q - p) (unitVec (slotAngle θ j)) ≤ angle (q - p) (unitVec (slotAngle θ k)) := by
    intro q
    obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ
      (fun k => angle (q - p) (unitVec (slotAngle θ k))) Finset.univ_nonempty
    exact ⟨j, fun k => hj k (Finset.mem_univ k)⟩
  choose σ hσ using hσ
  exact ⟨θ, σ, hθ, fun q _ k => hσ q k⟩

/-- Orientations of `X` exist. -/
theorem exists_isOrientation (ε : ℝ) (X : Set Plane) : ∃ θ σ, IsOrientation ε X θ σ := by
  choose θ σ h using exists_isSlotAssignment ε X
  exact ⟨θ, σ, fun p _ => h p⟩

theorem mem_nbrs_add_vec (hv : ∀ x, x + v ∈ X ↔ x ∈ X) :
    q ∈ nbrs ε X (p + v) ↔ q - v ∈ nbrs ε X p := by
  rw [mem_nbrs, mem_nbrs, ← hv (q - v), sub_add_cancel,
    show q - v - p = q - (p + v) by abel]

/-- Slot assignments are compatible with translations preserving `X`. -/
theorem IsSlotAssignment.add_vec (h : IsSlotAssignment ε X p θ σ)
    (hv : ∀ x, x + v ∈ X ↔ x ∈ X) :
    IsSlotAssignment ε X (p + v) θ (fun q => σ (q - v)) where
  anchor hne := by
    obtain ⟨q, hq⟩ := hne
    obtain ⟨q₀, hq₀, he⟩ := h.anchor ⟨q - v, (mem_nbrs_add_vec hv).1 hq⟩
    refine ⟨q₀ + v, (mem_nbrs_add_vec hv).2 (by simpa using hq₀), ?_⟩
    rwa [show q₀ + v - (p + v) = q₀ - p by abel]
  closest q hq j := by
    have := h.closest (q - v) ((mem_nbrs_add_vec hv).1 hq) j
    rwa [show q - v - p = q - (p + v) by abel] at this

/-! ### Directional errors -/

theorem angle_slotAngle_eq_norm (hX : IsRetainedSet ε X) (hq : q ∈ nbrs ε X p) (θ : ℝ)
    (j : Fin 6) :
    angle (q - p) (unitVec (slotAngle θ j)) = ‖dir (q - p) - (slotAngle θ j : Angle)‖ :=
  angle_unitVec_right (hX.sub_ne_zero_of_mem_nbrs hq) _

namespace IsSlotAssignment

/-- The anchor neighbor: some nearest neighbor `q₀` has direction `θ`. -/
theorem exists_dir_eq (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hne : (nbrs ε X p).Nonempty) : ∃ q₀ ∈ nbrs ε X p, dir (q₀ - p) = θ := by
  obtain ⟨q₀, hq₀, he⟩ := h.anchor hne
  exact ⟨q₀, hq₀, dir_eq_of_eq_smul (norm_pos_iff.2 (hX.sub_ne_zero_of_mem_nbrs hq₀)) he⟩

/-- Every nearest neighbor is within `4√ε` of some slot direction. -/
theorem exists_slot_near (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hq : q ∈ nbrs ε X p) : ∃ j : Fin 6, ‖dir (q - p) - (slotAngle θ j : Angle)‖ ≤ 4 * √ε := by
  obtain ⟨q₀, hq₀, hdir⟩ := h.exists_dir_eq hX ⟨q, hq⟩
  have hε := hX.le_small
  have hε0 := hX.pos
  have hsq := hX.sqrt_le
  have hes := hX.eps_le_sqrt_div
  by_cases hqq₀ : q = q₀
  · refine ⟨0, ?_⟩
    rw [slotAngle_zero, hqq₀, hdir, sub_self, norm_zero]
    positivity
  set ψ := (dir (q - p) - (θ : Angle)).toReal with hψ
  have hdq : dir (q - p) = ((θ + ψ : ℝ) : Angle) := by
    rw [Angle.coe_add, hψ, Angle.coe_toReal, add_sub_cancel]
  have hd : angle (q - p) (q₀ - p) = |ψ| := by
    rw [angle_eq_norm_dir_sub (hX.sub_ne_zero_of_mem_nbrs hq) (hX.sub_ne_zero_of_mem_nbrs hq₀),
      hdir, Angle.norm_eq_abs_toReal]
  have hπ := angle_le_pi (q - p) (q₀ - p)
  rw [hdq]
  rcases hX.threeShell hq hq₀ hqq₀ with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
  · exact exists_norm_coe_sub_slotAngle_le θ ψ _ 1
      (by rw [← hd]; push_cast; rw [one_mul]; linarith [Real.sqrt_nonneg ε])
  · exact exists_norm_coe_sub_slotAngle_le θ ψ _ 2
      (by
        rw [← hd]; push_cast; rw [show (2 : ℝ) * (π / 3) = 2 * π / 3 by ring]
        linarith [Real.sqrt_nonneg ε])
  · refine exists_norm_coe_sub_slotAngle_le θ ψ _ 3 ?_
    rw [← hd]
    push_cast
    rw [show (3 : ℝ) * (π / 3) = π by ring, abs_le]
    constructor <;> linarith

/-- **Directional errors are small** (Lemma 5.5(b) with `A'_dir = 6`, and the `√ε` bound at every
vertex): every directional error is at most `4√ε`. -/
theorem slotError_le (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hq : q ∈ nbrs ε X p) : slotError p θ σ q ≤ 4 * √ε := by
  obtain ⟨j, hj⟩ := h.exists_slot_near hX hq
  exact (h.closest q hq j).trans ((angle_slotAngle_eq_norm hX hq θ j).trans_le hj)

theorem norm_dir_sub_le (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hq : q ∈ nbrs ε X p) : ‖dir (q - p) - (slotAngle θ (σ q) : Angle)‖ ≤ 4 * √ε := by
  rw [← angle_slotAngle_eq_norm hX hq θ]
  exact h.slotError_le hX hq

/-- **Distinct neighbors receive distinct slots** (Lemma 5.5(b)). -/
theorem injOn (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ) :
    Set.InjOn σ (nbrs ε X p) := by
  intro q hq q' hq' hσ
  by_contra hne
  have h1 := h.norm_dir_sub_le hX hq
  have h2 := h.norm_dir_sub_le hX hq'
  rw [← hσ] at h2
  have h3 := hX.pi_div_three_sub_le_angle hq hq' hne
  rw [angle_eq_norm_dir_sub (hX.sub_ne_zero_of_mem_nbrs hq) (hX.sub_ne_zero_of_mem_nbrs hq')]
    at h3
  have h4 := norm_sub_le_norm_sub_add_norm_sub (dir (q - p)) (slotAngle θ (σ q) : Angle)
    (dir (q' - p))
  rw [norm_sub_rev (slotAngle θ (σ q) : Angle)] at h4
  have hε := hX.le_small
  have hsq := hX.sqrt_le
  have hπ := Real.pi_gt_three
  linarith

/-- The anchor neighbor occupies slot `0`. -/
theorem slot_eq_zero (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hq₀ : q ∈ nbrs ε X p) (hdir : dir (q - p) = θ) : σ q = 0 := by
  have h1 := h.closest q hq₀ 0
  rw [angle_slotAngle_eq_norm hX hq₀, angle_slotAngle_eq_norm hX hq₀, hdir, slotAngle_zero,
    sub_self, norm_zero] at h1
  have h2 : (θ : Angle) = slotAngle θ (σ q) :=
    sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  by_contra hne
  exact coe_slotAngle_ne (θ := θ) hne (by rw [← h2, slotAngle_zero])

end IsSlotAssignment

/-- **At most six nearest neighbors** (Lemma 5.3). -/
theorem IsRetainedSet.encard_nbrs_le_six (hX : IsRetainedSet ε X) (p : Plane) :
    (nbrs ε X p).encard ≤ 6 := by
  obtain ⟨θ, σ, h⟩ := exists_isSlotAssignment ε X p
  calc (nbrs ε X p).encard ≤ (Set.univ : Set (Fin 6)).encard :=
        Set.encard_le_encard_of_injOn (fun _ _ => Set.mem_univ _) (h.injOn hX)
    _ = 6 := by simp

theorem IsRetainedSet.finite_nbrs (hX : IsRetainedSet ε X) (p : Plane) :
    (nbrs ε X p).Finite :=
  Set.finite_of_encard_le_coe (hX.encard_nbrs_le_six p)

/-! ### Occupancy -/

theorem occupant_spec (hj : IsOccupied ε X p σ j) :
    occupant ε X p σ j ∈ nbrs ε X p ∧ σ (occupant ε X p σ j) = j := by
  unfold occupant
  split_ifs
  exact hj.choose_spec

theorem occupant_mem_nbrs (hj : IsOccupied ε X p σ j) : occupant ε X p σ j ∈ nbrs ε X p :=
  (occupant_spec hj).1

theorem slot_occupant (hj : IsOccupied ε X p σ j) : σ (occupant ε X p σ j) = j :=
  (occupant_spec hj).2

theorem occupant_of_not_isOccupied (hj : ¬IsOccupied ε X p σ j) : occupant ε X p σ j = p := by
  unfold occupant
  split_ifs
  rfl

theorem occupant_mem_nbrs_or_eq (j : Fin 6) :
    occupant ε X p σ j ∈ nbrs ε X p ∨ occupant ε X p σ j = p := by
  by_cases hj : IsOccupied ε X p σ j
  · exact Or.inl (occupant_mem_nbrs hj)
  · exact Or.inr (occupant_of_not_isOccupied hj)

theorem isOccupied_slot (hq : q ∈ nbrs ε X p) : IsOccupied ε X p σ (σ q) :=
  ⟨q, hq, rfl⟩

/-- Distinct occupied slots have distinct occupants. -/
theorem eq_of_occupant_eq {i j : Fin 6} (hi : IsOccupied ε X p σ i) (hj : IsOccupied ε X p σ j)
    (hij : occupant ε X p σ i = occupant ε X p σ j) : i = j := by
  rw [← slot_occupant hi, ← slot_occupant hj, hij]

namespace IsSlotAssignment

/-- The occupant of the slot of a neighbor is that neighbor. -/
theorem occupant_slot (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hq : q ∈ nbrs ε X p) : occupant ε X p σ (σ q) = q :=
  h.injOn hX (occupant_mem_nbrs (isOccupied_slot hq)) hq (slot_occupant (isOccupied_slot hq))

/-- At a full vertex every slot is occupied. -/
theorem isOccupied_of_isFull (hX : IsRetainedSet ε X) (h : IsSlotAssignment ε X p θ σ)
    (hp : IsFull ε X p) (j : Fin 6) : IsOccupied ε X p σ j := by
  have himg : σ '' nbrs ε X p = Set.univ := by
    refine (Set.toFinite _).eq_of_subset_of_encard_le (Set.subset_univ _) ?_
    rw [(h.injOn hX).encard_image, hp]
    simp
  have : j ∈ σ '' nbrs ε X p := himg ▸ Set.mem_univ j
  obtain ⟨q, hq, rfl⟩ := this
  exact isOccupied_slot hq

/-- A vertex all of whose slots are occupied is full. -/
theorem isFull_of_forall_isOccupied (hX : IsRetainedSet ε X)
    (h : ∀ j, IsOccupied ε X p σ j) : IsFull ε X p := by
  refine le_antisymm (hX.encard_nbrs_le_six p) ?_
  have himg : σ '' nbrs ε X p = Set.univ := by
    ext j
    simp only [Set.mem_image, Set.mem_univ, iff_true]
    obtain ⟨q, hq, hj⟩ := h j
    exact ⟨q, hq, hj⟩
  calc (6 : ℕ∞) = (Set.univ : Set (Fin 6)).encard := by simp
    _ = (σ '' nbrs ε X p).encard := by rw [himg]
    _ ≤ (nbrs ε X p).encard := Set.encard_image_le _ _

/-- A deficient vertex has an unoccupied slot. -/
theorem exists_not_isOccupied (hX : IsRetainedSet ε X) (hp : ¬IsFull ε X p) :
    ∃ j, ¬IsOccupied ε X p σ j := by
  by_contra hcon
  push Not at hcon
  exact hp (isFull_of_forall_isOccupied hX hcon)

end IsSlotAssignment

/-! ### The largest errors `a_p` and `s_p` -/

theorem slotError_nonneg (p : Plane) (θ : ℝ) (σ : Plane → Fin 6) (q : Plane) :
    0 ≤ slotError p θ σ q :=
  angle_nonneg _ _

theorem dirErrMax_nonneg : 0 ≤ dirErrMax ε X p θ σ :=
  Real.sSup_nonneg (by rintro _ ⟨q, -, rfl⟩; exact slotError_nonneg _ _ _ _)

theorem slotError_le_dirErrMax (hq : q ∈ nbrs ε X p) :
    slotError p θ σ q ≤ dirErrMax ε X p θ σ :=
  le_csSup ⟨π, by rintro _ ⟨q, -, rfl⟩; exact angle_le_pi _ _⟩ ⟨q, hq, rfl⟩

theorem dirErrMax_le {a : ℝ} (ha : 0 ≤ a) (h : ∀ q ∈ nbrs ε X p, slotError p θ σ q ≤ a) :
    dirErrMax ε X p θ σ ≤ a :=
  Real.sSup_le (by rintro _ ⟨q, hq, rfl⟩; exact h q hq) ha

theorem IsSlotAssignment.dirErrMax_le (hX : IsRetainedSet ε X)
    (h : IsSlotAssignment ε X p θ σ) : dirErrMax ε X p θ σ ≤ 4 * √ε :=
  TriangularLattice.dirErrMax_le (by positivity) fun _ hq => h.slotError_le hX hq

theorem strainMax_nonneg : 0 ≤ strainMax ε X p :=
  Real.sSup_nonneg (by rintro _ ⟨q, -, rfl⟩; exact abs_nonneg _)

theorem strainMax_le {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ q ∈ nbrs ε X p, |‖q - p‖ / latticeSpacing - 1| ≤ s) : strainMax ε X p ≤ s :=
  Real.sSup_le (by rintro _ ⟨q, hq, rfl⟩; exact h q hq) hs

theorem le_strainMax (hq : q ∈ nbrs ε X p) :
    |‖q - p‖ / latticeSpacing - 1| ≤ strainMax ε X p :=
  le_csSup ⟨ε, by rintro _ ⟨q, hq, rfl⟩; exact hq.2⟩ ⟨q, hq, rfl⟩

theorem IsRetainedSet.strainMax_le_eps (hX : IsRetainedSet ε X) : strainMax ε X p ≤ ε :=
  strainMax_le hX.pos.le fun _ hq => hq.2

/-- `s_p` is attained at some nearest neighbor (if there is one). -/
theorem IsRetainedSet.exists_strainMax_eq (hX : IsRetainedSet ε X)
    (hne : (nbrs ε X p).Nonempty) :
    ∃ q ∈ nbrs ε X p, strainMax ε X p = |‖q - p‖ / latticeSpacing - 1| := by
  have hfin := (hX.finite_nbrs p).image (fun q => |‖q - p‖ / latticeSpacing - 1|)
  obtain ⟨q, hq, hmax⟩ := (hne.image _).csSup_mem hfin
  exact ⟨q, hq, hmax.symm⟩

/-! ### Orientation differences along nearest edges -/

theorem abs_orientDiff_le_abs (θ θ' : ℝ) (k : ℤ) :
    |orientDiff θ θ'| ≤ |θ - θ' - k * (π / 3)| := by
  have hπ : 0 < π / 3 := by positivity
  have h1 : orientDiff θ θ' = (π / 3) * ((θ - θ') / (π / 3) - round ((θ - θ') / (π / 3))) := by
    rw [orientDiff]
    field_simp
  have h2 : θ - θ' - k * (π / 3) = (π / 3) * ((θ - θ') / (π / 3) - k) := by
    field_simp
  rw [h1, h2, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (round_le _ _) (abs_nonneg _)

/-- If `θ - θ'` is within `a` of `kπ/3` modulo `2π`, then `|Δ| ≤ a`. -/
theorem abs_orientDiff_le_of_norm_le {θ θ' a : ℝ} (k : ℤ)
    (h : ‖((θ - θ' - k * (π / 3) : ℝ) : Angle)‖ ≤ a) : |orientDiff θ θ'| ≤ a := by
  have hn : ‖((θ - θ' - k * (π / 3) : ℝ) : Angle)‖ =
      |θ - θ' - k * (π / 3) - round ((2 * π)⁻¹ * (θ - θ' - k * (π / 3))) * (2 * π)| :=
    AddCircle.norm_eq (p := 2 * π)
  set m := round ((2 * π)⁻¹ * (θ - θ' - k * (π / 3)))
  refine (abs_orientDiff_le_abs θ θ' (k + 6 * m)).trans ?_
  rw [hn] at h
  convert h using 2
  push_cast
  ring

/-- **Lemma 5.5(d).** For every nearest edge `{p, q}`, `|Δ_pq| ≤ a_p + a_q`. -/
theorem abs_orientDiff_le (hX : IsRetainedSet ε X) (hp : p ∈ X) (hq : q ∈ nbrs ε X p)
    (θ : Plane → ℝ) (σ : Plane → Plane → Fin 6) :
    |orientDiff (θ p) (θ q)| ≤ dirErrMax ε X p (θ p) (σ p) + dirErrMax ε X q (θ q) (σ q) := by
  have hpq : p ∈ nbrs ε X q := mem_nbrs_comm hp hq
  have h1 := (angle_slotAngle_eq_norm hX hq (θ p) (σ p q)).symm.trans_le
    (slotError_le_dirErrMax (θ := θ p) (σ := σ p) hq)
  have h2 := (angle_slotAngle_eq_norm hX hpq (θ q) (σ q p)).symm.trans_le
    (slotError_le_dirErrMax (θ := θ q) (σ := σ q) hpq)
  have hneg : p - q = -(q - p) := (neg_sub q p).symm
  rw [hneg, dir_neg (hX.sub_ne_zero_of_mem_nbrs hq)] at h2
  refine abs_orientDiff_le_of_norm_le ((σ q p : ℕ) - (σ p q : ℕ) - 3) ?_
  have key : ((θ p - θ q - (((σ q p : ℕ) : ℤ) - ((σ p q : ℕ) : ℤ) - 3 : ℤ) * (π / 3) : ℝ) :
      Angle) = (dir (q - p) + π - slotAngle (θ q) (σ q p)) - (dir (q - p) -
        slotAngle (θ p) (σ p q)) := by
    have e : (dir (q - p) + π - slotAngle (θ q) (σ q p)) - (dir (q - p) -
        slotAngle (θ p) (σ p q)) =
        (((π : ℝ) - slotAngle (θ q) (σ q p) + slotAngle (θ p) (σ p q) : ℝ) : Angle) := by
      rw [Angle.coe_add, Angle.coe_sub]
      abel
    rw [e, Angle.angle_eq_iff_two_pi_dvd_sub]
    exact ⟨0, by simp only [slotAngle]; push_cast; ring⟩
  rw [key]
  exact (norm_sub_le _ _).trans (by linarith)

/-! ### Endpoint errors -/

/-- **Endpoint errors** (behind Lemma 5.5(e)): `|err_{p,j}| ≤ ℓ (s_p + a_p)` for an occupied
slot. -/
theorem norm_endpointErr_le (hX : IsRetainedSet ε X) {j : Fin 6} (hj : IsOccupied ε X p σ j) :
    ‖endpointErr ε X p θ σ j‖ ≤
      latticeSpacing * (strainMax ε X p + dirErrMax ε X p θ σ) := by
  set q := occupant ε X p σ j
  have hq : q ∈ nbrs ε X p := occupant_mem_nbrs hj
  have hσq : σ q = j := slot_occupant hj
  have hℓ := latticeSpacing_pos
  have h1 : endpointErr ε X p θ σ j =
      ‖q - p‖ • unitVec (vecArg (q - p)) - latticeSpacing • unitVec (slotAngle θ j) := by
    rw [endpointErr, norm_smul_unitVec_vecArg]
  rw [h1]
  refine (norm_smul_unitVec_sub_le hℓ.le _ _).trans ?_
  have h2 : |‖q - p‖ - latticeSpacing| ≤ latticeSpacing * strainMax ε X p := by
    have := le_strainMax hq
    rw [show ‖q - p‖ - latticeSpacing = latticeSpacing * (‖q - p‖ / latticeSpacing - 1) by
      field_simp, abs_mul, abs_of_pos hℓ]
    exact mul_le_mul_of_nonneg_left this hℓ.le
  have h3 : ‖((vecArg (q - p) : ℝ) : Angle) - slotAngle θ j‖ ≤ dirErrMax ε X p θ σ := by
    have := slotError_le_dirErrMax (θ := θ) (σ := σ) hq
    rwa [slotError, hσq, angle_slotAngle_eq_norm hX hq θ] at this
  nlinarith

end TriangularLattice
