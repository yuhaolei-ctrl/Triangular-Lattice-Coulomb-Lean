/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Statement
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Lattices in the plane

A lattice `Γ = ℤ b₀ + ℤ b₁` in the plane is given by a basis `b₀, b₁` with nonzero determinant.
This file develops the elementary theory of such lattices used in §2.1 of the manuscript.

## Main definitions

* `TriangularLattice.PlaneLattice`: a lattice in the plane, given by a basis.
* `PlaneLattice.det`, `PlaneLattice.covolume`: the determinant `det (b₀, b₁)` and the covolume
  `|det (b₀, b₁)|`.
* `PlaneLattice.points`: the points `ℤ b₀ + ℤ b₁`, as a `ℤ`-submodule of the plane, and
  `PlaneLattice.point : ℤ × ℤ → Plane`, `(m, n) ↦ m b₀ + n b₁`.
* `PlaneLattice.dual`: the dual (reciprocal) lattice, with basis `b₀*, b₁*` such that
  `⟪bᵢ*, bⱼ⟫ = δᵢⱼ`.
* `PlaneLattice.cell`: the half-open fundamental parallelogram `{s b₀ + t b₁ : s, t ∈ [0, 1)}`.
* `PlaneLattice.scale`: the scaled lattice `s Γ`.
* `PlaneLattice.triangular`: the triangular lattice `Λ` of covolume one.
* `TriangularLattice.planeRotation`: the rotation of the plane by an angle.

## Main results

* `PlaneLattice.mem_dual_points_iff`: `k ∈ Γ* ↔ ∀ v ∈ Γ, ⟪k, v⟫ ∈ ℤ`.
* `PlaneLattice.isAddFundamentalDomain_cell`, `PlaneLattice.existsUnique_sub_mem_cell`: the
  translates of the cell by `Γ` tile the plane.
* `PlaneLattice.volume_cell`: the cell has measure `covolume Γ`.
* `PlaneLattice.ncard_inter_closedBall_le`: `#(Γ ∩ closedBall x r) ≤ C_Γ (1 + r)²`.
* `PlaneLattice.summable_comp_add` and `PlaneLattice.hasSumLocallyUniformly_comp_add`: lattice
  sums `∑_{v ∈ Γ} f (x + v)` of functions with `‖f y‖ ≤ A (1 + ‖y‖)^(-s)`, `s > 2`, converge
  absolutely and locally uniformly in `x`.
* `PlaneLattice.coe_triangular_points`, `PlaneLattice.triangular_cell`,
  `PlaneLattice.covolume_triangular`, `PlaneLattice.coe_triangular_dual_points`,
  `PlaneLattice.norm_sq_triangular_point`: the triangular lattice is `triangularLattice`, its cell
  is `fundamentalCell`, it has covolume one, its dual is its rotation by `π/6`, and
  `|ℓ (a + b/2, b√3/2)|² = ℓ² (a² + ab + b²)`.
-/

@[expose] public section

open MeasureTheory Metric Set Module Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace TriangularLattice

/-! ### Coordinates in the plane -/

/-- The inner product on the plane in coordinates: `⟪x, y⟫ = x₀ y₀ + x₁ y₁`. -/
theorem inner_plane (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The squared norm on the plane in coordinates: `‖x‖² = x₀² + x₁²`. -/
theorem norm_sq_plane (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

/-- A lattice `Γ = ℤ b₀ + ℤ b₁` in the plane, given by a basis `b₀, b₁` with nonzero
determinant. -/
@[ext]
structure PlaneLattice where
  /-- The first basis vector. -/
  b₀ : Plane
  /-- The second basis vector. -/
  b₁ : Plane
  /-- The basis vectors are linearly independent; see `PlaneLattice.det_ne_zero`. -/
  det_ne_zero' : b₀ 0 * b₁ 1 - b₀ 1 * b₁ 0 ≠ 0

namespace PlaneLattice

variable (Γ : PlaneLattice)

/-! ### Determinant, covolume and the dual lattice -/

/-- The determinant `det (b₀, b₁)` of the basis of `Γ`. -/
def det : ℝ := Γ.b₀ 0 * Γ.b₁ 1 - Γ.b₀ 1 * Γ.b₁ 0

/-- The determinant of the basis of a lattice is nonzero. -/
theorem det_ne_zero : Γ.det ≠ 0 := Γ.det_ne_zero'

/-- The covolume `|det (b₀, b₁)|` of `Γ`, the area of a fundamental cell. -/
def covolume : ℝ := |Γ.det|

/-- The covolume of a lattice is positive. -/
theorem covolume_pos : 0 < Γ.covolume := abs_pos.mpr Γ.det_ne_zero

/-- The covolume of a lattice is nonzero. -/
theorem covolume_ne_zero : Γ.covolume ≠ 0 := Γ.covolume_pos.ne'

/-- The dual (reciprocal) lattice `Γ* = {k : ⟪k, v⟫ ∈ ℤ for all v ∈ Γ}`, with basis
`b₀* = det⁻¹ (b₁ 1, -b₁ 0)` and `b₁* = det⁻¹ (-b₀ 1, b₀ 0)`, so that `⟪bᵢ*, bⱼ⟫ = δᵢⱼ`. -/
noncomputable def dual : PlaneLattice where
  b₀ := Γ.det⁻¹ • !₂[Γ.b₁ 1, -Γ.b₁ 0]
  b₁ := Γ.det⁻¹ • !₂[-Γ.b₀ 1, Γ.b₀ 0]
  det_ne_zero' := by
    have h := Γ.det_ne_zero
    convert inv_ne_zero h using 1
    simp only [det] at h ⊢
    simp
    field_simp

/-- The first dual basis vector is `b₀* = det⁻¹ (b₁ 1, -b₁ 0)`. -/
theorem dual_b₀ : Γ.dual.b₀ = Γ.det⁻¹ • !₂[Γ.b₁ 1, -Γ.b₁ 0] := rfl

/-- The second dual basis vector is `b₁* = det⁻¹ (-b₀ 1, b₀ 0)`. -/
theorem dual_b₁ : Γ.dual.b₁ = Γ.det⁻¹ • !₂[-Γ.b₀ 1, Γ.b₀ 0] := rfl

/-- The determinant of the dual basis is `det⁻¹`. -/
@[simp]
theorem det_dual : Γ.dual.det = Γ.det⁻¹ := by
  have h := Γ.det_ne_zero
  simp only [det, dual_b₀, dual_b₁] at h ⊢
  simp
  field_simp

/-- The covolume of the dual lattice is the inverse covolume. -/
@[simp]
theorem covolume_dual : Γ.dual.covolume = Γ.covolume⁻¹ := by
  simp [covolume, abs_inv]

/-- The dual of the dual lattice is the lattice itself (with the same basis). -/
@[simp]
theorem dual_dual : Γ.dual.dual = Γ := by
  have h := Γ.det_ne_zero
  ext i <;> fin_cases i <;> simp [dual_b₀, dual_b₁, det] at h ⊢ <;> field_simp

/-- Biorthogonality: `⟪b₀*, b₀⟫ = 1`. -/
@[simp]
theorem inner_dual_b₀_b₀ : ⟪Γ.dual.b₀, Γ.b₀⟫ = 1 := by
  have h := Γ.det_ne_zero
  simp only [det] at h
  simp [inner_plane, dual_b₀, det]
  field_simp
  ring

/-- Biorthogonality: `⟪b₀*, b₁⟫ = 0`. -/
@[simp]
theorem inner_dual_b₀_b₁ : ⟪Γ.dual.b₀, Γ.b₁⟫ = 0 := by
  simp [inner_plane, dual_b₀]
  ring

/-- Biorthogonality: `⟪b₁*, b₀⟫ = 0`. -/
@[simp]
theorem inner_dual_b₁_b₀ : ⟪Γ.dual.b₁, Γ.b₀⟫ = 0 := by
  simp [inner_plane, dual_b₁]
  ring

/-- Biorthogonality: `⟪b₁*, b₁⟫ = 1`. -/
@[simp]
theorem inner_dual_b₁_b₁ : ⟪Γ.dual.b₁, Γ.b₁⟫ = 1 := by
  have h := Γ.det_ne_zero
  simp only [det] at h
  simp [inner_plane, dual_b₁, det]
  field_simp
  ring

/-- Biorthogonality: `⟪b₀, b₀*⟫ = 1`. -/
@[simp]
theorem inner_b₀_dual_b₀ : ⟪Γ.b₀, Γ.dual.b₀⟫ = 1 := by
  rw [real_inner_comm, inner_dual_b₀_b₀]

/-- Biorthogonality: `⟪b₁, b₀*⟫ = 0`. -/
@[simp]
theorem inner_b₁_dual_b₀ : ⟪Γ.b₁, Γ.dual.b₀⟫ = 0 := by
  rw [real_inner_comm, inner_dual_b₀_b₁]

/-- Biorthogonality: `⟪b₀, b₁*⟫ = 0`. -/
@[simp]
theorem inner_b₀_dual_b₁ : ⟪Γ.b₀, Γ.dual.b₁⟫ = 0 := by
  rw [real_inner_comm, inner_dual_b₁_b₀]

/-- Biorthogonality: `⟪b₁, b₁*⟫ = 1`. -/
@[simp]
theorem inner_b₁_dual_b₁ : ⟪Γ.b₁, Γ.dual.b₁⟫ = 1 := by
  rw [real_inner_comm, inner_dual_b₁_b₁]

/-- Every vector is `x = ⟪x, b₀*⟫ b₀ + ⟪x, b₁*⟫ b₁`. -/
theorem inner_dual_smul_add_inner_dual_smul (x : Plane) :
    ⟪x, Γ.dual.b₀⟫ • Γ.b₀ + ⟪x, Γ.dual.b₁⟫ • Γ.b₁ = x := by
  have h := Γ.det_ne_zero
  simp only [det] at h
  ext i
  fin_cases i <;> simp [inner_plane, dual_b₀, dual_b₁, det] <;> field_simp <;> ring

/-! ### Coordinates and the basis -/

/-- The coordinates `x ↦ (⟪x, b₀*⟫, ⟪x, b₁*⟫)` with respect to the basis of `Γ`, as a linear
equivalence; its inverse is `t ↦ t 0 • b₀ + t 1 • b₁`. -/
noncomputable def equivFun : Plane ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![⟪x, Γ.dual.b₀⟫, ⟪x, Γ.dual.b₁⟫]
  invFun t := t 0 • Γ.b₀ + t 1 • Γ.b₁
  map_add' x y := by ext i; fin_cases i <;> simp [inner_add_left]
  map_smul' c x := by ext i; fin_cases i <;> simp [real_inner_smul_left]
  left_inv x := Γ.inner_dual_smul_add_inner_dual_smul x
  right_inv t := by
    ext i; fin_cases i <;> simp [inner_add_left, real_inner_smul_left]

/-- The first coordinate of `x` is `⟪x, b₀*⟫`. -/
@[simp]
theorem equivFun_apply_zero (x : Plane) : Γ.equivFun x 0 = ⟪x, Γ.dual.b₀⟫ := rfl

/-- The second coordinate of `x` is `⟪x, b₁*⟫`. -/
@[simp]
theorem equivFun_apply_one (x : Plane) : Γ.equivFun x 1 = ⟪x, Γ.dual.b₁⟫ := rfl

/-- The inverse of the coordinate map is `t ↦ t 0 • b₀ + t 1 • b₁`. -/
@[simp]
theorem equivFun_symm_apply (t : Fin 2 → ℝ) : Γ.equivFun.symm t = t 0 • Γ.b₀ + t 1 • Γ.b₁ :=
  rfl

/-- The basis `b₀, b₁` of the plane. -/
noncomputable def basis : Basis (Fin 2) ℝ Plane := Basis.ofEquivFun Γ.equivFun

/-- The first vector of `Γ.basis` is `b₀`. -/
@[simp]
theorem basis_zero : Γ.basis 0 = Γ.b₀ := by
  simp [basis, Basis.coe_ofEquivFun]

/-- The second vector of `Γ.basis` is `b₁`. -/
@[simp]
theorem basis_one : Γ.basis 1 = Γ.b₁ := by
  simp [basis, Basis.coe_ofEquivFun]

/-- The basis `Γ.basis` is `![b₀, b₁]`. -/
theorem coe_basis : ⇑Γ.basis = ![Γ.b₀, Γ.b₁] := by
  ext1 i; fin_cases i <;> simp

/-- The coordinates of `x` in `Γ.basis` are given by `Γ.equivFun`. -/
@[simp]
theorem basis_repr_apply (x : Plane) (i : Fin 2) : Γ.basis.repr x i = Γ.equivFun x i :=
  Basis.ofEquivFun_repr_apply _ _ _

/-- The coordinate map of `Γ.basis` is `Γ.equivFun`. -/
@[simp]
theorem basis_equivFun : Γ.basis.equivFun = Γ.equivFun := Basis.equivFun_ofEquivFun _

/-! ### The points of the lattice -/

/-- The points `ℤ b₀ + ℤ b₁` of `Γ`, as a `ℤ`-submodule of the plane. -/
def points : Submodule ℤ Plane := Submodule.span ℤ (Set.range Γ.basis)

/-- The points of `Γ` are the `ℤ`-span of `Γ.basis` (by definition). -/
theorem points_eq_span : Γ.points = Submodule.span ℤ (Set.range Γ.basis) := rfl

/-- The points of a lattice form a discrete subgroup of the plane. -/
instance : DiscreteTopology Γ.points :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range Γ.basis)))

/-- The points of a lattice form a `ℤ`-lattice in the sense of Mathlib. -/
instance : IsZLattice ℝ Γ.points :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range Γ.basis)))

/-- A lattice is countable. -/
instance : Countable Γ.points := inferInstance

/-- The lattice `Γ` has rank two. -/
theorem finrank_points : finrank ℤ Γ.points = 2 := by
  rw [ZLattice.rank ℝ, finrank_euclideanSpace_fin]

/-- The lattice point `m b₀ + n b₁`. -/
def point (p : ℤ × ℤ) : Plane := (p.1 : ℝ) • Γ.b₀ + (p.2 : ℝ) • Γ.b₁

/-- The lattice point of `-p` is the negative of the lattice point of `p`. -/
theorem point_neg (p : ℤ × ℤ) : Γ.point (-p) = -Γ.point p := by
  simp only [point, Prod.fst_neg, Prod.snd_neg, Int.cast_neg, neg_smul, neg_add]

/-- The lattice point of `p + q` is the sum of the lattice points of `p` and `q`. -/
theorem point_add (p q : ℤ × ℤ) : Γ.point (p + q) = Γ.point p + Γ.point q := by
  simp only [point, Prod.fst_add, Prod.snd_add, Int.cast_add, add_smul]
  abel

/-- The lattice point of `0` is `0`. -/
@[simp]
theorem point_zero : Γ.point 0 = 0 := by
  simp [point]

/-- The first coordinate of `m b₀ + n b₁` is `m`. -/
@[simp]
theorem inner_point_dual_b₀ (p : ℤ × ℤ) : ⟪Γ.point p, Γ.dual.b₀⟫ = p.1 := by
  simp [point, inner_add_left, real_inner_smul_left]

/-- The second coordinate of `m b₀ + n b₁` is `n`. -/
@[simp]
theorem inner_point_dual_b₁ (p : ℤ × ℤ) : ⟪Γ.point p, Γ.dual.b₁⟫ = p.2 := by
  simp [point, inner_add_left, real_inner_smul_left]

/-- A vector lies in `Γ` iff both of its coordinates `⟪v, bᵢ*⟫` are integers. -/
theorem mem_points_iff_inner {v : Plane} :
    v ∈ Γ.points ↔ (∃ m : ℤ, ⟪v, Γ.dual.b₀⟫ = m) ∧ ∃ n : ℤ, ⟪v, Γ.dual.b₁⟫ = n := by
  rw [points, Basis.mem_span_iff_repr_mem, Fin.forall_fin_two]
  simp [eq_comm]

/-- A vector lies in `Γ` iff it is `m b₀ + n b₁` for some integers `m, n`. -/
theorem mem_points {v : Plane} : v ∈ Γ.points ↔ ∃ p : ℤ × ℤ, Γ.point p = v := by
  rw [mem_points_iff_inner]
  constructor
  · rintro ⟨⟨m, hm⟩, n, hn⟩
    refine ⟨(m, n), ?_⟩
    rw [← Γ.inner_dual_smul_add_inner_dual_smul v, hm, hn, point]
  · rintro ⟨p, rfl⟩
    exact ⟨⟨p.1, by simp⟩, p.2, by simp⟩

/-- The vector `m b₀ + n b₁` lies in `Γ`. -/
theorem point_mem_points (p : ℤ × ℤ) : Γ.point p ∈ Γ.points := Γ.mem_points.mpr ⟨p, rfl⟩

/-- The basis vector `b₀` lies in `Γ`. -/
@[simp]
theorem b₀_mem_points : Γ.b₀ ∈ Γ.points := by
  simpa [point] using Γ.point_mem_points (1, 0)

/-- The basis vector `b₁` lies in `Γ`. -/
@[simp]
theorem b₁_mem_points : Γ.b₁ ∈ Γ.points := by
  simpa [point] using Γ.point_mem_points (0, 1)

/-- The range of `Γ.point` is the point set of `Γ`. -/
theorem range_point : Set.range Γ.point = Γ.points := by
  ext v
  simp [mem_points]

/-- The map `(m, n) ↦ m b₀ + n b₁` is injective. -/
theorem point_injective : Function.Injective Γ.point := by
  intro p q h
  have h₀ := congrArg (⟪·, Γ.dual.b₀⟫) h
  have h₁ := congrArg (⟪·, Γ.dual.b₁⟫) h
  simp only [inner_point_dual_b₀, inner_point_dual_b₁, Int.cast_inj] at h₀ h₁
  exact Prod.ext h₀ h₁

/-- The bijection `ℤ × ℤ ≃ Γ`, `(m, n) ↦ m b₀ + n b₁`. -/
noncomputable def pointEquiv : ℤ × ℤ ≃ Γ.points :=
  Equiv.ofBijective (fun p ↦ ⟨Γ.point p, Γ.point_mem_points p⟩)
    ⟨fun p q h ↦ Γ.point_injective (congrArg Subtype.val h), fun v ↦ by
      obtain ⟨p, hp⟩ := Γ.mem_points.mp v.2
      exact ⟨p, Subtype.ext hp⟩⟩

/-- The bijection `Γ.pointEquiv` sends `(m, n)` to `m b₀ + n b₁`. -/
@[simp]
theorem coe_pointEquiv (p : ℤ × ℤ) : (Γ.pointEquiv p : Plane) = Γ.point p := rfl

/-- The characterization `k ∈ Γ* ↔ ∀ v ∈ Γ, ⟪k, v⟫ ∈ ℤ` of the dual lattice. -/
theorem mem_dual_points_iff {k : Plane} :
    k ∈ Γ.dual.points ↔ ∀ v ∈ Γ.points, ∃ n : ℤ, ⟪k, v⟫ = n := by
  constructor
  · intro hk v hv
    obtain ⟨p, rfl⟩ := Γ.dual.mem_points.mp hk
    obtain ⟨q, rfl⟩ := Γ.mem_points.mp hv
    refine ⟨p.1 * q.1 + p.2 * q.2, ?_⟩
    simp [point, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    ring
  · intro h
    rw [Γ.dual.mem_points_iff_inner, dual_dual]
    exact ⟨h _ Γ.b₀_mem_points, h _ Γ.b₁_mem_points⟩

/-- The pairing of a lattice point and a dual lattice point is an integer. -/
theorem exists_int_inner_eq {v k : Plane} (hv : v ∈ Γ.points) (hk : k ∈ Γ.dual.points) :
    ∃ n : ℤ, ⟪v, k⟫ = n := by
  rw [real_inner_comm]
  exact Γ.mem_dual_points_iff.mp hk v hv

/-! ### The fundamental cell -/

/-- The half-open fundamental parallelogram `{s b₀ + t b₁ : s, t ∈ [0, 1)}` of `Γ`. -/
def cell : Set Plane :=
  {x | ∃ s ∈ Ico (0 : ℝ) 1, ∃ t ∈ Ico (0 : ℝ) 1, x = s • Γ.b₀ + t • Γ.b₁}

/-- A vector lies in the cell iff both of its coordinates lie in `[0, 1)`. -/
theorem mem_cell_iff {x : Plane} :
    x ∈ Γ.cell ↔ ⟪x, Γ.dual.b₀⟫ ∈ Ico (0 : ℝ) 1 ∧ ⟪x, Γ.dual.b₁⟫ ∈ Ico (0 : ℝ) 1 := by
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    simpa [inner_add_left, real_inner_smul_left] using ⟨hs, ht⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨_, h₀, _, h₁, (Γ.inner_dual_smul_add_inner_dual_smul x).symm⟩

/-- The cell of `Γ` is Mathlib's `ZSpan.fundamentalDomain` of its basis. -/
theorem cell_eq_fundamentalDomain : Γ.cell = ZSpan.fundamentalDomain Γ.basis := by
  ext x
  simp [mem_cell_iff, ZSpan.mem_fundamentalDomain, Fin.forall_fin_two]

/-- The cell is measurable. -/
theorem measurableSet_cell : MeasurableSet Γ.cell := by
  rw [cell_eq_fundamentalDomain]
  exact ZSpan.fundamentalDomain_measurableSet _

/-- The cell is bounded. -/
theorem isBounded_cell : Bornology.IsBounded Γ.cell := by
  rw [cell_eq_fundamentalDomain]
  exact ZSpan.fundamentalDomain_isBounded _

/-- The translates of the cell by the points of `Γ` tile the plane. -/
theorem isAddFundamentalDomain_cell' (μ : Measure Plane) :
    IsAddFundamentalDomain Γ.points Γ.cell μ := by
  rw [cell_eq_fundamentalDomain]
  exact ZSpan.isAddFundamentalDomain Γ.basis μ

/-- The translates of the cell by the points of `Γ` tile the plane (for Lebesgue measure). -/
theorem isAddFundamentalDomain_cell : IsAddFundamentalDomain Γ.points Γ.cell :=
  Γ.isAddFundamentalDomain_cell' volume

/-- Translation by lattice vectors preserves translation-invariant measures. -/
instance (μ : Measure Plane) [μ.IsAddLeftInvariant] : VAddInvariantMeasure Γ.points Plane μ :=
  inferInstanceAs (VAddInvariantMeasure Γ.points.toAddSubmonoid Plane μ)

/-- Every point of the plane is uniquely `x = y + v` with `y` in the cell and `v ∈ Γ`. -/
theorem existsUnique_sub_mem_cell (x : Plane) : ∃! v : Γ.points, x - v ∈ Γ.cell := by
  obtain ⟨v, hv, huniq⟩ : ∃! v : Γ.points, v +ᵥ x ∈ ZSpan.fundamentalDomain Γ.basis :=
    ZSpan.exist_unique_vadd_mem_fundamentalDomain Γ.basis x
  have key (w : Γ.points) :
      x - w ∈ Γ.cell ↔ (-w) +ᵥ x ∈ ZSpan.fundamentalDomain Γ.basis := by
    rw [cell_eq_fundamentalDomain, Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg,
      neg_add_eq_sub]
  refine ⟨-v, ?_, fun w hw ↦ ?_⟩
  · beta_reduce
    rw [key, neg_neg]
    exact hv
  · beta_reduce at hw
    rw [← huniq (-w) ((key w).mp hw), neg_neg]

/-- The cell has measure `covolume Γ`. -/
theorem volume_cell : volume Γ.cell = ENNReal.ofReal Γ.covolume := by
  classical
  let e := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have h₁ : volume (ZSpan.fundamentalDomain e) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped e volume)]
    simpa [e] using (EuclideanSpace.basisFun (Fin 2) ℝ).volume_parallelepiped
  have h₂ : e.det Γ.basis = Γ.det := by
    rw [Basis.det_apply, Matrix.det_fin_two]
    simp [e, Basis.toMatrix_apply, det]
    ring
  rw [cell_eq_fundamentalDomain, ZSpan.measure_fundamentalDomain Γ.basis volume e, h₁, h₂,
    mul_one, covolume]

/-- The cell has measure `covolume Γ` (real-valued version). -/
theorem volume_real_cell : volume.real Γ.cell = Γ.covolume := by
  rw [measureReal_def, volume_cell, ENNReal.toReal_ofReal Γ.covolume_pos.le]

/-- The reduction `x - ⌊x⌋_Γ` of a vector modulo `Γ` into the cell. -/
noncomputable def fract (x : Plane) : Plane := ZSpan.fract Γ.basis x

/-- The reduction of `x` modulo `Γ` lies in the cell. -/
theorem fract_mem_cell (x : Plane) : Γ.fract x ∈ Γ.cell := by
  rw [cell_eq_fundamentalDomain]
  exact ZSpan.fract_mem_fundamentalDomain _ x

/-- A vector differs from its reduction modulo `Γ` by a lattice vector. -/
theorem sub_fract_mem_points (x : Plane) : x - Γ.fract x ∈ Γ.points := by
  simp [fract, ZSpan.fract_apply, points]

/-- The reduction modulo `Γ` is `Γ`-periodic. -/
theorem fract_add_of_mem (x : Plane) {v : Plane} (hv : v ∈ Γ.points) :
    Γ.fract (x + v) = Γ.fract x :=
  ZSpan.fract_add_ZSpan Γ.basis x hv

/-- A vector is its own reduction modulo `Γ` iff it lies in the cell. -/
theorem fract_eq_self {x : Plane} : Γ.fract x = x ↔ x ∈ Γ.cell := by
  rw [cell_eq_fundamentalDomain]
  exact ZSpan.fract_eq_self

/-- Two vectors have the same reduction modulo `Γ` iff they differ by a lattice vector. -/
theorem fract_eq_fract_iff {x y : Plane} : Γ.fract x = Γ.fract y ↔ y - x ∈ Γ.points := by
  rw [fract, fract, ZSpan.fract_eq_fract, neg_add_eq_sub, points]

/-- The covolume agrees with Mathlib's `ZLattice.covolume`. -/
theorem zlattice_covolume_eq : ZLattice.covolume Γ.points = Γ.covolume := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Γ.points volume Γ.isAddFundamentalDomain_cell,
    volume_real_cell]

/-! ### Counting lattice points in discs -/

/-- An integer interval `[⌈c - R⌉, ⌊c + R⌋]` has at most `2R + 1` elements. -/
theorem card_Icc_ceil_floor_le (c : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ((Finset.Icc ⌈c - R⌉ ⌊c + R⌋).card : ℝ) ≤ 2 * R + 1 := by
  rw [Int.card_Icc]
  have h₁ : (⌊c + R⌋ : ℝ) ≤ c + R := Int.floor_le _
  have h₂ : c - R ≤ (⌈c - R⌉ : ℝ) := Int.le_ceil _
  have : ((⌊c + R⌋ + 1 - ⌈c - R⌉).toNat : ℝ) = ((max (⌊c + R⌋ + 1 - ⌈c - R⌉) 0 : ℤ) : ℝ) := by
    rw [← Int.toNat_eq_max]
    norm_cast
  rw [this]
  push_cast
  exact max_le (by linarith) (by linarith)

/-- The constant `C_Γ = (2‖b₀*‖ + 1)(2‖b₁*‖ + 1)` in the counting bound
`#(Γ ∩ closedBall x r) ≤ C_Γ (1 + r)²`. -/
noncomputable def countingConst : ℝ := (2 * ‖Γ.dual.b₀‖ + 1) * (2 * ‖Γ.dual.b₁‖ + 1)

/-- The counting constant is positive. -/
theorem countingConst_pos : 0 < Γ.countingConst := by
  unfold countingConst
  positivity

/-- The lattice points in a closed disc lie in the image of an explicit box of indices. -/
theorem inter_closedBall_subset (x : Plane) (r : ℝ) :
    (Γ.points : Set Plane) ∩ closedBall x r ⊆ Γ.point ''
      ↑(Finset.Icc ⌈⟪x, Γ.dual.b₀⟫ - ‖Γ.dual.b₀‖ * r⌉ ⌊⟪x, Γ.dual.b₀⟫ + ‖Γ.dual.b₀‖ * r⌋ ×ˢ
        Finset.Icc ⌈⟪x, Γ.dual.b₁⟫ - ‖Γ.dual.b₁‖ * r⌉ ⌊⟪x, Γ.dual.b₁⟫ + ‖Γ.dual.b₁‖ * r⌋) := by
  rintro v ⟨hv, hvx⟩
  obtain ⟨p, rfl⟩ := Γ.mem_points.mp hv
  refine ⟨p, ?_, rfl⟩
  have hd : ‖Γ.point p - x‖ ≤ r := by rwa [← dist_eq_norm]
  have key : ∀ k : Plane, |⟪Γ.point p, k⟫ - ⟪x, k⟫| ≤ ‖k‖ * r := fun k ↦ by
    rw [← inner_sub_left, mul_comm]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  have k₀ := abs_le.mp (key Γ.dual.b₀)
  have k₁ := abs_le.mp (key Γ.dual.b₁)
  simp only [inner_point_dual_b₀, inner_point_dual_b₁] at k₀ k₁
  simp only [Finset.coe_product, Finset.coe_Icc, mem_prod, mem_Icc]
  refine ⟨⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩, Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩ <;>
    linarith [k₀.1, k₀.2, k₁.1, k₁.2]

/-- The lattice points in a bounded set form a finite set. -/
theorem finite_inter_of_isBounded {s : Set Plane} (hs : Bornology.IsBounded s) :
    ((Γ.points : Set Plane) ∩ s).Finite := by
  rw [inter_comm]
  exact ZSpan.setFinite_inter Γ.basis hs

/-- **Counting lattice points.** `#(Γ ∩ closedBall x r) ≤ C_Γ (1 + r)²` with the explicit
constant `C_Γ = (2‖b₀*‖ + 1)(2‖b₁*‖ + 1)`. -/
theorem ncard_inter_closedBall_le (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    (((Γ.points : Set Plane) ∩ closedBall x r).ncard : ℝ) ≤ Γ.countingConst * (1 + r) ^ 2 := by
  classical
  set I₀ := Finset.Icc ⌈⟪x, Γ.dual.b₀⟫ - ‖Γ.dual.b₀‖ * r⌉ ⌊⟪x, Γ.dual.b₀⟫ + ‖Γ.dual.b₀‖ * r⌋
  set I₁ := Finset.Icc ⌈⟪x, Γ.dual.b₁⟫ - ‖Γ.dual.b₁‖ * r⌉ ⌊⟪x, Γ.dual.b₁⟫ + ‖Γ.dual.b₁‖ * r⌋
  have hsub := Γ.inter_closedBall_subset x r
  have h₁ : ((Γ.points : Set Plane) ∩ closedBall x r).ncard ≤ I₀.card * I₁.card := by
    calc ((Γ.points : Set Plane) ∩ closedBall x r).ncard
        ≤ (Γ.point '' ↑(I₀ ×ˢ I₁)).ncard := ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
      _ ≤ (↑(I₀ ×ˢ I₁) : Set (ℤ × ℤ)).ncard := ncard_image_le (Finset.finite_toSet _)
      _ = I₀.card * I₁.card := by rw [ncard_coe_finset, Finset.card_product]
  have c₀ := card_Icc_ceil_floor_le ⟪x, Γ.dual.b₀⟫ (mul_nonneg (norm_nonneg Γ.dual.b₀) hr)
  have c₁ := card_Icc_ceil_floor_le ⟪x, Γ.dual.b₁⟫ (mul_nonneg (norm_nonneg Γ.dual.b₁) hr)
  have e₀ : 2 * (‖Γ.dual.b₀‖ * r) + 1 ≤ (2 * ‖Γ.dual.b₀‖ + 1) * (1 + r) := by
    nlinarith [norm_nonneg Γ.dual.b₀]
  have e₁ : 2 * (‖Γ.dual.b₁‖ * r) + 1 ≤ (2 * ‖Γ.dual.b₁‖ + 1) * (1 + r) := by
    nlinarith [norm_nonneg Γ.dual.b₁]
  calc (((Γ.points : Set Plane) ∩ closedBall x r).ncard : ℝ)
      ≤ (I₀.card : ℝ) * I₁.card := by exact_mod_cast h₁
    _ ≤ ((2 * ‖Γ.dual.b₀‖ + 1) * (1 + r)) * ((2 * ‖Γ.dual.b₁‖ + 1) * (1 + r)) :=
        mul_le_mul (c₀.trans e₀) (c₁.trans e₁) (Nat.cast_nonneg _) (by positivity)
    _ = Γ.countingConst * (1 + r) ^ 2 := by unfold countingConst; ring

/-- The points of a lattice form a locally finite set. -/
theorem isLocallyFinite_points : IsLocallyFinite (Γ.points : Set Plane) :=
  fun _ hK ↦ Γ.finite_inter_of_isBounded hK.isBounded

/-- The points of a lattice have bounded density. -/
theorem hasBoundedDensity_points : HasBoundedDensity (Γ.points : Set Plane) := by
  refine ⟨4 * Γ.countingConst / Real.pi, fun R hR ↦ ?_⟩
  have hfin := Γ.finite_inter_of_isBounded (isBounded_closedBall (x := 0) (r := R))
  calc (((Γ.points : Set Plane) ∩ ball 0 R).ncard : ℝ)
      ≤ ((Γ.points : Set Plane) ∩ closedBall 0 R).ncard := by
        exact_mod_cast ncard_le_ncard (inter_subset_inter_right _ ball_subset_closedBall) hfin
    _ ≤ Γ.countingConst * (1 + R) ^ 2 := Γ.ncard_inter_closedBall_le 0 (by linarith)
    _ ≤ Γ.countingConst * (4 * R ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) Γ.countingConst_pos.le
    _ = 4 * Γ.countingConst / Real.pi * (Real.pi * R ^ 2) := by
        field_simp

/-! ### Lattice sums of decaying functions -/

/-- The lattice sum `∑_{v ∈ Γ} (1 + ‖v‖)^(-s)` converges for `s > 2`. -/
theorem summable_one_add_norm_rpow_neg {s : ℝ} (hs : 2 < s) :
    Summable fun v : Γ.points ↦ (1 + ‖(v : Plane)‖) ^ (-s) := by
  have h := ZLattice.summable_norm_rpow (L := Γ.points) (-s)
    (by rw [finrank_points]; push_cast; linarith)
  refine Summable.of_norm_bounded_eventually h ?_
  filter_upwards [eventually_cofinite_ne 0] with v hv
  have hv' : 0 < ‖(v : Plane)‖ := norm_pos_iff.mpr (by simpa using hv)
  rw [Real.norm_of_nonneg (by positivity), ← Submodule.norm_coe]
  exact Real.rpow_le_rpow_of_nonpos hv' (by linarith) (by linarith)

/-- Translating by a vector of norm at most `R` changes `(1 + ‖y‖)^(-s)` by at most the factor
`(1 + R)^s`. -/
theorem one_add_norm_add_rpow_neg_le {s : ℝ} (hs : 0 ≤ s) {x : Plane} {R : ℝ} (hx : ‖x‖ ≤ R)
    (y : Plane) : (1 + ‖x + y‖) ^ (-s) ≤ (1 + R) ^ s * (1 + ‖y‖) ^ (-s) := by
  have hR : 0 ≤ R := (norm_nonneg x).trans hx
  have h : 1 + ‖y‖ ≤ (1 + ‖x + y‖) * (1 + R) := by
    have : ‖y‖ ≤ ‖x + y‖ + ‖x‖ := by
      simpa using norm_sub_le (x + y) x
    nlinarith [norm_nonneg (x + y)]
  have h₁ : (1 + ‖y‖) ^ s ≤ (1 + ‖x + y‖) ^ s * (1 + R) ^ s := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h hs
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), ← div_eq_mul_inv]
  rw [inv_le_iff_one_le_mul₀' (by positivity), ← mul_div_assoc, le_div_iff₀ (by positivity),
    one_mul]
  exact h₁

variable {E : Type*} [NormedAddCommGroup E]

/-- A decay bound `‖f y‖ ≤ A (1 + ‖y‖)^(-s)` gives a uniform bound for the terms of the lattice
sum over a disc. -/
theorem norm_comp_add_le {f : Plane → E} {A s : ℝ} (hs : 0 ≤ s)
    (hf : ∀ y, ‖f y‖ ≤ A * (1 + ‖y‖) ^ (-s)) {R : ℝ} {x : Plane} (hx : ‖x‖ ≤ R) (v : Plane) :
    ‖f (x + v)‖ ≤ A * (1 + R) ^ s * (1 + ‖v‖) ^ (-s) := by
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hf 0)
    simpa using this
  rw [mul_assoc]
  exact (hf _).trans (mul_le_mul_of_nonneg_left (one_add_norm_add_rpow_neg_le hs hx v) hA)

/-- **Lattice sums of decaying functions converge.** If `‖f y‖ ≤ A (1 + ‖y‖)^(-s)` with `s > 2`,
then `∑_{v ∈ Γ} f (x + v)` converges absolutely. -/
theorem summable_norm_comp_add {f : Plane → E} {A s : ℝ} (hs : 2 < s)
    (hf : ∀ y, ‖f y‖ ≤ A * (1 + ‖y‖) ^ (-s)) (x : Plane) :
    Summable fun v : Γ.points ↦ ‖f (x + v)‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun v ↦ norm_comp_add_le (by linarith) hf le_rfl v)
    ((Γ.summable_one_add_norm_rpow_neg hs).mul_left _)

/-- **Lattice sums of decaying functions converge.** If `‖f y‖ ≤ A (1 + ‖y‖)^(-s)` with `s > 2`,
then `∑_{v ∈ Γ} f (x + v)` converges. -/
theorem summable_comp_add [CompleteSpace E] {f : Plane → E} {A s : ℝ} (hs : 2 < s)
    (hf : ∀ y, ‖f y‖ ≤ A * (1 + ‖y‖) ^ (-s)) (x : Plane) :
    Summable fun v : Γ.points ↦ f (x + v) :=
  (Γ.summable_norm_comp_add hs hf x).of_norm

/-- The lattice sum `∑_{v ∈ Γ} f (x + v)` converges uniformly on discs. -/
theorem hasSumUniformlyOn_comp_add [CompleteSpace E] {f : Plane → E} {A s : ℝ} (hs : 2 < s)
    (hf : ∀ y, ‖f y‖ ≤ A * (1 + ‖y‖) ^ (-s)) (R : ℝ) :
    HasSumUniformlyOn (fun (v : Γ.points) x ↦ f (x + v)) (fun x ↦ ∑' v : Γ.points, f (x + v))
      (closedBall 0 R) :=
  hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr <| tendstoUniformlyOn_tsum
    ((Γ.summable_one_add_norm_rpow_neg hs).mul_left (A * (1 + R) ^ s))
    fun v x hx ↦ norm_comp_add_le (by linarith) hf (by simpa using hx) v

/-- The lattice sum `∑_{v ∈ Γ} f (x + v)` converges locally uniformly. -/
theorem hasSumLocallyUniformly_comp_add [CompleteSpace E] {f : Plane → E} {A s : ℝ} (hs : 2 < s)
    (hf : ∀ y, ‖f y‖ ≤ A * (1 + ‖y‖) ^ (-s)) :
    HasSumLocallyUniformly (fun (v : Γ.points) x ↦ f (x + v))
      (fun x ↦ ∑' v : Γ.points, f (x + v)) := by
  refine hasSumLocallyUniformly_of_forall_compact fun K hK ↦ ?_
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  exact (Γ.hasSumUniformlyOn_comp_add hs hf R).mono hR

/-- The lattice sum of a continuous decaying function is continuous. -/
theorem continuous_tsum_comp_add [CompleteSpace E] {f : Plane → E} (hc : Continuous f) {A s : ℝ}
    (hs : 2 < s)
    (hf : ∀ y, ‖f y‖ ≤ A * (1 + ‖y‖) ^ (-s)) :
    Continuous fun x ↦ ∑' v : Γ.points, f (x + v) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  have hU := (Γ.hasSumUniformlyOn_comp_add hs hf (‖x‖ + 1)).tendstoUniformlyOn
  refine (hU.continuousOn (Frequently.of_forall fun t ↦ ?_)).continuousAt
    (closedBall_mem_nhds_of_mem (by simp))
  exact continuousOn_finsetSum _ fun v _ ↦
    (hc.comp (continuous_id.add continuous_const)).continuousOn

/-- The lattice sum `x ↦ ∑_{v ∈ Γ} f (x + v)` is `Γ`-periodic. -/
theorem tsum_comp_add_add {f : Plane → E} (x : Plane) {w : Plane} (hw : w ∈ Γ.points) :
    ∑' v : Γ.points, f (x + w + v) = ∑' v : Γ.points, f (x + v) := by
  let e : Γ.points ≃ Γ.points := Equiv.addLeft ⟨w, hw⟩
  rw [← e.tsum_eq (fun v : Γ.points ↦ f (x + v))]
  simp [e, add_assoc]

/-! ### Scaling -/

/-- The scaled lattice `s Γ`, with basis `s b₀, s b₁`. -/
def scale (s : ℝ) (hs : s ≠ 0) : PlaneLattice where
  b₀ := s • Γ.b₀
  b₁ := s • Γ.b₁
  det_ne_zero' := by
    have h := Γ.det_ne_zero
    simp only [det] at h
    simp only [PiLp.smul_apply, smul_eq_mul]
    have : s * Γ.b₀ 0 * (s * Γ.b₁ 1) - s * Γ.b₀ 1 * (s * Γ.b₁ 0) =
      s ^ 2 * (Γ.b₀ 0 * Γ.b₁ 1 - Γ.b₀ 1 * Γ.b₁ 0) := by ring
    rw [this]
    exact mul_ne_zero (pow_ne_zero 2 hs) h

variable {s : ℝ} (hs : s ≠ 0)

/-- The first basis vector of `s Γ` is `s b₀`. -/
@[simp]
theorem scale_b₀ : (Γ.scale s hs).b₀ = s • Γ.b₀ := rfl

/-- The second basis vector of `s Γ` is `s b₁`. -/
@[simp]
theorem scale_b₁ : (Γ.scale s hs).b₁ = s • Γ.b₁ := rfl

/-- The determinant of `s Γ` is `s² det Γ`. -/
@[simp]
theorem det_scale : (Γ.scale s hs).det = s ^ 2 * Γ.det := by
  simp only [det, scale_b₀, scale_b₁, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The covolume of `s Γ` is `s² covolume Γ`. -/
@[simp]
theorem covolume_scale : (Γ.scale s hs).covolume = s ^ 2 * Γ.covolume := by
  simp [covolume, abs_mul]

/-- The points of `s Γ` are the scaled points of `Γ`. -/
theorem point_scale (p : ℤ × ℤ) : (Γ.scale s hs).point p = s • Γ.point p := by
  simp only [point, scale_b₀, scale_b₁, smul_add, smul_comm s]

/-- A vector `v` lies in `s Γ` iff `s⁻¹ v` lies in `Γ`. -/
theorem mem_scale_points {v : Plane} : v ∈ (Γ.scale s hs).points ↔ s⁻¹ • v ∈ Γ.points := by
  simp only [mem_points, point_scale]
  refine exists_congr fun p ↦ ?_
  constructor
  · rintro rfl
    rw [inv_smul_smul₀ hs]
  · intro h
    rw [h, smul_inv_smul₀ hs]

/-- The point set of `s Γ` is `s` times the point set of `Γ`. -/
theorem coe_scale_points :
    ((Γ.scale s hs).points : Set Plane) = s • (Γ.points : Set Plane) := by
  ext v
  rw [SetLike.mem_coe, mem_scale_points, ← SetLike.mem_coe, mem_smul_set_iff_inv_smul_mem₀ hs]

/-- The cell of `s Γ` is `s` times the cell of `Γ`. -/
theorem scale_cell : (Γ.scale s hs).cell = s • Γ.cell := by
  ext x
  simp only [cell, scale_b₀, scale_b₁, mem_ofPred_eq, mem_smul_set]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a • Γ.b₀ + b • Γ.b₁, ⟨a, ha, b, hb, rfl⟩, by simp only [smul_add, smul_comm s]⟩
  · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨a, ha, b, hb, by simp only [smul_add, smul_comm s]⟩

/-- The dual of `s Γ` is `s⁻¹ Γ*`. -/
theorem dual_scale : (Γ.scale s hs).dual = Γ.dual.scale s⁻¹ (inv_ne_zero hs) := by
  have h := Γ.det_ne_zero
  ext i <;> fin_cases i <;> simp [dual_b₀, dual_b₁] <;> field_simp

end PlaneLattice

/-! ### Rotations of the plane -/

/-- The rotation of the plane by the angle `θ`. -/
noncomputable def planeRotation (θ : ℝ) : Plane ≃ₗᵢ[ℝ] Plane where
  toFun x := !₂[Real.cos θ * x 0 - Real.sin θ * x 1, Real.sin θ * x 0 + Real.cos θ * x 1]
  invFun x := !₂[Real.cos θ * x 0 + Real.sin θ * x 1, -Real.sin θ * x 0 + Real.cos θ * x 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring
  left_inv x := by
    ext i; fin_cases i
    · simp; linear_combination x 0 * Real.sin_sq_add_cos_sq θ
    · simp; linear_combination x 1 * Real.sin_sq_add_cos_sq θ
  right_inv x := by
    ext i; fin_cases i
    · simp; linear_combination x 0 * Real.sin_sq_add_cos_sq θ
    · simp; linear_combination x 1 * Real.sin_sq_add_cos_sq θ
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_plane, norm_sq_plane]
    simp
    linear_combination (x 0 ^ 2 + x 1 ^ 2) * Real.sin_sq_add_cos_sq θ

/-- The first coordinate of the rotated vector. -/
@[simp]
theorem planeRotation_apply_zero (θ : ℝ) (x : Plane) :
    planeRotation θ x 0 = Real.cos θ * x 0 - Real.sin θ * x 1 := by
  simp [planeRotation]

/-- The second coordinate of the rotated vector. -/
@[simp]
theorem planeRotation_apply_one (θ : ℝ) (x : Plane) :
    planeRotation θ x 1 = Real.sin θ * x 0 + Real.cos θ * x 1 := by
  simp [planeRotation]

/-! ### The triangular lattice -/

/-- The lattice spacing `ℓ` is positive. -/
theorem latticeSpacing_pos : 0 < latticeSpacing :=
  Real.sqrt_pos.mpr (div_pos two_pos (Real.sqrt_pos.mpr three_pos))

/-- The lattice spacing satisfies `ℓ² = 2/√3`. -/
theorem latticeSpacing_sq : latticeSpacing ^ 2 = 2 / √3 :=
  Real.sq_sqrt (div_nonneg zero_le_two (Real.sqrt_nonneg _))

namespace PlaneLattice

/-- **The triangular lattice** `Λ = ℓ [ℤ (1, 0) + ℤ (1/2, √3/2)]` of covolume one, with
`ℓ = latticeSpacing`. -/
noncomputable def triangular : PlaneLattice where
  b₀ := latticeSpacing • !₂[1, 0]
  b₁ := latticeSpacing • !₂[1 / 2, √3 / 2]
  det_ne_zero' := by
    have := latticeSpacing_pos
    simp
    positivity

/-- The first basis vector of the triangular lattice is `ℓ (1, 0)`. -/
theorem triangular_b₀ : triangular.b₀ = latticeSpacing • !₂[1, 0] := rfl

/-- The second basis vector of the triangular lattice is `ℓ (1/2, √3/2)`. -/
theorem triangular_b₁ : triangular.b₁ = latticeSpacing • !₂[1 / 2, √3 / 2] := rfl

/-- The triangular lattice has determinant one. -/
@[simp]
theorem det_triangular : triangular.det = 1 := by
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : 0 < √3 := Real.sqrt_pos.mpr three_pos
  simp only [det, triangular_b₀, triangular_b₁, PiLp.smul_apply, smul_eq_mul]
  simp
  have : latticeSpacing * (latticeSpacing * (√3 / 2)) = latticeSpacing ^ 2 * √3 / 2 := by ring
  rw [this, latticeSpacing_sq]
  field_simp

/-- The triangular lattice has covolume one. -/
@[simp]
theorem covolume_triangular : triangular.covolume = 1 := by
  simp [covolume]

/-- The points of the triangular lattice are `ℓ (a + b/2, b√3/2)`. -/
theorem triangular_point (a b : ℤ) :
    triangular.point (a, b) = latticeSpacing • !₂[(a : ℝ) + b / 2, b * √3 / 2] := by
  ext i; fin_cases i <;> simp [point, triangular_b₀, triangular_b₁] <;> ring

/-- The points of `PlaneLattice.triangular` form the triangular lattice `triangularLattice` of
the statement. -/
theorem coe_triangular_points : (triangular.points : Set Plane) = triangularLattice := by
  ext v
  simp only [SetLike.mem_coe, mem_points, Prod.exists, triangular_point, triangularLattice,
    mem_ofPred_eq, eq_comm]

/-- The cell of `PlaneLattice.triangular` is the fundamental cell `fundamentalCell` of the
statement. -/
theorem triangular_cell : triangular.cell = fundamentalCell := by
  ext x
  simp only [cell, fundamentalCell, mem_ofPred_eq]
  refine exists_congr fun s ↦ and_congr_right fun _ ↦ exists_congr fun t ↦
    and_congr_right fun _ ↦ ?_
  have : s • triangular.b₀ + t • triangular.b₁ = latticeSpacing • !₂[s + t / 2, t * √3 / 2] := by
    ext i; fin_cases i <;> simp [triangular_b₀, triangular_b₁] <;> ring
  rw [this]

/-- `|ℓ (a + b/2, b√3/2)|² = ℓ² (a² + ab + b²)`. -/
theorem norm_sq_triangular_point (a b : ℤ) :
    ‖triangular.point (a, b)‖ ^ 2 = latticeSpacing ^ 2 * (a ^ 2 + a * b + b ^ 2) := by
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [norm_sq_plane, triangular_point]
  simp
  linear_combination (latticeSpacing ^ 2 * b ^ 2 / 4) * h3

/-- The first dual basis vector of the triangular lattice is `ℓ (√3/2, -1/2)`. -/
theorem triangular_dual_b₀ : triangular.dual.b₀ = latticeSpacing • !₂[√3 / 2, -1 / 2] := by
  ext i; fin_cases i
  · simp [dual_b₀, triangular_b₁]
  · simp [dual_b₀, triangular_b₁]
    ring

/-- The second dual basis vector of the triangular lattice is `ℓ (0, 1)`. -/
theorem triangular_dual_b₁ : triangular.dual.b₁ = latticeSpacing • !₂[0, 1] := by
  ext i; fin_cases i <;> simp [dual_b₁, triangular_b₀]

/-- The rotation by `π/6` maps `ℓ (a (1, 0) + b (1/2, √3/2))` to `a b₀* + (a + b) b₁*`. -/
theorem planeRotation_triangular_point (a b : ℤ) :
    planeRotation (Real.pi / 6) (triangular.point (a, b)) = triangular.dual.point (a, a + b) := by
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i; fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, planeRotation_apply_zero, planeRotation_apply_one,
      point, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, triangular_b₀, triangular_b₁,
      triangular_dual_b₀, triangular_dual_b₁, Real.cos_pi_div_six, Real.sin_pi_div_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_add]
  · ring
  · linear_combination (latticeSpacing * b / 4) * h3

/-- **The dual of the triangular lattice is its rotation by `π/6`.** -/
theorem coe_triangular_dual_points :
    (triangular.dual.points : Set Plane) = planeRotation (Real.pi / 6) '' triangularLattice := by
  rw [← coe_triangular_points]
  ext k
  constructor
  · intro hk
    obtain ⟨⟨m, n⟩, rfl⟩ := triangular.dual.mem_points.mp hk
    refine ⟨triangular.point (m, n - m), triangular.point_mem_points _, ?_⟩
    rw [planeRotation_triangular_point]
    simp
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := triangular.mem_points.mp hv
    rw [planeRotation_triangular_point]
    exact triangular.dual.point_mem_points _

/-- `|a b₀* + b b₁*|² = ℓ² (a² - ab + b²)` for the dual of the triangular lattice. -/
theorem norm_sq_triangular_dual_point (a b : ℤ) :
    ‖triangular.dual.point (a, b)‖ ^ 2 = latticeSpacing ^ 2 * (a ^ 2 - a * b + b ^ 2) := by
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [norm_sq_plane]
  simp [point, triangular_dual_b₀, triangular_dual_b₁]
  linear_combination (latticeSpacing ^ 2 * a ^ 2 / 4) * h3

end PlaneLattice

end TriangularLattice
