/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Rigidity.Directions
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The retained set, nearest neighbors and the three-shell test

The local setting of Section 5 of the manuscript. A set `X` of points of the plane (the retained
set) satisfies `IsRetainedSet ε X` if `0 < ε ≤ ε_geo = 10⁻⁸` and every pair of distinct points
`p, p' ∈ X` with `|p - p'| ≤ ρ₀ ℓ`, `ρ₀ = 2.1`, satisfies `dist(|p - p'|/ℓ, {1, √3, 2}) ≤ ε`
(no bad pairs, Definition 5.1). Periodicity and counting per period play no role here.

## Main definitions

* `TriangularLattice.rho0`, `TriangularLattice.epsGeo`: the constants `ρ₀ = 2.1`, `ε_geo = 10⁻⁸`.
* `TriangularLattice.shellDist r`: the distance from `r` to `{1, √3, 2}`.
* `TriangularLattice.IsRetainedSet ε X`: the hypotheses of the local setting.
* `TriangularLattice.nbrs ε X p`: the nearest neighbors `q ∈ X`, `|q - p|/ℓ ∈ [1 - ε, 1 + ε]`.

## Main results

* `TriangularLattice.IsRetainedSet.mul_le_norm_sub`,
  `TriangularLattice.IsRetainedSet.one_lt_norm_sub`: separation, `|p - p'| ≥ ℓ (1 - ε) > 1`
  (the last assertion of Lemma 5.2, `lem:badcounts`).
* `TriangularLattice.IsRetainedSet.le_norm_sub_of_not_mem_nbrs`: retained points which are not
  nearest neighbors are at distance at least `(√3 - ε) ℓ`.
* `TriangularLattice.IsRetainedSet.threeShell`: the three-shell test (first part of Lemma 5.3,
  `lem:threeshell`): for nearest neighbors `q ≠ q'` of `p`, `|q - q'|/ℓ` is within `ε` of `1`, `√3`
  or `2`, and correspondingly `∠ q p q'` is within `8ε` of `π/3` or `2π/3`, or at least
  `π - 4√ε`.
* `TriangularLattice.IsRetainedSet.abs_angle_sub_pi_div_three_le`: the gap estimate (5.gap).
-/

@[expose] public section

open Real InnerProductGeometry
open scoped RealInnerProductSpace

namespace TriangularLattice

/-! ### Constants -/

/-- The range `ρ₀ = 2.1` (in units of `ℓ`) of the bad-pair test. -/
noncomputable def rho0 : ℝ := 21 / 10

/-- The geometric threshold `ε_geo = 10⁻⁸` of (5.epsgeo). -/
noncomputable def epsGeo : ℝ := 1 / 10 ^ 8

/-- The distance `dist(r, {1, √3, 2})` from `r` to the three shells. -/
noncomputable def shellDist (r : ℝ) : ℝ :=
  min |r - 1| (min |r - √3| |r - 2|)

theorem shellDist_le_iff {r ε : ℝ} :
    shellDist r ≤ ε ↔ |r - 1| ≤ ε ∨ |r - √3| ≤ ε ∨ |r - 2| ≤ ε := by
  simp [shellDist, min_le_iff]

theorem shellDist_nonneg (r : ℝ) : 0 ≤ shellDist r := by
  simp [shellDist]

theorem sqrt_three_lt : √3 < 1.7321 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

theorem lt_sqrt_three : 1.732 < √3 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

theorem latticeSpacing_pos : 0 < latticeSpacing := by
  unfold latticeSpacing
  positivity

theorem latticeSpacing_sq : latticeSpacing ^ 2 = 2 / √3 := by
  unfold latticeSpacing
  rw [Real.sq_sqrt (by positivity)]

theorem latticeSpacing_lt : latticeSpacing < 1.0746 := by
  unfold latticeSpacing
  rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ (by positivity)]
  nlinarith [lt_sqrt_three]

theorem lt_latticeSpacing : 1.0745 < latticeSpacing := by
  unfold latticeSpacing
  rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ (by positivity)]
  nlinarith [sqrt_three_lt]

/-! ### The retained set -/

/-- **The local setting of Section 5.** The tolerance satisfies `0 < ε ≤ ε_geo`, and any two
distinct points `p, p' ∈ X` with `|p - p'| ≤ ρ₀ ℓ` satisfy `dist(|p - p'|/ℓ, {1, √3, 2}) ≤ ε`,
that is, `X` contains no bad pair (Definition 5.1). -/
structure IsRetainedSet (ε : ℝ) (X : Set Plane) : Prop where
  pos : 0 < ε
  le_epsGeo : ε ≤ epsGeo
  shellDist_le : ∀ ⦃p⦄, p ∈ X → ∀ ⦃p'⦄, p' ∈ X → p ≠ p' →
    ‖p - p'‖ ≤ rho0 * latticeSpacing → shellDist (‖p - p'‖ / latticeSpacing) ≤ ε

variable {ε : ℝ} {X : Set Plane} {p q q' : Plane}

namespace IsRetainedSet

theorem le_small (hX : IsRetainedSet ε X) : ε ≤ 1 / 10 ^ 8 :=
  hX.le_epsGeo

theorem sqrt_le (hX : IsRetainedSet ε X) : √ε ≤ 1 / 10 ^ 4 := by
  rw [Real.sqrt_le_left (by norm_num)]
  have := hX.le_small
  norm_num at this ⊢
  linarith

theorem eps_le_sqrt (hX : IsRetainedSet ε X) : ε ≤ √ε := by
  have h1 : ε ≤ 1 := by linarith [hX.le_small]
  calc ε = √ε * √ε := (Real.mul_self_sqrt hX.pos.le).symm
    _ ≤ √ε * 1 := by
        gcongr
        rw [Real.sqrt_le_one]
        exact h1
    _ = √ε := mul_one _

theorem eps_le_sqrt_div (hX : IsRetainedSet ε X) : ε ≤ √ε / 10 ^ 4 := by
  have h := hX.sqrt_le
  calc ε = √ε * √ε := (Real.mul_self_sqrt hX.pos.le).symm
    _ ≤ √ε * (1 / 10 ^ 4) := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = √ε / 10 ^ 4 := by ring

theorem one_lt_mul (hX : IsRetainedSet ε X) : 1 < latticeSpacing * (1 - ε) := by
  have := hX.le_small
  nlinarith [lt_latticeSpacing]

/-- **Separation.** Distinct retained points are at distance at least `ℓ (1 - ε)`. -/
theorem mul_le_norm_sub (hX : IsRetainedSet ε X) (hp : p ∈ X) (hq : q ∈ X) (hpq : p ≠ q) :
    latticeSpacing * (1 - ε) ≤ ‖p - q‖ := by
  by_contra hlt
  push Not at hlt
  have hℓ := latticeSpacing_pos
  have hε := hX.le_small
  have hle : ‖p - q‖ ≤ rho0 * latticeSpacing := by
    unfold rho0
    nlinarith [hX.pos]
  have hr : ‖p - q‖ / latticeSpacing < 1 - ε := by
    rw [div_lt_iff₀ hℓ]
    linarith
  rcases shellDist_le_iff.1 (hX.shellDist_le hp hq hpq hle) with h | h | h <;>
    rw [abs_le] at h <;> nlinarith [lt_sqrt_three]

/-- **Separation.** Distinct retained points are more than `1` apart. -/
theorem one_lt_norm_sub (hX : IsRetainedSet ε X) (hp : p ∈ X) (hq : q ∈ X) (hpq : p ≠ q) :
    1 < ‖p - q‖ :=
  hX.one_lt_mul.trans_le (hX.mul_le_norm_sub hp hq hpq)

end IsRetainedSet

/-! ### Nearest neighbors -/

/-- The nearest neighbors of `p` in `X`: the points `q ∈ X` with `|q - p|/ℓ ∈ [1 - ε, 1 + ε]`.
For `p ∈ X`, the pairs `{p, q}` with `q ∈ nbrs ε X p` are the nearest edges. -/
def nbrs (ε : ℝ) (X : Set Plane) (p : Plane) : Set Plane :=
  {q | q ∈ X ∧ |‖q - p‖ / latticeSpacing - 1| ≤ ε}

theorem mem_nbrs : q ∈ nbrs ε X p ↔ q ∈ X ∧ |‖q - p‖ / latticeSpacing - 1| ≤ ε :=
  Iff.rfl

theorem nbrs_subset : nbrs ε X p ⊆ X :=
  fun _ hq => hq.1

theorem abs_sub_one_le_of_mem_nbrs (hq : q ∈ nbrs ε X p) :
    |‖q - p‖ / latticeSpacing - 1| ≤ ε :=
  hq.2

/-- The nearest-neighbor relation is symmetric. -/
theorem mem_nbrs_comm (hp : p ∈ X) (hq : q ∈ nbrs ε X p) : p ∈ nbrs ε X q :=
  ⟨hp, by rw [norm_sub_rev]; exact hq.2⟩

theorem norm_sub_mem_Icc_of_mem_nbrs (hq : q ∈ nbrs ε X p) :
    latticeSpacing * (1 - ε) ≤ ‖q - p‖ ∧ ‖q - p‖ ≤ latticeSpacing * (1 + ε) := by
  have hℓ := latticeSpacing_pos
  have h := abs_le.1 hq.2
  constructor
  · have : 1 - ε ≤ ‖q - p‖ / latticeSpacing := by linarith
    rwa [le_div_iff₀ hℓ, mul_comm] at this
  · have : ‖q - p‖ / latticeSpacing ≤ 1 + ε := by linarith
    rwa [div_le_iff₀ hℓ, mul_comm] at this

namespace IsRetainedSet

theorem sub_ne_zero_of_mem_nbrs (hX : IsRetainedSet ε X) (hq : q ∈ nbrs ε X p) : q - p ≠ 0 := by
  intro h
  have := (norm_sub_mem_Icc_of_mem_nbrs hq).1
  rw [h, norm_zero] at this
  have := hX.one_lt_mul
  linarith

theorem ne_of_mem_nbrs (hX : IsRetainedSet ε X) (hq : q ∈ nbrs ε X p) : q ≠ p :=
  fun h => hX.sub_ne_zero_of_mem_nbrs hq (sub_eq_zero.2 h)

/-- Retained points which are not nearest neighbors are at distance at least `(√3 - ε) ℓ`. -/
theorem le_norm_sub_of_not_mem_nbrs (hX : IsRetainedSet ε X) (hp : p ∈ X) (hq : q ∈ X)
    (hpq : q ≠ p) (hnq : q ∉ nbrs ε X p) : (√3 - ε) * latticeSpacing ≤ ‖q - p‖ := by
  have hℓ := latticeSpacing_pos
  have hε := hX.le_small
  have h3 := sqrt_three_lt
  rw [← le_div_iff₀ hℓ]
  by_cases hle : ‖q - p‖ ≤ rho0 * latticeSpacing
  · rcases shellDist_le_iff.1 (hX.shellDist_le hq hp hpq hle) with h | h | h
    · exact absurd ⟨hq, h⟩ hnq
    · linarith [(abs_le.1 h).1]
    · linarith [(abs_le.1 h).1]
  · push Not at hle
    have : rho0 < ‖q - p‖ / latticeSpacing := by rwa [lt_div_iff₀ hℓ]
    unfold rho0 at this
    linarith [hX.pos]

end IsRetainedSet

/-! ### The law of cosines in normalized form -/

/-- The law of cosines: `cos ∠(q - p, q' - p) = (a² + b² - c²)/(2ab)` with `a = |q - p|/ℓ`,
`b = |q' - p|/ℓ`, `c = |q - q'|/ℓ`. -/
theorem cos_angle_eq_cosLaw (hq : q - p ≠ 0) (hq' : q' - p ≠ 0) :
    Real.cos (angle (q - p) (q' - p)) =
      ((‖q - p‖ / latticeSpacing) ^ 2 + (‖q' - p‖ / latticeSpacing) ^ 2 -
        (‖q - q'‖ / latticeSpacing) ^ 2) /
      (2 * (‖q - p‖ / latticeSpacing) * (‖q' - p‖ / latticeSpacing)) := by
  have hℓ := latticeSpacing_pos.ne'
  have h1 : ‖q - p‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have h2 : ‖q' - p‖ ≠ 0 := norm_ne_zero_iff.2 hq'
  have key : ‖q - q'‖ ^ 2 = ‖q - p‖ ^ 2 - 2 * ⟪q - p, q' - p⟫ + ‖q' - p‖ ^ 2 := by
    rw [show q - q' = (q - p) - (q' - p) by abel, norm_sub_sq_real]
  rw [cos_angle, div_pow, div_pow, div_pow, key]
  field_simp
  ring

private theorem two_mul_mul_ge {a b ε : ℝ} (hε : ε ≤ 1 / 10 ^ 8) (ha : |a - 1| ≤ ε)
    (hb : |b - 1| ≤ ε) : 1.99 ≤ 2 * a * b := by
  rw [abs_le] at ha hb
  nlinarith

/-- Normalized law of cosines near the first shell: if `a, b, c` are within `ε` of `1`, then
`(a² + b² - c²)/(2ab)` is within `1.01 (|a - 1| + |b - 1| + |c - 1|)` of `1/2`. -/
theorem abs_cosLaw_sub_half_le {a b c ε : ℝ} (hε : ε ≤ 1 / 10 ^ 8) (ha : |a - 1| ≤ ε)
    (hb : |b - 1| ≤ ε) (hc : |c - 1| ≤ ε) :
    |(a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) - 1 / 2| ≤
      1.01 * (|a - 1| + |b - 1| + |c - 1|) := by
  have hab := two_mul_mul_ge hε ha hb
  have hN : |a ^ 2 + b ^ 2 - c ^ 2 - a * b| ≤ 1.99 * (1.01 * (|a - 1| + |b - 1| + |c - 1|)) := by
    have e : a ^ 2 + b ^ 2 - c ^ 2 - a * b =
        (a - 1) * (a - b + 1) + (b - 1) * b - (c - 1) * (c + 1) := by ring
    rw [e]
    have h1 : |a - b + 1| ≤ 1 + 2 * ε := by
      rw [abs_le] at ha hb ⊢; constructor <;> linarith
    have h2 : |b| ≤ 1 + ε := by
      rw [abs_le] at hb ⊢; constructor <;> linarith
    have h3 : |c + 1| ≤ 2 + ε := by
      rw [abs_le] at hc ⊢; constructor <;> linarith
    calc |(a - 1) * (a - b + 1) + (b - 1) * b - (c - 1) * (c + 1)|
        ≤ |a - 1| * |a - b + 1| + |b - 1| * |b| + |c - 1| * |c + 1| := by
          rw [← abs_mul, ← abs_mul, ← abs_mul]
          exact (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ |a - 1| * (1 + 2 * ε) + |b - 1| * (1 + ε) + |c - 1| * (2 + ε) := by
          gcongr
      _ ≤ 1.99 * (1.01 * (|a - 1| + |b - 1| + |c - 1|)) := by
          have := abs_nonneg (a - 1)
          have := abs_nonneg (b - 1)
          have := abs_nonneg (c - 1)
          have := abs_nonneg ε
          nlinarith
  have hpos : 0 < 2 * a * b := by linarith
  have ha0 : a ≠ 0 := by rintro rfl; simp at hpos
  have hb0 : b ≠ 0 := by rintro rfl; simp at hpos
  rw [show (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) - 1 / 2 =
      (a ^ 2 + b ^ 2 - c ^ 2 - a * b) / (2 * a * b) by field_simp,
    abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have : 0 ≤ 1.01 * (|a - 1| + |b - 1| + |c - 1|) := by positivity
  nlinarith

/-- Normalized law of cosines near the second shell. -/
theorem abs_cosLaw_add_half_le {a b c ε : ℝ} (hε : ε ≤ 1 / 10 ^ 8) (ha : |a - 1| ≤ ε)
    (hb : |b - 1| ≤ ε) (hc : |c - √3| ≤ ε) :
    |(a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) + 1 / 2| ≤ 5 * ε := by
  have hab := two_mul_mul_ge hε ha hb
  have hpos : 0 < 2 * a * b := by linarith
  have ha0 : a ≠ 0 := by rintro rfl; simp at hpos
  have hb0 : b ≠ 0 := by rintro rfl; simp at hpos
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs := sqrt_three_lt
  rw [show (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) + 1 / 2 =
      (a ^ 2 + b ^ 2 - c ^ 2 + a * b) / (2 * a * b) by field_simp,
    abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have e : a ^ 2 + b ^ 2 - c ^ 2 + a * b =
      (a - 1) * (a + 1) + (b - 1) * (b + 1) + (a - 1) * b + (b - 1) - (c - √3) * (c + √3) := by
    linear_combination (-1 : ℝ) * h3
  rw [abs_le] at ha hb hc
  have hε0 : 0 ≤ ε := by linarith
  have p1 : |(a - 1) * (a + 1)| ≤ ε * 2.01 := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 ha) (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _) hε0
  have p2 : |(b - 1) * (b + 1)| ≤ ε * 2.01 := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 hb) (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _) hε0
  have p3 : |(a - 1) * b| ≤ ε * 1.01 := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 ha) (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _) hε0
  have p4 : |b - 1| ≤ ε := abs_le.2 hb
  have p5 : |(c - √3) * (c + √3)| ≤ ε * 3.47 := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.2 hc) (abs_le.2 ⟨by linarith [lt_sqrt_three], by linarith⟩)
      (abs_nonneg _) hε0
  have hN : |a ^ 2 + b ^ 2 - c ^ 2 + a * b| ≤ 9.5 * ε := by
    rw [e]
    calc _ ≤ |(a - 1) * (a + 1) + (b - 1) * (b + 1) + (a - 1) * b + (b - 1)| +
          |(c - √3) * (c + √3)| := abs_sub _ _
      _ ≤ |(a - 1) * (a + 1)| + |(b - 1) * (b + 1)| + |(a - 1) * b| + |b - 1| +
          |(c - √3) * (c + √3)| := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans
            (add_le_add_left (abs_add_le _ _) _)) _) |>.trans (le_of_eq (by ring))
      _ ≤ 9.5 * ε := by linarith
  calc _ ≤ 9.5 * ε := hN
    _ ≤ 5 * ε * 1.99 := by linarith
    _ ≤ 5 * ε * (2 * a * b) := mul_le_mul_of_nonneg_left hab (by positivity)

/-- Normalized law of cosines near the third shell. -/
theorem cosLaw_le_neg_one_add {a b c ε : ℝ} (hε : ε ≤ 1 / 10 ^ 8) (ha : |a - 1| ≤ ε)
    (hb : |b - 1| ≤ ε) (hc : |c - 2| ≤ ε) (hcab : c ≤ a + b) :
    (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ≤ -1 + 6.1 * ε := by
  have hab := two_mul_mul_ge hε ha hb
  have hpos : 0 < 2 * a * b := by linarith
  rw [div_le_iff₀ hpos]
  rw [abs_le] at ha hb hc
  have hε0 : 0 ≤ ε := by linarith
  have e : a ^ 2 + b ^ 2 - c ^ 2 + 2 * a * b = (a + b - c) * (a + b + c) := by ring
  have h1 : 0 ≤ a + b - c := by linarith
  have h2 : a + b - c ≤ 3 * ε := by linarith
  have h3 : a + b + c ≤ 4 + 3 * ε := by linarith
  have h4 : (a + b - c) * (a + b + c) ≤ 3 * ε * (4 + 3 * ε) := by
    apply mul_le_mul h2 h3 (by linarith) (by linarith)
  nlinarith

/-! ### The three-shell test -/

theorem sin_two_pi_div_three : Real.sin (2 * π / 3) = √3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem cos_two_pi_div_three : Real.cos (2 * π / 3) = -(1 / 2) := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

namespace IsRetainedSet

/-- The normalized distance between two nearest neighbors of a retained point is within `ε` of a
shell. -/
theorem shellDist_nbrs_le (hX : IsRetainedSet ε X) (hq : q ∈ nbrs ε X p)
    (hq' : q' ∈ nbrs ε X p) (hqq' : q ≠ q') :
    |‖q - q'‖ / latticeSpacing - 1| ≤ ε ∨ |‖q - q'‖ / latticeSpacing - √3| ≤ ε ∨
      |‖q - q'‖ / latticeSpacing - 2| ≤ ε := by
  have hℓ := latticeSpacing_pos
  have h1 := (norm_sub_mem_Icc_of_mem_nbrs hq).2
  have h2 := (norm_sub_mem_Icc_of_mem_nbrs hq').2
  have hε := hX.le_small
  have htri : ‖q - q'‖ ≤ ‖q - p‖ + ‖q' - p‖ := by
    rw [show q - q' = (q - p) - (q' - p) by abel]
    exact norm_sub_le _ _
  refine shellDist_le_iff.1 (hX.shellDist_le hq.1 hq'.1 hqq' ?_)
  unfold rho0
  nlinarith

theorem triangle_le (p q q' : Plane) :
    ‖q - q'‖ / latticeSpacing ≤ ‖q - p‖ / latticeSpacing + ‖q' - p‖ / latticeSpacing := by
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ latticeSpacing_pos.le
  rw [show q - q' = (q - p) - (q' - p) by abel]
  exact norm_sub_le _ _

/-- **The three-shell test** (Lemma 5.3, `lem:threeshell`). Let `q ≠ q'` be nearest neighbors of
a retained point `p`. Then `|q - q'|/ℓ` is within `ε` of `1`, `√3` or `2`, and accordingly the
angle `∠ q p q'` is within `8ε` of `π/3`, within `8ε` of `2π/3`, or at least `π - 4√ε`. -/
theorem threeShell (hX : IsRetainedSet ε X) (hq : q ∈ nbrs ε X p)
    (hq' : q' ∈ nbrs ε X p) (hqq' : q ≠ q') :
    (|‖q - q'‖ / latticeSpacing - 1| ≤ ε ∧ |angle (q - p) (q' - p) - π / 3| ≤ 8 * ε) ∨
    (|‖q - q'‖ / latticeSpacing - √3| ≤ ε ∧
      |angle (q - p) (q' - p) - 2 * π / 3| ≤ 8 * ε) ∨
    (|‖q - q'‖ / latticeSpacing - 2| ≤ ε ∧ π - 4 * √ε ≤ angle (q - p) (q' - p)) := by
  have hε := hX.le_small
  have hε0 := hX.pos
  have ha := hq.2
  have hb := hq'.2
  have hcos := cos_angle_eq_cosLaw (hX.sub_ne_zero_of_mem_nbrs hq) (hX.sub_ne_zero_of_mem_nbrs hq')
  set d := angle (q - p) (q' - p)
  have hd0 : 0 ≤ d := angle_nonneg _ _
  have hdπ : d ≤ π := angle_le_pi _ _
  have hπ := Real.pi_gt_three
  rcases hX.shellDist_nbrs_le hq hq' hqq' with hc | hc | hc
  · refine Or.inl ⟨hc, ?_⟩
    have h1 := abs_cosLaw_sub_half_le hε ha hb hc
    rw [← hcos] at h1
    have h2 : |Real.cos d - Real.cos (π / 3)| ≤ 3.03 * ε := by
      rw [Real.cos_pi_div_three]
      nlinarith [abs_nonneg (‖q - p‖ / latticeSpacing - 1)]
    have := abs_sub_le_of_abs_cos_sub_le hd0 hdπ Real.sin_pi_div_three
      (by rw [Real.cos_pi_div_three, abs_of_pos (by norm_num)]) (abs_nonneg _)
      (by linarith) (by nlinarith) (by nlinarith) le_rfl
    nlinarith
  · refine Or.inr (Or.inl ⟨hc, ?_⟩)
    have h1 := abs_cosLaw_add_half_le hε ha hb hc
    rw [← hcos] at h1
    have h2 : |Real.cos d - Real.cos (2 * π / 3)| ≤ 5 * ε := by
      rw [cos_two_pi_div_three, sub_neg_eq_add]
      exact h1
    have := abs_sub_le_of_abs_cos_sub_le hd0 hdπ sin_two_pi_div_three
      (by rw [cos_two_pi_div_three, abs_neg, abs_of_pos (by norm_num)]) (abs_nonneg _)
      (by linarith) (by nlinarith) (by nlinarith) le_rfl
    nlinarith
  · refine Or.inr (Or.inr ⟨hc, ?_⟩)
    have h1 := cosLaw_le_neg_one_add hε ha hb hc (triangle_le p q q')
    rw [← hcos] at h1
    have hs := Real.sq_sqrt hε0.le
    have hs4 : √ε ^ 4 = ε ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hs]
    have hsq := hX.sqrt_le
    have := pi_sub_le_of_cos_le hd0 (t := 4 * √ε) (by positivity) (by linarith) (δ := 6.1 * ε) (by
      rw [mul_pow, mul_pow, hs, hs4]
      nlinarith) h1
    linarith

/-- The angle at `p` between distinct nearest neighbors is at least `π/3 - 8ε`. -/
theorem pi_div_three_sub_le_angle (hX : IsRetainedSet ε X) (hq : q ∈ nbrs ε X p)
    (hq' : q' ∈ nbrs ε X p) (hqq' : q ≠ q') :
    π / 3 - 8 * ε ≤ angle (q - p) (q' - p) := by
  have hε := hX.le_small
  have hε0 := hX.pos
  have hsq := hX.sqrt_le
  have hπ := Real.pi_gt_three
  rcases hX.threeShell hq hq' hqq' with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · linarith [(abs_le.1 h).1]
  · linarith [(abs_le.1 h).1]
  · linarith

/-- **The gap estimate (5.gap).** If `q, q'` are nearest neighbors of `p` and of each other, then
`|∠ q p q' - π/3| ≤ 20 (|a - 1| + |b - 1| + |c - 1|)` with `a = |q - p|/ℓ`, `b = |q' - p|/ℓ`,
`c = |q' - q|/ℓ`. -/
theorem abs_angle_sub_pi_div_three_le (hX : IsRetainedSet ε X) (hq : q ∈ nbrs ε X p)
    (hq' : q' ∈ nbrs ε X p) (hc : |‖q' - q‖ / latticeSpacing - 1| ≤ ε) :
    |angle (q - p) (q' - p) - π / 3| ≤
      20 * (|‖q - p‖ / latticeSpacing - 1| + |‖q' - p‖ / latticeSpacing - 1| +
        |‖q' - q‖ / latticeSpacing - 1|) := by
  have hε := hX.le_small
  have hε0 := hX.pos
  rw [norm_sub_rev q' q] at hc ⊢
  have hcos := cos_angle_eq_cosLaw (hX.sub_ne_zero_of_mem_nbrs hq) (hX.sub_ne_zero_of_mem_nbrs hq')
  set d := angle (q - p) (q' - p)
  set σ := |‖q - p‖ / latticeSpacing - 1| + |‖q' - p‖ / latticeSpacing - 1| +
    |‖q - q'‖ / latticeSpacing - 1|
  have hσ0 : 0 ≤ σ := by positivity
  have hσ : σ ≤ 3 * ε := by
    have := hq.2
    have := hq'.2
    linarith
  have hπ := Real.pi_gt_three
  have h1 : |Real.cos d - Real.cos (π / 3)| ≤ 1.01 * σ := by
    have := abs_cosLaw_sub_half_le hε hq.2 hq'.2 hc
    rwa [← hcos, ← Real.cos_pi_div_three] at this
  have hd0 : 0 ≤ d := angle_nonneg _ _
  have hdπ : d ≤ π := angle_le_pi _ _
  have := abs_sub_le_of_abs_cos_sub_le hd0 hdπ
    Real.sin_pi_div_three (by rw [Real.cos_pi_div_three, abs_of_pos (by norm_num)])
    (abs_nonneg _) (by nlinarith) (by nlinarith) (by nlinarith) le_rfl
  nlinarith

end IsRetainedSet

end TriangularLattice
