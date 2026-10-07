/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Rigidity.Directions
public import TriangularLattice.Rigidity.Hexagon
public import TriangularLattice.Rigidity.ThreeShell
public import TriangularLattice.Rigidity.Slots
public import TriangularLattice.Rigidity.FullVertex
public import TriangularLattice.Rigidity.Cells
public import TriangularLattice.Rigidity.Holes

/-!
# Defects, local directions and disjoint hexagonal cells

The local plane geometry of Section 5 of the manuscript, in an abstract local setting: a set
`X` of points (the retained set) with `IsRetainedSet ε X`, that is, `0 < ε ≤ ε_geo = 10⁻⁸` and no
two distinct points `p, p' ∈ X` with `|p - p'| ≤ ρ₀ ℓ` have `dist(|p - p'|/ℓ, {1, √3, 2}) > ε`.
Periodicity, the counts per period and the occupancy of the removed points (Lemmas 5.2 and 5.8)
are not treated here.

## Correspondence with the manuscript

* Separation (end of Lemma 5.2): `IsRetainedSet.mul_le_norm_sub`,
  `IsRetainedSet.one_lt_norm_sub`, `IsRetainedSet.le_norm_sub_of_not_mem_nbrs`.
* Lemma 5.3 (three-shell test): `IsRetainedSet.threeShell`,
  `IsRetainedSet.pi_div_three_sub_le_angle`, at most six neighbors
  `IsRetainedSet.encard_nbrs_le_six`; six neighbors: `IsSlotAssignment.occupant_succ_mem_nbrs_and`,
  `IsSlotAssignment.angle_occupant_succ_mem_Icc`, `IsSlotAssignment.abs_angle_occupant_succ_sub_le`
  and the counterclockwise order `IsSlotAssignment.toReal_dir_occupant_succ_sub`; (5.gap):
  `IsRetainedSet.abs_angle_sub_pi_div_three_le`.
* Definition 5.4: `IsSlotAssignment`, `IsOrientation`, `exists_isOrientation`,
  `IsSlotAssignment.add_vec`, `IsFull`, `IsOccupied`, `occupant`, `slotError`, `dirErrMax` (`a_p`),
  `strainMax` (`s_p`), `strainEnergy` (`e_p`), `orientDiff` (`Δ_pq`), `endpointErr`
  (`err_{p,s}`).
* Lemma 5.5: (a) `IsSlotAssignment.slotError_le_of_isFull`,
  `IsSlotAssignment.dirErrMax_le_of_isFull`; (b) `IsSlotAssignment.injOn`,
  `IsSlotAssignment.slotError_le`; (c) the multiplicity
  `IsRetainedSet.encard_setOf_mem_strainEdges_le` and `IsSlotAssignment.strainEnergy_eq_sum`;
  (d) `abs_orientDiff_le`; (e) `IsSlotAssignment.norm_endpointErr_le_of_isFull`,
  `IsSlotAssignment.norm_endpointErr_le_sqrt`.
* `H_θ` and (5.kappa): `hexagon`, `hexCell`, `kappa`, `cell`, `IsSlotAssignment.kappa_lt`.
* Lemma 5.6: `IsOrientation.disjoint_cell`; the pointwise bounds behind (5.kappasum):
  `kappa_sq_le`, `IsSlotAssignment.dirErrMax_sq_le_of_isFull`, `IsSlotAssignment.dirErrMax_sq_le`,
  `orientDiff_sq_le`, `IsSlotAssignment.norm_endpointErr_sq_le_of_isFull`,
  `IsSlotAssignment.norm_endpointErr_sq_le`, `IsRetainedSet.exists_strainMax_eq`.
* Lemma 5.7: `holeRadius`, `holeCenter`, `IsOrientation.disjoint_ball_holeCenter_cell`,
  `IsRetainedSet.encard_holes_le`, `IsSlotAssignment.exists_not_isOccupied`.

## Representation

Directions are elements of `Real.Angle`, whose quotient norm `‖θ‖ = |θ.toReal|` is the
unoriented angle (`angle_eq_norm_dir_sub`); orientations `θ_p` are real numbers and slot `j` has
direction `θ_p + jπ/3`. Orientations and slot assignments are not chosen once and for all: the
predicate `IsSlotAssignment ε X p θ σ` says that `θ` is the direction of `q₀ - p` for a nearest
neighbor `q₀` and that every neighbor is assigned a closest slot; all estimates hold for every such
choice, choices exist (`exists_isOrientation`), and they transport along translations preserving
`X` (`IsSlotAssignment.add_vec`), so that they can be made once per `Γ`-orbit. For a full vertex
the manuscript's counterclockwise numbering starting from `q₀` is exactly the slot numbering
(`IsSlotAssignment.toReal_dir_occupant_succ_sub`). The hexagon is the open set
`H_θ = {x | ⟪x, e_{θ + jπ/3}⟫ < ℓ/2 for all j}`, so cells are open and are disjoint (not only their
interiors).

## Deviations from the manuscript

* Directional errors are at most `4√ε` at every vertex (the manuscript has `6√ε = A'_dir √ε` at
  deficient vertices); the statements are given with the manuscript's constants `A_dir = 140`,
  `A'_dir = 6`, `m_e = 4`, except `m_hole = 96` instead of `60` (see
  `TriangularLattice.Rigidity.Holes`).
* The bound `|Δ_pq| ≤ a_p + a_q` and the endpoint error bound `|err_{p,s}| ≤ ℓ (s_p + a_p)` hold for
  arbitrary slot assignments; the multiplicity `m_e = 4` holds for arbitrary slot assignments as
  well (edges of `e_p` through unoccupied slots are degenerate or contain `p`).
* In the proof of Lemma 5.3 the manuscript bounds the partial derivatives of
  `(a² + b² - c²)/(2ab)` on `c ≤ ρ₀`; there the bound `2.2` fails (`∂_a = 2.205` at
  `a = b = 1`, `c = 2.1`), but the bound is only needed for `c ≤ 2 + 2ε`, where it holds. The
  formalization bounds `|(a² + b² - c²)/(2ab) - cos θ₀|` directly by `1.01(|a-1|+|b-1|+|c-1|)`,
  `5ε` and `6.1ε` in the three cases, which gives the stated `8ε` and `4√ε`.
* The disjointness of cells along a nearest edge uses the support-function bound
  `r (ℓ/2 + (ℓ/√3)|u - n|)` (chord instead of angle), and the holes argument uses endpoint errors;
  constants are unchanged.
-/

@[expose] public section

namespace TriangularLattice

end TriangularLattice
