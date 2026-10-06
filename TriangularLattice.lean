/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module

public import TriangularLattice.Statement
public import TriangularLattice.Main
public import TriangularLattice.Rigidity.Directions
public import TriangularLattice.Rigidity.Hexagon
public import TriangularLattice.Rigidity.ThreeShell
public import TriangularLattice.Rigidity.Slots

/-!
# The triangular lattice minimizes the two-dimensional Coulomb renormalized energy

Root of the development. `TriangularLattice.Statement` holds the definitions of the public
statement (generated from `Challenge.lean`), and `TriangularLattice.Main` proves Theorem 1.1.
See `docs/PLAN.md` for the module structure.
-/
