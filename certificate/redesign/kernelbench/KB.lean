/-!
# Kernel benchmark library: fixed-point dyadic interval arithmetic on `Int`

An interval `⟨lo, hi⟩` at scale `k` denotes `[lo · 2^-k, hi · 2^-k]`.
Rounding: `x >>> k` is floor division by `2^k` on `Int`; ceiling is `-((-x) >>> k)`.
Loops are strict: each step forces the new state through a decidable test, so the
kernel never builds a deep unevaluated term.
-/

namespace KB

structure Ival where
  lo : Int
  hi : Int

@[inline] def fl (x : Int) (k : Nat) : Int := x >>> k
@[inline] def ce (x : Int) (k : Nat) : Int := -((-x) >>> k)

def add (a b : Ival) : Ival := ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- general interval product (four products, min/max). -/
def mul (k : Nat) (a b : Ival) : Ival :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨fl (min (min p1 p2) (min p3 p4)) k, ce (max (max p1 p2) (max p3 p4)) k⟩

/-- product when both intervals are known to be positive (two products). -/
def mulPos (k : Nat) (a b : Ival) : Ival := ⟨fl (a.lo * b.lo) k, ce (a.hi * b.hi) k⟩

def step (k : Nat) (y c x : Ival) : Ival := add (mul k x y) c
def stepPos (k : Nat) (y c x : Ival) : Ival := add (mulPos k x y) c

/-- `n` strict iterations of `x ↦ x * y + c`. -/
def loop (k : Nat) (y c : Ival) : Nat → Ival → Ival
  | 0, x => x
  | n + 1, x =>
    let x' := step k y c x
    if x'.lo ≤ x'.hi then loop k y c n x' else x'

def loopPos (k : Nat) (y c : Ival) : Nat → Ival → Ival
  | 0, x => x
  | n + 1, x =>
    let x' := stepPos k y c x
    if x'.lo ≤ x'.hi then loopPos k y c n x' else x'

/-- `y ≈ 1/2`, `c ≈ 1/2`: the iteration converges to `1`, numbers stay `k`-bit. -/
def yv (k : Nat) : Ival := ⟨2 ^ (k - 1) - 1, 2 ^ (k - 1) + 1⟩
def cv (k : Nat) : Ival := ⟨2 ^ (k - 1) - 3, 2 ^ (k - 1) + 3⟩
def x0 : Ival := ⟨0, 0⟩

/-- the result contains 1 and has width < 2^(k/2). -/
def check (k n : Nat) : Bool :=
  let r := loop k (yv k) (cv k) n x0
  decide (r.lo ≤ 2 ^ k) && decide (2 ^ k ≤ r.hi) && decide (r.hi - r.lo < 2 ^ (k / 2))

def checkPos (k n : Nat) : Bool :=
  let r := loopPos k (yv k) (cv k) n x0
  decide (r.lo ≤ 2 ^ k) && decide (2 ^ k ≤ r.hi) && decide (r.hi - r.lo < 2 ^ (k / 2))

/-! ## Dot products and matrix products (exact integer arithmetic) -/

/-- deterministic pseudo-random `b`-bit signed integers. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def randList (b : Nat) : Nat → Nat → List Int
  | 0, _ => []
  | n + 1, s =>
    let s' := lcg s
    let v : Int := (Int.ofNat ((s' * (2 ^ b / 2 ^ 64 + 1)) % 2 ^ b)) - 2 ^ (b - 1)
    v :: randList b n s'

def dot : List Int → List Int → Int → Int
  | a :: as, b :: bs, acc =>
    let acc' := acc + a * b
    if acc' = 0 then dot as bs 0 else dot as bs acc'
  | _, _, acc => acc

/-- `n × n` matrix as list of rows. -/
def randMat (b n s : Nat) : List (List Int) :=
  (List.range n).map fun i => randList b n (s + 7919 * i)

def transpose (n : Nat) (M : List (List Int)) : List (List Int) :=
  (List.range n).map fun j => M.map fun r => r.getD j 0

/-- sum over all entries of `|R M|`, strict per row. -/
def absRowSums (R Mt : List (List Int)) : List Int :=
  R.map fun r => (Mt.map fun c => (dot r c 0).natAbs).foldl (· + ·) 0 |> Int.ofNat

def matCheck (b n : Nat) : Bool :=
  let R := randMat b n 1
  let Mt := randMat b n 2
  let s := absRowSums R Mt
  decide (s.foldl (· + ·) 0 ≠ 0)

/-! ## Kronecker packing: one big product replaces a dot product -/

/-- pack `[a₀, a₁, …]` as `Σ aᵢ 2^(D i)` (signed digits). -/
def pack (D : Nat) : List Int → Int
  | [] => 0
  | a :: as => a + (pack D as) * 2 ^ D

/-- unpack `n` signed digits (each assumed `< 2^(D-1)` in absolute value). -/
def unpack (D : Nat) : Nat → Int → List Int
  | 0, _ => []
  | n + 1, x =>
    let r := x % 2 ^ D          -- Int.emod: 0 ≤ r < 2^D
    let d := if r < 2 ^ (D - 1) then r else r - 2 ^ D
    d :: unpack D n ((x - d) / 2 ^ D)

/-- row `i` of `R·M` via packing the rows of `M`: `Σ_j R_ij · pack(M_j)`. -/
def packedRow (r : List Int) (Mp : List Int) : Int :=
  (List.zipWith (· * ·) r Mp).foldl (· + ·) 0

def packedCheck (b n : Nat) : Bool :=
  let D := 2 * b + 16
  let R := randMat b n 1
  let M := randMat b n 2
  let Mp := M.map (pack D)
  let rows : List Nat := R.map fun r => (unpack D n (packedRow r Mp)).foldl (fun (s : Nat) d => s + d.natAbs) 0
  decide (rows.foldl (· + ·) (0 : Nat) ≠ 0)

/-- consistency of the two matrix-product routes (used once, small). -/
def agree (b n : Nat) : Bool :=
  let D := 2 * b + 16
  let R := randMat b n 1
  let M := randMat b n 2
  let Mp := M.map (pack D)
  let Mt := transpose n M
  R.all fun r => unpack D n (packedRow r Mp) == Mt.map fun c => dot r c 0

end KB
