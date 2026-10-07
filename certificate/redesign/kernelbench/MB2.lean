namespace MB2
/-- `lit e k` : evaluate `e` to a numeral `v` and continue with `k v`
(iota-reduction of `Nat.rec` on the numeral `e + 1` binds `v` to a numeral). -/
@[reducible] def lit {α : Sort _} (e : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun v _ => k v) (Nat.add e 1)

/-- x ↦ ((x*y) >>> k) + c, strict via `lit`. Fixed point 2^k if y = c = 2^(k-1). -/
def loop (k y c n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => lit (Nat.add (Nat.shiftRight (Nat.mul x y) k) c) ih) n x
end MB2
