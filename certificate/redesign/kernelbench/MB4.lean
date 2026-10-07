namespace MB4
@[reducible] def lit {α : Sort _} (e : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun v _ => k v) (Nat.add e 1)
/-- x ↦ (x*y + c) mod p : values change at every step (no cache hits). -/
def loop (p y c n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => lit (Nat.mod (Nat.add (Nat.mul x y) c) p) ih) n x
/-- two-level: outer `n1`, inner `n2`, inner result forced by `lit`. -/
def loop2 (p y c n1 n2 x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => lit (loop p y c n2 x) ih) n1 x
end MB4
