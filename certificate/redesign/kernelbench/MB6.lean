namespace MB6
@[reducible] def lit {α : Sort _} (e : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun v _ => k v) (Nat.add e 1)
/-- fixed point with shift: x ↦ ((x*y) >>> k) + c, c varying via a counter to avoid convergence -/
def shiftLoop (k y n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun i ih x => lit (Nat.add (Nat.shiftRight (Nat.mul x y) k) (Nat.mul i 1000003)) ih) n x
def modLoop (p y n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun i ih x => lit (Nat.mod (Nat.add (Nat.mul x y) i) p) ih) n x
def addLoop (y n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun i ih x => lit (Nat.sub (Nat.add x y) i) ih) n x
end MB6
