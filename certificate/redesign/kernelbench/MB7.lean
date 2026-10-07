import MB6
/-- x ↦ (x * y) / (i + 3) + i : big-by-small division each step -/
def divLoop (y n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun i ih x => MB6.lit (Nat.add (Nat.div (Nat.mul x y) (Nat.add i 3)) i) ih) n x
