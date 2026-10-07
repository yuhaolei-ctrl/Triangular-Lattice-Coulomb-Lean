namespace MB
/-- primitive-only strict loop: x ↦ (x*y + c) >>> k, forced by `Nat.ble` each step. -/
def primLoop (k y c : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x =>
    let x' := Nat.shiftRight (Nat.add (Nat.mul x y) c) k
    cond (Nat.ble x' 0) x' (primLoop k y c n x')

/-- same with notation (instances). -/
def notaLoop (k y c : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x =>
    let x' := (x * y + c) >>> k
    if x' ≤ 0 then x' else notaLoop k y c n x'

/-- Int with notation. -/
def intLoop (k : Nat) (y c : Int) : Nat → Int → Int
  | 0, x => x
  | n + 1, x =>
    let x' := (x * y + c) >>> k
    if x' ≤ 0 then x' else intLoop k y c n x'

/-- primitive loop via `Nat.rec` instead of structural recursion. -/
def recLoop (k y c n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => let x' := Nat.shiftRight (Nat.add (Nat.mul x y) c) k
                   cond (Nat.ble x' 0) x' (ih x')) n x
end MB
