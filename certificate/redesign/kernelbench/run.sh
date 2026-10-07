#!/bin/sh
# Reproduce the kernel calibration (scratch benchmarks, not part of the library).
# usage: PATH=<lean-4.35.0-rc3/bin>:$PATH ./run.sh   (run inside a scratch copy of this folder)
set -e
for m in KB MB MB2 MB4 MB6 MB7; do lean -o $m.olean $m.lean; done
python3 - <<'PY'
import random, sys
sys.set_int_max_str_digits(0)
random.seed(4)
b = 1024; y2 = (1 << b) - random.getrandbits(b - 20); x = random.getrandbits(b)
open("Q.lean", "w").write(f"""import MB6
set_option profiler true
@[reducible] def inner (x : Nat) : Nat := MB6.shiftLoop {b} {y2} 1000 x
def outer (n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x) (fun _ ih x => MB6.lit (inner x) ih) n x
theorem t : Nat.ble 0 (outer 60 {x}) = true := by decide +kernel
""")
PY
LEAN_PATH=. lean -o Q.olean Q.lean | grep "type checking took"
LEAN_PATH=. leanexport Q -- t > Q.ndjson
cat > nanoda.json <<J
{"export_file_path": "Q.ndjson", "permitted_axioms": ["propext","Quot.sound","Classical.choice"], "unpermitted_axiom_hard_error": false, "nat_extension": true, "string_extension": true, "num_threads": 1, "print_success_message": true}
J
/usr/bin/time nanoda_bin nanoda.json
/usr/bin/time con-ron --verified --jobs=1 Q.ndjson
