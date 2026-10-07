#!/usr/bin/env python3
"""For each M: feasible z for coefficientwise positivity of A, B; radii sanity."""
import sys, time
from flint import arb, ctx
from lp import Construction

for M in [int(a) for a in sys.argv[1:]]:
    t0 = time.time()
    prec = max(2000, 140 * M)
    C = Construction(M, prec)
    zi = C.z_interval_coeffwise()
    worst = max(max(abs(x.rad() / x.mid()) if x.mid() != 0 else 0 for x in C.Aa + C.Ab + C.Ba + C.Bb), 0)
    print(f"M={M:3d} m_M={C.ms[-1]:4d} t_M={float(C.ts[-1].mid()):8.2f} t_next={float(C.t_next.mid()):8.2f} "
          f"prec={prec} zint={zi} worst_relrad={float(worst):.2e}  ({time.time()-t0:.1f}s)", flush=True)
