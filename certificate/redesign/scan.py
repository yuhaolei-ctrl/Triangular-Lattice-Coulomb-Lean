#!/usr/bin/env python3
"""Scan over the number M of prescribed shells.

For each M: the coefficientwise-feasible z-interval, then for the given z values
gamma (Appendix A (iii)) and K (Appendix A (iv)) with cutoff t_b = floor(t_{M+1}) - 1,
t_a = t_b - w and chi = I_u(k+1, k+1).  Prints log10(K / K_max(gamma)).

usage: scan.py --M 20 30 40 --z -1.02 -2 --w 50 --k 22
"""
import argparse, time
from math import floor, log10
from flint import arb, fmpq
from lp import Construction
from analysis import gamma_bound, tail_K
from kmax import kmax

ap = argparse.ArgumentParser()
ap.add_argument("--M", type=int, nargs="+", required=True)
ap.add_argument("--z", type=str, nargs="+", default=["-51/50"])
ap.add_argument("--w", type=int, nargs="+", default=[50])
ap.add_argument("--k", type=int, default=22)
ap.add_argument("--prec", type=int, default=0)
ap.add_argument("--tight", action="store_true")
args = ap.parse_args()


def lg(x):
    return float(x.log().mid()) / 2.302585092994046


for M in args.M:
    t0 = time.time()
    prec = args.prec or (150 * M + 1000)
    C = Construction(M, prec)
    zi = C.z_interval_coeffwise()
    zs = "None" if zi is None else f"({float(zi[0].mid()):.6g}, {float(zi[1].mid()):.8g})"
    tb = floor(float(C.t_next.mid())) - 1
    assert tb < C.t_next and tb > C.ts[-1] - 50
    print(f"M={M} m_M={C.ms[-1]} t_M={float(C.ts[-1].mid()):.2f} t_next={float(C.t_next.mid()):.2f} "
          f"t_b={tb}  z-interval {zs}  [{time.time()-t0:.1f}s]", flush=True)
    for zstr in args.z:
        num, den = (zstr.split("/") + ["1"])[:2]
        z = arb(fmpq(int(num), int(den)))
        A, B = C.A(z), C.B(z)
        posA = all(c > 0 for c in A); posB = all(c > 0 for c in B)
        if not (posA and posB):
            print(f"   z={zstr}: positivity fails (A {posA}, B {posB})")
            continue
        g, where = gamma_bound(C, A)
        for w in args.w:
            K, parts = tail_K(C, A, B, tb - w, w, k=args.k, prec=max(2048, prec // 2), tight=args.tight)
            km, _ = kmax(float(g.mid()))
            print(f"   z={zstr:>8s} w={w:3d} t_a={tb-w}: gamma={float(g.mid()):.4e} (s={where:.3f})  "
                  f"K={float(K.mid()):.3e}  [qhi {lg(parts['sup_qhi']):.1f}, D2qhi {lg(parts['sup_D2qhi']):.1f}, "
                  f"K0 {lg(parts['sup_K0']):.1f}, D2K0 {lg(parts['sup_D2K0']):.1f}]  "
                  f"log10(K/Kmax)={lg(K) - log10(km):+.1f}  [{time.time()-t0:.1f}s]", flush=True)
