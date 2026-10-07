#!/usr/bin/env python3
"""Minimal precision of the redesigned certificate at given M, z (ball arithmetic).

Pipeline (all in Arb at `prec` bits, nothing at higher precision):
 1. parity solves (Arb verified solver, a-posteriori like Krawczyk) for P_e, P_o, F_e, F_o;
 2. P = P0 + mu[z Fe/Fe0 + (1+z) Fo/Fo0] in the Laguerre basis;
 3. sample-point positivity of A and B: at N negative Chebyshev-like points s_k,
    A(s_k) = P(s_k)/Omega(s_k) + sum_i [beta_i/(s_k-t_i)^2 + alpha_i/(s_k-t_i)]  (barycentric Hermite,
    partial fractions of H/Omega), B(s_k) = (1 - s_k TP(s_k))/Omega(s_k);
    with a rational approximation At (positive coefficients, from a high-precision run) and
    |u(s_k)| = |A(s_k) - At(s_k)|, the polynomial  At - sum_k |u(s_k)| prod_{m!=k}(t+|s_m|)/w_k
    must have positive coefficients (=> A >= that minorant > 0 on [0, inf)).
usage: precision_study.py M prec [prec ...]
"""
import sys, math, time
from flint import arb, arb_mat, ctx, fmpq
import lp
from lp import Construction, laguerre_vals, h_fun

M = int(sys.argv[1])
ref = Construction(M, 150 * M + 1000)
zq = fmpq(-2)
Aref = [x.mid() for x in ref.A(arb(zq))]
Bref = [x.mid() for x in ref.B(arb(zq))]


def esym(vals):
    e = [arb(1)]
    for v in vals:
        e = [(e[r] if r < len(e) else arb(0)) + (v * e[r - 1] if r >= 1 else arb(0)) for r in range(len(e) + 1)]
    return e


def check(prec):
    t0 = time.time()
    try:
        C = Construction.__new__(Construction)
        # reuse Construction but only the solve part at this precision
        C2 = Construction(M, prec)
    except Exception as e:
        return f"solve failed ({type(e).__name__})"
    ctx.prec = prec
    z = arb(zq)
    Pl = C2.P_lag(z)
    TPl = [c * (-1) ** j for j, c in enumerate(Pl)]
    ts = C2.ts
    # partial-fraction data of H/Omega
    Wi = []
    for i, ti in enumerate(ts):
        pr = arb(1); sd = arb(0)
        for j, tj in enumerate(ts):
            if j != i:
                pr *= (ti - tj) ** 2; sd += 2 / (ti - tj)
        hv = h_fun(ti); hp = hv / 2 - 1 / (2 * ti)
        Wi.append((hv / pr, (hp - hv * sd) / pr))
    N = 2 * M + 3
    S = float(ts[-1].mid())
    pts = [arb(fmpq(-int(round((S * (1 - math.cos(math.pi * (k + 0.5) / N)) / 2 + 1) * 64)), 64)) for k in range(N)]
    uA, uB = [], []
    for s in pts:
        L, _ = laguerre_vals(s, len(Pl) - 1)
        Ps = sum(c * l for c, l in zip(Pl, L)); TPs = sum(c * l for c, l in zip(TPl, L))
        Om = arb(1)
        for t in ts:
            Om *= (s - t) ** 2
        As = Ps / Om + sum(b / (s - t) ** 2 + a / (s - t) for (b, a), t in zip(Wi, ts))
        Bs = (1 - s * TPs) / Om
        uA.append(abs(As - lp.poly_eval([arb(c) for c in Aref], s)).upper())
        uB.append(abs(Bs - lp.poly_eval([arb(c) for c in Bref], s)).upper())
    out = []
    for name, ref_c, u, n in (("A", Aref, uA, 2 * M + 2), ("B", Bref, uB, 2 * M + 3)):
        P = pts[:n]; uu = u[:n]
        absP = [abs(p) for p in P]
        ok = True; worst = None
        for k in range(n):
            pass
        # U_j = sum_k u_k e_{n-1-j}(|s|_{-k}) / w_k ; use e over all points (upper bound)
        e = esym(absP)
        wk = []
        for k in range(n):
            pr = arb(1)
            for m in range(n):
                if m != k: pr *= abs(P[k] - P[m])
            wk.append(pr)
        coef = sum(uu[k] / wk[k] for k in range(n))
        for j in range(n):
            Uj = coef * e[n - 1 - j]
            r = arb(ref_c[j]) - Uj
            if not (r > 0):
                ok = False
            m = arb((Uj / arb(ref_c[j])).mid())
            worst = m if worst is None or m > worst else worst
        out.append(f"{name}: {'OK' if ok else 'FAIL'} (max U_j/At_j = 2^{float((worst.log()/arb(2).log()).mid()) if worst > 0 else -9999:.0f})")
    return "; ".join(out) + f"  [{time.time()-t0:.1f}s]"


for p in [int(a) for a in sys.argv[2:]]:
    print(f"M={M} prec={p}: {check(p)}", flush=True)
