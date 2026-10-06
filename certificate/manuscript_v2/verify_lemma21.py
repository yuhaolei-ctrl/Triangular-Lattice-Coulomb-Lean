#!/usr/bin/env python3
"""
Rigorous certificate for the finite computational lemma (Lemma 2.1).

Everything is computed in ball arithmetic (python-flint / Arb).  Each printed
bound is a rigorous enclosure or a rigorous one-sided bound of the exact
quantity it names.  The four assertions certified are:

  (C1) the two 200x200 Hermite systems are nonsingular, F_e(0) F_o(0) != 0;
  (C2) every power coefficient of A (202 of them) and B (203) is > 0;
  (C3) q(r) >= 1e-4 * dist(r/l, {1, sqrt3, 2})^2  on  0 < r <= 2.1 l;
  (C4) sup (1+|x|)^20 (|V(x)| + ||D^2 V(x)||_op)  <  K_cert   (printed).

Usage:  python3 verify_lemma21.py [solve_prec_bits] [tail_prec_bits]
Defaults: 13312 and 4096.
"""
import sys, time, json
from math import comb
from flint import arb, arb_mat, ctx, fmpq

PREC_SOLVE = int(sys.argv[1]) if len(sys.argv) > 1 else 13312
PREC_TAIL = int(sys.argv[2]) if len(sys.argv) > 2 else 4096
T0 = time.time()
OUT = {}


def log(*a):
    print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)


# ---------------------------------------------------------------------------
# 0.  Exact inputs
# ---------------------------------------------------------------------------
NODES_M = sorted({a * a + a * b + b * b for a in range(-21, 22) for b in range(-21, 22)} - {0})
NODES_M = [m for m in NODES_M if m <= 324]
assert len(NODES_M) == 100 and NODES_M[-1] == 324
Z_RAT = fmpq(-51, 50)           # the rational correction z
CUT_LO, CUT_HI, CUT_ORD = 2000, 2100, 26   # cutoff interval and order


def laguerre_vals(t, n):
    """L_0..L_n and L_0'..L_n' at t (ball arithmetic)."""
    L = [arb(1), 1 - t]
    for j in range(1, n):
        L.append(((2 * j + 1 - t) * L[j] - j * L[j - 1]) / (j + 1))
    dL = [arb(0)] + [j * (L[j] - L[j - 1]) / t for j in range(1, n + 1)]
    return L, dL


def h_fun(t):
    """h(t) = (1/2) e^{t/2} E_1(t/2)."""
    return (t / 2).exp() * (t / 2).expint(1) / 2


def to_power(c):
    """Laguerre coefficients c_j  ->  power coefficients of sum c_j L_j."""
    n = len(c)
    out = []
    fact = arb(1)
    for v in range(n):
        if v > 0:
            fact *= v
        s = arb(0)
        for j in range(v, n):
            s += c[j] * comb(j, v)
        out.append(s * (-1) ** v / fact)
    return out


def poly_divide(num, den):
    num = list(num)
    dq = len(num) - len(den)
    q = [arb(0)] * (dq + 1)
    lc = den[-1]
    for k in range(dq, -1, -1):
        q[k] = num[k + len(den) - 1] / lc
        for i, c in enumerate(den):
            num[k + i] -= q[k] * c
    return q, num[: len(den) - 1]


def poly_mul(p, q):
    out = [arb(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def poly_add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else arb(0)) + (q[i] if i < len(q) else arb(0)) for i in range(n)]


def poly_scale(p, c):
    return [c * a for a in p]


def poly_deriv(p, k=1):
    for _ in range(k):
        p = [i * p[i] for i in range(1, len(p))] or [arb(0)]
    return p


def poly_shift(p, s):
    """coefficients of p(s + x) in x."""
    n = len(p)
    out = [arb(0)] * n
    for k in range(n):
        if p[k] == 0:
            continue
        sp = arb(1)
        for v in range(k, -1, -1):
            out[v] += p[k] * comb(k, v) * sp
            sp *= s
    return out


def poly_eval(p, x):
    s = arb(0)
    for c in reversed(p):
        s = s * x + c
    return s


# ---------------------------------------------------------------------------
# 1.  Finite solves  (C1), construction of P, A, B  (C2)
# ---------------------------------------------------------------------------
ctx.prec = PREC_SOLVE
pi = arb.pi()
alpha = 4 * pi / arb(3).sqrt()
ts = [alpha * m for m in NODES_M]
NL = 401
LV = [laguerre_vals(t, NL) for t in ts]
log("Laguerre values done")

Pl = {}
Fl = {0: {}, 1: {}}
for par in (0, 1):
    js = [j for j in range(400) if j % 2 == par]
    M = arb_mat(200, 200)
    rhs = arb_mat(200, 2)
    lead = 400 + par
    for i in range(100):
        t = ts[i]
        L, dL = LV[i]
        for c, j in enumerate(js):
            M[2 * i, c] = L[j]
            M[2 * i + 1, c] = dL[j]
        hv = h_fun(t)
        hp = hv / 2 - 1 / (2 * t)
        if par == 0:
            v, dv = (-hv + 1 / t) / 2, (-hp - 1 / t ** 2) / 2
        else:
            v, dv = (-hv - 1 / t) / 2, (-hp + 1 / t ** 2) / 2
        rhs[2 * i, 0] = v
        rhs[2 * i + 1, 0] = dv
        rhs[2 * i, 1] = -L[lead]
        rhs[2 * i + 1, 1] = -dL[lead]
    X = M.solve(rhs)          # certified enclosure; raises if singular not excluded
    for c, j in enumerate(js):
        Pl[j] = X[c, 0]
        Fl[par][j] = X[c, 1]
    log(f"system parity {par}: solved (nonsingularity certified by Arb)")

P0 = [Pl.get(j, arb(0)) for j in range(402)]
Fe = [Fl[0].get(j, arb(0)) for j in range(402)]
Fo = [Fl[1].get(j, arb(0)) for j in range(402)]
Fe[400] = arb(1)
Fo[401] = arb(1)
Fe0 = sum(Fe)
Fo0 = sum(Fo)
assert Fe0 != 0 and Fo0 != 0, "F_e(0) F_o(0) != 0 NOT certified"
OUT["Fe0"] = Fe0.str(8)
OUT["Fo0"] = Fo0.str(8)
log("F_e(0) =", Fe0.str(8), "  F_o(0) =", Fo0.str(8), "  (both certified nonzero)")

mu = sum(P0[j] * (-1) ** j for j in range(402))
z = arb(Z_RAT)
P = [P0[j] + mu * (z * Fe[j] / Fe0 + (1 + z) * Fo[j] / Fo0) for j in range(402)]
TP = [P[j] * (-1) ** j for j in range(402)]
OUT["mu"] = mu.str(8)
OUT["TP0_enclosure"] = sum(TP).str(5)
log("mu =", mu.str(8), "  (TP)(0) enclosure =", sum(TP).str(5), " [identically 0 by (2.5)]")

Pp = to_power(P)
TPp = to_power(TP)

# Hermite interpolant of h (degree <= 199), confluent Vandermonde in power basis
V = arb_mat(200, 200)
r = arb_mat(200, 1)
for i, t in enumerate(ts):
    p = arb(1)
    for k in range(200):
        V[2 * i, k] = p
        V[2 * i + 1, k] = k * p / t
        p = p * t
    hv = h_fun(t)
    r[2 * i, 0] = hv
    r[2 * i + 1, 0] = hv / 2 - 1 / (2 * t)
Hc = V.solve(r)
Hpol = [Hc[k, 0] for k in range(200)]
log("Hermite interpolant of h done")

Om = [arb(1)]
for t in ts:
    for _ in range(2):
        Om = poly_add([arb(0)] + Om, poly_scale(Om, -t))
numA = poly_add(Pp, Hpol)
A, remA = poly_divide(numA, Om)
numB = poly_add([arb(1)], [arb(0)] + poly_scale(TPp, -1))
B, remB = poly_divide(numB, Om)
assert len(A) == 202 and len(B) == 203
okA = all(c > 0 for c in A)
okB = all(c > 0 for c in B)
assert okA and okB, "positivity of A or B NOT certified"
OUT["remA_max"] = max(abs(x).upper() for x in remA).str(3)
OUT["remB_max"] = max(abs(x).upper() for x in remB).str(3)
OUT["A0"] = A[0].str(6)
OUT["B0"] = B[0].str(6)
OUT["Alead"] = A[-1].str(6)
log("all 202 coefficients of A > 0 and all 203 of B > 0: CERTIFIED")
log("  (consistency: |rem A| <=", OUT["remA_max"], " |rem B| <=", OUT["remB_max"], ")")

gamma = arb.const_euler()
cq = poly_eval(Pp, arb(0)) - (gamma + pi.log()) / 2
OUT["cq_minus_H"] = (cq - arb(1) / 2).str(40)
log("diagnostic c_q - H =", OUT["cq_minus_H"])

# ---------------------------------------------------------------------------
# 2.  (C3): q(r) >= 1e-4 dist(s,{1,sqrt3,2})^2  for s = r/l in (0, 2.1]
#     q = e^{-t/2} Omega(t) [A(t) + J(t)],  J > 0,  t = alpha s^2,
#     Omega(t) = alpha^2 (s - s_i)^2 (s + s_i)^2 prod_{j != i} (t - t_j)^2.
# ---------------------------------------------------------------------------
ctx.prec = 2048
s3 = arb(3).sqrt()
S_NODES = [arb(1), s3, arb(2)]            # s-values of the three near shells
VOR = [(arb(0), (1 + s3) / 2), ((1 + s3) / 2, (s3 + 2) / 2), ((s3 + 2) / 2, arb(21) / 10)]
NSUB = 256
A2048 = [arb(c) for c in A]              # coefficients re-rounded at 2048 bits (enclosures persist)
ts2048 = [arb(t) for t in ts]
alpha2048 = arb(alpha)
best_ratio = None
for i, (sa_lo, sa_hi) in enumerate(VOR):
    si = S_NODES[i]
    for n in range(NSUB):
        s_lo = sa_lo + (sa_hi - sa_lo) * n / NSUB
        s_hi = sa_lo + (sa_hi - sa_lo) * (n + 1) / NSUB
        t_lo, t_hi = alpha2048 * s_lo ** 2, alpha2048 * s_hi ** 2
        # lower bounds of each monotone factor on [s_lo, s_hi]
        val = (-t_hi / 2).exp()                 # e^{-t/2} decreasing
        val *= alpha2048 ** 2 * (s_lo + si) ** 2  # increasing
        val *= poly_eval(A2048, t_lo)           # positive coefficients: increasing
        for j in range(100):
            if j == i:
                continue
            tj = ts2048[j]
            # no node inside (t_lo,t_hi): verify and take endpoint minimum
            assert not (t_lo < tj and tj < t_hi), "node inside subinterval"
            val *= min((t_lo - tj) ** 2, (t_hi - tj) ** 2)
        # J >= 0 discarded.  val is a rigorous lower bound of q / (s - s_i)^2.
        lb = val.lower()
        if best_ratio is None or lb < best_ratio:
            best_ratio = lb
OUT["min_ratio_214"] = best_ratio.str(8)
assert best_ratio > arb(1) / 10000, "(2.14) NOT certified"
log("(2.14) certified: q / dist^2 >=", best_ratio.str(8), " > 1e-4 on (0, 2.1 l]")

# ---------------------------------------------------------------------------
# 3.  (C4): weighted tail bounds for V = q_hi + K_0.
#     Every function of t = 2000 + x, x >= 0, is majorised by
#     e^{-1000} e^{-x/2} M(x), M a polynomial with nonnegative coefficients.
#     sup_{x>=0} e^{-x/2} x^j = (2j/e)^j ;  int_0^oo e^{-x/2} x^j dx = 2^{j+1} j!.
# ---------------------------------------------------------------------------
from flint import arb_poly
ctx.prec = PREC_TAIL
pi = arb.pi()
E = arb(1).exp()
e_m1000 = (-arb(1000)).exp()
T_LO = arb(CUT_LO)
MAXD = 24


def P(lst):
    return arb_poly([arb(c) for c in lst])


def nonneg(p):
    return arb_poly([abs(c).upper() if c != 0 else arb(0) for c in p.coeffs()])


def sup_ex(M):
    s = arb(0)
    for j, c in enumerate(M.coeffs()):
        s += c * ((2 * arb(j) / E) ** j if j > 0 else 1)
    return s.upper()


def int_ex(M):
    s = arb(0); f = arb(1)
    for j, c in enumerate(M.coeffs()):
        if j > 0:
            f *= j
        s += c * 2 ** (j + 1) * f
    return s.upper()


def derivs(p, n):
    out = [p]
    for _ in range(n):
        out.append(out[-1].derivative())
    return out


fact = [arb(1)]
for k in range(1, 60):
    fact.append(fact[-1] * k)

# majorant of Omega(2000+x):  prod (|2000 - t_i| + x)^2
Omt = P([1])
for t in ts:
    c = abs(T_LO - arb(t))
    Omt = Omt * P([c * c, 2 * c, 1])
Omt = nonneg(Omt)
Om0_lo = poly_eval([arb(c) for c in Om], arb(0)).lower()      # Omega(0) > 0
A_sh = nonneg(P(poly_shift([arb(c) for c in A], T_LO)))
B_sh = nonneg(P(poly_shift([arb(c) for c in B], T_LO)))
OmA = derivs(Omt * A_sh, MAXD)        # majorises |(Omega A)^{(d)}(2000+x)|
OmB = derivs(Omt * B_sh, MAXD)        # majorises |(Omega B)^{(d)}(2000+x)|
Omd = derivs(Omt, MAXD)
J_d = [(fact[c] / (T_LO ** (c + 1) * Om0_lo)).upper() for c in range(MAXD + 1)]   # |J^{(c)}|
it_d = [(fact[c] / T_LO ** (c + 1)).upper() for c in range(MAXD + 1)]              # |(1/t)^{(c)}|


def OmAJ(d):
    """majorant of |(Omega (A+J))^{(d)}|."""
    p = OmA[d]
    for b in range(d + 1):
        p = p + Omd[b] * (comb(d, b) * J_d[d - b])
    return p


def with_exp(parts_fn, m, scal_fn=None):
    """
    majorant of |d^m/dt^m [ e^{-t/2} * F * (scalar-bounded factor) ]| / (e^{-1000} e^{-x/2}),
    parts_fn(d) majorises |F^{(d)}|, scal_fn(c) bounds |third^{(c)}| (or None).
    """
    out = P([0])
    for a in range(m + 1):
        for b in range(m - a + 1):
            c = m - a - b
            if scal_fn is None and c > 0:
                continue
            coef = fact[m] / (fact[a] * fact[b] * fact[c]) * arb(2) ** (-a)
            if scal_fn is not None:
                coef *= scal_fn(c)
            out = out + parts_fn(b) * coef
    return out


Q_maj = [with_exp(OmAJ, m) for m in range(3)]                                   # q(t) derivatives
a_maj = [with_exp(lambda d: OmB[d], m, lambda c: it_d[c]) for m in range(MAXD - 1)]  # a(t) derivatives
log("derivative majorants of q(t), a(t) built")

# cutoff derivative bounds  c_j = sup_{[2000,2100]} |chi^{(j)}|
pu = [arb(0)] * 53
for k in range(27):
    pu[26 + k] += comb(26, k) * (-1) ** k
Beta = fact[26] * fact[26] / fact[53]
c_chi = [arb(1)]
pd = P(pu)
for j in range(1, CUT_ORD + 1):
    sup_pd = sum(abs(c) for c in pd.coeffs())
    c_chi.append((sup_pd / (100 * Beta) / arb(100) ** (j - 1)).upper())
    pd = pd.derivative()
OUT["c_chi_max"] = max(c_chi).str(5)


def chi_times(maj, m):
    out = P([0])
    for j in range(m + 1):
        out = out + maj[m - j] * (comb(m, j) * c_chi[j])
    return out


qhi = [chi_times(Q_maj, m) for m in range(3)]
ahi = [chi_times(a_maj, m) for m in range(MAXD - 1)]

# weight (1+r)^20 <= 2^19 (1 + (t/2pi)^10)
Wt = P([1]) + nonneg(P(poly_shift([arb(0)] * 10 + [(1 / (2 * pi)) ** 10], T_LO)))
W19 = arb(2) ** 19
tpoly = P([T_LO, 1])

sup_qhi = (W19 * e_m1000 * sup_ex(Wt * qhi[0])).upper()
hess_q = qhi[1] * (4 * pi) + tpoly * qhi[2] * (8 * pi)       # ||D^2 g|| <= 4pi|G'| + 8pi t|G''|
sup_D2qhi = (W19 * e_m1000 * sup_ex(Wt * hess_q)).upper()
log("q_hi: weighted sup |q_hi| <=", sup_qhi.str(5), "  weighted sup ||D^2 q_hi|| <=", sup_D2qhi.str(5))


def lap_coeffs(n, dharm):
    cur = {(0, 0): arb(1)}
    for _ in range(n):
        nxt = {}
        for (j, k), b in cur.items():
            if j >= 1:
                nxt[(j - 1, k)] = nxt.get((j - 1, k), arb(0)) + b * (j * (j - 1) + (dharm + 1) * j)
            nxt[(j, k + 1)] = nxt.get((j, k + 1), arb(0)) + b * (2 * j + dharm + 1)
            nxt[(j + 1, k + 2)] = nxt.get((j + 1, k + 2), arb(0)) + b
        cur = nxt
    return cur


def int_abs_lap(F, n, dharm, extra_t=0):
    """upper bound of int |Delta^n [H_d F]| dk,  |H_0|=1, |H_2| <= t/(4pi) (extra_t=1)."""
    beta = lap_coeffs(n, dharm)
    tot = P([0])
    for (j, k), b in beta.items():
        tot = tot + tpoly ** (j + extra_t) * F[k] * b
    scale = (8 * pi) ** n * (1 / (4 * pi)) ** extra_t / 2
    return (scale * e_m1000 * int_ex(tot)).upper()


I0 = int_abs_lap(ahi, 0, 0)
I10 = int_abs_lap(ahi, 10, 0)
sup_K0 = (W19 * (I0 + I10 / (2 * pi) ** 20)).upper()
F_rad = []
for m in range(MAXD - 1):
    pm = tpoly * ahi[m] * (1 / (4 * pi))
    if m >= 1:
        pm = pm + ahi[m - 1] * (m / (4 * pi))
    F_rad.append(pm)
R0 = int_abs_lap(F_rad, 0, 0)
R10 = int_abs_lap(F_rad, 10, 0)
H0 = int_abs_lap(ahi, 0, 2, extra_t=1)
H10 = int_abs_lap(ahi, 10, 2, extra_t=1)
sup_D2K0 = (W19 * 4 * pi ** 2 * (R0 + H0 + (R10 + H10) / (2 * pi) ** 20)).upper()
log("K_0: weighted sup |K_0| <=", sup_K0.str(5), "  weighted sup ||D^2 K_0|| <=", sup_D2K0.str(5))

sup_V = (sup_qhi + sup_K0).upper()
sup_D2V = (sup_D2qhi + sup_D2K0).upper()
K_cert = (sup_V + sup_D2V).upper()
OUT["sup_w_V"] = sup_V.str(6)
OUT["sup_w_D2V"] = sup_D2V.str(6)
OUT["K_cert"] = K_cert.str(6)
log("(2.15)/(2.16): sup (1+|x|)^20 |V| <=", sup_V.str(6))
log("                sup (1+|x|)^20 ||D^2 V|| <=", sup_D2V.str(6))
log("                K <=", K_cert.str(6))
need = arb(10) ** (-14) / (6 * arb(10) ** 198)
OUT["K_required"] = need.str(4)
assert K_cert < need, "K bound insufficient"
log("6e198 * K < 1e-14 : CERTIFIED  (K <", K_cert.str(4), " vs required <", need.str(4), ")")
OUT["prec_solve"], OUT["prec_tail"] = PREC_SOLVE, PREC_TAIL
OUT["time_s"] = round(time.time() - T0, 1)
json.dump(OUT, open("certificate_output.json", "w"), indent=1)
log("ALL FOUR ASSERTIONS CERTIFIED. Output written to certificate_output.json")
