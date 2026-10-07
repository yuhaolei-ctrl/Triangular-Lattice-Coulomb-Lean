#!/usr/bin/env python3
"""Non-rigorous 'ideal' values of the ingredients of the tail bound of Appendix A (iv):
the same inequalities (Fourier integration by parts with Delta^10, harmonic split of the
Hessian, radial Hessian bound), but with the true signed derivatives of q_hi and a_hi,
evaluated on a fine t-grid, instead of the coefficientwise majorants.  This shows how
much of the manuscript's K bound is lost in the majorants.

usage: ideal_K.py M z w [k]
"""
import sys
from math import comb, log10, floor
from flint import arb, arb_series, fmpq, ctx
from lp import Construction
from analysis import lap_coeffs, tail_K, chi_bounds

M = int(sys.argv[1]); zs = sys.argv[2]; w = int(sys.argv[3]); k = int(sys.argv[4]) if len(sys.argv) > 4 else 22
num, den = (zs.split("/") + ["1"])[:2]
C = Construction(M, 150 * M + 1000)
z = arb(fmpq(int(num), int(den)))
A, B = C.A(z), C.B(z)
tb = floor(float(C.t_next.mid())) - 1
ta = tb - w
ctx.prec = 600
ctx.cap = 30
pi = arb.pi()
ORD = 24
Bfac = arb(1)
from math import factorial
Bfac = arb(factorial(2 * k + 1)) / arb(factorial(k)) ** 2
chi_poly = []   # chi(u) = Bfac * sum_i (-1)^i C(k,i) u^{k+i+1}/(k+i+1)
for i in range(k + 1):
    chi_poly.append((k + i + 1, Bfac * comb(k, i) * (-1) ** i / (k + i + 1)))


def chi_series(t0):
    u0 = (t0 - ta) / w
    if u0 >= 1:
        return arb_series([1], prec=ORD)
    u = arb_series([u0, arb(1) / w], prec=ORD)
    s = arb_series([0], prec=ORD)
    for e, c in chi_poly:
        s += c * u ** e
    return s


def series_at(t0):
    x = arb_series([t0, 1], prec=ORD)
    Om = arb_series([1], prec=ORD)
    for t in C.ts:
        d = x - arb(t)
        Om = Om * d * d
    def horner(p):
        s = arb_series([0], prec=ORD)
        for c in reversed(p):
            s = s * x + arb(c)
        return s
    e = (-x / 2).exp()
    q = e * Om * horner(A)          # J (< 1/(t Omega(0))) neglected
    a = e * Om * horner(B) / x
    ch = chi_series(t0)
    return q * ch, a * ch, x


fact = [1]
for i in range(1, 60):
    fact.append(fact[-1] * i)
beta0 = lap_coeffs(10, 0)
beta2 = lap_coeffs(10, 2)


def deriv(s, m):
    return s.coeffs()[m] * fact[m] if m < len(s.coeffs()) else arb(0)


h = arb(1) / 5
n = int(600 * 5)
sup_q = sup_d2q = arb(0)
I0 = I10 = R0 = R10 = H0 = H10 = arb(0)
for i in range(n + 1):
    t0 = arb(ta) + h * i
    qh, ah, x = series_at(t0)
    r = (t0 / (2 * pi)).sqrt()
    wgt = (1 + r) ** 20
    sup_q = max(sup_q, (wgt * abs(deriv(qh, 0))).mid())
    d2 = 4 * pi * abs(deriv(qh, 1)) + 8 * pi * t0 * abs(deriv(qh, 2))
    sup_d2q = max(sup_d2q, (wgt * d2).mid())
    frad = ah * x / (4 * pi)
    lap_a = sum(b * t0 ** j * deriv(ah, kk) for (j, kk), b in beta0.items()) * (8 * pi) ** 10
    lap_r = sum(b * t0 ** j * deriv(frad, kk) for (j, kk), b in beta0.items()) * (8 * pi) ** 10
    lap_h = sum(b * t0 ** j * deriv(ah, kk) for (j, kk), b in beta2.items()) * (8 * pi) ** 10 * t0 / (4 * pi)
    wq = h / 2   # dk = dt/2
    I0 += wq * abs(deriv(ah, 0)); I10 += wq * abs(lap_a)
    R0 += wq * abs(deriv(frad, 0)); R10 += wq * abs(lap_r)
    H0 += wq * abs(deriv(ah, 0)) * t0 / (4 * pi); H10 += wq * abs(lap_h)
tp20 = (2 * pi) ** 20
W19 = arb(2) ** 19
sup_K0 = W19 * (I0 + I10 / tp20)
sup_D2K0 = W19 * 4 * pi ** 2 * (R0 + H0 + (R10 + H10) / tp20)
# better weight split: (1+|x|)^20 |f| <= (S0^{1/20} + S20^{1/20})^20
split = lambda a0, a20: (a0 ** (arb(1) / 20) + a20 ** (arb(1) / 20)) ** 20
sup_K0s = split(I0, I10 / tp20)
sup_D2K0s = 4 * pi ** 2 * split(R0 + H0, (R10 + H10) / tp20)
lg = lambda v: float(abs(v).mid().log()) / 2.302585092994046 if abs(v).mid() > 0 else -999
print(f"M={M} z={zs} w={w} k={k} t_a={ta} t_b={tb}")
print(f"  ideal (paper's inequalities, true derivatives):  qhi {lg(sup_q):.1f}  D2qhi {lg(sup_d2q):.1f}  "
      f"K0 {lg(sup_K0):.1f}  D2K0 {lg(sup_D2K0):.1f}")
print(f"  ideal with weight split (S0^(1/20)+S20^(1/20))^20:  K0 {lg(sup_K0s):.1f}  D2K0 {lg(sup_D2K0s):.1f}")
Kc, parts = tail_K(C, A, B, ta, w, k=k, prec=2048)
print(f"  manuscript majorants: qhi {lg(parts['sup_qhi']):.1f}  D2qhi {lg(parts['sup_D2qhi']):.1f}  "
      f"K0 {lg(parts['sup_K0']):.1f}  D2K0 {lg(parts['sup_D2K0']):.1f}   K {lg(Kc):.1f}")
