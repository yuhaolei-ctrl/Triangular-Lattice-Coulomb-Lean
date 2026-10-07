"""Shared construction of the auxiliary function for M prescribed shells.

This is verify_lemma21.py (manuscript, Appendix A) with the number M of shells,
the cutoff and the precision as parameters.  P = P_a + z P_b is affine in z, hence
so are A = (P + H)/Omega and B = (1 - t TP)/Omega.
"""
from math import comb
from flint import arb, arb_mat, ctx


def shells(count):
    """first `count` positive values of a^2+ab+b^2."""
    r = 1
    while True:
        vals = sorted({a * a + a * b + b * b for a in range(-r, r + 1) for b in range(-r, r + 1)} - {0})
        lim = 3 * r * r // 4          # every value <= lim is represented with |a|,|b| <= r
        good = [m for m in vals if m <= lim]
        if len(good) >= count:
            return good[:count]
        r *= 2


def laguerre_vals(t, n):
    L = [arb(1), 1 - t]
    for j in range(1, n):
        L.append(((2 * j + 1 - t) * L[j] - j * L[j - 1]) / (j + 1))
    dL = [arb(0)] + [j * (L[j] - L[j - 1]) / t for j in range(1, n + 1)]
    return L, dL


def h_fun(t):
    return (t / 2).exp() * (t / 2).expint(1) / 2


def to_power(c):
    n = len(c)
    out = []
    fact = arb(1)
    for v in range(n):
        if v > 0:
            fact *= v
        s = arb(0)
        for j in range(v, n):
            if c[j] != 0:
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


def poly_add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else arb(0)) + (q[i] if i < len(q) else arb(0)) for i in range(n)]


def poly_scale(p, c):
    return [c * a for a in p]


def poly_eval(p, x):
    s = arb(0)
    for c in reversed(p):
        s = s * x + c
    return s


class Construction:
    """Everything up to A, B, for M shells at the given precision (bits)."""

    def __init__(self, M, prec, verbose=False):
        self.M = M
        self.prec = prec
        ctx.prec = prec
        self.ms = shells(M + 1)
        self.m_next = self.ms[M]
        self.ms = self.ms[:M]
        pi = arb.pi()
        self.alpha = 4 * pi / arb(3).sqrt()
        ts = [self.alpha * m for m in self.ms]
        self.ts = ts
        self.t_next = self.alpha * self.m_next
        N = 4 * M + 1                      # top Laguerre index
        LV = [laguerre_vals(t, N) for t in ts]
        self.LV = LV
        Pl, Fl = {}, {0: {}, 1: {}}
        self.mats = {}
        for par in (0, 1):
            js = [j for j in range(4 * M) if j % 2 == par]
            n = 2 * M
            Mt = arb_mat(n, n)
            rhs = arb_mat(n, 2)
            lead = 4 * M + par
            for i in range(M):
                t = ts[i]
                L, dL = LV[i]
                for c, j in enumerate(js):
                    Mt[2 * i, c] = L[j]
                    Mt[2 * i + 1, c] = dL[j]
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
            self.mats[par] = (Mt, rhs, js)
            X = Mt.solve(rhs, algorithm="precond")   # preconditioned (Rump-type) = the Lean strategy
            for c, j in enumerate(js):
                Pl[j] = X[c, 0]
                Fl[par][j] = X[c, 1]
        NP = 4 * M + 2
        P0 = [Pl.get(j, arb(0)) for j in range(NP)]
        Fe = [Fl[0].get(j, arb(0)) for j in range(NP)]
        Fo = [Fl[1].get(j, arb(0)) for j in range(NP)]
        Fe[4 * M] = arb(1)
        Fo[4 * M + 1] = arb(1)
        self.Fe0, self.Fo0 = sum(Fe), sum(Fo)
        mu = sum(P0[j] * (-1) ** j for j in range(NP))
        self.mu = mu
        # P = P0 + mu [ z Fe/Fe0 + (1+z) Fo/Fo0 ] = Pa + z Pb   (Laguerre coefficients)
        self.Pa = [P0[j] + mu * Fo[j] / self.Fo0 for j in range(NP)]
        self.Pb = [mu * (Fe[j] / self.Fe0 + Fo[j] / self.Fo0) for j in range(NP)]
        self.P0, self.Fe, self.Fo = P0, Fe, Fo
        # Hermite interpolant of h, degree <= 2M-1
        V = arb_mat(2 * M, 2 * M)
        r = arb_mat(2 * M, 1)
        for i, t in enumerate(ts):
            p = arb(1)
            for k in range(2 * M):
                V[2 * i, k] = p
                V[2 * i + 1, k] = k * p / t
                p = p * t
            hv = h_fun(t)
            r[2 * i, 0] = hv
            r[2 * i + 1, 0] = hv / 2 - 1 / (2 * t)
        Hc = V.solve(r)
        self.Hpol = [Hc[k, 0] for k in range(2 * M)]
        Om = [arb(1)]
        for t in ts:
            for _ in range(2):
                Om = poly_add([arb(0)] + Om, poly_scale(Om, -t))
        self.Om = Om
        Pa_p, Pb_p = to_power(self.Pa), to_power(self.Pb)
        TPa_p = to_power([self.Pa[j] * (-1) ** j for j in range(NP)])
        TPb_p = to_power([self.Pb[j] * (-1) ** j for j in range(NP)])
        self.Aa, self.remAa = poly_divide(poly_add(Pa_p, self.Hpol), Om)
        self.Ab, self.remAb = poly_divide(Pb_p, Om)
        self.Ba, self.remBa = poly_divide(poly_add([arb(1)], [arb(0)] + poly_scale(TPa_p, -1)), Om)
        self.Bb, self.remBb = poly_divide([arb(0)] + poly_scale(TPb_p, -1), Om)
        self.Pa_p, self.Pb_p = Pa_p, Pb_p

    def A(self, z):
        return [a + z * b for a, b in zip(self.Aa, self.Ab)]

    def B(self, z):
        return [a + z * b for a, b in zip(self.Ba, self.Bb)]

    def P_lag(self, z):
        return [a + z * b for a, b in zip(self.Pa, self.Pb)]

    def z_interval_coeffwise(self):
        """{z : all coefficients of A_z and B_z > 0} as (lo, hi) floats (midpoints)."""
        lo, hi = None, None      # arb bounds, z in (lo, hi)
        ilo = ihi = None
        for idx, (a, b) in enumerate(list(zip(self.Aa, self.Ab)) + list(zip(self.Ba, self.Bb))):
            # a + z b > 0
            if b > 0:
                v = -a / b
                if lo is None or v > lo:
                    lo, ilo = v, idx
            elif b < 0:
                v = -a / b
                if hi is None or v < hi:
                    hi, ihi = v, idx
            elif not (a > 0):
                return None
        self.z_binding = (ilo, ihi)
        if lo is None or hi is None:
            return (lo, hi)
        return (lo, hi) if lo < hi else None


def poly_shift_arb(p, s):
    """coefficients of p(s + x) in x (ball arithmetic)."""
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
