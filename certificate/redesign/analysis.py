"""Near-contact constant gamma and tail size K of the pair (q, chi), following
Appendix A (iii), (iv) of the manuscript, for general M, z and cutoff.

gamma_bound: Appendix A (iii) (A positive coefficientwise, J >= 0 dropped).
tail_K:      Appendix A (iv) with t_a, width w = t_b - t_a and chi built from
             u^k (1-u)^k; all majorants as in verify_lemma21.py.
"""
from math import comb
from flint import arb, arb_poly, ctx
from lp import poly_eval, poly_shift_arb


def gamma_bound(C, A, nsub=256, prec=2048):
    old = ctx.prec
    ctx.prec = prec
    s3 = arb(3).sqrt()
    S = [arb(1), s3, arb(2)]
    VOR = [(arb(0), (1 + s3) / 2), ((1 + s3) / 2, (s3 + 2) / 2), ((s3 + 2) / 2, arb(21) / 10)]
    A2 = [arb(c) for c in A]
    ts = [arb(t) for t in C.ts]
    al = arb(C.alpha)
    best, where = None, None
    for i, (lo, hi) in enumerate(VOR):
        si = S[i]
        for n in range(nsub):
            s_lo = lo + (hi - lo) * n / nsub
            s_hi = lo + (hi - lo) * (n + 1) / nsub
            t_lo, t_hi = al * s_lo ** 2, al * s_hi ** 2
            val = (-t_hi / 2).exp() * al ** 2 * (s_lo + si) ** 2 * poly_eval(A2, t_lo)
            for j, tj in enumerate(ts):
                if j == i:
                    continue
                assert not (t_lo < tj and tj < t_hi)
                val *= min((t_lo - tj) ** 2, (t_hi - tj) ** 2)
            lb = val.lower()
            if best is None or lb < best:
                best, where = lb, float(((s_lo + s_hi) / 2).mid())
    ctx.prec = old
    return best, where


def _nonneg(p):
    return arb_poly([abs(c).upper() if c != 0 else arb(0) for c in p.coeffs()])


def _sup_ex(M, E):
    s = arb(0)
    for j, c in enumerate(M.coeffs()):
        s += c * ((2 * arb(j) / E) ** j if j > 0 else 1)
    return s.upper()


def _int_ex(M):
    s = arb(0); f = arb(1)
    for j, c in enumerate(M.coeffs()):
        if j > 0:
            f *= j
        s += c * 2 ** (j + 1) * f
    return s.upper()


def _derivs(p, n):
    out = [p]
    for _ in range(n):
        out.append(out[-1].derivative())
    return out


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


def chi_bounds(w, k, jmax):
    """c_j >= sup |chi^{(j)}|, chi = I_u(k+1,k+1), u = (t - t_a)/w (Appendix A (iv))."""
    pu = [arb(0)] * (2 * k + 1)
    for i in range(k + 1):
        pu[k + i] += comb(k, i) * (-1) ** i
    fact = [arb(1)]
    for i in range(1, 2 * k + 3):
        fact.append(fact[-1] * i)
    Beta = fact[k] * fact[k] / fact[2 * k + 1]
    c = [arb(1)]
    pd = arb_poly(pu)
    for j in range(1, jmax + 1):
        if j - 1 > 2 * k:
            c.append(arb(0)); continue
        sup_pd = sum(abs(x) for x in pd.coeffs()) if pd.degree() >= 0 else arb(0)
        c.append((sup_pd / (Beta * arb(w) ** j)).upper())
        pd = pd.derivative()
    return c


def chi_bounds_bernstein(w, k, jmax, pieces=32):
    """rigorous c_j >= sup |chi^{(j)}| from Bernstein coefficients on `pieces` subintervals
    of [0,1] (exact rational arithmetic), divided by w^j."""
    from flint import fmpq_poly, fmpq
    from math import factorial
    p = fmpq_poly([0] * k + [comb(k, i) * (-1) ** i for i in range(k + 1)])
    Bfac = fmpq(factorial(2 * k + 1), factorial(k) ** 2)
    c = [arb(1)]
    pd = p
    for j in range(1, jmax + 1):
        n = pd.degree()
        best = fmpq(0)
        if n >= 0:
            for r in range(pieces):
                a, b = fmpq(r, pieces), fmpq(r + 1, pieces)
                # q(s) = pd(a + (b-a) s): Taylor shift then scale
                q = pd(fmpq_poly([a, b - a]))
                cs = [q[i] for i in range(n + 1)]
                for i in range(n + 1):
                    bi = sum(fmpq(comb(i, jj), comb(n, jj)) * cs[jj] for jj in range(i + 1))
                    if abs(bi) > best:
                        best = abs(bi)
        c.append((arb(best * Bfac) / arb(w) ** j).upper())
        pd = pd.derivative()
    return c


def tail_K(C, A, B, t_a, w, k=22, prec=4096, maxd=22, tight=False):
    """Rigorous (ball) upper bound on K(q, chi) by the method of Appendix A (iv).
    maxd = highest derivative of a_hi used (20 for Delta^10 plus 2 for the Hessian is
    what the manuscript allows for; derivatives > 20 enter only F_rad's lower terms)."""
    old = ctx.prec
    ctx.prec = prec
    pi = arb.pi()
    E = arb(1).exp()
    T = arb(t_a)
    e_ta = (-T / 2).exp()
    MAXD = maxd + 1
    fact = [arb(1)]
    for i in range(1, 80):
        fact.append(fact[-1] * i)
    P = lambda lst: arb_poly([arb(c) for c in lst])
    ts = [arb(t) for t in C.ts]
    Omt = P([1])
    for t in ts:
        c = abs(T - t)
        Omt = Omt * P([c * c, 2 * c, 1])
    Omt = _nonneg(Omt)
    Om0_lo = poly_eval([arb(c) for c in C.Om], arb(0)).lower()
    A_sh = _nonneg(P(poly_shift_arb([arb(c) for c in A], T)))
    B_sh = _nonneg(P(poly_shift_arb([arb(c) for c in B], T)))
    OmA = _derivs(Omt * A_sh, MAXD)
    OmB = _derivs(Omt * B_sh, MAXD)
    Omd = _derivs(Omt, MAXD)
    J_d = [(fact[c] / (T ** (c + 1) * Om0_lo)).upper() for c in range(MAXD + 1)]
    it_d = [(fact[c] / T ** (c + 1)).upper() for c in range(MAXD + 1)]

    def OmAJ(d):
        p = OmA[d]
        for b in range(d + 1):
            p = p + Omd[b] * (comb(d, b) * J_d[d - b])
        return p

    def with_exp(parts_fn, m, scal_fn=None):
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

    Q_maj = [with_exp(OmAJ, m) for m in range(3)]
    a_maj = [with_exp(lambda d: OmB[d], m, lambda c: it_d[c]) for m in range(MAXD)]
    c_chi = chi_bounds_bernstein(w, k, MAXD) if tight else chi_bounds(w, k, MAXD)

    def chi_times(maj, m):
        out = P([0])
        for j in range(m + 1):
            out = out + maj[m - j] * (comb(m, j) * c_chi[j])
        return out

    qhi = [chi_times(Q_maj, m) for m in range(3)]
    ahi = [chi_times(a_maj, m) for m in range(MAXD)]
    if tight:
        # (1+r)^20 <= (1-l)^-19 + l^-19 r^20 (convexity), l = r_a/(1+r_a), r^20 = (t/2pi)^10
        ra = (T / (2 * pi)).sqrt()
        lam = ra / (1 + ra)
        Wt = P([(1 - lam) ** -19]) + _nonneg(P(poly_shift_arb([arb(0)] * 10 + [lam ** -19 * (1 / (2 * pi)) ** 10], T)))
        W19 = arb(1)
    else:
        Wt = P([1]) + _nonneg(P(poly_shift_arb([arb(0)] * 10 + [(1 / (2 * pi)) ** 10], T)))
        W19 = arb(2) ** 19
    tpoly = P([T, 1])
    sup_qhi = (W19 * e_ta * _sup_ex(Wt * qhi[0], E)).upper()
    hess_q = qhi[1] * (4 * pi) + tpoly * qhi[2] * (8 * pi)
    sup_D2qhi = (W19 * e_ta * _sup_ex(Wt * hess_q, E)).upper()

    def int_abs_lap(F, n, dharm, extra_t=0):
        beta = lap_coeffs(n, dharm)
        tot = P([0])
        for (j, kk), b in beta.items():
            tot = tot + tpoly ** (j + extra_t) * F[kk] * b
        scale = (8 * pi) ** n * (1 / (4 * pi)) ** extra_t / 2
        return (scale * e_ta * _int_ex(tot)).upper()

    I0 = int_abs_lap(ahi, 0, 0)
    I10 = int_abs_lap(ahi, 10, 0)
    split = lambda a0, a20: ((a0 ** (arb(1) / 20) + a20 ** (arb(1) / 20)) ** 20).upper()
    if tight:
        sup_K0 = split(I0, I10 / (2 * pi) ** 20)
    else:
        sup_K0 = (W19 * (I0 + I10 / (2 * pi) ** 20)).upper()
    F_rad = []
    for m in range(MAXD):
        pm = tpoly * ahi[m] * (1 / (4 * pi))
        if m >= 1:
            pm = pm + ahi[m - 1] * (m / (4 * pi))
        F_rad.append(pm)
    R0 = int_abs_lap(F_rad, 0, 0)
    R10 = int_abs_lap(F_rad, 10, 0)
    H0 = int_abs_lap(ahi, 0, 2, extra_t=1)
    H10 = int_abs_lap(ahi, 10, 2, extra_t=1)
    if tight:
        sup_D2K0 = (4 * pi ** 2 * split(R0 + H0, (R10 + H10) / (2 * pi) ** 20)).upper()
    else:
        sup_D2K0 = (W19 * 4 * pi ** 2 * (R0 + H0 + (R10 + H10) / (2 * pi) ** 20)).upper()
    parts = dict(sup_qhi=sup_qhi, sup_D2qhi=sup_D2qhi, sup_K0=sup_K0, sup_D2K0=sup_D2K0)
    K = (sup_qhi + sup_K0 + sup_D2qhi + sup_D2K0).upper()
    ctx.prec = old
    return K, parts
