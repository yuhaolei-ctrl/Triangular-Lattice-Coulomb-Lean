#!/usr/bin/env python3
"""
Explicit evaluation of the constants of the rigidity theorem (Appendix C).
Every constant below is defined by the formula proved in the indicated lemma;
the script only evaluates the formulas (with rounding up) and checks the final
inequality  (2 C_tail + C_res) * C_def * K <= 1/2.
"""
from fractions import Fraction as Fr
from math import pi, sqrt, ceil, log10

ell = sqrt(2 / sqrt(3))                      # lattice constant
rows = []
def rec(name, val, where, formula):
    rows.append((name, val, where, formula))
    return val

# --- geometry of the lattice and of the cells (Section 5) --------------------
rho0  = rec(r"\rho_0", 2.1, "\\eqref{eq:tconv}", r"\text{any number in }(2,\sqrt7)")
eps_geo = rec(r"\varepsilon_{\mathrm{geo}}", 1e-8, r"\eqref{eq:epsgeo}", r"10^{-8}")
A_dir = rec(r"A_{\mathrm{dir}}", 140, "Lemma~\\ref{lem:directional}", r"40\sqrt{12}\le 140")
A_dirp= rec(r"A'_{\mathrm{dir}}", 6, "Lemma~\\ref{lem:directional}", r"\pi\sqrt{3.5}\le 6")
m_e   = rec(r"m_e", 4, "Lemma~\\ref{lem:directional}", r"4")
C_kap = rec(r"C_\kappa", 32 * (2 + m_e * A_dir**2), "Lemma~\\ref{lem:cells}", r"32(2+m_eA_{\mathrm{dir}}^2)")
C_Del = rec(r"C_\Delta", 12 * m_e * A_dir**2, "Lemma~\\ref{lem:cells}", r"12\,m_eA_{\mathrm{dir}}^2")
C_err = rec(r"C_{\mathrm{err}}", 6 * ell**2 * (1 + A_dir)**2 * m_e, "Lemma~\\ref{lem:cells}", r"6\lat^2(1+A_{\mathrm{dir}})^2m_e")
h     = rec(r"h", (1/sqrt(3) - 0.5) * ell, "Lemma~\\ref{lem:holes}", r"(1/\sqrt3-1/2)\lat")
m_hole= rec(r"m_{\mathrm{hole}}", 60, "Lemma~\\ref{lem:holes}", r"60")

# --- filter and separated-point estimates (Section 6) ------------------------
A_eta = rec(r"A_\eta", 256, "\\eqref{eq:eta-bounds}", r"256")
c_eta = rec(r"c_\eta", 0.25, "\\eqref{eq:eta-bounds}", r"1/4")
c_sep = rec(r"c_{\mathrm{sep}}", 8, "Lemma~\\ref{lem:separated}", r"(3/2)^4\cdot(4/\pi)\cdot(\pi/3)\le 8")
I4    = rec(r"I_4", pi / 3, "Lemma~\\ref{lem:separated}", r"\pi/3")
C_Sch = rec(r"C_{\mathrm{Sch}}", c_sep * I4, "Lemma~\\ref{lem:separated}", r"c_{\mathrm{sep}}I_4")
c_hole= rec(r"c_{\mathrm{hole}}", (pi * h**2 * c_eta)**2 * pi / 256 / m_hole**2, "Lemma~\\ref{lem:holemass}", r"(\pi h^2c_\eta)^2\pi/(256\,m_{\mathrm{hole}}^2)")
C_rem = rec(r"C_{\mathrm{rem}}", (2 * A_eta * I4)**2 * 100, "Lemma~\\ref{lem:removedmass}", r"(2A_\eta I_4)^2\cdot 100")
C_shr = rec(r"C_{\mathrm{shr}}", C_Sch * (4 * A_eta)**2, "\\eqref{eq:thresholds}", r"C_{\mathrm{Sch}}(4A_\eta)^2")
A_K   = rec(r"A_K", 1e13, "Lemma~\\ref{lem:kernel}", r"10^{13}")
C_or  = rec(r"C_{\mathrm{or}}", 3 * C_Sch * 6 * (2 * A_K)**2 / 36 * max(4 * ell**2 * C_Del + C_err, 6 * ell**2 + 4*ell**2*C_Del + C_err),
            "Lemma~\\ref{lem:orient}", r"2C_{\mathrm{Sch}}A_K^2\,(4\lat^2C_\Delta+C_{\mathrm{err}}+6\lat^2)")
# absorption thresholds
R0    = rec(r"R_0", max(64.0, (16 * C_or / c_hole)**(1/8)), "\\eqref{eq:thresholds}", r"\max\{64,(16C_{\mathrm{or}}/c_{\mathrm{hole}})^{1/8}\}")
def eps0(R): return c_hole * R**-2 / (16 * C_shr * C_kap)
rec(r"\varepsilon_0(R)", eps0(R0), "\\eqref{eq:thresholds}", r"c_{\mathrm{hole}}R^{-2}/(16C_{\mathrm{shr}}C_\kappa)\ \ (\text{at }R=R_0)")

# --- development and tail (Sections 7-8) -------------------------------------
N_tri = rec(r"N_{\mathrm{tri}}", 34, "Lemma~\\ref{lem:development}", r"34")
C_dev = rec(r"C_{\mathrm{dev}}", 2 * sqrt(128 * N_tri) + 3, "Lemma~\\ref{lem:development}", r"2\sqrt{128N_{\mathrm{tri}}}+3")
theta0= rec(r"\theta_0", 0.1, "Definition~\\ref{def:good}", r"1/10")
N_cnt = rec(r"N_{\mathrm{cnt}}", 52, "Corollary~\\ref{cor:counts}", r"52")
N_def = rec(r"N_{\mathrm{def}}", 26, "Corollary~\\ref{cor:counts}", r"26")
N_Lam = rec(r"N_\Lambda", 42, "Lemma~\\ref{lem:expansion}", r"\pi(3+\lat/\sqrt3)^2\le 42")
N_anc = rec(r"N_{\mathrm{anc}}", 121, "Proposition~\\ref{prop:cancellation}", r"4(5+1/2)^2=121")
C_h   = rec(r"C_h", 2001 * 2**20, "\\eqref{eq:72}", r"2001\cdot 2^{20}")
# per-scale constants with R = 8 r, R' = 32 r
rho_R = 8
C_bad = 50 * (N_def * rho_R**2 + N_cnt * C_dev**2 / theta0**2 * rho_R**3)        # r^5 h_j (S+D)
C_exp = 168 * N_Lam * C_dev**2                                                  # r^5 h_j S_p
C_nl  = C_exp * N_cnt * rho_R**2                                                 # r^7 h_j S_nn
C_exc = 6 * (N_def * (4 * rho_R)**2 + N_cnt * C_dev**2 / theta0**2 * (4 * rho_R)**3)   # r^3 (S+D)
C_coef= N_anc * N_Lam * 2                                                          # r^4 h_j
C_rep = 2 * C_coef * 2 * C_exc                                                     # r^7 h_j (S+D), |delta_f| <= 2
C_scale = 0.5 * (C_bad + C_nl + C_rep)
rec(r"C_{\mathrm{bad}}", C_bad, "Lemma~\\ref{lem:badanchors}", r"50\,(N_{\mathrm{def}}\,8^2+N_{\mathrm{cnt}}C_{\mathrm{dev}}^2\theta_0^{-2}8^3)")
rec(r"C_{\mathrm{exp}}", C_exp, "Lemma~\\ref{lem:expansion}", r"168\,N_\Lambda C_{\mathrm{dev}}^2")
rec(r"C_{\mathrm{nl}}", C_nl, "\\eqref{eq:nl}", r"64\,C_{\mathrm{exp}}N_{\mathrm{cnt}}")
rec(r"C_{\mathrm{exc}}", C_exc, "Proposition~\\ref{prop:cancellation}", r"6\,(N_{\mathrm{def}}32^2+N_{\mathrm{cnt}}C_{\mathrm{dev}}^2\theta_0^{-2}32^3)")
rec(r"C_{\mathrm{coef}}", C_coef, "Proposition~\\ref{prop:cancellation}", r"2N_{\mathrm{anc}}N_\Lambda")
rec(r"C_{\mathrm{rep}}", C_rep, "\\eqref{eq:rep}", r"4C_{\mathrm{coef}}C_{\mathrm{exc}}")
rec(r"C_{\mathrm{scale}}", C_scale, "\\eqref{eq:710}", r"\tfrac12(C_{\mathrm{bad}}+C_{\mathrm{nl}}+C_{\mathrm{rep}})")
C_tail = rec(r"C_{\mathrm{tail}}", C_scale * C_h * 1 / (1 - 2**-13), "\\eqref{eq:Ctail}", r"C_{\mathrm{scale}}C_h\sum_{j\ge0}2^{-13j}")
C_res  = rec(r"C_{\mathrm{res}}", 24 + 2e8, "Lemma~\\ref{lem:restore}", r"24+2\cdot 10^8")

# --- defect constant and final check (Section 9) -------------------------------
def C_def(R, eps, gamma):
    # D <= (2R^2/c_hole) [16 L_spec + (64 C_rem + 4 C_shr C_kap + 4 C_or R^-10)/(gamma eps^2) Q]
    cD_Q = (2 * R**2 / c_hole) * (64 * C_rem + 4 * C_shr * C_kap + 4 * C_or * R**-10) / (gamma * eps**2)
    cD_L = (2 * R**2 / c_hole) * 16
    # S_nn + D + J_C <= C_def * L,  with  L >= 2Q + L_spec,  S <= Q/gamma,  J_C <= 4Q/(gamma eps^2)
    return max(cD_L, (cD_Q + 1 / gamma + 4 / (gamma * eps**2)) / 2)

gamma = 1.37e-4
K = 3.54e-215
R = R0
eps = min(eps_geo, eps0(R))
Cd = C_def(R, eps, gamma)
rec(r"C_{\mathrm{def}}(R_0,\varepsilon,\gamma)", Cd, "\\eqref{eq:Cdef}", r"\eqref{eq:Cdef}")
final = (2 * C_tail + C_res) * Cd * K
rec(r"(2C_{\mathrm{tail}}+C_{\mathrm{res}})\,C_{\mathrm{def}}\,K", final, "Theorem~\\ref{thm:periodic}", r"")

def fmt(v):
    if v == 0: return "0"
    e = int(ceil(log10(abs(v)))) - 1
    m = v / 10**e
    if abs(v) < 1e4 and abs(v) >= 1e-3 and float(v).is_integer():
        return f"{int(v)}"
    if abs(v) < 1e4 and abs(v) >= 1e-2:
        return f"{v:.4g}"
    # round mantissa up to 3 significant digits (upper bound)
    m3 = ceil(m * 100) / 100
    if m3 >= 10: m3, e = 1.0, e + 1
    return f"{m3:.2f}\\cdot 10^{{{e}}}"

with open("constants_table.tex", "w") as f:
    f.write("\\begin{tabular}{llll}\\toprule\nconstant & where & expression & value (rounded up)\\\\\\midrule\n")
    for name, val, where, formula in rows:
        f.write(f"${name}$ & {where} & ${formula}$ & ${fmt(val)}$\\\\\n")
    f.write("\\bottomrule\\end{tabular}\n")
for name, val, where, formula in rows:
    print(f"{name:40s} {fmt(val):>20s}   [{where}]")
print("\nR_0 =", R0, " eps =", eps, " gamma =", gamma, " K =", K)
print("final product =", final, "  <= 1/2 :", final <= 0.5)
assert final <= 0.5
