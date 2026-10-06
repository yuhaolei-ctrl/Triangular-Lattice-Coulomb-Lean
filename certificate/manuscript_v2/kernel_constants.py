"""Explicit constants for the kernel bounds (Lemma 6.4 / Appendix B)."""
from fractions import Fraction as Fr
from math import comb, pi, factorial
C = [Fr(6)]
for m in range(1, 6):
    C.append(6 * sum(comb(m, j) * C[m - j] for j in range(1, m + 1)))
B = [sum(Fr(comb(m, j)) * C[m - j] / factorial(6 - j) for j in range(m + 1)) for m in range(6)]
Bth = [B[m + 1] + m * B[m] for m in range(5)]   # angular derivative: (B_{m+1} + m B_m)|xi|^{4-m}
print("C_m =", C)
print("B_m =", B, [float(b) for b in B])
print("B^theta_m =", Bth)
# rescaled symbol: kappa in |kappa|<9, xi = 2 pi l kappa / R, 2 pi l < 7
# |D^m_kappa [R^4 F(xi)]| <= 7^m * B_m * |xi|^{4-m} R^{4-m} ... = 7^4 9^{4-m} B_m
def Dm(Bs):
    return [sum(comb(m, j) * 16 * 2 ** j * 7 ** 4 * 9 ** (4 - m + j) * Bs[m - j] for j in range(m + 1)) for m in range(5)]
D = Dm(B); E = Dm(Bth)
print("D_m =", D, [float(d) for d in D])
print("E_m =", E, [float(e) for e in E])
# |K| (1+|y|)^4 <= 8 * 144 * ( D0 + 4 D4/(2pi)^4 ) R^{-6}
K0 = 8 * 144 * (float(D[0]) + 4 * float(D[4]) / (2 * pi) ** 4)
Kth = 8 * 144 * (float(E[0]) + 4 * float(E[4]) / (2 * pi) ** 4)
# gradient: symbol 2 pi i kappa_i B / R ; |kappa_i B| <= 9 D0 ; d^4(kappa_i B) <= 9 D4 + 4 D3
G0 = 2 * pi * 8 * 144 * (9 * float(D[0]) + 4 * (9 * float(D[4]) + 4 * float(D[3])) / (2 * pi) ** 4)
Gth = 2 * pi * 8 * 144 * (9 * float(E[0]) + 4 * (9 * float(E[4]) + 4 * float(E[3])) / (2 * pi) ** 4)
print("sup (1+|y|)^4 R^6 |K|      <= %.3e" % K0)
print("sup (1+|y|)^4 R^6 |d_th K| <= %.3e" % Kth)
print("sup (1+|y|)^4 R^7 |grad K| <= %.3e  (both components: x sqrt2 -> %.3e)" % (G0, G0*2**0.5))
print("sup (1+|y|)^4 R^7 |d_th grad K| <= %.3e  (x sqrt2 -> %.3e)" % (Gth, Gth*2**0.5))
print("sum K + d_th K <= %.3e ; grad + d_th grad <= %.3e" % (K0+Kth, (G0+Gth)*2**0.5))
