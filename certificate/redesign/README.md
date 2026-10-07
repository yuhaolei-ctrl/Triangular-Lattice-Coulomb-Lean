# Redesign of the finite certificate (Lemma 10.1) for Lean's kernel

Status: design study, 2026-10-07. Scripts in this folder reproduce every number below
(python-flint 0.9 / Arb; `kernelbench/` contains the scratch Lean benchmarks). Nothing here is
part of the Lean library yet.

## 1. Recommendation in one paragraph

Keep the manuscript's ansatz (A1) and its construction (§10: two parity Hermite systems in the
Laguerre basis, one free parameter `z`), but prescribe only **M = 67 shells** (m ≤ 201) instead of
100. Use **z = −2** and the cutoff χ(t) = I_u(23, 23) (the C²² beta-CDF), u = (t − t_a)/w, on
**[t_a, t_b] = [1458, 1508]**. Here t_67 = 201α = 1458.29 and t_68 = 208α = 1509.08, so every
shell with t ≤ t_b is prescribed. Arb certifies the following for this pair, with the manuscript's
(iii) method and the manuscript's (iv) method plus two simple sharpenings (§4):

| quantity | value |
|---|---|
| coefficients of A (136) and B (137), monomial basis | all > 0; feasible z-interval (−154473, −1.00019) |
| γ (near-contact constant) | 1.3727·10⁻⁴ (minimum at s ≈ 1.865) |
| K (tail size) | ≤ 1.86·10⁻¹⁵² |
| K_max(γ) = 1/(2(2C_tail + C_res)C_def) | 5.79·10⁻¹³⁹ |
| margin K_max / K | **10^13.5** |

Each further shell gains about 3.5 orders of magnitude. M = 64 is the smallest M that passes,
with margin 10^1.9. M = 67 is a good point because the gap 201 → 208 in the shells is large.
In Lean: the solve is verified a posteriori (Rump/Krawczyk with an approximate inverse supplied as
data). Positivity of A and B is certified from **values at 137 negative rational sample points**
plus an explicit Lagrange bound, so there is no monomial conversion and no division by Ω. All
arithmetic is fixed-point dyadic on raw `Nat` primitives. Rounding uses shifts only, never
`Nat.div`/`Nat.mod` on large numbers. The work is split into a few hundred declarations, each at
most about 5·10⁴ arithmetic steps. Estimated total cost: Lean kernel 1–2 min, nanoda about 1 min,
**con-ron 3–8 min (con-ron is the bottleneck)**.

## 2. Threshold (Task 1) — `kmax.py`

`kmax.py` runs the manuscript's `constants.py` unchanged and evaluates

    K_max(γ) = 1 / (2 (2 C_tail + C_res) C_def(R₀, ε₀, γ)) = 4.2214·10⁻¹³⁵ · γ

since C_def ∝ 1/γ. With R₀ = 4.36·10⁵, ε = ε₀(R₀) = 1.50·10⁻³⁶, C_tail = 7.94·10²⁶ and
C_res = 2.0·10⁸:

* γ = 1.37·10⁻⁴: (2C_tail+C_res)C_def = 8.65·10¹³⁷, so K_max = 5.78·10⁻¹³⁹
  (the manuscript says "≈ 10¹³⁸").

`constants.py` uses floating point. The Lean side must evaluate these constants with upward
rounding; that changes K_max only in the last digits. The margin of 10^13.5 also leaves room if
the formalization of Theorem A loosens constants.

## 3. Dependence on M (Task 2) — `lp.py`, `analysis.py`, `scan.py`, `ideal_K.py`

`lp.py` is `verify_lemma21.py` with M as a parameter (nodes = the first M values of
a² + ab + b²). P = P_a + z P_b is affine in z, so A and B are affine in z. The set of z giving
coefficientwise positivity is therefore an exact interval. `analysis.py` contains γ
(Appendix A (iii), unchanged) and K (Appendix A (iv)), with t_a, w, k as parameters.
Cutoff placement is t_b = ⌊t_{M+1}⌋ − 1, t_a = t_b − w.

* Coefficientwise positivity of A and B fails at M = 10 and holds for **every M ≥ 20** tested
  (20…70, 100). The z-interval always has upper end → −1⁻ (the leading coefficient is ∝ −(1+z)) and
  lower end around −10³…−10⁵.
* γ hardly depends on M or z: 1.3816·10⁻⁴ (M=20), 1.3747·10⁻⁴ (M=50), 1.3727·10⁻⁴ (M=67),
  1.3701·10⁻⁴ (M=100, the manuscript's value, reproduced exactly).
* log₁₀(K/K_max):

| M | m_M → m_{M+1} | t_b | manuscript majorants (z=−51/50 or −2, w=50, k=22) | sharpened (§4), z=−2 |
|---|---|---|---|---|
| 20 | 49→52 | 376 | +159.2 | |
| 30 | 79→81 | 586 | +133.1 | |
| 40 | 111→112 | 811 | +105.0 | |
| 50 | 147→148 | 1072 | +72.9 | +46.8 (w=50) |
| 60 | 181→183 | 1326 | +37.8 | +11.8 (w=50) |
| 61 | 183→189 | 1370 | | +7.1 (w=40) |
| 62 | 189→192 | 1391 | | +4.4 |
| 63 | 192→193 | 1399 | | +1.9 |
| 64 | 193→196 | 1421 | | −1.9 |
| 65 | 196→199 | 1442 | | −5.6 |
| 66 | 199→201 | 1457 | | −8.3 |
| **67** | **201→208** | **1508** | | **−12.8 (w=40), −13.5 (w=50)** |
| 68 | 208→211 | 1529 | | −15.6 |
| 69 | 211→217 | 1573 | | −20.7 |
| 70 | 217→219 | 1587 | | −23.2 |
| 100 | 324→325 | 2100 | K = 3.53·10⁻²¹⁵ (reproduced) | |

K is essentially e^{−t_b/2} times a polynomial factor. It decays by **≈ 3.4 orders of magnitude
per shell** and is governed by the next shell t_{M+1}, not by M itself. With the manuscript's own
majorants one needs M ≈ 72. The width w ∈ [30, 70] and the order k ∈ {20, 22} change K by
less than 1.5 orders.

The tail budget is dominated by the Hessian of the Fourier tail K₀ = 𝓕⁻¹a_hi. `ideal_K.py`
evaluates the manuscript's inequalities with the true signed derivatives on a fine grid (not
rigorous). At M=50 this gives D²K₀ ≈ 10⁻⁹⁹·⁵ against 10⁻⁹¹·⁴ with the sharpened majorants and
10⁻⁶⁵ with the manuscript's majorants. The weight (1+|x|)²⁰ with |x|²⁰|K₀| ≤ (2π)⁻²⁰∫|Δ¹⁰a_hi|
costs about 30 orders intrinsically, because a_hi is a thin ring of width ≈ 0.02 in |k|. So no
majorant can push M below about 62 at exponent 20. Lowering the exponent 20 of (A5) (the
manuscript: "any exponent > 8 would do") would save about 15 orders, i.e. about 4 shells, but
changes Theorem A's constants. Not recommended.

## 4. Two sharpenings of the tail bound (rigorous, trivial to formalize)

1. **Cutoff derivatives.** The manuscript bounds sup|χ^{(j)}| by the sum of the absolute values
   of the coefficients of d^{j−1}[u^k(1−u)^k], which overestimates by about 10¹⁸–10²⁰
   (k = 22: c₁ ≈ 10¹⁸·⁹ against the true 10⁻¹·⁰). `chi_bounds_bernstein` replaces this by the
   maximum Bernstein coefficient on 32 pieces of [0,1], in exact rationals. In Lean these are
   23 rational constants c_j, each with a proof via Bernstein nonnegativity and partition of unity.
2. **Weight split.** Replace (1+r)²⁰ ≤ 2¹⁹(1 + r²⁰) by convexity:
   (1+r)²⁰ ≤ (1−λ)⁻¹⁹ + λ⁻¹⁹r²⁰ with λ = r_a/(1+r_a) for q_hi. For K₀, minimizing over λ gives
   (S₀^{1/20} + S₂₀^{1/20})²⁰. This gains about 5 orders.

Together these gain about 26 orders of magnitude, which is the difference between M ≈ 72 and
M = 64.

## 5. Verification design for Lemma 10.1 at M = 67 (Task 3)

Sizes: two parity systems of size n = 2M = 134, each with two right-hand sides; P of degree
4M+1 = 269; A of degree 135, B of degree 136.
Equilibrated ∞-condition numbers of the Laguerre parity matrices: 2⁹⁴ (M=20), 2²⁶⁰ (M=40),
**2⁵¹⁵ (M=67)**. The raw entries span 2⁻⁸…2⁹⁴⁴ and are row-scaled to fixed point.

### Inputs (transcendental enclosures)
* √3: rational bounds a/b with a² < 3b² < (a+1)²; integer squaring only.
* π: Machin's formula with alternating-series remainders (Mathlib has `Real.hasSum_arctan` and
  the alternating-series bounds). About 2000/(2·log₂5) ≈ 430 + 130 terms, each a division by a
  small odd integer: under 10³ big-by-small divisions, ≈ 0.2 s in con-ron.
* α = 4π/√3 and t_i = α m_i: interval operations.
* h(t_i) = ½e^{t_i/2}E₁(t_i/2), h'(t_i) = h/2 − 1/(2t_i), using only h(t) = ∫₀^∞ e^{−s}/(t+2s) ds:
  * at the top node, the asymptotic series with remainder |R_n| ≤ n! 2ⁿ/t^{n+1} (repeated
    integration by parts; ≈ 2000 bits at t = 1458);
  * then step down node by node with the exact geometric-series identity
    h(t₀−δ) = Σ_{k<n} δᵏ I_{k+1}(t₀) + R, 0 ≤ R ≤ (δ/t₀)ⁿ/(t₀−δ), with
    I_{k+1} = (t₀^{−k} − I_k)/(2k);
  * propagate the affine dependence on h(t₀) separately (coefficient ≈ e^{−δ/2}) to avoid
    wrapping.

  No γ_E and no logarithms are needed. Insert intermediate points where δ > t₀/3 (only below
  t ≈ 15). Cost ≈ 67 × 50–150 terms ≈ 10⁴ operations.
* e^{−x} for (iii) and (iv): Mathlib's `Real.exp_bound` on [0,1] plus repeated squaring;
  negligible.

### (i) Nonsingularity and the solution enclosure (Rump/Krawczyk)
Data: an approximate inverse R (134² dyadic numbers per parity, about 700 bits each) and
approximate solutions x̃ (2 × 134 numbers, about 2000 bits).
1. Laguerre values at the nodes, division-free: ℓ_j = j!L_j satisfies
   ℓ_{j+1} = (2j+1−t)ℓ_j − j²ℓ_{j−1}, and L_j' comes from tL_j' = j(L_j − L_{j−1}).
   Cost: 67 × 270 ≈ 1.8·10⁴ steps.
2. Check ‖I − R M_mid‖_∞ + ‖R‖·rad(M) ≤ θ < 1. This is an exact integer product with
   signs kept as (Bool, Nat) or with split ± accumulators: **134³ ≈ 2.4·10⁶ multiply-adds per
   parity, 4.8·10⁶ in total, at ≈ 700 bits** (log₂ cond = 515 plus margin).
   This is the dominant cost. Kronecker packing (one big product per dot product) would cut the
   operation count 100×, but it is **ruled out by con-ron** (§6).
3. The residual r − M x̃ and its image R(r − M x̃) at about 2000 bits: 4 × 134² ≈ 7·10⁴
   operations. Then |x − x̃| ≤ |R(r − M x̃)|/(1−θ) componentwise. Nonsingularity of M follows
   from θ < 1.
4. F_e(0) = Σ e_j and F_o(0) = Σ o_j are bounded away from 0; μ and P are formed in the Laguerre
   basis. (TP)(0) = 0 is exact algebra, not numerics.

### (ii) Positivity of A, B: sample-point certificate (replaces the monomial conversion)
Data: Ã, B̃ with positive dyadic monomial coefficients (from an offline high-precision run),
and N = 2M+3 = 137 negative rational sample points s_k (Chebyshev-like on
[−t_M − 1, −1], denominators 64).
* A(s_k) = P(s_k)/Ω(s_k) + Σ_i [β_i/(s_k−t_i)² + α_i/(s_k−t_i)]. These are the partial fractions
  of H_pol/Ω, with β_i = h(t_i)/Ω_i(t_i) and α_i = (h'(t_i) − h(t_i)Σ_{j≠i}2/(t_i−t_j))/Ω_i(t_i).
  This is barycentric Hermite interpolation, so H_pol itself is never formed.
* B(s_k) = (1 − s_k TP(s_k))/Ω(s_k). One Laguerre recurrence per point gives both P(s_k) and
  TP(s_k), because the coefficients differ only by signs.
* Lagrange: u = Ã − A has degree < N, so u(t) = Σ_k u(s_k)ℓ_k(t). Because every s_m < 0,
  the coefficients of |ℓ_k| are exactly e_{N−1−j}(|s|_{−k})/w_k. Check coefficientwise that
  Ã − Σ_k |u(s_k)| e_{N−1−j}(|s|)/w_k > 0, which gives A > 0 on [0,∞). The same polynomial gives
  the lower bound used in (iii), and Ã + (the same) gives the upper majorant used in (iv). B is
  handled the same way.
* Cost: 137 × 270 ≈ 3.7·10⁴ recurrence steps, plus Ω and partial fractions
  (2 × 137 × 67 ≈ 2·10⁴), plus e_r and w_k (2·10⁴). In total ≈ 1.5·10⁵ multiplications.
* Precision (`precision_study.py`, uniform precision): fails at 1600 bits; **passes at 1800 bits
  with 85 bits of margin** and at 2000 bits with 206 bits. With the manuscript's route
  (monomial conversion, then synthetic division by Ω) one needs 13312 bits at M=100.

Lean soundness needs: Lagrange interpolation (Mathlib `Lagrange`), the Hermite partial-fraction
identity, the bound |t − s_m| = t + |s_m| for t ≥ 0, and "positive coefficients ⇒ positive on
[0,∞)".

### (iii) Near-contact bound
This is the manuscript's method unchanged: 3 × 256 subintervals, monotone factors, J ≥ 0
dropped, and A replaced by the lower polynomial from (ii). About 5·10⁴ interval products at
64–128 bits. γ = 1.3727·10⁻⁴.

### (iv) Tail size
This is the manuscript's method plus the sharpenings of §4. All quantities are upper bounds of
nonnegative-coefficient polynomials. Use dyadic floats (64-bit mantissa, exponent, round up),
because the dynamic range is 10^{±1000}.
* Restructure the final functionals so they act linearly on the polynomials: precompute the
  moments ∫e^{−x/2}xᵛ(t_a+x)ʲ by the recurrence μ_{v,j+1} = t_a μ_{v,j} + μ_{v+1,j}. This avoids
  forming t^jF^{(k)}.
* Cost ≈ 2–5·10⁵ low-precision operations.

### Totals (M = 67)
| part | multiply-adds | bits |
|---|---|---|
| Krawczyk θ-check | 4.8·10⁶ | ≈ 700 |
| everything else (inputs, Laguerre, residual, sample points, γ) | ≈ 3·10⁵ | ≤ 2000 |
| tail bound | ≈ 3·10⁵ | 64-bit floats |

The θ-check precision (about 700 bits, i.e. log₂ cond + margin) is an estimate. The measured
uniform-precision Arb pipeline needs 1800 bits. Running the θ-check at 2000 bits instead is the
conservative fallback and costs about 2.5× in con-ron.

## 6. Kernel calibration (Task 4) — `kernelbench/`

Machine: Apple M-series, 10 cores, 16 GB; Lean v4.35.0-rc3; nanoda_bin 0.4.17; con-ron
(verified mode, `--jobs=1`). Exports use `leanexport Mod -- <thm>`, which contains only the
theorem's dependency closure (about 200 declarations); a full-module export (about 59k
declarations) costs nanoda 25–30 s of baseline.

**Representation matters more than precision in Lean's kernel.** 10⁴ strict steps of
x ↦ x·y + c (interval or modular) at 512 bits:

| encoding | Lean kernel |
|---|---|
| `Int`, `+ * ≤` notation, structural recursion (`KB.lean`, 4-product interval mul) | 13.6 s (1.36 ms/step) |
| `Int` notation, scalar | 2.25 s |
| `Nat` notation | 0.44 s |
| raw `Nat.mul/add/shiftRight/ble`, structural recursion | 0.25 s |
| raw primitives, `Nat.rec` loop | 0.10 s |

**Strictness:** the kernel is call-by-name. A loop state passed on unevaluated becomes a deep
term chain and the cost turns superlinear: 16k steps 0.28 s, 32k 1.16 s, 64k > 300 s. The fix
is to force each new state to a numeral via iota-reduction,
`lit e k := Nat.rec (k 0) (fun v _ => k v) (Nat.add e 1)`. With it, 256k steps take 2.9 s,
which is linear. Every loop in the certificate must use this, or an equivalent match on a numeral.

**Cross-kernel timings** (strict `Nat.rec` loops, values changing at every step):

| benchmark | Lean kernel | nanoda | con-ron |
|---|---|---|---|
| 3·10⁴ × (mul+add+**mod**), 512 bit | 0.35 s | 0.59 s | 5.2 s |
| 3·10⁴ × (mul+add+**mod**), 2048 bit | 0.60 s | 0.72 s | 56 s |
| 10⁵ × (mul+add+mod), 512 bit, single loop | 2.18 s | 2.45 s | **rejected: fuel exhausted (whnf loop)** |
| same, nested 100 × 10³ (inner forced by `lit`) | 2.34 s | 2.31 s | 16.8 s, accepted |
| 6·10⁴ × (mul+**shift**+add), 1024 bit, nested | 1.06 s (17 µs/step) | 0.63 s (10 µs) | 2.26 s (37 µs) |
| 3·10³ × (mul+shift+add), 512 / 2048 bit | – | – | 0.19 / 0.31 s |
| 3·10³ × (mul+add+mod), 512 / 2048 bit | – | – | 0.59 / 4.41 s |
| 2·10³ × big/small `Nat.div`, 2 kbit | – | – | 0.41 s (0.2 ms/step) |
| 10³ × (600-bit × 20-kbit mul + add + mod 2^W) | – | 0.10 s | 61 s |
| 200 × (600-bit × 150-kbit …) | – | 0.11 s | 635 s |
| peak RSS for 10⁵ steps | 0.7 GB | 0.5 GB | 0.6 GB |

The tampered-proof negative control works: changing the expected numeral in the export makes
nanoda fail (`assertion failed: self.def_eq`) and con-ron reject (`application type mismatch`).

Consequences, which are design rules:
1. **con-ron is the bottleneck, and its fuel is per whnf loop.** A single loop of about 10⁵
   iterations exhausts it, while 10 declarations of 2.5·10⁴ steps each, or nested loops, pass.
   Keep every loop at 5·10⁴ iterations or fewer and nest the rest.
2. **No `Nat.div`/`Nat.mod` on large operands.** con-ron's division is slow and superlinear.
   Use fixed point with power-of-two scales: round by `Nat.shiftRight`, and use division-free
   recurrences such as j!L_j. Big-by-small division is acceptable in small numbers (π, h).
3. **No huge integers.** con-ron's cost grows quadratically with operand size (§6 table), so
   Kronecker packing is out. Keep operands ≲ 2000 bits.
4. Memory is about 3 KB per step in Lean (per-declaration caches). Keep declarations at
   ≲ 5·10⁴ steps (≈ 150 MB). Combine the per-chunk facts `chunk_i = true` by rewriting
   (generated `fin_cases`), never by re-evaluation.
5. Signs: use (Bool, Nat) sign-magnitude or split ± accumulators. Never `Int` arithmetic in hot
   loops.

**Projected cost at M = 67** (per-step costs from the table, scaled to the bit sizes):
* Krawczyk check, 4.8·10⁶ multiply-adds at 700 bits: Lean ≈ 60–80 s, nanoda ≈ 40 s,
  con-ron ≈ 150–200 s. At 2000 bits: con-ron ≈ 8 min.
* The rest (≈ 6·10⁵ steps): Lean ≈ 10 s, nanoda ≈ 6 s, con-ron ≈ 30–60 s.
* Declarations: about 270 for the θ-check (one row per declaration, 1.8·10⁴ steps) plus about
  50 others.

## 7. Risks
* **con-ron throughput** sets the schedule. Its per-step cost rises superlinearly with bits.
  Validate the mixed-precision θ-check (≈ 700 bits) before writing the Lean side; it was
  estimated from the condition number, not run in fixed point.
* **con-ron fuel constants** are undocumented; I located the threshold only for one loop shape
  (between 9.2·10⁴ and 10⁵ iterations of `lit`-forced steps). The generator must keep a safety
  factor of at least 2.
* nanoda was fast and lean on memory in every test. The earlier Beckner–Onofri failure
  (15 GB RSS) presumably came from one huge declaration; rule 4 addresses that.
* lean4lean was not tested: the bundled binary reads .olean files, not exports, and fails on
  header mismatch here.
* The positivity margin of the sample-point check is about 85 bits at 1800 bits and grows by
  about 0.6 bit per added bit. Use 2000-bit data for a comfortable margin.
* The tail bound still uses the Δ¹⁰ Fourier argument and all of the manuscript's analysis.
  Formalizing that (Fourier integration by parts in ℝ², radial Laplacian identities,
  harmonic-polynomial identity (A.217)) is the main *mathematical* work of this layer. The
  numerics are cheap.
* Using fewer shells (M ≈ 62–64) would need a sharper tail argument. The margin at M=64 is only
  10^1.9.

## 8. Reproduction
```
PY=<venv>/bin/python                    # python-flint 0.9, mpmath
$PY kmax.py                             # §2
$PY scan.py --M 60 64 67 --z -2 --w 40 50 --tight    # §3 (add no --tight for manuscript majorants)
$PY ideal_K.py 50 -2 50                 # §3, non-rigorous ideal values
$PY precision_study.py 67 1600 1800 2000             # §5 (ii)
cd kernelbench && PATH=<lean-4.35.0-rc3/bin>:$PATH ./run.sh   # §6 (in a scratch copy)
```
`scan_M67.txt` is the output of the final M=67 scan (z ∈ {−101/100, −2, −10}, w ∈ {30, 40, 50}).
