# Layer 2: the Green function of Λ, the canonical field and the energy per cell

Design note for the modules `Green/*` and `Energy/*`. Notation: `Λ` is the triangular lattice of
covolume one, `Λ*` its dual, `q₀(x) = ½ E₁(π|x|²)` (`TriangularLattice.ewaldKernel`),
`a₀(k) = e^{-π|k|²} / (2π|k|²)`. These modules prove the first three compared statements of
`Challenge.lean`.

## 1. The distributional Laplacian of q₀

**Lemma 1.1.** For every test function `φ`,
`∫ q₀ Δφ = 2π (∫ e^{-π|x|²} φ(x) dx − φ(0))`.

*Proof (reduces everything to Gaussians).* By `integral_mul_ewaldKernel` (Fubini in `u`, applied
to the bounded continuous weight `Δφ / ‖Δφ‖_∞`),
`∫ q₀ Δφ = ½ ∫₁^∞ u⁻¹ ∫ e^{-πu|x|²} Δφ(x) dx du`. Integrating by parts twice (Gaussians times
test functions; `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`),
`∫ e^{-πu|x|²} Δφ = ∫ Δ_x(e^{-πu|x|²}) φ`, and pointwise
`u⁻¹ Δ_x e^{-πu|x|²} = (4π² u|x|² − 4π) e^{-πu|x|²} = −4π ∂_u (u e^{-πu|x|²})`.
Hence `∫ q₀ Δφ = −2π ∫₁^∞ ∂_u [∫ u e^{-πu|x|²} φ(x) dx] du = −2π (φ(0) − ∫ e^{-π|x|²} φ)`, using
that `u e^{-πu|x|²}` is an approximate identity as `u → ∞` (`∫ u e^{-πu|x|²} dx = 1`). ∎

The same computation with `∇` gives `∫ ∇q₀ · ∇φ = −∫ q₀ Δφ` (both sides via the `u`-integral), so
`E = −∇q₀` has `div E = 2π(δ₀ − e^{-π|x|²})` in the weak sense used in `IsAdmissible`.

## 2. The Ewald Green function

**Definition 2.1.** For `x ∉ Λ`,
`G(x) = ∑_{λ∈Λ} q₀(x − λ) − ½ + ∑_{k∈Λ*∖0} a₀(k) cos(2π k·x)`; both series converge absolutely and
locally uniformly on `Λᶜ` (Gaussian decay; `Basic/Lattice` counting bounds). Put `G = 0` on `Λ`.

**Proposition 2.2.** `G` satisfies `IsGreenFunction`.
* Periodicity: reindex both sums.
* Continuity off `Λ`: locally uniform convergence and `continuousOn_ewaldKernel`.
* Local integrability: `q₀(x) ≤ −log|x| + C` near `0` (`ewaldKernel_add_log_sub_mem_Icc`) and
  boundedness elsewhere on compacts.
* Zero average: `∫_cell ∑_λ q₀(x − λ) dx = ∫_{ℝ²} q₀ = ½` (unfolding, `integral_ewaldKernel`), and
  `∫_cell cos(2π k·x) dx = 0` for `k ∈ Λ*∖0`.
* Laplacian: by Lemma 1.1 translated to each `λ`, and `∫ cos(2πk·x) Δφ = −4π²|k|² ∫ cos(2πk·x) φ`,
  `∫ G Δφ = 2π ∑_λ (∫ e^{-π|y−λ|²} φ(y) dy − φ(λ)) − 2π ∑_{k≠0} e^{-π|k|²} ∫ cos(2πk·y) φ(y) dy`;
  Poisson summation for the Gaussian, `∑_λ e^{-π|y−λ|²} = ∑_{k∈Λ*} e^{-π|k|²} cos(2πk·y)`, turns
  this into `2π (∫ φ − ∑_λ φ(λ))`. All interchanges are justified by absolute convergence and the
  compact support of `φ`.

**Proposition 2.3 (Robin constant).** `G(x) + log|x| → R_Λ` as `x → 0`, with
`R_Λ = c₀ + ∑_{λ≠0} q₀(λ) − ½ + ∑_{k≠0} a₀(k)`, `c₀ = ewaldConst`.

**Proposition 2.4 (uniqueness).** If `G'` satisfies `IsGreenFunction`, then `G' = G` on `Λᶜ`.
*Proof.* `F = G' − G` is periodic, locally integrable, with `∫ F Δφ = 0` for all test `φ` and zero
average. Testing against `φ = ψ · e^{2πik·x}`-type functions shows that its torus Fourier
coefficients satisfy `|k|² F̂(k) = 0`, so `F̂(k) = 0` for `k ≠ 0`, and `F̂(0) = 0` by the zero
average; hence `F = 0` a.e., and `F` is continuous on the open set `Λᶜ`, so `F = 0` there. (Use a
periodization of a test function: for `χ` a smooth compactly supported partition-of-unity function
with `∑_λ χ(x − λ) = 1`, test with `φ(x) = χ(x) e^{-2πik·x}`; the real and imaginary parts are test
functions.) ∎

## 3. The canonical field

**Definition 3.1.** `E_Λ = −∇G` off `Λ`, `0` on `Λ`.

**Proposition 3.2.** `E_Λ` satisfies `IsCanonicalField`.
* Admissibility: `Λ` is locally finite with bounded density; `|E_Λ(x)| ≤ C/|x − λ|` near each `λ`
  gives local integrability; the weak divergence follows from §1 termwise (and the Fourier part),
  the weak curl vanishes because `E_Λ` is a gradient of a function that is `W^{1,1}_loc` (or again
  termwise through the `u`-representation).
* Periodicity and zero average: `∫_cell ∇G = 0` by periodicity.

**Proposition 3.3 (uniqueness up to null sets).** If `E₀` satisfies `IsCanonicalField`, then
`E₀ = E_Λ` a.e. *Proof.* As in 2.4: `D = E₀ − E_Λ` is periodic, locally integrable, weakly
divergence- and curl-free with zero average; its Fourier coefficients satisfy `k · D̂(k) = 0` and
`k^⊥ · D̂(k) = 0`, so `D̂(k) = 0` for `k ≠ 0`, and `D̂(0) = 0`. ∎

## 4. The energy per cell and `W_U(E_Λ) = π R_Λ`

**Proposition 4.1 (core decomposition, (11.finitepart)).** Fix `r₀ = ℓ/4`. Near each `λ`,
`E_Λ(x) = (x − λ)/|x − λ|² − π(x − λ) + ∇h(x − λ)` with `h` smooth (from Definition 2.1:
`h = −(G + log|·|)` restricted to `B(0, r₀)` is smooth because `q₀ + log|·|` is smooth — via
`E₁(y) + log y = c + ∫₀^y (1 − e^{-v})/v dv`, an entire function of `y`). For every Lipschitz
compactly supported `χ`, the limit (1.2) exists and
`W(E_Λ, χ) = ∫ χ dμ + ½ ∑_λ ∫_{B(λ, r₀)} (χ(x) − χ(λ)) / |x − λ|² dx`,
where `μ` is the periodic signed measure with density `½|E_Λ|²` off the cores,
`½(|E_Λ|² − |x − λ|⁻²)` in `B(λ, r₀)`, and an atom `π log r₀` at each `λ`.

**Proposition 4.2 (energy per cell).** `μ(cell) = π R_Λ`.
*Proof without a divergence theorem on a punctured cell.* Let `ψ_η(x) = ψ(|x|/η)` with `ψ` smooth,
`0` on `[0, 1]`, `1` on `[2, ∞)`, and periodize `Ψ_η = ∏`-free: `Ψ_η(x) = ψ_η(x − λ)` on the cell
containing only the core at `λ`. On the torus, `Ψ_η ∇G` is smooth, so
`∫_cell Ψ_η |∇G|² = −∫_cell G div(Ψ_η ∇G) = −∫_cell G ∇Ψ_η · ∇G − 2π ∫_cell Ψ_η G` (the integral of
the divergence of a smooth periodic field over a cell vanishes, e.g. by Fourier coefficients or
FTC on the parallelogram; `ΔG = 2π` off `Λ`). The first term lives in the annulus `η < |x| < 2η`,
where `G = −log|x| + R_Λ + O(|x|)` and `∇G = −x/|x|² + O(1)`; explicit radial integrals give
`−∫ G ∇Ψ_η · ∇G = 2π(−log η + R_Λ) − 2πκ + o(1)` with `κ = ∫₁² log s ψ'(s) ds`, and
`∫ (1_{|x|>η} − Ψ_η) |∇G|² = 2π κ' + o(1)` with `κ' = ∫₁² (1 − ψ(s))/s ds`; `κ' − κ = 0` by an
integration by parts (`∫₁² 1/s = log 2`). Also `∫_cell Ψ_η G → ∫_cell G = 0`. Hence
`½ ∫_{cell ∖ B(0, η)} |∇G|² + π log η → π R_Λ`, which is `μ(cell)` by Proposition 4.1. ∎

**Proposition 4.3 (Lemma 11.periodic-cutoff).** For discs or squares, every `L > 0` and every
cutoff family `χ_R` of width `L`, `W(E_Λ, χ_R)/|U_R| → μ(cell) = π R_Λ`. *Proof.* From 4.1:
`∫ χ_R dμ = μ(cell) · #(cells in the plateau) + O(R)` (cells meeting the transition strip number
`O(R)`, `|μ|` per cell is finite), and the core corrections vanish for cores in the plateau or
outside the support and are `O(r₀ ‖∇χ_R‖_∞)` each otherwise, `O(R)` in total. Divide by
`|U_R| ∼ c R²`. ∎

With Propositions 2.2–2.4 and 3.2–3.3 this gives `exists_isGreenFunction`,
`exists_isCanonicalField` and `energyPerArea_canonicalField` (the latter for every canonical `E₀`,
since `W` depends on `E₀` only through its a.e. class, and for every Green function `G'`, since
`robinConstant G' = robinConstant G` by 2.4).
