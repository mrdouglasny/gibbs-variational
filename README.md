# gibbs-variational

A Mathlib-only Lean 4 library formalising the **Gibbs / Donsker–Varadhan variational
principle** and a **finite-dimensional Boué–Dupuis bound** — the entropy/free-energy duality
that links a log-Laplace transform (cumulant generating functional) to the Kullback–Leibler
divergence, and its specialisation to shifted Gaussians.

## What is proved

All statements live in the namespace `GibbsVariational`. The library is built on Mathlib's
`InformationTheory.klDiv` and `ProbabilityTheory.gaussianReal`; its only dependency is Mathlib
`v4.29.0`.

### 1. The variational inequality

For probability measures `ν ≪ μ` on a measurable space and a test function `f : α → ℝ` with
`eᶠ ∈ L¹(μ)`, `f ∈ L¹(ν)`, and finite relative entropy,

```
∫ f dν ≤ log (∫ eᶠ dμ) + KL(ν ‖ μ).
```

This is the **Gibbs variational inequality** (`integral_le_log_integral_exp_add_klDiv` in
`Variational.lean`). It is half of the Donsker–Varadhan duality: rearranged, it says that
`log ∫ eᶠ dμ` upper-bounds `∫ f dν − KL(ν ‖ μ)` for every admissible `ν`. The full duality
(equality with the supremum over `ν`) is stated as `log_integral_exp_eq_sSup_sub_klDiv` and
left as a `sorry` skeleton.

### 2. Cameron–Martin relative entropy of a finite-dimensional Gaussian

For the standard Gaussian on `Fin n → ℝ` and any shift `h : Fin n → ℝ`,

```
KL( (stdGaussian n).map (· + h)  ‖  stdGaussian n ) = ½ ‖h‖² = ½ ∑ᵢ (hᵢ)².
```

This is `klDiv_stdGaussian_map_add` in `GaussianEntropy.lean`. It identifies the abstract
KL divergence with the explicit quadratic Cameron–Martin cost. The proof factors the shift
density coordinatewise and reduces to the 1D building block

```
KL(N(c,1) ‖ N(0,1)) = ½ c²    (klDiv_gaussianReal_shift),
```

a direct PDF-ratio computation. The tensorisation step is supported by three general lemmas
that are independent of Gaussians and ready to upstream to Mathlib:

* `klDiv_map_measurableEquiv` — KL is invariant under measurable equivalences.
* `klDiv_prod` — KL of a product is the sum of marginal KLs.
* `klDiv_pi` — the same for `Measure.pi` over `Fin n`.

### 3. The finite-dimensional Boué–Dupuis upper bound

Combine (1) and (2): take `μ = stdGaussian n`, `ν = (stdGaussian n).map (· + h)`,
`f = −V`, and use the translation change of variables. The result
(`neg_log_integral_exp_neg_le` in `BoueDupuis.lean`) is

```
− log ∫ e^{−V} d(stdGaussian n)  ≤  ∫ V(· + h) d(stdGaussian n)  +  ½ ‖h‖².
```

In words: every choice of *drift* `h` controls the negative log-partition function (the
"free energy" `F = −log Z`) from above, with cost equal to the post-shift average of `V`
plus the Cameron–Martin penalty. The Boué–Dupuis variational formula proper is the infimum
over `h`; this library proves the *one-sided* inequality, which is what every application
actually uses.

## What it is useful for

The Gibbs variational principle and its Gaussian-drift specialisation underlie a wide spread
of analytic methods.

**Large deviations.** Donsker–Varadhan duality is the dual representation of the
log-Laplace transform of a probability measure. It is the basic ingredient in the variational
form of large-deviation rate functions and in the Donsker–Varadhan LDP for empirical
measures of Markov processes.

**Statistical mechanics.** For an energy `H`, the Gibbs measure `μ_β ∝ e^{−βH} μ`
minimises the free-energy functional `ν ↦ β·𝔼_ν[H] + KL(ν‖μ)`; the variational inequality
is the bound that makes this minimisation property a theorem. The same machine drives
entropy methods (log-Sobolev, modified-log-Sobolev) for Markov semigroups and concentration
inequalities via Herbst-style arguments.

**Information theory.** The inequality is sharp at the tilted measure `μ_f ∝ eᶠ μ`,
which gives the standard derivation of the Csiszár-style projection theorems.

**Stochastic analysis.** In infinite dimensions, the analogous statement for Wiener space
is the Boué–Dupuis formula: for a functional `F` of Brownian motion `W`,

```
− log 𝔼[ e^{−F(W)} ]  =  inf_u  𝔼[ F(W + ∫₀· u_s ds) + ½ ∫₀¹ ‖u_s‖² ds ],
```

where the infimum runs over progressively measurable drifts `u`. The finite-dimensional
form proved here is the same statement after replacing Brownian motion with a standard
Gaussian on `Fin n → ℝ` and Cameron–Martin functions with vectors. It is *not* a toy:
on a finite lattice it is the exact form one applies, with no Wiener-space machinery.

**Constructive quantum field theory.** This is the motivating application. The
variational approach (Barashkov–Gubinelli; earlier roots in Üstünel and Boué–Dupuis)
replaces the combinatorics of cluster / phase-cell expansions by a single well-chosen
drift `h` that absorbs the Wick-singular part of the interaction. For the
two-dimensional `P(φ)₂` model on a lattice approximation, the bound

```
− log ∫ e^{−V} dμ_{free}  ≤  ∫ V(· + h) dμ_{free}  +  ½ ‖h‖²
```

is the route to a **volume-uniform exponential-moment bound** on cylinder partition
functions (downstream in `pphi2`, this is CYL-1a). Choosing `h` to cancel the most
singular Wick monomial makes the right-hand side extensive in the volume, so the bound
per unit volume is uniform, and one can pass to the infinite-volume / continuum limit.
A cluster expansion is not needed at any step.

## File map

| File | Contents |
|---|---|
| `GibbsVariational/Variational.lean` | Gibbs variational inequality (proved); Donsker–Varadhan duality (skeleton). |
| `GibbsVariational/GaussianEntropy.lean` | 1D and `n`-D Cameron–Martin KL identities; KL invariance / product / pi lemmas. |
| `GibbsVariational/BoueDupuis.lean` | Finite-dimensional Boué–Dupuis upper bound on the free energy. |

## Status

| Result | State |
|---|---|
| `integral_le_log_integral_exp_add_klDiv` (Gibbs inequality) | proved |
| `log_integral_exp_eq_sSup_sub_klDiv` (Donsker–Varadhan equality) | `sorry` skeleton |
| `klDiv_gaussianReal_shift` (1D Gaussian KL) | proved |
| `klDiv_stdGaussian_map_add` (Cameron–Martin cost) | proved |
| `klDiv_map_measurableEquiv`, `klDiv_prod`, `klDiv_pi` | proved (Mathlib-upstreamable) |
| `neg_log_integral_exp_neg_le` (Boué–Dupuis upper bound) | proved |

The proved results are bare-Mathlib, depend on no project-specific axioms, and the
KL invariance / product / pi lemmas are written generically so they can be lifted
directly into `Mathlib.InformationTheory`.

## Why a separate library

The variational principle is universal — it has nothing intrinsically to do with any one
semigroup, lattice, or field theory — so it sits below the project-specific libraries
(`markov-semigroups`, `gaussian-field`, `gaussian-hilbert`, `pphi2`) and can be consumed
by any of them. The intent is for the general lemmas here to migrate upstream into
Mathlib over time.

## Build

```bash
lake exe cache get   # fetch Mathlib oleans
lake build
```

Toolchain: `leanprover/lean4:v4.29.0` (see `lean-toolchain`).

## References

* M. Boué, P. Dupuis, *A variational representation for certain functionals of Brownian
  motion*, Ann. Probab. 26 (1998).
* P. Dupuis, R. S. Ellis, *A Weak Convergence Approach to the Theory of Large Deviations*,
  Wiley (1997), §1.4.2.
* M. D. Donsker, S. R. S. Varadhan, *Asymptotic evaluation of certain Markov process
  expectations for large time*, Comm. Pure Appl. Math. 28 (1975) and sequels.
* N. Barashkov, M. Gubinelli, *A variational method for `Φ⁴₃`*, Duke Math. J. 169 (2020).
* A. S. Üstünel, *Entropy, invertibility and variational calculus of adapted shifts on
  Wiener space*, J. Funct. Anal. 257 (2009).
