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

> **⚠️ Known issue (2026-06-02): the current `log_integral_exp_eq_sSup_sub_klDiv`
> statement appears to be _false as literally written_.** The supremand uses
> `(klDiv ν μ).toReal`, and `.toReal` collapses an _infinite_ KL divergence to `0`
> rather than `−∞`. So a `ν` with `KL(ν‖μ) = ∞` contributes `∫ f dν − 0` to the
> `sSup` set, which can exceed `log ∫ eᶠ dμ` and breaks the claimed equality. The
> intended theorem needs either (a) the `sSup` set restricted to `ν` with
> `klDiv ν μ ≠ ∞`, or (b) the subtraction taken in `EReal`/`ENNReal` so that infinite
> KL gives `−∞`. The statement must be corrected before the `sorry` can be discharged.
> (Surfaced by an automated discharge attempt, which correctly refused to "prove" the
> statement as stated.)

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

## For physicists: known names for the same inequality

The bound `−log ∫ e^{−V} dμ_G ≤ ∫ V(· + h) dμ_G + ½‖h‖²` is a single inequality with
at least four standard names in the physics literature.

**Peierls–Bogoliubov / Gibbs–Bogoliubov–Feynman inequality.** In statistical mechanics,
for any trial Hamiltonian `H₀` with Gibbs measure `ρ₀`,

```
F  ≤  F₀ + ⟨H − H₀⟩_{ρ₀}.
```

This is the Gibbs variational inequality applied with `ν = ρ₀`. The Boué–Dupuis
specialisation chooses the trial measure to be a *Cameron–Martin translate* of the
Gaussian, i.e. `ρ₀ = μ_G(· − h)`; for that choice `F₀ = 0` and the trial free entropy
collapses to the quadratic Cameron–Martin cost `½‖h‖²`.

**Bogoliubov variational principle in many-body physics.** The same inequality used
in BCS / Hartree–Fock to optimise a quadratic (quasi-free) trial state against the
interacting one. The trial-state class is Gaussian; the bound reduces to mean-field
theory.

**Feynman polaron variational principle (1955).** Feynman's polaron upper bound is
exactly this inequality on path space, with `μ` = Wiener measure under the full polaron
action and `ν` = Wiener measure under a Gaussian trial action. The Boué–Dupuis formula
is the modern path-space form of Feynman's argument, with deterministic shifts replaced
by progressively measurable drifts.

**Background-field method at tree level.** The Cameron–Martin shift `W ↦ W + h` is the
background-field decomposition `φ = h + φ̃`:

* `½‖h‖²` = classical (free) action of the background.
* `∫ V(h + φ̃) dμ_G(φ̃)` = average of the interaction over the quantum fluctuation `φ̃`.
* Minimising the sum over `h` is the saddle-point / classical-equations-of-motion step.

The right-hand side is the effective action evaluated at one-loop Gaussian level around
the background `h`; the inequality says this upper-bounds the true free energy.

### Relation to the 1PI effective action

The 1PI effective action is the Legendre transform of the cumulant generating
functional `W[J] = log Z[J]`:

```
Γ[φ_cl]  =  sup_J ( ⟨J, φ_cl⟩ − W[J] ).
```

The **Donsker–Varadhan duality** is the same Legendre transform at the level of
probability measures rather than sources:

```
log ∫ eᶠ dμ  =  sup_ν ( 𝔼_ν[f] − KL(ν‖μ) ).
```

Identifying `f ↔ J` and `ν ↔ φ_cl` (with `KL` playing the role of `Γ` minus its
`J`-coupling), the two statements are the same convex-analysis identity. The Gibbs
inequality is one side of this duality, applied with a Gaussian translate as the
trial measure; the supremum is attained at the tilted (Gibbs-with-source) measure,
which is the probabilistic analogue of solving `∂Γ/∂φ_cl = J`.

### Relation to Wilsonian / Polchinski flow

In the Barashkov–Gubinelli variational method for `Φ⁴₃` — and the lattice variant for
`Φ⁴₂` underneath `pphi2` — the drift `h` is constructed *scale by scale* to cancel the
Wick-singular pieces of `V` as the UV cutoff is removed. The drift then plays the role
of a **running counterterm**, which is morally the same object as the counterterm in
Polchinski's exact RG / Wilsonian effective action: the regulator scale of the flow
equation is replaced by the time horizon of an SDE built from the drift. The Gibbs
inequality + Cameron–Martin cost packages the bookkeeping of one scale; iterated over
scales it is a non-perturbative renormalisation procedure.

**Bottom line.** `neg_log_integral_exp_neg_le` is the formalised one-line statement
underneath Peierls–Bogoliubov, Bogoliubov's mean-field principle, Feynman's polaron
bound, the tree-level background-field method, the Donsker–Varadhan / 1PI Legendre
duality (one direction), and the per-scale Polchinski flow bound. The modern
"variational approach to constructive QFT" is the application of this inequality with
the drift `h` chosen as a Wilsonian counterterm.

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
| `log_integral_exp_eq_sSup_sub_klDiv` (Donsker–Varadhan equality) | `sorry` skeleton — ⚠️ statement likely false as written (`.toReal` on ∞-KL); see Known issue under §1 |
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
