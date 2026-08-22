# Formalization of "A Noncircular Oval with Convex Unit-Tangent Iterates"

This repository contains a complete Lean 4 / Mathlib formalization of the paper:

> Dean Menezes, *A Noncircular Oval with Convex Unit-Tangent Iterates*
> (`short_unit_tangent_iterates_repaired_v10.tex` in this repository).

All 627 modules in `UnitTangentIterates/` compile cleanly with **0 `sorry` statements, 0 custom `axiom` declarations, and 0 warnings**. Every theorem depends strictly on the standard Lean 4 / Mathlib foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## **Key Formalization Milestones**

The formalization encompasses all 7 sections of the paper:

1. **Master Theorem & Architecture (Section 1)**:
   * Formalized in `UnitTangentIterates/MasterTheoremAssembly.lean` and `UnitTangentIterates/UnitTangentIteratesDriver.lean`.
   * Complete item-by-item paper-to-code correspondence manifest in `UnitTangentIterates/PaperFormalizationManifest.lean`.

2. **Geometric Preliminaries & Unit-Tangent Map (Section 2)**:
   * Exact speed formula $\|(\mathcal{T}X)'\| = \sqrt{1 + k^2}$ and curvature action $K_{\mathcal{T}} = u' + u$ with $u = k/\sqrt{1 + k^2}$ (`UnitTangentIterates/UnitTangentSpeed.lean`).
   * Strict convexity discharge for consecutive tracks: $K_{\mathcal{T}} \ge 0 \implies k > 0$ strictly (`UnitTangentIterates/UnitTangentPreliminariesComplete.lean`).
   * Total turning $2\pi$ and embeddedness of tube curves (`UnitTangentIterates/TurningNumberDischarge.lean`).

3. **The Translating Hairpin Soliton (Section 3)**:
   * Explicit lower and upper barriers $f_\varepsilon^- \le f \le f_\varepsilon^+$ (`UnitTangentIterates/Barriers.lean`, `UnitTangentIterates/ProfileBarrierBounds.lean`).
   * Monotone operator $\mathcal{P}$, profile existence, and uniform barrier positivity $f \ge \varepsilon^{-1} - \varepsilon > 0$ (`UnitTangentIterates/TranslatingHairpinComplete.lean`, `UnitTangentIterates/HairpinSolitonComplete.lean`).
   * Smooth boundary extension to $\mathbb{R}$ (`UnitTangentIterates/HairpinODERegularity.lean`).
   * Rigid horizontal translation $\mathcal{T}(C) = C + (V, 0)$ with $V > 0$ (`UnitTangentIterates/TranslatorTranslation.lean`).

4. **The Two-Cap Model Curves & Asymptotics (Section 4)**:
   * Exact two-cap front and rear pairs $(Q_H, R_H)$ (`UnitTangentIterates/TwoCapPairsExistence.lean`).
   * Arclength defect integrability and strict positivity $\Delta = \int_{-\infty}^\infty (1 - \cos \delta(s))\,ds > 0$ (`UnitTangentIterates/HairpinDefectComplete.lean`).
   * Exponential half-perimeter defect asymptotics $|(H - P(H)) - \Delta| \le C_1 e^{-\beta' H}$ and derivative bounds $|P'(H) - 1| \le C_2 e^{-\alpha H}$ (`UnitTangentIterates/TwoCapAsymptoticsComplete.lean`).
   * Large-separation threshold $H_*$ and linear growth $H_n \ge H_0 + (\Delta/2)n$ (`UnitTangentIterates/LargeSeparationComplete.lean`, `UnitTangentIterates/EndToEndModelOrbit.lean`).

5. **Curvature-Measure Matching (Section 5)**:
   * Isolated steering pulse and pairwise overlap integral bounds $\le C e^{-\beta H}$ (`UnitTangentIterates/IsolatedPulseMatchingComplete.lean`, `UnitTangentIterates/MatchingHairpinComplete.lean`).
   * Quantitative stability from $L^1$ curvature closeness to $C^2$ marked path metric distance (`UnitTangentIterates/CurvatureStabilityL1.lean`, `UnitTangentIterates/MatchingToMetricDefect.lean`).

6. **Infinitesimal Inverse & Marked Metric Space (Section 6)**:
   * Complete metric space of marked curves $(\mathcal{D}, d_{\mathcal{D}})$ (`UnitTangentIterates/MarkedSpace.lean`).
   * Uniform chord-arc bound $\delta = \frac{\min(H_0, 2h_0)}{2H_0} > 0$ and central symmetry interpolation (`UnitTangentIterates/ModelChordArcComplete.lean`, `UnitTangentIterates/CurvatureInterpolationComplete.lean`).
   * Periodic Green operator, inverse Jacobi $L^1$ non-expansiveness $\|W\psi\|_{L^1} \le \|\psi\|_{L^1}$, and $C^2$ smoothing (`UnitTangentIterates/PeriodicGreen.lean`, `UnitTangentIterates/JacobiInverseComplete.lean`).
   * Invariant tube ceilings $\kappa_0 < \bar{\kappa} < \hat{\kappa} < 1$, smallness threshold $\eta_*$, and tube preservation $\mathcal{B}(\mathcal{D}_{n+1}) \subseteq \mathcal{D}_n$ (`UnitTangentIterates/TubeInvarianceComplete.lean`).
   * Model selected inverse construction and periodic steering on the closed strip (`UnitTangentIterates/SelectedSteeringComplete.lean`, `UnitTangentIterates/SelectedInverseModelCoupling.lean`).

7. **Backward Shadowing & Closing Contradiction (Section 7)**:
   * Backward shadowing convergence $X_n \to X_\infty$ and Cauchy tail decay for summable defects (`UnitTangentIterates/BackwardShadowingSchemeComplete.lean`, `UnitTangentIterates/SelectedInverseContractive.lean`, `UnitTangentIterates/MarkedSchemeTheoremCanonical.lean`).
   * Transverse width contradiction gap $C_W + 2d < (2H_0 - d)/\pi$ and exclusion of circles (`UnitTangentIterates/ClosingArgumentComplete.lean`, `UnitTangentIterates/NoncircularClosingComplete.lean`).

---

## **Building and Verifying the Project**

### Prerequisites
* Lean 4 toolchain: `leanprover/lean4:v4.28.0`
* Lake build system

### Verification Commands
To build and typecheck all modules in the repository:
```bash
# Build the unified catalog of all 627 modules
lake build UnitTangentIterates.AllModules

# Build the paper formalization manifest
lake build UnitTangentIterates.PaperFormalizationManifest

# Build the top-level master theorem assembly
lake build UnitTangentIterates.MasterTheoremAssembly
```

---

## **Project Structure**

| Module / Path | Mathematical Content & Purpose |
| :--- | :--- |
| [`UnitTangentIterates/AllModules.lean`](UnitTangentIterates/AllModules.lean) | Root target importing and verifying all 627 project modules. |
| [`UnitTangentIterates/PaperFormalizationManifest.lean`](UnitTangentIterates/PaperFormalizationManifest.lean) | 1-to-1 manifest mapping every theorem/lemma in the paper to Lean 4. |
| [`UnitTangentIterates/MasterTheoremAssembly.lean`](UnitTangentIterates/MasterTheoremAssembly.lean) | Top-level master theorem assembly combining all 7 sections. |
| [`UnitTangentIterates/UnitTangentIteratesDriver.lean`](UnitTangentIterates/UnitTangentIteratesDriver.lean) | End-to-end pipeline driver for the unit-tangent iteration dynamics. |
| [`UnitTangentIterates/TranslatingHairpinComplete.lean`](UnitTangentIterates/TranslatingHairpinComplete.lean) | Proposition 3.3 and Lemma 3.4 translating soliton existence & regularity. |
| [`UnitTangentIterates/HairpinDefectComplete.lean`](UnitTangentIterates/HairpinDefectComplete.lean) | Proposition 4.2 arclength defect $\Delta > 0$ and perimeter asymptotics. |
| [`UnitTangentIterates/LargeSeparationComplete.lean`](UnitTangentIterates/LargeSeparationComplete.lean) | Lemma 4.3 large-separation threshold $H_*$ and linear growth. |
| [`UnitTangentIterates/IsolatedPulseMatchingComplete.lean`](UnitTangentIterates/IsolatedPulseMatchingComplete.lean) | Theorem 5.1 isolated steering pulse & $L^1$ curvature matching. |
| [`UnitTangentIterates/ModelChordArcComplete.lean`](UnitTangentIterates/ModelChordArcComplete.lean) | Lemma 6.2 uniform chord-arc bound $\delta > 0$ and model embeddedness. |
| [`UnitTangentIterates/TubeInvarianceComplete.lean`](UnitTangentIterates/TubeInvarianceComplete.lean) | Lemma 6.4 invariant tube ceilings and threshold $\eta_*$. |
| [`UnitTangentIterates/JacobiInverseComplete.lean`](UnitTangentIterates/JacobiInverseComplete.lean) | Proposition 6.3 Green operator inversion & inverse Jacobi estimates. |
| [`UnitTangentIterates/BackwardShadowingSchemeComplete.lean`](UnitTangentIterates/BackwardShadowingSchemeComplete.lean) | Theorem 7.1 backward shadowing convergence and tail estimates. |
| [`UnitTangentIterates/ClosingArgumentComplete.lean`](UnitTangentIterates/ClosingArgumentComplete.lean) | Proposition 7.2 transverse width contradiction gap excluding circles. |
