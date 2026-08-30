# Formalization of "A Noncircular Oval with Convex Unit-Tangent Iterates"

This repository contains a Lean 4 / Mathlib formalization of substantial
components of the paper:

> Dean Menezes, *A Noncircular Oval with Convex Unit-Tangent Iterates*
> (`noncircular_oval_unit_tangent_iterates.tex` in this repository).

The maintained unified catalog imports the theorem-bearing and support modules.
The formalization proves the paper's unconditional main theorem and its
analytic construction without `sorry` statements or custom axiom declarations.
The canonical zero-argument declaration is `Theorem11Status.mainConclusion`;
its construction is `PaperMainTheoremUnconditional.mainConclusion` in
`UnitTangentIterates/PaperMainTheoremUnconditional.lean`.

---

## **Key Formalization Milestones**

The formalization encompasses all 7 sections of the paper:

1. **Main Theorem (Section 1)**:
   * Proved unconditionally: `Theorem11Status.mainConclusion` in `UnitTangentIterates/Theorem11Status.lean`, constructed by `PaperMainTheoremUnconditional.mainConclusion` in `UnitTangentIterates/PaperMainTheoremUnconditional.lean`.
   * Complete item-by-item paper-to-code correspondence manifest in `UnitTangentIterates/PaperFormalizationManifest.lean`.

2. **One Tangent Step: Rear and Front Tracks (Section 2)**:
   * Exact speed formula $\|(\mathcal{T}X)'\| = \sqrt{1 + k^2}$ and curvature action $K_{\mathcal{T}} = u' + u$ with $u = k/\sqrt{1 + k^2}$ (`UnitTangentIterates/UnitTangentSpeed.lean`).
   * Strict convexity discharge for consecutive tracks: $K_{\mathcal{T}} \ge 0 \implies k > 0$ strictly (`UnitTangentIterates/UnitTangentPreliminariesComplete.lean`).
   * Total turning $2\pi$ and embeddedness of tube curves (`UnitTangentIterates/TurningNumberDischarge.lean`).

3. **A Translating Hairpin (Section 3)**:
   * Explicit lower and upper barriers $f_\varepsilon^- \le f \le f_\varepsilon^+$ (`UnitTangentIterates/Barriers.lean`, `UnitTangentIterates/ProfileBarrierBounds.lean`).
   * Monotone operator $\mathcal{P}$, profile existence, and uniform barrier positivity $f \ge \varepsilon^{-1} - \varepsilon > 0$ (`UnitTangentIterates/TranslatingHairpinComplete.lean`, `UnitTangentIterates/HairpinSolitonComplete.lean`).
   * Interior smoothness and the all-orders relative derivative chain used by
     the constructed model (`UnitTangentIterates/HairpinODERegularity.lean`,
     `UnitTangentIterates/ConstructedPeriodizationAllOrders.lean`), including
     the discharged arbitrary-order translator coefficient recurrence.
   * Rigid horizontal translation $\mathcal{T}(C) = C + (V, 0)$ with $V > 0$ (`UnitTangentIterates/TranslatorTranslation.lean`).

4. **Exact Two-Cap Pairs (Section 4)**:
   * Exact two-cap front and rear pairs $(Q_H, R_H)$ (`UnitTangentIterates/TwoCapPairsExistence.lean`).
   * Arclength defect integrability and strict positivity $\Delta = \int_{-\infty}^\infty (1 - \cos \delta(s))\,ds > 0$ (`UnitTangentIterates/HairpinDefectComplete.lean`).
   * Exponential half-perimeter defect asymptotics $|(H - P(H)) - \Delta| \le C_1 e^{-\beta' H}$ and derivative bounds $|P'(H) - 1| \le C_2 e^{-\alpha H}$ (`UnitTangentIterates/TwoCapAsymptoticsComplete.lean`).

5. **Curvature-Measure Matching (Section 5)**:
   * Isolated steering pulse and pairwise overlap integral bounds $\le C e^{-\beta H}$ (`UnitTangentIterates/IsolatedPulseMatchingComplete.lean`, `UnitTangentIterates/MatchingHairpinComplete.lean`).
   * Quantitative stability from $L^1$ curvature closeness to $C^2$ marked path metric distance (`UnitTangentIterates/CurvatureStabilityL1.lean`, `UnitTangentIterates/MatchingToMetricDefect.lean`).

6. **Regularizing Backward Shadowing: Marked Metric Space & Infinitesimal Inverse (Section 6)**:
   * Complete metric space of marked curves $(\mathcal{D}, d_{\mathcal{D}})$ (`UnitTangentIterates/MarkedSpace.lean`).
   * Uniform chord-arc bound $\delta = \frac{\min(H_0, 2h_0)}{2H_0} > 0$ and central symmetry interpolation (`UnitTangentIterates/ModelChordArcComplete.lean`, `UnitTangentIterates/CurvatureInterpolationComplete.lean`).
   * Periodic Green operator, inverse Jacobi $L^1$ non-expansiveness $\|W\psi\|_{L^1} \le \|\psi\|_{L^1}$, and $C^2$ smoothing (`UnitTangentIterates/PeriodicGreen.lean`, `UnitTangentIterates/JacobiInverseComplete.lean`).
   * Invariant tube ceilings $\kappa_0 < \bar{\kappa} < \hat{\kappa} < 1$, smallness threshold $\eta_*$, and tube preservation $\mathcal{B}(\mathcal{D}_{n+1}) \subseteq \mathcal{D}_n$ (`UnitTangentIterates/TubeInvarianceComplete.lean`).
   * Model selected inverse construction and periodic steering on the closed strip (`UnitTangentIterates/SelectedSteeringComplete.lean`, `UnitTangentIterates/SelectedInverseModelCoupling.lean`).
   * Backward shadowing convergence $X_n \to X_\infty$ (Theorem 6.8) and Cauchy tail decay for summable defects (`UnitTangentIterates/BackwardShadowingSchemeComplete.lean`, `UnitTangentIterates/SelectedInverseContractive.lean`, `UnitTangentIterates/MarkedSchemeTheoremCanonical.lean`).

7. **Proof of the Main Theorem & Closing Contradiction (Section 7)**:
   * Large-separation threshold $H_*$ and linear growth $H_n \ge H_0 + (\Delta/2)n$ (Lemma 7.1; `UnitTangentIterates/LargeSeparationComplete.lean`, `UnitTangentIterates/EndToEndModelOrbit.lean`).
   * Transverse width contradiction gap $C_W + 2d < (2H_0 - d)/\pi$ and exclusion of circles (`UnitTangentIterates/ClosingArgumentComplete.lean`, `UnitTangentIterates/NoncircularClosingComplete.lean`).
   * Weighted approximate pullback closing at the sharp threshold
     $K e^{-\beta\,\Delta H}<1$, allowing $K>1$
     (`UnitTangentIterates/WeightedMarkedDefectThreshold.lean`,
     `UnitTangentIterates/ApproximatePaperAssemblyResidual.lean`).
   * Direct selected-inverse range orbit with no auxiliary total forward map
     (`UnitTangentIterates/DirectMarkedLimitOrbit.lean`,
     `UnitTangentIterates/ApproximatePaperAssemblySelectedInverse.lean`).

---

## **Current Formalization Status**

The paper-facing theorem is now closed:

* `Theorem11Status.mainConclusion : MainConclusion` is the canonical
  zero-argument statement of Theorem 1.1.
* `PaperMainTheoremUnconditional.mainConclusion`, in
  `UnitTangentIterates/PaperMainTheoremUnconditional.lean`, constructs every
  input and proves the smooth, embedded, genuinely noncircular infinite
  unit-tangent orbit.
* The prepared recursive-chain modules construct the arbitrary-depth
  `ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain.ChosenChain`; the
  chosen-chain physical package and unconditional-main modules complete its
  coherent physical closure.

The following supporting pieces are also compiled and are no longer open
assumptions:

* Strict geometry for the epsilon-constructed configured model sequence.
* Linear separation growth and all positivity data needed by closing.
* Weighted canonical-defect summability under
  $K e^{-\beta\,\Delta H}<1$, without assuming $K\leq1$.
* The explicit shadow-tail/start-separation implication for the final gap.
* The final direct range-orbit argument for the canonical selected inverse,
  with `T`, `hTB`, and `hTev` removed.

The physical component family derives the forward unit-tangent range orbit
directly; the earlier `RangeProvider` cleanup remains complete and no
`RangeProvider` remains.

All superseded layers have been removed: the historical
`Theorem11Status.RemainingInput` compatibility API, the conditional
coherent-grid pipeline, the floor-positive and floor-free conditional
assemblies (`MasterTheoremAssembly`, `UnitTangentIteratesDriver`,
`UnitTangentIteratesMain`), and every module reachable from none of the
canonical theorem, the manifest, or the documented paper-item formalizations.

The former interface `ConstructedPeriodizationAllOrders.InteriorCoefficientRecurrenceProvider`
(arbitrary-order translator coefficient recurrence) is **discharged**:
`ConstructedPeriodizationAllOrders.interiorCoefficientRecurrenceProvider`
(`ConstructedPeriodizationAllOrders.lean:709`) proves it from the shifted
intrinsic curvature evolution and Harnack bound, with
`interiorRecurrenceProvider:753` and unconditional
`exists_constructed_certificate_unconditional:908` for every `eps ≤ 1/10` and
finite `(r,q)`; the all-order Faà di Bruno closure is complete.

---

## **Building and Verifying the Project**

### Prerequisites
* Lean 4 toolchain: `leanprover/lean4:v4.28.0`
* Lake build system

### Verification Commands
To build and typecheck all modules in the repository:
```bash
# Build the unified module catalog (imports every module)
lake build UnitTangentIterates.AllModules

# Build the canonical main theorem
lake build UnitTangentIterates.Theorem11Status

# Build the paper formalization manifest
lake build UnitTangentIterates.PaperFormalizationManifest
```

---

## **Project Structure**

| Module / Path | Mathematical Content & Purpose |
| :--- | :--- |
| [`UnitTangentIterates/AllModules.lean`](UnitTangentIterates/AllModules.lean) | Maintained root target importing the project module catalog. |
| [`UnitTangentIterates/Theorem11Status.lean`](UnitTangentIterates/Theorem11Status.lean) | Canonical zero-argument statement of Theorem 1.1. |
| [`UnitTangentIterates/PaperMainTheoremUnconditional.lean`](UnitTangentIterates/PaperMainTheoremUnconditional.lean) | Closed construction of the unconditional paper main theorem. |
| [`UnitTangentIterates/PaperFormalizationManifest.lean`](UnitTangentIterates/PaperFormalizationManifest.lean) | 1-to-1 manifest mapping every theorem/lemma in the paper to Lean 4. |
| [`UnitTangentIterates/TranslatingHairpinComplete.lean`](UnitTangentIterates/TranslatingHairpinComplete.lean) | Lemmas 3.1–3.2 monotone translator operator & profile existence (Theorem 3.4 support). |
| [`UnitTangentIterates/HairpinDefectComplete.lean`](UnitTangentIterates/HairpinDefectComplete.lean) | Lemma 3.5 / Proposition 4.3 arclength defect $\Delta > 0$ and perimeter asymptotics. |
| [`UnitTangentIterates/LargeSeparationComplete.lean`](UnitTangentIterates/LargeSeparationComplete.lean) | Lemma 7.1 large-separation threshold $H_*$ and linear growth. |
| [`UnitTangentIterates/IsolatedPulseMatchingComplete.lean`](UnitTangentIterates/IsolatedPulseMatchingComplete.lean) | Theorem 5.2 isolated steering pulse & $L^1$ curvature matching. |
| [`UnitTangentIterates/ModelChordArcComplete.lean`](UnitTangentIterates/ModelChordArcComplete.lean) | Uniform chord-arc bound $\delta > 0$ and model embeddedness (Section 6 support). |
| [`UnitTangentIterates/TubeInvarianceComplete.lean`](UnitTangentIterates/TubeInvarianceComplete.lean) | Invariant tube ceilings and threshold $\eta_*$ (proof of Theorem 6.8). |
| [`UnitTangentIterates/JacobiInverseComplete.lean`](UnitTangentIterates/JacobiInverseComplete.lean) | Lemma 6.4 inverse Jacobi estimates & periodic Green operator inversion. |
| [`UnitTangentIterates/BackwardShadowingSchemeComplete.lean`](UnitTangentIterates/BackwardShadowingSchemeComplete.lean) | Theorem 6.8 backward shadowing convergence and tail estimates. |
| [`UnitTangentIterates/ClosingArgumentComplete.lean`](UnitTangentIterates/ClosingArgumentComplete.lean) | Section 7 closing step: transverse width contradiction gap excluding circles. |
