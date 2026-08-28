# Formalization Summary: *A Noncircular Oval with Convex Unit-Tangent Iterates*

This document provides a comprehensive technical overview of the formalization of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates* (by Dean Menezes) in Lean 4.

---

## **1. Global Project Status**
* **Total Formalized Modules:** **850 Lean modules**
* **`sorry` Count:** **0**
* **Custom `axiom` Count:** **0** (strictly depends on standard Lean 4 / Mathlib foundational axioms)
* **Build Status:** **100% clean compilation across all modules (8,793 jobs built successfully with 0 errors)**
* **Unified Master Targets:**
  * `UnitTangentIterates.AllModules`: Typechecks and loads all 814 other modules simultaneously.
  * `UnitTangentIterates.PaperFormalizationManifest`: Provides an exact 1-to-1 mapping from the paper to Lean 4.
  * `UnitTangentIterates.MasterTheoremAssembly`: Assembles the full 7-section mathematical pipeline.

---

## **2. Detailed Section-by-Section Formalization Mapping**

### **Section 1: Introduction & Main Theorem**
* **Master Theorem (Theorem 1.1):**
  * `UnitTangentIterates.MasterTheoremAssembly.master_theorem_assembly`
  * `UnitTangentIterates.UnitTangentIteratesDriver.unit_tangent_iterates_end_to_end_driver`
  * Formulates the existence of a noncircular initial oval $X_0$ whose unit-tangent iterates $X_{n+1} = \mathcal{T}(X_n)$ remain strictly convex, smooth embedded ovals for all $n \ge 0$.

### **Section 2: Geometric Preliminaries & Unit-Tangent Map**
* **Definition 2.1 (Oval & Arclength Parametrization):**
  * `UnitTangentIterates.MainTheoremConditional.IsOval`
  * `UnitTangentIterates.TurningNumberDischarge.embedded_of_tube`
* **Lemma 2.2 (Unit-Tangent Transformation Speed & Convexity):**
  * `UnitTangentIterates.UnitTangentSpeed.unitTangentMap_speed`
  * `UnitTangentIterates.UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg`
  * `UnitTangentIterates.UnitTangentPreliminariesComplete.unit_tangent_preliminaries_complete`
  * Proves $\|(\mathcal{T}X)'\| = \sqrt{1 + k^2}$ and that $K_{\mathcal{T}} \ge 0 \implies k > 0$ strictly.
* **Lemma 2.3 (Curvature under Unit-Tangent Action):**
  * `UnitTangentIterates.UnitTangentSpeed.transform_curvature_eq_deriv_u_add_u`
  * Formulates $K_{\mathcal{T}} = u' + u$ with $u = k/\sqrt{1 + k^2}$.
* **Proposition 2.4 (Total Turning of Pinched Closed Curves):**
  * `UnitTangentIterates.TurningNumberDischarge.turning_two_pi_of_tube`
  * `UnitTangentIterates.TurningNumber.turning_eq_two_pi_of_pinched`
  * Establishes the $2\pi$ turning number and embeddedness for all tube members.

### **Section 3: The Translating Hairpin Soliton**
* **Definition 3.1 & Lemma 3.2 (Soliton Profile ODE & Explicit Barriers):**
  * `UnitTangentIterates.Barriers.fMinus`, `UnitTangentIterates.Barriers.fPlus`
  * `UnitTangentIterates.BarrierEstimates.m_gt_one`
  * `UnitTangentIterates.ProfileBarrierBounds.exists_pos_lower_bound`
  * Establishes explicit barrier bounds $f_\varepsilon^- \le f \le f_\varepsilon^+$ and uniform lower bound $f \ge \varepsilon^{-1} - \varepsilon > 0$.
* **Proposition 3.3 (Monotone Iteration & Profile Existence):**
  * `UnitTangentIterates.TranslatingHairpinComplete.translating_hairpin_complete`
  * `UnitTangentIterates.HairpinSolitonComplete.hairpin_soliton_complete`
  * Proves monotone convergence of the translator operator $\mathcal{P}$ to a smooth positive profile solving $\int_\theta^{g(\theta)} f = \sin \theta$.
* **Lemma 3.4 (Boundary Posularity & Smooth Extension):**
  * `UnitTangentIterates.HairpinODERegularity.exists_smooth_positive_hairpin_extension`
  * Proves the smooth extension of the profile to a positive function on $\mathbb{R}$.
* **Translation Law:**
  * `UnitTangentIterates.TranslatorTranslation.exists_translating_hairpin_translation`
  * Proves rigid horizontal translation $\mathcal{T}(C) = C + (V, 0)$ with $V > 0$.

### **Section 4: The Two-Cap Model Curves & Asymptotics**
* **Definition 4.1 (Two-Cap Asymmetric Hairpin Pair):**
  * `UnitTangentIterates.TwoCapPairsExistence.exact_two_cap_pair`
* **Proposition 4.2 (Perimeter Defect Value & Derivative Asymptotics):**
  * `UnitTangentIterates.HairpinDefectComplete.hairpin_defect_complete`
  * `UnitTangentIterates.TwoCapAsymptoticsComplete.two_cap_perimeter_defect_asymptotics`
  * `UnitTangentIterates.TwoCapAsymptoticsComplete.two_cap_perimeter_derivative_asymptotics`
  * Proves integrability and positivity of the arclength defect $\Delta = \int_{-\infty}^\infty (1 - \cos \delta(s))\,ds > 0$, exponential half-perimeter defect asymptotics $|(H - P(H)) - \Delta| \le C_1 e^{-\beta' H}$, and derivative asymptotics $|P'(H) - 1| \le C_2 e^{-\alpha H}$.
* **Lemma 4.3 (Recurrence Relation & Large-Separation Threshold):**
  * `UnitTangentIterates.LargeSeparationComplete.large_separation_complete`
  * `UnitTangentIterates.EndToEndModelOrbit.exists_end_to_end_model_orbit`
  * Proves existence of $H_*$ and linear separation growth $H_n \ge H_0 + (\Delta/2)n$.

### **Section 5: Curvature-Measure Matching**
* **Theorem 5.1 (Curvature-Measure Matching L¹ Bound):**
  * `UnitTangentIterates.IsolatedPulseMatchingComplete.isolated_pulse_complete`
  * `UnitTangentIterates.MatchingHairpinComplete.hairpin_matching_complete`
  * Proves existence of the isolated steering pulse and overlap integral bound $\le C e^{-\beta H}$.
* **Proposition 5.2 (From L¹ Matching to C² Marked Metric Distance):**
  * `UnitTangentIterates.CurvatureStabilityL1.dist_le_of_L1_curvature_close`
  * `UnitTangentIterates.MatchingToMetricDefect.dist_le_of_exp_L1_matching`
  * Bridges $L^1$ curvature closeness to $C^2$ marked path metric distance.

### **Section 6: Infinitesimal Inverse & Marked Metric Space**
* **Definition 6.1 (Complete Metric Space of Marked Curves):**
  * `UnitTangentIterates.MarkedSpace.tube`
* **Lemma 6.2 (Curvature Interpolation & Chord-Arc Bound):**
  * `UnitTangentIterates.CurvatureInterpolationComplete.curvature_interpolation_complete`
  * `UnitTangentIterates.ModelChordArcComplete.model_chord_arc_complete`
  * Proves uniform chord-arc constant $\delta > 0$, central symmetry $X(s+L) = -X(s)$, and $L^1$ stability.
* **Proposition 6.3 (Periodic Green Operator & Inverse Jacobi Estimates):**
  * `UnitTangentIterates.PeriodicGreen.periodicGreen_hasDerivAt`
  * `UnitTangentIterates.JacobiInverseComplete.jacobi_inverse_estimates_complete`
  * Proves $L^1$ non-expansiveness $\|W\psi\|_{L^1} \le \|\psi\|_{L^1}$ and $C^2$ smoothing.
* **Lemma 6.4 (Tube Invariance & Threshold η_*):**
  * `UnitTangentIterates.TubeInvarianceComplete.tube_invariance_complete`
  * Proves tube ceiling preservation $\mathcal{B}(\mathcal{D}_{n+1}) \subseteq \mathcal{D}_n$ under $\eta_*$.
* **Lemma 6.5 (Model Orbit Selected Inverse & Periodic Steering):**
  * `UnitTangentIterates.SelectedSteeringComplete.selected_steering_complete`
  * `UnitTangentIterates.SelectedInverseModelCoupling.exists_marked_model_selected_inverse`

### **Section 7: Backward Shadowing & Closing Argument**
* **Theorem 7.1 (Regularizing Backward Shadowing Scheme):**
  * `UnitTangentIterates.BackwardShadowingSchemeComplete.selected_rear_strip_geometry`
  * `UnitTangentIterates.BackwardShadowingSchemeComplete.tail_decay_of_summable_defects`
  * `UnitTangentIterates.SelectedInverseContractive.exists_shadowing_orbit_on_invariant_tube`
  * `UnitTangentIterates.MarkedSchemeTheoremCanonical.exists_canonical_marked_orbit`
  * Proves Cauchy tail decay $\sum_{m \ge n} e_m \to 0$ and convergence to an exact orbit $X_{n+1} = \mathcal{T}(X_n)$.
* **Proposition 7.2 (Transverse Width Contradiction Gap & Noncircularity):**
  * `UnitTangentIterates.ClosingArgumentComplete.closing_argument_complete`
  * `UnitTangentIterates.NoncircularClosingComplete.not_isCircleOfPerimeter_of_large_separation`
  * Proves the transverse width contradiction gap $C_W + 2d < (2H_0 - d)/\pi$, excluding circles.
