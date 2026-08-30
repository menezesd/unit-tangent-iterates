# Formalization Summary: *A Noncircular Oval with Convex Unit-Tangent Iterates*

This document provides a comprehensive technical overview of the formalization of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates* (by Dean Menezes) in Lean 4.

---

## **1. Global Project Status**
* **Main Theorem:** proved **unconditionally** — `Theorem11Status.mainConclusion` depends only on `propext`, `Classical.choice`, and `Quot.sound`
* **Total Formalized Modules:** **1,214 Lean modules** (after removal of all superseded conditional-pipeline modules)
* **`sorry` Count:** **0**
* **Custom `axiom` Count:** **0** (strictly depends on standard Lean 4 / Mathlib foundational axioms)
* **Build Status:** **100% clean compilation across all modules**
* **Unified Master Targets:**
  * `UnitTangentIterates.AllModules`: Typechecks and loads every other module simultaneously.
  * `UnitTangentIterates.PaperFormalizationManifest`: Provides an exact 1-to-1 mapping from the paper to Lean 4.
  * `UnitTangentIterates.Theorem11Status`: The canonical zero-argument unconditional main theorem.

---

## **2. Detailed Section-by-Section Formalization Mapping**

### **Section 1: Introduction & Main Theorem**
* **Master Theorem (Theorem 1.1) — proved unconditionally:**
  * `UnitTangentIterates.Theorem11Status.mainConclusion` (canonical zero-argument statement)
  * `UnitTangentIterates.PaperMainTheoremUnconditional.mainConclusion` (closed construction)
  * Proves the existence of a noncircular initial oval $X_0$ whose unit-tangent iterates $X_{n+1} = \mathcal{T}(X_n)$ remain strictly convex, smooth embedded ovals for all $n \ge 0$, with every construction input produced internally.

### **Section 2: One Tangent Step — Rear and Front Tracks**
* **Bicycle equations & unit-tangent speed (eqs. 2.1–2.3):**
  * `UnitTangentIterates.UnitTangentSpeed.unitTangentMap_speed`
  * `UnitTangentIterates.UnitTangentSpeed.transform_curvature_eq_deriv_u_add_u`
  * Proves $\|(\mathcal{T}X)'\| = \sqrt{1 + k^2}$ and $K_{\mathcal{T}} = u' + u$ with $u = k/\sqrt{1 + k^2}$.
* **Lemma 2.1 (Low-curvature inverse):**
  * `UnitTangentIterates.SelectedSteeringComplete.selected_steering_complete`
  * `UnitTangentIterates.SelectedInverseModelCoupling.exists_marked_model_selected_inverse`
  * Unique periodic steering solution on the branch $0 < \delta < \pi/2$ with the rear curvature bound.
* **Lemma 2.2 (Convex consecutive tracks):**
  * `UnitTangentIterates.UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg`
  * `UnitTangentIterates.UnitTangentPreliminariesComplete.unit_tangent_preliminaries_complete`
  * Proves that $K_{\mathcal{T}} \ge 0 \implies k > 0$ strictly.
* **Oval definition, embeddedness & total turning (introduction / Section 2 conventions):**
  * `UnitTangentIterates.MainTheoremConditional.IsOval`
  * `UnitTangentIterates.TurningNumberDischarge.embedded_of_tube`
  * `UnitTangentIterates.TurningNumberDischarge.turning_two_pi_of_tube`
  * `UnitTangentIterates.TurningNumber.turning_eq_two_pi_of_pinched`
  * Establishes the $2\pi$ turning number and embeddedness for all tube members.

### **Section 3: A Translating Hairpin**
* **Lemmas 3.1–3.2 (Translator equation & monotone translator operator):**
  * `UnitTangentIterates.TranslatingHairpinComplete.translating_hairpin_complete`
  * Monotone convergence of the translator operator $\mathcal{P}$ to a positive profile solving $\int_\theta^{g(\theta)} f = \sin \theta$.
* **Lemma 3.3 (Explicit barriers):**
  * `UnitTangentIterates.Barriers.fMinus`, `UnitTangentIterates.Barriers.fPlus`
  * `UnitTangentIterates.BarrierEstimates.m_gt_one`
  * `UnitTangentIterates.ProfileBarrierBounds.exists_pos_lower_bound`
  * Establishes $f_\varepsilon^- \le \mathcal{P}f_\varepsilon^- \le \mathcal{P}f_\varepsilon^+ \le f_\varepsilon^+$ and the uniform lower bound $f \ge \varepsilon^{-1} - \varepsilon > 0$.
* **Theorem 3.4 (Translating hairpin):**
  * `UnitTangentIterates.HairpinSolitonComplete.hairpin_soliton_complete`
  * `UnitTangentIterates.HairpinODERegularity.exists_smooth_positive_hairpin_extension`
  * `UnitTangentIterates.TranslatorTranslation.exists_translating_hairpin_translation`
  * Smooth strictly convex complete hairpin with $\mathcal{T}(C) = C + (V, 0)$ and $V > 0$.
* **Lemma 3.5 (Hairpin pulse estimates):**
  * `UnitTangentIterates.HairpinAsymptoticsComplete.exists_hairpin_pulse_package`
  * `UnitTangentIterates.HairpinDefectComplete.hairpin_defect_complete`
  * `UnitTangentIterates.ConstructedPeriodizationAllOrders.interiorCoefficientRecurrenceProvider`
  * Exponential decay of $y$ and all derivatives, relative bounds $|y^{(j)}| \le D_j y$, steering mass $\int y = \pi$, and defect positivity $\Delta = \int (1 - \cos \delta)\,ds > 0$.

### **Section 4: Exact Two-Cap Pairs**
* **Lemmas 4.1–4.2 (Exponential periodization & front periodization error):**
  * `UnitTangentIterates.ConstructedPeriodizationAllOrders.exists_constructed_certificate_unconditional`
  * `UnitTangentIterates.FrontPeriodizationPositivity`
  * `UnitTangentIterates.IsolatedPulseMatchingComplete.isolated_pulse_complete`
  * Periodization $C^r$/$\partial_H$ bounds and the pairwise overlap estimate $\le C e^{-\beta H}$.
* **Proposition 4.3 (Exact two-cap pairs):**
  * `UnitTangentIterates.TwoCapPairsExistence.exact_two_cap_pair`
  * `UnitTangentIterates.TwoCapAsymptoticsComplete.two_cap_perimeter_defect_asymptotics`
  * `UnitTangentIterates.TwoCapAsymptoticsComplete.two_cap_perimeter_derivative_asymptotics`
  * Exact centrally symmetric pairs $\mathcal{T}R_H = F_H$ with $|(H - P(H)) - \Delta| \le C_1 e^{-\beta' H}$ and $|P'(H) - 1| \le C_2 e^{-\alpha H}$.
* **Lemma 4.4 (Uniform transverse width):**
  * `UnitTangentIterates.TransverseWidthPositivity`
  * `UnitTangentIterates.ClosingArgumentComplete.closing_argument_complete`
  * Uniform bound $0 < W_H \le C$ for all large $H$.

### **Section 5: Curvature-Measure Matching**
* **Lemma 5.1 & Theorem 5.2 (Common phase; curvature-measure matching $L^1$ bound):**
  * `UnitTangentIterates.IsolatedPulseMatchingComplete.isolated_pulse_complete`
  * `UnitTangentIterates.MatchingHairpinComplete.hairpin_matching_complete`
  * Proves the matching bound $\int |k_H - K_{P(H)}| \le C e^{-\beta H}$.
* **From $L^1$ matching to $C^2$ marked metric distance (used by Theorem 6.8):**
  * `UnitTangentIterates.CurvatureStabilityL1.dist_le_of_L1_curvature_close`
  * `UnitTangentIterates.MatchingToMetricDefect.dist_le_of_exp_L1_matching`
  * Bridges $L^1$ curvature closeness to $C^2$ marked path metric distance.

### **Section 6: Regularizing Backward Shadowing**
* **Marked metric space of curves (Section 6 conventions):**
  * `UnitTangentIterates.MarkedSpace.tube`
* **Lemma 6.2 (Curvature interpolation) & chord-arc control:**
  * `UnitTangentIterates.CurvatureInterpolationComplete.curvature_interpolation_complete`
  * `UnitTangentIterates.ModelChordArcComplete.model_chord_arc_complete`
  * Constant-speed interpolation path with $W + S_0 + S_1 \le C(1+L)^2 \|\kappa^{(1)} - \kappa^{(0)}\|_{L^1}$, uniform chord-arc constant, and central symmetry $X(s+L) = -X(s)$.
* **Lemmas 6.3–6.4 (Smooth dependence of the selected rear; inverse Jacobi estimates):**
  * `UnitTangentIterates.SelectedRearSmoothDependence.hasDerivAt_selected_steering_time`
  * `UnitTangentIterates.PeriodicGreen.periodicGreen_hasDerivAt`
  * `UnitTangentIterates.JacobiInverseComplete.jacobi_inverse_estimates_complete`
  * $L^1$ non-expansiveness $W(\mathcal{B}\Gamma) \le W(\Gamma)$ with the $S_0, S_1, S_2$ gains and the $C^{r+1}$ regularity gain.
* **Lemmas 6.5–6.6 (Completeness of summable normal paths; stopped curvature / tube invariance):**
  * `UnitTangentIterates.TubeInvarianceComplete.tube_invariance_complete`
  * Tube preservation $\mathcal{B}(\mathcal{D}_{n+1}) \subseteq \mathcal{D}_n$ with ceilings $\kappa_0 < \bar{\kappa} < \hat{\kappa} < 1$ and the smallness threshold $\eta_*$.
* **Lemma 6.7 (Selected inverse on the closed strip):**
  * `UnitTangentIterates.SelectedSteeringComplete.selected_steering_complete`
  * `UnitTangentIterates.BackwardShadowingSchemeComplete.selected_rear_strip_geometry`
* **Theorem 6.8 (Regularizing backward shadowing):**
  * `UnitTangentIterates.BackwardShadowingSchemeComplete.tail_decay_of_summable_defects`
  * `UnitTangentIterates.SelectedInverseContractive.exists_shadowing_orbit_on_invariant_tube`
  * `UnitTangentIterates.MarkedSchemeTheoremCanonical.exists_canonical_marked_orbit`
  * Cauchy tail decay $\sum_{m \ge n} e_m \to 0$ and convergence to an exact orbit $X_{n+1} = \mathcal{T}(X_n)$ of smooth ovals.

### **Section 7: Proof of the Main Theorem**
* **Lemma 7.1 (Large-separation threshold):**
  * `UnitTangentIterates.LargeSeparationComplete.large_separation_complete`
  * `UnitTangentIterates.EndToEndModelOrbit.exists_end_to_end_model_orbit`
  * Existence of $H_*$, linear separation growth $H_n \ge H_0 + (\Delta/2)n$, and summable synchronized defect tails.
* **Excluding a circle (closing step of the proof of Theorem 1.1):**
  * `UnitTangentIterates.ClosingArgumentComplete.closing_argument_complete`
  * `UnitTangentIterates.NoncircularClosingComplete.not_isCircleOfPerimeter_of_large_separation`
  * The transverse width contradiction gap $C_W + 2d < (2H_0 - d)/\pi$, excluding circles.

*(Item numbers refer to the current `noncircular_oval_unit_tangent_iterates.tex`; the paper numbers its results by section, e.g. Theorem 6.8 is the regularizing backward shadowing theorem.)*
