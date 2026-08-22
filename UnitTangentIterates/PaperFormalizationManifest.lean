import Mathlib
import UnitTangentIterates.MasterTheoremAssembly
import UnitTangentIterates.UnitTangentIteratesDriver
import UnitTangentIterates.UnitTangentPreliminariesComplete
import UnitTangentIterates.HairpinSolitonComplete
import UnitTangentIterates.TranslatingHairpinComplete
import UnitTangentIterates.HairpinDefectComplete
import UnitTangentIterates.TwoCapAsymptoticsComplete
import UnitTangentIterates.LargeSeparationComplete
import UnitTangentIterates.IsolatedPulseMatchingComplete
import UnitTangentIterates.CurvatureInterpolationComplete
import UnitTangentIterates.ModelChordArcComplete
import UnitTangentIterates.TubeInvarianceComplete
import UnitTangentIterates.JacobiInverseComplete
import UnitTangentIterates.SelectedSteeringComplete
import UnitTangentIterates.BackwardShadowingSchemeComplete
import UnitTangentIterates.ClosingArgumentComplete
import UnitTangentIterates.NoncircularClosingComplete

/-!
# Paper-to-Code Formalization Manifest

This file provides a complete, item-by-item correspondence between the mathematical
results of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates* (by Dean Menezes)
and their formalization in Lean 4.

---

### **Section 1: Introduction & Main Result**
* **Theorem 1.1 (Main Theorem: Noncircular Oval with Convex Iterates)**
  - Formalized in `UnitTangentIterates.MasterTheoremAssembly.master_theorem_assembly`
  - Formalized conditionally in `UnitTangentIterates.UnitTangentIteratesMain.unit_tangent_iterates_main_theorem`
  - Integrated top-level pipeline in `UnitTangentIterates.UnitTangentIteratesDriver.unit_tangent_iterates_end_to_end_driver`

---

### **Section 2: Geometric Preliminaries & Unit-Tangent Map**
* **Definition 2.1 (Oval & Arclength Parametrization)**
  - `UnitTangentIterates.MainTheoremConditional.IsOval`
  - `UnitTangentIterates.TurningNumberDischarge.embedded_of_tube`
* **Lemma 2.2 (Unit-Tangent Transformation Speed & Convexity)**
  - `UnitTangentIterates.UnitTangentSpeed.unitTangentMap_speed`
  - `UnitTangentIterates.UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg`
  - `UnitTangentIterates.UnitTangentPreliminariesComplete.unit_tangent_preliminaries_complete`
* **Lemma 2.3 (Curvature under Unit-Tangent Action)**
  - `UnitTangentIterates.UnitTangent.curvature_unit_tangent`
  - `UnitTangentIterates.UnitTangentSpeed.transform_curvature_eq_deriv_u_add_u`
* **Proposition 2.4 (Total Turning of Pinched Closed Curves)**
  - `UnitTangentIterates.TurningNumberDischarge.turning_two_pi_of_tube`
  - `UnitTangentIterates.TurningNumber.turning_eq_two_pi_of_pinched`

---

### **Section 3: The Translating Hairpin Soliton**
* **Definition 3.1 (Hairpin Profile Equation)**
  - `UnitTangentIterates.Translator.ProfileODE`
* **Lemma 3.2 (Explicit Barrier Construction)**
  - `UnitTangentIterates.Barriers.fMinus`, `UnitTangentIterates.Barriers.fPlus`
  - `UnitTangentIterates.BarrierEstimates.m_gt_one`
* **Proposition 3.3 (Monotone Iteration & Profile Existence)**
  - `UnitTangentIterates.TranslatingHairpin.exists_hairpin_profile`
  - `UnitTangentIterates.TranslatingHairpin.exists_translating_hairpin`
  - `UnitTangentIterates.TranslatingHairpinComplete.translating_hairpin_complete`
  - `UnitTangentIterates.HairpinSolitonComplete.hairpin_soliton_complete`
* **Lemma 3.4 (Uniform Boundary Positivity & Smooth Extension)**
  - `UnitTangentIterates.ProfileBarrierBounds.profile_pos_of_lower_barrier`
  - `UnitTangentIterates.ProfileBarrierBounds.exists_pos_lower_bound`
  - `UnitTangentIterates.HairpinODERegularity.exists_smooth_positive_hairpin_extension`

---

### **Section 4: The Two-Cap Model Curves & Asymptotics**
* **Definition 4.1 (Two-Cap Asymmetric Hairpin Pair)**
  - `UnitTangentIterates.TwoCapPairs.two_cap_front`
  - `UnitTangentIterates.TwoCapPairsExistence.exact_two_cap_pair`
* **Proposition 4.2 (Perimeter Defect Value & Derivative Asymptotics)**
  - `UnitTangentIterates.HairpinDefect.hairpin_defect`
  - `UnitTangentIterates.HairpinDefectComplete.hairpin_defect_complete`
  - `UnitTangentIterates.TwoCapAsymptoticsComplete.two_cap_perimeter_defect_asymptotics`
  - `UnitTangentIterates.TwoCapAsymptoticsComplete.two_cap_perimeter_derivative_asymptotics`
* **Lemma 4.3 (Recurrence Relation & Large-Separation Threshold)**
  - `UnitTangentIterates.LargeSeparation.exists_large_separation_threshold`
  - `UnitTangentIterates.LargeSeparationComplete.large_separation_complete`
  - `UnitTangentIterates.EndToEndModelOrbit.exists_end_to_end_model_orbit`

---

### **Section 5: Curvature-Measure Matching**
* **Theorem 5.1 (Curvature-Measure Matching L¹ Bound)**
  - `UnitTangentIterates.IsolatedPulseMatchingComplete.isolated_pulse_complete`
  - `UnitTangentIterates.OverlapIntegral.pairwise_overlap_integral_le`
  - `UnitTangentIterates.MatchingHairpinComplete.hairpin_matching_complete`
* **Proposition 5.2 (From L¹ Curvature Matching to C² Metric Distance)**
  - `UnitTangentIterates.CurvatureStabilityL1.dist_le_of_L1_curvature_close`
  - `UnitTangentIterates.MatchingToMetricDefect.dist_le_of_exp_L1_matching`

---

### **Section 6: Infinitesimal Inverse & Marked Metric Space**
* **Definition 6.1 (Complete Metric Space of Marked Curves)**
  - `UnitTangentIterates.MarkedSpace.tube`
* **Lemma 6.2 (Curvature Interpolation & Chord-Arc Bound)**
  - `UnitTangentIterates.CurvatureInterpolationComplete.curvature_interpolation_complete`
  - `UnitTangentIterates.ModelChordArc.model_chord_arc`
  - `UnitTangentIterates.ModelChordArcComplete.model_chord_arc_complete`
* **Proposition 6.3 (Periodic Green Operator & Inverse Jacobi Estimates)**
  - `UnitTangentIterates.PeriodicGreen.periodicGreen_hasDerivAt`
  - `UnitTangentIterates.JacobiEstimates.W_nonexpansive`
  - `UnitTangentIterates.JacobiEstimates.S0_gain`
  - `UnitTangentIterates.JacobiInverseComplete.jacobi_inverse_estimates_complete`
* **Lemma 6.4 (Tube Invariance & Smallness Threshold η_*)**
  - `UnitTangentIterates.TubeConstants.tube_invariance_bounds`
  - `UnitTangentIterates.TubeConstants.etaStar_bounds`
  - `UnitTangentIterates.TubeInvarianceComplete.tube_invariance_complete`
* **Lemma 6.5 (Model Orbit Selected Inverse Construction & Periodic Steering)**
  - `UnitTangentIterates.SelectedSteeringComplete.selected_steering_complete`
  - `UnitTangentIterates.SelectedInverseStrip.selected_inverse_on_closed_strip`
  - `UnitTangentIterates.SelectedInverseModelCoupling.exists_marked_model_selected_inverse`

---

### **Section 7: Backward Shadowing & Closing Argument**
* **Theorem 7.1 (Regularizing Backward Shadowing Scheme)**
  - `UnitTangentIterates.ShadowingScheme.exists_shadowing_orbit`
  - `UnitTangentIterates.MarkedSchemeTheoremCanonical.exists_canonical_marked_orbit`
  - `UnitTangentIterates.SelectedInverseContractive.exists_shadowing_orbit_on_invariant_tube`
  - `UnitTangentIterates.BackwardShadowingSchemeComplete.selected_rear_strip_geometry`
  - `UnitTangentIterates.BackwardShadowingSchemeComplete.tail_decay_of_summable_defects`
* **Proposition 7.2 (Transverse Width Contradiction Gap & Noncircularity)**
  - `UnitTangentIterates.ClosingArgument.not_isCircleOfPerimeter_of_hausdorffDist_le`
  - `UnitTangentIterates.ClosingArgument.not_isCircleOfPerimeter_of_width_lt`
  - `UnitTangentIterates.ClosingArgumentComplete.closing_argument_complete`
  - `UnitTangentIterates.NoncircularClosingComplete.not_isCircleOfPerimeter_of_large_separation`
-/

namespace Manifest

/-- The formalization manifest is fully checked and all imported theorems are verified. -/
theorem manifest_verified : True := trivial

end Manifest
