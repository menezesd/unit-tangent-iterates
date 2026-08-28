import Mathlib
import UnitTangentIterates.C2NormalPathReparam
import UnitTangentIterates.RangeClosingAdapters
import UnitTangentIterates.ControlledJunctionRangeClosing
import UnitTangentIterates.PaperControlledJunctionInputs
import UnitTangentIterates.PaperMainTheoremControlled
import UnitTangentIterates.PaperControlledJunctionInputsConstructor
import UnitTangentIterates.PaperGaugeControlledFamilyAdapter
import UnitTangentIterates.GaugeControlledClosingConfiguredModel
import UnitTangentIterates.ControlledJunctionTailLimit
import UnitTangentIterates.ModelGaugeControlledFamilyChooser
import UnitTangentIterates.VariableSpeedReparamTransport
import UnitTangentIterates.ConfiguredModelGaugeFamily
import UnitTangentIterates.RearFrenetLimitStrictness
import UnitTangentIterates.RearArclengthInverseBridge
import UnitTangentIterates.SelectedRearFrenetChain
import UnitTangentIterates.FrontFrenetTubeCompatibility
import UnitTangentIterates.InterpolationPathEtaC2Adapter
import UnitTangentIterates.PeriodicDerivativeAdapters
import UnitTangentIterates.InterpolationGaugeFieldSecondState
import UnitTangentIterates.ScalarGlobalODEC2FlowCertificate
import UnitTangentIterates.InterpolationGaugeSmoothFlow
import UnitTangentIterates.ConvexConsecutiveStrictnessCore
import UnitTangentIterates.FlowSecondDerivativeJointContinuity
import UnitTangentIterates.InterpolationGaugeCutoffSecondBound
import UnitTangentIterates.InterpolationGaugeSmoothSpecialized
import UnitTangentIterates.InterpolationPathEtaSmoothChain
import UnitTangentIterates.InterpolationControlledJunctionOutput
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
import UnitTangentIterates.CurvatureInterpolationPinch
import UnitTangentIterates.InterpolationSmooth
import UnitTangentIterates.InterpolationSelectedRearRegularity
import UnitTangentIterates.SelectedSteeringCoefficientPos
import UnitTangentIterates.PeriodicGreenCoefficientDecay
import UnitTangentIterates.PeriodicGreenUniformBound
import UnitTangentIterates.PeriodicGreenDerivativeBound
import UnitTangentIterates.PeriodicGreenSecondDerivativeBound
import UnitTangentIterates.PeriodicGreenThirdDerivativeBound
import UnitTangentIterates.CanonicalConsecutivePulsePair
import UnitTangentIterates.CanonicalConsecutivePulseJet
import UnitTangentIterates.CanonicalConsecutiveBasicAdapters
import UnitTangentIterates.CanonicalSeparationRecurrence
import UnitTangentIterates.CanonicalConfiguredModelSequence
import UnitTangentIterates.CanonicalConsecutivePaperWitness
import UnitTangentIterates.PeriodizedStripThreshold
import UnitTangentIterates.CanonicalPulseTailAdapters
import UnitTangentIterates.CanonicalConfiguredModelCapstone
import UnitTangentIterates.CanonicalConfiguredRecursiveAdapter
import UnitTangentIterates.CompatibleMarkings
import UnitTangentIterates.CompatibleSelectedRearJunction
import UnitTangentIterates.NonaffineGaugeEndpointDiffeomorphisms
import UnitTangentIterates.CanonicalConsecutiveConfig
import UnitTangentIterates.CanonicalConsecutiveGeometricCertificates
import UnitTangentIterates.CanonicalConsecutiveFinalAdapters
import UnitTangentIterates.SelectedRearGaugeQualitative
import UnitTangentIterates.InterpolationSelectedRearClosing
import UnitTangentIterates.InterpolationSelectedRearEndpoints
import UnitTangentIterates.GaugeMarkedSelectedInverseEndpoint
import UnitTangentIterates.InterpolationSelInvSupAdapter
import UnitTangentIterates.InterpolationNormalizedPeriodicAdapter
import UnitTangentIterates.ExplicitNormalizedInterpolation
import UnitTangentIterates.InterpolationGaugeSliceTransfer
import UnitTangentIterates.InterpolationVariableSpeedSelInvAdapter
import UnitTangentIterates.ModelCurvatureSmooth
import UnitTangentIterates.PeriodizedPulseSmooth
import UnitTangentIterates.ModelOrbitConfigSmooth
import UnitTangentIterates.PaperHairpinConfig
import UnitTangentIterates.PaperHairpinQuantitativeData
import UnitTangentIterates.ShiftedCurvatureJetMajorant
import UnitTangentIterates.PeriodizationPositiveMixedCertificate
import UnitTangentIterates.TransverseWidthPositivity
import UnitTangentIterates.UnconditionalAssemblyRemainder
import UnitTangentIterates.InterpolationRearCostBridge
import UnitTangentIterates.ModelChordArcComplete
import UnitTangentIterates.TubeInvarianceComplete
import UnitTangentIterates.JacobiInverseComplete
import UnitTangentIterates.SelectedSteeringComplete
import UnitTangentIterates.SelectedRearSmoothDependence
import UnitTangentIterates.RearSmoothDependence
import UnitTangentIterates.WideHairpinBounds
import UnitTangentIterates.WideHairpinSmallness
import UnitTangentIterates.ModelOrbitHairpinBridge
import UnitTangentIterates.FrontPeriodizationPositivity
import UnitTangentIterates.HairpinPulseSmooth
import UnitTangentIterates.SelInvLipUniversal
import UnitTangentIterates.SelInvTubePathDist
import UnitTangentIterates.BackwardShadowingSchemeComplete
import UnitTangentIterates.ClosingArgumentComplete
import UnitTangentIterates.NoncircularClosingComplete
import UnitTangentIterates.ApproximatePaperAssemblyResidual
import UnitTangentIterates.ApproximatePaperAssemblySelectedInverse
import UnitTangentIterates.ApproximatePullbackClosedTube
import UnitTangentIterates.ApproximatePullbackGeometric
import UnitTangentIterates.ConfiguredApproximateDefectPath
import UnitTangentIterates.ConstructedConfiguredSequenceWeighted
import UnitTangentIterates.ConstructedModelGeometry
import UnitTangentIterates.ConstructedPeriodizationAllOrders
import UnitTangentIterates.ConstructedPulseWidth
import UnitTangentIterates.ConstructedWeightedClosingGap
import UnitTangentIterates.DirectMarkedLimitOrbit
import UnitTangentIterates.PhysicalRearLimitComponents
import UnitTangentIterates.PhysicalRearLimitKinematicClosure
import UnitTangentIterates.PhysicalRearLimitCurvatureClosure
import UnitTangentIterates.ProfiledInterpolationBoundsConstructor
import UnitTangentIterates.StrictConstructedModelGeometry
import UnitTangentIterates.VariableSpeedApproximatePullback
import UnitTangentIterates.WeightedMarkedDefectThreshold
import UnitTangentIterates.WeightedRecursiveDefect

/-!
# Paper-to-Code Formalization Manifest

This file provides an audited, item-by-item correspondence between the mathematical
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
  - `UnitTangentIterates.UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg_of_turning`
    — the paper's own exclusion of `k ≡ 0`, from the turning number rather than
    as a hypothesis
  - `UnitTangentIterates.UnitTangentPreliminariesComplete.unit_tangent_preliminaries_complete`
* **Lemma 2.3 (Curvature under Unit-Tangent Action)**
  - `UnitTangentIterates.UnitTangent.curvature_unit_tangent`
  - `UnitTangentIterates.UnitTangentSpeed.transform_curvature_eq_deriv_u_add_u`
* **Proposition 2.4 (Total Turning of Pinched Closed Curves)**
  - `UnitTangentIterates.TurningNumberDischarge.turning_two_pi_of_tube`
  - `UnitTangentIterates.TurningNumber.turning_eq_two_pi_of_pinched`

---

### **Section 3: The Translating Hairpin Soliton**
* **Auxiliary profile-ODE interface (not used by the TeX route)**
  - `UnitTangentIterates.HairpinODERegularity.ProfileODE`
  - `UnitTangentIterates.HairpinODERegularity.ProfileODE.abs_second_le`
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
  - `UnitTangentIterates.HairpinPulseSmooth.exists_smooth_hairpin_pulse`

---

### **Section 4: The Two-Cap Model Curves & Asymptotics**
* **Definition 4.1 (Two-Cap Asymmetric Hairpin Pair)**
  - `UnitTangentIterates.TwoCapPairs.two_cap_front`
  - `UnitTangentIterates.TwoCapPairsExistence.exact_two_cap_pair`
  - `UnitTangentIterates.TwoCapMarked.injOn_front` — the front is embedded,
    *derived*: the prescribed curvature is strictly positive, so the tangent
    angle is strictly increasing, and `TwoCapMarked.frontAngle_add_period` makes
    its turning exactly `2π`.  No Umlaufsatz and no topological hypothesis.
  - `UnitTangentIterates.TwoCapRearEmbedded.injOn_rearTrack_of_two_cap_front` —
    the same turning identity discharges the standing hypothesis `hinjR` of the
    selected-inverse API (embeddedness of every reconstructed rear track).
  - `UnitTangentIterates.TwoCapRearEmbedded.exists_marked_two_cap_pair_of_prescribed_curvature`
    — consequently **both members of the exact two-cap pair are marked curves of
    the tube with no embeddedness hypothesis at all**, the only inputs being the
    prescribed curvature data `0 < kmin ≤ κ ≤ κ̂ < 1`, `κ` continuous and
    `H`-periodic, `∫₀^H κ = π`.
  - `UnitTangentIterates.TwoCapRearEmbedded.exists_model_selected_rear_sequence`
    — the `Aₙ = 𝔅 Q_{n+1}` side of the Section 7 pseudo-orbit, unconditionally.
  - `UnitTangentIterates.TwoCapPseudoOrbit.exists_model_pseudo_orbit` — fronts
    and selected rears together: `Qₙ` in one tube, `Aₙ` an oval with
    `𝒯 Aₙ` retracing `Q_{n+1}` as a set.  The metric defect
    `dist (Qₙ, Aₙ) ≤ eₙ` is *not* included; it remains the open input.
  - `UnitTangentIterates.TwoCapPseudoOrbit.exists_model_pseudo_orbit_of_prescribed_curvature`
    — the same conclusion from the Section 4 data *alone*: the uniform
    chord-arc bound is supplied by `ModelChordArc.model_chord_arc`, so the
    inputs are only `0 < kmin ≤ κₙ ≤ κ̂ < 1`, `κₙ` continuous and `Hₙ`-periodic,
    `∫₀^{Hₙ} κₙ = π`, and `H₀ ≤ Hₙ`.
  - `UnitTangentIterates.TwoCapPseudoOrbit.exists_model_pseudo_orbit_selInv`
    — the same pseudo-orbit written with the *map* the paper uses,
    `𝔅 = SelectedInverseMap.selInv κ̂`, rather than a chosen sequence of rears:
    `selInv κ̂ Q_{n+1}` is a tube member, an oval, and `𝒯` of it retraces
    `Q_{n+1}`.
  - `UnitTangentIterates.TwoCapPseudoOrbit.exists_model_pseudo_orbit_instance`
    — the constant (circular) model witnesses that these hypotheses are
    consistent.
  - Note that the general criterion
    `TurningNumberDischarge.turning_two_pi_of_tube` does **not** cover these
    curves: it requires `κ_max · L < 4π`, while the two-cap fronts have
    perimeter `2H → ∞`.  The exact turning identity of the prescribed curvature
    is what makes the model case unconditional.
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
  - `UnitTangentIterates.JacobiEstimates.S1_gain`
  - `UnitTangentIterates.JacobiEstimates.S2_gain` — `eq:S2gain`, with the
    explicit constant `κ̂²/c₀³ + 1/c₀ + 1`; previously only the second-order
    *identity* (`second_derivative_identity`) was present, not the estimate
  - `UnitTangentIterates.JacobiPathGains` — the same four inequalities for the
    **path functionals** `MarkedTopology.W` and `MarkedTopology.S j`, which is
    the form the lemma is stated in:
    `W_nonexpansive_path` (`eq:Wnonexp`), `S0_gain_path` (`eq:S0gain`),
    `S1_gain_path` (`eq:S1gain`), `S2_gain_path` (`eq:S2gain`).  Each integrates
    the corresponding slice estimate in `t`; integrability of the slice
    functionals is carried as a hypothesis, as elsewhere in this project.
  - `UnitTangentIterates.JacobiInverseComplete.jacobi_inverse_estimates_complete`
  - `UnitTangentIterates.InverseJacobiGeometry` — the identity `eq:inverse-jacobi`
    is now **derived from the Frenet geometry** rather than assumed.
    `Shadowing.inverse_jacobi_identity` takes the scalar formula
    `η_F = -ξ sin δ + (η_R + η_{R,x} + kξ) cos δ` as a hypothesis; the new module
    proves it:
    * `hasDerivAt_frenet_frame` : `∂ₓ(ξτ + ην) = (ξ' − kη)τ + (η' + kξ)ν`;
    * `tangent_variation_normal` : in the arclength gauge `ξ' = kη`, the
      variation `τ̇` is purely normal, `τ̇ = (η' + kξ)ν`;
    * `frontNormal_eq` : `−sin δ · τ + cos δ · ν = i e^{i(ψ+δ)}`;
    * `front_normal_of_rear_variation` : the real part of
      `conj(ν_F)·Ḟ` is `−ξ sin δ + A cos δ`;
    * `inverse_jacobi_of_geometry`, `inverse_jacobi_of_variation` :
      `(1 + ∂ₓ)η_R = sec δ · η_F` with no scalar hypothesis.
* **Lemma 6.4 (Tube Invariance & Smallness Threshold η_*)**
  - `UnitTangentIterates.TubeConstants.tube_invariance_bounds`
  - `UnitTangentIterates.TubeConstants.etaStar_bounds`
  - `UnitTangentIterates.TubeInvarianceComplete.tube_invariance_complete`
* **Lemma 6.5 (Model Orbit Selected Inverse Construction & Periodic Steering)**
  - `UnitTangentIterates.SelectedSteeringComplete.selected_steering_complete`
  - `UnitTangentIterates.SelectedInverseStrip.selected_inverse_on_closed_strip`
  - `UnitTangentIterates.TwoCapRearEmbedded.selected_inverse_on_closed_strip_two_cap`
    — the same conclusion for the paper's model fronts with the turning
    hypothesis discharged
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


/-!
### **NEW (this revision): The paper's own hairpin is now fed into the pipeline**

`HairpinAsymptoticsComplete.lean` closes the previously-declared gap that the
large-separation threshold consumed the two perimeter asymptotics as bare
hypotheses:

* `HairpinAsymptoticsComplete.exists_hairpin_pulse_package`: from the
  constructed hairpin profile, ONE canonical arclength parametrization
  produces the steering pulse with exponential decay of `y` and `y'`, relative
  derivative bounds, steering mass `∫ y = π`, and defect positivity
  `Δ = ∫ Φ(y) > 0` (paper Lemma *Hairpin pulse estimates*, fully instantiated);
* `HairpinAsymptoticsComplete.hairpin_perimeter_tail_asymptotics`: for the
  periodization of THAT pulse, the half-perimeter functional satisfies
  `R H = H - Δ + O(e^{-γH})`, is differentiable at every large `H`, and
  `R' H = 1 + O(e^{-γH})` (the asymptotic clauses of Proposition *Exact
  two-cap pairs*, produced rather than assumed).

### Status after this revision

* `HairpinAsymptoticsComplete.exists_hairpin_pulse_package` and
  `.hairpin_perimeter_tail_asymptotics` discharge item (i) below;
  the canonical package now retains `Integrable y` together with
  `∫ y = pi`, rather than discarding the integrability witness constructed
  inside `HairpinPulseMass.hairpin_pulse_mass`;
* `HairpinAsymptoticsComplete.synchronization_tail_of_perimeter_asymptotics`
  discharges item (ii): the large-separation threshold is assembled under
  asymptotics localized above an explicit threshold — no global C¹ pasting is
  needed, because every recursion/tail ingredient only acts above the
  threshold;
* `SelectedRearSmoothDependence.hasDerivAt_selected_steering_time` proves
  that the selected steering family is differentiable in the path parameter,
  by convergence of its uniform difference quotients to the unique periodic
  linearized solution.  `RearSmoothDependence.hasDerivAt_selected_rearTrack`
  propagates that derivative to the reconstructed rear track.  Together they
  discharge the paper's Lemma *Smooth dependence of the selected rear*.
* `SelInvLipUniversal.dist_selInv_le_lipUniversal_pathDist` and
  `SelInvTubePathDist.dist_selInv_le_lipUniversal_pinchedPathDist` reduce the
  selected-inverse metric estimate to an explicit universal Lipschitz
  constant and the pinched-path pseudodistance.
* `WideHairpinBounds.exists_wide_pulse_relative_data` turns the translator
  barrier lower bound into the explicit pulse scale
  `y <= 1 / (eps⁻¹ - eps)`, together with the first two relative derivative
  bounds.  `ModelOrbitHairpinBridge.exists_second_steering_data` places the
  two-derivative pulse, the rear-speed identity, and the steering identity on
  one common pair of hairpin coordinates; `eq_modelRearArclength` identifies
  that coordinate with `ModelOrbitDefect.modelRearArclength`, and
  `pulse_identity_modelRear` transports the exact isolated curvature identity
  to that model coordinate.
* `InterpolationSmooth.contDiff_three_uncurry_interpCurve` now supplies the
  joint `C³` regularity of the explicit curvature-interpolation front family
  from `C³` endpoint curvature data.
* `InterpolationSelectedRearRegularity.interpolation_selectedRear_core_data`
  combines the explicit interpolation with smooth selected-steering dependence
  and the global rear-arclength inverse.  From `C⁴` endpoint curvatures it
  supplies joint `C⁴` regularity of the front, tangent angle, selected steering,
  and inverse rear arclength, together with all four spatial ODE identities
  consumed by the variable-speed front-to-rear interface.
* `SelectedRearGaugeQualitative.exists_canonical_gauge_jacobi_data` chooses
  the rear velocity canonically from the joint derivatives and supplies its
  joint `C³` regularity, joint `C³` rear-angle regularity, joint `C¹` rear
  curvature, the actual rear-family time derivative, and the inverse Jacobi
  ODE.  These qualitative frame/Jacobi inputs therefore no longer need to be
  assumed separately.
* `InterpolationSelectedRearClosing.interpolation_selectedRear_closing_data`
  fixes the half-period/full-period convention and supplies closed-front
  periodicity, `2π` tangent turn, positive rear period bounded by the front
  period, closed rear slices, rear-angle turn, and the raw interpolation
  endpoint identities.
* `InterpolationSelectedRearEndpoints.marked_rearEndpoint_eq_selInv` turns
  either raw endpoint into the exact value of the marked selected-inverse map
  as soon as that rear endpoint is a tube datum with the canonical affine
  rear-arclength marking.  Existence and uniqueness of the selected inverse,
  including uniqueness of its steering angle, are supplied by the existing
  `SelectedInverseRearOwn`/`SelectedInverseMap` construction.
* A terminal gauge marking is generally not affine and hence is not literally
  the same `MarkedSpace.Data`.  The correct endpoint conclusion is recorded by
  `GaugeMarkedSelectedInverseEndpoint.gauge_marked_endpoint_same_selectedInverse_geometry`:
  a surjective normalized gauge marking fixing zero preserves the curve image
  and marked basepoint.  `gauge_marked_position_eq_iff` isolates the stronger
  parameter-invariance condition that literal equality would require.
  `surjective_normalized_of_quasiPeriodic` now derives the needed surjectivity
  from continuity, strict spatial monotonicity, period transport, positivity
  of the transported period, and basepoint fixing.
* The marked path pseudodistance is not invariant under a general spatial
  reparametrization: `position_eq_of_pathDist_eq_zero` proves that zero
  `pathDist` (when a normal path exists) forces pointwise equality of the
  parameterized position components.  Hence same image and basepoint cannot
  replace literal marked equality in the current metric architecture.
* `InterpolationSelInvSupAdapter.exists_sup_fundamental_qualitative_inputs`
  packages the smooth interpolation data in the exact qualitative form used
  by `SelInvRearFamilySupFundamentalC2.dist_selInv_le_of_rear_family_sup_fundamental_C2`:
  canonical rear velocity, its time derivative identity and `C³` regularity,
  `C³` rear angle, `C¹` rear curvature, and the inverse Jacobi ODE.  That
  comparison theorem handles the nonaffine terminal marking quantitatively via
  `MarkingFlowDefectC2`, so endpoint equality or zero distance is not required.
* `InterpolationNormalizedPeriodicAdapter.normalized_periodic_inputs` packages
  the canonical normalized derivatives `pathVel`/`pathAcc`, constant speed,
  slice and derivative periodicity, and total turning `2π` in the form used by
  the sup-fundamental comparison.  The basepoint condition `Γ.eta t 0 = 0`
  remains explicit because it is a marking choice rather than a closing
  consequence.
* `ExplicitNormalizedInterpolation.normalized_interpCurve_data` instantiates
  the raw normalized slices `u ↦ X_t(2Lu)`: they are jointly `C³`, one-periodic,
  have positive full perimeter `2L`, and inherit the endpoint curvature lower
  and upper bounds throughout `t ∈ [0,1]`.  Identifying these raw slices with
  the normal-gauge path would be incorrect: the gauge flow is generally
  nonaffine.
* `InterpolationGaugeSliceTransfer` gives the exact bridge to the `pathCurve`
  used by `InterpolationPathDist.exists_normalPath_interp`.  It transfers
  closing and sampled curvature bounds, and proves that gauge-slice speed is
  exactly `|∂ᵤ Phi|`.  Hence the constant-speed input of
  `SelInvRearFamilySupFundamentalC2` needs the explicit extra hypothesis that
  this derivative has constant norm; it is not supplied by the raw normalized
  interpolation.  The remaining comparison inputs are the marking/basepoint
  choice and the quantitative front/rear tube estimates.  Without constant
  gauge speed, the paper-faithful continuation is the variable-speed interface
  in `GaugeRearFamilyFromFront`.
* `InterpolationVariableSpeedSelInvAdapter.dist_selInv_le_terminalDefect_add_integralCost`
  is the paper-faithful terminal comparison for that interface.  It applies
  the variable-speed `C²` increment estimate directly to the generated rear
  path, with no constant-speed or tube-membership hypothesis, and leaves only
  the marked `C²` distance from its nonaffinely gauge-marked terminal endpoint
  to the canonical selected inverse.  This is exactly the terminal
  `MarkingFlowDefectC2` term, rather than an endpoint-equality assumption.
  Its strengthened theorem
  `dist_selInv_le_of_gaugeFlow_and_variableSpeed` derives that terminal term
  directly from the gauge ODE, the first two spatial derivatives of its
  field, and their cost-density bounds.  The terminal endpoint therefore no
  longer appears as an unexplained distance hypothesis.
  `exists_terminalCertificate` further derives the canonical terminal
  selected-inverse tube member, its stored curve/velocity derivatives, and
  its tangent lift with the sharp bounds
  `kh/sqrt(1-kh^2)` and `2kh/sqrt(1-kh^2)^3`, directly from the endpoint
  front tube data.  Those terminal geometric inputs are therefore no longer
  independent assumptions.
  `GaugeRearFamilyFundamental.selectedRear_gaugeField_certificate` now exports
  the exact field used by the produced marking, `R=-xi`, together with its
  first two spatial derivatives, their joint continuity and derivative
  identities, and the sharp bounds `rearKappa1 kh * Gamma.m` and
  `rearKappa2 kh * Gamma.m`.  These estimates were formerly local to the
  variable-speed construction proof and can now be fed directly to
  `MarkingDefectCostC2`.  `selectedRear_gaugeField_global_bounds` uses the
  normal path's continuous stopped density to choose the remaining global
  Lipschitz and second-derivative constants automatically.
  `InterpolationVariableSpeedSelInvAdapter.dist_selInv_le_of_selectedRear_gauge`
  performs the final wiring: it uses the selected-rear path itself for both
  the gauge-marking defect and the variable-speed increment, derives period
  transport from the tangential closing relation, and consumes the canonical
  endpoint certificates.  Its conclusion is the concrete marked-distance
  estimate required before the marked pullback-limit construction.
  `PaperFaithfulAssemblyRemainder.pullbackSteps_of_baseDefects` propagates the
  normalized one-step gauge/interpolation bound through every selected-inverse
  pullback using nonexpansiveness, in exactly the `hstep` form required by
  `ofPullbackSteps`; `summable_pullbackSteps_of_baseDefects` pairs it with the
  existing summable defect sequence.  Tube invariance and the strict-oval
  regularity upgrade remain the separate geometric inputs.
  `summable_pullbackSteps_of_selectedRearBounds` makes the final normalization
  explicit: the detailed `markingC2Bound + c2ConstVar * cost` output is first
  bounded by the chosen L1-matching defect `d n` using the standard smallness
  thresholds, and the resulting base inequality is then propagated. 
  For the paper-faithful `kmin = 0` tube,
  `PaperFaithfulAssemblyRemainder.pullback_mem_closedTube` proves the exact
  sequence-level `hmem` statement from
  `ClosedTubeInvarianceResidual`: membership of each model and preservation of
  the closed tube by one selected-rear step.  The induction and the stopped
  curvature ceiling require no positive lower curvature.  The exact residual
  is the one-step embedded/chord-arc preservation theorem at zero lower
  pinching; current `SelectedInverseMap.selInv_spec` and rear-track injectivity
  still assume a strictly positive input lower bound.
  `SelectedInverseDenseCauchyData.toSelfCompletion` now performs the exact
  completion assembly: finite canonical selected inverses preserving the
  nonnegative tube, density of positive-curvature members, and convergence of
  their images along the additive Jacobi/path-cost filter produce
  `SelectedInverseSelfCompletionData`.  Its theorem
  `closedSelInv_rightInverse_of_selInv` transfers the finite right-inverse
  identity to the completed operator by continuity, so that identity is no
  longer an independent capstone assumption.  The remaining unproved bridge
  is stated without concealment: positive-curvature regularization must be
  dense in the marked closed tube and the Jacobi/path-cost estimate must imply
  the displayed image-filter limit.  Marked-distance nonexpansiveness is not
  inferred from the available path-cost Lipschitz estimates.
  `selectedInverseDenseCauchyData_of_invariance` supplies its finite
  preservation field directly from `ClosedTubeInvarianceResidual`; hence the
  completion no longer repeats tube invariance as a separate certificate.
  A constructive-density audit identifies a further boundary issue in the
  present formulation.  Replacing a nonnegative curvature by
  `(1-epsilon) K + epsilon (pi/H)` gives strict positivity and convergence of
  the reconstructed marked data, but it does not by itself prove membership
  in the same closed tube: one must still show
  `dlt * cyc u v <= ‖X_epsilon u - X_epsilon v‖` with the original `dlt`.
  Uniform convergence proves this inequality for the limit from inequalities
  for the approximants (`MarkedSpace.isClosed_tube`), not conversely.  The
  available `IsTubeMember.mono` only permits lowering the requested chord
  constant.  Consequently `IsDenseInducing positiveToNonnegative` requires a
  new chord-monotonicity theorem for this specific regularization, a strict
  chord-margin hypothesis, or a redesigned completion over varying tube
  constants; it cannot presently be claimed from curvature regularization
  alone.  The selected-rear image-Cauchy argument can only be applied after
  this domain approximation issue is resolved.
  The fixed-chord subtype completion is therefore not the primary paper
  route.  `exists_nonnegative_shadowing_of_summable_normalPaths` specializes
  `TubePullbackLimit.exists_shadowing_limit_of_radii` at `kmin = 0`.  It
  transports each interpolation normal path through the selected inverse,
  concatenates the resulting paths with costs bounded by
  `K^k d (n+k)`, and applies
  `SummableNormalPathLimit.exists_limit_of_summable_costs`.  The latter uses
  `NormalPathC2Increment.dist_le_cost`; its expanded theorem
  `markedC2_tendsto_of_summable_costs` records uniform convergence of curve,
  velocity, and acceleration, derivative closure, periodicity, and the
  positive limiting speed.  The pullback theorem then derives the exact
  inverse orbit by continuity and supplies the position and perimeter tail
  bounds.  Thus the capstone can consume path transport, interpolation defect
  paths, closed-tube invariance, and `LimitStrictnessData` directly, without
  density of positive members or marked-metric nonexpansiveness.
  This normal-path theorem does not, by itself, discharge
  `LimitStrictnessData`.  Its expanded conclusion is regular `C2`: the curve,
  velocity, and acceleration converge uniformly and the first two derivative
  identities pass to the limit.  In contrast,
  `UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg` explicitly
  needs a derivative of the limiting curvature (`HasDerivAt k k'`), hence the
  corresponding curve regularity is effectively `C3`.  Closed-tube membership
  supplies nonnegative curvature and embeddedness, but not this derivative;
  an exact inverse-orbit equality alone also does not create it.  The remaining
  paper theorem is therefore the selected-steering ODE closure and rear
  regularity bootstrap along the normal-path limit.  Only after that result
  may a full capstone legitimately take just transported defect paths, radius
  inequalities, and tube invariance as inputs.
  A further correspondence audit is essential here.  The current forward
  orbit interface records only
  `range (ev (T p)) = range (unitTangentMap (ev p))`; it does not identify
  points with a common arclength parameter.  Therefore it cannot be rewritten
  as the pointwise bicycle identity `F(s) = R(s) + tau_R(s)`.
  `RearRegularity.rear_contDiff` likewise requires explicit tangent-angle
  lifts `Theta`, `Psi` and the steering ODE
  `Psi' = sin (Theta-Psi)`, rather than equality of curve ranges.  The precise
  missing adapter must retain the selected inverse's arclength correspondence
  (including any marking shift), prove the pointwise front/rear identity and
  steering equation at the limit, and only then invoke the regularity gain.
  Range-level unit-tangent realization is sufficient for the final geometric
  orbit statement but not for this regularity bootstrap.
  The appropriate finite-stage datum has now been identified precisely as
  `SelectedInverseMap.IsMarkedSelectedInverse`.  It stores the front tangent
  angle and curvature, steering angle, inverse rear-arclength coordinate,
  steering ODE, period and strip bounds, perimeter transport, and the
  pointwise reconstructed rear identity.  Marked `C2` convergence alone,
  however, converges only the curve, velocity, and acceleration components of
  `Data`; it gives no convergence of the witnesses `Theta`, `K`, `dl`, or
  `sf`.  Closing the specialized correspondence therefore requires uniform
  compactness/ODE-stability estimates for the steering witnesses and stability
  of the inverse rear-arclength maps, or an equivalent theorem that the
  selected-rear reconstruction is continuous with these witnesses.  Merely
  retaining `IsMarkedSelectedInverse` at every finite pullback does not pass
  its existential witnesses through the limit.
  The scalar ODE ingredients for this adapter are already formalized:
  `SteeringExistence.exists_periodic_steering` constructs the selected
  periodic solution for continuous `0 <= K <= kap <= 1`,
  `SelectedRear.steering_sup_dist_le` gives its uniform Lipschitz dependence
  on curvature for a common period, and
  `RearDependence.rear_depends_continuously` propagates this to rear position,
  tangent, speed, and curvature.  What is not yet packaged is the
  variable-period passage required by marked convergence: rewrite the ODE on
  period one using `P_n * K_n (P_n u)`, prove these normalized curvatures
  converge uniformly as `P_n` varies, apply steering stability there, and
  prove convergence of the inverse primitives of `cos delta_n`.  This is the
  concrete remaining route to close `IsMarkedSelectedInverse` and invoke
  `RearRegularity.rear_contDiff` at the limit.
  Two existing results shorten that route.  `MarkedTopology.MarkedC2Tendsto`
  already states uniform convergence of curvature and speed in one transported
  parameter, so a pullback-level version can avoid reconstructing normalized
  curvature convergence from scratch.  `HairpinLimit.tendsto_inverse_points`
  proves stability of inverse points from uniform primitive error and a common
  positive slope lower bound; it applies to the primitives of `cos delta_n`
  once steering convergence is known.  A uniform-on-compact upgrade of that
  pointwise inverse estimate, followed by the rear reconstruction bounds in
  `RearDependence`, is the remaining reusable adapter.

  **Resolution of both obstacles above.**  The entire route just described was
  needed only because `curvature_pos_of_transform_curvature_nonneg` consumes a
  *differential* hypothesis, `HasDerivAt k k'` together with nonnegativity of
  the transformed curvature.  A differential inequality is not closed under
  pointwise limits, which is exactly why the finite-stage witnesses `Theta`,
  `K`, `dl`, `sf` had to survive the passage, and hence why the arclength
  correspondence and the pointwise bicycle identity were required.
  `UnitTangent.curvature_pos_of_harnack` replaces that hypothesis by its
  *integrated* form, the paper's bounded-shift Harnack inequality
  `exp (a - b) * (k a / sqrt (1 + k a ^ 2)) <= k b / sqrt (1 + k b ^ 2)`
  for `a <= b`, and `UnitTangent.harnack_of_next_nonneg` shows the integrated
  form is implied by the differential one, so nothing is lost at finite stage.
  Being a closed condition on the curvature values alone, it *is* stable under
  pointwise limits (`UnitTangent.harnack_of_tendsto`).
  Consequently `UnconditionalAssembly.limitStrictnessDataH_of_tendsto`
  discharges `LimitStrictnessDataH` at the limit from strictly `C2` data — the
  curve, angle and curvature relations, periodicity, nonnegativity — plus
  pointwise convergence of the approximating curvatures and the Harnack
  inequality at each finite stage.  No third derivative, no steering witness
  convergence, no variable-period ODE stability, and no arclength
  correspondence between levels is used.  The `C3` regularity bootstrap and
  the correspondence audit it forced are therefore both discharged, not
  postponed; range-level unit-tangent realization, which the paragraph above
  already records as sufficient for the final geometric orbit statement, now
  suffices outright.  The `IsMarkedSelectedInverse` route remains formalized
  and correct, but is no longer on the critical path.
  `PaperFaithfulAssemblyRemainder.abs_rightInverse_sub_le_of_uniform` now
  supplies the needed uniform upgrade directly: if the limiting primitive has
  slope at least `m > 0`, the primitives are uniformly `e`-close, and their
  right inverses have the same target, then the inverse maps are uniformly
  `e/m`-close.  No Arzela-Ascoli or compact-period reduction is required for
  this step.
  Endpoint witness compatibility is now expressed intrinsically in
  `UnconditionalAssemblyRemainder`: `intrinsicSpeed`, `intrinsicTangent`, and
  `intrinsicCurvature` are read from the stored velocity and acceleration;
  `intrinsicSpeed_eq_period_of_slice` and
  `intrinsicTangent_eq_exp_of_slice` identify the first two with the `P` and
  `exp(i theta)` witnesses of `IsConstantSpeedNormalPath`.  The proof uses the
  existing exact endpoint formula `NormalPathC2Increment.vel_eq_of_slice`, so
  no choice of tangent-angle lift is compared across adjacent paths.  The
  analogous curvature identification is reduced to
  `NormalPathC2Increment.acc_eq_of_slice`.
  `NormalizedSelectedRearClosure` now isolates the safe period-one closure
  layer outside the quarantined assembly file.  `SteeringData` records the
  normalized periodic ODE, `steering_sup_dist_le` applies the existing selected
  steering stability theorem at common period one, and
  `inverse_sup_dist_le` gives the global uniform convergence estimate for the
  inverse rear-arclength coordinates.  `ClosureEstimate` records the exact
  position, tangent, and curvature bounds supplied by `RearDependence` after
  those two steps.
  The estimate feeds the marked-limit/shadowing construction; it is not a
  field of `PaperFaithfulAssemblyRemainder`, whose `shadowing_orbit` field is
  already the output of that construction.  The legacy fixed-positive record
  is the one that separately names `marked_interpolation_defect`.
  a chosen `NormalPath` remains an explicit gauge-path equality, since the
  ungauged interpolation itself has tangential velocity.
* `HairpinPulseSmooth.exists_smooth_hairpin_pulse` supplies every finite
  differentiability order for the isolated pulse coordinates, while
  `PeriodizedPulseSmooth.contDiff_three_periodizedPulse` obtains `C³`
  periodizations by three justified termwise differentiations, and
  `contDiff_three_modelCurvature_of_derivative_chain` turns a five-member
  exponentially decaying derivative chain directly into the `C³`
  model-curvature endpoint consumed by that interpolation theorem.
  `ModelOrbitDefect.Config.contDiff_three_modelCurvatures_of_derivative_chains`
  applies this simultaneously to the two endpoint curvatures of a configured
  model-orbit step and derives their strict strip hypotheses from the bounds
  already stored in the configuration.
* `PaperHairpinConfig.PaperHairpinData.toConfig` isolates the remaining raw
  configuration hypotheses from the common-phase identity: normalized
  hairpin rear-coordinate data discharge `Config.hid` through
  `ModelOrbitHairpinBridge.phase_identity_modelRear`, while the period, decay,
  positivity, mass, and quantitative matching fields remain explicit in the
  `ConfigRemainder` completion package.
  `PaperHairpinConfig.PeriodizedStripData.periodized_abs_le` now derives the
  configuration's strip field from pointwise decay, a pulse supremum, and the
  explicit overlap budget.  `CurvaturePositivityData.of_large_period` derives
  the paper's geometric positivity branch from the established front
  periodization error and a large-period inequality.
  `PaperHairpinConfig.RearCellData.of_tail_bounds` derives `Config.hPdef'`,
  both centered-cell endpoint bounds, and `Config.hPH` from the existing rear
  tail estimates after choosing the rear period by definition.  The remaining
  scalar choices are exposed together as `QuantitativeConstants`.
  `SeparationConstants.exists_threshold` proves that its three
  separation-dependent exponential inequalities hold beyond one common
  threshold (using `P >= H - 2B`), leaving only the fixed inequalities in
  `ProfileConstants`.
  `ConfigRemainder.of_certificates` now performs the full field-by-field
  construction of the remainder from the fixed profile constants, pulse-pair
  analytic data, derived current-strip and rear-cell certificates, and the
  geometric positivity certificate.  Its theorem
  `ConfigRemainder.exists_separation_threshold` absorbs all three remaining
  exponential inequalities into one eventual separation threshold.  Thus the
  opaque completion function is no longer the only configuration interface;
  the genuinely unconstructed inputs are exactly the two consecutive
  pulse-function certificates (including the prior periodized strip), their
  positivity comparison, and the current rear-cell/strip estimates.
  `PaperHairpinData.exists_threshold_toConfig_of_consecutive` is the
  recurrence-indexed endpoint of this assembly: with
  `rearPeriod(y,Hnext)=Hcurr` it produces the actual `toConfig` result for
  every sufficiently large `Hnext`, deriving the common-phase field and all
  scalar smallness internally.
* `FrontPeriodizationPositivity.overlapDensity_le_cell` proves the missing
  pointwise relative-overlap estimate with the explicit coefficient
  `8 C exp (-(alpha/2) P)`.  Combining it with the infinite front-error sum,
  the hairpin lower comparison, and periodic reduction,
  `hairpin_and_modelCurvature_nonneg_of_large_period` proves simultaneous
  nonnegativity of the isolated and periodized front curvatures whenever
  `8 lipConst(a) D C exp (-(alpha/2) P) <= b0`.  Its conclusion directly
  supplies the geometric branch of `ModelOrbitDefect.Config.hcurvNonnegU`.
  `exists_largePeriod_positivity_threshold` proves this coefficient condition
  and the geometric-series condition eventually in `P`, while
  `exists_threshold_hairpin_and_modelCurvature_nonneg` packages the resulting
  eventual positivity for direct use in the paper's `Config` assembly.
* `PaperHairpinConfig.PulseMassData` bundles integrability and exact steering
  mass.  `PulseMassData.of_exp_decay` derives its integrability field from the
  exponential envelope, and `exists_of_hairpin_profile` constructs the full
  certificate from the canonical paper hairpin.  The current and previous
  pulse certificates are now explicit inputs of `PaperHairpinData.toConfig`,
  so the four `Config.hyint`, `hmass`, `hyuint`, and `hmassu` obligations are
  discharged as two coherent packages rather than hidden in `ConfigRemainder`.
* `PaperHairpinQuantitativeData.exists_data` now collects, on one canonical
  coordinate pair, all profile-side finite-order smoothness, exponential
  constants, relative derivative constants, mass, first-moment integrability,
  positive defect, and perimeter value/derivative asymptotics.  Its
  `Data.wide_pulse_and_derivative_bounds` combines these constants with the
  barrier estimate to obtain the absolute `2 D_j eps` bounds for every order.
  `Data.exists_profileConstants_of_wide` chooses all fixed scalar majorants
  appearing in `PaperHairpinConfig.ProfileConstants`, and
  `exists_profileConstants_and_wide_bounds` packages that certificate with
  the actual wide-profile bounds.  `Data.rearCell_mass_budget` converts the
  exact pulse mass into the `B=((1+b)/2)pi` hypothesis of `RearCellData`, and
  `Data.positive_defect` exposes the strict recursion input.
  `Data.fixed_wide_profile_quantifier_order` records the TeX's actual choice
  order: first fix `eps <= 1/40` and its translator, obtaining intrinsic and
  steering curvature at most `1/20`; then produce that fixed profile's finite
  `C_j,D_j`; finally enlarge the separation to absorb the resulting overlap
  constants.  The paper does not require uniform control of
  `eps * D_j(eps)` across an epsilon-indexed family, so no such unsupported
  requirement remains in this manifest.

### Faithfulness findings recorded in Lean

* **The uniform curvature floor is incompatible with the paper's separations.**
  `MasterTheoremAssembly.master_theorem_assembly` assumes both a positive floor
  `0 < kmin <= kappas n s` and total turning `int_0^{H_n} kappa_n = pi`.
  `CurvatureFloorObstruction.separation_le_of_curvature_floor` proves these
  force `H_n <= pi / kmin`, and
  `CurvatureFloorObstruction.not_forall_of_curvature_floor_of_linear_growth`
  proves they are outright contradictory with the paper's `H_n >= H_0 + (Delta/2) n`.
  The paper assumes only a common curvature *ceiling* `kappa_0 < 1`; the minima of
  the periodized hairpin decay like `e^{-beta H_n}`.  The hypotheses are still
  satisfiable (by a constant-separation family, as in `AdmissibleFrontFamily`),
  so the theorem is not vacuous -- but it cannot be applied to the pseudo-orbit
  it is meant for.  A faithful statement must let the lower bound depend on `n`,
  or drop it in favour of the closed `kmin = 0` tube of
  `UnconditionalAssembly.PaperFaithfulAssemblyRemainder`.

* **The global barrier hypothesis is inconsistent with the extension route.**
  `Data.wide_pulse_and_derivative_bounds` asks for `forall t, fMinus eps t <= f t`,
  but the smooth positive extension produced by
  `ProfileExtension.exists_contDiff_pos_extension_pi` is identically `1` off a
  collar of `[0,pi]`, while the barrier lower bound is `eps^{-1} - eps > 1`.
  Every proof uses the hypothesis only at angles in `[0,pi]`;
  `WideHairpinLocalBounds` restates the whole chain that way.

* **The curvature floor: the constructive correction.**
  `CurvatureFloorFreeFamily` completes the diagnosis above into a fix.  The
  explicit family `H_n = 2*pi + n`, `kappa_n = pi / H_n` satisfies every
  remaining hypothesis of the model family — continuity, `H_n`-periodicity,
  nonnegative curvature, ceiling `1/2 < 1`, total turning `pi`, `H_0 <= H_n` —
  **with `H_n` unbounded** (`exists_unbounded_floor_free_family`), and no
  positive floor bounds it from below (`no_positive_floor`).  Moreover
  `MarkedSpaceChord.exists_tube_member_of_oval_chord` never uses `0 < kmin`, so
  `exists_model_orbit_tube_zero_floor` builds the model orbit in the closed
  `kmin = 0` tube.  Conclusion: the model family's curvature hypothesis should be
  **nonnegativity**, and then the separations are free to grow, as the paper
  requires.  (The uniform chord-arc constant must then come from somewhere other
  than `ModelChordArc.model_chord_arc`, whose proof does use `0 < kmin`.)

* **The profile regularity demanded exceeds the paper's.**  The paper proves
  `f_eps in C^infinity(0,pi)` and states explicitly that no endpoint values are
  assigned.  `HairpinInteriorRegularity` shows the two hairpin fields are
  pointwise in `f`, hence localize, and that composition with an angle map into
  the open interval restores the global smoothness the packages consume; so the
  global `ContDiff R infinity f` hypothesis is removable at the point where it
  enters (`contDiff_nat_hairpin_coordinates`).  The one place it is *not* yet
  removable is `RelativeDerivatives.abs_iteratedDeriv_le`, whose uniform
  constant comes from compactness of `Icc 0 pi`; the paper instead gets those
  constants from the bounded-shift Harnack estimate, and only orders `j <= 4`
  are ever consumed (`CanonicalConsecutivePulseJet` uses `relative 0..4` and
  `smooth_pulse 0, 4`).  `PulseRelativeHigherOrder` supplies orders three and
  four of `eq:relative-y-derivatives` by that route.
  `HairpinInteriorRegularity.exists_hairpin_coordinates_interior` now produces
  the angle `theta`, the inverse front arclength `x`, their autonomous
  equations, and every finite smoothness order of `theta`, of the state
  `w = theta o x` and of the pulse — from `ContDiffOn R infinity f (Ioo 0 pi)`
  and a barrier lower bound alone, with no hypothesis at or beyond the
  endpoints.  Note that interior regularity alone does *not* give the
  relative-derivative constants: `f(t) = 2 + t^3 sin(1/t^2)` is smooth and
  positive on `(0,pi)` and satisfies the barriers while violating the
  order-one relative bound.  Those constants come from the translator equation,
  which is extra structure, not extra regularity.
  `PulseIteratedDeriv` closes the last gap on that route for the orders the
  development consumes: it identifies the named front-arclength derivatives
  `pulseD, pulseDD, pulseDDD, pulseDDDD` with `iteratedDeriv 1..4` of the pulse,
  and records `pulse (curvField f o theta) x = fun s => pulseField f (theta (x s))`
  and `frontLen (curvField f o theta) = frontArclength f theta` (both
  definitional).  So the Harnack-route bounds now read literally as
  `|iteratedDeriv j (fun r => pulseField f (theta (x r))) s| <= D_j * pulseField f (theta (x s))`,
  which is the shape of `Data.relative`.

* **Exponential tails without endpoint regularity (Stage 5, second half).**
  `HairpinTailsInterior` restates the order-zero tail chain
  (`hasDerivAt_frontArclength`, `frontArclength_le`, `le_frontArclength`,
  `abs_frontArclength_le`, `abs_pulseState_ge`, `pulse_decay`) with the global
  `ContDiff R infinity f` hypothesis replaced by continuity of `curvField f o theta`
  and pointwise nonnegativity — the only things those proofs ever used it for.
  `HairpinPulseDecay.sqrt_integrand_le`/`sqrt_integrand_le'` were correspondingly
  generalized in place (they had no external callers).  The tails at every order
  then follow with no new analysis, by `decay_of_relative`, which is profile-free:
  `abs_iteratedDeriv_pulse_decay_of_relative`.  This is the paper's own
  "the exponential bounds therefore extend to every derivative".

* **Backward shadowing under a Lipschitz bound instead of non-expansiveness.**
  `SelectedInverseContractive.exists_shadowing_orbit_on_invariant_tube` assumes
  `dist (B p) (B q) <= dist p q` in the marked `C^2` metric.  The paper does not
  prove that: its lemma *Inverse Jacobi estimates* gives `W(BGamma) <= W(Gamma)` --
  non-expansiveness of the `L^1` functional alone -- plus *gains* for `S0, S1, S2`.
  What the development does prove for the metric is a Lipschitz bound with an
  explicit but large constant (`SelInvLipUniversal.dist_selInv_le_lipUniversal_pathDist`).
  `LipschitzShadowing.exists_shadowing_orbit_of_lipschitz` shows that suffices:
  backward shadowing holds for an `L`-Lipschitz `B` whenever the defects satisfy
  `sum L^n e_n < infinity`, which the paper's exponentially decaying defects
  (`e_n <= C(1+H_n)^2 e^{-beta H_{n+1}}` with `H_n` growing linearly) provide.
  `exists_shadowing_orbit_of_nonexpansive` recovers the old statement at `L = 1`,
  so this is a strict generalization -- it replaces one hypothesis the paper does
  not establish by two that it does.
  `SelInvPathLipschitz` supplies the missing shape:
  `pathDist_selInv_le_mul_pathDist` bounds `pathDist (B p) (B q)` by
  `C * pathDist p q` -- the same quantity on both sides, which is what iterating
  requires -- via the generic infimum passage `le_mul_pathDist_of_costs`, whose
  per-path input is the Jacobi gains of `MarkedSelInvRegular`.  (Note that
  `SelInvLipUniversal.dist_selInv_le_lipUniversal_pathDist` bounds the *ambient*
  distance of the images by `pathDist` of the sources, which is the wrong shape
  to iterate, since `dist <= pathDist`.)  `summable_lipschitz_defects` closes the
  second input: `e_n <= C e^{-gamma n}` with `L < exp gamma` gives
  `sum L^n e_n < infinity`, and the paper's `gamma` can be made as large as one
  likes by increasing the initial separation.

* **A tempting shortcut that is unsound in spirit.**  A census of the
  projections of `PaperHairpinQuantitativeData.Data` shows that of its ~25
  fields only ten are ever cited (`relativeConst`, `relative`,
  `relativeConst_nonneg`, `smooth_pulse`, `angle_mem`, `angle_value`,
  `angle_deriv`, `inverse_value`, `state_deriv`, `mass`).  In particular the
  exponential-tail field `decay` is **never cited**, so deleting it would leave
  the development compiling and would remove the half of the
  relative-derivative work that the endpoint-free Harnack route has not yet
  covered.  That deletion would be wrong: `decayConst 0` is handed to
  `ProfileConstants` as `CU`, and `CU` reappears in
  `PulsePairAnalyticData.previous_decay` as a genuine bound on the prior pulse,
  so an arbitrary `CU` makes the downstream hypothesis unsatisfiable.  The field
  is load-bearing through its meaning, not through any citation.
  `DataDecayLink.Data.decayConst_zero_bound` records the link explicitly so the
  trap is visible.

### The interior-regularity route: verified replacement map

Every use of the global profile hypothesis `ContDiff R infinity f` in the hairpin
chain has been traced.  In each case it is used for exactly one of three things,
and each now has a verified interior replacement:

| what the global hypothesis is used for | interior replacement |
| --- | --- |
| `Continuous (curvField f o theta)` | `HairpinInteriorRegularity.contDiffOn_curvField` + `ContinuousOn.comp_continuous` (theta lands in the open interval) |
| `ContDiff` of the fields, for the ODE bootstrap | `HairpinInteriorRegularity.contDiffOn_pulseField_nat` with `HairpinPulseSmooth.contDiff_nat_of_autonomousOn` / `contDiff_nat_compOn` |
| a positive lower/upper bound for `f` on `Icc 0 pi`, obtained by compactness | the translator's explicit barrier constants `eps^{-1}-eps <= f <= eps^{-1}+4/3+3eps` |

Lemmas already converted: `exists_pulseState` (`exists_pulseState_of_continuous_comp`),
the coordinate constructor (`exists_hairpin_coordinates_interior`), and the whole
order-zero tail chain (`HairpinTailsInterior`).

Now also converted, in `HairpinMassInterior`: `integrableOn_curv_Ioi_of_comp`,
`integrableOn_curv_Iic_of_comp`, `integral_curv_eq_pi_of_comp` (the rear tangent
turns through `pi`), and `pulse_mass_of_comp` (the steering mass is `pi`) --
which supplies the `mass` field of `Data` on the interior route.

What is left on this path is the two sites in `HairpinAsymptoticsComplete`
(the perimeter-defect and threshold constants).  Note there was only ever a
handful of files on this path, not the ~28 the raw `grep` count suggests,
because most of the 75 binder sites are forwarding.

That structural point is now settled.  `Data.relative` and `Data.decay`
previously quantified over **all** orders `j`, whereas the endpoint-free Harnack
route supplies orders `j <= 4`.  A census showed the development consumes
`relative` only at `j = 0,1,2,3,4` (in `CanonicalConsecutivePulseJet`), so both
fields have been **bounded to `j <= 4`**.  `Data` therefore records less than the
paper proves -- the paper proves every order -- but exactly what the pipeline
uses, and it is now satisfiable from the paper's own hypotheses instead of only
from a global smoothness assumption the paper does not make.  The `smooth_pulse`
field needed no change, since
`HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates` gives every finite
order from interior data.

The extension route is now bypassed entirely.
`PaperHairpinQuantitativeData.exists_consecutiveData_of_interior` builds the
**consecutive** package -- the input of the model-orbit defect chain -- with no
smoothness of the profile on a neighbourhood of `[0,pi]` and no appeal to
`ProfileExtension`, i.e. it replaces
`ConsecutiveData.exists_of_smooth_extension`.  Its inputs are exactly what the
paper's theorem *Translating hairpin* and lemma *Hairpin pulse estimates*
provide, plus the translator relations.  The endpoint-regularity blocker that
this manifest recorded for gap (b) is therefore removed.

That rests on: `PaperHairpinQuantitativeData.data_of_interior`
(`DataInterior`) constructs **every field of `Data`** from

* `ContDiffOn R infinity f (Ioo 0 pi)` -- the regularity the paper proves;
* a positive lower bound for `f` on `(0, pi)` -- the paper's barrier bound;
* the hairpin coordinates of `exists_hairpin_coordinates_interior`;
* the order-zero curvature tail of `HairpinArclength.curvature_decay_arclength`,
  which was already endpoint-free;
* the relative derivative bounds at orders `j <= 4`.

Only the last is genuinely extra input, and that is faithful: interior
smoothness plus the barriers do **not** imply the relative bounds
(`f(t) = 2 + t^3 sin(1/t^2)` is a counterexample); the paper derives them from the
translator equation.  Given them, the tails at those orders are free, by
`HairpinTailsInterior.abs_iteratedDeriv_pulse_decay_of_relative`.

Two removals made this possible, both sanctioned by a usage census and both
leaving the corresponding paper results proved elsewhere: `Data.relative` and
`Data.decay` are bounded to `j <= 4` (every order consumed), and the
perimeter-asymptotics block (`defect_pos`, `defect_eq`, `beta_pos`,
`asymptoticConst_nonneg`, `threshold_pos`, `perimeter_value`, `perimeter_deriv`,
`perimeter_deriv_value`) has been dropped from `Data`, since nothing projected
it and constructing it was what forced the profile package through the
perimeter-asymptotics chain.

### Historical development log (superseded by the current audit below)

1. The paper-faithful propagation of admissible paths through the selected
   inverse.  The TeX proves `W(BΓ) <= W(Γ)` and the `S₀,S₁,S₂` Jacobi gains,
   then uses the vector tube inequalities of `TubeConstants.lean`.  The
   the normal-gauge interpolation path has a generally non-affine marking and
   therefore cannot be fed to the constant-speed interface
   `SelInvRearFamilyFundamentalC2`.  The matching conditional interface is
   `GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`.
   The concrete interpolation-to-selected-rear qualitative regularity and
   spatial ODE identities are now packaged by
   `InterpolationSelectedRearRegularity.interpolation_selectedRear_core_data`.
   Its qualitative periodic closing, rear-period bounds, and raw front
   endpoint identities are now supplied by
   `InterpolationSelectedRearClosing.interpolation_selectedRear_closing_data`.
   It remains to establish the quantitative frame/source derivative bounds
   needed by that variable-speed construction.  Once it is produced,
   `InterpolationVariableSpeedSelInvAdapter` removes the tube-membership and
   constant-speed requirements from the terminal distance step.  The exact
   canonical terminal selected-inverse tube/curvature data are now discharged
   by `exists_terminalCertificate`.  The remaining inputs are the quantitative
   gauge-field derivative bounds consumed by `MarkingDefectCostC2`; the `MarkingFlowDefectC2`
   inequality itself is derived.  No endpoint equality, zero-distance, or
   manually supplied terminal-distance step is required.  The
   current marked-space driver instead assumes a
   stronger scalar path-metric map bound.  In particular,
   `selInvLipUniversal <= 1` is not asserted by the paper.
2. The defect estimate for the paper's two-cap model orbit —
   `dist (Qₙ) (B (Qₙ₊₁)) ≤ eₙ` with `eₙ` summable.  The analytic
   curvature-measure estimate is proved in
   `MatchingHairpinComplete.hairpin_matching_complete`, and
   `ModelOrbitDefect.pathDistRigid_selInv_model_orbit` derives the orbit bound
   from `ModelOrbitDefect.Config`.  What remains is to construct that full
   `PaperHairpinConfig.ConfigRemainder` package from the paper's hairpin.  Strip
   control and curvature positivity now have derived certificate interfaces;
   rear cell/period estimates now also have a derived certificate interface.
   Mass and fixed `ProfileConstants` are now supplied by
   `PaperHairpinQuantitativeData`, and
   `ConfigRemainder.exists_separation_threshold` performs the actual `Config`
   field assembly after a single large-separation choice.  What remains is to
   instantiate its explicit `PulsePairAnalyticData`, prior periodized-strip
   and positivity certificates coherently for each consecutive pair in the
   recursive hairpin sequence.  It also remains to transfer the rigid path-distance estimate to the marked tube
   `PaperHairpinQuantitativeData.ConsecutiveData` now supplies the correct
   same-profile coherence package: it carries the translator map and an
   explicit pulse derivative, defines the prior pulse as the canonical phase
   translate of the current pulse, and its `local_phase` theorem derives the
   exact `PaperHairpinData.local_phase` identity from
   `HairpinFrontCurvature.front_curvature_identity_shifted`.
   `TranslatorData.transfer_extension` proves that every translator identity
   survives a smooth extension agreeing on `[0,pi]`, and
   `ConsecutiveData.exists_of_smooth_extension` then constructs `Data`, an
   explicit pulse derivative, and `ConsecutiveData` on that one extension.
   The remaining profile regularity boundary is now isolated exactly.
   `TranslatorConsecutiveBridge` restates
   `ConsecutiveData.exists_of_smooth_extension` in the shape the translator
   construction delivers (`forall n, ContDiffOn n`, and positivity on the whole
   line), discharging the notational half of the mismatch via
   `contDiffOn_infty`.  What is left is a single analytic statement: the
   translating-hairpin profile is smooth on a *neighbourhood* `(-r, pi+r)` of the
   closed angle interval, whereas
   `TranslatorTranslation.exists_translating_hairpin_translation` proves
   smoothness only on the open interval `(0, pi)`.  That widening is genuinely
   extra — smoothness on an open interval does not extend to its closure — and
   it is not assumed anywhere: `exists_consecutiveData_of_profile` takes it as
   an explicit hypothesis.  Since every canonical angle lies in `(0,pi)`, the
   paper needs only this interior smoothness.  The Lean constructor
   `exists_data` and its upstream decay/relative-derivative packages currently
   request global `ContDiff f`; they should be localized to `ContDiffOn
   (0,pi)` (or supplied directly from their already stored pulse data).
   Treating the translator and smooth extension as independent profiles would
   destroy the phase identity and is not valid.
   An auxiliary endpoint-continuation route is staged soundly by
   `HairpinODERegularity.ProfileODE`: it stores the two derivative witnesses
   and `f''+f=f^{-3}` on the interior, while `ProfileODE.abs_second_le` derives
   the uniform bound `|f''| <= M+m^{-3}` directly from the global positive
   barriers.  The remaining step is to prove that the constructed fixed-point
   profile satisfies this ODE package; no such implication is presently
   asserted, and this auxiliary ODE is not substituted for the TeX argument.
   On the paper-faithful route,
   `HairpinPulse.curvature_deriv_eq_of_translator` solves the established
   Frenet/translation identity for
   `K'=(1+K^2)sqrt(1+K^2)(K o sigma)-K-K^3` without endpoint hypotheses.
   `HairpinTails.sin_le_exp_of_logHalf_sub_le` and
   `curvField_shift_harnack` now derive the required bounded-shift comparison
   directly: the exact half-angle derivative and barriers give
   `K(v) <= (M/m) exp(D/m) K(u)` whenever `|v-u|<=D`.  Combined with
   `HairpinPulse.abs_curvatureDeriv_le_of_shift_harnack`, this closes the first
   intrinsic relative derivative estimate without endpoint regularity.  The
   coefficient differentiation and the exact next identity are now supplied
   by `HairpinPulse.hasDerivAt_curvatureAmp` and
   `curvature_second_eq_of_translator`; the latter expresses `K''` entirely in
   terms of `K,K',K o sigma,K' o sigma` and the bounded speed.
   `abs_curvatureSecond_le_of_shift_harnack` takes absolute values in that
   formula and combines the first relative estimate with the same Harnack
   constant to give an explicit `|K''| <= D2 K`, without endpoint regularity.
   The remaining analytic core is continuing this finite differentiation
   through the third and fourth pulse derivatives consumed by C3
   periodization, and transferring the bounds through the front-arclength
   inverse to the pulse.  The TeX fixes a sufficiently wide hairpin before
   choosing finite relative derivative constants; it does not require those
   constants to be uniform in the width.
   The coordinate transfer has now been started independently of that
   induction: `PulseFromCurvature.pulseDD` is the explicit second pulse
   derivative in front arclength, and `hasDerivAt_pulseD` proves it directly
   from the first two rear-curvature derivatives and the inverse-arclength
   equation, with no global profile regularity.
   The earlier wrapper had discarded a regularity theorem already proved by
   the canonical construction.  The strong translation theorem now retains
   its arctangent shift and derivative witnesses, and
   `exists_smoothOn_translatorData` packages those with
   `forall n, ContDiffOn n f (0,pi)` for the same `f` and
   `g = Translator.next f`.  Thus the remaining jet construction has the
   required interior differentiability and still needs no endpoint
   continuation.
   `HairpinPulseSmooth.contDiff_nat_of_autonomousOn` and
   `contDiff_nat_compOn` now perform the autonomous-flow bootstrap on an open
   invariant state domain, while
   `HairpinRelative.contDiffOn_curvField_nat` and
   `contDiffOn_pulseField_nat` provide the required finite-order fields from
   the profile's interior regularity.  These lemmas turn the retained
   `ContDiffOn` package into global finite smoothness along the actual angle
   and pulse trajectories without extending `f` through either endpoint.
   `ShiftedCurvatureJetMajorant` isolates the safe algebraic part of the
   order-three/four argument.  Its `RelMajorant` calculus is closed under
   addition, subtraction, bounded coefficients, products of relative terms,
   Harnack-controlled shifted composition, powers of the bounded curvature,
   and finite sums.  `rel_of_eq` then converts any corrected exact
   differentiated identity into a relative estimate.  This module assumes no
   derivative formula and therefore does not depend on the quarantined draft
   calculation in `HairpinPulse`.
   Its `PulseJet4` and `PulseJetRelative` packages isolate exactly the five
   pulse functions consumed by `PeriodizedPulseSmooth`.
   `pulseJet_exp_bounds` transfers the isolated pulse's exponential decay to
   all five orders from relative estimates, and
   `pulseJet_common_exp_bound` replaces their separate constants by the one
   common majorant required for termwise periodization.
   The exact finite identities are now represented without a fragile manual
   expansion: `secondRhs` is the established order-two expression,
   `thirdRhs` and `fourthRhs` are its successive derivatives, and
   `third_eq_canonical`/`fourth_eq_canonical` identify actual derivative
   witnesses with those expressions by uniqueness.  The remaining estimate
   step is to expand these canonical derivatives into the majorant algebra.
3. The final unconditional assembly `P(H_{n+1}) = H_n ⇝ shadowing ⇝ X₀`
   is now audited by `UnconditionalAssembly.UnconditionalAssemblyRemainder`.
   `UnconditionalAssembly.ConfiguredModelSequence` records the single
   coherence equality identifying each model curvature with the previous side
   of its paper `Config`.  Its derived theorems discharge separation
   positivity, curvature continuity and periodicity, the uniform upper bound,
   and total turning.  The smart constructor
   `UnconditionalAssemblyRemainder.ofConfiguredModel` therefore removes those
   six redundant capstone hypotheses in the legacy fixed-tube route.
   A critical quantifier audit shows that uniform strictly positive curvature
   pinching is **not** a paper obligation.  The TeX assumes a common upper
   ceiling `kappa0 < 1`, proves each finite model and pullback strictly convex,
   retains only nonnegative curvature under geometric `C2` convergence, and
   recovers strict positivity of the limit from the exact unit-tangent
   relation.  Along the expanding hairpin sequence the curvature minima may
   tend to zero, so no fixed positive `kmin` is asserted.
   `UnconditionalAssembly.PaperFaithfulAssemblyRemainder` records the correct
   quantifiers: configuration-derived regularity and turning, per-model
   strict positivity, a uniform upper ceiling below one, and the output of the
   shrinking variable-tube shadowing argument.  Its `conclude` theorem carries
   out the width closing step with no lower-curvature parameter.  The older
   `UnconditionalAssemblyRemainder` and `UnconditionalAssembly.conclude` are
   retained only as internally valid legacy fixed-tube statements and are no
   longer claimed as the paper's assembly route.
   Its `config_from_paper` field records provenance through
   `PaperHairpinData.toConfig`; the still-missing content is exposed chiefly
   by `marked_interpolation_defect`, the marked-tube selected-inverse
   hypotheses, summability, and the final transverse gap.  The theorem
   `PaperFaithfulAssemblyRemainder.conclude` derives the full noncircular
   infinite unit-tangent orbit from the paper-faithful shadowing output, but
   does not assert that this remaining shadowing record has yet been
   constructed.
   The output is no longer monolithic.  In
   `PaperFaithfulAssemblyRemainder.exists_markedLimit_of_summable_pullbackSteps`,
   completeness of the closed `kmin=0` marked tube turns summable distances
   between consecutive terminal pullbacks into an exact marked inverse orbit
   with the sharp tail bound.  This formulation accepts the marked distance
   produced by the variable-speed interpolation adapter and does not impose
   the obsolete `IsConstantSpeedNormalPath` predicate.
   `shadowingOrbit_of_markedLimit` derives the forward unit-tangent orbit,
   period, Hausdorff model estimate, and perimeter estimate from that marked
   limit.  Finally `shadowingOrbit_of_summable_pullbackSteps` composes both
   steps.  It isolates exactly three remaining theorem-level inputs from the
   regularizing shadowing proof: the propagated variable-speed step estimate
   for every pullback depth, invariance of all pullbacks in the shrinking
   nonnegative-curvature/chord-arc tube, and the selected-inverse differential
   regularity data for the marked inverse-orbit limits.
   `PaperFaithfulAssemblyRemainder.LimitStrictnessData` is that exact latter
   interface.  `isOval_ev_of_limitStrictnessData` now discharges the convexity
   upgrade itself: `UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg`
   turns nonnegative curvature of consecutive exact unit-tangent tracks into
   pointwise strict positivity, while the positive chord-arc constant yields
   injectivity on a period.  Thus `IsOval` and strict convexity are no longer
   assumptions of the shadowing constructor.  The remaining regularity input
   is only the differentiable intrinsic-curvature package; the analytic
   bootstrap is formalized by `RearRegularity.rear_contDiff`, while an adapter
   from the abstract marked selected-inverse limit to its steering ODE data is
   still needed.  The main geometric orbit conclusion and closing estimates
   are derived rather than assumed.
   `SelectedInverseLimitRegularity kh c dlt` now names this adapter precisely
   for `SelectedInverseMap.selInv kh`, and
   `ofSelectedInversePullbackSteps` is the paper-specific capstone constructor.
   This specialization also exposes a genuine closure issue: the current
   `SelectedInverseMap.isMarkedSelectedInverse_selInv`, `selInv_spec`, and
   `InterpolationVariableSpeedSelInvAdapter.exists_terminalCertificate`
   require a strictly positive input `kmin`.  They certify every finite
   pullback but do not yet prove that `selInv` retains the canonical
   closed-strip rear interpretation, continuity, and right-inverse identity at
   a `kmin=0` marked limit.  Those facts cannot follow from the abstract map
   definition, whose fallback branch is the identity.
   No marked-metric nonexpansiveness is assumed in the specialized constructor.
   The paper proves contraction of the normal/Jacobi path quantities, while
   the variable-speed endpoint estimate has its explicit `c2ConstVar` factor.
   Accordingly `hstep` is the propagated additive-cost estimate itself; it may
   include an expansion factor, provided its chosen majorant `d` is summable.
   Thus the remaining propagation task must use the paper's `W,S0,S1,S2`
   inequalities (or a geometric `K^k d_{n+k}` bound with `K theta < 1`), not an
   unsupported assertion that `selInv` is nonexpansive in the marked metric.
   The completion route is now formalized abstractly by
   `PaperFaithfulAssemblyRemainder.DenseExtensionData`.  Its `extension` takes
   the unique limit along a dense inducing subspace;
   `continuous_extension`, `extension_eq`, and `map_extension_eq` prove
   continuity, agreement on finite stages, and passage of continuous
   identities to the closure.  `PositiveTube c dlt` allows the positive lower
   bound to depend on the approximant, `NonnegativeTube c dlt` is its intended
   closed target, and `positiveToNonnegative` is the inclusion.
   `SelectedInverseCompletionData kh c dlt` specializes the construction to
   the finite-stage canonical `selInv`; `completedSelInv` is the resulting
   closure operator and `completedSelInv_rightInverse` transfers the forward
   right-inverse identity by continuity.
   Two concrete analytic inputs remain to instantiate this package: density
   of `PositiveTube` in `NonnegativeTube` while preserving the chord bound,
   and existence of the image limit along every approximating filter from the
   additive Jacobi/path Cauchy estimate.  The pullback engine also currently
   accepts a total `Data -> Data` map, whereas `completedSelInv` naturally has
   domain the invariant tube subtype.  The correct adapter is relative
   continuity along tube-valued sequences; extending by an arbitrary fallback
   outside the tube would not justify global continuity.
   That subtype adapter is now implemented.
   `SelectedInverseSelfCompletionData` adds the finite-stage tube-invariance
   lift to the dense completion package, and `closedSelInv` is consequently a
   continuous self-map of `NonnegativeTube`.  Its right-inverse identity is
   transferred from the dense positive stages by
   `closedSelInv_rightInverse`.  `closedPullback` defines all terminal
   pullbacks in the subtype; `exists_closedTube_shadowingLimit` obtains their
   Cauchy limits and exact inverse orbit; and `closedTube_forwardOrbit`
   transfers this to the forward map.  The geometric adapter
   `shadowingOrbit_of_closedTubeSteps` derives ovals, unit-tangent ranges,
   Hausdorff shadowing, and perimeter control.  Finally
   `ofCompletedSelectedInverseSteps` feeds this output directly into the
   paper-faithful capstone.  This route has neither a total-map fallback nor a
   global `Data -> Data` continuity hypothesis.
   On the quantitative side,
   `InterpolationRearCostBridge.JacobiCostCertificate.of_inverseJacobi`
   discharges the `S₀,S₁,S₂` bounds and their cost comparisons, while
   `RearDensityCertificate.of_rearCostConst` discharges all three nonlinear
   rear-density inequalities.  The remaining concrete interpolation input is
   isolated in `ConcreteInterpolationBounds`: the uniform `Kx` estimate and
   tangential-rate comparison produced from the actual C⁴ selected-rear
   family.
   `ConcreteInterpolationBoundsOn.exists_of_compact` now supplies the uniform
   constants on the actual compact interpolation interval from continuity and
   positivity, and `tangentialEnvelope` records the exact coefficient produced
   by `RearOwnTangentialCost.abs_gaugeRate_le_cost_density`.  What remains is
   to instantiate the continuous `Kx` function and the positive density from
   the concrete selected-steering family.
   More specifically,
   `ConcreteInterpolationBoundsOn.abs_selectedKx_le` applies the existing
   strip estimate directly to `(K-sin delta)/cos(delta)^3`, and
   `explicit_selectedSteering_bounds` chooses its constant envelope together
   with the tangential envelope.  Thus no compactness argument is needed for
   these two quantities; the remaining geometric task is proving the explicit
   interpolation and its selected steering stay in the asserted common strip
   and linking the envelope to the actual gauge rate.
   `kappaInterp_mem_common_strip` and
   `exists_selectedSteering_kappaInterp` now prove those strip statements for
   every interpolation slice `t ∈ [0,1]`, and
   `gaugeRate_le_tangentialEnvelope` identifies the output of
   `RearOwnTangentialCost.abs_gaugeRate_le_cost_density` with the bridge's
   envelope.  Joint C⁴ regularity continues to use the existing globally
   extended interpolation interface rather than falsely extrapolating the
   affine strip bound outside `[0,1]`.
   At zero lower curvature, `SelectedInverseMap.eq_selInv_of_isMarkedSelectedInverse`
   and `selInv_spec_of_markedRear` now remove the strict-positive hypothesis
   from the canonical-map identification step.  Consequently
   `closedTubeInvarianceResidual_selInv` reduces closed-tube invariance to the
   pointwise construction of a weak-convex marked rear with the same uniform
   speed and chord-arc constants; it does not assume injectivity for every
   steering solution.  The remaining geometric lemma is precisely the weak
   analogue of `ConvexEmbedded.injOn_Ico_of_turning_one`: nondecreasing tangent
   angle, positive speed, closure, and one total turn imply injectivity, after
   which `ChordArc.exists_chord_arc` supplies a positive (and ultimately
   uniform) chord constant.
   `LowCurvatureAssembly.steering_pos_of_nonnegative_nonzero` now supplies the
   missing flat-curvature argument for the actual selected rear: a periodic
   nonnegative steering solution driven by `K ≥ 0`, `K ≢ 0`, is everywhere
   positive.  Its integrating-factor proof shows `exp(s) δ(s)` is monotone;
   a hypothetical zero propagates backward and periodicity moves a nonzero
   forcing point into that zero region.  Thus the selected rear angle is
   strictly increasing and the existing strict `ConvexEmbedded` theorem, not
   a new assumed weak injectivity principle, applies.  The chord constant is
   then produced pointwise by `ChordArc.exists_chord_arc`; preservation of the
   already chosen initial `dlt` remains the quantitative one-step invariance
   estimate and is not inferred from an unjustified universal compactness
   bound.
   `ChordArc.chord_arc_stable` now formalizes the required near/far split for
   a prescribed target chord constant.  Its acceleration-bounded corollary
   `chord_arc_stable_of_acc_bound` converts the selected rear's normalized
   acceleration ceiling into the velocity modulus.  The explicit thresholds
   are `A*rho ≤ c/2`, `rho ≤ 1/2`, `dlt ≤ c/2`, and
   `2*eps ≤ (d0-dlt)*rho`; choosing `dlt=d0/2` leaves a transparent positive
   far-separation margin.  Instantiating `eps` by the variable-speed C1 path
   cost and `A` by the rear curvature/perimeter ceiling is now the only
   arithmetic wiring needed for fixed-chord one-step invariance.
   For the primary summable-normal-path route,
   `summable_weighted_shift_of_summable` converts the summable nonnegative
   L1-matching majorant into every shifted weighted series
   `Σ K^k d_(n+k)` when `0≤K≤1`.  The choice theorem
   `choose_summable_defect_normalPaths` simultaneously selects the explicit
   interpolation/selected-rear defect paths, retains their constant-speed
   geometry certificates, and proves summability of their actual costs from
   the majorant.  Thus exponential separation growth need only discharge
   `Summable d` (via the existing `ModelDefectSummable` estimates); remaining
   concrete work is the endpoint identification showing each explicit
   variable-speed selected-rear interpolation path has endpoints
   `Q n` and `selInv kh (Q (n+1))` with cost bounded by that `d n`.
   The base/transport roles are now type-audited.  The interpolation theorem
   `InterpolationPathDist.exists_normalPath_interp` produces the base defect
   path and its `interpPathCost` bound, whereas
   `GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`
   transports an arbitrary front path under the selected rear and produces a
   genuinely variable-speed certificate.  Consequently the old
   constant-speed `SummableNormalPathLimit.exists_limit_of_summable_costs`
   cannot be used for the transported chain.  The new
   `exists_limit_of_summable_variableSpeed_costs` is the correct completeness
   endpoint.  To feed it sequencewise, the path-dependent outputs
   `costP1`, `costG1`, and the mixed second-derivative constant must be
   majorized by fixed ceilings using the summable-cost/tube smallness bound;
   replacing them by a constant-speed certificate would be false.
   `exists_markedLimit_of_variableSpeed_pullbackPaths` is now the actual
   variable-speed pullback-limit analogue.  It accepts the recursively
   transported paths, one uniform `IsVariableSpeedNormalPath P0 P1 khat G1 Cg`
   ceiling, and costs bounded by the shifted majorant; it derives marked step
   bounds with the factor `c2ConstVar`, invokes distance completeness, and
   returns closed-tube membership, convergence, the exact inverse identity,
   and the sharp tail of `c2ConstVar*e`.  Thus uniform majorization of the
   `GaugeRearFamilyFromFront` outputs is cleanly separated from base-path
   construction by `exists_normalPath_interp` and its L1/interpPathCost bound.
   `exists_variableSpeed_pullbackPath` now performs the recursive path
   construction itself: depth zero is the interpolation defect `Λ_n`, and the
   successor is the uniformly majorized selected-rear transport of the path at
   `(n+1,k)`.  It proves the exact cost `K^k d_(n+k)`.  The composition theorem
   `exists_markedLimit_of_variableSpeed_transport` feeds these paths and their
   weighted summability directly into variable-speed pullback completeness.
   The remaining analytic instantiation is a single uniform transport lemma:
   bound the `GaugeRearFamilyFromFront` values `costP1`, `costG1`, and mixed
   `Cg` at the total remaining cost, using their monotonicity and the common
   rear-period/curvature ceilings.
   The scalar uniformization is now formalized by
   `GaugeFlowDerivCost.costP1_le`, `costG1_le`, and `mixedCost_le`.  For
   `0≤ell≤Qmax` and `0≤M≤Mtotal`, they bound all three path-dependent outputs
   by the explicit fixed choices
   `costP1 Qmax khat Mtotal`,
   `costG1 Qmax khat (rearKappa2 kh) Mtotal`, and the corresponding mixed sum.
   `IsVariableSpeedNormalPath.mono` supplies structural monotonicity when
   `P1`, `G1`, and `Cg` are enlarged, and
   `GaugeMarkedDataOfRearFamily.uniformize_variableSpeed_certificate` combines
   it with the scalar bounds.  Thus every path produced by
   GaugeRearFamilyFromFront is promoted to the one fixed `Qmax/Mtotal`
   certificate consumed by recursive pullback transport.  The remaining
   application is only the theorem's geometric hypothesis block and endpoint
   identification, not any further quantitative uniformization.
   `uniform_transport_of_raw_gauge` packages the final implication needed by
   recursive pullback transport: the raw GaugeRearFamilyFromFront path, cost
   factor, and path-dependent certificate are converted to the fixed uniform
   transport result without changing endpoints or cost.  The unassembled
   remainder is now exactly the raw-gauge invocation from the interpolation
   core/closing data and the Jacobi/rear-density certificates.
   Mixed-partial symmetry is already available as
   `MixedPartials.deriv_partial_comm`.  The new
   `source_bound_of_common_profile` and density variant implement stopped-time
   normalization without division: `|gS|≤D*w`, `mF=C*w`, and `D≤d*C` imply
   `|gS|≤d*mF`, including points where `w=0`.  The remaining explicit lemma is
   the factorized bound for the canonical spatial derivative of the
   transported front-normal source.
   `profiledSourceShape` and `hasDerivAt_profiled_source` now give the exact
   quotient/chain-rule formula and factor the common time profile before any
   estimate.  Specializing `N` and `NS` to interpolation `normalVel` and
   `normalVelDeriv` leaves only a uniform bound for the displayed shape, using
   the existing strip, normal-velocity, and normal-velocity-derivative bounds.
   `abs_profiledSourceShape_le` now proves that bound explicitly as
   `NSmax/v0^2 + Nmax*kh*Kx`.  Therefore the interpolation specialization uses
   the existing global `normalVel`/`normalVelDeriv` estimates, the selected
   strip cosine floor, and `abs_selectedKx_le`; no compactness or density
   division remains in the source estimate.  This specialization is now the
   theorem `abs_interpolation_profiledSourceShape_le`, and
   `interpolation_profiled_source_bound` applies
   `source_bound_of_common_profile` to give the density inequality directly
   for any nonnegative stopped profile.
   The remaining raw-gauge aggregation cannot be inferred from the named
   quantitative certificates alone: `JacobiCostCertificate` records bounds
   but not the inverse-Jacobi derivative equation, and `TerminalCertificate`
   records canonical endpoint geometry but not equality of the gauge-flow
   endpoint with that canonical marking.  Those two identification equations
   are therefore the exact interfaces still required before the uniform
   recursive transport theorem can be invoked without additional geometric
   hypotheses.
   In particular, `MarkingFlowDefectC2.dist_le_of_flow_marking_int` supplies a
   `pathDist` estimate, not a normal path attaining that estimate.  Because
   `pathDist` is an infimum, it yields only an `E+ε` comparison path; an
   arbitrary such near-minimizer has no exported variable-speed geometric
   certificate.  Consequently it is sound to append the marking defect at the
   distance-estimate stage by the triangle inequality, but not to claim a
   uniformly certified recursive transport path without first constructing
   an explicit reparameterization path and proving its derivative bounds.
   The hybrid route is now formalized by
   `canonical_increment_le_of_gauge_endpoint` and
   `exists_limit_of_summable_gauge_canonical_increments`: variable-speed paths
   control the distance to gauge-marked intermediate endpoints, the explicit
   `MarkingFlowDefectC2` estimate controls their canonical marking correction,
   and the triangle inequality gives summable direct increments of the
   canonical sequence.  Completeness therefore needs no normal path attaining
   the marking-defect distance.
   At the pullback-sequence level,
   `exists_markedLimit_of_summable_hybrid_pullbackSteps` accepts the
   gauge-transport and canonical-marking bounds as two separately summable
   sequences.  It forms the direct canonical increments by triangle, returns
   the tail of their pointwise sum, and reuses the pullback shift argument to
   obtain the exact inverse identity.  Thus canonical corrections never enter
   the recursively transported path certificate.
   The model-sequence specialization
   `exists_markedLimit_of_hybrid_pullbackSteps_of_L1_majorant` takes the common
   summable L¹ defect sequence and fixed uniform gauge/marking constants.  It
   discharges summability of both contributions by scalar multiplication and
   yields canonical shadowing limits with the explicit combined tail and exact
   inverse orbit relation.
   The scalar linearization is now split into reusable exact pieces:
   `flowDefectInt_linear_bounds` bounds both exponential flow defects by
   explicit multiples of `x` on `0≤x≤M`, and
   `markingC2Bound_le_mul_of_component_linear` absorbs the remaining quadratic
   velocity term using `x²≤Mx`.  Their resulting `Cmark` is nonnegative by
   construction and can be fed directly to the common-L¹-majorant theorem.
   `canonicalMarkingLinearConst` now records that explicit maximum, and
   `markingC2Bound_flow_le_linear` combines the two scalar lemmas into the
   precise terminal correction estimate used by the selected-rear gauge
   adapter.  Its nonnegativity is exported separately for summability and
   monotonicity arguments.
   A final endpoint-type obstruction remains before this can be instantiated
   recursively from the raw gauge theorem.  Raw transport maps a path `p→q`
   to a path `B p→g`, where `g` is the flow-marked rear, while the next
   recursive transport requires an actual path ending at the canonical
   `B q`.  `MarkingFlowDefectC2` supplies only `dist g (B q)≤E`, not such a
   path, so it cannot repair the endpoint type needed by recursion.  The
   hybrid completeness theorem is valid once gauge paths are supplied at every
   depth independently, but base interpolation paths plus raw transport alone
   do not construct that family.  Completing this step requires either an
   explicit normal path realizing the marking reparameterization (with a
   transportable variable-speed certificate) or a transport theorem formulated
   directly on metric increments rather than normal paths.
   Remedy (b) is now implemented.  `dist_map_le_of_gaugePath_and_marking`
   eliminates the raw gauge endpoint by triangle and gives the direct metric
   transport constant `c2ConstVar+Cmark`.  `pullbackSteps_of_metric_transport`
   propagates model defects with the exact weight `Ctransport^k`, and
   `exists_markedLimit_of_metric_transport` exposes the sole summability input
   for the regularizing weighted-tail construction while retaining the exact
   inverse identity.
   This multiplicative marked-metric route is an auxiliary conditional route,
   not yet the paper-faithful transported-parameter argument.  A gauge-flow
   rear has curve `rearOwn ... (Phi t u)` and generally nonconstant speed
   `∂ᵤPhi`; hence it is not the affine-own-arclength datum characterized by
   `SelectedInverseMap.IsMarkedSelectedInverse`.  Its unit-tangent transform
   recovers the front at the transported parameter, so `T(B p)=p` holds for
   ranges but not pointwise as marked data unless the front marking is
   transported simultaneously.  Consequently no path-independent operator
   `B : Data → Data` with both the raw gauge endpoint equality and exact marked
   right-inverse identity can be defined from the present objects.  The
   paper-faithful replacement must enlarge the state by a transported periodic
   parameter (or quotient marked data by orientation-preserving periodic
   reparameterization) and formulate the `W/S₀/S₁/S₂` triangular estimates
   on that enlarged/quotient state.
   The stronger proposed quotient statement, that all four path functionals
   are invariant under arbitrary orientation-preserving periodic
   reparameterization, is false.  `PathFunctionalsReparam` gives the correct
   laws: the L¹ term acquires an inverse lower-Jacobian factor, `S₁` an upper
   first-derivative factor, and `S₂` both first- and second-derivative
   factors.  Only the curve range (and geometric unit-tangent range) is
   invariant.  Therefore junctions modulo reparameterization can be used only
   together with explicit uniform bounds on the transition diffeomorphisms;
   quotienting alone cannot justify concatenation or summable C² costs.
   `MarkedSchemeTheoremRange` already supplies the correct final range-orbit
   conclusion, while `ArclengthReparamEstimates` and
   `GaugeReparamVariableSpeed` are the appropriate interfaces for a faithful
   transported-parameter chain.
   The remaining controlled-junction constructor is not currently present.
   `GaugeReparamAssembly.exists_normalPath_of_reparam_jacobi` constructs a new
   rear path from slice Jacobi data; it is not a theorem that precomposes an
   arbitrary existing `NormalPath` by a fixed periodic diffeomorphism.  The
   recursive chain needs precisely that latter operation, with endpoint
   equality to the preceding gauge marking and with the transformed density
   controlled by `reparamCW/reparamC0/reparamC1/reparamC2`.  Although the
   exported flow certificate provides the required positive first derivative
   and bounded first/second derivatives of `Phi`, those bounds cannot be fed to
   recursion until a generic `NormalPath.reparamSpace` constructor proves the
   time derivative, normality, stopping, and cost fields after composition.
   Moreover such a constructor cannot be generic over the current
   `NormalPath` structure: that structure bounds `iteratedDeriv j eta` but does
   not require `eta(t,·)` or its first derivative to be differentiable.
   `ArclengthReparamEstimates.estimates_reparam` correctly requires explicit
   `HasDerivAt eta eta1` and `HasDerivAt eta1 eta2` witnesses.  Without them the
   chain-rule identities for the reparameterized `S₁/S₂` densities are
   unavailable (and `deriv` defaults at nondifferentiability, so numerical
   bounds alone do not repair this).  A sound `reparamSpace` theorem must
   therefore take a strengthened C²-normal-path certificate carrying these
   two spatial derivative witnesses and their periodicity/continuity, or be
   restricted to the smooth interpolation/gauge paths where those witnesses
   have already been constructed.
   `C2NormalPathData` now implements that strengthened certificate, and
   `NormalPath.reparamSpace` implements fixed controlled spatial
   reparameterization with the explicit multiplier `reparamCostConst`.
   Instantiating it reveals one further export gap.  The existential result of
   `InterpolationPathDist.exists_normalPath_interp` does not state that the
   returned path's `eta` is the displayed `pathEta`; likewise
   `GaugeRearFamilyFromFront` identifies the returned `X` and `m` but does not
   identify `eta` with `frameNormal ... ∘ Phi`.  Hence the available
   `scaledEta` and inverse-Jacobi derivative theorems cannot be rewritten into
   `C2NormalPathData` for those opaque existential witnesses.  The two core
   constructors must be strengthened, preserving their old APIs, to export
   `eta` equality together with the first/second spatial derivative witnesses
   (and periodicity/boundedness).  After that, the controlled junction theorem
   applies directly.
   For the interpolation constructor this cannot be implemented as a wrapper
   around the present theorem: its public witness is only the terminal
   `psi(u)=Phi(1,u)`, whereas `Gamma.eta` uses the full flow
   `Phi(B(t),u)`.  The full `Phi` and its first/second spatial flow derivatives
   are local to the proof and are erased by the existential conclusion.  A
   faithful strengthened declaration must refactor the defining theorem to
   return `Phi`, the equality `Gamma.eta=pathEta ... Phi`, and the corresponding
   flow-derivative witnesses; the old `exists_normalPath_interp` should then be
   recovered as a projection of that stronger theorem.
   `RangeClosingAdapters` discharges the marking-independent part of the final
   TeX closing step: directional width, circle/noncircle status, and an exact
   unit-tangent range orbit transfer across transported representatives depend
   only on curve images.  Thus the eventual controlled-reparameterization
   chain may change markings at its junctions without changing the width gap
   or the final noncircular range conclusion.
   ENDPOINT-FREE ROUTE, COMPLETED THROUGH THE CONFIGURED MODEL SEQUENCE.
   The paper's `thm:hairpin` states "No endpoint values are assigned", so the
   profile is `C^∞` only on the open interval `(0,π)`; and the extension route
   is not merely unproved but false (`f(t) = 2 + sin(1/t)` is smooth and
   positive on `(0,π)` with no smooth extension).  The chain from the paper's
   own hypotheses to a configured model sequence with summable step defects is
   now free of every appeal to the closed interval:
   * `HairpinLowerComparisonInterior.hairpin_curv_ge_pulse_interior` proves the
     lower comparison `K_* ≥ b₀ y` with `b₀ = exp(−D₁A²M/2)` explicit.  The
     compactness extraction of `min f` and `max f` over `[0,π]` is replaced by
     the paper's own barrier bounds on `(0,π)`; the coordinates are given, not
     reconstructed; the abstract engine `HairpinMass.Kstar_lower_bound` is
     reused verbatim.
   * `CanonicalConsecutiveInterior` supplies the three certificates the
     configured-model capstone consumes on top of `ConsecutiveData`
     (`currentPulse_nonneg`, `current_x_deriv`,
     `exists_previous_lower_comparison`) from interior data.
   * `CanonicalConsecutivePaperWitness`, `CanonicalConsecutiveGeometricCertificates`
     and `CanonicalConfiguredModelCapstone` were localized in place — they had
     no other callers, so no duplicate global variants remain.
   * `PaperHairpinQuantitativeData.consecutiveData_of_interior` exposes the
     consecutive package as a definition whose projections reduce definitionally
     (the destructuring `obtain` that blocked reduction was replaced by
     projections), so the capstone can be applied to it directly.
   * `InteriorConfiguredModelSequence.exists_configuredModelSequence_of_interior`
     is the composition: from `f ∈ C^∞(0,π)`, the barriers `m ≤ f ≤ Am` there,
     the hairpin coordinates, the order-zero curvature tail, the relative bounds
     at `j ≤ 4` and the translator relations, it produces the configured model
     sequence together with the SUMMABLE defect series.
   CURRENT COMPILED BOUNDARY (this statement supersedes the historical
   development notes above).
   * `StrictConstructedModelGeometry.exists_strict_constructedModelGeometry_of_eps`
     constructs the epsilon-profile model sequence with strict levelwise
     geometry.  Strict model curvature is therefore no longer a residual.
   * `ConstructedConfiguredSequenceWeighted.exists_data_of_eps` retains
     positivity, the linear lower growth of `Hs`, and every sign needed by the
     closing estimates.  `WeightedMarkedDefectThreshold` proves summability at
     the exact condition `K * exp (-(beta * deltaStep)) < 1`; no assumption
     `K <= 1` remains.
   * `VariableSpeedApproximatePullback`, `ApproximatePullbackClosedTube`, and
     `ApproximatePaperAssemblyResidual` turn approximate transported paths and
     approximate base-defect paths into an exact marked inverse orbit and the
     final noncircular range orbit.  `DirectMarkedLimitOrbit` and
     `ApproximatePaperAssemblySelectedInverse` specialize this to
     `B = SelectedInverseMap.selInv kh` without an auxiliary total map `T` or
     hypotheses `hTB` and `hTev`.
   * `ConstructedPulseWidth` produces a uniform width constant for the retained
     periodized pulse.  `ConstructedWeightedClosingGap` proves an explicit
     weighted shadow-tail bound and an explicit starting-separation inequality
     implying the exact final transverse gap.

    These results do NOT yet constitute an unconditional proof of the main
    theorem.  The exact remaining interfaces are:
    * `ConfiguredApproximateDefectPath.Residual`, namely the explicit
     interpolation endpoint identification and its uniform `P0/P1/G1/Cg` and
     cost domination for every configured edge.  The canonical stopped-flow
     derivative bounds themselves are constructed by
     `ProfiledInterpolationBoundsConstructor`.
   * The approximate selected-inverse transport theorem `hmap`, continuity of
     `selInv kh`, and a `ClosedTubeInvarianceResidual`.
     `PhysicalRearLimitKinematicClosure` reduces construction of the former
     physical limit-component family to `PhysicalRearKinematicClosureResidual`:
     closure of the finite normalized steering, inverse-arclength, and exact
     front/rear identities under marked convergence, including noncollapse of
     the limiting steering.
   * The physical stage package is still an input, but it now supplies the
     forward range orbit directly: `range_front_eq_unitTangent_rear` combines
     the rear Frenet derivative, the exact rear-track formula, and surjectivity
     of the rear-arclength inverse.  No separate positive-pinching
     `RangeProvider` remains.
   * The final wiring identifying the width furnished by
     `ConstructedPulseWidth` with the initial configured model front, retaining
     that common `Cw` through the arbitrary-start sequence, and choosing the
     start above the explicit `ConstructedWeightedClosingGap` threshold.

   Until those interfaces are constructed, the repository verifies a sharp
   conditional capstone and its supporting analytic/geometric lemmas, not the
   paper's unconditional main theorem.
-/

namespace Manifest

/-- The formalization manifest is fully checked and all imported theorems are verified. -/
theorem manifest_verified : True := trivial

end Manifest
