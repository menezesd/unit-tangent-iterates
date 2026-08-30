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
import UnitTangentIterates.Theorem11Status

/-!
# Paper-to-Code Formalization Manifest

This file provides an audited, item-by-item correspondence between the mathematical
results of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates* (by Dean Menezes)
and their formalization in Lean 4.

---

### **Section 1: Introduction & Main Result**
* **Theorem 1.1 (Main Theorem: Noncircular Oval with Convex Iterates)**
  - **Current status: proved unconditionally.**  The canonical audit
    declaration is the zero-argument theorem
    `Theorem11Status.mainConclusion`.  Its construction is
    `PaperMainTheoremUnconditional.mainConclusion`, defined in
    `UnitTangentIterates/PaperMainTheoremUnconditional.lean`; it yields the full
    smooth, embedded, genuinely noncircular infinite unit-tangent orbit.
  - The former conditional assembly layers (the coherent-grid
    `Theorem11Status.RemainingInput` boundary, the floor-free conditional
    assemblies, and the legacy floor-positive variants) have been removed:
    they were superseded by the unconditional construction above.

---

### **Section 2: One Tangent Step — Rear and Front Tracks**
(Item numbers follow the current TeX: Lemma 2.1 is the low-curvature
inverse and Lemma 2.2 the convex-consecutive-tracks lemma.)
* **Oval definition & embeddedness (introduction / Section 2 conventions)**
  - `UnitTangentIterates.MainTheoremConditional.IsOval`
  - `UnitTangentIterates.TurningNumberDischarge.embedded_of_tube`
* **Lemma 2.2 (Convex consecutive tracks: speed & strict convexity)**
  - `UnitTangentIterates.UnitTangentSpeed.unitTangentMap_speed`
  - `UnitTangentIterates.UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg`
  - `UnitTangentIterates.UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg_of_turning`
    — the paper's own exclusion of `k ≡ 0`, from the turning number rather than
    as a hypothesis
  - `UnitTangentIterates.UnitTangentPreliminariesComplete.unit_tangent_preliminaries_complete`
* **Curvature action `K = u' + u` under the unit-tangent map (Section 2 preliminaries)**
  - `UnitTangentIterates.UnitTangent.curvature_unit_tangent`
  - `UnitTangentIterates.UnitTangentSpeed.transform_curvature_eq_deriv_u_add_u`
* **Total turning of pinched closed curves (embeddedness support)**
  - `UnitTangentIterates.TurningNumberDischarge.turning_two_pi_of_tube`
  - `UnitTangentIterates.TurningNumber.turning_eq_two_pi_of_pinched`

---

### **Section 3: A Translating Hairpin**
* **Auxiliary profile-ODE interface (not used by the TeX route)**
  - `UnitTangentIterates.HairpinODERegularity.ProfileODE`
  - `UnitTangentIterates.HairpinODERegularity.ProfileODE.abs_second_le`
* **Lemma 3.3 (Explicit barriers)**
  - `UnitTangentIterates.Barriers.fMinus`, `UnitTangentIterates.Barriers.fPlus`
  - `UnitTangentIterates.BarrierEstimates.m_gt_one`
* **Lemmas 3.1–3.2 & Theorem 3.4 (Translator equation, monotone iteration & profile existence)**
  - `UnitTangentIterates.TranslatingHairpin.exists_hairpin_profile`
  - `UnitTangentIterates.TranslatingHairpin.exists_translating_hairpin`
  - `UnitTangentIterates.TranslatingHairpinComplete.translating_hairpin_complete`
  - `UnitTangentIterates.HairpinSolitonComplete.hairpin_soliton_complete`
* **Uniform barrier positivity & smooth extension (Theorem 3.4 support; Lemma 3.5 pulse regularity)**
  - `UnitTangentIterates.ProfileBarrierBounds.profile_pos_of_lower_barrier`
  - `UnitTangentIterates.ProfileBarrierBounds.exists_pos_lower_bound`
  - `UnitTangentIterates.HairpinODERegularity.exists_smooth_positive_hairpin_extension`
  - `UnitTangentIterates.HairpinPulseSmooth.exists_smooth_hairpin_pulse`

---

### **Section 4: Exact Two-Cap Pairs**
* **Proposition 4.3 (Exact two-cap pairs): construction & embeddedness**
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
* **Proposition 4.3 (Exact two-cap pairs): perimeter defect value & derivative asymptotics**
  - `UnitTangentIterates.HairpinDefect.hairpin_defect`
  - `UnitTangentIterates.HairpinDefectComplete.hairpin_defect_complete`
  - `UnitTangentIterates.TwoCapAsymptoticsComplete.two_cap_perimeter_defect_asymptotics`
  - `UnitTangentIterates.TwoCapAsymptoticsComplete.two_cap_perimeter_derivative_asymptotics`
* **Lemma 7.1 (Large-separation threshold; stated in Section 7 of the TeX)**
  - `UnitTangentIterates.LargeSeparation.exists_large_separation_threshold`
  - `UnitTangentIterates.LargeSeparationComplete.large_separation_complete`
  - `UnitTangentIterates.EndToEndModelOrbit.exists_end_to_end_model_orbit`

---

### **Section 5: Curvature-Measure Matching**
* **Theorem 5.2 (Curvature-measure matching L¹ bound; with Lemma 5.1 common phase)**
  - `UnitTangentIterates.IsolatedPulseMatchingComplete.isolated_pulse_complete`
  - `UnitTangentIterates.OverlapIntegral.pairwise_overlap_integral_le`
  - `UnitTangentIterates.MatchingHairpinComplete.hairpin_matching_complete`
* **From L¹ curvature matching to C² metric distance (Theorem 6.8 support)**
  - `UnitTangentIterates.CurvatureStabilityL1.dist_le_of_L1_curvature_close`
  - `UnitTangentIterates.MatchingToMetricDefect.dist_le_of_exp_L1_matching`

---

### **Section 6: Regularizing Backward Shadowing — Marked Metric Space & Infinitesimal Inverse**
* **Marked metric space of curves (Section 6 conventions)**
  - `UnitTangentIterates.MarkedSpace.tube`
* **Lemma 6.2 (Curvature interpolation) & chord-arc control**
  - `UnitTangentIterates.CurvatureInterpolationComplete.curvature_interpolation_complete`
  - `UnitTangentIterates.ModelChordArc.model_chord_arc`
  - `UnitTangentIterates.ModelChordArcComplete.model_chord_arc_complete`
* **Lemma 6.4 (Inverse Jacobi estimates) & the periodic Green operator**
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
* **Tube invariance & smallness threshold η_* (proof of Theorem 6.8)**
  - `UnitTangentIterates.TubeConstants.tube_invariance_bounds`
  - `UnitTangentIterates.TubeConstants.etaStar_bounds`
  - `UnitTangentIterates.TubeInvarianceComplete.tube_invariance_complete`
* **Lemmas 2.1 & 6.7 (Low-curvature inverse; selected inverse on the closed strip) & periodic steering**
  - `UnitTangentIterates.SelectedSteeringComplete.selected_steering_complete`
  - `UnitTangentIterates.SelectedInverseStrip.selected_inverse_on_closed_strip`
  - `UnitTangentIterates.TwoCapRearEmbedded.selected_inverse_on_closed_strip_two_cap`
    — the same conclusion for the paper's model fronts with the turning
    hypothesis discharged
  - `UnitTangentIterates.SelectedInverseModelCoupling.exists_marked_model_selected_inverse`

---

### **Section 7: Proof of the Main Theorem**
* **Theorem 6.8 (Regularizing backward shadowing; stated in Section 6 of the TeX)**
  - `UnitTangentIterates.ShadowingScheme.exists_shadowing_orbit`
  - `UnitTangentIterates.MarkedSchemeTheoremCanonical.exists_canonical_marked_orbit`
  - `UnitTangentIterates.SelectedInverseContractive.exists_shadowing_orbit_on_invariant_tube`
  - `UnitTangentIterates.BackwardShadowingSchemeComplete.selected_rear_strip_geometry`
  - `UnitTangentIterates.BackwardShadowingSchemeComplete.tail_decay_of_summable_defects`
* **Closing step (excluding a circle) & Lemma 4.4 (Uniform transverse width)**
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
  A positive floor `0 < kmin <= kappas n s` together with total turning
  `int_0^{H_n} kappa_n = pi` forces `H_n <= pi / kmin`, contradicting the
  paper's `H_n >= H_0 + (Delta/2) n`.  The paper assumes only a common
  curvature *ceiling* `kappa_0 < 1`; the minima of the periodized hairpin decay
  like `e^{-beta H_n}`.  The current formalization therefore works throughout
  in the closed `kmin = 0` tube, with strict positivity recovered pointwise at
  each stage (`UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg`).
  The legacy floor-positive conditional assembly that motivated this finding
  has been removed.

* **The global barrier hypothesis is inconsistent with the extension route.**
  `Data.wide_pulse_and_derivative_bounds` asks for `forall t, fMinus eps t <= f t`,
  but the smooth positive extension produced by
  `ProfileExtension.exists_contDiff_pos_extension_pi` is identically `1` off a
  collar of `[0,pi]`, while the barrier lower bound is `eps^{-1} - eps > 1`.
  Every proof uses the hypothesis only at angles in `[0,pi]`;
  `WideHairpinLocalBounds` restates the whole chain that way.

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

### Current compiled status

The historical development log that previously occupied this section
described the conditional intermediate layers.  Those layers are
superseded by the unconditional construction and have been removed.

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
CURRENT COMPILED STATUS.
* `PaperMainTheoremUnconditional.mainConclusion`, defined in
  `UnitTangentIterates/PaperMainTheoremUnconditional.lean`, is the closed
  paper-facing theorem.  Its conclusion is
  `PaperMainTheoremGenuineNoncircularStatement.MainConclusion`, which includes
  a smooth embedded oval, parameter-independent geometric noncircularity,
  and a smooth infinite forward unit-tangent orbit.
* `Theorem11Status.mainConclusion` is the canonical zero-argument audit
  declaration and delegates to that unconditional construction.
* The prepared initial/next-step and recursive-chain modules now construct
  the actual-depth
  `ConfiguredRecursiveEdgeRecostFinitePreparedChosenChain.ChosenChain`.
  The chosen-chain completion and physical-cell/package modules supply the
  coherent physical closure consumed by
  `ConfiguredRecursiveEdgeRecostFinitePreparedChosenChainUnconditionalMain`.
* The scalar choices, summable recost error, shadowing tail, starting shift,
  transverse width gap, limiting strictness, smoothness projection,
  noncircularity upgrade, recursive chosen chain, and coherent physical grid
  are all discharged before the paper-facing theorem.
* The former conditional assembly layers and compatibility declarations
  (`Theorem11Status.RemainingInput`, the coherent-grid boundary, the
  floor-positive and floor-free conditional assemblies, and
  `PhysicalRearKinematicClosureReduction.lean`) have been removed: each was
  superseded by the unconditional construction.

Consequently the repository contains an unconditional proof of Theorem 1.1,
with `Theorem11Status.mainConclusion` as the canonical formalization boundary.
-/

namespace Manifest

/-- This only records that the manifest module elaborates.  The canonical
zero-argument statement of Theorem 1.1 is `Theorem11Status.mainConclusion`. -/
theorem manifest_verified : True := trivial

end Manifest
