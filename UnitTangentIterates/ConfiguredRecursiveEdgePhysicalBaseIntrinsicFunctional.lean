import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawDiagonalBase
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink
import UnitTangentIterates.PeriodicSupNormFunctionalIntegrable
import UnitTangentIterates.InterpolationSecondOrder

/-! # Intrinsic-front functional regularity of the configured physical base

The lightweight source interface retains only slicewise regularity of its
front normal density.  The configured depth-zero source is stronger: before
the source is packaged, its density is an explicitly shifted profiled
interpolation field with joint spatial `C²` regularity.  This file records the
resulting functional-integrability certificate without adding a recursive
analytic callback.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalBaseIntrinsicFunctional

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink
  PeriodicSupNormFunctionalIntegrable

/-- Joint continuity of a unit-periodic spatial `C²` family suffices for all
four path-functional integrability channels.  Unlike the normal-path version,
this statement applies before the family has been installed as a path. -/
def functionalIntegrable_of_jointSpatialC2
    (eta eta1 eta2 : ℝ → ℝ → ℝ)
    (heta : Continuous (uncurry eta))
    (heta1 : Continuous (uncurry eta1))
    (heta2 : Continuous (uncurry eta2))
    (hderiv1 : ∀ t u, HasDerivAt (eta t) (eta1 t u) u)
    (hderiv2 : ∀ t u, HasDerivAt (eta1 t) (eta2 t u) u)
    (hperiodic : ∀ t, Periodic (eta t) 1) :
    FunctionalIntegrable eta := by
  have hperiodic' := PeriodicDerivativeAdapters.eta_derivatives_periodic
    hperiodic hderiv1 hderiv2
  have hd1 : ∀ t, iteratedDeriv 1 (eta t) = eta1 t := by
    intro t
    funext u
    rw [iteratedDeriv_one]
    exact (hderiv1 t u).deriv
  have hd2 : ∀ t, iteratedDeriv 2 (eta t) = eta2 t := by
    intro t
    funext u
    simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_zero]
    rw [show deriv (eta t) = eta1 t by
      funext x
      exact (hderiv1 t x).deriv]
    exact (hderiv2 t u).deriv
  refine
    { w := (continuous_L1_density_of_joint_continuous heta).intervalIntegrable 0 1
      s0 := (continuous_supNorm_of_joint_continuous_periodic one_pos heta
        hperiodic).intervalIntegrable 0 1
      s1 := ?_
      s2 := ?_ }
  · simpa only [hd1] using
      (continuous_supNorm_of_joint_continuous_periodic one_pos heta1
        hperiodic'.1).intervalIntegrable 0 1
  · simpa only [hd2] using
      (continuous_supNorm_of_joint_continuous_periodic one_pos heta2
        hperiodic'.2).intervalIntegrable 0 1

variable {MA NA : ℝ}

private abbrev D
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) :=
  ConfiguredBaseProfiledEdgeSourceFamily.data O

private def rawIntrinsic
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : ℝ → ℝ → ℝ :=
  fun t u ↦
    ProfiledInterpolationFields.en
      (sourceK0 (D O) (n + 1)) (sourceK1 (D O) (n + 1))
      (D O).model.thetaBase ((D O).Hs (n + 1)) t
      ((2 * (D O).Hs (n + 1)) * u)

private def rawIntrinsic1
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : ℝ → ℝ → ℝ :=
  fun t u ↦
    (2 * (D O).Hs (n + 1)) *
      ProfiledInterpolationFields.enS
        (sourceK0 (D O) (n + 1)) (sourceK1 (D O) (n + 1))
        (D O).model.thetaBase ((D O).Hs (n + 1)) t
        ((2 * (D O).Hs (n + 1)) * u)

private def rawIntrinsic2
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : ℝ → ℝ → ℝ :=
  fun t u ↦
    (2 * (D O).Hs (n + 1)) ^ 2 *
      ProfiledInterpolationFields.enSS
        (sourceK0 (D O) (n + 1)) (sourceK1 (D O) (n + 1))
        (sourceK0' (D O) (n + 1)) (sourceK1' (D O) (n + 1))
        (D O).model.thetaBase ((D O).Hs (n + 1)) t
        ((2 * (D O).Hs (n + 1)) * u)

private theorem rawIntrinsic_periodic
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) (t : ℝ) : Periodic (rawIntrinsic O n t) 1 := by
  let c := (D O).model.configs (n + 1)
  let L := (D O).Hs (n + 1)
  let k0 := sourceK0 (D O) (n + 1)
  let k1 := sourceK1 (D O) (n + 1)
  have hk0c : Continuous k0 := by simpa [c, L, k0] using c.continuous_KP
  have hk1c : Continuous k1 := by simpa [c, k1] using c.continuous_kH
  have hper0 : Periodic k0 L := by simpa [c, L, k0] using c.periodic_KP
  have hper1 : Periodic k1 L := by simpa [c, L, k1] using c.periodic_kH
  have htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi := by
    simpa [c, L, k0] using c.integral_KP_eq_pi
  have htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi := by
    simpa [c, L, k1] using c.integral_kH_eq_pi
  intro u
  have hn := InterpolationEstimate.normalVel_periodic
    (θ₀ := (D O).model.thetaBase) (L := L)
    hk0c hk1c hper0 hper1 htot0 htot1 (PathMetricCircle.B t)
  have hn2 := hn.add_period hn
  change PathMetricCircle.w t *
      InterpolationEstimate.normalVel k0 k1 (D O).model.thetaBase L
        (PathMetricCircle.B t) ((2 * L) * (u + 1)) =
    PathMetricCircle.w t *
      InterpolationEstimate.normalVel k0 k1 (D O).model.thetaBase L
        (PathMetricCircle.B t) ((2 * L) * u)
  rw [show (2 * L) * (u + 1) = (2 * L) * u + (L + L) by ring, hn2]

/-- Functional regularity of the normalized, unshifted profiled normal rate
used by the configured base edge. -/
private def rawIntrinsicFunctional
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) : FunctionalIntegrable (rawIntrinsic O n) := by
  let c := (D O).model.configs (n + 1)
  let L := (D O).Hs (n + 1)
  let k0 := sourceK0 (D O) (n + 1)
  let k1 := sourceK1 (D O) (n + 1)
  let k0' := sourceK0' (D O) (n + 1)
  let k1' := sourceK1' (D O) (n + 1)
  have hk0c : Continuous k0 := by simpa [c, L, k0] using c.continuous_KP
  have hk1c : Continuous k1 := by simpa [c, k1] using c.continuous_kH
  have hk0'c : Continuous k0' := by simpa [c, k0'] using c.continuous_KP'
  have hk1'c : Continuous k1' := by
    simpa [c, k1'] using c.continuous_kHderiv
  have hpair : Continuous (fun p : ℝ × ℝ ↦
      (p.1, (2 * L) * p.2)) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have h0 : Continuous (uncurry (rawIntrinsic O n)) := by
    simpa [rawIntrinsic, D, L, k0, k1, uncurry] using
      ((edgeOutput O (n + 1)).sourceCertificate.en_cont.comp hpair)
  have h1 : Continuous (uncurry (rawIntrinsic1 O n)) := by
    have hbase : Continuous (uncurry
        (ProfiledInterpolationFields.enS k0 k1 (D O).model.thetaBase L)) := by
      show Continuous (fun p : ℝ × ℝ ↦
        PathMetricCircle.w p.1 *
          InterpolationEstimate.normalVelDeriv k0 k1
            (D O).model.thetaBase L (PathMetricCircle.B p.1) p.2)
      exact (PathMetricCircle.continuous_w.comp continuous_fst).mul
        ((InterpolationEstimate.continuous_uncurry_normalVelDeriv
          (θ₀ := (D O).model.thetaBase) (L := L) hk0c hk1c).comp
            ((PathMetricCircle.continuous_B.comp continuous_fst).prodMk
              continuous_snd))
    simpa [rawIntrinsic1, D, L, k0, k1, uncurry] using
      continuous_const.mul (hbase.comp hpair)
  have h2 : Continuous (uncurry (rawIntrinsic2 O n)) := by
    have hbase : Continuous (uncurry
        (ProfiledInterpolationFields.enSS k0 k1 k0' k1'
          (D O).model.thetaBase L)) := by
      show Continuous (fun p : ℝ × ℝ ↦
        PathMetricCircle.w p.1 *
          InterpolationSecondOrder.normalVelSecondDeriv k0 k1 k0' k1'
            (D O).model.thetaBase L (PathMetricCircle.B p.1) p.2)
      exact (PathMetricCircle.continuous_w.comp continuous_fst).mul
        ((InterpolationSecondOrder.continuous_uncurry_normalVelSecondDeriv
          (θ₀ := (D O).model.thetaBase) (L := L)
          hk0c hk1c hk0'c hk1'c).comp
            ((PathMetricCircle.continuous_B.comp continuous_fst).prodMk
              continuous_snd))
    simpa [rawIntrinsic2, D, L, k0, k1, k0', k1', uncurry] using
      continuous_const.mul (hbase.comp hpair)
  have hd1 : ∀ t u, HasDerivAt (rawIntrinsic O n t)
      (rawIntrinsic1 O n t u) u := by
    intro t u
    have h :=
      ((edgeOutput O (n + 1)).sourceCertificate.en_space t ((2 * L) * u)).comp u
        ((hasDerivAt_id u).const_mul (2 * L))
    convert h using 1 <;> simp [rawIntrinsic, rawIntrinsic1, D, L, k0, k1] <;>
      ring
  have hd2 : ∀ t u, HasDerivAt (rawIntrinsic1 O n t)
      (rawIntrinsic2 O n t u) u := by
    intro t u
    have h := ((edgeOutput O (n + 1)).sourceCertificate.en_space2 t
      ((2 * L) * u)).comp u ((hasDerivAt_id u).const_mul (2 * L))
    convert h.const_mul (2 * L) using 1 <;>
      simp [rawIntrinsic1, rawIntrinsic2, D, L, k0, k1, k0', k1', pow_two] <;>
      ring
  exact functionalIntegrable_of_jointSpatialC2
    (rawIntrinsic O n) (rawIntrinsic1 O n) (rawIntrinsic2 O n)
    h0 h1 h2 hd1 hd2 (rawIntrinsic_periodic O n)

private def totalPhase
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) (t : ℝ) : ℝ :=
  (ConfiguredBaseProfiledSelectedRearReanchoring.frontPhase
      (edgeOutput O (n + 1)) t +
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma
      (edgeOutput O (n + 1)) (edgeSelected O n)
      (edgeReanchoredAt O n (ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.initialRearPhase O n)).gauge.q t) /
    (2 * (D O).Hs (n + 1))

/-- The exact configured physical base source has a normalized intrinsic front
obtained from `rawIntrinsic` by a slicewise rigid phase shift. -/
private theorem intrinsicFront_source_eq
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    intrinsicFront
      (ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source
        O C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) n) =
      fun t u ↦ rawIntrinsic O n t (u + totalPhase O n t) := by
  funext t u
  have hHs : (D O).Hs (n + 1) ≠ 0 := ne_of_gt
    ((D O).model.separation_pos (n + 1))
  simp [intrinsicFront, rawIntrinsic, totalPhase,
    ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source,
    ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.phaseRigid,
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.physicalRigidFields,
    edgeSourceAt, ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual,
    ConfiguredBaseProfiledInitialGaugeResidual.geom,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.etaF,
    ConfiguredBaseProfiledSelectedRearReanchoring.geometry,
    ConfiguredBaseProfiledSelectedRearReanchoring.etaF,
    ConfiguredBaseProfiledSelectedRearReanchoring.rawEtaF,
    TimeDependentSpatialReanchoring.shift,
    ConfiguredBaseInterpolationShiftedFront.period]
  congr 3
  field_simp [hHs]
  ring

/-- Callback-free intrinsic-front functional certificate for the configured
physical base source. -/
def sourceIntrinsicFrontFunctionalFacts
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) :
    IntrinsicFrontFunctionalFacts
      (ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.source
        O C (MA0 := MA0) (NA0 := NA0) (K0 := K0) (K1 := K1) (K2 := K2) n) := by
  refine ⟨?_⟩
  rw [intrinsicFront_source_eq]
  exact functionalIntegrable_shift (rawIntrinsicFunctional O n)
    (totalPhase O n) (rawIntrinsic_periodic O n)

/-- The same certificate at the exact depth-zero stage used by the truthful
recost diagonal. -/
def stageIntrinsicFrontFunctionalFacts
    (J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput MA NA)
    {K0 K1 K2 : ℝ} (n : ℕ) :
    IntrinsicFrontFunctionalFacts
      ((ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage
        (K0 := K0) (K1 := K1) (K2 := K2) J n).source) := by
  simpa [ConfiguredRecursiveEdgeRecostedRawDiagonalBase.stage,
    ConfiguredRecursiveEdgeRecostedRawDiagonalBase.unaryStage,
    ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.stage,
    ConfiguredRecursiveEdgePhysicalGeometricBase.base,
    ConfiguredRecursiveEdgePhysicalCompositionBase.baseCorrelated_source,
    ConfiguredRecursiveEdgePhysicalCompositionBase.baseSource] using
    sourceIntrinsicFrontFunctionalFacts J.scalar
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.rowC J.scalar)
      (MA0 := MA) (NA0 := NA) (K0 := K0) (K1 := K1) (K2 := K2) n

end ConfiguredRecursiveEdgePhysicalBaseIntrinsicFunctional
