import UnitTangentIterates.ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter

/-! # Sharp curvature sidecar for the configured physical base source -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePhysicalBaseCurvature

open ConfiguredBaseProfiledEdgeSourceFamily
  ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily
  ConfiguredBaseProfiledResidualConstructor
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter
  FiniteSmoothRearFamilyMarkingAwareSource

variable {MA NA : ℝ}

/-- A second selected witness built at the actual paper ceiling `1/2`.  Its
steering is geometrically the same unique periodic selected inverse as the
coarsely typed recursive witness. -/
noncomputable def halfSelected
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ExactSelected (n := n + 1) O.actualCertificate :=
  Classical.choice (exists_exactSelected O.shiftedC3 O.actualCertificate (n + 1))

theorem edgeSelected_delta_eq_halfSelected
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) (t : ℝ) :
    (edgeSelected O n).delta t = (halfSelected O n).delta t := by
  let S := edgeSelected O n
  let R := halfSelected O n
  have hP : 0 < 2 * (data O).Hs (n + 1) := by
    nlinarith [(data O).model.separation_pos (n + 1)]
  apply Shadowing.steering_unique hP (S.steering t) (R.steering t)
    (S.periodic t) (R.periodic t)
  · intro s
    exact ⟨by nlinarith [S.strip_nonnegative t s, Real.pi_pos],
      (S.strip_le t s).trans (Real.arcsin_le_pi_div_two _)⟩
  · intro s
    exact ⟨by nlinarith [R.strip_nonnegative t s, Real.pi_pos],
      (R.strip_le t s).trans (Real.arcsin_le_pi_div_two _)⟩

/-- The coarse recursive selected witness retains the sharper actual-half
strip because periodic selected steering is unique. -/
theorem edgeSelected_delta_le_half
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) (t s : ℝ) :
    (edgeSelected O n).delta t s ≤ Real.arcsin (1 / 2 : ℝ) := by
  rw [edgeSelected_delta_eq_halfSelected O n t]
  simpa using (halfSelected O n).strip_le t s

/-- Initial-gauge and spatial reanchoring only translate the sharp steering
strip in its periodic spatial coordinate. -/
theorem edgeSourceAt_delta_le_half
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (n : ℕ) (q0 t s : ℝ) :
    (ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily.edgeSourceAt
      O n q0).delta t s ≤ Real.arcsin (1 / 2 : ℝ) := by
  let W := edgeOutput O (n + 1)
  let S := edgeSelected O n
  let q := (edgeReanchoredAt O n q0).gauge.q
  simpa [ConfiguredBaseProfiledEdgeInitialGaugeSourceFamily.edgeSourceAt,
    ConfiguredBaseProfiledInitialGaugeResidual.baseSource,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSourceOfActual,
    ConfiguredBaseInterpolationMarkingAwareSourceResidual.Residual.toSource,
    ConfiguredBaseProfiledInitialGaugeResidual.residual, sourceCertificate_k0,
    ConfiguredBaseProfiledSelectedRearGaugeReanchoring.delta,
    ConfiguredBaseProfiledResidualConstructor.ExactSelected.deltaR,
    ConfiguredBaseProfiledSelectedRearReanchoring.deltaShift,
    TimeDependentSpatialReanchoring.shift, W, S, q] using
      (edgeSelected_delta_le_half O n t
        (s + ConfiguredBaseProfiledSelectedRearGaugeReanchoring.sigma W S q t +
          ConfiguredBaseProfiledSelectedRearReanchoring.frontPhase W t))

/-- The two presentation transports preserve the actual-half strip. -/
theorem source_delta_le_half
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) (t s : ℝ) :
    (source O C (MA0 := MA0) (NA0 := NA0)
      (K0 := K0) (K1 := K1) (K2 := K2) n).delta t s ≤
        Real.arcsin (1 / 2 : ℝ) := by
  simpa [source,
    ConfiguredRecursiveEdgeSourceP0BaseSourceAdapter.sourceOfOutput,
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.physicalRigidFields,
    FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.phaseRigid] using
    (edgeSourceAt_delta_le_half O n (initialRearPhase O n) t s)

/-- The configured base selected-rear curvature fits the common recursive
ceiling `sourceKh`; the proof uses the sharper actual-half strip, not the
coarse source type parameter. -/
theorem base_source_curvature_le_sourceKh
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA)
    (C : ℕ → ℝ) {MA0 NA0 K0 K1 K2 : ℝ} (n : ℕ) (t s : ℝ) :
    |FiniteSmoothRearFamilyMarkingAwareSuccessorFront.curvature
      (source O C (MA0 := MA0) (NA0 := NA0)
        (K0 := K0) (K1 := K1) (K2 := K2) n) t s| ≤ sourceKh := by
  let A := source O C (MA0 := MA0) (NA0 := NA0)
    (K0 := K0) (K1 := K1) (K2 := K2) n
  change |Real.tan (A.delta t (A.sf t s))| ≤ sourceKh
  refine (GaugeMarkedDataOfRearFamily.abs_tan_le_rearKappa1
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
    (A.strip_nonnegative t (A.sf t s)) ?_).trans ?_
  · exact source_delta_le_half O C n t (A.sf t s)
  · rw [GaugeMarkedDataOfRearFamily.rearKappa1,
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_eq]
    norm_num

end ConfiguredRecursiveEdgePhysicalBaseCurvature
