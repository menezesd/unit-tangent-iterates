import UnitTangentIterates.ConfiguredBaseProfiledExactAnalyticSuccessorFamily
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSourceStopping
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor

/-!
# Recursive sidecars for the configured profiled sources

The genuine-gauge source is first packaged before rewriting the actual
curvature constant to `sourceKh`.  This keeps all geometric projections
transparent.  The complete recursive package is transported across that one
scalar equality only at the boundary.
-/

noncomputable section

open Function Set MarkedSpace

namespace ConfiguredBaseProfiledRecursiveAnalyticSuccessorFamily

open ConfiguredBaseProfiledSourceFamily
  ConfiguredBaseProfiledExactAnalyticSuccessorFamily
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareExactSourceStopping
  FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor

variable {MA NA : ℝ}

/-- The configured genuine-gauge edge source before the dependent rewrite
from the actual curvature constant to `sourceKh`. -/
def rawSource (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA)
    (n : ℕ) :=
  ConfiguredBaseProfiledGenuineGaugeResidual.baseSource
    (edgeOutput O (n + 1))
    (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (data O) n)
    (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat (data O))
    (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (data O) n)
    (sourceCertificate O) (edgeSelected O n)
    (edgeReanchored O n).preTransport (edgeReanchored O n).gauge
    (edgeTransport O n) (edgeBounds O n)

/-- The spatial frame certificate used definitionally by the raw source. -/
def rawSpatialFrames
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    SpatialFrameRegularity (edgeOutput O (n + 1)).increment
      (rawSource O n).Ydot (rawSource O n).Theta (rawSource O n).delta
      (rawSource O n).sf (rawSource O n).P (rawSource O n).m
      (sourceCertificate O).k0
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (data O) n) := by
  let W := edgeOutput O (n + 1)
  let S := edgeSelected O n
  let P := (edgeReanchored O n).preTransport
  let G := (edgeReanchored O n).gauge
  let T := edgeTransport O n
  let R := ConfiguredBaseProfiledGenuineGaugeResidual.spatialFrames W S P G T
  exact
    { tangential := R.1
      normal := R.2
      tangential1_bound := (edgeBounds O n).tangential1_bound
      tangential2_bound := (edgeBounds O n).tangential2_bound
      tangential_period_bound := (edgeBounds O n).tangential_period_bound }

/-- Fresh compact selection bounds of the configured raw source. -/
noncomputable def rawSelectionBounds
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :=
  Classical.choice (by
    apply exists_selectionBounds (rawSource O n) (rawSpatialFrames O n)
    · simpa [rawSource, edgeSourceFamily, sourceCertificate_k0] using
        (edgeSliceFacts O n).normal_stopped
    · exact ConfiguredRecursiveEdgeSourceP0.edgeSourceP0_pos (data O) n
    · simpa [rawSource, edgeSourceFamily, sourceCertificate_k0] using
        (edgeSliceFacts O n).period_lower)

/-- The exact slice facts transported back to the transparent raw source. -/
noncomputable def rawSliceFacts
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    AnalyticSuccessorSliceFacts (rawSource O n) := by
  simpa [rawSource, edgeSourceFamily, sourceCertificate_k0] using
    edgeSliceFacts O n

noncomputable def rawRecursiveSidecars
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    RecursiveExactSidecars (rawSource O n) :=
  RecursiveExactSidecars.ofSource (rawSource O n) (rawSelectionBounds O n)

theorem range_shiftData (p : Data) (b : ℝ) :
    range (MarkedShift.shiftData b p).1 = range p.1 := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u + b, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u - b, by simp [MarkedShift.shiftData, MarkedShift.shiftMap]⟩

theorem range_of_normalizedMarking
    {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedTerminalMarkingComposition.NormalizedC2Marking
      base rear lambda Lambda) :
    range rear.1 = range base.1 := by
  have hc : Continuous M.marking.psi :=
    continuous_iff_continuousAt.2 fun u ↦ (M.psi_deriv u).continuousAt
  have hs : Surjective M.marking.psi :=
    surjective_of_continuous_quasiPeriodic (by norm_num) hc
      M.marking.translate
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨M.marking.psi u, (M.marking.position u).symm⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := hs v
    exact ⟨u, by rw [M.marking.position, hu]⟩

theorem raw_terminalCurvature_nonnegative
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (s : ℝ) :
    0 ≤ (rawSource O n).K (edgeOutput O (n + 1)).increment.T s := by
  let W := edgeOutput O (n + 1)
  change 0 ≤ (ConfiguredBaseProfiledSelectedRearGaugeReanchoring.K W
    (edgeSelected O n) (edgeReanchored O n).gauge.q) W.increment.T s
  unfold ConfiguredBaseProfiledSelectedRearGaugeReanchoring.K
    TimeDependentSpatialReanchoring.shift
  change 0 ≤ ConfiguredBaseProfiledSelectedRearReanchoring.K W W.increment.T _
  unfold ConfiguredBaseProfiledSelectedRearReanchoring.K
    ConfiguredBaseProfiledSelectedRearReanchoring.rawK
    ProfiledInterpolationFields.kappa CurvatureInterpolation.kappaInterp
  have hB := ProfiledInterpolationFields.B_mem_Icc W.increment.T
  apply add_nonneg
  · apply mul_nonneg (sub_nonneg.mpr hB.2)
    simpa only [ConfiguredApproximateDefectPathActualTerminal.sourceK0,
      ← (data O).model.curvature_eq (n + 1)] using
      (sourceCertificate O).front_nonnegative (n + 1) _
  · apply mul_nonneg hB.1
    simpa only [ConfiguredApproximateDefectPathActualTerminal.sourceK1] using
      (sourceCertificate O).rear_nonnegative (n + 1) _

theorem raw_terminalRange_carrier
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    range ((rawSource O n).F (edgeOutput O (n + 1)).increment.T) =
      range (O.pair.input.carrier (n + 1)).data.1 := by
  let W := edgeOutput O (n + 1)
  change range (ConfiguredBaseProfiledSelectedRearGaugeReanchoring.F W
    (edgeSelected O n) (edgeReanchored O n).gauge.q W.increment.T) = _
  unfold ConfiguredBaseProfiledSelectedRearGaugeReanchoring.F
  rw [TimeDependentSpatialReanchoring.range_shift]
  change range (ConfiguredBaseProfiledSelectedRearReanchoring.F W W.increment.T) = _
  unfold ConfiguredBaseProfiledSelectedRearReanchoring.F
  rw [TimeDependentSpatialReanchoring.range_shift, W.increment_time_one]
  have hp : perim (O.pair.input.carrier (n + 1)).data ≠ 0 := by
    rw [(O.pair.input.carrier (n + 1)).perim_eq]
    exact mul_ne_zero (by norm_num)
      (ne_of_gt ((data O).model.separation_pos (n + 1)))
  rw [← MarkedSpace.range_ev_of_perim_ne_zero hp]
  rw [(O.pair.input.carrier (n + 1)).curve_eq]
  apply congrArg range
  funext s
  simp [ConfiguredBaseProfiledSelectedRearReanchoring.rawF,
    ProfiledInterpolationFields.Y,
    ConfiguredApproximateDefectPathActualTerminal.sourceK1]

theorem raw_terminalRange
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    range ((rawSource O n).F (edgeOutput O (n + 1)).increment.T) =
      range (edgeOutput O (n + 1)).rear.1 := by
  let W := edgeOutput O (n + 1)
  calc
    range ((rawSource O n).F W.increment.T) =
        range (O.pair.input.carrier (n + 1)).data.1 :=
      raw_terminalRange_carrier O n
    _ = range W.terminalBase.1 := by
      rw [W.terminalBase_eq, range_shiftData]
    _ = range W.rear.1 := (range_of_normalizedMarking W.marking).symm

/-- The configured recursive package before rewriting the physical curvature
constant. -/
noncomputable def rawRecursiveAnalyticSuccessor
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    RecursiveAnalyticSuccessor (edgeOutput O (n + 1)).increment
      (sourceFamily O n)
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (data O) n)
      (sourceCertificate O).k0
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat (data O))
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (data O) n) :=
  RecursiveAnalyticSuccessor.ofExact (rawSource O n) (rawSliceFacts O n)
    (rawRecursiveSidecars O n) (rawSpatialFrames O n)
    (raw_terminalCurvature_nonnegative O n) (raw_terminalRange O n)

/-- The unconditional configured recursive successor.  All source-tied fields
are transported together through `sourceCertificate_k0`. -/
noncomputable def recursiveAnalyticSuccessor
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    RecursiveAnalyticSuccessor (edgeOutput O (n + 1)).increment
      (sourceFamily O n)
      (ConfiguredRecursiveEdgeSourceP0.edgeSourceP0 (data O) n)
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh
      (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat (data O))
      (ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap (data O) n) :=
  RecursiveAnalyticSuccessor.castKap (sourceCertificate_k0 O)
    (rawRecursiveAnalyticSuccessor O n)

/-- The transported source is exactly the existing configured edge source.
This projection lemma prevents downstream code from unfolding the dependent
curvature cast. -/
@[simp] theorem recursiveAnalyticSuccessor_source
    (O : ConfiguredRecursiveSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    (recursiveAnalyticSuccessor O n).source = edgeSourceFamily O n := by
  simp [recursiveAnalyticSuccessor, RecursiveAnalyticSuccessor.castKap,
    rawRecursiveAnalyticSuccessor, RecursiveAnalyticSuccessor.ofExact,
    rawSource, edgeSourceFamily, sourceCertificate_k0]

end ConfiguredBaseProfiledRecursiveAnalyticSuccessorFamily
