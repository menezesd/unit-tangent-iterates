import UnitTangentIterates.ConfiguredApproximateDefectPathActualTerminal
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareSource

/-!
# The actual marking source of the configured base interpolation

The gauge flow need not fix spatial zero.  We normalize it by its moving
phase and shift the intrinsic normal velocity by the same phase.  This gives
the exact nonaffine `MarkingCertificate` belonging to the returned configured
normal path.
-/

noncomputable section

open Function Set MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredBaseInterpolationMarkingSource

open ConfiguredApproximateDefectPathActualTerminal
  FiniteSmoothRearFamilyMarkingAwareSource
  ProfiledInterpolationFields

variable
    {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
    {n : ℕ} {A : RearCarrier D n} (W : Output D Q n A)

/-- Moving intrinsic phase of the profiled gauge marking. -/
def phase (t : ℝ) : ℝ := PhiB W.sourcePhi t 0

/-- Normalized nonaffine marking of the actual interpolation path. -/
def phi (t u : ℝ) : ℝ := PhiB W.sourcePhi t u - phase W t

def phi1 (t u : ℝ) : ℝ := W.sourcePhi1 (PathMetricCircle.B t) u

def phi2 (t u : ℝ) : ℝ := W.sourcePhi2 (PathMetricCircle.B t) u

/-- Intrinsic front normal velocity in the same moving phase. -/
def etaF (t s : ℝ) : ℝ :=
  en (sourceK0 D n) (sourceK1 D n) D.model.thetaBase (D.Hs n)
    t (s + phase W t)

/-- The exact marking certificate for the configured base increment.  In
particular, its intrinsic normal-rate bound is subsequently available from
`MarkingCertificate.etaF_bound`; it is not a new hypothesis. -/
def markingCertificate : MarkingCertificate W.increment (etaF W)
    (fun _ ↦ 2 * D.Hs n) := by
  refine
    { phi := phi W
      phi1 := phi1 W
      phi2 := phi2 W
      eta_link := ?_
      shift := ?_
      deriv := ?_
      deriv2 := ?_
      phi1_continuous := ?_
      phi2_continuous := ?_ }
  · intro t u
    rw [W.source_eta_eq]
    simp only [InterpolationPathDist.pathEta, InterpolationPathDist.scaledEta]
    change en (sourceK0 D n) (sourceK1 D n) D.model.thetaBase (D.Hs n)
        t (PhiB W.sourcePhi t u) = _
    congr 1
    simp [etaF, phi, phase]
  · intro t u
    have h := W.sourceCertificate.phi_translation t u
    dsimp [phi, phase]
    linarith
  · intro t u
    exact ((W.sourcePhi_space (PathMetricCircle.B t) u).sub_const
      (phase W t))
  · intro t u
    exact W.sourcePhi1_space (PathMetricCircle.B t) u
  · intro t
    exact W.sourcePhi1_joint.comp
      (continuous_const.prodMk continuous_id)
  · intro t
    exact W.sourcePhi2_joint.comp
      (continuous_const.prodMk continuous_id)

/-- The intrinsic source is bounded by the actual path density. -/
theorem etaF_bound : ∀ t s, |etaF W t s| ≤ W.increment.m t :=
  (markingCertificate W).etaF_bound (fun _ ↦ by
    have := D.model.separation_pos n
    positivity)

end ConfiguredBaseInterpolationMarkingSource
