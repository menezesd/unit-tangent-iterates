import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
import UnitTangentIterates.MarkingAwareSourcePhysicalRigidTransport

/-! # Normalized source jets from an explicit marking flow -/

noncomputable section

open Function Set MeasureTheory MarkedSpace PathMetric FlowDerivative

namespace FiniteSmoothRearFamilyMarkingAwareSourceNormalizedFlowJets

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableJetLinear
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
  GaugeMarkedDataOfRearFamily GaugeTerminalNearIdentityJets
  MarkingFlowDefectC2

variable {p q : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax P1 : ℝ}

/-- Constant phase and Euclidean rigid transport preserve a normalized source
jet bound. -/
def phaseRigid
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) {eps : ℝ}
    (J : SourceNormalizedJetBounds A eps)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    SourceNormalizedJetBounds (A.phaseRigid phase a w hw) eps where
  eps_nonnegative := J.eps_nonnegative
  dphi := by
    intro t ht u
    simpa using J.dphi t ht (u + phase)

/-- Changing only the physical Euclidean frame preserves normalized marking
jets definitionally. -/
def physicalRigidFields
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) {eps : ℝ}
    (J : SourceNormalizedJetBounds A eps)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    SourceNormalizedJetBounds (A.physicalRigidFields a w hw) eps where
  eps_nonnegative := J.eps_nonnegative
  dphi := by
    intro t ht u
    simpa [FiniteSmoothRearFamilyMarkingAwareSource.MarkingAwareSource.physicalRigidFields]
      using J.dphi t ht u

/-- An explicit all-time marking flow gives the normalized first source jet.
The rate hypothesis is stated against the source density itself, so phase and
rigid transports can be handled before invoking this theorem. -/
def sourceNormalizedJetBounds_of_flow
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (hunit : Gamma.T = 1) (hPone : ∀ t, 1 ≤ A.P t)
    (Phi hx : ℝ → ℝ → ℝ)
    (hphi1 : ∀ t u,
      A.phi1 t u = flowDeriv hx Phi (A.P 0) t u)
    (hperiod : ∀ t, Phi t 1 - Phi t 0 = A.P t)
    (hspace : ∀ t u, HasDerivAt (Phi t)
      (flowDeriv hx Phi (A.P 0) t u) u)
    (hrate : ∀ t x, |hx t x| ≤ rearKappa1 kh * A.m t)
    (Mcap : ℝ) (hmass : sourceMass A ≤ Mcap) :
    SourceNormalizedJetBounds A
      (jetLinearConst (A.P 0) 1 (rearKappa1 kh) (rearKappa2 kh) Mcap *
        sourceMass A) := by
  let ell := A.P 0
  let L : ℝ := 1
  let M := sourceMass A
  let k1 := rearKappa1 kh
  let k2 := rearKappa2 kh
  have hell : 0 < ell := A.period_pos 0
  have hL : 0 < L := by simp [L]
  have hM : 0 ≤ M := sourceMass_nonnegative A
  have hk1 : 0 ≤ k1 := rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one
  have hk2 : 0 ≤ k2 := rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one
  have hC : Continuous (fun t => k1 * A.m t) :=
    continuous_const.mul A.density_continuous
  have hprefix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, A.m s) ≤ M := by
    have htT : t ≤ Gamma.T := by simpa [hunit] using ht.2
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 htT
      (Filter.Eventually.of_forall fun s => A.density_nonnegative s)
      (A.density_continuous.intervalIntegrable 0 Gamma.T)
  have hprefix1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, k1 * A.m s) ≤ k1 * M := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hprefix t ht) hk1
  have hlinear :
      jetError ell L (k1 * M) (k2 * M) ≤
        jetLinearConst (A.P 0) 1 (rearKappa1 kh) (rearKappa2 kh) Mcap *
          sourceMass A := by
    simpa [ell, L, M, k1, k2] using
      (jetError_le_linear hell.le hL hk1 hk2 hM hmass)
  have hjet0 : 0 ≤ jetError ell L (k1 * M) (k2 * M) :=
    jetError_nonnegative hell.le hL (mul_nonneg hk1 hM) (mul_nonneg hk2 hM)
  refine
    { eps_nonnegative := hjet0.trans hlinear
      dphi := ?_ }
  intro t ht u
  have hraw := abs_flowDeriv_sub_period_le_int
    (hx := hx) (Phi := Phi) hell hrate hC ht.1 (hspace t) u
  rw [hperiod t, ← hphi1 t u] at hraw
  have hdefect : |A.phi1 t u - A.P t| ≤
      flowDefectC1Int ell (k1 * M) :=
    hraw.trans (flowDefectC1Int_mono hell.le (hprefix1 t ht))
  have hdefect0 : 0 ≤ flowDefectC1Int ell (k1 * M) :=
    flowDefectC1Int_nonneg hell.le (mul_nonneg hk1 hM)
  have hPt : 0 < A.P t := A.period_pos t
  have hdiv : A.phi1 t u / A.P t - 1 =
      (A.phi1 t u - A.P t) / A.P t := by
    field_simp
  calc
    |A.phi1 t u / A.P t - 1| =
        |A.phi1 t u - A.P t| / A.P t := by
      rw [hdiv, abs_div, abs_of_pos hPt]
    _ ≤ flowDefectC1Int ell (k1 * M) / A.P t :=
      div_le_div_of_nonneg_right hdefect hPt.le
    _ ≤ flowDefectC1Int ell (k1 * M) / L :=
      div_le_div_of_nonneg_left hdefect0 hL (by simpa [L] using hPone t)
    _ ≤ jetError ell L (k1 * M) (k2 * M) := le_max_left _ _
    _ ≤ jetLinearConst (A.P 0) 1 (rearKappa1 kh) (rearKappa2 kh) Mcap *
        sourceMass A := hlinear

end FiniteSmoothRearFamilyMarkingAwareSourceNormalizedFlowJets
