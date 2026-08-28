import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareAppliedSource

/-!
# Normalized quantitative frame bounds for a marking-aware application

An `Applied` witness can report loose global rate constants even though its
retained source-weighted estimates are sharp.  When the source density is at
most one, this adapter replaces only those two reported constants by the
canonical curvature coefficients.  All functions, flows, and chosen-path
producers remain unchanged.
-/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareAppliedSource

open FiniteSmoothRearFamilyMarkingAwareSource GaugeMarkedDataOfRearFamily

/-- Normalize the two quantitative constants of an application using its
sharp source-weighted rate bounds. -/
def Applied.normalizeFrame
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) (hm : ∀ t, A.m t ≤ 1) : Applied Gamma A := by
  let D : UniformFrameBounds.GaugeFrameData :=
    { E.frame.frame with
      rateLip := rearKappa1 kh
      rateBound2 := rearKappa2 kh
      hrate1 := fun t x ↦ by
        have h := mul_le_mul_of_nonneg_left (hm t)
          (rearKappa1_nonneg A.kh_nonnegative A.kh_lt_one)
        exact (E.frame.rate1_bound t x).trans (by simpa using h)
      hrate2 := fun t x ↦ by
        have h := mul_le_mul_of_nonneg_left (hm t)
          (rearKappa2_nonneg A.kh_nonnegative A.kh_lt_one)
        exact (E.frame.rate2_bound t x).trans (by simpa using h) }
  let R : GaugeRearFamilyFundamental.RetainedGaugeFrame E.Phi
      (rearPeriod A)
      (fun t ↦ (∫ u in (0 : ℝ)..A.P t,
        SelectedChangeOfVariable.cosTimeDeriv A.delta
          (RearOwnHigherRegularity.partialTime A.delta) t u) +
        A.P' t * Real.cos (A.delta t (A.P t)))
      A.m (RearFamilyFrame.frameTangential A.Ydot
        (RearOwnArclength.rearOwnAngle A.Theta A.delta A.sf))
      (rearKappa1 kh) (rearKappa2 kh) :=
    { E.frame with frame := D }
  exact { E with frame := R }

@[simp] theorem Applied.normalizeFrame_Phi
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) (hm : ∀ t, A.m t ≤ 1) :
    (E.normalizeFrame hm).Phi = E.Phi := by
  simp [Applied.normalizeFrame]

@[simp] theorem Applied.normalizeFrame_rateLip
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) (hm : ∀ t, A.m t ≤ 1) :
    (E.normalizeFrame hm).frame.frame.rateLip = rearKappa1 kh := by
  simp [Applied.normalizeFrame]

@[simp] theorem Applied.normalizeFrame_rateBound2
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (E : Applied Gamma A) (hm : ∀ t, A.m t ≤ 1) :
    (E.normalizeFrame hm).frame.frame.rateBound2 = rearKappa2 kh := by
  simp [Applied.normalizeFrame]

end FiniteSmoothRearFamilyMarkingAwareAppliedSource
