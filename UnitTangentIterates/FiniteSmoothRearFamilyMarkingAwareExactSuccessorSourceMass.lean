import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminal

/-!
# Source-mass recurrence for the canonical exact successor

The automatic exact successor uses the actual chosen path density divided by
the inverse-cosine floor.  It does not recursively reuse the predecessor
source density.  The unavoidable factor is made explicit here.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorSourceMass

open FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorReadySource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareTimeRescaleCostObstruction

/-- The actual chosen increment stored in a presented output has precisely the
terminal input's cost bound. -/
theorem PresentedOutputCore.chosen_cost_le_bound
    {a b p base : Data} {Gamma : NormalPath a b}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := p) (base := base)
      (bound := bound) E}
    (O : PresentedOutputCore E B) :
    O.chosen.Delta.cost ≤ bound := by
  rw [← O.stage_eq]
  exact O.stage.increment_cost

/-- Exact mass formula for the source built by the automatic exact-successor
constructor. -/
theorem automatic_sourceMass_eq_cost_div_sqrt
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax kap P0Next khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A (kap := kap))
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (T : ShiftedTransport R G)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (C : Scalar (A := A) (kap := kap) (P0Next := P0Next)
      (khatNext := khatNext) (QmaxNext := QmaxNext))
    (hP0 : 0 < P0Next) :
    sourceMass (source W S R G hkap0 hkap1 T
      (bounds W S R G T hkap0 hkap1 C hP0)) =
      W.Delta.cost / Real.sqrt (1 - kap ^ 2) := by
  unfold sourceMass PathMetric.NormalPath.cost
  change (∫ t in (0 : ℝ)..W.Delta.T,
    W.Delta.m t / Real.sqrt (1 - kap ^ 2)) = _
  rw [intervalIntegral.integral_div]

/-- Any chosen-path cost bound transports to the canonical successor mass
with exactly one inverse-cosine loss. -/
theorem automatic_sourceMass_le_costBound_div_sqrt
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax kap P0Next khatNext QmaxNext d : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A (kap := kap))
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (T : ShiftedTransport R G)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (C : Scalar (A := A) (kap := kap) (P0Next := P0Next)
      (khatNext := khatNext) (QmaxNext := QmaxNext))
    (hP0 : 0 < P0Next) (hcost : W.Delta.cost ≤ d) :
    sourceMass (source W S R G hkap0 hkap1 T
      (bounds W S R G T hkap0 hkap1 C hP0)) ≤
      d / Real.sqrt (1 - kap ^ 2) := by
  rw [automatic_sourceMass_eq_cost_div_sqrt W S R G T hkap0 hkap1 C hP0]
  exact (div_le_div_iff_of_pos_right
    (Real.sqrt_pos.mpr (by nlinarith))).2 hcost

/-- At the configured curvature `5/6`, the inverse-cosine amplification is
strictly below two. -/
theorem automatic_sourceMass_le_two_mul_of_five_six
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P0Next khatNext QmaxNext d : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A (kap := (5 / 6 : ℝ)))
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (T : ShiftedTransport R G)
    (C : Scalar (A := A) (kap := (5 / 6 : ℝ)) (P0Next := P0Next)
      (khatNext := khatNext) (QmaxNext := QmaxNext))
    (hP0 : 0 < P0Next) (hcost : W.Delta.cost ≤ d) :
    sourceMass (source W S R G (by norm_num) (by norm_num) T
      (bounds W S R G T (by norm_num) (by norm_num) C hP0)) ≤ 2 * d := by
  rw [automatic_sourceMass_eq_cost_div_sqrt W S R G T
    (by norm_num) (by norm_num) C hP0]
  have hsquare :
      (Real.sqrt (1 - (5 / 6 : ℝ) ^ 2)) ^ 2 = 1 - (5 / 6 : ℝ) ^ 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt (1 - (5 / 6 : ℝ) ^ 2) := Real.sqrt_nonneg _
  have hsqrtHalf : (1 / 2 : ℝ) ≤ Real.sqrt (1 - (5 / 6 : ℝ) ^ 2) := by
    nlinarith
  have hsqrtPos : 0 < Real.sqrt (1 - (5 / 6 : ℝ) ^ 2) := by linarith
  have hd0 : 0 ≤ d := W.Delta.cost_nonneg.trans hcost
  rw [div_le_iff₀ hsqrtPos]
  nlinarith

/-- Stable components with cost `4 * D * defect` give the canonical next
source the summable majorant `8 * D * defect` at curvature `5/6`. -/
theorem automatic_sourceMass_le_eight_mul
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P0Next khatNext QmaxNext D d : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (S : ExactSelected A (kap := (5 / 6 : ℝ)))
    (R : PreTransport S)
    (G : RearOwnFrameGaugeFlowReanchoring.Gauge (xi R))
    (T : ShiftedTransport R G)
    (C : Scalar (A := A) (kap := (5 / 6 : ℝ)) (P0Next := P0Next)
      (khatNext := khatNext) (QmaxNext := QmaxNext))
    (hP0 : 0 < P0Next) (hcost : W.Delta.cost ≤ 4 * D * d) :
    sourceMass (source W S R G (by norm_num) (by norm_num) T
      (bounds W S R G T (by norm_num) (by norm_num) C hP0)) ≤
      8 * D * d := by
  have H := automatic_sourceMass_le_two_mul_of_five_six
    W S R G T C hP0 hcost
  nlinarith

/-- The source-mass majorant compatible with the configured defect diagonal. -/
def sourceMassMajor (D : ℝ) (defect : ℕ → ℝ) (j : ℕ) : ℝ :=
  8 * D * defect j

theorem sourceMassMajor_summable (D : ℝ) {defect : ℕ → ℝ}
    (hdefect : Summable defect) : Summable (sourceMassMajor D defect) := by
  apply (hdefect.mul_left (8 * D)).congr
  intro j
  simp [sourceMassMajor]

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorSourceMass
