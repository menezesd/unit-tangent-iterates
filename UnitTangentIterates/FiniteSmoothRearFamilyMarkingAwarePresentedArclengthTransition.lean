import UnitTangentIterates.ArclengthScaledJacobiTransition
import UnitTangentIterates.CompatibleSelectedRearJunction
import UnitTangentIterates.ConfiguredEnrichedGaugeStage
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedConfiguredTransition

/-! # Nonexpansive arclength transitions for presented rows

This is the row-local transition used by the finite backward construction.
It does not mention a recursive source, a fixed global domination constant,
or the coherent marked-grid endpoint.  The spatial junction internal to the
normal-rate estimate is the identity; the metric defect between the selected
endpoint and the presented rear remains a separate capstone estimate.
-/

noncomputable section

open Function Set MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePresentedArclengthTransition

open ArclengthScaledJacobiTransition
  AnchoredJacobiStableTransition
  ConfiguredEnrichedGaugeStage
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwarePresentedConfiguredTransition
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource

/-- Convert the exact flowed density bounds to the physical arclength
analytic input, using the already theorem-produced functional facts rather
than adding joint-continuity callbacks. -/
def analyticInputOfFlowed
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := a) (base := base)
      (bound := bound) E}
    {O : PresentedOutputCore E B}
    {PF PR CW c0 c1 c2 C0 C1 C2 : ℝ}
    (F : GaugeNormalPath.FlowedDensityBounds Gamma.eta O.chosen.Delta.eta
      CW c0 c1 c2)
    (HD : FixedDensityDomination PF PR CW c0 c1 c2 C0 C1 C2)
    (hPF : 0 ≤ PF)
    (HF : PresentedFunctionalFacts O) :
    AnalyticInput PF PR Gamma.eta O.chosen.Delta.eta C0 C1 C2 := by
  let D : DensityBounds PF PR Gamma.eta O.chosen.Delta.eta C0 C1 C2 :=
    physicalDensityBounds_of_flowed F HD
  refine
    { PF_nonnegative := hPF
      C0_nonnegative := HD.C0_nonnegative
      rearW_integrable := HF.rear.w
      frontW_integrable := HF.front.w
      W_slice := fun t _ ↦ D.w t
      rearS0_integrable := HF.rear.s0
      S0_slice := ?_
      rearS1_integrable := HF.rear.s1
      frontS0_integrable := HF.front.s0
      S1_slice := ?_
      rearS2_integrable := HF.rear.s2
      frontS1_integrable := HF.front.s1
      S2_slice := ?_ }
  · intro t x
    exact (le_supNorm
      ⟨O.chosen.Delta.m t, by
        rintro _ ⟨u, rfl⟩
        exact O.chosen.Delta.abs_eta_le t u⟩ x).trans (D.s0 t)
  · intro t x
    have hd1 : iteratedDeriv 1 (O.chosen.Delta.eta t) = O.chosen.c2.eta1 t := by
      funext u
      rw [iteratedDeriv_one]
      exact (O.chosen.c2.eta_deriv t u).deriv
    exact (le_supNorm (by simpa only [hd1] using O.chosen.c2.eta1_bdd t) x).trans
      (D.s1 t)
  · intro t x
    have hd1 : deriv (O.chosen.Delta.eta t) = O.chosen.c2.eta1 t := by
      funext u
      exact (O.chosen.c2.eta_deriv t u).deriv
    have hd2 : iteratedDeriv 2 (O.chosen.Delta.eta t) = O.chosen.c2.eta2 t := by
      funext u
      simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_zero, hd1]
      exact (O.chosen.c2.eta1_deriv t u).deriv
    exact (le_supNorm (by simpa only [hd2] using O.chosen.c2.eta2_bdd t) x).trans
      (D.s2 t)

/-- Aggregate the separated first- and second-derivative coefficients without
passing through the legacy fixed-K domination record. -/
def aggregatedFlowed
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := a) (base := base)
      (bound := bound) E}
    {O : PresentedOutputCore E B}
    (H : SeparatedApplied E) :
    GaugeNormalPath.FlowedDensityBounds Gamma.eta O.chosen.Delta.eta
      (FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedCW H)
      (FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedC0 H)
      (FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedC1 H)
      (FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedC2 H) := by
  let G := H.flowedChosen O.chosen
  refine
    { w := ?_
      s0 := ?_
      s1 := ?_
      s2 := ?_ }
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ ↦ abs_nonneg _)
    exact (G.w t).trans (mul_le_mul_of_nonneg_right
      (le_max_right 0 H.CW) hw)
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ ↦ abs_nonneg _)
    exact (G.s0 t).trans (mul_le_mul_of_nonneg_right
      (le_max_right 0 H.C0) hw)
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ ↦ abs_nonneg _)
    have hs : 0 ≤ supNorm (Gamma.eta t) := supNorm_nonneg _
    let C1 := FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedC1 H
    have h10 : H.C10 ≤ C1 :=
      (le_max_left H.C10 H.C11).trans (le_max_right 0 _)
    have h11 : H.C11 ≤ C1 :=
      (le_max_right H.C10 H.C11).trans (le_max_right 0 _)
    calc
      supNorm (iteratedDeriv 1 (O.chosen.Delta.eta t)) ≤
          H.C10 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            H.C11 * supNorm (Gamma.eta t) := G.s1 t
      _ ≤ C1 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            C1 * supNorm (Gamma.eta t) :=
        add_le_add (mul_le_mul_of_nonneg_right h10 hw)
          (mul_le_mul_of_nonneg_right h11 hs)
      _ = C1 * ((∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
          supNorm (Gamma.eta t)) := by ring
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ ↦ abs_nonneg _)
    have hs0 : 0 ≤ supNorm (Gamma.eta t) := supNorm_nonneg _
    have hs1 : 0 ≤ supNorm (iteratedDeriv 1 (Gamma.eta t)) := supNorm_nonneg _
    let C2 := FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedC2 H
    have h20 : H.C20 ≤ C2 :=
      (le_max_left H.C20 (max H.C21 H.C22)).trans (le_max_right 0 _)
    have h21 : H.C21 ≤ C2 :=
      ((le_max_left H.C21 H.C22).trans
        (le_max_right H.C20 (max H.C21 H.C22))).trans (le_max_right 0 _)
    have h22 : H.C22 ≤ C2 :=
      ((le_max_right H.C21 H.C22).trans
        (le_max_right H.C20 (max H.C21 H.C22))).trans (le_max_right 0 _)
    calc
      supNorm (iteratedDeriv 2 (O.chosen.Delta.eta t)) ≤
          H.C20 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            H.C21 * supNorm (Gamma.eta t) +
            H.C22 * supNorm (iteratedDeriv 1 (Gamma.eta t)) := G.s2 t
      _ ≤ C2 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            C2 * supNorm (Gamma.eta t) +
            C2 * supNorm (iteratedDeriv 1 (Gamma.eta t)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right h20 hw)
          (mul_le_mul_of_nonneg_right h21 hs0))
          (mul_le_mul_of_nonneg_right h22 hs1)
      _ = C2 * ((∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
          supNorm (Gamma.eta t) +
          supNorm (iteratedDeriv 1 (Gamma.eta t))) := by ring

/-- The exact nonexpansive physical transition attached to one presented
row.  The upper-triangular gains remain explicit, while the junction factors
are definitionally `1,1,0`. -/
structure PresentedArclengthTransitionData
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := a) (base := base)
      (bound := bound) E}
    (O : PresentedOutputCore E B) (PF PR C0 C1 C2 : ℝ) : Prop where
  transition : Transition
    (physicalComponents PF Gamma.eta)
    (physicalComponents PR O.chosen.Delta.eta)
    1 1 0 C0 C1 C2

/-- Construct the nonexpansive transition from the concrete separated
certificate and its physical arclength domination inequalities. -/
def PresentedArclengthTransitionData.ofSeparatedApplied
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := a) (base := base)
      (bound := bound) E}
    {O : PresentedOutputCore E B}
    {PF PR C0 C1 C2 : ℝ}
    (H : SeparatedApplied E)
    (HD : FixedDensityDomination PF PR
      (FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedCW H)
      (FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedC0 H)
      (FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedC1 H)
      (FiniteSmoothRearFamilyMarkingAwareConfiguredTransition.separatedC2 H)
      C0 C1 C2)
    (hPF : 0 ≤ PF)
    (HF : PresentedFunctionalFacts O) :
    PresentedArclengthTransitionData O PF PR C0 C1 C2 := by
  let F := aggregatedFlowed (O := O) H
  let hraw : AnalyticInput PF PR Gamma.eta O.chosen.Delta.eta C0 C1 C2 :=
    analyticInputOfFlowed F HD hPF HF
  let J : ReparamJunctionCertificate O.chosen.Delta :=
    reparamJunctionCertificate_of_compatible_affine_endpoints rfl rfl
  have htarget : FunctionalIntegrable
      (reparamAtJunction O.chosen.Delta O.chosen.c2 J).eta := by
    simpa [J, reparamAtJunction, NormalPath.reparamSpace] using HF.rear
  have heta : (reparamAtJunction O.chosen.Delta O.chosen.c2 J).eta =
      O.chosen.Delta.eta := by
    funext t u
    rfl
  refine ⟨?_⟩
  have T := transition_of_raw_and_junction O.chosen.Delta O.chosen.c2 J
    HD.PR_nonnegative hraw HF.rear htarget
  have hm : J.m = 1 := rfl
  have hM : J.M = 1 := rfl
  have hN : J.N = 0 := rfl
  rw [heta, hm, hM, hN] at T
  simpa using T

end FiniteSmoothRearFamilyMarkingAwarePresentedArclengthTransition
