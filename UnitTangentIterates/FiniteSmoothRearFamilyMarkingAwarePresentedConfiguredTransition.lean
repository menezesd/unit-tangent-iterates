import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts

/-!
# Configured transitions for independently presented terminals

The existing configured transition package is indexed by the legacy terminal
input, whose terminal base is fixed by the incoming column.  A genuinely
selected inverse terminal has an independent presentation.  This file repeats
only the type-facing integration boundary for `PresentedTerminalInputCore` and
`PresentedOutputCore`; all pointwise estimates still come from the same
theorem-produced `SeparatedApplied` certificate.
-/

noncomputable section

open Set Function MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePresentedConfiguredTransition

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  JacobiControlledJunctionComponents
  PhysicalArclengthJacobiTransition

/-- Functional measurability for a genuinely presented chosen output. -/
structure PresentedFunctionalFacts
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ} {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {bound : ℝ} {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := a) (base := base)
      (bound := bound) E}
    (O : PresentedOutputCore E B) : Prop where
  front : FunctionalIntegrable Gamma.eta
  rear : FunctionalIntegrable O.chosen.Delta.eta

/-- Exact sources make the selected presented path functionally integrable;
the proof depends only on the chosen path and not on the terminal-input type. -/
def PresentedFunctionalFacts.ofExactSource
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := a) (base := base)
      (bound := bound) E}
    (O : PresentedOutputCore E B) (front : FunctionalIntegrable Gamma.eta) :
    PresentedFunctionalFacts O where
  front := front
  rear :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource
      O.chosen

/-- Aggregate the separated coefficients on the actual presented chosen path. -/
def rawOfSeparatedApplied
    {p q a base : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : PresentedTerminalInputCore (p := a) (base := base)
      (bound := bound) E}
    {O : PresentedOutputCore E B} (H : SeparatedApplied E)
    (F : PresentedFunctionalFacts O) :
    RawJacobiAnalyticInput Gamma.eta O.chosen.Delta.eta
      (separatedCW H) (separatedC0 H) (separatedC1 H) (separatedC2 H) := by
  let G := H.flowedChosen O.chosen
  apply RawJacobiAnalyticInput.of_density_bounds
    (le_max_left 0 H.CW) (le_max_left 0 H.C0) F.front F.rear
  · intro t _
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
    exact (G.w t).trans (mul_le_mul_of_nonneg_right
      (le_max_right 0 H.CW) hw)
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
    exact (G.s0 t).trans (mul_le_mul_of_nonneg_right
      (le_max_right 0 H.C0) hw)
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
    have hs : 0 ≤ supNorm (Gamma.eta t) := supNorm_nonneg _
    have h10 : H.C10 ≤ separatedC1 H :=
      (le_max_left H.C10 H.C11).trans (le_max_right 0 _)
    have h11 : H.C11 ≤ separatedC1 H :=
      (le_max_right H.C10 H.C11).trans (le_max_right 0 _)
    calc
      supNorm (iteratedDeriv 1 (O.chosen.Delta.eta t)) ≤
          H.C10 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            H.C11 * supNorm (Gamma.eta t) := G.s1 t
      _ ≤ separatedC1 H * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            separatedC1 H * supNorm (Gamma.eta t) :=
        add_le_add (mul_le_mul_of_nonneg_right h10 hw)
          (mul_le_mul_of_nonneg_right h11 hs)
      _ = separatedC1 H * (supNorm (Gamma.eta t) +
          ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by ring
  · intro t
    have hw : 0 ≤ ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
    have hs0 : 0 ≤ supNorm (Gamma.eta t) := supNorm_nonneg _
    have hs1 : 0 ≤ supNorm (iteratedDeriv 1 (Gamma.eta t)) := supNorm_nonneg _
    have h20 : H.C20 ≤ separatedC2 H :=
      (le_max_left H.C20 (max H.C21 H.C22)).trans (le_max_right 0 _)
    have h21 : H.C21 ≤ separatedC2 H :=
      ((le_max_left H.C21 H.C22).trans
        (le_max_right H.C20 (max H.C21 H.C22))).trans (le_max_right 0 _)
    have h22 : H.C22 ≤ separatedC2 H :=
      ((le_max_right H.C21 H.C22).trans
        (le_max_right H.C20 (max H.C21 H.C22))).trans (le_max_right 0 _)
    calc
      supNorm (iteratedDeriv 2 (O.chosen.Delta.eta t)) ≤
          H.C20 * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            H.C21 * supNorm (Gamma.eta t) +
            H.C22 * supNorm (iteratedDeriv 1 (Gamma.eta t)) := G.s2 t
      _ ≤ separatedC2 H * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) +
            separatedC2 H * supNorm (Gamma.eta t) +
            separatedC2 H * supNorm (iteratedDeriv 1 (Gamma.eta t)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right h20 hw)
          (mul_le_mul_of_nonneg_right h21 hs0))
          (mul_le_mul_of_nonneg_right h22 hs1)
      _ = separatedC2 H * supNorm (Gamma.eta t) +
          separatedC2 H * supNorm (iteratedDeriv 1 (Gamma.eta t)) +
          separatedC2 H * (∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by ring
  · intro t
    refine ⟨O.chosen.Delta.m t, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact O.chosen.Delta.abs_eta_le t x
  · intro t
    have hd1 : deriv (O.chosen.Delta.eta t) = O.chosen.c2.eta1 t :=
      funext fun u => (O.chosen.c2.eta_deriv t u).deriv
    simpa only [iteratedDeriv_one, hd1] using O.chosen.c2.eta1_bdd t
  · intro t
    have hd1 : deriv (O.chosen.Delta.eta t) = O.chosen.c2.eta1 t :=
      funext fun u => (O.chosen.c2.eta_deriv t u).deriv
    have hd2 : deriv (O.chosen.c2.eta1 t) = O.chosen.c2.eta2 t :=
      funext fun u => (O.chosen.c2.eta1_deriv t u).deriv
    simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_zero, hd1, hd2]
    exact O.chosen.c2.eta2_bdd t

/-- Exact configured transition data for an independently presented output. -/
structure PresentedConfiguredTransitionData
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n)}
    {base : Data}
    {B : PresentedTerminalInputCore (p := S.column.step.next n)
      (base := base) (bound := e n (k + 1)) E}
    (O : PresentedOutputCore E B) where
  CW : ℝ
  c0 : ℝ
  c1 : ℝ
  c2 : ℝ
  raw : RawJacobiAnalyticInput
    (S.column.step.richStage (n + 1)).stage.increment.eta
    O.chosen.Delta.eta CW c0 c1 c2
  domination : Domination
    (period (n + 1) k) (period n (k + 1)) (a n k)
    CW c0 c1 c2 K0 K1 K2
  MA_ge_one : 1 ≤ MA n k
  NA_nonnegative : 0 ≤ NA n k

/-- Construct the presented transition package from the actual separated
application and its scalar domination certificate. -/
def PresentedConfiguredTransitionData.ofSeparatedApplied
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n)}
    {base : Data}
    {B : PresentedTerminalInputCore (p := S.column.step.next n)
      (base := base) (bound := e n (k + 1)) E}
    {O : PresentedOutputCore E B}
    (H : SeparatedApplied E) (F : PresentedFunctionalFacts O)
    (HD : Domination
      (period (n + 1) k) (period n (k + 1)) (a n k)
      (separatedCW H) (separatedC0 H) (separatedC1 H) (separatedC2 H)
      K0 K1 K2)
    (hMA : 1 ≤ MA n k) (hNA : 0 ≤ NA n k) :
    PresentedConfiguredTransitionData (n := n) (a := a) (MA := MA)
      (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) O where
  CW := separatedCW H
  c0 := separatedC0 H
  c1 := separatedC1 H
  c2 := separatedC2 H
  raw := rawOfSeparatedApplied H F
  domination := HD
  MA_ge_one := hMA
  NA_nonnegative := hNA

/-- Integrate, rescale, and install the identity anchoring on the actual
presented selected path. -/
def PresentedConfiguredTransitionData.transition
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {E : Applied
      (S.column.step.richStage (n + 1)).stage.increment (S.source n)}
    {base : Data}
    {B : PresentedTerminalInputCore (p := S.column.step.next n)
      (base := base) (bound := e n (k + 1)) E}
    {O : PresentedOutputCore E B}
    (D : PresentedConfiguredTransitionData (n := n) (a := a) (MA := MA)
      (NA := NA) (K0 := K0) (K1 := K1) (K2 := K2) O)
    (hperiod : 1 ≤ period n (k + 1)) :
    Transition
      (components (period (n + 1) k)
        (S.column.step.richStage (n + 1)).stage.increment.eta)
      (components (period n (k + 1)) O.chosen.Delta.eta)
      (a n k) (MA n k) (NA n k) K0 K1 K2 := by
  let rawPhysical : RawBounds
      (period (n + 1) k) (period n (k + 1))
      (S.column.step.richStage (n + 1)).stage.increment.eta
      O.chosen.Delta.eta (a n k) K0 K1 K2 :=
    RawBounds.of_normalized D.raw.toScaledRawJacobiBounds D.domination
  let junction : FixedReparamBounds O.chosen.Delta.eta O.chosen.Delta.eta
      1 (MA n k) (NA n k) :=
    identityFixedReparamBounds O.chosen.Delta.eta D.MA_ge_one D.NA_nonnegative
  simpa using transition_of_raw_and_fixedReparam hperiod (by norm_num)
    (zero_le_one.trans D.MA_ge_one) D.NA_nonnegative rawPhysical junction

end FiniteSmoothRearFamilyMarkingAwarePresentedConfiguredTransition
