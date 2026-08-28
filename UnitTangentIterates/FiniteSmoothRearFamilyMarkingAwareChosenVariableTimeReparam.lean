import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
import UnitTangentIterates.VariableArclengthScaledTimeReparamTransition
import UnitTangentIterates.UniformFrameBounds

/-!
# The actual chosen gauge as a variable-period component transition

The affine rear density is only a virtual component stage.  This file passes
from it to the density of the actual chosen path through the normalized,
time-dependent gauge marking.  The quantitative input is stated on the time
interval used by the component functionals; no fictitious affine normal path
is introduced.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric
  RearOwnArclength FlowDerivative

namespace FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam

open ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
  FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW
  FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  VariableArclengthScaledJacobiTransition
  VariableArclengthScaledTimeReparamTransition

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax P1 : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- The normalized spatial gauge marking on a rear slice. -/
def normalizedPsi (E : Applied Gamma A) (t u : ℝ) : ℝ :=
  E.Phi t u / rearPeriod A t

/-- First normalized spatial jet of the chosen gauge. -/
def normalizedPsi1
    (W : ChosenPath Gamma A E.Phi a b) (t u : ℝ) : ℝ :=
  W.phi1 t u / rearPeriod A t

/-- Second normalized spatial jet of the chosen gauge. -/
def normalizedPsi2
    (W : ChosenPath Gamma A E.Phi a b) (t u : ℝ) : ℝ :=
  W.phi2 t u / rearPeriod A t

/-- Uniform near-identity control on every time slice entering the path
functionals.  Unlike terminal jet bounds, this is exactly the sidecar needed
for a transition between whole-path components. -/
structure NormalizedJetBounds
    (W : ChosenPath Gamma A E.Phi a b) (eps : ℝ) : Prop where
  eps_nonnegative : 0 ≤ eps
  dpsi : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
    |normalizedPsi1 W t u - 1| ≤ eps
  ddpsi : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u,
    |normalizedPsi2 W t u| ≤ eps

private def timeReparamInputOfSeparated
    (W : ChosenPath Gamma A E.Phi a b)
    (S : SeparatedFacts A P1)
    (H : AnalyticInput A.P (rearPeriod A) Gamma.eta
      (normalizedRearDensity A)
      (preGaugeC0 P0 P1 kh) (preGaugeC1 P0 P1 kh Qmax)
      (preGaugeC2 P0 P1 kh Qmax))
    (Ftarget : FunctionalIntegrable W.Delta.eta)
    {eps : ℝ} (J : NormalizedJetBounds W eps) (heps : eps < 1) :
    TimeReparamInput (rearPeriod A) (normalizedRearDensity A) W.Delta.eta
      (1 - eps) (1 + eps) eps := by
  have hRcont : Continuous (rearPeriod A) :=
    Differentiable.continuous fun t ↦ (E.frame.period_deriv t).differentiableAt
  have hsourceC2 : ∀ t, ContDiff ℝ (2 : ℕ) (normalizedRearDensity A t) := by
    intro t
    have hlin : ContDiff ℝ (2 : ℕ)
        (fun u : ℝ ↦ rearPeriod A t * u) := contDiff_const.mul contDiff_id
    simpa only [normalizedRearDensity] using (S.rearNormal_c2 t).comp hlin
  have hsource1c : ∀ t, Continuous (deriv (normalizedRearDensity A t)) := by
    intro t
    exact (UniformFrameBounds.contDiff_deriv_of_two (hsourceC2 t)).continuous
  have hsource2c : ∀ t,
      Continuous (deriv (deriv (normalizedRearDensity A t))) := by
    intro t
    exact (UniformFrameBounds.contDiff_deriv_of_two
      (hsourceC2 t)).continuous_deriv (by norm_num)
  have hp0 : ∀ t, Periodic (normalizedRearDensity A t) 1 :=
    normalizedRearDensity_periodic (A := A)
  have hp1 : ∀ t, Periodic (deriv (normalizedRearDensity A t)) 1 := fun t ↦
    ArclengthInverse.periodic_of_hasDerivAt
      (fun u ↦ ((hsourceC2 t).differentiable (by norm_num) u).hasDerivAt)
      (hp0 t)
  have hp2 : ∀ t, Periodic
      (deriv (deriv (normalizedRearDensity A t))) 1 := fun t ↦
    ArclengthInverse.periodic_of_hasDerivAt
      (fun u ↦ by
        have hC1 := UniformFrameBounds.contDiff_deriv_of_two (hsourceC2 t)
        exact (hC1.differentiable (by norm_num) u).hasDerivAt)
      (hp1 t)
  have htargetPhysical : IntervalIntegrable
      (fun t ↦ rearPeriod A t *
        ∫ u in (0 : ℝ)..1, |W.Delta.eta t u|) volume 0 1 := by
    simpa [mul_comm] using
      Ftarget.w.mul_continuousOn hRcont.continuousOn
  refine
    { psi := normalizedPsi E
      psi1 := normalizedPsi1 W
      psi2 := normalizedPsi2 W
      target_eq := ?_
      source_differentiable := fun t u ↦
        (hsourceC2 t).differentiable (by norm_num) u
      source_deriv_differentiable := fun t u ↦ by
        have hC1 := UniformFrameBounds.contDiff_deriv_of_two (hsourceC2 t)
        exact hC1.differentiable (by norm_num) u
      psi_deriv := fun t u ↦ (W.phi1_deriv t u).div_const (rearPeriod A t)
      psi1_deriv := fun t u ↦ (W.phi2_deriv t u).div_const (rearPeriod A t)
      psi1_continuous := fun t ↦ (W.phi1_continuous t).div_const _
      psi_zero := ?_
      psi_one := ?_
      mA_pos := by linarith
      jacobian_lower := ?_
      jacobian_upper := ?_
      second_upper := J.ddpsi
      period_nonnegative := fun t _ ↦ (A.rear_period_pos t).le
      source_bdd0 := fun t ↦ ArclengthInverse.bddAbove_abs_of_periodic
        one_pos (hsourceC2 t).continuous (hp0 t)
      source_bdd1 := fun t ↦ ArclengthInverse.bddAbove_abs_of_periodic
        one_pos (hsource1c t) (hp1 t)
      source_bdd2 := fun t ↦ ArclengthInverse.bddAbove_abs_of_periodic
        one_pos (hsource2c t) (hp2 t)
      source_functional := normalizedRearFunctionalIntegrable (E := E)
      target_functional := Ftarget
      source_physicalW := H.rearPhysicalW_integrable
      target_physicalW := htargetPhysical }
  · intro t u
    rw [W.eta_eq]
    unfold normalizedRearDensity normalizedPsi
    congr 1
    exact (mul_div_cancel₀ (E.Phi t u) (A.rear_period_pos t).ne').symm
  · intro t
    rw [normalizedPsi, E.base t, zero_div]
  · intro t
    have hs := W.shift t 0
    have hPhi1 : E.Phi t 1 = rearPeriod A t := by
      simpa [E.base t] using hs
    rw [normalizedPsi, hPhi1]
    exact div_self (ne_of_gt (A.rear_period_pos t))
  · intro t ht u
    have h := (abs_le.mp (J.dpsi t ht u)).1
    unfold normalizedPsi1 at h ⊢
    linarith
  · intro t ht u
    have h := abs_le.mp (J.dpsi t ht u)
    have hpos : 0 < normalizedPsi1 W t u := by linarith
    rw [abs_of_pos hpos]
    linarith

/-- The chosen density is obtained from the virtual affine density by the
actual normalized gauge marking. -/
def timeReparamInput
    (W : ChosenPath Gamma A E.Phi a b)
    (S : SeparatedFacts A P1)
    (H : AnalyticInput A.P (rearPeriod A) Gamma.eta
      (normalizedRearDensity A)
      (preGaugeC0 P0 P1 kh) (preGaugeC1 P0 P1 kh Qmax)
      (preGaugeC2 P0 P1 kh Qmax))
    {eps : ℝ} (J : NormalizedJetBounds W eps) (heps : eps < 1) :
    TimeReparamInput (rearPeriod A) (normalizedRearDensity A) W.Delta.eta
      (1 - eps) (1 + eps) eps := by
  let Ftarget := FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource W
  exact timeReparamInputOfSeparated W S H Ftarget J heps

/-- The complete row-local stable transition: exact variable-period Jacobi
transport followed by the actual chosen gauge. -/
def transition
    (W : ChosenPath Gamma A E.Phi a b)
    (S : SeparatedFacts A P1) (F : FunctionalIntegrable Gamma.eta)
    {eps : ℝ} (J : NormalizedJetBounds W eps) (heps : eps < 1) :
    AnchoredJacobiStableTransition.Transition
      (physicalComponents A.P Gamma.eta)
      (physicalComponents (rearPeriod A) W.Delta.eta)
      (1 / (1 - eps)) (1 + eps) eps
      (preGaugeC0 P0 P1 kh) (preGaugeC1 P0 P1 kh Qmax)
      (preGaugeC2 P0 P1 kh Qmax) := by
  let H := analyticInput (E := E) S F
  exact transition_of_raw_and_timeReparam H.toRawBounds
    (timeReparamInput W S H J heps)

end FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
