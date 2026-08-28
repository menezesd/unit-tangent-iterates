import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings
import UnitTangentIterates.SelectedRearOneStepRegularity

/-!
# The paper's inverse Jacobi lemma as one theorem

The quantitative and regularity halves of `lem:jacobi` were previously
available through separate APIs.  This file packages them with the actual
selected-rear inputs used by the construction:

* a separated marking-aware applied source, which gives the intrinsic
  fully-physical selected-rear transition;
* a physical selected-rear stage, which retains the exact Frenet/arclength
  reconstruction needed for the regularity gain.

No affine-path, global inverse-map, or extra smoothness assumption is added.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric

namespace InverseJacobiPaperLemma

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi
  FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource

/-- **Inverse Jacobi estimates and regularity gain (`lem:jacobi`).**

For the actual selected-rear transition, the fully physical rear velocity is
non-expansive in `W` and satisfies the three triangular spatial gains with
constants depending only on the curvature ceiling `kh`.  For the same
selected-rear geometry, a `C^r` front (`2 ≤ r`) has a `C^(r+1)` rear.

The path component statement uses the intrinsic arclength representatives:
`Gamma.eta` on the front and `normalizedRearDensity A` on the selected rear.
This is the normalization in the TeX proof before any marking comparison is
applied. -/
theorem inverse_jacobi_estimates_and_regularity
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (hkh : 0 < kh)
    (S : SeparatedFacts A P1)
    (F : FunctionalIntegrable Gamma.eta)
    {rear front : Data}
    (stage : PhysicalRearLimitStageComponents rear front)
    (r : ℕ) (hr : 2 ≤ r)
    (hfront : ContDiff ℝ (r : ℕ) (ev front)) :
    let VF := physicalComponents A.P Gamma.eta
    let VR := physicalComponents (rearPeriod A) (normalizedRearDensity A)
    VR.w ≤ VF.w ∧
    VR.s0 ≤ ceilingC0 kh * VF.w ∧
    VR.s1 ≤ ceilingC1 kh * (VF.w + VF.s0) ∧
    VR.s2 ≤ ceilingC2 kh * (VF.w + VF.s0 + VF.s1) ∧
    ContDiff ℝ (r + 1 : ℕ) (ev rear) := by
  dsimp only
  have H := fullyPhysicalTransition (E := E) hkh S F
  have hreg : ContDiff ℝ (r + 1 : ℕ) (ev rear) := by
    let n := r - 2
    have hn : n + 2 = r := Nat.sub_add_cancel hr
    have hf : ContDiff ℝ (n + 2 : ℕ) (ev front) := by
      simpa [hn]
    have hs :=
      SelectedRearOneStepRegularity.contDiff_succ_ev_of_stage_of_front n stage hf
    have hnr : n + 3 = r + 1 := by omega
    rw [hnr] at hs
    exact hs
  refine ⟨?_, ?_, ?_, ?_, hreg⟩
  · simpa using H.w
  · simpa using H.s0
  · simpa using H.s1
  · simpa using H.s2

end InverseJacobiPaperLemma
