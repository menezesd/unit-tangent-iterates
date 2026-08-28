import UnitTangentIterates.GaugeRearFamilyFromFront
import UnitTangentIterates.TriangularMarkedRecursiveChoice

/-!
# Gauge rear-family output as a triangular recursive stage

The gauge flow generally reaches the selected rear in a nonaffine marking.
Consequently its terminal datum must be the actual endpoint of the gauge path,
not `SelectedInverseMap.selInv` with its canonical affine marking.

This file adapts the continuation returned by
`GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front`
directly to `TriangularMarkedRecursiveChoice.StageOutput`.  The large analytic
constructor already supplies the normal path, its exact cost, and its
variable-speed certificate.  The only facts outside that output are isolated
in `TerminalResidual`: membership of the chosen marking in the compact class,
the range-level rear identity, and the finite Harnack estimate.
-/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearOwnArclength RearFamilyFrame
  NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace GaugeRearFamilyTriangularStageAdapter

open GaugeMarkedDataOfRearFamily

/-- Facts about the terminal gauge marking which are not conclusions of the
rear-family path constructor.  In particular, `rear_tube` must not be inferred
from the corresponding canonical selected inverse: a nonaffine marking does
not in general have constant speed. -/
structure TerminalResidual
    (front rear : Data) (c dlt : ℝ) : Prop where
  rear_tube : IsTubeMember c 0 dlt rear
  range_edge : range (ev front) =
    range (UnitTangent.unitTangentMap (ev rear))
  rear_harnack : ∀ a b : ℝ, a ≤ b →
    Real.exp (a - b) *
        (UnconditionalAssembly.arcCurv rear a /
          Real.sqrt (1 + UnconditionalAssembly.arcCurv rear a ^ 2)) ≤
      UnconditionalAssembly.arcCurv rear b /
        Real.sqrt (1 + UnconditionalAssembly.arcCurv rear b ^ 2)

/-- The weakened continuation interface obtained by partially applying the
raw gauge rear-family theorem to all of its differential hypotheses.  The
endpoint equations remain arguments, so the terminal datum is visibly the
one carrying the gauge marking. -/
def RearFamilyContinuation
    (F : ℝ → ℝ → ℂ) (Theta delta sf : ℝ → ℝ → ℝ)
    (Ydot : ℝ → ℝ → ℂ) (Phi : ℝ → ℝ → ℝ) (T M : ℝ)
    (m : ℝ → ℝ) (P0 ell kh khat : ℝ) : Prop :=
  ∀ a b : Data,
    (∀ u, rearOwn F Theta delta sf 0 (Phi 0 u) = a.1 u) →
    (∀ u, rearOwn F Theta delta sf T (Phi T u) = b.1 u) →
    (∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j
        (fun u => frameNormal Ydot (rearOwnAngle Theta delta sf) t (Phi t u))) ≤ m t) →
    ∃ Delta : NormalPath a b,
      cost Delta = M ∧
      IsVariableSpeedNormalPath P0 (costP1 ell khat M) khat
        (costG1 ell khat (rearKappa2 kh) M)
        (khat * costG1 ell khat (rearKappa2 kh) M +
          rearKappa2 kh * costP1 ell khat M ^ 2) Delta

/-- The strongest direct adapter from the raw rear-family continuation to one
triangular recursive stage.  `rear` is characterized by `hterminal`; no
canonical selected-inverse marking occurs in the statement or proof. -/
theorem stageOutput_of_rearFamilyContinuation
    {p front rear : Data}
    {F : ℝ → ℝ → ℂ} {Theta delta sf : ℝ → ℝ → ℝ}
    {Ydot : ℝ → ℝ → ℂ} {Phi : ℝ → ℝ → ℝ}
    {T M bound : ℝ} {m : ℝ → ℝ}
    {P0 ell kh khat c dlt : ℝ}
    (hcontinue : RearFamilyContinuation F Theta delta sf Ydot Phi T M m
      P0 ell kh khat)
    (hinitial : ∀ u, rearOwn F Theta delta sf 0 (Phi 0 u) = p.1 u)
    (hterminal : ∀ u, rearOwn F Theta delta sf T (Phi T u) = rear.1 u)
    (hsup : ∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j
        (fun u => frameNormal Ydot (rearOwnAngle Theta delta sf) t (Phi t u))) ≤ m t)
    (hcost : M ≤ bound)
    (R : TerminalResidual front rear c dlt) :
    Nonempty (TriangularMarkedRecursiveChoice.StageOutput p front rear bound
      P0 (costP1 ell khat M) khat
      (costG1 ell khat (rearKappa2 kh) M)
      (khat * costG1 ell khat (rearKappa2 kh) M +
        rearKappa2 kh * costP1 ell khat M ^ 2) c dlt) := by
  obtain ⟨Delta, hDeltaCost, hDeltaGeometry⟩ :=
    hcontinue p rear hinitial hterminal hsup
  refine ⟨{
    rear_tube := R.rear_tube
    increment := Delta
    increment_geometry := hDeltaGeometry
    increment_cost := ?_
    range_edge := R.range_edge
    rear_harnack := R.rear_harnack }⟩
  rw [hDeltaCost]
  exact hcost

/-- A packaged honest gauge endpoint.  This is convenient for recursive-choice
providers: the endpoint datum is stored together with the marking equation
which defines it, rather than being replaced by a canonical marking. -/
structure GaugeMarkedEndpoint
    (F : ℝ → ℝ → ℂ) (Theta delta sf : ℝ → ℝ → ℝ)
    (Phi : ℝ → ℝ → ℝ) (T : ℝ) where
  rear : Data
  terminal_marking : ∀ u,
    rearOwn F Theta delta sf T (Phi T u) = rear.1 u

/-- Packaged-endpoint form of `stageOutput_of_rearFamilyContinuation`. -/
theorem stageOutput_of_gaugeMarkedEndpoint
    {p front : Data}
    {F : ℝ → ℝ → ℂ} {Theta delta sf : ℝ → ℝ → ℝ}
    {Ydot : ℝ → ℝ → ℂ} {Phi : ℝ → ℝ → ℝ}
    {T M bound : ℝ} {m : ℝ → ℝ}
    {P0 ell kh khat c dlt : ℝ}
    (E : GaugeMarkedEndpoint F Theta delta sf Phi T)
    (hcontinue : RearFamilyContinuation F Theta delta sf Ydot Phi T M m
      P0 ell kh khat)
    (hinitial : ∀ u, rearOwn F Theta delta sf 0 (Phi 0 u) = p.1 u)
    (hsup : ∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j
        (fun u => frameNormal Ydot (rearOwnAngle Theta delta sf) t (Phi t u))) ≤ m t)
    (hcost : M ≤ bound)
    (R : TerminalResidual front E.rear c dlt) :
    Nonempty (TriangularMarkedRecursiveChoice.StageOutput p front E.rear bound
      P0 (costP1 ell khat M) khat
      (costG1 ell khat (rearKappa2 kh) M)
      (khat * costG1 ell khat (rearKappa2 kh) M +
        rearKappa2 kh * costP1 ell khat M ^ 2) c dlt) :=
  stageOutput_of_rearFamilyContinuation hcontinue hinitial
    E.terminal_marking hsup hcost R

end GaugeRearFamilyTriangularStageAdapter
