import UnitTangentIterates.GaugeRearFamilyVariableTerminal
import UnitTangentIterates.GaugeNormalPathSeparatedData

/-! A correlated, component-separated rear-family continuation. -/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearOwnArclength RearFamilyFrame NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace GaugeRearFamilySeparatedContinuation

open GaugeRearFamilyTriangularStageAdapter GaugeRearFamilyVariableTerminal
  GaugeNormalPathSeparated GaugeMarkedDataOfRearFamily

structure Result
    {a b : Data} (frontPath : NormalPath a b)
    (p rear : Data) (M P0 ell kh khat : ℝ)
    (CW C0 C10 C11 C20 C21 C22 : ℝ) where
  increment : NormalPath p rear
  time_eq : increment.T = frontPath.T
  cost_eq : cost increment = M
  geometry : IsVariableSpeedNormalPath P0 (costP1 ell khat M) khat
    (costG1 ell khat (rearKappa2 kh) M)
    (khat * costG1 ell khat (rearKappa2 kh) M +
      rearKappa2 kh * costP1 ell khat M ^ 2) increment
  c2 : C2NormalPathData increment
  flowed : FlowedBounds frontPath.eta increment.eta
    CW C0 C10 C11 C20 C21 C22

/-- Package the *same* path returned by the long rear-family theorem with its
separated density certificate.  This avoids a second existential path choice. -/
def Result.ofLongOutput
    {a b p rear : Data} {frontPath : NormalPath a b}
    {M P0 ell kh khat CW C0 C10 C11 C20 C21 C22 : ℝ}
    (increment : NormalPath p rear)
    (htime : increment.T = frontPath.T)
    (hcost : cost increment = M)
    (hgeometry : IsVariableSpeedNormalPath P0 (costP1 ell khat M) khat
      (costG1 ell khat (rearKappa2 kh) M)
      (khat * costG1 ell khat (rearKappa2 kh) M +
        rearKappa2 kh * costP1 ell khat M ^ 2) increment)
    (hc2 : C2NormalPathData increment)
    (hflowed : FlowedBounds frontPath.eta increment.eta
      CW C0 C10 C11 C20 C21 C22) :
    Result frontPath p rear M P0 ell kh khat
      CW C0 C10 C11 C20 C21 C22 where
  increment := increment
  time_eq := htime
  cost_eq := hcost
  geometry := hgeometry
  c2 := hc2
  flowed := hflowed

def Continuation
    {a b : Data} (frontPath : NormalPath a b)
    (F : ℝ → ℝ → ℂ) (Theta delta sf : ℝ → ℝ → ℝ)
    (Ydot : ℝ → ℝ → ℂ) (Phi : ℝ → ℝ → ℝ)
    (M : ℝ) (m : ℝ → ℝ) (P0 ell kh khat : ℝ)
    (CW C0 C10 C11 C20 C21 C22 : ℝ) : Prop :=
  ∀ p rear : Data,
    (∀ u, rearOwn F Theta delta sf 0 (Phi 0 u) = p.1 u) →
    (∀ u, rearOwn F Theta delta sf frontPath.T (Phi frontPath.T u) = rear.1 u) →
    (∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j
        (fun u => frameNormal Ydot (rearOwnAngle Theta delta sf) t (Phi t u))) ≤ m t) →
    Nonempty (Result frontPath p rear M P0 ell kh khat
      CW C0 C10 C11 C20 C21 C22)

def Continuation.toRearFamilyContinuation
    {a b : Data} {frontPath : NormalPath a b}
    {F : ℝ → ℝ → ℂ} {Theta delta sf : ℝ → ℝ → ℝ}
    {Ydot : ℝ → ℝ → ℂ} {Phi : ℝ → ℝ → ℝ}
    {M : ℝ} {m : ℝ → ℝ} {P0 ell kh khat : ℝ}
    {CW C0 C10 C11 C20 C21 C22 : ℝ}
    (H : Continuation frontPath F Theta delta sf Ydot Phi M m P0 ell kh khat
      CW C0 C10 C11 C20 C21 C22) :
    RearFamilyContinuation F Theta delta sf Ydot Phi frontPath.T M m
      P0 ell kh khat := by
  intro p rear hinitial hterminal hsup
  obtain ⟨R⟩ := H p rear hinitial hterminal hsup
  exact ⟨R.increment, R.cost_eq, R.geometry⟩

structure RawStageOutput
    {a b : Data} (frontPath : NormalPath a b)
    (p front rear : Data) (bound M P0 ell kh khat : ℝ)
    (CW C0 C10 C11 C20 C21 C22 : ℝ) where
  stage : GaugeRearFamilyVariableTerminal.RawStageOutput p front rear bound
    P0 (costP1 ell khat M) khat
    (costG1 ell khat (rearKappa2 kh) M)
    (khat * costG1 ell khat (rearKappa2 kh) M +
      rearKappa2 kh * costP1 ell khat M ^ 2)
  c2 : C2NormalPathData stage.increment
  flowed : FlowedBounds frontPath.eta stage.increment.eta
    CW C0 C10 C11 C20 C21 C22

/-- Attach the terminal geometric certificate to a correlated separated long
output without re-running the continuation or choosing another path. -/
def RawStageOutput.ofResult
    {a b p front rear : Data} {frontPath : NormalPath a b}
    {M bound P0 ell kh khat CW C0 C10 C11 C20 C21 C22 : ℝ}
    (R : Result frontPath p rear M P0 ell kh khat
      CW C0 C10 C11 C20 C21 C22)
    (hcost : M ≤ bound) (T : RawTerminalResidual front rear) :
    RawStageOutput frontPath p front rear bound M P0 ell kh khat
      CW C0 C10 C11 C20 C21 C22 where
  stage :=
    { increment := R.increment
      increment_geometry := R.geometry
      increment_cost := R.cost_eq.le.trans hcost
      rear_curve_deriv := T.rear_curve_deriv
      rear_vel_deriv := T.rear_vel_deriv
      rear_periodic := T.rear_periodic
      rear_curvature_nonnegative := T.rear_curvature_nonnegative
      range_edge := T.range_edge
      rear_harnack := T.rear_harnack }
  c2 := R.c2
  flowed := R.flowed

theorem rawStageOutput_of_continuation
    {a b p front rear : Data} {frontPath : NormalPath a b}
    {F : ℝ → ℝ → ℂ} {Theta delta sf : ℝ → ℝ → ℝ}
    {Ydot : ℝ → ℝ → ℂ} {Phi : ℝ → ℝ → ℝ}
    {M bound P0 ell kh khat : ℝ} {m : ℝ → ℝ}
    {CW C0 C10 C11 C20 C21 C22 : ℝ}
    (H : Continuation frontPath F Theta delta sf Ydot Phi M m P0 ell kh khat
      CW C0 C10 C11 C20 C21 C22)
    (hinitial : ∀ u, rearOwn F Theta delta sf 0 (Phi 0 u) = p.1 u)
    (hterminal : ∀ u,
      rearOwn F Theta delta sf frontPath.T (Phi frontPath.T u) = rear.1 u)
    (hsup : ∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j
        (fun u => frameNormal Ydot (rearOwnAngle Theta delta sf) t (Phi t u))) ≤ m t)
    (hcost : M ≤ bound) (T : RawTerminalResidual front rear) :
    Nonempty (RawStageOutput frontPath p front rear bound M P0 ell kh khat
      CW C0 C10 C11 C20 C21 C22) := by
  obtain ⟨R⟩ := H p rear hinitial hterminal hsup
  let stage : GaugeRearFamilyVariableTerminal.RawStageOutput p front rear bound
      P0 (costP1 ell khat M) khat
      (costG1 ell khat (rearKappa2 kh) M)
      (khat * costG1 ell khat (rearKappa2 kh) M +
        rearKappa2 kh * costP1 ell khat M ^ 2) :=
    { increment := R.increment
      increment_geometry := R.geometry
      increment_cost := R.cost_eq.le.trans hcost
      rear_curve_deriv := T.rear_curve_deriv
      rear_vel_deriv := T.rear_vel_deriv
      rear_periodic := T.rear_periodic
      rear_curvature_nonnegative := T.rear_curvature_nonnegative
      range_edge := T.range_edge
      rear_harnack := T.rear_harnack }
  exact ⟨{ stage := stage, c2 := R.c2, flowed := R.flowed }⟩

end GaugeRearFamilySeparatedContinuation
