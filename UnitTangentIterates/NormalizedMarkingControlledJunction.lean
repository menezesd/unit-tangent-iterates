import UnitTangentIterates.C2NormalPathJunctionAdapter
import UnitTangentIterates.NormalizedTerminalMarkingComposition
import UnitTangentIterates.SelectedInverseApproximateMapPath

/-!
# Controlled junctions from normalized terminal markings

The recursive rear-family path is naturally produced with an affine initial
marking.  This module changes that marking to the actual endpoint selected by
the preceding stage.  The conservative bounds `1/2`, `2`, and `1` give one
fixed distortion constant, independent of the row and recursive depth.
-/

noncomputable section

open Function MarkedSpace PathMetric PathMetric.NormalPath

namespace NormalizedMarkingControlledJunction

open NormalizedTerminalMarkingComposition

namespace NormalizedC2Marking

theorem dpsi_add_one
    {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda) (u : ℝ) :
    M.marking.dpsi (u + 1) = M.marking.dpsi u := by
  have hleft : HasDerivAt (fun x => M.marking.psi (x + 1))
      (M.marking.dpsi (u + 1)) u := by
    simpa [Function.comp_def] using
      (M.psi_deriv (u + 1)).comp u ((hasDerivAt_id u).add_const 1)
  have heq : (fun x => M.marking.psi (x + 1)) =
      (fun x => M.marking.psi x + 1) :=
    funext M.marking.translate
  rw [heq] at hleft
  exact hleft.unique ((M.psi_deriv u).add_const 1)

theorem ddpsi_add_one
    {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda) (u : ℝ) :
    M.ddpsi (u + 1) = M.ddpsi u := by
  have hleft : HasDerivAt (fun x => M.marking.dpsi (x + 1))
      (M.ddpsi (u + 1)) u := by
    simpa [Function.comp_def] using
      (M.dpsi_deriv (u + 1)).comp u ((hasDerivAt_id u).add_const 1)
  have heq : (fun x => M.marking.dpsi (x + 1)) = M.marking.dpsi :=
    funext (dpsi_add_one M)
  rw [heq] at hleft
  exact hleft.unique (M.dpsi_deriv u)

theorem dpsi_periodic
    {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda) :
    Periodic M.marking.dpsi 1 :=
  dpsi_add_one M

theorem ddpsi_periodic
    {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda) :
    Periodic M.ddpsi 1 :=
  ddpsi_add_one M

end NormalizedC2Marking

/-- The fixed loss caused by anchoring an affine rear-family path to a
normalized marking whose two spatial jets obey the conservative bounds used
in the recursive construction. -/
def anchoringCost : ℝ := reparamCostConst (1 / 2) 2 1

theorem anchoringCost_eq : anchoringCost = 15 := by
  norm_num [anchoringCost, reparamCostConst]

theorem anchoringCost_nonneg : 0 ≤ anchoringCost := by
  rw [anchoringCost_eq]
  norm_num

/-- Total amplification after the raw selected-rear transport and the fixed
change from its affine marking to the preceding actual terminal marking. -/
def anchoredMapK (kh : ℝ) : ℝ :=
  anchoringCost * SelectedInverseApproximateMapPath.mapK kh

/-- A normalized stage marking with the uniform bounds needed to anchor the
next gauge rear-family path. -/
structure UniformAnchoringBounds
    {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda) : Prop where
  lower : ∀ u, (1 / 2 : ℝ) ≤ M.marking.dpsi u
  upper : ∀ u, M.marking.dpsi u ≤ 2
  second : ∀ u, |M.ddpsi u| ≤ 1

/-- Tunable anchoring bounds.  In the final scalar threshold these constants
approach `(1,1,0)`, so their reparameterization cost approaches one. -/
structure ControlledAnchoringBounds
    {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (mA MA NA : ℝ) : Prop where
  m_pos : 0 < mA
  M_nonneg : 0 ≤ MA
  N_nonneg : 0 ≤ NA
  lower : ∀ u, mA ≤ M.marking.dpsi u
  upper : ∀ u, |M.marking.dpsi u| ≤ MA
  second : ∀ u, |M.ddpsi u| ≤ NA

def UniformAnchoringBounds.toControlled
    {base rear : Data} {lambda Lambda : ℝ}
    {M : NormalizedC2Marking base rear lambda Lambda}
    (B : UniformAnchoringBounds M) :
    ControlledAnchoringBounds M (1 / 2) 2 1 where
  m_pos := by norm_num
  M_nonneg := by norm_num
  N_nonneg := by norm_num
  lower := B.lower
  upper := fun u => by
    rw [abs_of_nonneg (le_trans (by norm_num) (B.lower u))]
    exact B.upper u
  second := B.second

/-- Tunable version of `junction`. -/
def controlledJunction
    {p q p' q' base rear : Data} {lambda Lambda mA MA NA : ℝ}
    (Gamma : NormalPath p q)
    (M : NormalizedC2Marking base rear lambda Lambda)
    (B : ControlledAnchoringBounds M mA MA NA)
    (hstart : ∀ u, Gamma.X 0 (M.marking.psi u) = p'.1 u)
    (hfinish : ∀ u, Gamma.X Gamma.T (M.marking.psi u) = q'.1 u) :
    ReparamJunctionCertificate (p' := p') (q' := q') Gamma where
  phi := M.marking.psi
  phi1 := M.marking.dpsi
  phi2 := M.ddpsi
  m := mA
  M := MA
  N := NA
  m_pos := B.m_pos
  phi_deriv := M.psi_deriv
  phi1_deriv := M.dpsi_deriv
  phi1_cont := continuous_iff_continuousAt.2 fun u =>
    (M.dpsi_deriv u).continuousAt
  phi2_cont := M.ddpsi_cont
  jacobian_lower := B.lower
  jacobian_upper := B.upper
  second_upper := B.second
  phi_zero := M.psi_zero
  phi_one := by simpa [M.psi_zero] using M.marking.translate 0
  phi_add_one := M.marking.translate
  phi1_periodic :=
    NormalizedMarkingControlledJunction.NormalizedC2Marking.dpsi_periodic M
  phi2_periodic :=
    NormalizedMarkingControlledJunction.NormalizedC2Marking.ddpsi_periodic M
  start := hstart
  finish := hfinish

theorem controlledJunction_cost
    {p q p' q' base rear : Data} {lambda Lambda mA MA NA : ℝ}
    (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    (M : NormalizedC2Marking base rear lambda Lambda)
    (B : ControlledAnchoringBounds M mA MA NA)
    (hstart : ∀ u, Gamma.X 0 (M.marking.psi u) = p'.1 u)
    (hfinish : ∀ u, Gamma.X Gamma.T (M.marking.psi u) = q'.1 u) :
    cost (reparamAtJunction Gamma hC2
      (controlledJunction Gamma M B hstart hfinish)) =
      reparamCostConst mA MA NA * cost Gamma := by
  rw [cost_reparamAtJunction]
  rfl

/-- Build the exact fixed spatial junction from a preceding normalized
terminal marking.  Endpoint identities are the only data specific to the
affine gauge path. -/
def junction
    {p q p' q' base rear : Data} {lambda Lambda : ℝ}
    (Gamma : NormalPath p q)
    (M : NormalizedC2Marking base rear lambda Lambda)
    (B : UniformAnchoringBounds M)
    (hstart : ∀ u, Gamma.X 0 (M.marking.psi u) = p'.1 u)
    (hfinish : ∀ u, Gamma.X Gamma.T (M.marking.psi u) = q'.1 u) :
    ReparamJunctionCertificate (p' := p') (q' := q') Gamma where
  phi := M.marking.psi
  phi1 := M.marking.dpsi
  phi2 := M.ddpsi
  m := 1 / 2
  M := 2
  N := 1
  m_pos := by norm_num
  phi_deriv := M.psi_deriv
  phi1_deriv := M.dpsi_deriv
  phi1_cont := continuous_iff_continuousAt.2 fun u =>
    (M.dpsi_deriv u).continuousAt
  phi2_cont := M.ddpsi_cont
  jacobian_lower := B.lower
  jacobian_upper := fun u => by
    rw [abs_of_nonneg (le_trans (by norm_num) (B.lower u))]
    exact B.upper u
  second_upper := B.second
  phi_zero := M.psi_zero
  phi_one := by
    simpa [M.psi_zero] using M.marking.translate 0
  phi_add_one := M.marking.translate
  phi1_periodic :=
    NormalizedMarkingControlledJunction.NormalizedC2Marking.dpsi_periodic M
  phi2_periodic :=
    NormalizedMarkingControlledJunction.NormalizedC2Marking.ddpsi_periodic M
  start := hstart
  finish := hfinish

theorem junction_cost
    {p q p' q' base rear : Data} {lambda Lambda : ℝ}
    (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    (M : NormalizedC2Marking base rear lambda Lambda)
    (B : UniformAnchoringBounds M)
    (hstart : ∀ u, Gamma.X 0 (M.marking.psi u) = p'.1 u)
    (hfinish : ∀ u, Gamma.X Gamma.T (M.marking.psi u) = q'.1 u) :
    cost (reparamAtJunction Gamma hC2
      (junction Gamma M B hstart hfinish)) = anchoringCost * cost Gamma := by
  rw [cost_reparamAtJunction]
  rfl

end NormalizedMarkingControlledJunction
