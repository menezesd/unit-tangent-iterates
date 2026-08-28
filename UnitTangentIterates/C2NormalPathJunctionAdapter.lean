import Mathlib
import UnitTangentIterates.C2NormalPathReparam

/-! # Downstream adapter for controlled marked-path junctions -/

noncomputable section

open Set Function MeasureTheory MarkedSpace

namespace PathMetric

open NormalPath

/-- A controlled fixed spatial change of marking joining the desired endpoint
data.  The quasi-periodicity fields are the junction information used by
recursive marked assembly. -/
structure ReparamJunctionCertificate
    {p q p' q' : Data} (Gamma : NormalPath p q) where
  phi : ℝ → ℝ
  phi1 : ℝ → ℝ
  phi2 : ℝ → ℝ
  m : ℝ
  M : ℝ
  N : ℝ
  m_pos : 0 < m
  phi_deriv : ∀ u, HasDerivAt phi (phi1 u) u
  phi1_deriv : ∀ u, HasDerivAt phi1 (phi2 u) u
  phi1_cont : Continuous phi1
  phi2_cont : Continuous phi2
  jacobian_lower : ∀ u, m ≤ phi1 u
  jacobian_upper : ∀ u, |phi1 u| ≤ M
  second_upper : ∀ u, |phi2 u| ≤ N
  phi_zero : phi 0 = 0
  phi_one : phi 1 = 1
  phi_add_one : ∀ u, phi (u + 1) = phi u + 1
  phi1_periodic : Periodic phi1 1
  phi2_periodic : Periodic phi2 1
  start : ∀ u, Gamma.X 0 (phi u) = p'.1 u
  finish : ∀ u, Gamma.X Gamma.T (phi u) = q'.1 u

/-- Constructor output sufficient to recover the strengthened `C²` path
certificate after the spatial marking is changed.  Analytic constructors can
export these fields without exposing their internal formula for `eta`. -/
structure ReparamC2Certificate
    {p q p' q' : Data} (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma) where
  eta1 : ℝ → ℝ → ℝ
  eta2 : ℝ → ℝ → ℝ
  eta_deriv : ∀ t u, HasDerivAt (fun v => Gamma.eta t (J.phi v)) (eta1 t u) u
  eta1_deriv : ∀ t u, HasDerivAt (eta1 t) (eta2 t u) u
  eta1_cont : ∀ t, Continuous (eta1 t)
  eta2_cont : ∀ t, Continuous (eta2 t)
  eta1_bdd : ∀ t, BddAbove (Set.range fun u => |eta1 t u|)
  eta2_bdd : ∀ t, BddAbove (Set.range fun u => |eta2 t u|)
  eta_periodic : ∀ t, Periodic (fun u => Gamma.eta t (J.phi u)) 1
  eta1_periodic : ∀ t, Periodic (eta1 t) 1
  eta2_periodic : ∀ t, Periodic (eta2 t) 1
  eta1_formula : ∀ t u,
    eta1 t u = hC2.eta1 t (J.phi u) * J.phi1 u
  eta2_formula : ∀ t u,
    eta2 t u = hC2.eta2 t (J.phi u) * J.phi1 u ^ 2 +
      hC2.eta1 t (J.phi u) * J.phi2 u

/-- The path produced by a junction certificate. -/
def reparamAtJunction
    {p q p' q' : Data} (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma) : NormalPath p' q' :=
  Gamma.reparamSpace hC2 J.m_pos J.phi_deriv J.phi1_deriv J.phi1_cont J.phi2_cont
    J.jacobian_lower J.jacobian_upper J.second_upper J.phi_zero J.phi_one
    J.start J.finish

/-- Abstract strengthened constructor certificates produce actual
`C2NormalPathData` for the controlled junction path. -/
def c2NormalPathData_reparamAtJunction
    {p q p' q' : Data} {Gamma : NormalPath p q} (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma) (C : ReparamC2Certificate Gamma hC2 J) :
    C2NormalPathData (reparamAtJunction Gamma hC2 J) where
  eta1 := C.eta1
  eta2 := C.eta2
  eta_deriv := C.eta_deriv
  eta1_deriv := C.eta1_deriv
  eta1_cont := C.eta1_cont
  eta2_cont := C.eta2_cont
  eta1_bdd := C.eta1_bdd
  eta2_bdd := C.eta2_bdd
  eta_periodic := C.eta_periodic
  eta1_periodic := C.eta1_periodic
  eta2_periodic := C.eta2_periodic

/-- Exact transformed density, the pointwise estimate needed by recursive
summability bookkeeping. -/
theorem reparamAtJunction_density
    {p q p' q' : Data} {Gamma : NormalPath p q} (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma) (t : ℝ) :
    (reparamAtJunction Gamma hC2 J).m t =
      reparamCostConst J.m J.M J.N * Gamma.m t := rfl

/-- The controlled junction multiplies total cost by exactly the advertised
constant. -/
theorem cost_reparamAtJunction
    {p q p' q' : Data} {Gamma : NormalPath p q} (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma) :
    cost (reparamAtJunction Gamma hC2 J) =
      reparamCostConst J.m J.M J.N * cost Gamma := by
  simp [cost, reparamAtJunction, NormalPath.reparamSpace,
    MeasureTheory.integral_const_mul]

/-- Complete downstream output: a marked junction path, its strengthened C²
certificate, endpoint equalities, and its recursive cost estimate. -/
theorem exists_controlled_reparam_junction
    {p q p' q' : Data} {Gamma : NormalPath p q} (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma) (C : ReparamC2Certificate Gamma hC2 J) :
    ∃ Gamma' : NormalPath p' q',
      Nonempty (C2NormalPathData Gamma') ∧
      Gamma'.X 0 = p'.1 ∧ Gamma'.X Gamma'.T = q'.1 ∧
      cost Gamma' ≤ reparamCostConst J.m J.M J.N * cost Gamma := by
  refine ⟨reparamAtJunction Gamma hC2 J,
    ⟨c2NormalPathData_reparamAtJunction hC2 J C⟩, ?_, ?_, ?_⟩
  · funext u
    exact J.start u
  · funext u
    exact J.finish u
  · exact (cost_reparamAtJunction hC2 J).le

end PathMetric
