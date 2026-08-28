import UnitTangentIterates.CompatibleMarkings
import UnitTangentIterates.InterpolationSelectedRearEndpoints
import UnitTangentIterates.InterpolationControlledJunctionOutput
import UnitTangentIterates.ModelGaugeControlledFamilyChooser

/-! # Compatible selected-rear endpoint junction -/

noncomputable section

open MarkedSpace

namespace PathMetric

/-- Once compatible rotation and the selected-rear arclength identification
make the marked endpoints literal, the junction reparameterization is the
identity.  This is the `ReparamJunctionCertificate` used at the canonical
affinely marked endpoint. -/
def reparamJunctionCertificate_of_compatible_affine_endpoints
    {p q p' q' : Data} {Gamma : NormalPath p q}
    (hp : p' = p) (hq : q' = q) :
    ReparamJunctionCertificate (p' := p') (q' := q') Gamma where
  phi := fun u => u
  phi1 := fun _ => 1
  phi2 := fun _ => 0
  m := 1
  M := 1
  N := 0
  m_pos := one_pos
  phi_deriv := fun u => hasDerivAt_id u
  phi1_deriv := fun u => hasDerivAt_const u (1 : ℝ)
  phi1_cont := continuous_const
  phi2_cont := continuous_const
  jacobian_lower := fun _ => le_rfl
  jacobian_upper := fun _ => by norm_num
  second_upper := fun _ => by norm_num
  phi_zero := rfl
  phi_one := rfl
  phi_add_one := fun _ => rfl
  phi1_periodic := fun _ => rfl
  phi2_periodic := fun _ => rfl
  start := by
    subst hp
    exact fun u => Gamma.start u
  finish := by
    subst hq
    exact fun u => Gamma.finish u

/-- Paper-facing endpoint bridge: any proof that the initial endpoint is
unchanged and that the compatibly marked terminal rear is the canonical
selected inverse immediately supplies the recursive junction certificate. -/
theorem exists_junction_of_compatible_selectedRear
    {p q p' q' : Data} {Gamma : NormalPath p q}
    (hp : p' = p) (hselected : q' = q) :
    ∃ J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma,
      J.m = 1 ∧ J.M = 1 ∧ J.N = 0 := by
  let J := reparamJunctionCertificate_of_compatible_affine_endpoints
    (Gamma := Gamma) hp hselected
  exact ⟨J, rfl, rfl, rfl⟩

/-- The strengthened C² certificate for the identity compatible junction. -/
def reparamC2Certificate_of_compatible_affine_endpoints
    {p q : Data} {Gamma : NormalPath p q} (hC2 : C2NormalPathData Gamma) :
    ReparamC2Certificate Gamma hC2
      (reparamJunctionCertificate_of_compatible_affine_endpoints
        (Gamma := Gamma) rfl rfl) where
  eta1 := hC2.eta1
  eta2 := hC2.eta2
  eta_deriv := hC2.eta_deriv
  eta1_deriv := hC2.eta1_deriv
  eta1_cont := hC2.eta1_cont
  eta2_cont := hC2.eta2_cont
  eta1_bdd := hC2.eta1_bdd
  eta2_bdd := hC2.eta2_bdd
  eta_periodic := hC2.eta_periodic
  eta1_periodic := hC2.eta1_periodic
  eta2_periodic := hC2.eta2_periodic
  eta1_formula := fun t u => by
    show hC2.eta1 t u = hC2.eta1 t u * 1
    ring
  eta2_formula := fun t u => by
    show hC2.eta2 t u = hC2.eta2 t u * 1 ^ 2 + hC2.eta1 t u * 0
    ring

/-- Sequence-level compatible-affine chooser.  Every already endpoint-correct
recursive stage receives the identity marking junction, with common derivative
ceilings `M=1`, `N=0`. -/
def ModelRecursiveEndpointDiffeomorphisms.ofCompatibleAffineStages
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg : ℝ}
    (A : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) :
    ModelRecursiveEndpointDiffeomorphisms A P0 P1 khat G1 Cg := by
  let J : ∀ n k, ReparamJunctionCertificate
      (p' := Q n k) (q' := Q n (k + 1)) (A.stage n k).path :=
    fun n k => reparamJunctionCertificate_of_compatible_affine_endpoints rfl rfl
  let C2 : ∀ n k, ReparamC2Certificate (A.stage n k).path
      (A.stage n k).c2 (J n k) :=
    fun n k => reparamC2Certificate_of_compatible_affine_endpoints (A.stage n k).c2
  have h := ModelRecursiveEndpointDiffeomorphisms.ofBaseVariableSpeed
    (M := (1 : ℝ)) (N := (0 : ℝ)) A J C2 (fun _ _ => rfl) (fun _ _ => rfl)
      hP0 hP1 hkhat hG1 hCg (by norm_num) (by norm_num)
  simpa using h

end PathMetric
