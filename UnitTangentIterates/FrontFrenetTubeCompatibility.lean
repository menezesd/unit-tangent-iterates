import Mathlib
import UnitTangentIterates.SelectedRearFrenetChain

noncomputable section

open Function Set

namespace FrontFrenetTubeCompatibility

/-- A unit-speed Frenet presentation of a marked curve identifies its scalar
angle derivative with the intrinsic curvature encoded by the marked velocity
and acceleration.  In particular, the closed `kmin = 0` tube makes that
scalar nonnegative. -/
theorem curvature_nonnegative_of_tube
    {c dlt : ℝ} {p : MarkedSpace.Data} (hp : MarkedSpace.IsTubeMember c 0 dlt p)
    (hc : 0 < c) {theta K : ℝ → ℝ}
    (hfront : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I * (theta s : ℂ))) s)
    (htheta : ∀ s, HasDerivAt theta (K s) s) :
    ∀ s, 0 ≤ K s := by
  let L := MarkedSpace.perim p
  have hL : 0 < L := MarkedSpace.perim_pos hc hp
  have hLn : L ≠ 0 := ne_of_gt hL
  have hinner : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t / L) (1 / L) s := by
    intro s
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const L
  have hvel : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (p.2.1 (s / L) / L) s := by
    intro s
    have h := (hp.hasDerivAt_curve (s / L)).scomp s (hinner s)
    simpa [MarkedSpace.ev, L, Function.comp, div_eq_mul_inv, one_div,
      smul_eq_mul, mul_comm] using h
  have htangent : ∀ s, p.2.1 (s / L) / L =
      Complex.exp (Complex.I * (theta s : ℂ)) := fun s =>
    (hvel s).unique (hfront s)
  intro s
  have hacc : HasDerivAt (fun t => p.2.1 (t / L) / L)
      (p.2.2 (s / L) / (L ^ 2)) s := by
    have h0 := (hp.hasDerivAt_vel (s / L)).scomp s (hinner s)
    have h1 := h0.div_const L
    simpa [Function.comp, div_eq_mul_inv, one_div, smul_eq_mul, sq,
      mul_comm, mul_assoc, mul_left_comm] using h1
  have hexp : HasDerivAt
      (fun t => Complex.exp (Complex.I * (theta t : ℂ)))
      (Complex.exp (Complex.I * (theta s : ℂ)) *
        (Complex.I * (K s : ℂ))) s := by
    have hi := ((htheta s).ofReal_comp).const_mul Complex.I
    simpa [mul_comm, mul_assoc] using hi.cexp
  have haccEq : p.2.2 (s / L) / (L ^ 2) =
      Complex.exp (Complex.I * (theta s : ℂ)) *
        (Complex.I * (K s : ℂ)) := by
    apply hacc.unique
    have hfun : (fun t : ℝ => p.2.1 (t / L) / L)
        = fun t : ℝ => Complex.exp (Complex.I * (theta t : ℂ)) := funext htangent
    rw [hfun]
    exact hexp
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hLn
  have hvelEq : p.2.1 (s / L) =
      (L : ℂ) * Complex.exp (Complex.I * (theta s : ℂ)) := by
    rw [← htangent s]
    field_simp
  have haccMul : p.2.2 (s / L) = ((L : ℂ) ^ 2) *
      (Complex.exp (Complex.I * (theta s : ℂ)) *
        (Complex.I * (K s : ℂ))) := by
    rw [← haccEq]
    field_simp
  have hce : (starRingEnd ℂ) (Complex.exp (Complex.I * (theta s : ℂ)))
      * Complex.exp (Complex.I * (theta s : ℂ)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  have hb := hp.curv_lb (s / L)
  simp only [zero_mul] at hb
  have hVA : (starRingEnd ℂ) (p.2.1 (s / L)) * p.2.2 (s / L)
      = ((L ^ 3 * K s : ℝ) : ℂ) * Complex.I := by
    rw [hvelEq, haccMul, map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination ((L : ℂ) ^ 3 * (K s : ℂ) * Complex.I) * hce
  rw [hVA] at hb
  simp only [Complex.mul_I_im, Complex.ofReal_re] at hb
  nlinarith [hb, show (0:ℝ) < L ^ 3 by positivity]

/-- The successor physical steering curvature is nonnegative whenever its
marked front belongs to the closed nonnegative-curvature tube. -/
theorem curvaturePhys_nonnegative_of_tube
    {kap c dlt P theta0 : ℝ} (d : NormalizedSelectedRearClosure.SteeringData kap)
    {p : MarkedSpace.Data} (hp : MarkedSpace.IsTubeMember c 0 dlt p)
    (hc : 0 < c) (hK : Continuous d.K)
    (hfront : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I *
        (NormalizedSteeringPhysicalRescaling.thetaPhys d P theta0 s : ℂ))) s) :
    ∀ s, 0 ≤ NormalizedSteeringPhysicalRescaling.curvaturePhys d P s :=
  curvature_nonnegative_of_tube hp hc hfront
    (NormalizedSteeringPhysicalRescaling.hasDerivAt_thetaPhys d hK)

/-- Closed successor-tube membership now discharges the last curvature field
of the selected-rear strictness datum. -/
def limitStrictness_of_rearCore_and_successor_tube
    {kap c dlt P theta0 : ℝ}
    (d : NormalizedSelectedRearClosure.SteeringData kap) (sf : ℝ → ℝ)
    {p q : MarkedSpace.Data}
    (F : SelectedRearFrenetChain.RearFrenetCoreCertificate q)
    (hp : MarkedSpace.IsTubeMember c 0 dlt p) (hc : 0 < c)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1) (hK : Continuous d.K)
    (hfront : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I *
        (NormalizedSteeringPhysicalRescaling.thetaPhys d P theta0 s : ℂ))) s)
    (hk : F.k = SelectedRearFrenetChain.rearK d P sf)
    (hk' : F.k' = SelectedRearFrenetChain.rearK' d P sf) :
    UnconditionalAssembly.LimitStrictnessData q :=
  F.limitStrictness_of_front_curvature_nonnegative d sf hkap0 hkap1 hk hk'
    (fun s => curvaturePhys_nonnegative_of_tube d hp hc hK hfront (sf s))

end FrontFrenetTubeCompatibility
