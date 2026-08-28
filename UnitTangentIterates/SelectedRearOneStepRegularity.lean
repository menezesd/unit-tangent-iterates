import UnitTangentIterates.PhysicalRearLimitComponents
import UnitTangentIterates.RearOwnHigherRegularity

/-!
# One-step regularity of an exact selected rear

Equality of curve ranges does not retain the point correspondence needed by
the selected-rear ODE.  `PhysicalRearLimitStageComponents` does: it stores the
steering solution, the inverse rear-arclength coordinate, and the exact rear
track reconstruction.  This module proves that this witness upgrades the
rear curve from the ambient `C2` tube regularity to `C3`.
-/

noncomputable section

open Function Set

namespace SelectedRearOneStepRegularity

open MarkedSpace NormalizedSelectedRearClosure
open NormalizedSteeringPhysicalRescaling SelectedRearFrenetChain

/-- Integrating a `C^n` derivative raises regularity by one. -/
theorem contDiff_succ_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {f f' : ℝ → E}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ContDiff ℝ (n : ℕ) f') :
    ContDiff ℝ (n + 1 : ℕ) f := by
  have hderiv : deriv f = f' := by
    funext x
    exact (hf x).deriv
  have h : ContDiff ℝ (((n : ℕ) : WithTop ℕ∞) + 1) f := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x => (hf x).differentiableAt, by simp, ?_⟩
    rw [hderiv]
    exact hf'
  exact_mod_cast h

/-- A Frenet chain with continuous curvature derivative is `C3`.  This is the
minimal analytic witness used by the selected-rear application below. -/
theorem contDiff_three_of_frenet
    {gamma : ℝ → ℂ} {psi k k' : ℝ → ℝ}
    (hgamma : ∀ s, HasDerivAt gamma
      (Complex.exp (Complex.I * (psi s : ℂ))) s)
    (hpsi : ∀ s, HasDerivAt psi (k s) s)
    (hk : ∀ s, HasDerivAt k (k' s) s)
    (hk' : Continuous k') :
    ContDiff ℝ (3 : ℕ) gamma := by
  have hk'0 : ContDiff ℝ (0 : ℕ) k' := by
    simpa [contDiff_zero] using hk'
  have hk1 : ContDiff ℝ (1 : ℕ) k := by
    simpa using contDiff_succ_of_hasDerivAt (n := 0) hk hk'0
  have hpsi2 : ContDiff ℝ (2 : ℕ) psi := by
    simpa using contDiff_succ_of_hasDerivAt (n := 1) hpsi hk1
  have htangent : ContDiff ℝ (2 : ℕ)
      (fun s => Complex.exp (Complex.I * (psi s : ℂ))) := by
    have hcast : ContDiff ℝ (2 : ℕ) (fun s => (psi s : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hpsi2
    exact Complex.contDiff_exp.comp (contDiff_const.mul hcast)
  simpa using contDiff_succ_of_hasDerivAt (n := 2) hgamma htangent

/-- The explicit derivative of selected-rear curvature is continuous for a
physical limiting rear stage. -/
theorem continuous_rearK'_of_stage
    {rear front : Data}
    (S : PathMetric.PhysicalRearLimitStageComponents rear front) :
    Continuous (rearK' S.steering S.period S.sf) := by
  have hdelta : Continuous (deltaPhys S.steering S.period) :=
    Differentiable.continuous fun s =>
      (hasDerivAt_deltaPhys S.steering S.period_positive s).differentiableAt
  have hdeltaComp : Continuous
      (fun x => deltaPhys S.steering S.period (S.sf x)) :=
    hdelta.comp S.inverseData.sf_continuous
  have hcos : Continuous
      (fun x => Real.cos (deltaPhys S.steering S.period (S.sf x))) :=
    Real.continuous_cos.comp hdeltaComp
  have hcos_ne : ∀ x,
      Real.cos (deltaPhys S.steering S.period (S.sf x)) ≠ 0 := by
    intro x
    have hm := deltaPhys_mem S.steering (P := S.period) (S.sf x)
    exact ne_of_gt
      (RearTrack.rear_speed_ge S.kap_lt_one S.kap_nonnegative hm.1 hm.2)
  have hinv : Continuous
      (fun x => (Real.cos (deltaPhys S.steering S.period (S.sf x)))⁻¹) :=
    hcos.inv₀ hcos_ne
  have hcurvature : Continuous
      (fun x => curvaturePhys S.steering S.period (S.sf x)) :=
    (continuous_curvaturePhys S.steering S.curvature_continuous).comp
      S.inverseData.sf_continuous
  have hsin : Continuous
      (fun x => Real.sin (deltaPhys S.steering S.period (S.sf x))) :=
    Real.continuous_sin.comp hdeltaComp
  unfold rearK'
  simpa [one_div, inv_pow] using
    ((hinv.pow 2).mul (hcurvature.sub hsin)).mul hinv

/-- **One selected inverse gains one derivative.**  An exact physical
selected-rear stage upgrades its rear arclength representative to `C3`.

The stage is the required orientation/phase witness missing from a bare
equality of ranges. -/
theorem contDiff_three_ev_of_stage
    {rear front : Data}
    (S : PathMetric.PhysicalRearLimitStageComponents rear front) :
    ContDiff ℝ (3 : ℕ) (ev rear) := by
  let F := S.rearFrenetCore
  apply contDiff_three_of_frenet F.curve_deriv F.angle_deriv
    F.curvature_deriv
  change Continuous (rearK' S.steering S.period S.sf)
  exact continuous_rearK'_of_stage S

/-- A selected-rear stage gains one derivative over the regularity encoded by
the physical front tangent angle.  In particular, a `C^(n+2)` front whose
tangent is presented by a `C^(n+1)` angle lift has a `C^(n+3)` selected rear. -/
theorem contDiff_succ_ev_of_stage
    {rear front : Data} (n : ℕ)
    (S : PathMetric.PhysicalRearLimitStageComponents rear front)
    (hTheta : ContDiff ℝ (n + 1 : ℕ)
      (thetaPhys S.steering S.period S.theta0)) :
    ContDiff ℝ (n + 3 : ℕ) (ev rear) := by
  let Theta := thetaPhys S.steering S.period S.theta0
  let delta := deltaPhys S.steering S.period
  let Psi : ℝ → ℝ := fun s => Theta s - delta s
  have hPsiDeriv : ∀ s, HasDerivAt Psi (Real.sin (Theta s - Psi s)) s := by
    intro s
    have ht := hasDerivAt_thetaPhys
      (P := S.period) (theta0 := S.theta0) S.steering
      S.curvature_continuous s
    have hd := hasDerivAt_deltaPhys S.steering S.period_positive s
    convert ht.sub hd using 1 <;> simp [Theta, delta, Psi] <;> ring
  have hPsi : ContDiff ℝ ((n + 1) + 1 : ℕ) Psi :=
    RearRegularity.contDiff_of_steering (n + 1) hTheta hPsiDeriv
  have hdelta : ContDiff ℝ (n + 1 : ℕ) delta := by
    have hTheta' : ContDiff ℝ (n + 1 : ℕ) Theta := by
      simpa [Theta] using hTheta
    have hPsi' : ContDiff ℝ (n + 1 : ℕ) Psi := hPsi.of_le (by simp)
    simpa only [Psi, sub_sub_cancel] using hTheta'.sub hPsi'
  let deltaFam : ℝ → ℝ → ℝ := fun _ s => delta s
  let sfFam : ℝ → ℝ → ℝ := fun _ x => S.sf x
  have hdeltaJoint : ContDiff ℝ (n + 1 : ℕ) (Function.uncurry deltaFam) := by
    simpa [deltaFam, Function.uncurry] using hdelta.comp contDiff_snd
  have hsfJoint : ContDiff ℝ (n + 1 : ℕ) (Function.uncurry sfFam) := by
    apply RearOwnHigherRegularity.contDiff_sf (n := n)
      S.kap_nonnegative S.kap_lt_one hdeltaJoint
    · intro t s
      exact (deltaPhys_mem S.steering (P := S.period) s).1
    · intro t s
      exact (deltaPhys_mem S.steering (P := S.period) s).2
    · intro t x
      exact S.arclength_rightInverse x
  have hsf : ContDiff ℝ (n + 1 : ℕ) S.sf := by
    have hline : ContDiff ℝ (n + 1 : ℕ) (fun x : ℝ => ((0 : ℝ), x)) :=
      contDiff_const.prodMk contDiff_id
    simpa [sfFam, Function.uncurry] using hsfJoint.comp hline
  have hcomp : ContDiff ℝ (n + 1 : ℕ) (fun x => delta (S.sf x)) :=
    hdelta.comp hsf
  have hcos_ne : ∀ x, Real.cos (delta (S.sf x)) ≠ 0 := by
    intro x
    have hm := deltaPhys_mem S.steering (P := S.period) (S.sf x)
    exact ne_of_gt
      (RearTrack.rear_speed_ge S.kap_lt_one S.kap_nonnegative hm.1 hm.2)
  have hrearK : ContDiff ℝ (n + 1 : ℕ)
      (rearK S.steering S.period S.sf) := by
    have hs := Real.contDiff_sin.comp hcomp
    have hc := Real.contDiff_cos.comp hcomp
    change ContDiff ℝ (n + 1 : ℕ)
      (fun x => Real.tan (deltaPhys S.steering S.period (S.sf x)))
    simpa [Real.tan_eq_sin_div_cos, div_eq_mul_inv, delta] using
      hs.mul (hc.inv hcos_ne)
  let F := S.rearFrenetCore
  have hk : ContDiff ℝ (n + 1 : ℕ) F.k := by
    change ContDiff ℝ (n + 1 : ℕ) (rearK S.steering S.period S.sf)
    exact hrearK
  have hpsi : ContDiff ℝ ((n + 1) + 1 : ℕ) F.psi :=
    contDiff_succ_of_hasDerivAt (n := n + 1) F.angle_deriv hk
  have htangent : ContDiff ℝ ((n + 1) + 1 : ℕ)
      (fun x => Complex.exp (Complex.I * (F.psi x : ℂ))) := by
    simpa [mul_comm] using RearRegularity.contDiff_unitTangent hpsi
  have hcurve : ContDiff ℝ (((n + 1) + 1) + 1 : ℕ) (ev rear) :=
    contDiff_succ_of_hasDerivAt (n := (n + 1) + 1) F.curve_deriv htangent
  simpa [Nat.add_assoc] using hcurve

/-- Regularity of a unit-speed front curve transfers to its chosen physical
tangent-angle lift.  The identity `Theta' = Im (T' / T)` avoids choosing a
local branch of the complex logarithm. -/
theorem contDiff_thetaPhys_of_front
    {rear front : Data} (n : ℕ)
    (S : PathMetric.PhysicalRearLimitStageComponents rear front)
    (hfront : ContDiff ℝ (n + 2 : ℕ) (ev front)) :
    ContDiff ℝ (n + 1 : ℕ)
      (thetaPhys S.steering S.period S.theta0) := by
  let Theta := thetaPhys S.steering S.period S.theta0
  let K := curvaturePhys S.steering S.period
  let T : ℝ → ℂ := fun s => Complex.exp (Complex.I * (Theta s : ℂ))
  have hfront' : ContDiff ℝ
      (((n + 1 : ℕ) : WithTop ℕ∞) + 1) (ev front) := by
    exact_mod_cast hfront
  have hderivFrontWT : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞)
      (deriv (ev front)) :=
    (contDiff_succ_iff_deriv.mp hfront').2.2
  have hderivFront : ContDiff ℝ (n + 1 : ℕ) (deriv (ev front)) := by
    exact_mod_cast hderivFrontWT
  have hderivFront_eq : deriv (ev front) = T := by
    funext s
    exact (S.front_frenet s).deriv
  have hT : ContDiff ℝ (n + 1 : ℕ) T := by
    rw [hderivFront_eq] at hderivFront
    exact hderivFront
  have hT' : ContDiff ℝ (((n : ℕ) : WithTop ℕ∞) + 1) T := by
    exact_mod_cast hT
  have hderivTWT : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) (deriv T) :=
    (contDiff_succ_iff_deriv.mp hT').2.2
  have hderivT : ContDiff ℝ (n : ℕ) (deriv T) := by
    exact_mod_cast hderivTWT
  have hTn : ContDiff ℝ (n : ℕ) T := hT.of_le (by simp)
  have hquot : ContDiff ℝ (n : ℕ) (fun s => deriv T s / T s) :=
    by simpa [div_eq_mul_inv] using
      hderivT.mul (hTn.inv fun s => Complex.exp_ne_zero _)
  have him : ContDiff ℝ (n : ℕ) (fun s => (deriv T s / T s).im) :=
    Complex.imCLM.contDiff.comp hquot
  have hThetaDeriv : ∀ s, HasDerivAt Theta (K s) s := by
    intro s
    exact hasDerivAt_thetaPhys S.steering S.curvature_continuous s
  have hTDeriv : ∀ s,
      HasDerivAt T (T s * (Complex.I * (K s : ℂ))) s := by
    intro s
    have hc : HasDerivAt (fun x => (Theta x : ℂ)) (K s : ℂ) s := by
      convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s
        (hThetaDeriv s) using 1 <;> simp
    simpa [T, mul_assoc] using (hc.const_mul Complex.I).cexp
  have hK_eq : K = fun s => (deriv T s / T s).im := by
    funext s
    rw [(hTDeriv s).deriv]
    simp [T, Complex.exp_ne_zero]
  have hK : ContDiff ℝ (n : ℕ) K := by
    rw [hK_eq]
    exact him
  exact contDiff_succ_of_hasDerivAt (n := n) hThetaDeriv hK

/-- One-step regularity gain stated solely with the adjacent front curve and
the full selected-rear stage witness. -/
theorem contDiff_succ_ev_of_stage_of_front
    {rear front : Data} (n : ℕ)
    (S : PathMetric.PhysicalRearLimitStageComponents rear front)
    (hfront : ContDiff ℝ (n + 2 : ℕ) (ev front)) :
    ContDiff ℝ (n + 3 : ℕ) (ev rear) :=
  contDiff_succ_ev_of_stage n S (contDiff_thetaPhys_of_front n S hfront)

end SelectedRearOneStepRegularity
