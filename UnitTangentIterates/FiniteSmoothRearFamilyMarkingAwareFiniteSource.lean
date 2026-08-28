import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareResidual
import UnitTangentIterates.SelectedRearGaugeQualitative
import UnitTangentIterates.RearJacobiSourceCost
import UnitTangentIterates.SelectedInverseUnique
import UnitTangentIterates.SelInvFrontMotionC2

/-!
# The finite source produced by an all-order selected-rear source

The all-order sidecar determines all differential data in the next finite
gauge source.  This file makes those choices canonical and applies the sharp
source estimate from `RearJacobiSourceCost`.  The only retained input is the
chosen normal-path alignment/pinning and the scalar inequalities used by the
long gauge theorem.
-/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwareSmoothSource

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  RearOwnHigherRegularity RearFamilyFrame

/-- Uniform spatial curvature-derivative majorant on the selected strip. -/
def successorKx (kap : ℝ) : ℝ :=
  2 * kap / Real.sqrt (1 - kap ^ 2) ^ 3

/-- The sharp inverse-Jacobi source constant. -/
def successorSourceConst (kap periodLower : ℝ) : ℝ :=
  RearJacobiSourceCost.jacobiSourceConst kap periodLower

/-- The intrinsic selected-rear normal velocity is differentiated by its
Jacobi equation.  The two terms cost respectively one strip cosine and one
unweighted copy of the path density. -/
def intrinsicDerivativeConst (kap : ℝ) : ℝ :=
  1 / Real.sqrt (1 - kap ^ 2) + 1

/-- Source constant after differentiating in physical rear arclength. -/
def intrinsicSourceConst (kap derivativeConst : ℝ) : ℝ :=
  RearJacobiSourceCost.jacobiSourceConst kap (1 / derivativeConst)

/-- Density used by the successor source after the strip loss. -/
def successorDensity {a b : Data} (Delta : NormalPath a b) (kap : ℝ) : ℝ → ℝ :=
  fun t => Delta.m t / Real.sqrt (1 - kap ^ 2)

/-- The front-normal convention used by the inverse Jacobi equation is the
normal component in the intrinsic tangent frame: `rearAngle + steering`
cancels back to the front angle. -/
theorem frontNormalVelocityAt_successor_eq_frameNormal
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (S : SmoothSource A periodLower kap) (D : NormalizedSteering S)
    (t s : ℝ) :
    frontNormalVelocityAt (partialTime (front A)) (angle A) D.arclength t s =
      frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t s := by
  have hdot : partialTime (front A) t s = A.Ydot t s := by
    exact (RearOwnHigherRegularity.hasDerivAt_partialTime
      (S.front_smooth.differentiable (by norm_num)) t s).unique
      (A.rear_time_deriv t s)
  simp only [frontNormalVelocityAt]
  rw [hdot]
  simp only [frontNormalVelocityAt, SelectedInverseJacobiODE.frontNormalVelocity,
    RearTrack.rearAngle, angle, frameNormal]
  ring_nf
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The genuinely correlated and scalar inputs not implied by smoothness.
In particular, the Jacobi identity is not a field: it is reconstructed from
the canonical smooth rear family. -/
structure MarkingAwareFiniteSourceMajorants
    {p q a b : Data} {Gamma : NormalPath p q} (Delta : NormalPath a b)
    {P0 kh khat Qmax periodLower kap : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    {D : NormalizedSteering S} (R : SuccessorRegularity D)
    (khatNext QmaxNext : ℝ) where
  marking : MarkingCertificate Delta
    (frontNormalVelocityAt (partialTime (front A)) (angle A) D.arclength)
    (period A)
  density_eq : A.m = Delta.m
  tangential_zero : ∀ t, frameTangential
    (partialTime (nextFront D R.sf)) (nextAngle D R.sf) t 0 = 0
  periodUpper_le : S.periodUpper ≤ QmaxNext
  rearKappa1_le : GaugeMarkedDataOfRearFamily.rearKappa1 kap ≤ khatNext
  numerical_A :
    2 + 2 * khatNext * GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap ≤
      1 / periodLower
  numerical_K :
    (intrinsicSourceConst kap (intrinsicDerivativeConst kh) + 2) + khatNext ^ 2 +
        2 * GaugeRearFamilyFromFront.rearDriftConst QmaxNext kap * successorKx kap ≤
      1 / periodLower ^ 2 + khatNext ^ 2

/-- Smoothness and the explicit majorants produce the entire finite residual.
The source derivative has the paper's sharp constant
`jacobiSourceConst kap periodLower`; no arbitrary `Dd`, `d`, or `Kx` callback
remains. -/
theorem exists_markingAwareFiniteSourceResidual_of_majorants
    {p q a b : Data} {Gamma : NormalPath p q} {Delta : NormalPath a b}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    {D : NormalizedSteering S} {R : SuccessorRegularity D}
    (M : MarkingAwareFiniteSourceMajorants Delta R khatNext QmaxNext) :
    Nonempty (MarkingAwareFiniteSourceResidual Delta R khatNext QmaxNext) := by
  let etaF : ℝ → ℝ → ℝ :=
    frontNormalVelocityAt (partialTime (front A)) (angle A) D.arclength
  let source : ℝ → ℝ → ℝ := fun t x =>
    etaF t (R.sf t x) / Real.cos (D.arclength t (R.sf t x))
  let gS : ℝ → ℝ → ℝ := fun t x => deriv (source t) x
  let dens : ℝ → ℝ := successorDensity Delta kap
  let dd : ℝ := intrinsicSourceConst kap (intrinsicDerivativeConst kh)
  let kx0 : ℝ := successorKx kap
  have hPpos : ∀ t, 0 < period A t := fun t =>
    lt_of_lt_of_le S.periodLower_pos (S.period_lower t)
  have hcos : ∀ t x, Real.cos (D.arclength t x) ≠ 0 := by
    intro t x
    have hs := D.strip t (x / period A t)
    have hp : 0 < Real.sqrt (1 - kap ^ 2) :=
      Real.sqrt_pos.mpr (by nlinarith [S.kap_nonnegative, S.kap_lt_one])
    exact ne_of_gt (lt_of_lt_of_le hp
      (Shadowing.cos_ge_of_mem_strip hs.1 hs.2))
  have hcurv : ∀ t x, |curvature A t x| ≤ kap := by
    intro t x
    have h := S.curvature_bound t (x / period A t)
    simpa [normalizedCurvature, mul_div_cancel₀ x (hPpos t).ne'] using h
  have hdeltaC : Continuous (uncurry D.arclength) :=
    D.contDiff_infty_arclength.continuous
  have hsfC : Continuous (uncurry R.sf) := R.sf_smooth.continuous
  have hrearPos : ∀ t, 0 < nextPeriod D t := by
    intro t
    exact SelectedInverseUnique.rearArclength_pos (hPpos t)
      S.kap_nonnegative S.kap_lt_one
      (hdeltaC.comp (continuous_const.prodMk continuous_id))
      (fun x => D.strip t (x / period A t))
  have hrearLe : ∀ t, nextPeriod D t ≤ QmaxNext := by
    intro t
    exact (ArclengthInverse.rearArclength_le_of_period
      (hdeltaC.comp (continuous_const.prodMk continuous_id)) (hPpos t).le).trans
      ((S.period_upper t).trans M.periodUpper_le)
  have hcore :=
    FiniteSmoothRearFamilyMarkingAwareSuccessorFront.MarkingAwareSource.successorFrontCore A
  have hcanonical := SelectedRearGaugeQualitative.exists_canonical_gauge_jacobi_data
    S.kap_nonnegative S.kap_lt_one
    (contDiff_infty.mp S.front_smooth 3)
    (contDiff_infty.mp S.angle_smooth 3)
    (contDiff_infty.mp D.contDiff_infty_arclength 4)
    (contDiff_infty.mp R.sf_smooth 4)
    hcore.front_frenet hcore.angle_frenet
    R.steering_deriv
    (fun t x => (D.strip t (x / period A t)).1)
    (fun t x => (D.strip t (x / period A t)).2)
    R.sf_rightInverse
  obtain ⟨Ydot, hYtime, hYdot3, hang3, htan1, hjac0⟩ := hcanonical
  have hYdot : ∀ t x, Ydot t x = partialTime (nextFront D R.sf) t x := by
    intro t x
    exact (hYtime t x).unique (R.front_time_deriv t x)
  have hYdotEq : Ydot = partialTime (nextFront D R.sf) := by
    funext t x
    exact hYdot t x
  have hjac : ∀ t x, HasDerivAt
      (fun x' => frameNormal (partialTime (nextFront D R.sf))
        (nextAngle D R.sf) t x')
      (etaF t (R.sf t x) / Real.cos (D.arclength t (R.sf t x)) -
        frameNormal (partialTime (nextFront D R.sf))
          (nextAngle D R.sf) t x) x := by
    intro t x
    rw [hYdotEq] at hjac0
    simpa [etaF, nextAngle] using hjac0 t x
  let etaFs : ℝ → ℝ → ℝ := fun t x =>
    A.etaF t (A.sf t x) / Real.cos (A.delta t (A.sf t x)) - etaF t x
  have hetaD : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s := by
    intro t s
    have heq : etaF t =
        frameNormal A.Ydot (rearOwnAngle A.Theta A.delta A.sf) t := by
      funext x
      exact frontNormalVelocityAt_successor_eq_frameNormal S D t x
    rw [heq]
    simpa [etaFs, heq] using A.jacobi t s
  have hetaBd : ∀ t s, |etaF t s| ≤ Delta.m t :=
    M.marking.etaF_bound hPpos
  have hsqrtKhPos : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hderivPos : 0 < intrinsicDerivativeConst kh := by
    unfold intrinsicDerivativeConst
    positivity
  have hetaDBd : ∀ t s,
      |etaFs t s| ≤ intrinsicDerivativeConst kh * Delta.m t := by
    intro t s
    have hcosLower : Real.sqrt (1 - kh ^ 2) ≤
        Real.cos (A.delta t (A.sf t s)) :=
      Shadowing.cos_ge_of_mem_strip
        (A.strip_nonnegative t _) (A.strip_le t _)
    have hcosPos : 0 < Real.cos (A.delta t (A.sf t s)) :=
      lt_of_lt_of_le hsqrtKhPos hcosLower
    have hsqrtKhLe : Real.sqrt (1 - kh ^ 2) ≤ 1 := by
      have := Real.sqrt_le_sqrt
        (show 1 - kh ^ 2 ≤ (1 : ℝ) by nlinarith [sq_nonneg kh])
      simpa using this
    have hGammaLe : Gamma.m t ≤ A.m t := by
      have hmul : Gamma.m t * Real.sqrt (1 - kh ^ 2) ≤ Gamma.m t :=
        mul_le_of_le_one_right (Gamma.m_nonneg t) hsqrtKhLe
      have hdiv : Gamma.m t ≤ Gamma.m t / Real.sqrt (1 - kh ^ 2) := by
        exact (le_div_iff₀ hsqrtKhPos).2 hmul
      exact hdiv.trans (A.density_domination t)
    have hnum : |A.etaF t (A.sf t s)| ≤ Delta.m t := by
      exact (A.etaF_bound t _).trans
        (hGammaLe.trans_eq (congrFun M.density_eq t))
    have hfrac :
        |A.etaF t (A.sf t s) / Real.cos (A.delta t (A.sf t s))| ≤
          Delta.m t / Real.sqrt (1 - kh ^ 2) := by
      rw [abs_div, abs_of_pos hcosPos]
      exact div_le_div₀ (Delta.m_nonneg t) hnum hsqrtKhPos hcosLower
    calc
      |etaFs t s| ≤
          |A.etaF t (A.sf t s) / Real.cos (A.delta t (A.sf t s))| +
            |etaF t s| := by
              simpa [etaFs, sub_eq_add_neg] using
                abs_add_le
                  (A.etaF t (A.sf t s) / Real.cos (A.delta t (A.sf t s)))
                  (-etaF t s)
      _ ≤ Delta.m t / Real.sqrt (1 - kh ^ 2) + Delta.m t :=
        add_le_add hfrac (hetaBd t s)
      _ = intrinsicDerivativeConst kh * Delta.m t := by
        simp [intrinsicDerivativeConst]
        ring
  have hetaDBd' : ∀ t s,
      |etaFs t s| ≤ Delta.m t / (1 / intrinsicDerivativeConst kh) := by
    intro t s
    simpa [div_eq_mul_inv, mul_comm] using hetaDBd t s
  have hsourceD : ∀ t x, HasDerivAt (source t) (gS t x) x := by
    intro t x
    have hnum := (hetaD t (R.sf t x)).comp x (R.sf_deriv t x)
    have hden := ((R.steering_deriv t (R.sf t x)).comp x
      (R.sf_deriv t x)).cos
    have hd := hnum.div hden (hcos t (R.sf t x))
    exact hd.congr_deriv hd.deriv.symm
  have hgS0 : ∀ t x, |gS t x| ≤ dd * Delta.m t := by
    intro t x
    exact RearJacobiSourceCost.abs_source_deriv_le
      S.kap_nonnegative S.kap_lt_one (one_div_pos.mpr hderivPos)
      (hetaD t) (hetaBd t) (hetaDBd' t)
      (fun s => (D.strip t (s / period A t)).1)
      (fun s => (D.strip t (s / period A t)).2)
      (R.steering_deriv t) (hcurv t) (R.sf_deriv t) (hsourceD t) x
  have hsqrtPos : 0 < Real.sqrt (1 - kap ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [S.kap_nonnegative, S.kap_lt_one])
  have hsqrtLe : Real.sqrt (1 - kap ^ 2) ≤ 1 := by
    have := Real.sqrt_le_sqrt (show 1 - kap ^ 2 ≤ (1 : ℝ) by nlinarith [sq_nonneg kap])
    simpa using this
  have hmLe : ∀ t, Delta.m t ≤ dens t := by
    intro t
    dsimp [dens, successorDensity]
    exact (le_div_iff₀ hsqrtPos).2
      (mul_le_of_le_one_right (Delta.m_nonneg t) hsqrtLe)
  have hdd0 : 0 ≤ dd :=
    RearJacobiSourceCost.jacobiSourceConst_nonneg
      (one_div_pos.mpr hderivPos)
  have hgS : ∀ t x, |gS t x| ≤ dd * dens t := by
    intro t x
    exact (hgS0 t x).trans (mul_le_mul_of_nonneg_left (hmLe t) hdd0)
  have hKx : ∀ t x,
      |(curvature A t (R.sf t x) - Real.sin (D.arclength t (R.sf t x))) /
        Real.cos (D.arclength t (R.sf t x)) ^ 3| ≤ kx0 := by
    intro t x
    exact RearOwnTangential.abs_curvDeriv_le_strip S.kap_nonnegative S.kap_lt_one
      (D.strip t (R.sf t x / period A t)).1
      (D.strip t (R.sf t x / period A t)).2 (hcurv t (R.sf t x))
  have hkx0 : 0 ≤ kx0 := by
    dsimp [kx0, successorKx]
    exact div_nonneg (mul_nonneg (by norm_num) S.kap_nonnegative)
      (pow_nonneg (Real.sqrt_nonneg _) 3)
  have hKxC : Continuous (uncurry fun t x =>
      (curvature A t (R.sf t x) - Real.sin (D.arclength t (R.sf t x))) /
        Real.cos (D.arclength t (R.sf t x)) ^ 3) := by
    have hcomp : Continuous (fun z : ℝ × ℝ => (z.1, R.sf z.1 z.2)) :=
      continuous_fst.prodMk hsfC
    have hk := S.curvature_smooth.continuous.comp hcomp
    have hd := D.contDiff_infty_arclength.continuous.comp hcomp
    exact (hk.sub (Real.continuous_sin.comp hd)).div
      ((Real.continuous_cos.comp hd).pow 3)
      (fun z => pow_ne_zero 3 (hcos z.1 (R.sf z.1 z.2)))
  have hangSpatial : ∀ t x, HasDerivAt
      (partialTime (nextAngle D R.sf) t)
      (partialTime (nextCurvature D R.sf) t x) x := by
    intro t x
    exact SelInvFrontMotionC2.hasDerivAt_partialTime_arc
      (contDiff_infty.mp R.angle_smooth 2) R.angle_deriv t x
  have hmixed : ∀ t x, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp
        (Complex.I * (nextAngle D R.sf r x : ℂ))) W t ∧
      HasDerivAt (fun y =>
        (frameTangential (partialTime (nextFront D R.sf))
            (nextAngle D R.sf) t y : ℂ) *
            Complex.exp (Complex.I * (nextAngle D R.sf t y : ℂ)) +
          (frameNormal (partialTime (nextFront D R.sf))
            (nextAngle D R.sf) t y : ℂ) *
            (Complex.I * Complex.exp
              (Complex.I * (nextAngle D R.sf t y : ℂ)))) W x := by
    exact SelectedRearGaugeQualitative.exists_mixed_frame_witness
      (contDiff_infty.mp R.front_smooth 2)
      (RearOwnHigherRegularity.contDiff_partialTime_self
        (contDiff_infty.mp R.front_smooth 2))
      (RearOwnTangential.contDiff_expI
        (contDiff_infty.mp R.angle_smooth 1))
      (fun t x => by
        exact RearOwnArclength.hasDerivAt_rearOwn_space
          hcore.front_frenet hcore.angle_frenet
          R.steering_deriv R.sf_deriv hcos t x)
      R.front_time_deriv
  exact ⟨{
    etaF := etaF
    Kx := fun _ => kx0
    Dd := fun t => dd * dens t
    gS := gS
    m := dens
    kx := kx0
    d := dd
    rear_period_pos := hrearPos
    rear_period_le := hrearLe
    tangential_zero := M.tangential_zero
    jacobi := hjac
    marking := M.marking
    etaF_bound := hetaBd
    rearKappa1_le := M.rearKappa1_le
    angleTime_spatial := hangSpatial
    mixed_derivative := hmixed
    Kx_bound := hKx
    Kx_nonnegative := fun _ => hkx0
    Kx_le := fun _ => le_rfl
    Kx_continuous := hKxC
    gS_deriv := hsourceD
    gS_bound := hgS
    Dd_le := fun _ => le_rfl
    density_continuous := Delta.cont_m.div_const _
    density_nonnegative := fun t => div_nonneg (Delta.m_nonneg t) hsqrtPos.le
    density_support := fun t ht => by simp [dens, successorDensity, Delta.m_stop t ht]
    density_domination := fun _ => le_rfl
    numerical_A := M.numerical_A
    numerical_K := M.numerical_K
  }⟩

/-- Produce the next finite source directly from the all-order source and the
correlated/scalar majorants. -/
theorem exists_markingAwareSuccessorSource_of_majorants
    {p q a b : Data} {Gamma : NormalPath p q} {Delta : NormalPath a b}
    {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {S : SmoothSource A periodLower kap}
    {D : NormalizedSteering S} {R : SuccessorRegularity D}
    (M : MarkingAwareFiniteSourceMajorants Delta R khatNext QmaxNext) :
    Nonempty (MarkingAwareSource Delta periodLower kap khatNext QmaxNext) := by
  obtain ⟨B⟩ := exists_markingAwareFiniteSourceResidual_of_majorants M
  exact ⟨B.toSource⟩

end FiniteSmoothRearFamilyMarkingAwareSmoothSource
