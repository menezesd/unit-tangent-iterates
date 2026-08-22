import Mathlib
import UnitTangentIterates.RearOwnPathDistCurvature
import UnitTangentIterates.RearPeriodDeriv
import UnitTangentIterates.SelectedChangeOfVariable

/-!
# The path pseudodistance of the selected rears: the last auxiliary data removed

`RearOwnPathDistCurvature.pathDist_le_of_front_curvature` states the bound for
the selected rears of a normal path of fronts with every *regularity*
hypothesis on the front curvature.  It still carries three pieces of auxiliary
information that are not data of the front but consequences of it:

* the periodicity of the front normal velocity `η_F(t, ·)` with the front
  period `P t`;
* a sup bound `E_F` for `η_F`;
* the derivative `Q'(t)` of the rear arclength period
  `Q t = ∫₀^{P t} cos δ(t, s) ds`.

All three are produced here.

* `periodic_frontNormalVelocityAt` — differentiating the closing relation
  `F(t, s + P t) = F(t, s)` in the time gives
  `Ḟ(t, s + P t) = Ḟ(t, s) − P'(t) e^{iΘ(t,s)}`, and the extra term is
  *tangential*, so it does not change the normal component: `η_F(t, ·)` is
  `P t`-periodic whatever the motion of the period.
* `exists_bound_of_periodic_rest` — a jointly continuous velocity which is
  periodic in the arclength with a bounded period and vanishes outside the time
  window of the path is bounded, by compactness of `[0,T] × [0,P₁]`.
* `exists_hasDerivAt_rearPeriod` — the rear period is differentiable, by the
  Leibniz rule with a moving endpoint of `RearPeriodDeriv`, the steering angle
  being Lipschitz in the path parameter and differentiable under the integral
  sign.

The resulting statement, `pathDist_le_of_front_intrinsic`, asks nothing of the
front beyond its geometry, its regularity and its coming to rest outside the
time window; the sup bound of the normal velocity, which the constant of the
bound depends on, is produced with it.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistIntrinsic

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE

variable {F : ℝ → ℝ → ℂ} {Θ δ : ℝ → ℝ → ℝ} {P : ℝ → ℝ}

/-! ### Periodicity of the front normal velocity -/

/-- The chain rule for a jointly differentiable family evaluated at a moving
point `φ(t)`. -/
theorem hasDerivAt_moving_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ → E} (hf : Differentiable ℝ (uncurry f))
    {phi : ℝ → ℝ} {phi' t : ℝ} (hphi : HasDerivAt phi phi' t) :
    HasDerivAt (fun r => f r (phi r))
      (partialTime f t (phi t) + phi' • partialArc f t (phi t)) t := by
  have hcurve : HasDerivAt (fun r : ℝ => ((r, phi r) : ℝ × ℝ)) ((1, phi') : ℝ × ℝ) t :=
    (hasDerivAt_id t).prodMk hphi
  have hcomp := ((hf (t, phi t)).hasFDerivAt).comp_hasDerivAt t hcurve
  have hsplit : ((1, phi') : ℝ × ℝ) = (1, 0) + phi' • (0, 1) := by
    simp
  have := hcomp
  rw [hsplit, map_add, map_smul] at this
  simpa [partialTime, partialArc] using this

/-- The chain rule for the front evaluated at a moving point `φ(t)`. -/
theorem hasDerivAt_front_moving (hFdiff : Differentiable ℝ (uncurry F))
    {phi : ℝ → ℝ} {phi' t : ℝ} (hphi : HasDerivAt phi phi' t) :
    HasDerivAt (fun r => F r (phi r))
      (partialTime F t (phi t) + phi' • partialArc F t (phi t)) t :=
  hasDerivAt_moving_point hFdiff hphi

/-- The chain rule for the front evaluated at a moving point `s + P(t)`. -/
theorem hasDerivAt_front_shifted (hFdiff : Differentiable ℝ (uncurry F))
    {P' t : ℝ} (hP : HasDerivAt P P' t) (s : ℝ) :
    HasDerivAt (fun r => F r (s + P r))
      (partialTime F t (s + P t) + P' • partialArc F t (s + P t)) t :=
  hasDerivAt_front_moving hFdiff (hP.const_add s)

/-- **The time derivative of the front picks up a tangential term across the
period.**  Differentiating the closing relation `F(t, s + P t) = F(t, s)` gives
`Ḟ(t, s + P t) = Ḟ(t, s) − P'(t) e^{iΘ(t,s)}`. -/
theorem partialTime_shift (hFdiff : Differentiable ℝ (uncurry F))
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hFper : ∀ t s, F t (s + P t) = F t s)
    {P' t : ℝ} (hP : HasDerivAt P P' t) (s : ℝ) :
    partialTime F t (s + P t)
      = partialTime F t s - (P' : ℂ) * Complex.exp (Complex.I * (Θ t (s + P t) : ℂ)) := by
  have harc : partialArc F t (s + P t) = Complex.exp (Complex.I * (Θ t (s + P t) : ℂ)) :=
    ((hasDerivAt_partialArc hFdiff t (s + P t)).unique (hF t (s + P t)))
  have h1 := hasDerivAt_front_shifted (F := F) hFdiff hP s
  have h2 : HasDerivAt (fun r => F r (s + P r)) (partialTime F t s) t := by
    have hfun : (fun r => F r (s + P r)) = fun r => F r s := by
      funext r; exact hFper r s
    rw [hfun]
    exact hasDerivAt_partialTime hFdiff t s
  have := h1.unique h2
  rw [harc] at this
  have hsm : (P' • Complex.exp (Complex.I * (Θ t (s + P t) : ℂ)))
      = (P' : ℂ) * Complex.exp (Complex.I * (Θ t (s + P t) : ℂ)) := by
    simp [Complex.real_smul]
  rw [hsm] at this
  linear_combination this

/-- **The front normal velocity is periodic with the front period**, whatever
the motion of that period: the term the moving period contributes is
tangential. -/
theorem periodic_frontNormalVelocityAt (hFdiff : Differentiable ℝ (uncurry F))
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hPdiff : Differentiable ℝ P) (t : ℝ) :
    Function.Periodic (frontNormalVelocityAt (partialTime F) Θ δ t) (P t) := by
  intro s
  have hexp : Complex.exp (Complex.I * (Θ t (s + P t) : ℂ))
      = Complex.exp (Complex.I * (Θ t s : ℂ)) := by
    rw [hΘper t s]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
      have h := Complex.exp_two_pi_mul_I
      calc Complex.exp (Complex.I * (2 * (Real.pi : ℂ)))
          = Complex.exp (2 * (Real.pi : ℂ) * Complex.I) := by ring_nf
        _ = 1 := h
    rw [this, mul_one]
  have hkey := partialTime_shift (F := F) (Θ := Θ) hFdiff hF hFper
    ((hPdiff t).hasDerivAt) s
  rw [hexp] at hkey
  set e : ℂ := Complex.exp (Complex.I * (Θ t s : ℂ)) with he
  have hconj : e * (starRingEnd ℂ) e = 1 := by
    rw [he, ← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_I]
  simp only [frontNormalVelocityAt, frontNormalVelocity, rearAngle, sub_add_cancel]
  rw [hkey]
  have hang : Complex.exp (Complex.I * ((Θ t (s + P t) : ℝ) : ℂ)) = e := hexp
  rw [hang]
  have hexpand : (partialTime F t s - ((deriv P t : ℝ) : ℂ) * e)
      * (starRingEnd ℂ) (Complex.I * e)
      = partialTime F t s * (starRingEnd ℂ) (Complex.I * e)
        + ((deriv P t : ℝ) : ℂ) * Complex.I * (e * (starRingEnd ℂ) e) := by
    rw [map_mul, Complex.conj_I]
    ring
  rw [hexpand, hconj, ← he]
  simp

/-! ### A sup bound for a velocity at rest outside the time window -/

/-- **A jointly continuous velocity, periodic in the arclength with a bounded
period and at rest outside the time window, is bounded.** -/
theorem exists_bound_of_periodic_rest {eta : ℝ → ℝ → ℝ} {T P1 : ℝ}
    (hc : Continuous (uncurry eta)) (hT : 0 < T)
    (hPpos : ∀ t, 0 < P t) (hPu : ∀ t, P t ≤ P1)
    (hper : ∀ t, Function.Periodic (eta t) (P t))
    (hrest : ∀ t ∉ Ioo (0 : ℝ) T, ∀ s, eta t s = 0) :
    ∃ EF : ℝ, 0 ≤ EF ∧ ∀ t s, |eta t s| ≤ EF := by
  have hP1 : 0 < P1 := lt_of_lt_of_le (hPpos 0) (hPu 0)
  set S : Set (ℝ × ℝ) := Icc (0 : ℝ) T ×ˢ Icc (0 : ℝ) P1 with hS
  have hScomp : IsCompact S := (isCompact_Icc).prod (isCompact_Icc)
  have hSne : S.Nonempty := ⟨(0, 0), ⟨⟨le_refl 0, hT.le⟩, ⟨le_refl 0, hP1.le⟩⟩⟩
  have hfc : Continuous fun p : ℝ × ℝ => |eta p.1 p.2| := hc.abs
  obtain ⟨x, hxS, hxmax⟩ := hScomp.exists_isMaxOn hSne hfc.continuousOn
  refine ⟨max 0 |eta x.1 x.2|, le_max_left _ _, ?_⟩
  intro t s
  by_cases ht : t ∈ Ioo (0 : ℝ) T
  · obtain ⟨y, hy, hval⟩ := (hper t).exists_mem_Ico₀ (hPpos t) s
    have hmem : (t, y) ∈ S := by
      refine ⟨⟨ht.1.le, ht.2.le⟩, ⟨hy.1, ?_⟩⟩
      exact le_trans hy.2.le (hPu t)
    have := hxmax hmem
    rw [hval]
    exact le_trans this (le_max_right _ _)
  · rw [hrest t ht s]
    simp

/-! ### The derivative of the rear arclength period -/

/-- **The rear arclength period is differentiable in the time.**  For a jointly
`C¹` family of steering angles which is Lipschitz in the path parameter,
uniformly in the arclength, and a differentiable front period, the rear period
`Q t = ∫₀^{P t} cos δ(t, s) ds` has a derivative at every time. -/
theorem exists_hasDerivAt_rearPeriod {L : ℝ}
    (hδdiff : Differentiable ℝ (uncurry δ))
    (hdtc : Continuous (uncurry (partialTime δ)))
    (hlipδ : ∀ a b s, |δ a s - δ b s| ≤ L * |a - b|)
    (hPdiff : Differentiable ℝ P) :
    ∃ Qf' : ℝ → ℝ, ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t := by
  have hδc : Continuous (uncurry δ) := hδdiff.continuous
  have hdt : ∀ t s, HasDerivAt (fun r => δ r s) (partialTime δ t s) t :=
    hasDerivAt_partialTime hδdiff
  refine ⟨fun t => Real.cos (δ t (P t)) * deriv P t
      + ∫ u in (0:ℝ)..(P t), SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t u, ?_⟩
  intro t
  have hlip : ∀ r s, |Real.cos (δ r s) - Real.cos (δ t s)| ≤ L * |r - t| := by
    intro r s
    have h1 : |Real.cos (δ r s) - Real.cos (δ t s)| ≤ |δ r s - δ t s| := by
      have := Real.lipschitzWith_cos.dist_le_mul (δ r s) (δ t s)
      simpa [Real.dist_eq] using this
    exact le_trans h1 (hlipδ r t s)
  have hparam : HasDerivAt (fun r => ∫ s in (0:ℝ)..(P t), Real.cos (δ r s))
      (∫ s in (0:ℝ)..(P t), SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t s) t :=
    SelectedChangeOfVariable.hasDerivAt_rearArclength_time hδc hdt hdtc t (P t)
  exact RearPeriodDeriv.hasDerivAt_rearPeriod (L := L)
    (fun r => hδc.comp (continuous_const.prodMk continuous_id)) hlip
    ((hPdiff t).hasDerivAt) hparam

/-! ### The path-metric bound with those three data produced -/

/-- **The path pseudodistance of the selected rears, with the periodicity, the
sup bound and the period derivative produced.**

Same statement as `RearOwnPathDistCurvature.pathDist_le_of_front_curvature`,
with the periodicity of the front normal velocity, its sup bound `E_F` and the
derivative of the rear arclength period all derived from the front data. -/
theorem pathDist_le_of_front_intrinsic {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh Md Klip CK : ℝ} {K Kd sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hKdbd : ∀ t s, |Kd t s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPC3 : ContDiff ℝ (3 : ℕ) P) (hKC3 : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKdC3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hlink : ∀ t u, Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u))
    (hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ EF : ℝ, 0 ≤ EF ∧
      (∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ EF) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
        ((∀ t, RearBaseDrift.frontBaseDrift (partialTime F) Θ δ t = 0) → ∀ t, Phi t 0 = 0) ∧
        ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
          pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
              (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
              ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                  * (kh / Real.sqrt (1 - kh ^ 2))
                + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hstrip : ∀ t s, δ t s ∈ Icc (0 : ℝ) (Real.arcsin kh) := fun t s =>
    ⟨hstrip0 t s, hstrip1 t s⟩
  have hδc4 : ContDiff ℝ (4 : ℕ) (uncurry δ) :=
    SteeringVariablePeriod.contDiff_four_uncurry_delta (K := K) (Kd := Kd) (Pf := P)
      (kap := kh) hkh0 hkh1 hPpos hsteer hstrip hdper hKdper hKdbd hKlip hKtaylor hCK
      hPC3 hKC3 hKdC3
  have hδdiff : Differentiable ℝ (uncurry δ) := hδc4.differentiable (by norm_num)
  have hFdiff : Differentiable ℝ (uncurry F) := hFc4.differentiable (by norm_num)
  have hPdiff : Differentiable ℝ P := hPC3.differentiable (by norm_num)
  -- the periodicity of the front normal velocity
  have hetaFper : ∀ t,
      Function.Periodic (frontNormalVelocityAt (partialTime F) Θ δ t) (P t) :=
    periodic_frontNormalVelocityAt (δ := δ) hFdiff hF hFper hΘper hPdiff
  -- its sup bound
  have hF4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry F) := by norm_num; exact_mod_cast hFc4
  have hle34 : ((3 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
  have hΘ3 : ContDiff ℝ (3 : ℕ) (uncurry Θ) := hΘc4.of_le hle34
  have hFdot3 : ContDiff ℝ (3 : ℕ) (uncurry (partialTime F)) := contDiff_partialTime_self hF4
  have hetaC3 : ContDiff ℝ (3 : ℕ)
      (uncurry (frontNormalVelocityAt (partialTime F) Θ δ)) :=
    contDiff_frontNormalVelocityAt hFdot3 hΘ3
  obtain ⟨EF, hEF0, hEF⟩ := exists_bound_of_periodic_rest (P := P)
    (eta := frontNormalVelocityAt (partialTime F) Θ δ) hetaC3.continuous Γ.T_pos
    hPpos hPu hetaFper hFrest
  -- the derivative of the rear period
  have hδ4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry δ) := by norm_num; exact_mod_cast hδc4
  have hdtc : Continuous (uncurry (partialTime δ)) :=
    (contDiff_partialTime_self hδ4).continuous
  have hKcont : Continuous (uncurry K) := hKC3.continuous
  have hlipδ : ∀ a b s, |δ a s - δ b s| ≤ (Klip / Real.sqrt (1 - kh ^ 2)) * |a - b| := by
    intro a b s
    have := SteeringVariablePeriod.abs_delta_sub_le (kap := kh) (K := K) (Klip := Klip)
      hkh0 hkh1 hKcont hsteer hstrip hKlip a b s
    calc |δ a s - δ b s| ≤ Klip * |a - b| / Real.sqrt (1 - kh ^ 2) := this
      _ = (Klip / Real.sqrt (1 - kh ^ 2)) * |a - b| := by ring
  obtain ⟨Qf', hQd⟩ := exists_hasDerivAt_rearPeriod (δ := δ) (P := P) hδdiff hdtc hlipδ hPdiff
  obtain ⟨Phi, hPhi0, hbase, hPhi⟩ :=
    RearOwnPathDistCurvature.pathDist_le_of_front_curvature Γ p' (Qf' := Qf') (EF := EF)
      hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper hFc4 hΘc4
      hKdper hKdbd hKlip hKtaylor hCK hPC3 hKC3 hKdC3 hsfinv hetaFper hlink hQd hEF hFrest
      hstart
  exact ⟨EF, hEF0, hEF, Phi, hPhi0, hbase, hPhi⟩

end RearOwnPathDistIntrinsic
