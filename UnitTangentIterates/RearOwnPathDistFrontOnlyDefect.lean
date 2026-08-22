import Mathlib
import UnitTangentIterates.RearOwnPathDistFrontOnly
import UnitTangentIterates.RearOwnPathDistSmoothDefect

/-!
# The path pseudodistance from the front curve alone, together with the defect of
its gauge marking

`RearOwnPathDistFrontOnly.pathDist_le_of_front_curve` takes as data only the
front, its tangent angle, its curvature, the selected steering angle, the front
period and the change of variable: every auxiliary velocity is the corresponding
canonical partial derivative.  This file restates it with the extra conclusions
about the gauge marking `Φ` in which the pseudodistance is read — `Φ` fixes the
base point, reads exactly one rear period, and deviates from the affine marking
of the terminal period by at most `2 P₁ κ̂/(1 − κ̂²) · cost Γ` — under the single
extra hypothesis that the base drift of the front vanishes.

Main result: `pathDist_and_defect_le_of_front_curve`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistFrontOnlyDefect

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity

/-- **The path pseudodistance of the selected rears from the front curve alone,
together with the defect of its gauge marking.**
`RearOwnPathDistFrontOnly.pathDist_le_of_front_curve` with the three extra
conclusions about the marking. -/
theorem pathDist_and_defect_le_of_front_curve {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh EF : ℝ} {P Qf' : ℝ → ℝ} {F : ℝ → ℝ → ℂ} {Θ δ K sf : ℝ → ℝ → ℝ}
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
    (hδc4 : ContDiff ℝ (4 : ℕ) (uncurry δ))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hetaFper : ∀ t,
      Function.Periodic (frontNormalVelocityAt (partialTime F) Θ δ t) (P t))
    (hlink : ∀ t u, Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u))
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hEF : ∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ EF)
    (hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    (hdrift : ∀ t, RearBaseDrift.frontBaseDrift (partialTime F) Θ δ t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
            (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
            ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                * (kh / Real.sqrt (1 - kh ^ 2))
              + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  -- the front data in the form the regularity lemmas expect
  have hF4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry F) := by norm_num; exact_mod_cast hFc4
  have hΘ4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry Θ) := by norm_num; exact_mod_cast hΘc4
  have hδ4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry δ) := by norm_num; exact_mod_cast hδc4
  have hle34 : ((3 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
  have hΘ3 : ContDiff ℝ (3 : ℕ) (uncurry Θ) := hΘc4.of_le hle34
  -- the parameter derivatives of the front data, and of the change of variable
  have hFdiff : Differentiable ℝ (uncurry F) := hFc4.differentiable (by norm_num)
  have hΘdiff : Differentiable ℝ (uncurry Θ) := hΘc4.differentiable (by norm_num)
  have hδdiff : Differentiable ℝ (uncurry δ) := hδc4.differentiable (by norm_num)
  have hFdot3 : ContDiff ℝ (3 : ℕ) (uncurry (partialTime F)) := contDiff_partialTime_self hF4
  have hΘdot3 : ContDiff ℝ (3 : ℕ) (uncurry (partialTime Θ)) := contDiff_partialTime_self hΘ4
  have hw3 : ContDiff ℝ (3 : ℕ) (uncurry (partialTime δ)) := contDiff_partialTime_self hδ4
  have hsfC4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry sf) :=
    contDiff_sf hkh0 hkh1 hδ4 hstrip0 hstrip1 hsfinv
  have hsfdiff : Differentiable ℝ (uncurry sf) := hsfC4.differentiable (by norm_num)
  -- the arclength derivatives of those parameter derivatives
  have hFdotdiff : Differentiable ℝ (uncurry (partialTime F)) := hFdot3.differentiable (by norm_num)
  have hΘdotdiff : Differentiable ℝ (uncurry (partialTime Θ)) := hΘdot3.differentiable (by norm_num)
  have hwdiff : Differentiable ℝ (uncurry (partialTime δ)) := hw3.differentiable (by norm_num)
  -- the front normal velocity
  have hetaC3 : ContDiff ℝ (3 : ℕ)
      (uncurry (frontNormalVelocityAt (partialTime F) Θ δ)) :=
    contDiff_frontNormalVelocityAt hFdot3 hΘ3
  have hetaC3' : ContDiff ℝ ((2 + 1 : ℕ))
      (uncurry (frontNormalVelocityAt (partialTime F) Θ δ)) := by
    norm_num; exact_mod_cast hetaC3
  have hetadiff : Differentiable ℝ (uncurry (frontNormalVelocityAt (partialTime F) Θ δ)) :=
    hetaC3.differentiable (by norm_num)
  have hetaFs2 : ContDiff ℝ (2 : ℕ)
      (uncurry (partialArc (frontNormalVelocityAt (partialTime F) Θ δ))) :=
    contDiff_partialArc_self hetaC3'
  exact RearOwnPathDistSmoothDefect.pathDist_and_defect_le_of_front_data Γ p'
    (Fdot := partialTime F) (Fdots := partialArc (partialTime F))
    (Ydot := fun t x =>
      trackVelocity (partialTime F) (partialTime Θ) (partialTime δ) Θ δ t (sf t x)
        + (partialTime sf t x) • ((Real.cos (δ t (sf t x)) : ℂ)
          * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (Θdot := partialTime Θ) (w := partialTime δ) (dt := partialTime δ) (sft := partialTime sf)
    (etaF := frontNormalVelocityAt (partialTime F) Θ δ)
    (etaFs := partialArc (frontNormalVelocityAt (partialTime F) Θ δ))
    (Θdots := partialArc (partialTime Θ)) (ws := partialArc (partialTime δ)) (K := K) (Qf' := Qf')
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    (hasDerivAt_partialTime hδdiff) hw3.continuous
    (fun t s => rfl) (hasDerivAt_partialArc hetadiff) (fun t =>
      hetaFs2.continuous.comp (continuous_const.prodMk continuous_id))
    hetaFper hlink hsfinv (hasDerivAt_partialTime hsfdiff)
    (hasDerivAt_partialTime hFdiff) (hasDerivAt_partialTime hΘdiff) (hasDerivAt_partialTime hδdiff)
    (hasDerivAt_partialArc hFdotdiff) (hasDerivAt_partialArc hΘdotdiff)
    (hasDerivAt_partialArc hwdiff)
    hFc4 hΘc4 hδc4 (fun t x => rfl) hQd hEF hFrest hstart hdrift

end RearOwnPathDistFrontOnlyDefect
