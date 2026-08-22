import Mathlib
import UnitTangentIterates.RearOwnPathDistFrameDrift

/-!
# The path pseudodistance of the selected rears, with explicit constants

`RearOwnPathDistFrameDrift.pathDist_le_of_front_frame_variable` produces the
gauge frame bundle by a compactness argument over the time window of the path,
so the two constants of the bound come out *existentially*, and they depend on
the path.  That is enough for a single path, but not for a Lipschitz bound,
which needs one constant valid for every path at once.

Here the two constants are prescribed instead: the caller supplies bounds `rL`
and `rB` for the first two arclength derivatives of the tangential component of
the motion, and the bound is stated with exactly those constants.  Nothing else
about the family is used — in particular it is not asked to be at rest outside
the window in order to build the bundle, only for the normal path itself.

Main results: `pathDist_le_of_front_frame_bounds`, and the Lipschitz bound
`pathDist_le_of_front_unitTime` it feeds.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistFrameBounds

open UniformFrameBounds GaugePathDistVariable RearOwnPathDist RearOwnFrameDrift

/-- **The path pseudodistance of the selected rears of a path of fronts, with
the two gauge constants prescribed.**

The hypotheses are those of
`RearOwnPathDistFrameDrift.pathDist_le_of_front_frame_variable`, except that the
two conditions making the family frozen outside the time window are replaced by
explicit bounds `rL`, `rB` for the two arclength derivatives of the tangential
component `⟨Ẏ, e^{iΨ}⟩` of the motion.  The conclusion carries those two
constants, so it is uniform over any family of paths for which they hold. -/
theorem pathDist_le_of_front_frame_bounds {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh rL rB : ℝ} {P Qf' : ℝ → ℝ}
    {F Fdot Fdots Ydot : ℝ → ℝ → ℂ}
    {Θ δ K etaF etaFs sf sft dt Θdot w Θdots ws : ℝ → ℝ → ℝ}
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
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ))
    (hδt : ∀ t s, HasDerivAt (fun r => δ r s) (dt t s) t)
    (hdtc : Continuous (uncurry dt))
    (hetaFdef : ∀ t s, etaF t s = frontNormalVelocityAt Fdot Θ δ t s)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t)
    (hFa : ∀ t s, HasDerivAt (fun r => F r s) (Fdot t s) t)
    (hΘa : ∀ t s, HasDerivAt (fun r => Θ r s) (Θdot t s) t)
    (hδa : ∀ t s, HasDerivAt (fun r => δ r s) (w t s) t)
    (hFdots : ∀ t s, HasDerivAt (Fdot t) (Fdots t s) s)
    (hΘdots : ∀ t s, HasDerivAt (Θdot t) (Θdots t s) s)
    (hws : ∀ t s, HasDerivAt (w t) (ws t s) s)
    (hFc2 : ContDiff ℝ (2 : ℕ) (uncurry F)) (hΘc2 : ContDiff ℝ (2 : ℕ) (uncurry Θ))
    (hδc2 : ContDiff ℝ (2 : ℕ) (uncurry δ))
    (hYdot : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    -- the rear period moves differentiably
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    -- the regularity of the velocity and of the rear tangent angle
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    -- the prescribed bounds on the arclength derivatives of the tangential component
    (hrL : ∀ t x, |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x| ≤ rL)
    (hrB : ∀ t x,
      |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x| ≤ rB)
    -- the family is at rest outside the time window of the path
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      ((∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0) → ∀ t, Phi t 0 = 0) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh rL rB Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  obtain ⟨D, hv1, hxiD, hDL, hDB⟩ :=
    exists_gaugeFrameData_frameTangential_of_bounds hYdotC hangC hrL hrB
  have h := pathDist_le_of_front_smoothDependence Γ p'
    (Fdot := Fdot) (Fdots := Fdots) (Ydot := Ydot) (Qf' := Qf')
    (Θdot := Θdot) (w := w) (Θdots := Θdots) (ws := ws) (dt := dt) (sft := sft)
    (K := K) (etaF := etaF) (etaFs := etaFs)
    D hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot hv1 hxiD hrest hQd hstart
  rw [hDL, hDB] at h
  exact h

/-! ### The Lipschitz bound over all the paths -/

/-- **A bound valid on every normal path of duration one is a Lipschitz bound.**

If a fixed pair of marked curves is at pseudodistance at most `C` times the cost
of *every* normal path of duration one from `p` to `q`, then it is at
pseudodistance at most `C` times `pathDist p q`: by
`PathMetric.pathDist_eq_sInf_unitTime` the pseudodistance is already the infimum
of those costs. -/
theorem pathDist_le_mul_of_unitTime_costs {p q p' q' : Data} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 → pathDist p' q' ≤ C * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist p' q' ≤ C * pathDist p q := by
  obtain ⟨Γ₀⟩ := hne
  obtain ⟨Δ₀, hT₀, -⟩ := Γ₀.exists_unitTime_normalPath
  have hSne : (unitTimeCostSet p q).Nonempty := ⟨cost Δ₀, ⟨Δ₀, hT₀, rfl⟩⟩
  rw [pathDist_eq_sInf_unitTime p q]
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · have h0 : pathDist p' q' ≤ 0 := by
      have := h Δ₀ hT₀
      rwa [← hC0, zero_mul] at this
    calc pathDist p' q' ≤ 0 := h0
      _ = C * sInf (unitTimeCostSet p q) := by rw [← hC0, zero_mul]
  · have key : pathDist p' q' / C ≤ sInf (unitTimeCostSet p q) := by
      refine le_csInf hSne (fun c hc => ?_)
      obtain ⟨Γ, hT, hcost⟩ := hc
      rw [div_le_iff₀ hCpos, mul_comm, ← hcost]
      exact h Γ hT
    calc pathDist p' q' = C * (pathDist p' q' / C) := by field_simp
      _ ≤ C * sInf (unitTimeCostSet p q) := by
          exact mul_le_mul_of_nonneg_left key hCpos.le

/-- **The uniform Lipschitz bound for a map of marked curves, from the front
data.**

Combined with `pathDist_le_of_front_frame_bounds`, whose constants do not depend
on the path, this turns the single-path bound into a Lipschitz bound for a map
`F` of marked curves: it is enough that for every normal path of duration one
from `p` to `q` the images `F p` and `F q` be at pseudodistance at most the
gauge constant times the cost of the path. -/
theorem pathDist_le_of_front_unitTime {F : Data → Data} {p q : Data}
    {P0 P1 kh rL rB Q : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hQ : 0 < Q) (hrB : 0 ≤ rB)
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 →
      pathDist (F p) (F q) ≤ gaugeJacobiConst P0 P1 kh rL rB 1 Q * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤ gaugeJacobiConst P0 P1 kh rL rB 1 Q * pathDist p q :=
  pathDist_le_mul_of_unitTime_costs
    (gaugeJacobiConst_nonneg hP0 hP1 hkh0 hkh1 hQ hrB zero_le_one) h hne

end RearOwnPathDistFrameBounds
