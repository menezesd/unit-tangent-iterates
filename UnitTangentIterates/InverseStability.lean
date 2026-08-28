import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.RearDriftBound

/-!
# Stability of the rear-arclength inverse in the steering angle
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real ArclengthInverse RearTrack

namespace ArclengthInverse

/-- A slope bound below gives a two-sided separation bound. -/
theorem mul_abs_sub_le_abs_sub {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ s, HasDerivAt f (g s) s) (hg : ∀ s, c ≤ g s) (a b : ℝ) :
    c * |a - b| ≤ |f a - f b| := by
  have hmono : StrictMono f := strictMono_of_deriv_ge hc hf hg
  rcases le_total a b with h | h
  · have hgap : f b - f a ≥ c * (b - a) := by
      have hshift : ∀ s, HasDerivAt (fun y => f (y + a)) (g (s + a)) s := by
        intro s
        simpa [Function.comp] using (hf (s + a)).scomp s ((hasDerivAt_id s).add_const a)
      have h0 := le_of_deriv_ge hshift (fun s => hg (s + a)) (s := b - a) (by linarith)
      simp only [zero_add, sub_add_cancel] at h0
      linarith
    have hfab : f a ≤ f b := hmono.monotone h
    rw [abs_of_nonpos (by linarith : a - b ≤ 0),
      abs_of_nonpos (by linarith : f a - f b ≤ 0)]
    linarith
  · have hgap : f a - f b ≥ c * (a - b) := by
      have hshift : ∀ s, HasDerivAt (fun y => f (y + b)) (g (s + b)) s := by
        intro s
        simpa [Function.comp] using (hf (s + b)).scomp s ((hasDerivAt_id s).add_const b)
      have h0 := le_of_deriv_ge hshift (fun s => hg (s + b)) (s := a - b) (by linarith)
      simp only [zero_add, sub_add_cancel] at h0
      linarith
    have hfab : f b ≤ f a := hmono.monotone h
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ f a - f b)]
    linarith

/-- **Stability of the rear arclength in the steering angle.**  Two steering
angles differing by at most `e` have rear arclengths differing by at most
`|x| * e`, because `|cos a - cos b| <= |a - b|`. -/
theorem abs_rearArclength_sub_le {d1 d2 : ℝ → ℝ} {e : ℝ}
    (hd1 : Continuous d1) (hd2 : Continuous d2) (he : ∀ s, |d1 s - d2 s| ≤ e)
    (x : ℝ) : |rearArclength d1 x - rearArclength d2 x| ≤ |x| * e := by
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) (he 0)
  have hi1 : IntervalIntegrable (fun u => Real.cos (d1 u)) MeasureTheory.volume 0 x :=
    (Real.continuous_cos.comp hd1).intervalIntegrable 0 x
  have hi2 : IntervalIntegrable (fun u => Real.cos (d2 u)) MeasureTheory.volume 0 x :=
    (Real.continuous_cos.comp hd2).intervalIntegrable 0 x
  have hsub : rearArclength d1 x - rearArclength d2 x
      = ∫ u in (0:ℝ)..x, (Real.cos (d1 u) - Real.cos (d2 u)) := by
    rw [rearArclength, rearArclength, intervalIntegral.integral_sub hi1 hi2]
  rw [hsub]
  have hbd : ∀ u, |Real.cos (d1 u) - Real.cos (d2 u)| ≤ e :=
    fun u => le_trans (Real.abs_cos_sub_cos_le _ _) (he u)
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := x) (C := e)
    (fun u _ => by rw [Real.norm_eq_abs]; exact hbd u)
  rw [mul_comm]
  simpa [Real.norm_eq_abs] using this

/-- **Stability of the rear-arclength inverse.**  If two steering angles differ
by at most `e` on the line, their rear-arclength right inverses differ at `x` by
at most `|sf₂ x| * e / c`, where `c` is the common slope floor `cos delta >= c`.

This is the pointwise half of the "variable-period passage" the manifest asks
for.  It is the estimate that must be upgraded to uniformity on compacts before
`ContDiff ℝ 1 (uncurry sf)` — the single remaining blocker of the rear-family
constructor's hypothesis list — can be concluded. -/
theorem abs_sf_sub_le {d1 d2 sf1 sf2 : ℝ → ℝ} {c e : ℝ} (hc : 0 < c)
    (hd1 : Continuous d1) (hd2 : Continuous d2)
    (hcos1 : ∀ s, c ≤ Real.cos (d1 s))
    (hsf1 : ∀ x, rearArclength d1 (sf1 x) = x)
    (hsf2 : ∀ x, rearArclength d2 (sf2 x) = x)
    (he : ∀ s, |d1 s - d2 s| ≤ e) (x : ℝ) :
    |sf1 x - sf2 x| ≤ |sf2 x| * e / c := by
  have hderiv1 : ∀ s, HasDerivAt (rearArclength d1) (Real.cos (d1 s)) s :=
    fun s => hasDerivAt_rearArclength hd1 s
  have hsep := mul_abs_sub_le_abs_sub hc hderiv1 hcos1 (sf1 x) (sf2 x)
  have hval : rearArclength d1 (sf1 x) - rearArclength d1 (sf2 x)
      = rearArclength d2 (sf2 x) - rearArclength d1 (sf2 x) := by
    rw [hsf1 x, hsf2 x]
  rw [hval] at hsep
  have hstab : |rearArclength d2 (sf2 x) - rearArclength d1 (sf2 x)| ≤ |sf2 x| * e := by
    rw [abs_sub_comm]
    exact abs_rearArclength_sub_le hd1 hd2 he (sf2 x)
  rw [le_div_iff₀ hc, mul_comm]
  exact le_trans hsep hstab

end ArclengthInverse
