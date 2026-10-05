module

public import UnitTangentIterates.Resolvent

/-!
# `L¹` bounds for the periodic resolvent (Lemma 6.2, estimates (6.3) and (6.4))

In Lemma 6.2 the rear normal velocity is `η_R = ℛ_ℓ (sec δ · η_F ∘ s)`, where
`(ℛ_ℓ f)(x) = (1 - e^{-ℓ})⁻¹ ∫_{x-ℓ}^x e^{-(x-t)} f(t) dt` inverts `1 + ∂_x` on `ℝ/ℓℤ`.
The two analytic facts used are:

* `ℛ_ℓ` does not increase the `L¹` norm over a period (this gives `W(ℬΓ) ≤ W(Γ)`);
* `ℛ_ℓ` maps `L¹` to `L^∞` with norm at most `(1 - e^{-ℓ})⁻¹` (this gives `S₀ ≤ C₀ W`).
-/

@[expose] public section

namespace Ovals

open Real intervalIntegral MeasureTheory

variable {L : ℝ}

lemma continuous_exp_kernel_mul {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Continuous (fun t => Real.exp (t - x) * f t) :=
  (Real.continuous_exp.comp (continuous_id.sub continuous_const)).mul hf

/-- Pointwise domination `|ℛ_L f| ≤ ℛ_L |f|`. -/
theorem abs_periodicResolvent_le (hL : 0 < L) (f : ℝ → ℝ) (x : ℝ) :
    |periodicResolvent L f x| ≤ periodicResolvent L (fun t => |f t|) x := by
  unfold periodicResolvent
  rw [abs_mul, abs_of_pos (inv_pos.2 (one_sub_exp_neg_pos hL))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (one_sub_exp_neg_pos hL).le)
  refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans (le_of_eq ?_)
  congr 1; ext t
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]

/-- **`L¹ → L^∞` bound.**  For a continuous `L`-periodic `f`,
`|ℛ_L f(x)| ≤ (1 - e^{-L})⁻¹ ∫₀ᴸ |f|`. -/
theorem abs_periodicResolvent_le_integral (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f)
    (hfp : Function.Periodic f L) (x : ℝ) :
    |periodicResolvent L f x| ≤ (1 - Real.exp (-L))⁻¹ * ∫ t in (0 : ℝ)..L, |f t| := by
  refine (abs_periodicResolvent_le hL f x).trans ?_
  unfold periodicResolvent
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (one_sub_exp_neg_pos hL).le)
  have hfa : Function.Periodic (fun t => |f t|) L := fun t => by simp only [hfp t]
  have hshift : ∫ t in (x - L)..x, |f t| = ∫ t in (0:ℝ)..L, |f t| := by
    have := hfa.intervalIntegral_add_eq (x - L) 0
    simpa using this
  rw [← hshift]
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (continuous_exp_kernel_mul hf.abs x).intervalIntegrable _ _
  · exact hf.abs.intervalIntegrable _ _
  · intro t ht
    have : Real.exp (t - x) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith [ht.2]
    nlinarith [abs_nonneg (f t), Real.exp_pos (t - x)]

/-- The resolvent preserves the mean: `∫₀ᴸ ℛ_L g = ∫₀ᴸ g`. -/
theorem integral_periodicResolvent (hL : 0 < L) {g : ℝ → ℝ} (hg : Continuous g)
    (hgp : Function.Periodic g L) :
    ∫ x in (0 : ℝ)..L, periodicResolvent L g x = ∫ x in (0 : ℝ)..L, g x := by
  have hu := hasDerivAt_periodicResolvent hL hg hgp
  have hc := continuous_periodicResolvent hL hg hgp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := L) (fun x _ => hu x)
    ((hg.sub hc).intervalIntegrable _ _)
  have hp := periodicResolvent_periodic hgp 0
  rw [zero_add] at hp
  rw [hp, sub_self,
    intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hc.intervalIntegrable _ _)] at h
  linarith

/-- **`L¹` contraction.**  For a continuous `L`-periodic `f`,
`∫₀ᴸ |ℛ_L f| ≤ ∫₀ᴸ |f|`. -/
theorem integral_abs_periodicResolvent_le (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f)
    (hfp : Function.Periodic f L) :
    ∫ x in (0 : ℝ)..L, |periodicResolvent L f x| ≤ ∫ x in (0 : ℝ)..L, |f x| := by
  have hfa : Function.Periodic (fun t => |f t|) L := fun t => by simp only [hfp t]
  rw [← integral_periodicResolvent hL hf.abs hfa]
  apply intervalIntegral.integral_mono_on hL.le
  · exact (continuous_periodicResolvent hL hf hfp).abs.intervalIntegrable _ _
  · exact (continuous_periodicResolvent hL hf.abs hfa).intervalIntegrable _ _
  · exact fun x _ => abs_periodicResolvent_le hL f x

end Ovals

end
