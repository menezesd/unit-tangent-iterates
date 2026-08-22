import Mathlib
import UnitTangentIterates.BarrierEstimates
import UnitTangentIterates.HairpinOn

/-!
# The translating hairpin

This file is the capstone of Section 3 of *A Noncircular Oval with Convex
Unit-Tangent Iterates*.  Combining

* `BarrierEstimates.exists_hairpin_profile` — the monotone iteration of the
  translator operator, started at the explicit lower barrier, converges to a
  profile between the two barriers which solves the translator integral
  equation on `(0, π)` (this uses the verification of the explicit barriers,
  hence holds unconditionally for `0 < ε ≤ 1/10`), and
* `HairpinOn.isHairpin_of_continuousOn` — a profile continuous on `(0, π)` and
  pinched between two positive constants defines a complete embedded strictly
  convex hairpin,

gives the geometric statement of the theorem *Translating hairpin*:

`exists_translating_hairpin` — for every `0 < ε ≤ 1/10` there is a profile
`f_ε` with `f_ε^- ≤ f_ε ≤ f_ε^+`, continuous on `(0, π)`, which satisfies the
translator integral equation `∫_θ^{g(θ)} f = sin θ` with
`g(θ) = θ + arctan(sin θ / f(θ))`, and whose curve `X' = f cot θ`, `Z' = f` is
a complete embedded strictly convex hairpin of finite vertical width whose two
ends run off to horizontal infinity on the same side.

The translation law itself (`𝒯C = C + (V, 0)` with `V > 0`) is proved, for this
profile, in `TranslatorTranslation.lean`, where the smoothness of the profile is
also established.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace TranslatingHairpin

/-- **The translating hairpin exists.**  For `0 < ε ≤ 1/10` there is a profile
`f` between the explicit barriers, continuous on `(0, π)`, satisfying the
translator integral equation `∫_θ^{θ + arctan(sin θ / f θ)} f = sin θ`, whose
curve is regular with velocity `(f/sin θ)e^{iθ}` (so its tangent angle is the
parameter and the tangent turns through `π`), embedded, strictly convex, of
vertical width at most `Mπ`, with both ends running off to `X = -∞` and
infinite arclength. -/
theorem exists_translating_hairpin {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    ∃ f : ℝ → ℝ,
      (∀ t, Barriers.fMinus ε t ≤ f t) ∧ (∀ t, f t ≤ Barriers.fPlus ε t) ∧
      ContinuousOn f (Ioo 0 π) ∧
      (∀ θ ∈ Ioo (0:ℝ) π, (∫ t in θ..(Translator.next f θ), f t) = Real.sin θ) ∧
      ((∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt (Hairpin.hairpinCurve f)
          ((f θ / Real.sin θ : ℝ) * Complex.exp (Complex.I * (θ : ℂ))) θ ∧
          0 < f θ / Real.sin θ) ∧
        InjOn (Hairpin.hairpinCurve f) (Ioo 0 π) ∧
        (∀ θ ∈ Ioo (0:ℝ) π, 0 < Real.sin θ / f θ) ∧
        (∀ θ ∈ Ioo (0:ℝ) π, |Hairpin.hairpinZ f θ| ≤ (ε⁻¹ + 4 / 3 + 3 * ε) * π) ∧
        Tendsto (Hairpin.hairpinX f) (𝓝[>] (0:ℝ)) atBot ∧
        Tendsto (fun θ => Hairpin.hairpinX f (π - θ)) (𝓝[>] (0:ℝ)) atBot ∧
        Tendsto (fun θ => Hairpin.hairpinArclength f θ 1) (𝓝[>] (0:ℝ)) atTop ∧
        Tendsto (fun θ => Hairpin.hairpinArclength f (π - 1) (π - θ))
          (𝓝[>] (0:ℝ)) atTop ∧
        Tendsto (Hairpin.hairpinZ f) (𝓝[>] (0:ℝ)) (𝓝 (Hairpin.hairpinZ f 0)) ∧
        Tendsto (Hairpin.hairpinZ f) (𝓝[<] π) (𝓝 (Hairpin.hairpinZ f π))) := by
  obtain ⟨f, hmeas, hfl, hfu, hcont, -, hint, harctan, -⟩ :=
    BarrierEstimates.exists_hairpin_profile hε hε'
  have hm1 : 1 < ε⁻¹ - ε := BarrierEstimates.m_gt_one hε hε'
  have hlow : ∀ t, ε⁻¹ - ε ≤ f t := fun t =>
    le_trans ((Barriers.fMinus_min hε).1 t) (hfl t)
  have hup : ∀ t, f t ≤ ε⁻¹ + 4 / 3 + 3 * ε := fun t =>
    le_trans (hfu t) ((BarrierEstimates.profile_fPlus hε).upper t)
  refine ⟨f, hfl, hfu, hcont, ?_, ?_⟩
  · intro θ hθ
    have hnext : Translator.next f θ = θ + TranslatorOperator.shift f θ := by
      rw [Translator.next, Translator.steer, harctan θ hθ]
    rw [hnext]
    exact hint θ hθ
  · have hmain := HairpinOn.isHairpin_of_continuousOn hcont (lt_trans zero_lt_one hm1)
      (fun t _ => hlow t) (fun t _ => hup t)
    have hprof : TranslatorOperator.Profile (ε⁻¹ - ε) (ε⁻¹ + 4 / 3 + 3 * ε) f :=
      ⟨hmeas, hlow, hup⟩
    have hends := HairpinOn.tendsto_hairpinZ_ends (f := f) hprof.int
    exact ⟨hmain.1, hmain.2.1, hmain.2.2.1, hmain.2.2.2.1, hmain.2.2.2.2.1,
      hmain.2.2.2.2.2.1, hmain.2.2.2.2.2.2.1, hmain.2.2.2.2.2.2.2, hends.1, hends.2⟩

end TranslatingHairpin
