module

public import UnitTangentIterates.CurveFromCurvature
public import UnitTangentIterates.PeriodizationEstimates

/-!
# Width of a centrally symmetric curve built from its curvature (Lemma 4.4, geometric part)

Let `κ ≥ 0` be continuous and `L`-periodic with `∫₀ᴸ κ = π`, and let `X` be the centered curve
of curvature `κ` (equation (6.2)), with tangent angle `Θ`.  Rotate so that the tangent angle at
`s = -L/2` is horizontal: put `φ(s) = Θ(s) - Θ(-L/2)`.  The *width*

`W = ∫_{-L/2}^{L/2} sin φ(s) ds`

is the width of `X` in the direction `v = i τ(Θ(-L/2))` normal to that tangent: the whole curve
lies in the strip `-W/2 ≤ ⟨X, v⟩ ≤ W/2`.
-/

@[expose] public section

namespace Ovals

open Complex Real intervalIntegral MeasureTheory

/-- The width `W = ∫_{-L/2}^{L/2} sin (Θ(s) - Θ(-L/2)) ds` of the curve of curvature `κ`. -/
noncomputable def curveWidth (θ₀ : ℝ) (κ : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ s in (-L / 2)..(L / 2), Real.sin (angleOfCurvature θ₀ κ s - angleOfCurvature θ₀ κ (-L / 2))

variable {θ₀ L : ℝ} {κ : ℝ → ℝ}

/-- `Re (τ(a) · conj (i τ(b))) = sin (a - b)`. -/
lemma re_tau_mul_conj_I_tau (a b : ℝ) :
    (tau a * (starRingEnd ℂ) (I * tau b)).re = Real.sin (a - b) := by
  rw [tau_eq, tau_eq, Real.sin_sub]
  simp [Complex.mul_re, Complex.mul_im, -Complex.ofReal_sin, -Complex.ofReal_cos]

/-- The angle difference is the integral of the curvature. -/
lemma angleOfCurvature_sub (hκ : Continuous κ) (a b : ℝ) :
    angleOfCurvature θ₀ κ b - angleOfCurvature θ₀ κ a = ∫ r in a..b, κ r := by
  unfold angleOfCurvature
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := a) (c := b)
    (hκ.intervalIntegrable _ _) (hκ.intervalIntegrable _ _)]
  ring

/-- **The curve lies in a strip of width `W`.** -/
theorem curveOfCurvature_strip (hκ : Continuous κ) (hκ0 : ∀ s, 0 ≤ κ s)
    (hκp : Function.Periodic κ L) (hint : ∫ r in (0 : ℝ)..L, κ r = π) (hL : 0 < L) (s : ℝ) :
    -(curveWidth θ₀ κ L / 2) ≤
        (curveOfCurvature θ₀ κ L s * (starRingEnd ℂ) (I * tau (angleOfCurvature θ₀ κ (-L / 2)))).re ∧
      (curveOfCurvature θ₀ κ L s * (starRingEnd ℂ) (I * tau (angleOfCurvature θ₀ κ (-L / 2)))).re ≤
        curveWidth θ₀ κ L / 2 := by
  set Θ := angleOfCurvature θ₀ κ with hΘ
  set θ₁ := Θ (-L / 2)
  set v := I * tau θ₁
  set p : ℝ → ℝ := fun s => (curveOfCurvature θ₀ κ L s * (starRingEnd ℂ) v).re with hp
  set W := curveWidth θ₀ κ L
  have hΘc : Continuous Θ := continuous_angleOfCurvature hκ
  have hsc : Continuous (fun s => Real.sin (Θ s - θ₁)) :=
    Real.continuous_sin.comp (hΘc.sub continuous_const)
  have hpd : ∀ s, HasDerivAt p (Real.sin (Θ s - θ₁)) s := by
    intro s
    have h := ((hasDerivAt_curveOfCurvature (θ₀ := θ₀) (L := L) hκ s).mul_const
      ((starRingEnd ℂ) v))
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h
    rw [← re_tau_mul_conj_I_tau]
    exact h2
  have hFTC : ∀ a b, p b - p a = ∫ r in a..b, Real.sin (Θ r - θ₁) := fun a b =>
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hpd r)
      (hsc.intervalIntegrable _ _)).symm
  have hΘper : Θ (L / 2) = θ₁ + π := by
    have := angleOfCurvature_add_period (θ₀ := θ₀) hκ hκp hint (-L / 2)
    rw [show -L / 2 + L = L / 2 by ring] at this
    exact this
  have hsinnn : ∀ r ∈ Set.Icc (-L / 2) (L / 2), 0 ≤ Real.sin (Θ r - θ₁) := by
    intro r hr
    have h1 : 0 ≤ Θ r - θ₁ := by
      rw [angleOfCurvature_sub hκ]
      exact intervalIntegral.integral_nonneg hr.1 fun t _ => hκ0 t
    have h2 : Θ r - θ₁ ≤ π := by
      have : Θ (L / 2) - Θ r = ∫ t in r..(L / 2), κ t := angleOfCurvature_sub hκ _ _
      have h3 : 0 ≤ ∫ t in r..(L / 2), κ t :=
        intervalIntegral.integral_nonneg hr.2 fun t _ => hκ0 t
      linarith
    exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
  have hW : p (L / 2) - p (-L / 2) = W := hFTC _ _
  have hanti : ∀ s, p (s + L) = -p s := fun s => by
    simp only [hp, curveOfCurvature_add_period hκ hκp hint s, neg_mul, Complex.neg_re]
  have hend : p (L / 2) = -p (-L / 2) := by
    rw [← hanti, show -L / 2 + L = L / 2 by ring]
  have hcell : ∀ r ∈ Set.Icc (-L / 2) (L / 2), |p r| ≤ W / 2 := by
    intro r hr
    have h1 : 0 ≤ p r - p (-L / 2) := by
      rw [hFTC]
      exact intervalIntegral.integral_nonneg hr.1 fun t ht => hsinnn t ⟨ht.1, ht.2.trans hr.2⟩
    have h2 : 0 ≤ p (L / 2) - p r := by
      rw [hFTC]
      exact intervalIntegral.integral_nonneg hr.2 fun t ht => hsinnn t ⟨hr.1.trans ht.1, ht.2⟩
    rw [abs_le]; constructor <;> linarith
  have habsper : Function.Periodic (fun s => |p s|) L := fun s => by
    simp only [hanti, abs_neg]
  obtain ⟨k, hk⟩ := exists_int_cell hL s
  have := hcell (s - k * L) ⟨by linarith [(abs_le.1 hk).1], by linarith [(abs_le.1 hk).2]⟩
  have e : |p (s - k * L)| = |p s| := habsper.sub_int_mul_eq k
  rw [e] at this
  exact abs_le.1 this

/-- **The width is positive** when the curvature is. -/
theorem curveWidth_pos (hκ : Continuous κ) (hκ0 : ∀ s, 0 < κ s)
    (hκp : Function.Periodic κ L) (hint : ∫ r in (0 : ℝ)..L, κ r = π) (hL : 0 < L) :
    0 < curveWidth θ₀ κ L := by
  have hΘc : Continuous (angleOfCurvature θ₀ κ) := continuous_angleOfCurvature hκ
  have hΘper : angleOfCurvature θ₀ κ (L / 2) = angleOfCurvature θ₀ κ (-L / 2) + π := by
    have := angleOfCurvature_add_period (θ₀ := θ₀) hκ hκp hint (-L / 2)
    rw [show -L / 2 + L = L / 2 by ring] at this
    exact this
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((Real.continuous_sin.comp (hΘc.sub continuous_const)).intervalIntegrable _ _)
    (fun r hr => ?_) (by linarith)
  have h1 : 0 < angleOfCurvature θ₀ κ r - angleOfCurvature θ₀ κ (-L / 2) := by
    rw [angleOfCurvature_sub hκ]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hκ.intervalIntegrable _ _)
      (fun t _ => hκ0 t) hr.1
  have h2 : 0 < angleOfCurvature θ₀ κ (L / 2) - angleOfCurvature θ₀ κ r := by
    rw [angleOfCurvature_sub hκ]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hκ.intervalIntegrable _ _)
      (fun t _ => hκ0 t) hr.2
  exact Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)

/-- **Width bound from turning bounds.**  If the turning `∫_{-L/2}^s κ` on the left half-cell
is at most `g₁`, and the remaining turning `∫_s^{L/2} κ` on the right half-cell is at most
`g₂`, then `W ≤ ∫_{-L/2}^0 g₁ + ∫_0^{L/2} g₂` (using `sin x ≤ min (x, π - x)`). -/
theorem curveWidth_le (hκ : Continuous κ) (hκ0 : ∀ s, 0 ≤ κ s)
    (hκp : Function.Periodic κ L) (hint : ∫ r in (0 : ℝ)..L, κ r = π) (hL : 0 < L)
    {g₁ g₂ : ℝ → ℝ} (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (h₁ : ∀ s ∈ Set.Icc (-L / 2) 0, ∫ r in (-L / 2)..s, κ r ≤ g₁ s)
    (h₂ : ∀ s ∈ Set.Icc 0 (L / 2), ∫ r in s..(L / 2), κ r ≤ g₂ s) :
    curveWidth θ₀ κ L ≤ (∫ s in (-L / 2)..0, g₁ s) + ∫ s in (0 : ℝ)..(L / 2), g₂ s := by
  have hΘc : Continuous (angleOfCurvature θ₀ κ) := continuous_angleOfCurvature hκ
  have hsc : Continuous (fun s => Real.sin (angleOfCurvature θ₀ κ s -
      angleOfCurvature θ₀ κ (-L / 2))) :=
    Real.continuous_sin.comp (hΘc.sub continuous_const)
  have hΘper : angleOfCurvature θ₀ κ (L / 2) = angleOfCurvature θ₀ κ (-L / 2) + π := by
    have := angleOfCurvature_add_period (θ₀ := θ₀) hκ hκp hint (-L / 2)
    rw [show -L / 2 + L = L / 2 by ring] at this
    exact this
  unfold curveWidth
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hsc.intervalIntegrable _ _) (hsc.intervalIntegrable _ _)]
  refine add_le_add (intervalIntegral.integral_mono_on (by linarith)
    (hsc.intervalIntegrable _ _) (hg₁.intervalIntegrable _ _) fun s hs => ?_)
    (intervalIntegral.integral_mono_on (by linarith)
    (hsc.intervalIntegrable _ _) (hg₂.intervalIntegrable _ _) fun s hs => ?_)
  · rw [angleOfCurvature_sub hκ]
    have h0 : 0 ≤ ∫ r in (-L / 2)..s, κ r :=
      intervalIntegral.integral_nonneg hs.1 fun t _ => hκ0 t
    exact (Real.sin_le h0).trans (h₁ s hs)
  · have e : angleOfCurvature θ₀ κ s - angleOfCurvature θ₀ κ (-L / 2) =
        π - ∫ r in s..(L / 2), κ r := by
      rw [← angleOfCurvature_sub hκ, hΘper]; ring
    have h0 : 0 ≤ ∫ r in s..(L / 2), κ r :=
      intervalIntegral.integral_nonneg hs.2 fun t _ => hκ0 t
    rw [e, Real.sin_pi_sub]
    exact (Real.sin_le h0).trans (h₂ s hs)

end Ovals

end
