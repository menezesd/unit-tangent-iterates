import Mathlib

/-!
# The turning number of a closed curve, from a comparison with a model

Several statements of this project — most visibly
`SelectedInverseEmbedded.injOn_rearTrack_of_tubeMember` and
`SelectedInverseEmbedded.selInv_spec_of_turning` — carry as a hypothesis the
global topological normalization that the tangent angle of a closed curve
increases by exactly `2π` over one period.  The Umlaufsatz is not available in
Mathlib, and the fact is genuinely global, so it cannot be read off from the
local differential relations alone.

This file removes it whenever the curve is *quantitatively close to a model of
known turning*, which is exactly the situation of the last section of the
paper: every member of the tube is close to a model front, whose total turning
is computed from its curvature.

The mechanism is elementary and has two halves.

* `exists_int_turning` — the **quantization**: the tangent
  `X' = e^{iΘ}` of an `L`-periodic curve is `L`-periodic, so
  `Θ(s + L) − Θ(s) ∈ 2πℤ` for every `s`.
* `eq_zero_of_int_multiple` — the **rigidity**: a continuous function with
  values in `2πℤ` that vanishes somewhere vanishes identically (otherwise the
  intermediate value theorem would produce the value `π`).

Together they give `turning_eq_two_pi_of_integral`: if the total curvature over
one period is within `2π` of `2π`, then `Θ(s + L) = Θ(s) + 2π` for **every**
`s`.  Two ready-made forms of that hypothesis are provided:
`turning_eq_two_pi_of_L1_close` (an `L¹` comparison with a model curvature of
total turning `2π`) and `turning_eq_two_pi_of_sup_close` (a uniform one, with
`ε·L < 2π`).
-/

noncomputable section

open Real Set Function

namespace TurningNumber

/-- **Rigidity of continuous integer multiples.**  A continuous function with
values in `2πℤ` which vanishes at one point vanishes everywhere: otherwise the
intermediate value theorem would give it the value `±π`, which is not a
multiple of `2π`. -/
theorem eq_zero_of_int_multiple {h : ℝ → ℝ} (hc : Continuous h)
    (hint : ∀ s, ∃ n : ℤ, h s = 2 * π * n) {s₀ : ℝ} (h0 : h s₀ = 0) : ∀ s, h s = 0 := by
  intro s
  by_contra hne
  obtain ⟨n, hn⟩ := hint s
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn; exact hne hn
  have habs : 2 * π ≤ |h s| := by
    rw [hn, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
      have h1' : (1:ℤ) ≤ |n| := Int.one_le_abs (by omega)
      calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
        _ ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast h1'
        _ = |(n:ℝ)| := by push_cast [Int.cast_abs]; ring_nf
    nlinarith
  have key : ∃ c, h c = π ∨ h c = -π := by
    have hsub : uIcc (h s₀) (h s) ⊆ h '' uIcc s₀ s := intermediate_value_uIcc hc.continuousOn
    rcases le_or_gt 0 (h s) with hpos | hneg
    · have h2 : 2 * π ≤ h s := by rwa [abs_of_nonneg hpos] at habs
      have hmem : π ∈ uIcc (h s₀) (h s) := by
        rw [h0, uIcc_of_le (by linarith)]
        exact ⟨by linarith, by linarith⟩
      obtain ⟨c, _, hcv⟩ := hsub hmem
      exact ⟨c, Or.inl hcv⟩
    · have h2 : h s ≤ -(2 * π) := by rw [abs_of_neg hneg] at habs; linarith
      have hmem : -π ∈ uIcc (h s₀) (h s) := by
        rw [h0, uIcc_of_ge (by linarith)]
        exact ⟨by linarith, by linarith⟩
      obtain ⟨c, _, hcv⟩ := hsub hmem
      exact ⟨c, Or.inr hcv⟩
  obtain ⟨c, hc'⟩ := key
  obtain ⟨m, hm⟩ := hint c
  have hpi : (0:ℝ) < π := Real.pi_pos
  rcases hc' with h1 | h1 <;> rw [h1] at hm
  · have h2 : (2:ℝ) * m = 1 := by nlinarith [hm]
    have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
    omega
  · have h2 : (2:ℝ) * m = -1 := by nlinarith [hm]
    have h3 : (2 * m : ℤ) = -1 := by exact_mod_cast h2
    omega

/-- **Quantization of the turning.**  If `X` is `L`-periodic with unit tangent
`X' = e^{iΘ}`, then the tangent is `L`-periodic too, so the increment of the
tangent angle over one period is an integer multiple of `2π`. -/
theorem exists_int_turning {X : ℝ → ℂ} {Θ : ℝ → ℝ} {L : ℝ}
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hper : Function.Periodic X L) (s : ℝ) :
    ∃ n : ℤ, Θ (s + L) - Θ s = 2 * π * n := by
  have hi : HasDerivAt (fun t : ℝ => t + L) 1 s := by
    simpa using (hasDerivAt_id s).add_const L
  have hshift : HasDerivAt (fun t : ℝ => X (t + L))
      (Complex.exp (Complex.I * (Θ (s + L) : ℂ))) s := by
    simpa using (hX (s + L)).scomp s hi
  have heq : (fun t : ℝ => X (t + L)) = X := funext fun t => hper t
  rw [heq] at hshift
  have hexp : Complex.exp (Complex.I * (Θ (s + L) : ℂ)) = Complex.exp (Complex.I * (Θ s : ℂ)) :=
    hshift.unique (hX s)
  rw [Complex.exp_eq_exp_iff_exists_int] at hexp
  obtain ⟨n, hn⟩ := hexp
  refine ⟨n, ?_⟩
  have hn' : Complex.I * ((Θ (s + L) : ℂ) - (Θ s : ℂ) - (n : ℂ) * (2 * π)) = 0 := by
    linear_combination hn
  rcases mul_eq_zero.1 hn' with h2 | h2
  · exact absurd h2 Complex.I_ne_zero
  · have hc : (Θ (s + L) : ℂ) - (Θ s : ℂ) = (n : ℂ) * (2 * π) := by linear_combination h2
    have hr : Θ (s + L) - Θ s = (n : ℝ) * (2 * π) := by exact_mod_cast hc
    rw [hr]; ring

/-- **The turning number from the total curvature.**  For a closed curve of
period `L` with unit tangent `e^{iΘ}` and curvature `Θ' = K`, if the total
curvature over one period is within `2π` of `2π` then the tangent angle
increases by exactly `2π` over every period:  the increment is a continuous
multiple of `2π` (`exists_int_turning`) which is `2π` at the origin, hence `2π`
everywhere (`eq_zero_of_int_multiple`). -/
theorem turning_eq_two_pi_of_integral {X : ℝ → ℂ} {Θ K : ℝ → ℝ} {L : ℝ}
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hth : ∀ s, HasDerivAt Θ (K s) s)
    (hper : Function.Periodic X L)
    (hKint : IntervalIntegrable K MeasureTheory.volume 0 L)
    (hbound : |(∫ r in (0:ℝ)..L, K r) - 2 * π| < 2 * π) :
    ∀ s, Θ (s + L) = Θ s + 2 * π := by
  have hΘc : Continuous Θ :=
    continuous_iff_continuousAt.mpr fun s => (hth s).differentiableAt.continuousAt
  set h : ℝ → ℝ := fun s => Θ (s + L) - Θ s - 2 * π with hh
  have hcont : Continuous h := by fun_prop
  have hint : ∀ s, ∃ n : ℤ, h s = 2 * π * n := by
    intro s
    obtain ⟨n, hn⟩ := exists_int_turning hX hper s
    exact ⟨n - 1, by push_cast; simp only [hh]; rw [hn]; ring⟩
  have hInt : Θ L - Θ 0 = ∫ r in (0:ℝ)..L, K r :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hth x) hKint).symm
  have h0 : h 0 = 0 := by
    obtain ⟨n, hn⟩ := hint 0
    have habs : |h 0| < 2 * π := by
      simp only [hh, zero_add]
      rw [hInt]
      exact hbound
    rw [hn] at habs ⊢
    have hpi : (0:ℝ) < π := Real.pi_pos
    have hlt : |(n:ℝ)| < 1 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)] at habs
      nlinarith
    have hn0 : n = 0 := by
      by_contra hne
      have h1 : (1:ℤ) ≤ |n| := Int.one_le_abs (by omega)
      have h1' : (1:ℝ) ≤ |(n:ℝ)| := by
        calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
          _ ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast h1
          _ = |(n:ℝ)| := by push_cast [Int.cast_abs]; ring_nf
      linarith
    simp [hn0]
  intro s
  have hz := eq_zero_of_int_multiple hcont hint h0 s
  simp only [hh] at hz
  linarith

/-- **Quantization of the total curvature.**  The total curvature of a closed
curve over one period is an integer multiple of `2π`. -/
theorem exists_int_total_curvature {X : ℝ → ℂ} {Θ K : ℝ → ℝ} {L : ℝ}
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hth : ∀ s, HasDerivAt Θ (K s) s)
    (hper : Function.Periodic X L)
    (hKint : IntervalIntegrable K MeasureTheory.volume 0 L) :
    ∃ n : ℤ, (∫ r in (0:ℝ)..L, K r) = 2 * π * n := by
  obtain ⟨n, hn⟩ := exists_int_turning hX hper 0
  refine ⟨n, ?_⟩
  rw [zero_add] at hn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hth x) hKint]
  exact hn

/-- **The turning number of a pinched closed curve.**  A closed curve of period
`L` whose curvature is pinched by `0 < kmin ≤ K ≤ kmax` with `kmax·L < 4π` has
turning number one: its total curvature lies in `(0, 4π)` and is a multiple of
`2π`. -/
theorem turning_eq_two_pi_of_pinched {X : ℝ → ℂ} {Θ K : ℝ → ℝ} {L kmin kmax : ℝ}
    (hL : 0 < L)
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hth : ∀ s, HasDerivAt Θ (K s) s)
    (hper : Function.Periodic X L)
    (hKc : Continuous K)
    (hkmin : 0 < kmin) (hlow : ∀ s, kmin ≤ K s) (hhigh : ∀ s, K s ≤ kmax)
    (hsmall : kmax * L < 4 * π) :
    ∀ s, Θ (s + L) = Θ s + 2 * π := by
  refine turning_eq_two_pi_of_integral hX hth hper (hKc.intervalIntegrable 0 L) ?_
  have hlb : kmin * L ≤ ∫ r in (0:ℝ)..L, K r := by
    have := intervalIntegral.integral_mono_on (f := fun _ : ℝ => kmin) (g := K) hL.le
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := kmin))
      (hKc.intervalIntegrable 0 L) (fun x _ => hlow x)
    simpa [mul_comm] using this
  have hub : (∫ r in (0:ℝ)..L, K r) ≤ kmax * L := by
    have := intervalIntegral.integral_mono_on (f := K) (g := fun _ : ℝ => kmax) hL.le
      (hKc.intervalIntegrable 0 L)
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := kmax)) (fun x _ => hhigh x)
    simpa [mul_comm] using this
  have hpos : 0 < kmin * L := by positivity
  rw [abs_lt]
  constructor <;> linarith

/-- **The turning number from an `L¹` comparison with a model.**  If the
curvature of the closed curve differs from a model curvature `K₀` of total
turning `2π` by less than `2π` in `L¹` over one period, the curve has turning
number one. -/
theorem turning_eq_two_pi_of_L1_close {X : ℝ → ℂ} {Θ K K₀ : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hth : ∀ s, HasDerivAt Θ (K s) s)
    (hper : Function.Periodic X L)
    (hKint : IntervalIntegrable K MeasureTheory.volume 0 L)
    (hK0int : IntervalIntegrable K₀ MeasureTheory.volume 0 L)
    (hmodel : (∫ r in (0:ℝ)..L, K₀ r) = 2 * π)
    (hclose : (∫ r in (0:ℝ)..L, |K r - K₀ r|) < 2 * π) :
    ∀ s, Θ (s + L) = Θ s + 2 * π := by
  refine turning_eq_two_pi_of_integral hX hth hper hKint ?_
  have hsub : (∫ r in (0:ℝ)..L, (K r - K₀ r))
      = (∫ r in (0:ℝ)..L, K r) - ∫ r in (0:ℝ)..L, K₀ r :=
    intervalIntegral.integral_sub hKint hK0int
  have habs : |∫ r in (0:ℝ)..L, (K r - K₀ r)| ≤ ∫ r in (0:ℝ)..L, |K r - K₀ r| :=
    intervalIntegral.abs_integral_le_integral_abs hL
  rw [hsub, hmodel] at habs
  linarith

/-- **The turning number from a uniform comparison with a model.**  The same
conclusion when the curvature is within `ε` of a model curvature of total
turning `2π` uniformly, and `ε·L < 2π`. -/
theorem turning_eq_two_pi_of_sup_close {X : ℝ → ℂ} {Θ K K₀ : ℝ → ℝ} {L eps : ℝ}
    (hL : 0 ≤ L)
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hth : ∀ s, HasDerivAt Θ (K s) s)
    (hper : Function.Periodic X L)
    (hKc : Continuous K) (hK0c : Continuous K₀)
    (hmodel : (∫ r in (0:ℝ)..L, K₀ r) = 2 * π)
    (hclose : ∀ s, |K s - K₀ s| ≤ eps)
    (heps : eps * L < 2 * π) :
    ∀ s, Θ (s + L) = Θ s + 2 * π := by
  refine turning_eq_two_pi_of_L1_close hL hX hth hper (hKc.intervalIntegrable 0 L)
    (hK0c.intervalIntegrable 0 L) hmodel ?_
  have hle : (∫ r in (0:ℝ)..L, |K r - K₀ r|) ≤ eps * L := by
    have := intervalIntegral.integral_mono_on (f := fun r => |K r - K₀ r|)
      (g := fun _ => eps) hL ((hKc.sub hK0c).abs.intervalIntegrable 0 L)
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := eps)) (fun x _ => hclose x)
    simpa [mul_comm] using this
  linarith

end TurningNumber
