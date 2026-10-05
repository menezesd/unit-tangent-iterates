module

public import UnitTangentIterates.Steering
public import UnitTangentIterates.Reduction

/-!
# The steering equation in an arbitrary parameter

Along a path of curves (Section 6) the fronts are not parametrized by arclength.  If a front
has speed `b = |F'|` and tangent angle `Θ` with `Θ' = a`, the steering equation of Lemma 2.1
in the parameter `u` reads

`δ' = a - b sin δ`.

* `Ovals.weightedSteering_exists`: if `a, b` are continuous and `p`-periodic, `b > 0` and
  `0 ≤ a ≤ κ b` with `κ < 1`, there is a `p`-periodic solution with values in `[0, arcsin κ]`.
  We reduce to the arclength case by the change of parameter `s = ∫₀ᵘ b`.
* `Ovals.weightedSteering_diff_le`: a **maximum principle** comparison.  Two such solutions,
  for data `(a₁, b₁)` and `(a₂, b₂)` with `b₁, b₂ ≥ m > 0`, differ by at most
  `(sup |a₁ - a₂| + sup |b₁ - b₂|) / (m cos A)`, where `A < π/2` bounds both solutions.  At a
  maximum of `δ₁ - δ₂` the derivatives agree, which forces the bound.  In particular the
  selected solution is unique (`Ovals.weightedSteering_unique`) and depends Lipschitz
  continuously on the data.
-/

@[expose] public section

namespace Ovals

open Real

/-- **Maximum principle for the steering equation.**  Let `δ₁, δ₂` be `p`-periodic solutions of
`δᵢ' = aᵢ - bᵢ sin δᵢ` with values in `[0, A]`, `A < π/2`.  If `bᵢ ≥ m > 0`,
`|a₁ - a₂| ≤ α` and `|b₁ - b₂| ≤ β`, then `|δ₁ - δ₂| ≤ (α + β) / (m cos A)`. -/
theorem weightedSteering_diff_le {a₁ a₂ b₁ b₂ δ₁ δ₂ : ℝ → ℝ} {p A m α β : ℝ} (hp : 0 < p)
    (hA : A < π / 2) (hm : 0 < m)
    (h₁ : ∀ u, HasDerivAt δ₁ (a₁ u - b₁ u * Real.sin (δ₁ u)) u)
    (h₂ : ∀ u, HasDerivAt δ₂ (a₂ u - b₂ u * Real.sin (δ₂ u)) u)
    (h₁p : Function.Periodic δ₁ p) (h₂p : Function.Periodic δ₂ p)
    (h₁b : ∀ u, δ₁ u ∈ Set.Icc 0 A) (h₂b : ∀ u, δ₂ u ∈ Set.Icc 0 A)
    (hb₁ : ∀ u, m ≤ b₁ u) (hb₂ : ∀ u, m ≤ b₂ u)
    (hα : ∀ u, |a₁ u - a₂ u| ≤ α) (hβ : ∀ u, |b₁ u - b₂ u| ≤ β) (u : ℝ) :
    |δ₁ u - δ₂ u| ≤ (α + β) / (m * Real.cos A) := by
  have hcosA : 0 < Real.cos A := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(h₁b 0).1, (h₁b 0).2, Real.pi_pos], hA⟩
  -- one-sided bound, applied twice
  have one_side : ∀ {a₁ a₂ b₁ b₂ δ₁ δ₂ : ℝ → ℝ},
      (∀ u, HasDerivAt δ₁ (a₁ u - b₁ u * Real.sin (δ₁ u)) u) →
      (∀ u, HasDerivAt δ₂ (a₂ u - b₂ u * Real.sin (δ₂ u)) u) →
      Function.Periodic δ₁ p → Function.Periodic δ₂ p →
      (∀ u, δ₁ u ∈ Set.Icc 0 A) → (∀ u, δ₂ u ∈ Set.Icc 0 A) → (∀ u, m ≤ b₂ u) →
      (∀ u, |a₁ u - a₂ u| ≤ α) → (∀ u, |b₁ u - b₂ u| ≤ β) →
      ∀ u, δ₁ u - δ₂ u ≤ (α + β) / (m * Real.cos A) := by
    intro a₁ a₂ b₁ b₂ δ₁ δ₂ h₁ h₂ h₁p h₂p h₁b h₂b hb₂ hα hβ u
    have hc : Continuous fun u => δ₁ u - δ₂ u :=
      (continuous_iff_continuousAt.2 fun x => (h₁ x).continuousAt).sub
        (continuous_iff_continuousAt.2 fun x => (h₂ x).continuousAt)
    obtain ⟨u₀, hu₀⟩ := exists_max_of_periodic hp hc (fun u => by simp only [h₁p u, h₂p u])
    have hd : HasDerivAt (fun u => δ₁ u - δ₂ u)
        ((a₁ u₀ - b₁ u₀ * Real.sin (δ₁ u₀)) - (a₂ u₀ - b₂ u₀ * Real.sin (δ₂ u₀))) u₀ :=
      (h₁ u₀).sub (h₂ u₀)
    have h0 := IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hu₀) hd
    have hbound : δ₁ u₀ - δ₂ u₀ ≤ (α + β) / (m * Real.cos A) := by
      rcases le_or_gt (δ₁ u₀ - δ₂ u₀) 0 with hle | hgt
      · have hα0 : 0 ≤ α := (abs_nonneg _).trans (hα u₀)
        have hβ0 : 0 ≤ β := (abs_nonneg _).trans (hβ u₀)
        exact hle.trans (div_nonneg (by linarith) (mul_pos hm hcosA).le)
      · have hs : Real.cos A * (δ₁ u₀ - δ₂ u₀) ≤ Real.sin (δ₁ u₀) - Real.sin (δ₂ u₀) :=
          cos_mul_sub_le_sin_sub_sin hA (h₂b u₀).1 (by linarith) (h₁b u₀).2
        have hkey : b₂ u₀ * (Real.sin (δ₁ u₀) - Real.sin (δ₂ u₀)) ≤ α + β := by
          have e : b₂ u₀ * (Real.sin (δ₁ u₀) - Real.sin (δ₂ u₀)) =
              (a₁ u₀ - a₂ u₀) - (b₁ u₀ - b₂ u₀) * Real.sin (δ₁ u₀) := by linarith
          rw [e]
          have h1 := (le_abs_self _).trans (hα u₀)
          have h2 : -((b₁ u₀ - b₂ u₀) * Real.sin (δ₁ u₀)) ≤ β := by
            have := abs_mul (b₁ u₀ - b₂ u₀) (Real.sin (δ₁ u₀))
            have hs1 := Real.abs_sin_le_one (δ₁ u₀)
            have := neg_le_abs ((b₁ u₀ - b₂ u₀) * Real.sin (δ₁ u₀))
            nlinarith [hβ u₀, abs_nonneg (b₁ u₀ - b₂ u₀)]
          linarith
        rw [le_div_iff₀ (mul_pos hm hcosA)]
        have hb := hb₂ u₀
        have i1 : m * (Real.cos A * (δ₁ u₀ - δ₂ u₀)) ≤ b₂ u₀ * (Real.cos A * (δ₁ u₀ - δ₂ u₀)) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
        have i2 : b₂ u₀ * (Real.cos A * (δ₁ u₀ - δ₂ u₀)) ≤
            b₂ u₀ * (Real.sin (δ₁ u₀) - Real.sin (δ₂ u₀)) :=
          mul_le_mul_of_nonneg_left hs (by linarith)
        nlinarith
    exact (hu₀ u).trans hbound
  rw [abs_le]
  constructor
  · have := one_side h₂ h₁ h₂p h₁p h₂b h₁b hb₁ (fun u => by rw [abs_sub_comm]; exact hα u)
      (fun u => by rw [abs_sub_comm]; exact hβ u) u
    linarith
  · exact one_side h₁ h₂ h₁p h₂p h₁b h₂b hb₂ hα hβ u

/-- **Uniqueness** of the selected periodic solution of the weighted steering equation. -/
theorem weightedSteering_unique {a b δ₁ δ₂ : ℝ → ℝ} {p A m : ℝ} (hp : 0 < p)
    (hA : A < π / 2) (hm : 0 < m)
    (h₁ : ∀ u, HasDerivAt δ₁ (a u - b u * Real.sin (δ₁ u)) u)
    (h₂ : ∀ u, HasDerivAt δ₂ (a u - b u * Real.sin (δ₂ u)) u)
    (h₁p : Function.Periodic δ₁ p) (h₂p : Function.Periodic δ₂ p)
    (h₁b : ∀ u, δ₁ u ∈ Set.Icc 0 A) (h₂b : ∀ u, δ₂ u ∈ Set.Icc 0 A)
    (hb : ∀ u, m ≤ b u) : δ₁ = δ₂ := by
  funext u
  have := weightedSteering_diff_le (α := 0) (β := 0) hp hA hm h₁ h₂ h₁p h₂p h₁b h₂b hb hb
    (fun u => by simp) (fun u => by simp) u
  rw [add_zero, zero_div] at this
  have := abs_nonneg (δ₁ u - δ₂ u)
  have : |δ₁ u - δ₂ u| = 0 := by linarith
  linarith [abs_eq_zero.1 this]

/-- A positive continuous periodic function is bounded below by a positive constant. -/
lemma exists_pos_lower_bound_of_periodic {b : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hb : Continuous b)
    (hbp : Function.Periodic b p) (hb0 : ∀ u, 0 < b u) : ∃ m > 0, ∀ u, m ≤ b u := by
  obtain ⟨u₀, hu₀⟩ := exists_max_of_periodic hp hb.neg (fun u => by simp [hbp u])
  exact ⟨b u₀, hb0 u₀, fun u => by have := hu₀ u; simp only at this; linarith⟩

/-- **Existence** of a periodic solution of the weighted steering equation `δ' = a - b sin δ`
with values in `[0, arcsin κ]`, when `0 ≤ a ≤ κ b`, `b > 0`, `κ < 1`. -/
theorem weightedSteering_exists {a b : ℝ → ℝ} {p κ : ℝ} (hp : 0 < p) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (ha : Continuous a) (hb : Continuous b) (hap : Function.Periodic a p)
    (hbp : Function.Periodic b p) (hb0 : ∀ u, 0 < b u) (ha0 : ∀ u, 0 ≤ a u)
    (hab : ∀ u, a u ≤ κ * b u) :
    ∃ δ : ℝ → ℝ, Function.Periodic δ p ∧ (∀ u, HasDerivAt δ (a u - b u * Real.sin (δ u)) u) ∧
      ∀ u, δ u ∈ Set.Icc 0 (Real.arcsin κ) := by
  obtain ⟨m, hm, hbm⟩ := exists_pos_lower_bound_of_periodic hp hb hbp hb0
  -- the arclength-type parameter `s(u) = ∫₀ᵘ b`
  set s : ℝ → ℝ := fun u => ∫ r in (0 : ℝ)..u, b r with hs_def
  have hs : ∀ u, HasDerivAt s (b u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable _ _)
      (hb.stronglyMeasurableAtFilter _ _) hb.continuousAt
  have hsc : Continuous s := continuous_iff_continuousAt.2 fun u => (hs u).continuousAt
  have hsmono : StrictMono s := strictMono_of_deriv_pos fun u => by rw [(hs u).deriv]; exact hb0 u
  set L := s p
  have hsper : ∀ u, s (u + p) = s u + L := fun u => by
    simp only [s, L]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := u)
      (hb.intervalIntegrable _ _) (hb.intervalIntegrable _ _),
      hbp.intervalIntegral_add_eq u 0, zero_add]
  have hL : 0 < L := by
    have := hsmono hp
    simpa [s, L] using this
  have hslow : ∀ u, 0 ≤ u → m * u ≤ s u := fun u hu => by
    have : ∫ r in (0 : ℝ)..u, m ≤ s u :=
      intervalIntegral.integral_mono_on hu intervalIntegrable_const
        (hb.intervalIntegrable _ _) fun r _ => hbm r
    simpa [mul_comm] using this
  have hshigh : ∀ u, u ≤ 0 → s u ≤ m * u := fun u hu => by
    have h1 : ∫ r in u..(0 : ℝ), m ≤ ∫ r in u..(0 : ℝ), b r :=
      intervalIntegral.integral_mono_on hu intervalIntegrable_const
        (hb.intervalIntegrable _ _) fun r _ => hbm r
    have h2 : s u = -∫ r in u..(0 : ℝ), b r := by
      simp only [s]; rw [intervalIntegral.integral_symm]
    simp at h1
    rw [h2]; linarith
  have hsurj : Function.Surjective s := by
    refine hsc.surjective ?_ ?_
    · refine Filter.tendsto_atTop_mono' Filter.atTop ?_ (Filter.tendsto_id.const_mul_atTop hm)
      filter_upwards [Filter.eventually_ge_atTop 0] with u hu using hslow u hu
    · refine Filter.tendsto_atBot_mono' Filter.atBot ?_ (Filter.tendsto_id.const_mul_atBot hm)
      filter_upwards [Filter.eventually_le_atBot 0] with u hu using hshigh u hu
  set e := StrictMono.orderIsoOfSurjective s hsmono hsurj
  set σ : ℝ → ℝ := fun r => e.symm r
  have hsσ : ∀ r, s (σ r) = r := fun r => e.apply_symm_apply r
  have hσs : ∀ u, σ (s u) = u := fun u => e.symm_apply_apply u
  have hσc : Continuous σ := e.symm.continuous
  have hσper : ∀ r, σ (r + L) = σ r + p := fun r => by
    have : s (σ r + p) = r + L := by rw [hsper, hsσ]
    rw [← this, hσs]
  -- the curvature in the new parameter
  set K : ℝ → ℝ := fun r => a (σ r) / b (σ r)
  have hK : Continuous K := (ha.comp hσc).div (hb.comp hσc) fun r => (hb0 _).ne'
  have hKp : Function.Periodic K L := fun r => by simp only [K, hσper, hap (σ r), hbp (σ r)]
  have hK0 : ∀ r, 0 ≤ K r := fun r => div_nonneg (ha0 _) (hb0 _).le
  have hK1 : ∀ r, K r ≤ κ := fun r => (div_le_iff₀ (hb0 _)).2 (hab _)
  obtain ⟨δ', hδ'p, hδ', hδ'b⟩ := steering_exists hL hκ0 hκ1 hK hKp hK0 hK1
  refine ⟨fun u => δ' (s u), fun u => by simp only [hsper, hδ'p (s u)], fun u => ?_,
    fun u => hδ'b _⟩
  have := (hδ' (s u)).comp u (hs u)
  convert this using 1
  simp only [K, hσs]
  field_simp [(hb0 u).ne']

end Ovals

end
