module

public import UnitTangentIterates.WeightedResolvent
public import UnitTangentIterates.Jacobi

/-!
# Lemma 6.2 at a fixed time: the estimates `(6.5)`, `(6.6)` and `(6.7)`

At a fixed time of a path, let `η` be the front normal velocity and `η_R` the rear normal
velocity, as functions of the front parameter `u`.  By `Ovals.jacobi_equation`,

`∂ᵤη_R = g η - g cos δ · η_R`,

where `g > 0` is the front speed and `0 ≤ δ ≤ A < π/2` the steering angle.  The rear speed is
`g cos δ`, so `∫ g cos δ |η_R| du` and `∫ g |η| du` are the `L¹` norms of `η_R` and `η` in rear
and front arclength.  We obtain:

* (6.5) `∫ g cos δ |η_R| ≤ ∫ g |η|`;
* (6.6) `(1 - e^{-ℓ}) |η_R| ≤ ∫ g |η|`, with `ℓ = ∫ g cos δ` the rear perimeter, and
  `ℓ ≥ 2π / tan A` by total turning (the rear angle `Θ - δ` has `u`-derivative `g sin δ` and
  turns by `2π`);
* (6.7) in rear arclength, `∂ₓη_R = sec δ · η - η_R`, so `|∂ₓη_R| ≤ sec A |η| + |η_R|`.
-/

@[expose] public section

namespace Ovals

open Real intervalIntegral MeasureTheory

variable {η ηR g δ : ℝ → ℝ} {p A : ℝ}

/-- **(6.5)** The selected inverse does not increase the `L¹` norm of the normal velocity. -/
theorem jacobi_L1_le (hp : 0 < p) (hη : Continuous η) (hg : Continuous g) (hδ : Continuous δ)
    (hg0 : ∀ u, 0 < g u) (hδA : ∀ u, δ u ∈ Set.Icc 0 A) (hA : A < π / 2)
    (hJ : ∀ u, HasDerivAt ηR (g u * η u - g u * Real.cos (δ u) * ηR u) u)
    (hηRp : Function.Periodic ηR p) :
    ∫ u in (0 : ℝ)..p, g u * Real.cos (δ u) * |ηR u| ≤ ∫ u in (0 : ℝ)..p, g u * |η u| := by
  have hcos : ∀ u, 0 ≤ Real.cos (δ u) := fun u =>
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [(hδA u).1, Real.pi_pos], by linarith [(hδA u).2]⟩
  have := integral_mul_abs_le_of_periodic (f := fun u => g u * η u)
    (β := fun u => g u * Real.cos (δ u)) hp (hg.mul hη) (hg.mul (Real.continuous_cos.comp hδ))
    (fun u => mul_nonneg (hg0 u).le (hcos u)) hJ hηRp
  simpa [abs_mul, abs_of_pos (hg0 _)] using this

/-- **(6.6)** `L¹ → L^∞`: `(1 - e^{-ℓ}) |η_R| ≤ ∫ g |η|`, `ℓ = ∫₀ᵖ g cos δ`. -/
theorem jacobi_sup_le (hp : 0 < p) (hη : Continuous η) (hg : Continuous g) (hδ : Continuous δ)
    (hηp : Function.Periodic η p) (hgp : Function.Periodic g p) (hδp : Function.Periodic δ p)
    (hg0 : ∀ u, 0 < g u) (hδA : ∀ u, δ u ∈ Set.Icc 0 A) (hA : A < π / 2)
    (hJ : ∀ u, HasDerivAt ηR (g u * η u - g u * Real.cos (δ u) * ηR u) u)
    (hηRp : Function.Periodic ηR p) (u : ℝ) :
    (1 - Real.exp (-∫ v in (0 : ℝ)..p, g v * Real.cos (δ v))) * |ηR u| ≤
      ∫ v in (0 : ℝ)..p, g v * |η v| := by
  have hcos : ∀ u, 0 ≤ Real.cos (δ u) := fun u =>
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [(hδA u).1, Real.pi_pos], by linarith [(hδA u).2]⟩
  have := abs_le_integral_of_periodic (f := fun u => g u * η u)
    (β := fun u => g u * Real.cos (δ u)) hp (hg.mul hη) (hg.mul (Real.continuous_cos.comp hδ))
    (fun u => by simp only [hgp u, hηp u]) (fun u => by simp only [hgp u, hδp u])
    (fun u => mul_nonneg (hg0 u).le (hcos u)) hJ hηRp u
  simpa [abs_mul, abs_of_pos (hg0 _)] using this

/-- **Total turning bounds the rear perimeter below.**  If the rear angle `Ψ` has
`Ψ' = g sin δ` and turns by `2π` over a period, then `ℓ = ∫₀ᵖ g cos δ ≥ 2π / tan A`. -/
theorem rear_perimeter_ge {Ψ : ℝ → ℝ} (hp : 0 < p) (hg : Continuous g) (hδ : Continuous δ)
    (hg0 : ∀ u, 0 < g u) (hδA : ∀ u, δ u ∈ Set.Icc 0 A) (hA : A < π / 2) (hA0 : 0 < A)
    (hΨ : ∀ u, HasDerivAt Ψ (g u * Real.sin (δ u)) u) (hΨp : Ψ p = Ψ 0 + 2 * π) :
    2 * π / Real.tan A ≤ ∫ u in (0 : ℝ)..p, g u * Real.cos (δ u) := by
  have htan : 0 < Real.tan A := Real.tan_pos_of_pos_of_lt_pi_div_two hA0 hA
  have hturn : ∫ u in (0 : ℝ)..p, g u * Real.sin (δ u) = 2 * π := by
    rw [integral_eq_sub_of_hasDerivAt (fun u _ => hΨ u)
      ((hg.mul (Real.continuous_sin.comp hδ)).intervalIntegrable _ _), hΨp]; ring
  have hpt : ∀ u, g u * Real.sin (δ u) ≤ Real.tan A * (g u * Real.cos (δ u)) := fun u => by
    have hc : 0 < Real.cos (δ u) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [(hδA u).1, Real.pi_pos], by linarith [(hδA u).2]⟩
    have ht : Real.tan (δ u) ≤ Real.tan A :=
      Real.strictMonoOn_tan.monotoneOn ⟨by linarith [(hδA u).1, Real.pi_pos],
        by linarith [(hδA u).2]⟩ ⟨by linarith [Real.pi_pos], hA⟩ (hδA u).2
    rw [Real.tan_eq_sin_div_cos] at ht
    have := (div_le_iff₀ hc).1 ht
    nlinarith [hg0 u]
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hp.le
    ((hg.mul (Real.continuous_sin.comp hδ)).intervalIntegrable 0 p)
    ((continuous_const.mul (hg.mul (Real.continuous_cos.comp hδ))).intervalIntegrable 0 p)
    (fun u _ => hpt u)
  simp only [Pi.mul_apply, Function.comp] at hmono
  rw [hturn, intervalIntegral.integral_const_mul] at hmono
  rw [div_le_iff₀ htan]; linarith

/-- **(6.7)** In rear arclength `∂ₓ = (g cos δ)⁻¹ ∂ᵤ`, the Jacobi equation reads
`∂ₓη_R = sec δ · η - η_R`; hence `|∂ₓη_R| ≤ sec A |η| + |η_R|`. -/
theorem jacobi_deriv_bound (hg0 : ∀ u, 0 < g u) (hδA : ∀ u, δ u ∈ Set.Icc 0 A)
    (hA : A < π / 2) (u : ℝ) :
    |(g u * η u - g u * Real.cos (δ u) * ηR u) / (g u * Real.cos (δ u))| ≤
      |η u| / Real.cos A + |ηR u| := by
  have hc : 0 < Real.cos (δ u) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(hδA u).1, Real.pi_pos], by linarith [(hδA u).2]⟩
  have hcA : 0 < Real.cos A := Real.cos_pos_of_mem_Ioo ⟨by linarith [(hδA u).1,
    (hδA u).2, Real.pi_pos], hA⟩
  have hcle : Real.cos A ≤ Real.cos (δ u) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (hδA u).1 (by linarith [Real.pi_pos]) (hδA u).2
  have e : (g u * η u - g u * Real.cos (δ u) * ηR u) / (g u * Real.cos (δ u)) =
      η u / Real.cos (δ u) - ηR u := by
    field_simp [(hg0 u).ne', hc.ne']
  rw [e]
  refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
  rw [abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hcA hcle

/-- **Second derivative of the rear normal velocity.**  Differentiating the Jacobi equation:
in rear arclength (`∂ₓ = (g cos δ)⁻¹ ∂ᵤ`), the first derivative `X = ∂ₓη_R = η / cos δ - η_R`
satisfies

`∂ₓX = sec²δ tan δ (K - sin δ) η + sec²δ ∂ₛη - X`,

where `K = ∂ᵤΘ / g` is the front curvature and `∂ₛη = ∂ᵤη / g` the front arclength
derivative. -/
theorem jacobi_second_deriv {Θ' η' : ℝ → ℝ} (u : ℝ) (hg0 : 0 < g u)
    (hc : 0 < Real.cos (δ u)) (hη : HasDerivAt η (η' u) u)
    (hδ : HasDerivAt δ (Θ' u - g u * Real.sin (δ u)) u)
    (hJ : HasDerivAt ηR (g u * η u - g u * Real.cos (δ u) * ηR u) u) :
    HasDerivAt (fun u => η u / Real.cos (δ u) - ηR u)
      (g u * Real.cos (δ u) *
        (Real.tan (δ u) / Real.cos (δ u) ^ 2 * (Θ' u / g u - Real.sin (δ u)) * η u +
          η' u / g u / Real.cos (δ u) ^ 2 - (η u / Real.cos (δ u) - ηR u))) u := by
  have h := (hη.div hδ.cos hc.ne').sub hJ
  convert h using 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- **(6.8) pointwise.**  If the front curvature satisfies `|K| ≤ κ` and `0 ≤ δ ≤ A < π/2`, the
second rear-arclength derivative of `η_R` is bounded by
`sec²A (tan A (κ + 1) |η| + |∂ₛη|) + |∂ₓη_R|`. -/
theorem jacobi_second_deriv_bound {d e K ηs X κ : ℝ} (hδA : d ∈ Set.Icc 0 A)
    (hA : A < π / 2) (hK : |K| ≤ κ) :
    |Real.tan d / Real.cos d ^ 2 * (K - Real.sin d) * e +
        ηs / Real.cos d ^ 2 - X| ≤
      (Real.tan A * (κ + 1) * |e| + |ηs|) / Real.cos A ^ 2 + |X| := by
  have hc : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδA.1, Real.pi_pos], by linarith [hδA.2]⟩
  have hcA : 0 < Real.cos A := Real.cos_pos_of_mem_Ioo ⟨by linarith [hδA.1,
    hδA.2, Real.pi_pos], hA⟩
  have hcle : Real.cos A ≤ Real.cos d :=
    Real.cos_le_cos_of_nonneg_of_le_pi hδA.1 (by linarith [Real.pi_pos]) hδA.2
  have ht0 : 0 ≤ Real.tan d := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hδA.1
      (by linarith [hδA.2, Real.pi_pos])) hc.le
  have htle : Real.tan d ≤ Real.tan A :=
    Real.strictMonoOn_tan.monotoneOn ⟨by linarith [hδA.1, Real.pi_pos],
      by linarith [hδA.2]⟩ ⟨by linarith [hδA.1, hδA.2, Real.pi_pos], hA⟩ hδA.2
  have hc2 : Real.cos A ^ 2 ≤ Real.cos d ^ 2 := pow_le_pow_left₀ hcA.le hcle 2
  have htA : 0 ≤ Real.tan A := ht0.trans htle
  have hKs : |K - Real.sin d| ≤ κ + 1 :=
    (abs_sub _ _).trans (add_le_add hK (Real.abs_sin_le_one _))
  refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_nonneg ht0, abs_of_pos (by positivity :
    (0 : ℝ) < Real.cos d ^ 2), add_div]
  gcongr
  · calc Real.tan d / Real.cos d ^ 2 * |K - Real.sin d| * |e|
        ≤ Real.tan A / Real.cos A ^ 2 * (κ + 1) * |e| := by gcongr
      _ = Real.tan A * (κ + 1) * |e| / Real.cos A ^ 2 := by ring

end Ovals

end
