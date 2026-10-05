module

public import UnitTangentIterates.Circle
public import UnitTangentIterates.Steering

/-!
# The rear track of a front (Lemma 2.1, geometric part)

Let `F` be a front parametrized by arclength, `F' = τ(Θ)`, `Θ' = K`, and let `δ` solve the
steering equation `δ' = K - sin δ` with `0 < δ < π/2`.  Put `Ψ = Θ - δ` and
`R = F - τ(Ψ)`.  Then (equations (2.1)–(2.2) of the paper)

* `R' = cos δ · τ(Ψ)` (so `x' = cos δ`, `Ψ' = sin δ`), and `R` is regular;
* `𝒯 R = F`;
* the curvature of `R` is `tan δ > 0`;
* if `F`, `δ` are `ℓ`-periodic and `Θ(s + ℓ) = Θ(s) + 2π`, then `R` is `ℓ`-periodic.
-/

@[expose] public section

namespace Ovals

open Complex Real

variable {F : ℝ → ℂ} {Θ K δ : ℝ → ℝ}

/-- The rear curve `R = F - τ(Θ - δ)`. -/
noncomputable def rearCurve (F : ℝ → ℂ) (Θ δ : ℝ → ℝ) : ℝ → ℂ :=
  fun s => F s - tau (Θ s - δ s)

theorem hasDerivAt_rearCurve (hF : ∀ s, HasDerivAt F (tau (Θ s)) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s) (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s)
    (s : ℝ) :
    HasDerivAt (rearCurve F Θ δ) ((Real.cos (δ s) : ℂ) * tau (Θ s - δ s)) s := by
  have h := hasDerivAt_tau_comp ((hΘ s).sub (hδ s))
  have := (hF s).sub h
  convert this using 1
  have e : tau (Θ s) = tau (δ s) * tau (Θ s - δ s) := by
    rw [← tau_add]; ring_nf
  rw [e, tau_eq (δ s)]
  simp only [Pi.sub_apply]
  push_cast
  ring

theorem deriv_rearCurve (hF : ∀ s, HasDerivAt F (tau (Θ s)) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s) (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s) :
    deriv (rearCurve F Θ δ) = fun s => (Real.cos (δ s) : ℂ) * tau (Θ s - δ s) :=
  funext fun s => (hasDerivAt_rearCurve hF hΘ hδ s).deriv

/-- **`𝒯 R = F`**: the front is the unit-tangent transform of the rear. -/
theorem unitTangentTransform_rearCurve (hF : ∀ s, HasDerivAt F (tau (Θ s)) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s) (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s)
    (hcos : ∀ s, 0 < Real.cos (δ s)) :
    unitTangentTransform (rearCurve F Θ δ) = F := by
  funext s
  unfold unitTangentTransform
  rw [deriv_rearCurve hF hΘ hδ]
  simp only
  rw [norm_mul, norm_tau, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hcos s)]
  have : (Real.cos (δ s) : ℂ) ≠ 0 := by exact_mod_cast (hcos s).ne'
  unfold rearCurve
  field_simp
  ring

/-- The rear is regular. -/
theorem deriv_rearCurve_ne_zero (hF : ∀ s, HasDerivAt F (tau (Θ s)) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s) (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s)
    (hcos : ∀ s, 0 < Real.cos (δ s)) (s : ℝ) : deriv (rearCurve F Θ δ) s ≠ 0 := by
  rw [deriv_rearCurve hF hΘ hδ]
  exact mul_ne_zero (by exact_mod_cast (hcos s).ne') (tau_ne_zero _)

/-- The curvature of the rear is `k = tan δ` (equation (2.2)). -/
theorem curvature_rearCurve (hF : ∀ s, HasDerivAt F (tau (Θ s)) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s) (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s)
    (hcos : ∀ s, 0 < Real.cos (δ s)) (s : ℝ) :
    curvature (rearCurve F Θ δ) s = Real.tan (δ s) := by
  have hd2 : HasDerivAt (fun s => (Real.cos (δ s) : ℂ) * tau (Θ s - δ s))
      ((((-(Real.sin (δ s)) * (K s - Real.sin (δ s)) : ℝ)) : ℂ) * tau (Θ s - δ s) +
        (Real.cos (δ s) : ℂ) * ((Real.sin (δ s) : ℝ) * I * tau (Θ s - δ s))) s := by
    have h1 : HasDerivAt (fun s => (Real.cos (δ s) : ℂ))
        ((-(Real.sin (δ s)) * (K s - Real.sin (δ s)) : ℝ)) s := by
      have := (Real.hasDerivAt_cos (δ s)).comp s (hδ s)
      exact this.ofReal_comp
    have h2 := hasDerivAt_tau_comp ((hΘ s).sub (hδ s))
    convert h1.mul h2 using 1
    simp only [Pi.sub_apply]
    push_cast; ring
  unfold curvature
  rw [deriv_rearCurve hF hΘ hδ, hd2.deriv, Real.tan_eq_sin_div_cos]
  have hc := conj_tau_mul_tau (Θ s - δ s)
  have hcs := hcos s
  have ht := norm_tau (Θ s - δ s)
  simp only
  generalize Real.cos (δ s) = c at hcs ⊢
  generalize Real.sin (δ s) = sn
  generalize K s = k
  generalize tau (Θ s - δ s) = t at hc ht ⊢
  have key : (starRingEnd ℂ) ((c : ℂ) * t) * (((-sn * (k - sn) : ℝ) : ℂ) * t +
        (c : ℂ) * ((sn : ℂ) * I * t))
      = ((c * (-sn * (k - sn)) : ℝ) : ℂ) + ((c ^ 2 * sn : ℝ) : ℂ) * I := by
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination ((c : ℂ) * (-(sn : ℂ) * (k - sn)) + (c : ℂ) ^ 2 * (sn : ℂ) * I) * hc
  rw [key, norm_mul, ht, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcs]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  field_simp

/-- The rear closes up when the front does. -/
theorem rearCurve_periodic {ℓ : ℝ} (hFp : Function.Periodic F ℓ)
    (hΘp : ∀ s, Θ (s + ℓ) = Θ s + 2 * π) (hδp : Function.Periodic δ ℓ) :
    Function.Periodic (rearCurve F Θ δ) ℓ := by
  intro s
  unfold rearCurve
  rw [hFp s, hΘp s, hδp s, show Θ s + 2 * π - δ s = (Θ s - δ s) + 2 * π by ring, tau_add]
  unfold tau
  simp

/-- **Lemma 2.1 (selected inverse).**  Let `F` be an `L`-periodic front parametrized by
arclength, `F' = τ(Θ)`, whose tangent turns once (`Θ(s + L) = Θ(s) + 2π`) and whose
curvature `K = Θ'` is continuous with `0 ≤ K ≤ κ < 1`.  Then there is a closed regular rear
curve `R` (namely `R = F - τ(Θ - δ)` for the selected steering angle `δ`) with `𝒯 R = F`
and curvature `0 < k_R ≤ κ / √(1 - κ²)`. -/
theorem selectedInverse_exists {L κ : ℝ} (hL : 0 < L) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hF : ∀ s, HasDerivAt F (tau (Θ s)) s) (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hK : Continuous K) (hK0 : ∀ s, 0 ≤ K s) (hK1 : ∀ s, K s ≤ κ)
    (hFp : Function.Periodic F L) (hΘp : ∀ s, Θ (s + L) = Θ s + 2 * π) :
    ∃ R : ℝ → ℂ, unitTangentTransform R = F ∧ Function.Periodic R L ∧
      (∀ s, deriv R s ≠ 0) ∧ ∀ s, 0 < curvature R s ∧ curvature R s ≤ κ / √(1 - κ ^ 2) := by
  have hKp : Function.Periodic K L := by
    intro s
    have h1 : HasDerivAt (fun x => Θ (x + L)) (K (s + L)) s := by
      simpa using (hΘ (s + L)).comp s ((hasDerivAt_id s).add_const L)
    have h2 : HasDerivAt (fun x => Θ (x + L)) (K s) s := by
      have : (fun x => Θ (x + L)) = fun x => Θ x + 2 * π := funext hΘp
      rw [this]; exact (hΘ s).add_const _
    exact h1.unique h2
  have hKint : ∫ s in (0:ℝ)..L, K s = 2 * π := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hΘ x)
      (hK.intervalIntegrable _ _)]
    have := hΘp 0
    rw [zero_add] at this
    linarith
  obtain ⟨δ, hδp, hδ, hδb⟩ := steering_exists hL hκ0 hκ1 hK hKp hK0 hK1
  have ha := arcsin_lt_pi_div_two hκ1
  have hpos : ∀ s, 0 < δ s := steering_pos hL hK hKp hK0 (by rw [hKint]; positivity) hδp hδ
    (fun s => (hδb s).1)
  have hcos : ∀ s, 0 < Real.cos (δ s) := fun s =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos s, Real.pi_pos], by linarith [(hδb s).2]⟩
  refine ⟨rearCurve F Θ δ, unitTangentTransform_rearCurve hF hΘ hδ hcos,
    rearCurve_periodic hFp hΘp hδp, deriv_rearCurve_ne_zero hF hΘ hδ hcos, fun s => ?_⟩
  rw [curvature_rearCurve hF hΘ hδ hcos]
  refine ⟨Real.tan_pos_of_pos_of_lt_pi_div_two (hpos s) (by linarith [(hδb s).2]), ?_⟩
  exact tan_steering_le hκ1 (hδb s)

end Ovals

end
