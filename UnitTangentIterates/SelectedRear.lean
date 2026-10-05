module

public import UnitTangentIterates.RearFront
public import UnitTangentIterates.Embedded

/-!
# The selected rear of a smooth oval is a smooth oval (Lemma 2.1, completed)

`Ovals.selectedInverse_exists` constructs, for a closed front of curvature `0 ≤ K ≤ κ < 1`, a
closed regular rear `R` with `𝒯 R = F` and positive curvature.  Here we add the remaining
qualitative parts of Lemma 2.1:

* **regularity gain** (`Ovals.contDiff_steering`): the steering angle solving
  `δ' = K - sin δ` is `C^∞` when `K` is;
* **embeddedness** (`Ovals.isOval_selectedRear`): the rear's tangent angle `Θ - δ` increases
  (its derivative is `sin δ > 0`) by exactly `2π` per period, so the rear is simple by the
  turning criterion `Ovals.injOn_of_turning`.  Hence the selected rear of a smooth oval is a
  smooth oval.
-/

@[expose] public section

namespace Ovals

open Complex Real
open scoped ContDiff

/-- **Regularity gain.**  A solution of the steering equation `δ' = K - sin δ` with smooth `K`
is smooth. -/
theorem contDiff_steering {K δ : ℝ → ℝ} (hK : ContDiff ℝ ∞ K)
    (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s) : ContDiff ℝ ∞ δ := by
  have hderiv : deriv δ = fun s => K s - Real.sin (δ s) := funext fun s => (hδ s).deriv
  have hdiff : Differentiable ℝ δ := fun s => (hδ s).differentiableAt
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => exact contDiff_zero.2 hdiff.continuous
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_deriv]
    refine ⟨hdiff, fun h => by exact absurd h (by simp), ?_⟩
    rw [hderiv]
    exact (hK.of_le (by exact_mod_cast le_top)).sub (Real.contDiff_sin.comp ih)

/-- A function whose derivative is smooth is smooth. -/
theorem contDiff_of_hasDerivAt_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : ContDiff ℝ ∞ f') :
    ContDiff ℝ ∞ f := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hf s).differentiableAt, ?_⟩
  rw [show deriv f = f' from funext fun s => (hf s).deriv]
  exact hf'

/-- **Lemma 2.1, complete qualitative form.**  Let `F` be an `L`-periodic front parametrized by
arclength, `F' = τ(Θ)`, whose tangent turns once (`Θ(s + L) = Θ(s) + 2π`) and whose curvature
`K = Θ'` is smooth with `0 ≤ K ≤ κ < 1`.  Then there is a smooth `L`-periodic steering angle
`δ` with values in `(0, π/2)` such that the selected rear `R = F - τ(Θ - δ)` is an oval with
`𝒯 R = F` and curvature `tan δ ≤ κ / √(1 - κ²)`. -/
theorem isOval_selectedRear {F : ℝ → ℂ} {Θ K : ℝ → ℝ} {L κ : ℝ} (hL : 0 < L) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hF : ∀ s, HasDerivAt F (tau (Θ s)) s) (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hK : ContDiff ℝ ∞ K) (hK0 : ∀ s, 0 ≤ K s) (hK1 : ∀ s, K s ≤ κ)
    (hFp : Function.Periodic F L) (hΘp : ∀ s, Θ (s + L) = Θ s + 2 * π) :
    ∃ δ : ℝ → ℝ, Function.Periodic δ L ∧ (∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s) ∧
      (∀ s, 0 < δ s ∧ δ s < π / 2) ∧ ContDiff ℝ ∞ δ ∧
      IsOval (rearCurve F Θ δ) ∧ unitTangentTransform (rearCurve F Θ δ) = F ∧
      ∀ s, curvature (rearCurve F Θ δ) s = Real.tan (δ s) ∧
        Real.tan (δ s) ≤ κ / √(1 - κ ^ 2) := by
  have hKc := hK.continuous
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
      (hKc.intervalIntegrable _ _)]
    have := hΘp 0
    rw [zero_add] at this
    linarith
  obtain ⟨δ, hδp, hδ, hδb⟩ := steering_exists hL hκ0 hκ1 hKc hKp hK0 hK1
  have ha := arcsin_lt_pi_div_two hκ1
  have hpos : ∀ s, 0 < δ s := steering_pos hL hKc hKp hK0 (by rw [hKint]; positivity) hδp hδ
    (fun s => (hδb s).1)
  have hlt : ∀ s, δ s < π / 2 := fun s => (hδb s).2.trans_lt ha
  have hcos : ∀ s, 0 < Real.cos (δ s) := fun s =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hpos s, Real.pi_pos], hlt s⟩
  have hδs : ContDiff ℝ ∞ δ := contDiff_steering hK hδ
  have hΘs : ContDiff ℝ ∞ Θ := contDiff_of_hasDerivAt_smooth hΘ hK
  have hFs : ContDiff ℝ ∞ F := contDiff_of_hasDerivAt_smooth hF (contDiff_tau.comp hΘs)
  have hδc : Continuous δ := hδs.continuous
  -- the rear tangent angle `Θ - δ` is monotone (its derivative is `sin δ > 0`)
  have hψ : ∀ s, HasDerivAt (fun s => Θ s - δ s) (Real.sin (δ s)) s := fun s => by
    have := (hΘ s).sub (hδ s)
    convert this using 1; ring
  have hmono : Monotone (fun s => Θ s - δ s) :=
    monotone_of_deriv_nonneg (fun s => (hψ s).differentiableAt)
      (fun s => by rw [(hψ s).deriv]; exact (Real.sin_pos_of_pos_of_lt_pi (hpos s)
        (by linarith [hlt s, Real.pi_pos])).le)
  refine ⟨δ, hδp, hδ, fun s => ⟨hpos s, hlt s⟩, hδs, ?_,
    unitTangentTransform_rearCurve hF hΘ hδ hcos, fun s =>
      ⟨curvature_rearCurve hF hΘ hδ hcos s, tan_steering_le hκ1 (hδb s)⟩⟩
  refine
    { contDiff := hFs.sub (contDiff_tau.comp (hΘs.sub hδs))
      regular := deriv_rearCurve_ne_zero hF hΘ hδ hcos
      curvature_pos := fun s => by
        rw [curvature_rearCurve hF hΘ hδ hcos]
        exact Real.tan_pos_of_pos_of_lt_pi_div_two (hpos s) (hlt s)
      closed_simple := ⟨L, hL, rearCurve_periodic hFp hΘp hδp, ?_⟩ }
  exact injOn_of_turning (g := fun s => Real.cos (δ s)) (θ := fun s => Θ s - δ s)
    (Real.continuous_cos.comp hδc) hcos (hΘs.continuous.sub hδc) hmono
    (hasDerivAt_rearCurve hF hΘ hδ) (rearCurve_periodic hFp hΘp hδp)
    (fun s => by simp only; rw [hΘp, hδp]; ring)

end Ovals

end
