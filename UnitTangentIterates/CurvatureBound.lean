module

public import UnitTangentIterates.FrontError
public import UnitTangentIterates.PeriodizationEstimates

/-!
# Proposition 4.3: the curvature bound for the closed models

If the isolated front curvature `K_* = y + y'/c` and the isolated rear curvature `y/c` are at
most `κ₁`, then for every `κ₂ > κ₁` and all sufficiently large `H`, the closed front curvature
`K_H = Y_H + Y_H'/c_H` and the closed rear curvature `Y_H/c_H` are at most `κ₂`.  In the paper,
`κ₁ = 1/20` and `κ₂ = κ₀ = 1/10`.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- `z ↦ z / √(1 - z²)` is Lipschitz on `[0, b]`, `b < 1`. -/
lemma div_sqrt_one_sub_sq_lipschitz {b u v : ℝ} (hb : b < 1) (hu0 : 0 ≤ u)
    (hub : u ≤ b) (hv0 : 0 ≤ v) (hvb : v ≤ b) :
    |u / √(1 - u ^ 2) - v / √(1 - v ^ 2)| ≤
      |u - v| * (1 / √(1 - b ^ 2) + 1 / √(1 - b ^ 2) ^ 3) := by
  have hb0 : 0 ≤ b := hu0.trans hub
  have hpos : 0 < 1 - b ^ 2 := by nlinarith
  have hc0 : 0 < √(1 - b ^ 2) := Real.sqrt_pos.2 hpos
  have hcu0 : √(1 - b ^ 2) ≤ √(1 - u ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have hinv : 1 / √(1 - u ^ 2) ≤ 1 / √(1 - b ^ 2) := one_div_le_one_div_of_le hc0 hcu0
  have hinv0 : 0 ≤ 1 / √(1 - u ^ 2) := by positivity
  have hL := inv_sqrt_one_sub_sq_lipschitz hb hu0 hub hv0 hvb
  have e : u / √(1 - u ^ 2) - v / √(1 - v ^ 2) =
      (u - v) * (1 / √(1 - u ^ 2)) + v * (1 / √(1 - u ^ 2) - 1 / √(1 - v ^ 2)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hinv0, abs_of_nonneg hv0]
  have hv1 : v ≤ 1 := by linarith
  have h1 : |u - v| * (1 / √(1 - u ^ 2)) ≤ |u - v| * (1 / √(1 - b ^ 2)) :=
    mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
  have h2 : v * |1 / √(1 - u ^ 2) - 1 / √(1 - v ^ 2)| ≤
      |1 / √(1 - u ^ 2) - 1 / √(1 - v ^ 2)| := by
    nlinarith [abs_nonneg (1 / √(1 - u ^ 2) - 1 / √(1 - v ^ 2))]
  have h3 : |u - v| / √(1 - b ^ 2) ^ 3 = |u - v| * (1 / √(1 - b ^ 2) ^ 3) := by ring
  nlinarith

/-- **Proposition 4.3, curvature bound.**  If the isolated curvatures `K_*` and `y/c` are at
most `κ₁ < κ₂`, then for all sufficiently large `H` the closed curvatures `K_H` and `Y_H/c_H`
are at most `κ₂`. -/
theorem periodized_curvature_le {y y' : ℝ → ℝ} {A a D b κ₁ κ₂ : ℝ}
    (hy : ∀ t, HasDerivAt y (y' t) t) (hy0 : ∀ t, 0 ≤ y t)
    (hyA : ∀ t, y t ≤ A * exp (-(a * |t|))) (ha : 0 < a) (hyD : ∀ t, |y' t| ≤ D * y t)
    (hyb : ∀ t, y t ≤ b) (hb : b < 1) (hκ : κ₁ < κ₂)
    (hKF : ∀ t, frontCurv y t ≤ κ₁) (hKR : ∀ t, y t / √(1 - y t ^ 2) ≤ κ₁) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀, ∀ s : ℝ,
      frontCurv (periodize y H) s ≤ κ₂ ∧
      periodize y H s / √(1 - periodize y H s ^ 2) ≤ κ₂ := by
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left ((hy0 0).trans (hyA 0)) (exp_pos _)
  have hb0 : 0 ≤ b := (hy0 0).trans (hyb 0)
  have hyA' : ∀ t, |y t| ≤ A * exp (-(a * |t|)) := fun t => by
    rw [abs_of_nonneg (hy0 t)]; exact hyA t
  have hy'A : ∀ t, |y' t| ≤ (|D| * A) * exp (-(a * |t|)) := fun t => by
    have h1 : D * y t ≤ |D| * y t := mul_le_mul_of_nonneg_right (le_abs_self D) (hy0 t)
    have h2 : |D| * y t ≤ |D| * (A * exp (-(a * |t|))) :=
      mul_le_mul_of_nonneg_left (hyA t) (abs_nonneg D)
    linarith [hyD t]
  have hpos : 0 < 1 - b ^ 2 := by nlinarith
  set c0 := √(1 - b ^ 2) with hc0def
  have hc0 : 0 < c0 := Real.sqrt_pos.2 hpos
  set A' := A + |D| * A / c0 with hA'def
  have hKA : ∀ t, |frontCurv y t| ≤ A' * exp (-(a * |t|)) := by
    intro t
    rw [frontCurv, (hy t).deriv]
    have hct : c0 ≤ √(1 - y t ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hyb t, hy0 t])
    have h1 : |y' t / √(1 - y t ^ 2)| ≤ |D| * A * exp (-(a * |t|)) / c0 := by
      rw [abs_div, abs_of_pos (lt_of_lt_of_le hc0 hct)]
      exact div_le_div₀ (by positivity) (hy'A t) hc0 hct
    calc |y t + y' t / √(1 - y t ^ 2)| ≤ |y t| + |y' t / √(1 - y t ^ 2)| := abs_add_le _ _
      _ ≤ A * exp (-(a * |t|)) + |D| * A * exp (-(a * |t|)) / c0 := add_le_add (hyA' t) h1
      _ = A' * exp (-(a * |t|)) := by rw [hA'def]; ring
  obtain ⟨C, β, L₀, hβ, hfe⟩ := front_error hy hy0 hyA ha hyD hyb hb
  set b' := (1 + b) / 2 with hb'def
  have hb' : b' < 1 := by rw [hb'def]; linarith
  set Lip := 1 / √(1 - b' ^ 2) + 1 / √(1 - b' ^ 2) ^ 3 with hLip
  -- eventual smallness
  have hexp : ∀ {r : ℝ}, 0 < r → Tendsto (fun H : ℝ => exp (-(r * H))) atTop (𝓝 0) :=
    fun hr => Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
  have ha2 : (0 : ℝ) < a / 2 := by positivity
  have t1 : Tendsto (fun H : ℝ => |C| * exp (-(β * H)) * (b + 8 * A * exp (-(a / 2 * H))) +
      8 * A' * exp (-(a / 2 * H))) atTop (𝓝 (|C| * 0 * (b + 8 * A * 0) + 8 * A' * 0)) :=
    ((((hexp hβ).const_mul _).mul (((hexp ha2).const_mul _).const_add _))).add
      ((hexp ha2).const_mul _)
  have t2 : Tendsto (fun H : ℝ => 8 * A * exp (-(a / 2 * H))) atTop (𝓝 (8 * A * 0)) :=
    (hexp ha2).const_mul _
  have t3 : Tendsto (fun H : ℝ => 8 * A * exp (-(a / 2 * H)) * Lip) atTop (𝓝 (8 * A * 0 * Lip)) :=
    t2.mul_const _
  simp only [mul_zero, zero_mul, add_zero] at t1 t2 t3
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.1 ((t1.eventually (gt_mem_nhds (sub_pos.2 hκ))).and
    ((t2.eventually (gt_mem_nhds (show (0 : ℝ) < (1 - b) / 2 by linarith))).and
      (t3.eventually (gt_mem_nhds (sub_pos.2 hκ)))))
  refine ⟨max (max (2 / a) L₀) H₁, fun H hH s => ?_⟩
  have hHa : 2 / a ≤ H := (le_max_left _ _).trans ((le_max_left _ _).trans hH)
  have hHL : L₀ ≤ H := (le_max_right _ _).trans ((le_max_left _ _).trans hH)
  have hH1 : H₁ ≤ H := (le_max_right _ _).trans hH
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hHa
  obtain ⟨hs1, hs2, hs3⟩ := hH₁ H hH1
  set Y := periodize y H with hYdef
  set E := 8 * A * exp (-(a / 2 * H)) with hE
  have hYd : ∀ t, HasDerivAt Y (periodize y' H t) t :=
    hasDerivAt_periodize hy hyA' hy'A ha hH0
  obtain ⟨k, hk⟩ := exists_int_cell hH0 s
  set s' := s - k * H with hs'
  have hYs : Y s' = Y s := periodize_sub_int_mul y H s k
  have hKs : frontCurv Y s' = frontCurv Y s := by
    unfold frontCurv
    rw [hYs, (hYd s').deriv, (hYd s).deriv, periodize_sub_int_mul y' H s k]
  rw [← hKs, ← hYs]
  have hY0 : 0 ≤ Y s' := tsum_nonneg fun m => hy0 _
  have hYle : Y s' ≤ b + E := periodize_le hyA' ha hyb hHa s'
  constructor
  · obtain ⟨-, hfe'⟩ := hfe H hHL s'
    have hcell := periodize_sub_le_explicit hKA ha hHa hk
    have e1 : periodize (frontCurv y) H s' = ∑' m : ℤ, frontCurv y (s' - m * H) := rfl
    rw [e1] at hcell
    have h1 := (abs_le.1 hfe').2
    have h2 := (abs_le.1 hcell).2
    have h3 : C * exp (-(β * H)) * Y s' ≤ |C| * exp (-(β * H)) * (b + E) := by
      have : C * exp (-(β * H)) ≤ |C| * exp (-(β * H)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (exp_pos _).le
      calc C * exp (-(β * H)) * Y s' ≤ |C| * exp (-(β * H)) * Y s' :=
            mul_le_mul_of_nonneg_right this hY0
        _ ≤ |C| * exp (-(β * H)) * (b + E) :=
            mul_le_mul_of_nonneg_left hYle (by positivity)
    have h4 := hKF s'
    linarith
  · have hcell := periodize_sub_le_explicit hyA' ha hHa hk
    have hYb' : Y s' ≤ b' := by rw [hb'def]; linarith
    have hyb' : y s' ≤ b' := by rw [hb'def]; linarith [hyb s']
    have hL := div_sqrt_one_sub_sq_lipschitz hb' hY0 hYb' (hy0 s') hyb'
    have hLip0 : 0 ≤ Lip := by positivity
    have h1 : |Y s' - y s'| * Lip ≤ E * Lip := mul_le_mul_of_nonneg_right hcell hLip0
    have h2 := (abs_le.1 hL).2
    have h3 := hKR s'
    linarith

end Ovals

end
