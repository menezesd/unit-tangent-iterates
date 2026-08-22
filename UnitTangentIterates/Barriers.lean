import Mathlib

/-!
# The explicit barriers

This file formalizes the algebraic content of Lemma 3.3 (*Explicit barriers*)
of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*:

* the ordering of the two barrier profiles and their minima on `[0, π]`;
* the sign dictionary between the residual `ℛ(f) = ∫_θ^{θ+d_f} f - sin θ` and
  the comparison `𝒫f ≥ f`;
* the exact residual identity for a profile of the form `A + B cos θ` and the
  exact factorization through the three functions `Φ₀, Φ₁, Φ₂`;
* the analytic values `Φ₀(0) = -2/3`, `Φ₁(0) = -1`, `Φ₂(0) = -1/3` of those
  functions at the origin, obtained as limits.
-/

noncomputable section

open Real Set

namespace Barriers

/-- The base profile `u₀(θ) = (2/3)(1 - cos θ)`. -/
noncomputable def u0 (θ : ℝ) : ℝ := 2 / 3 * (1 - Real.cos θ)

/-- The lower barrier `f_ε⁻ = ε⁻¹ + u₀ - ε cos θ`. -/
noncomputable def fMinus (ε θ : ℝ) : ℝ := ε⁻¹ + u0 θ + ε * (-Real.cos θ)

/-- The upper barrier `f_ε⁺ = ε⁻¹ + u₀ + ε (cos θ + 2)`. -/
noncomputable def fPlus (ε θ : ℝ) : ℝ := ε⁻¹ + u0 θ + ε * (Real.cos θ + 2)

/-- The barriers are ordered, with `f⁺ - f⁻ = 2ε(1 + cos θ)`. -/
theorem fPlus_sub_fMinus (ε θ : ℝ) :
    fPlus ε θ - fMinus ε θ = 2 * ε * (1 + Real.cos θ) := by
  simp [fPlus, fMinus]
  ring

theorem fMinus_le_fPlus {ε : ℝ} (hε : 0 < ε) (θ : ℝ) : fMinus ε θ ≤ fPlus ε θ := by
  have h := fPlus_sub_fMinus ε θ
  have h2 : 0 ≤ 2 * ε * (1 + Real.cos θ) := by
    have := Real.neg_one_le_cos θ
    nlinarith
  linarith

/-- The minimum of the lower barrier on `[0, π]` is `ε⁻¹ - ε`, attained at
`θ = 0`. -/
theorem fMinus_min {ε : ℝ} (hε : 0 < ε) :
    (∀ θ, ε⁻¹ - ε ≤ fMinus ε θ) ∧ fMinus ε 0 = ε⁻¹ - ε := by
  constructor
  · intro θ
    have hc := Real.cos_le_one θ
    have : 0 ≤ (1 - Real.cos θ) * (2 / 3 + ε) := by nlinarith
    simp only [fMinus, u0]
    nlinarith
  · simp [fMinus, u0]
    ring

/-- For `ε ≤ 2/3` the minimum of the upper barrier on `[0, π]` is `ε⁻¹ + 3ε`,
attained at `θ = 0`. -/
theorem fPlus_min {ε : ℝ} (hε' : ε ≤ 2 / 3) :
    (∀ θ, ε⁻¹ + 3 * ε ≤ fPlus ε θ) ∧ fPlus ε 0 = ε⁻¹ + 3 * ε := by
  constructor
  · intro θ
    have hc := Real.cos_le_one θ
    have : 0 ≤ (1 - Real.cos θ) * (2 / 3 - ε) := by nlinarith
    simp only [fPlus, u0]
    nlinarith
  · simp [fPlus, u0]
    ring

section Residual

/-- The residual `ℛ(f) = ∫_θ^{θ+d} f - sin θ` of a profile `f` at the angle
`θ`, evaluated with the steering shift `d`. -/
noncomputable def residual (f : ℝ → ℝ) (θ d : ℝ) : ℝ := (∫ t in θ..(θ + d), f t) - Real.sin θ

/-- **The exact residual identity** for a profile `f = A + B cos`. -/
theorem residual_affine_cos (A B θ d : ℝ) :
    residual (fun t => A + B * Real.cos t) θ d
      = A * d + B * (Real.sin θ * (Real.cos d - 1) + Real.cos θ * Real.sin d)
        - Real.sin θ := by
  have hint : (∫ t in θ..(θ + d), (A + B * Real.cos t))
      = A * d + B * (Real.sin (θ + d) - Real.sin θ) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((intervalIntegral.intervalIntegrable_cos).const_mul B)]
    rw [intervalIntegral.integral_const_mul, integral_cos,
      intervalIntegral.integral_const]
    simp
    ring
  rw [residual, hint, Real.sin_add]
  ring

/-- **The sign dictionary.**  If the mass time `Df` realizes `∫_θ^{θ+Df} f = sin θ`
and `d > 0`, then the residual at `d` is nonnegative exactly when `Df ≤ d`. -/
theorem residual_nonneg_iff {f : ℝ → ℝ} {θ Df d : ℝ}
    (hf0 : ∀ t, 0 < f t)
    (hIf : ∫ t in θ..(θ + Df), f t = Real.sin θ)
    (hfint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b) :
    0 ≤ residual f θ d ↔ Df ≤ d := by
  have hsplit : (∫ t in θ..(θ + d), f t)
      = (∫ t in θ..(θ + Df), f t) + ∫ t in (θ + Df)..(θ + d), f t :=
    (intervalIntegral.integral_add_adjacent_intervals (hfint _ _) (hfint _ _)).symm
  have hres : residual f θ d = ∫ t in (θ + Df)..(θ + d), f t := by
    rw [residual, hsplit, hIf]
    ring
  rw [hres]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hneg : 0 < ∫ t in (θ + d)..(θ + Df), f t :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hfint _ _)
        (fun x _ => hf0 x) (by linarith)
    rw [intervalIntegral.integral_symm] at hneg
    linarith
  · intro h
    apply intervalIntegral.integral_nonneg (by linarith)
    intro x _
    exact (hf0 x).le

end Residual

section Phi

/-- `Φ₀(r) = 2(√r / tan √r - 1)/r`. -/
noncomputable def Phi0 (r : ℝ) : ℝ := 2 * (Real.sqrt r / Real.tan (Real.sqrt r) - 1) / r

/-- `Φ₁(r) = 2(cos √r - 1)/r`. -/
noncomputable def Phi1 (r : ℝ) : ℝ := 2 * (Real.cos (Real.sqrt r) - 1) / r

/-- `Φ₂(r) = 2(sin √r - √r)/(r tan √r)`. -/
noncomputable def Phi2 (r : ℝ) : ℝ :=
  2 * (Real.sin (Real.sqrt r) - Real.sqrt r) / (r * Real.tan (Real.sqrt r))

/-- **The exact factorization of the normalized residual.**  For `0 < d < π/2`, `0 < s`, and a
profile value `F = s cot d = A + B cos θ`, the normalized residual factors
through `Φ₀, Φ₁, Φ₂`. -/
theorem residual_factorization {A B d s c F : ℝ}
    (hd0 : 0 < d) (hd : d < π / 2)
    (hspos : 0 < s) (hF : F = s * (Real.cos d / Real.sin d)) (hAB : F = A + B * c) :
    2 * (A * d + B * (s * (Real.cos d - 1) + c * Real.sin d) - s) / (d ^ 2 * s)
      = Phi0 (d ^ 2) + B * Phi1 (d ^ 2) + (B * c / F) * Phi2 (d ^ 2) := by
  have hpi := Real.pi_pos
  have hsqrt : Real.sqrt (d ^ 2) = d := by
    rw [Real.sqrt_sq hd0.le]
  have hsd : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith)
  have hcd : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo ⟨by linarith, hd⟩
  simp only [Phi0, Phi1, Phi2, hsqrt, Real.tan_eq_sin_div_cos]
  have hA : A = F - B * c := by linarith
  have hFpos : 0 < F := by rw [hF]; positivity
  subst hA
  rw [hF]
  field_simp
  ring

open Filter Topology in
/-- A squeeze principle at `0` from the right. -/
lemma tendsto_nhdsGT_of_abs_le {f g : ℝ → ℝ} {L : ℝ}
    (h : ∀ᶠ x in 𝓝[>](0:ℝ), |f x - L| ≤ g x)
    (hg : Tendsto g (𝓝[>](0:ℝ)) (𝓝 0)) :
    Tendsto f (𝓝[>](0:ℝ)) (𝓝 L) := by
  have h0 : Tendsto (fun x => f x - L) (𝓝[>](0:ℝ)) (𝓝 0) :=
    squeeze_zero_norm' (by simpa using h) hg
  simpa using h0.add (tendsto_const_nhds (x := L) (f := 𝓝[>](0:ℝ)))

open Filter Topology in
lemma tendsto_linear_nhdsGT (C : ℝ) (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => C * x ^ n) (𝓝[>](0:ℝ)) (𝓝 0) := by
  have hcont : Continuous (fun x : ℝ => C * x ^ n) := by fun_prop
  have h : Tendsto (fun x : ℝ => C * x ^ n) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa [zero_pow hn] using hcont.tendsto (0:ℝ)
  exact h.mono_left nhdsWithin_le_nhds

open Filter Topology in
/-- `(cos x - 1)/x² → -1/2` as `x ↓ 0`. -/
lemma tendsto_cos_sub_one_div_sq :
    Tendsto (fun x : ℝ => (Real.cos x - 1) / x ^ 2) (𝓝[>](0:ℝ)) (𝓝 (-(1/2))) := by
  refine tendsto_nhdsGT_of_abs_le (g := fun x => (5/96) * x ^ 2) ?_
    (tendsto_linear_nhdsGT _ 2 (by norm_num))
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have habs : |x| ≤ 1 := by rw [abs_of_pos hx0]; linarith
  have hc := Real.cos_bound habs
  rw [abs_of_pos hx0] at hc
  have heq : (Real.cos x - 1) / x ^ 2 - (-(1/2)) = (Real.cos x - (1 - x ^ 2 / 2)) / x ^ 2 := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (by positivity : (0:ℝ) < x ^ 2),
    div_le_iff₀ (by positivity : (0:ℝ) < x ^ 2)]
  calc |Real.cos x - (1 - x ^ 2 / 2)| ≤ x ^ 4 * (5/96) := hc
    _ = 5/96 * x ^ 2 * x ^ 2 := by ring

open Filter Topology in
/-- `(sin x - x)/x³ → -1/6` as `x ↓ 0`. -/
lemma tendsto_sin_sub_self_div_cube :
    Tendsto (fun x : ℝ => (Real.sin x - x) / x ^ 3) (𝓝[>](0:ℝ)) (𝓝 (-(1/6))) := by
  refine tendsto_nhdsGT_of_abs_le (g := fun x => (5/96) * x ^ 1) ?_
    (tendsto_linear_nhdsGT _ 1 (by norm_num))
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have habs : |x| ≤ 1 := by rw [abs_of_pos hx0]; linarith
  have hs := Real.sin_bound habs
  rw [abs_of_pos hx0] at hs
  have heq : (Real.sin x - x) / x ^ 3 - (-(1/6)) = (Real.sin x - (x - x ^ 3 / 6)) / x ^ 3 := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (by positivity : (0:ℝ) < x ^ 3),
    div_le_iff₀ (by positivity : (0:ℝ) < x ^ 3)]
  calc |Real.sin x - (x - x ^ 3 / 6)| ≤ x ^ 4 * (5/96) := hs
    _ = 5/96 * x ^ 1 * x ^ 3 := by ring

open Filter Topology in
/-- `(x cos x - sin x)/x³ → -1/3` as `x ↓ 0`. -/
lemma tendsto_mul_cos_sub_sin_div_cube :
    Tendsto (fun x : ℝ => (x * Real.cos x - Real.sin x) / x ^ 3) (𝓝[>](0:ℝ)) (𝓝 (-(1/3))) := by
  refine tendsto_nhdsGT_of_abs_le (g := fun x => (5/48) * x ^ 1) ?_
    (tendsto_linear_nhdsGT _ 1 (by norm_num))
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have habs : |x| ≤ 1 := by rw [abs_of_pos hx0]; linarith
  have hc := Real.cos_bound habs
  have hs := Real.sin_bound habs
  rw [abs_of_pos hx0] at hc hs
  have heq : (x * Real.cos x - Real.sin x) / x ^ 3 - (-(1/3))
      = (x * (Real.cos x - (1 - x ^ 2 / 2)) - (Real.sin x - (x - x ^ 3 / 6))) / x ^ 3 := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (by positivity : (0:ℝ) < x ^ 3),
    div_le_iff₀ (by positivity : (0:ℝ) < x ^ 3)]
  have htri : |x * (Real.cos x - (1 - x ^ 2 / 2)) - (Real.sin x - (x - x ^ 3 / 6))|
      ≤ |x| * |Real.cos x - (1 - x ^ 2 / 2)| + |Real.sin x - (x - x ^ 3 / 6)| := by
    calc |x * (Real.cos x - (1 - x ^ 2 / 2)) - (Real.sin x - (x - x ^ 3 / 6))|
        ≤ |x * (Real.cos x - (1 - x ^ 2 / 2))| + |Real.sin x - (x - x ^ 3 / 6)| :=
          abs_sub _ _
      _ = |x| * |Real.cos x - (1 - x ^ 2 / 2)| + |Real.sin x - (x - x ^ 3 / 6)| := by
          rw [abs_mul]
  rw [abs_of_pos hx0] at htri
  have hx5 : x ^ 5 ≤ x ^ 4 := by nlinarith [pow_pos hx0 4]
  have hbound : x * |Real.cos x - (1 - x ^ 2 / 2)| ≤ x ^ 5 * (5/96) := by
    have := mul_le_mul_of_nonneg_left hc hx0.le
    calc x * |Real.cos x - (1 - x ^ 2 / 2)| ≤ x * (x ^ 4 * (5/96)) := this
      _ = x ^ 5 * (5/96) := by ring
  calc |x * (Real.cos x - (1 - x ^ 2 / 2)) - (Real.sin x - (x - x ^ 3 / 6))|
      ≤ x * |Real.cos x - (1 - x ^ 2 / 2)| + |Real.sin x - (x - x ^ 3 / 6)| := htri
    _ ≤ x ^ 5 * (5/96) + x ^ 4 * (5/96) := by linarith
    _ ≤ x ^ 4 * (5/96) + x ^ 4 * (5/96) := by linarith
    _ = 5/48 * x ^ 1 * x ^ 3 := by ring

open Filter Topology in
/-- `x / sin x → 1` as `x ↓ 0`. -/
lemma tendsto_self_div_sin :
    Tendsto (fun x : ℝ => x / Real.sin x) (𝓝[>](0:ℝ)) (𝓝 1) := by
  have hsinc : Tendsto Real.sinc (𝓝 (0:ℝ)) (𝓝 1) := by
    have := Real.continuous_sinc.tendsto (0:ℝ)
    simpa [Real.sinc] using this
  have h1 : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[>](0:ℝ)) (𝓝 1) := by
    refine (hsinc.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sinc_of_ne_zero (ne_of_gt hx)
  have h2 : Tendsto (fun x : ℝ => (Real.sin x / x)⁻¹) (𝓝[>](0:ℝ)) (𝓝 1) := by
    simpa using h1.inv₀ (by norm_num)
  refine h2.congr ?_
  intro x
  rw [inv_div]

open Filter Topology in
/-- The square root tends to `0` from the right along `0⁺`. -/
lemma tendsto_sqrt_nhdsGT : Tendsto Real.sqrt (𝓝[>](0:ℝ)) (𝓝[>](0:ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : Tendsto Real.sqrt (𝓝 (0:ℝ)) (𝓝 0) := by
      simpa using Real.continuous_sqrt.tendsto (0:ℝ)
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact Real.sqrt_pos.mpr hr

open Filter Topology in
/-- Value of `Φ₀` at `r = x²`. -/
lemma Phi0_eq_of_sq {r x : ℝ} (hx : 0 < x) (hr : r = x ^ 2)
    (hsin : 0 < Real.sin x) :
    Phi0 r = 2 * ((x * Real.cos x - Real.sin x) / x ^ 3) * (x / Real.sin x) := by
  have hsx : Real.sqrt r = x := by rw [hr, Real.sqrt_sq hx.le]
  rw [Phi0, hsx, hr, Real.tan_eq_sin_div_cos]
  field_simp

/-- Value of `Φ₁` at `r = x²`. -/
lemma Phi1_eq_of_sq {r x : ℝ} (hx : 0 < x) (hr : r = x ^ 2) :
    Phi1 r = 2 * ((Real.cos x - 1) / x ^ 2) := by
  have hsx : Real.sqrt r = x := by rw [hr, Real.sqrt_sq hx.le]
  rw [Phi1, hsx, hr]
  ring

/-- Value of `Φ₂` at `r = x²`. -/
lemma Phi2_eq_of_sq {r x : ℝ} (hx : 0 < x) (hr : r = x ^ 2)
    (hsin : 0 < Real.sin x) (hcos : 0 < Real.cos x) :
    Phi2 r = 2 * ((Real.sin x - x) / x ^ 3) * (x / Real.sin x * Real.cos x) := by
  have hsx : Real.sqrt r = x := by rw [hr, Real.sqrt_sq hx.le]
  rw [Phi2, hsx, hr, Real.tan_eq_sin_div_cos]
  field_simp

open Filter Topology in
/-- `Φ₁` extends analytically through `r = 0` with value `-1`. -/
theorem tendsto_Phi1 : Tendsto Phi1 (𝓝[>](0:ℝ)) (𝓝 (-1)) := by
  have hcomp : Tendsto (fun x : ℝ => 2 * ((Real.cos x - 1) / x ^ 2)) (𝓝[>](0:ℝ))
      (𝓝 (2 * (-(1/2)))) := tendsto_cos_sub_one_div_sq.const_mul (2:ℝ)
  have hval : (2:ℝ) * (-(1/2)) = -1 := by norm_num
  rw [hval] at hcomp
  refine (hcomp.comp tendsto_sqrt_nhdsGT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hx0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  exact (Phi1_eq_of_sq hx0 (Real.sq_sqrt (le_of_lt hr)).symm).symm

open Filter Topology in
/-- `Φ₀` extends analytically through `r = 0` with value `-2/3`. -/
theorem tendsto_Phi0 : Tendsto Phi0 (𝓝[>](0:ℝ)) (𝓝 (-(2/3))) := by
  have hcomp : Tendsto
      (fun x : ℝ => 2 * ((x * Real.cos x - Real.sin x) / x ^ 3) * (x / Real.sin x))
      (𝓝[>](0:ℝ)) (𝓝 (2 * (-(1/3)) * 1)) :=
    (tendsto_mul_cos_sub_sin_div_cube.const_mul (2:ℝ)).mul tendsto_self_div_sin
  have hval : (2:ℝ) * (-(1/3)) * 1 = -(2/3) := by norm_num
  rw [hval] at hcomp
  refine (hcomp.comp tendsto_sqrt_nhdsGT).congr' ?_
  filter_upwards [self_mem_nhdsWithin, tendsto_sqrt_nhdsGT.eventually
      (Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0:ℝ) < π / 2))] with r hr hsr
  have hx0 : 0 < Real.sqrt r := hsr.1
  have hsin : 0 < Real.sin (Real.sqrt r) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos, hsr.2])
  exact (Phi0_eq_of_sq hx0 (Real.sq_sqrt (le_of_lt hr)).symm hsin).symm

open Filter Topology in
/-- `Φ₂` extends analytically through `r = 0` with value `-1/3`. -/
theorem tendsto_Phi2 : Tendsto Phi2 (𝓝[>](0:ℝ)) (𝓝 (-(1/3))) := by
  have hcos1 : Tendsto (fun x : ℝ => Real.cos x) (𝓝[>](0:ℝ)) (𝓝 1) := by
    have h : Tendsto (fun x : ℝ => Real.cos x) (𝓝 (0:ℝ)) (𝓝 1) := by
      simpa using Real.continuous_cos.tendsto (0:ℝ)
    exact h.mono_left nhdsWithin_le_nhds
  have hcomp : Tendsto
      (fun x : ℝ => 2 * ((Real.sin x - x) / x ^ 3) * (x / Real.sin x * Real.cos x))
      (𝓝[>](0:ℝ)) (𝓝 (2 * (-(1/6)) * (1 * 1))) :=
    (tendsto_sin_sub_self_div_cube.const_mul (2:ℝ)).mul (tendsto_self_div_sin.mul hcos1)
  have hval : (2:ℝ) * (-(1/6)) * (1 * 1) = -(1/3) := by norm_num
  rw [hval] at hcomp
  refine (hcomp.comp tendsto_sqrt_nhdsGT).congr' ?_
  filter_upwards [self_mem_nhdsWithin, tendsto_sqrt_nhdsGT.eventually
      (Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0:ℝ) < π / 2))] with r hr hsr
  have hx0 : 0 < Real.sqrt r := hsr.1
  have hsin : 0 < Real.sin (Real.sqrt r) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos, hsr.2])
  have hcos : 0 < Real.cos (Real.sqrt r) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hsr.2⟩
  exact (Phi2_eq_of_sq hx0 (Real.sq_sqrt (le_of_lt hr)).symm hsin hcos).symm

end Phi

end Barriers
