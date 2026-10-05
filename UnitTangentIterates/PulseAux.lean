module

public import Mathlib

/-!
# Auxiliary facts for Lemma 3.5

* Global inverses of functions `ℝ → ℝ` whose derivative is bounded below by a positive
  constant (`exists_inverse_of_deriv_ge`).
* The angle map `T v = 2 arctan (eᵛ)`, a diffeomorphism `ℝ → (0, π)` with
  `sin (T v) = 1 / cosh v` and `T' = sin ∘ T`; its inverse is `log (tan (θ/2))`.
-/

@[expose] public section

namespace Ovals

open Real Set Filter Topology

/-- A function with derivative bounded below by `c > 0` has a global differentiable inverse. -/
theorem exists_inverse_of_deriv_ge {F F' : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hF' : ∀ x, c ≤ F' x) :
    ∃ G : ℝ → ℝ, (∀ y, F (G y) = y) ∧ (∀ x, G (F x) = x) ∧
      (∀ y, HasDerivAt G (F' (G y))⁻¹ y) := by
  have hcont : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hmono : StrictMono F := strictMono_of_hasDerivAt_pos hF fun x => hc.trans_le (hF' x)
  -- lower bound `F x - F 0 ≥ c x` for `x ≥ 0` and the symmetric one
  have hlow : ∀ x y, x ≤ y → c * (y - x) ≤ F y - F x := by
    have hm : Monotone (fun t => F t - c * t) :=
      monotone_of_hasDerivAt_nonneg (f' := fun t => F' t - c)
        (fun t => (hF t).sub ((hasDerivAt_id t).const_mul c |>.congr_deriv (by simp)))
        (fun t => by show 0 ≤ F' t - c; linarith [hF' t])
    intro x y hxy
    have := hm hxy
    simp only at this; linarith
  have hsurj : Function.Surjective F := by
    intro y
    have h1 : F (-(|y - F 0| / c)) ≤ y := by
      have := hlow (-(|y - F 0| / c)) 0 (by
        have := abs_nonneg (y - F 0); have : 0 ≤ |y - F 0| / c := by positivity
        linarith)
      have e : c * (0 - -(|y - F 0| / c)) = |y - F 0| := by field_simp; ring
      rw [e] at this; linarith [neg_abs_le (y - F 0)]
    have h2 : y ≤ F (|y - F 0| / c) := by
      have := hlow 0 (|y - F 0| / c) (by have := abs_nonneg (y - F 0); positivity)
      have e : c * (|y - F 0| / c - 0) = |y - F 0| := by field_simp; ring
      rw [e] at this; linarith [le_abs_self (y - F 0)]
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc (by
      have := abs_nonneg (y - F 0)
      have : 0 ≤ |y - F 0| / c := by positivity
      linarith) hcont.continuousOn ⟨h1, h2⟩
    exact ⟨x, hx⟩
  set e := StrictMono.orderIsoOfSurjective F hmono hsurj with he
  refine ⟨e.symm, fun y => ?_, fun x => ?_, fun y => ?_⟩
  · exact e.apply_symm_apply y
  · exact e.symm_apply_apply x
  · have hGc : Continuous e.symm := e.symm.continuous
    refine HasDerivAt.of_local_left_inverse hGc.continuousAt (hF _) ?_
      (Eventually.of_forall fun y => e.apply_symm_apply y)
    exact (hc.trans_le (hF' _)).ne'

/-- The angle map `T v = 2 arctan (eᵛ) ∈ (0, π)`. -/
noncomputable def angleMap (v : ℝ) : ℝ := 2 * Real.arctan (Real.exp v)

/-- Its inverse `log (tan (θ/2))`. -/
noncomputable def angleMapInv (θ : ℝ) : ℝ := Real.log (Real.tan (θ / 2))

theorem angleMap_mem (v : ℝ) : angleMap v ∈ Ioo 0 π := by
  unfold angleMap
  have h1 := Real.arctan_pos.2 (Real.exp_pos v)
  have h2 := Real.arctan_lt_pi_div_two (Real.exp v)
  constructor <;> linarith

theorem sin_angleMap (v : ℝ) : Real.sin (angleMap v) = 1 / Real.cosh v := by
  unfold angleMap
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan, Real.cosh_eq]
  have h : 0 < 1 + Real.exp v ^ 2 := by positivity
  have hs : Real.sqrt (1 + Real.exp v ^ 2) ^ 2 = 1 + Real.exp v ^ 2 := Real.sq_sqrt h.le
  have hs0 : 0 < Real.sqrt (1 + Real.exp v ^ 2) := Real.sqrt_pos.2 h
  have hne : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  rw [hs]
  have : Real.exp (-v) = (Real.exp v)⁻¹ := by rw [Real.exp_neg]
  rw [this]; field_simp; ring

theorem hasDerivAt_angleMap (v : ℝ) :
    HasDerivAt angleMap (Real.sin (angleMap v)) v := by
  unfold angleMap
  have h := ((Real.hasDerivAt_exp v).arctan).const_mul 2
  convert h using 1
  rw [← angleMap, sin_angleMap, Real.cosh_eq]
  have h1 : 0 < Real.exp v := Real.exp_pos v
  have : Real.exp (-v) = (Real.exp v)⁻¹ := by rw [Real.exp_neg]
  rw [this]; field_simp; ring

theorem angleMap_angleMapInv {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : angleMap (angleMapInv θ) = θ := by
  unfold angleMap angleMapInv
  have h0 : 0 < θ / 2 := by linarith [hθ.1]
  have h1 : θ / 2 < π / 2 := by linarith [hθ.2]
  have ht : 0 < Real.tan (θ / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two h0 h1
  rw [Real.exp_log ht, Real.arctan_tan (by linarith) h1]; ring

theorem angleMapInv_angleMap (v : ℝ) : angleMapInv (angleMap v) = v := by
  unfold angleMap angleMapInv
  rw [show 2 * Real.arctan (Real.exp v) / 2 = Real.arctan (Real.exp v) by ring,
    Real.tan_arctan, Real.log_exp]

theorem hasDerivAt_angleMapInv {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt angleMapInv (1 / Real.sin θ) θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hd : HasDerivAt angleMap (Real.sin θ) (angleMapInv θ) := by
    have := hasDerivAt_angleMap (angleMapInv θ); rwa [angleMap_angleMapInv hθ] at this
  have h := HasDerivAt.of_local_left_inverse (f := angleMap) (g := angleMapInv) (a := θ)
    ?_ hd hs.ne' ?_
  · simpa [one_div] using h
  · have h0 : 0 < θ / 2 := by linarith [hθ.1]
    have h1 : θ / 2 < π / 2 := by linarith [hθ.2]
    have ht : 0 < Real.tan (θ / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two h0 h1
    have hc : Real.cos (θ / 2) ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩).ne'
    unfold angleMapInv
    exact ((Real.continuousAt_tan.2 hc).comp (f := fun x : ℝ => x / 2) (by fun_prop)).log ht.ne'
  · filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact angleMap_angleMapInv hx

/-- `1 / cosh v ≤ 2 e^{-|v|}`. -/
theorem inv_cosh_le (v : ℝ) : 1 / Real.cosh v ≤ 2 * Real.exp (-|v|) := by
  have hc : 0 < Real.cosh v := Real.cosh_pos v
  rw [div_le_iff₀ hc, Real.cosh_eq]
  rcases le_total 0 v with h | h
  · rw [abs_of_nonneg h]
    have : Real.exp (-v) * Real.exp v = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-v), Real.exp_pos v]
  · rw [abs_of_nonpos h, neg_neg]
    have : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-v), Real.exp_pos v]

/-- `cosh v ≤ e^{|w|} cosh (v + w)`. -/
theorem cosh_le_exp_mul_cosh (v w : ℝ) :
    Real.cosh v ≤ Real.exp |w| * Real.cosh (v + w) := by
  rw [Real.cosh_eq, Real.cosh_eq, Real.exp_add, Real.exp_neg (v + w), Real.exp_add]
  have ha := Real.exp_pos v
  have hb := Real.exp_pos w
  have hw := Real.exp_pos |w|
  have h1 : Real.exp w ≤ Real.exp |w| := Real.exp_le_exp.2 (le_abs_self w)
  have h2 : Real.exp (-w) ≤ Real.exp |w| := Real.exp_le_exp.2 (neg_le_abs w)
  have h3 : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
  have h4 : Real.exp (-v) = (Real.exp v)⁻¹ := Real.exp_neg v
  rw [h4]
  have h5 : Real.exp |w| * Real.exp w ≥ 1 := by nlinarith
  have h6 : Real.exp |w| * (Real.exp w)⁻¹ ≥ 1 := by
    rw [← Real.exp_neg] ; nlinarith
  rw [mul_inv]
  have hinv : 0 < (Real.exp v)⁻¹ := inv_pos.2 ha
  nlinarith [mul_le_mul_of_nonneg_left h5.le ha.le, mul_le_mul_of_nonneg_left h6.le hinv.le]

end Ovals

end
