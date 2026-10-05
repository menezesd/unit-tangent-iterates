module

public import UnitTangentIterates.ShadowIntrinsic

/-!
# Regularity of the selected inverse

For an admissible normalized oval `(L, f)` with curvature bound `κ < 1`:

* the curvature `rearF L f` of the selected inverse is Lipschitz with constant
  `L / cos³ (arcsin κ)` (`Ovals.rearF_lipschitz`);
* if `f` is `C^r` then `rearF L f` is `C^{r+1}` (`Ovals.rearF_contDiff`), and the inverse of the
  rear arclength is `C^{r+2}` (`Ovals.rearInv_contDiff`).
-/

@[expose] public section

namespace Ovals

open Real

/-- `tan` is Lipschitz with constant `1 / cos² A` on `[0, A]`. -/
lemma abs_tan_sub_le {A a b : ℝ} (hA : A < π / 2) (ha : a ∈ Set.Icc 0 A)
    (hb : b ∈ Set.Icc 0 A) : |Real.tan a - Real.tan b| ≤ |a - b| / Real.cos A ^ 2 := by
  have hcA : 0 < Real.cos A := Real.cos_pos_of_mem_Ioo ⟨by linarith [ha.1, ha.2, Real.pi_pos], hA⟩
  have hcos : ∀ x ∈ Set.Icc 0 A, Real.cos A ≤ Real.cos x := fun x hx =>
    Real.cos_le_cos_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos]) hx.2
  have hpos : ∀ x ∈ Set.Icc 0 A, 0 < Real.cos x := fun x hx => hcA.trans_le (hcos x hx)
  have := (convex_Icc 0 A).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.tan) (f' := fun x => 1 / Real.cos x ^ 2) (C := 1 / Real.cos A ^ 2)
    (fun x hx => (Real.hasDerivAt_tan (hpos x hx).ne').hasDerivWithinAt) (fun x hx => by
      rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos (pow_pos (hpos x hx) 2)]
      exact one_div_le_one_div_of_le (pow_pos hcA 2) (pow_le_pow_left₀ hcA.le (hcos x hx) 2))
    hb ha
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  calc |Real.tan a - Real.tan b| ≤ 1 / Real.cos A ^ 2 * |a - b| := this
    _ = |a - b| / Real.cos A ^ 2 := by ring

/-- Bootstrapping regularity: if `C^k`-regularity of `h` implies that of `h'` for `k ≤ m`, then
`h` is `C^{m+1}`. -/
lemma contDiff_bootstrap {h : ℝ → ℝ} (hd : Differentiable ℝ h) (m : ℕ)
    (H : ∀ k : ℕ, k ≤ m → ContDiff ℝ k h → ContDiff ℝ k (deriv h)) :
    ContDiff ℝ (m + 1 : ℕ) h := by
  have : ∀ k : ℕ, k ≤ m + 1 → ContDiff ℝ k h := by
    intro k
    induction k with
    | zero => intro; exact contDiff_zero.2 hd.continuous
    | succ k ih =>
      intro hk
      have h1 := H k (by omega) (ih (by omega))
      rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl]
      exact contDiff_succ_iff_deriv.2 ⟨hd, by simp, h1⟩
  exact this _ le_rfl

section

variable {κ L : ℝ} {f : ℝ → ℝ}

/-- Basic arclength facts used below. -/
lemma rear_arc_basic (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    let δ := fun s => rδ L f (s / L)
    let x := fun s => ∫ r in (0 : ℝ)..s, Real.cos (δ r)
    0 < Real.cos (Real.arcsin κ) ∧ (∀ s, Real.cos (Real.arcsin κ) ≤ Real.cos (δ s)) ∧
      Continuous δ ∧ (∀ s, HasDerivAt x (Real.cos (δ s)) s) ∧
      (∀ s s', |δ s - δ s'| ≤ |s - s'|) ∧
      (∀ s s', |s - s'| ≤ |x s - x s'| / Real.cos (Real.arcsin κ)) := by
  intro δ x
  obtain ⟨hKc, hKp, hKi, hδd, hδp, hδb, hδpos, hkc, hkp, hki, hxL, hRL, hkx⟩ :=
    rear_arclength hA hκ0 hκ1
  have hA2 := arcsin_lt_pi_div_two hκ1
  have hcA : 0 < Real.cos (Real.arcsin κ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.arcsin_nonneg.2 hκ0, Real.pi_pos], hA2⟩
  have hcos : ∀ s, Real.cos (Real.arcsin κ) ≤ Real.cos (δ s) := fun s =>
    Real.cos_le_cos_of_nonneg_of_le_pi (hδb s).1 (by linarith [Real.pi_pos]) (hδb s).2
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun s => (hδd s).continuousAt
  have hcc : Continuous fun r => Real.cos (δ r) := Real.continuous_cos.comp hδc
  have hx : ∀ s, HasDerivAt x (Real.cos (δ s)) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hcc.intervalIntegrable _ _)
      (hcc.stronglyMeasurableAtFilter _ _) hcc.continuousAt
  refine ⟨hcA, hcos, hδc, hx, fun s s' => ?_, fun s s' => ?_⟩
  · have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := δ) (C := 1)
      (fun x _ => (hδd x).hasDerivWithinAt) (fun r _ => ?_) (Set.mem_univ s') (Set.mem_univ s)
    · simpa [Real.norm_eq_abs] using this
    · have h1 := hA.2.2.2.1 (r / L)
      have h2 : 0 ≤ Real.sin (δ r) := Real.sin_nonneg_of_nonneg_of_le_pi (hδb r).1
        (by linarith [(hδb r).2, Real.pi_pos])
      have h3 := Real.sin_le_one (δ r)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [h1.1, h1.2]
  · -- `x - c · id` is monotone
    have hmono : Monotone fun s => x s - Real.cos (Real.arcsin κ) * s := by
      have hd : ∀ s, HasDerivAt (fun s => x s - Real.cos (Real.arcsin κ) * s)
          (Real.cos (δ s) - Real.cos (Real.arcsin κ)) s := fun s => by
        simpa using (hx s).sub ((hasDerivAt_id s).const_mul (Real.cos (Real.arcsin κ)))
      refine monotone_of_deriv_nonneg (fun s => (hd s).differentiableAt) fun s => ?_
      rw [(hd s).deriv]
      linarith [hcos s]
    rw [le_div_iff₀ hcA]
    rcases le_total s s' with h | h
    · have := hmono h
      simp only at this
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by nlinarith)]
      nlinarith
    · have := hmono h
      simp only at this
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]
      nlinarith

/-- **The curvature of the selected inverse is Lipschitz.** -/
theorem rearF_lipschitz (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (y y' : ℝ) :
    |rearF L f y - rearF L f y'| ≤ L / Real.cos (Real.arcsin κ) ^ 3 * |y - y'| := by
  obtain ⟨hKc, hKp, hKi, hδd, hδp, hδb, hδpos, hkc, hkp, hki, hxL, hRL, hkx⟩ :=
    rear_arclength hA hκ0 hκ1
  obtain ⟨hcA, hcos, hδc, hx, hδlip, hxlow⟩ := rear_arc_basic hA hκ0 hκ1
  obtain ⟨-, hRle, -⟩ := rear_facts hA hκ0 hκ1
  have hA2 := arcsin_lt_pi_div_two hκ1
  obtain ⟨G, hG1, -, -⟩ := exists_inverse_of_deriv_ge hcA hx hcos
  set c := Real.cos (Real.arcsin κ)
  have hval : ∀ y, rearF L f y = Real.tan (rδ L f (G (rearL L f * y) / L)) := fun y => by
    have := hkx (G (rearL L f * y))
    simp only at this
    rw [hG1, mul_div_cancel_left₀ _ hRL.ne'] at this
    exact this
  rw [hval, hval]
  set z := rearL L f * y
  set z' := rearL L f * y'
  have h1 := abs_tan_sub_le hA2 (hδb (G z)) (hδb (G z'))
  have h2 := hδlip (G z) (G z')
  have h3 := hxlow (G z) (G z')
  simp only at h3
  rw [hG1, hG1] at h3
  have hz : |z - z'| = rearL L f * |y - y'| := by
    simp only [z, z']; rw [← mul_sub, abs_mul, abs_of_pos hRL]
  have hc2 : 0 < c ^ 2 := pow_pos hcA 2
  calc |Real.tan (rδ L f (G z / L)) - Real.tan (rδ L f (G z' / L))|
      ≤ |rδ L f (G z / L) - rδ L f (G z' / L)| / c ^ 2 := h1
    _ ≤ |G z - G z'| / c ^ 2 := by gcongr
    _ ≤ (|z - z'| / c) / c ^ 2 := by gcongr
    _ = rearL L f * |y - y'| / c ^ 3 := by rw [hz]; field_simp
    _ ≤ L * |y - y'| / c ^ 3 := by gcongr
    _ = L / c ^ 3 * |y - y'| := by ring

/-- The arclength steering angle is `C^{r+1}` when `f` is `C^r`. -/
lemma rearδ_contDiff (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {r : ℕ}
    (hf : ContDiff ℝ r f) : ContDiff ℝ (r + 1 : ℕ) fun s => rδ L f (s / L) := by
  obtain ⟨hKc, hKp, hKi, hδd, -⟩ := rear_arclength hA hκ0 hκ1
  have hK : ContDiff ℝ r fun s => f (s / L) := hf.comp (contDiff_id.div_const L)
  refine contDiff_bootstrap (fun s => (hδd s).differentiableAt) r fun k hk hδk => ?_
  rw [show deriv (fun s => rδ L f (s / L)) = fun s => f (s / L) - Real.sin (rδ L f (s / L)) from
    funext fun s => (hδd s).deriv]
  exact (hK.of_le (by exact_mod_cast hk)).sub (Real.contDiff_sin.comp hδk)

/-- Any right inverse of the rear arclength is `C^{r+2}` when `f` is `C^r`, with positive
derivative `1 / cos δ`. -/
lemma rearInv_contDiff (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {r : ℕ}
    (hf : ContDiff ℝ r f) {G : ℝ → ℝ}
    (hG : ∀ y, ∫ t in (0 : ℝ)..G y, Real.cos (rδ L f (t / L)) = y) :
    ContDiff ℝ (r + 2 : ℕ) G ∧
      ∀ y, HasDerivAt G (Real.cos (rδ L f (G y / L)))⁻¹ y := by
  obtain ⟨hcA, hcos, hδc, hx, -, -⟩ := rear_arc_basic hA hκ0 hκ1
  obtain ⟨G₀, hG1, hG2, hGd⟩ := exists_inverse_of_deriv_ge hcA hx hcos
  have hGG : G = G₀ := funext fun y => by
    have := hG2 (G y); simp only at this; rw [hG y] at this; exact this.symm
  subst hGG
  refine ⟨?_, hGd⟩
  have hδ := rearδ_contDiff hA hκ0 hκ1 hf
  have hGdiff : Differentiable ℝ G := fun y => (hGd y).differentiableAt
  refine contDiff_bootstrap hGdiff (r + 1) fun k hk hGk => ?_
  rw [show deriv G = fun y => (Real.cos (rδ L f (G y / L)))⁻¹ from funext fun y => (hGd y).deriv]
  refine ContDiff.inv (Real.contDiff_cos.comp ((hδ.of_le (by exact_mod_cast hk)).comp hGk))
    fun y => (hcA.trans_le (hcos _)).ne'

/-- **Regularity gain**: if `f` is `C^r`, the curvature `rearF L f` of the selected inverse is
`C^{r+1}`. -/
theorem rearF_contDiff (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {r : ℕ}
    (hf : ContDiff ℝ r f) : ContDiff ℝ (r + 1 : ℕ) (rearF L f) := by
  obtain ⟨hKc, hKp, hKi, hδd, hδp, hδb, hδpos, hkc, hkp, hki, hxL, hRL, hkx⟩ :=
    rear_arclength hA hκ0 hκ1
  obtain ⟨hcA, hcos, hδc, hx, -, -⟩ := rear_arc_basic hA hκ0 hκ1
  obtain ⟨G, hG1, -, -⟩ := exists_inverse_of_deriv_ge hcA hx hcos
  obtain ⟨hGc, -⟩ := rearInv_contDiff hA hκ0 hκ1 hf hG1
  have hδ := rearδ_contDiff hA hκ0 hκ1 hf
  have hval : rearF L f = fun y => Real.sin (rδ L f (G (rearL L f * y) / L)) /
      Real.cos (rδ L f (G (rearL L f * y) / L)) := funext fun y => by
    have := hkx (G (rearL L f * y))
    simp only at this
    rw [hG1, mul_div_cancel_left₀ _ hRL.ne', Real.tan_eq_sin_div_cos] at this
    exact this
  rw [hval]
  have hin : ContDiff ℝ (r + 1 : ℕ) fun y => rδ L f (G (rearL L f * y) / L) :=
    hδ.comp ((hGc.of_le (by exact_mod_cast (by omega : r + 1 ≤ r + 2))).comp
      (contDiff_const.mul contDiff_id))
  exact (Real.contDiff_sin.comp hin).div (Real.contDiff_cos.comp hin)
    fun y => (hcA.trans_le (hcos _)).ne'

end

end Ovals

end
