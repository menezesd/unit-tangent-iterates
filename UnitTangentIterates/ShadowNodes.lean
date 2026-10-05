module

public import UnitTangentIterates.ShadowLimitTools

/-!
# The backward iterates of the models

For a model chain we consider the backward iterates `node N n = 𝓑^{N-n} A_N` (`n ≤ N`) as
normalized ovals.  They are admissible with curvature bound `κ̂`, their half-perimeters stay
within a fixed distance of `L n`, their curvatures are uniformly Lipschitz, and (if the fronts
lie in strips of width `W`) they lie in strips of width `W`.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- The normalized oval `X = (L, f)` (with curvature `f(s / L)` at arclength `s`) lies in a strip
of width `W`. -/
def WidthLe (W : ℝ) (X : ℝ × (ℝ → ℝ)) : Prop :=
  ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature 0 (fun s => X.2 (s / X.1)) X.1 s -
    curveOfCurvature 0 (fun s => X.2 (s / X.1)) X.1 s') ≤ W

/-- Rears are no wider than their fronts (normalized form). -/
lemma widthLe_rear {κ W : ℝ} {X : ℝ × (ℝ → ℝ)} (hA : AdmOval κ X.1 X.2) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (h : WidthLe W X) : WidthLe W (rearOv X) := by
  obtain ⟨hKc, hKp, hKi, hδd, hδp, hδb, hδpos, hkc, hkp, hki, hxL, hRL, hkx⟩ :=
    rear_arclength hA hκ0 hκ1
  have hA2 := arcsin_lt_pi_div_two hκ1
  exact width_rear_le (θ := 0) hKc hKp hKi hA.1 hδd hδp
    (fun s => Real.cos_pos_of_mem_Ioo ⟨by linarith [(hδb s).1, Real.pi_pos],
      (hδb s).2.trans_lt hA2⟩) hkc hkp hki hxL hkx h 0

/-- The backward iterate `𝓑^{N-n} A_N`. -/
noncomputable def node (L : ℕ → ℝ) (KA : ℕ → ℝ → ℝ) (x₀ : ℕ → ℝ) (N n : ℕ) : ℝ × (ℝ → ℝ) :=
  rearOv^[N - n] (modelO L KA x₀ N)

lemma node_succ (L : ℕ → ℝ) (KA : ℕ → ℝ → ℝ) (x₀ : ℕ → ℝ) {N n : ℕ} (h : n < N) :
    node L KA x₀ N n = rearOv (node L KA x₀ N (n + 1)) := by
  unfold node
  rw [show N - n = (N - (n + 1)) + 1 by omega, Function.iterate_succ_apply']

lemma node_eq (L : ℕ → ℝ) (KA : ℕ → ℝ → ℝ) (x₀ : ℕ → ℝ) {N n : ℕ} (h : n ≤ N) :
    node L KA x₀ N n = rearOv^[N - n] (modelO L KA x₀ (n + (N - n))) := by
  unfold node; rw [Nat.add_sub_cancel' h]

section chain

variable {κ₀ : ℝ} {L : ℕ → ℝ} {KQ KA δ : ℕ → ℝ → ℝ} {x₀ : ℕ → ℝ}
  (hM : ModelChain κ₀ L KQ KA δ x₀)

include hM

lemma adm_modelO (N : ℕ) : AdmOval κ₀ (modelO L KA x₀ N).1 (modelO L KA x₀ N).2 := by
  have hL := hM.L_pos N
  refine ⟨hL, (hM.KA_cont N).comp (continuous_const.add (continuous_const.mul continuous_id)),
    fun σ => ?_, fun σ => ⟨(hM.KA_pos N _).le, hM.KA_le N _⟩, ?_⟩
  · show KA N (x₀ N + L N * (σ + 1)) = KA N (x₀ N + L N * σ)
    rw [mul_add, mul_one, ← add_assoc]; exact hM.KA_periodic N _
  · show ∫ σ in (0 : ℝ)..1, L N * KA N (x₀ N + L N * σ) = π
    have h1 := intervalIntegral.mul_integral_comp_mul_add (a := 0) (b := 1) (f := KA N)
      (c := L N) (d := x₀ N)
    rw [intervalIntegral.integral_const_mul]
    simp only [mul_zero, zero_add, mul_one] at h1
    rw [show (fun σ => KA N (x₀ N + L N * σ)) = fun σ => KA N (L N * σ + x₀ N) from
      funext fun σ => by rw [add_comm], h1, add_comm (L N) (x₀ N),
      (hM.KA_periodic N).intervalIntegral_add_eq (x₀ N) 0, zero_add, hM.KA_integral N]

/-- The model rears lie in strips of width `W` if the fronts do. -/
lemma widthLe_modelO {W : ℝ}
    (hW : ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature 0 (KQ n) (L n) s -
      curveOfCurvature 0 (KQ n) (L n) s') ≤ W) (N : ℕ) : WidthLe W (modelO L KA x₀ N) := by
  have hL := hM.L_pos N
  have hfun : (fun s => (modelO L KA x₀ N).2 (s / (modelO L KA x₀ N).1)) =
      fun s => KA N (x₀ N + s) := funext fun s => by
    simp only [modelO]; rw [mul_div_cancel₀ _ hL.ne']
  unfold WidthLe
  rw [hfun]
  have hk : Continuous fun s => KA N (x₀ N + s) :=
    (hM.KA_cont N).comp (continuous_const.add continuous_id)
  have hkp : Function.Periodic (fun s => KA N (x₀ N + s)) (L N) := fun s => by
    show KA N (x₀ N + (s + L N)) = KA N (x₀ N + s)
    rw [← add_assoc]; exact hM.KA_periodic N _
  have hki : ∫ r in (0 : ℝ)..L N, KA N (x₀ N + r) = π := by
    rw [intervalIntegral.integral_comp_add_left (KA N) (x₀ N), add_zero,
      (hM.KA_periodic N).intervalIntegral_add_eq (x₀ N) 0, zero_add, hM.KA_integral N]
  exact width_rear_le (θ := 0) (hM.KQ_cont (N + 1)) (hM.KQ_periodic (N + 1))
    (hM.KQ_integral (N + 1)) (hM.L_pos (N + 1)) (hM.steer_deriv N) (hM.steer_periodic N)
    (fun s => Real.cos_pos_of_mem_Ioo ⟨by linarith [(hM.steer_mem N s).1, Real.pi_pos],
      (hM.steer_mem N s).2⟩) hk hkp hki (hM.rear_length N) (hM.rear_curv N) (hW (N + 1)) 0

variable (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1) (hs : Summable (chainDefect L KQ KA))
  (hη : ∑' n, chainDefect L KQ KA n ≤ etaC κ₀)
include hκ₀ hκ₀1 hs hη

lemma iter_adm (k n : ℕ) :
    AdmOval (khat κ₀) (rearOv^[k] (modelO L KA x₀ (n + k))).1
      (rearOv^[k] (modelO L KA x₀ (n + k))).2 := by
  induction k generalizing n with
  | zero => exact (adm_modelO hM n).mono (lt_khat hκ₀1).le
  | succ k ih =>
    have hb := (chain_bounds hM hκ₀ hκ₀1 hs hη n (k + 1)).1
    rw [show n + (k + 1) = (n + 1) + k by omega, Function.iterate_succ_apply'] at hb ⊢
    exact adm_rear (ih (n + 1)) (khat_pos hκ₀).le (khat_lt_one hκ₀1) hb

lemma iter_width {W : ℝ}
    (hW : ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature 0 (KQ n) (L n) s -
      curveOfCurvature 0 (KQ n) (L n) s') ≤ W) (k n : ℕ) :
    WidthLe W (rearOv^[k] (modelO L KA x₀ (n + k))) := by
  induction k generalizing n with
  | zero => exact widthLe_modelO hM hW n
  | succ k ih =>
    have hA := iter_adm hM hκ₀ hκ₀1 hs hη k (n + 1)
    rw [show n + (k + 1) = (n + 1) + k by omega, Function.iterate_succ_apply']
    exact widthLe_rear hA (khat_pos hκ₀).le (khat_lt_one hκ₀1) (ih (n + 1))

/-- The uniform bound on the half-perimeter deviation. -/
noncomputable def devB (κ₀ : ℝ) : ℝ := khat κ₀ * K1c * etaC κ₀

lemma node_adm {N n : ℕ} (h : n ≤ N) :
    AdmOval (khat κ₀) (node L KA x₀ N n).1 (node L KA x₀ N n).2 := by
  rw [node_eq L KA x₀ h]; exact iter_adm hM hκ₀ hκ₀1 hs hη _ _

lemma node_width {W : ℝ}
    (hW : ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature 0 (KQ n) (L n) s -
      curveOfCurvature 0 (KQ n) (L n) s') ≤ W) {N n : ℕ} (h : n ≤ N) :
    WidthLe W (node L KA x₀ N n) := by
  rw [node_eq L KA x₀ h]; exact iter_width hM hκ₀ hκ₀1 hs hη hW _ _

lemma node_L {N n : ℕ} (h : n ≤ N) : |(node L KA x₀ N n).1 - L n| ≤ devB κ₀ := by
  rw [node_eq L KA x₀ h]
  refine (chain_bounds hM hκ₀ hκ₀1 hs hη n (N - n)).2.trans ?_
  have hnn : ∀ l, 0 ≤ chainDefect L KQ KA l := fun l => by
    unfold chainDefect
    exact mul_nonneg (sq_nonneg _) (intervalIntegral.integral_nonneg (hM.L_pos l).le
      fun s _ => abs_nonneg _)
  have h1 : ∑ l ∈ Finset.Ioc n (n + (N - n)), chainDefect L KQ KA l ≤ etaC κ₀ :=
    (hs.sum_le_tsum _ fun l _ => hnn l).trans hη
  have h2 : 0 ≤ khat κ₀ * K1c := mul_nonneg (khat_pos hκ₀).le K1c_pos.le
  unfold devB
  exact mul_le_mul_of_nonneg_left h1 h2

lemma node_lower {N n : ℕ} (h : n < N) :
    π / Real.tan (Real.arcsin (khat κ₀)) ≤ (node L KA x₀ N n).1 := by
  rw [node_succ L KA x₀ h]
  exact (rear_facts (node_adm hM hκ₀ hκ₀1 hs hη h) (khat_pos hκ₀).le (khat_lt_one hκ₀1)).2.2.1

lemma node_lip {N n : ℕ} (h : n < N) (σ σ' : ℝ) :
    |(node L KA x₀ N n).2 σ - (node L KA x₀ N n).2 σ'| ≤
      (L (n + 1) + devB κ₀) / Real.cos (Real.arcsin (khat κ₀)) ^ 3 * |σ - σ'| := by
  rw [node_succ L KA x₀ h]
  have hA := node_adm hM hκ₀ hκ₀1 hs hη (show n + 1 ≤ N from h)
  have h1 := rearF_lipschitz hA (khat_pos hκ₀).le (khat_lt_one hκ₀1) σ σ'
  have h2 := node_L hM hκ₀ hκ₀1 hs hη (show n + 1 ≤ N from h)
  have hc := cos_arcsin_pos' (khat_pos hκ₀).le (khat_lt_one hκ₀1)
  refine h1.trans ?_
  gcongr
  linarith [(abs_le.1 h2).2]

end chain

end Ovals

end
