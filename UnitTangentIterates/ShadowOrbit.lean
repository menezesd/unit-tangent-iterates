module

public import UnitTangentIterates.ShadowLimit
public import UnitTangentIterates.Reparam
public import UnitTangentIterates.Embedded

/-!
# From an orbit of normalized ovals to an orbit of ovals

If admissible normalized ovals `(Λ n, F n)` satisfy `(Λ n, F n) = 𝓑 (Λ (n+1), F (n+1))`, then
all `F n` are smooth (each application of `𝓑` gains one derivative) and positive, and the closed
curves with curvature `F n (s / Λ n)` (suitably rotated) form an orbit of ovals of the
unit-tangent transform up to reparametrization (`Ovals.orbit_of_data`).
-/

@[expose] public section

namespace Ovals

open Real
open scoped ContDiff

section rear

variable {θ L' L'' : ℝ} {K δ k : ℝ → ℝ}

/-- **The unit-tangent transform of the rear is the front**, in the rear arclength
`x(s) = ∫₀ˢ cos δ`. -/
theorem unitTangent_rear_curve (hK : Continuous K) (hKp : Function.Periodic K L')
    (hKi : ∫ r in (0 : ℝ)..L', K r = π)
    (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s) (hδp : Function.Periodic δ L')
    (hcos : ∀ s, 0 < Real.cos (δ s)) (hk : Continuous k) (hkp : Function.Periodic k L'')
    (hki : ∫ r in (0 : ℝ)..L'', k r = π) (hL : ∫ r in (0 : ℝ)..L', Real.cos (δ r) = L'')
    (hkx : ∀ s, k (∫ r in (0 : ℝ)..s, Real.cos (δ r)) = Real.tan (δ s)) (s : ℝ) :
    unitTangentTransform (curveOfCurvature (θ - δ 0) k L'') (∫ r in (0 : ℝ)..s, Real.cos (δ r)) =
      curveOfCurvature θ K L' s := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun s => (hδ s).continuousAt
  have hcc : Continuous fun r => Real.cos (δ r) := Real.continuous_cos.comp hδc
  set x : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, Real.cos (δ r) with hxdef
  have hx : ∀ s, HasDerivAt x (Real.cos (δ s)) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hcc.intervalIntegrable _ _)
      (hcc.stronglyMeasurableAtFilter _ _) hcc.continuousAt
  set γ := curveOfCurvature (θ - δ 0) k L''
  have hγd : Differentiable ℝ γ := fun s => (hasDerivAt_curveOfCurvature hk s).differentiableAt
  have h1 : unitTangentTransform (γ ∘ x) = unitTangentTransform γ ∘ x :=
    unitTangentTransform_comp hγd (fun s => (hx s).differentiableAt)
      (fun s => by rw [(hx s).deriv]; exact hcos s)
  have h2 : γ ∘ x = rearCurve (curveOfCurvature θ K L') (angleOfCurvature θ K) δ := by
    funext s
    exact (rearCurve_eq_curveOfCurvature hK hKp hKi hδ hδp hcos hk hkp hki hL hkx s).symm
  have h3 := unitTangentTransform_rearCurve (F := curveOfCurvature θ K L')
    (Θ := angleOfCurvature θ K) (hasDerivAt_curveOfCurvature (θ₀ := θ) (L := L') hK)
    (hasDerivAt_angleOfCurvature (θ₀ := θ) hK) hδ hcos
  rw [h2, h3] at h1
  exact (congrFun h1 s).symm

end rear

/-- **An exact backward orbit of normalized ovals yields an orbit of ovals.** -/
theorem orbit_of_data {κ W : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {Λ : ℕ → ℝ} {F : ℕ → ℝ → ℝ}
    (hA : ∀ n, AdmOval κ (Λ n) (F n))
    (hstep : ∀ n, (Λ n, F n) = rearOv (Λ (n + 1), F (n + 1)))
    (hW : ∀ n, WidthLe W (Λ n, F n)) :
    ∃ (X : ℕ → ℝ → ℂ) (p : ℕ → ℝ) (ψ : ℕ → ℝ → ℝ), IsOvalOrbit X p ψ ∧
      ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ t t', coord v (X n t - X n t') ≤ W := by
  have hΛ : ∀ n, Λ n = rearL (Λ (n + 1)) (F (n + 1)) := fun n => congrArg Prod.fst (hstep n)
  have hF : ∀ n, F n = rearF (Λ (n + 1)) (F (n + 1)) := fun n => congrArg Prod.snd (hstep n)
  have hsmooth_k : ∀ k : ℕ, ∀ n, ContDiff ℝ k (F n) := by
    intro k
    induction k with
    | zero => intro n; exact contDiff_zero.2 (hA n).2.1
    | succ k ih =>
      intro n; rw [hF n]; exact rearF_contDiff (hA (n + 1)) hκ0 hκ1 (ih (n + 1))
  have hsmooth : ∀ n, ContDiff ℝ ∞ (F n) := fun n => contDiff_infty.2 fun k => hsmooth_k k n
  have hpos : ∀ n y, 0 < F n y := fun n y => by
    rw [hF n]; exact (rear_facts (hA (n + 1)) hκ0 hκ1).2.2.2.2.2.1 y
  obtain ⟨θ, hθ⟩ : ∃ θ : ℕ → ℝ, ∀ n, θ n = θ (n + 1) - rδ (Λ (n + 1)) (F (n + 1)) 0 :=
    ⟨fun n => ∑ i ∈ Finset.range n, rδ (Λ (i + 1)) (F (i + 1)) 0,
      fun n => by simp [Finset.sum_range_succ]⟩
  have hKdata : ∀ n, Continuous (fun s => F n (s / Λ n)) ∧
      Function.Periodic (fun s => F n (s / Λ n)) (Λ n) ∧
      ∫ r in (0 : ℝ)..Λ n, F n (r / Λ n) = π := fun n => by
    obtain ⟨h1, h2, h3, -⟩ := rear_arclength (hA n) hκ0 hκ1; exact ⟨h1, h2, h3⟩
  have hKs : ∀ n, ContDiff ℝ ∞ (fun s => F n (s / Λ n)) := fun n =>
    (hsmooth n).comp (contDiff_id.div_const _)
  set X : ℕ → ℝ → ℂ := fun n => curveOfCurvature (θ n) (fun s => F n (s / Λ n)) (Λ n) with hX
  have hrep : ∀ n, ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ (∀ t, 0 < deriv G t) ∧
      (∀ t, G (t + 2 * Λ n) = G t + 2 * Λ (n + 1)) ∧
      unitTangentTransform (X n) = X (n + 1) ∘ G := by
    intro n
    obtain ⟨hKc, hKp, hKi, hδd, hδp, hδb, hδpos, hkc, hkp, hki, hxL, hRL, hkx⟩ :=
      rear_arclength (hA (n + 1)) hκ0 hκ1
    obtain ⟨hcA, hcos, hδc, hx, -, -⟩ := rear_arc_basic (hA (n + 1)) hκ0 hκ1
    obtain ⟨G, hG1, hG2, -⟩ := exists_inverse_of_deriv_ge hcA hx hcos
    obtain ⟨-, hGd⟩ := rearInv_contDiff (hA (n + 1)) hκ0 hκ1 (hsmooth_k 0 (n + 1)) hG1
    have hcc : Continuous fun r => Real.cos (rδ (Λ (n + 1)) (F (n + 1)) (r / Λ (n + 1))) :=
      Real.continuous_cos.comp hδc
    have hxp : ∀ s, ∫ r in (0 : ℝ)..s + 2 * Λ (n + 1),
        Real.cos (rδ (Λ (n + 1)) (F (n + 1)) (r / Λ (n + 1))) =
        (∫ r in (0 : ℝ)..s, Real.cos (rδ (Λ (n + 1)) (F (n + 1)) (r / Λ (n + 1)))) +
          2 * Λ n := fun s => by
      have hper : Function.Periodic
          (fun r => Real.cos (rδ (Λ (n + 1)) (F (n + 1)) (r / Λ (n + 1)))) (Λ (n + 1)) :=
        fun r => by simp only [hδp r]
      rw [two_mul, ← add_assoc, integral_add_period hcc hper, integral_add_period hcc hper, hxL,
        ← hΛ n]
      ring
    refine ⟨G, contDiff_infty.2 fun k =>
      (rearInv_contDiff (hA (n + 1)) hκ0 hκ1 (hsmooth_k k (n + 1)) hG1).1.of_le
        (by exact_mod_cast (by omega : k ≤ k + 2)), fun t => ?_, fun t => ?_, ?_⟩
    · rw [(hGd t).deriv]; exact inv_pos.2 (hcA.trans_le (hcos _))
    · have := hG2 (G t + 2 * Λ (n + 1))
      simp only at this
      rw [hxp, hG1] at this
      exact this
    · funext t
      have hXn : X n = curveOfCurvature
          (θ (n + 1) - (fun s => rδ (Λ (n + 1)) (F (n + 1)) (s / Λ (n + 1))) 0)
          (fun y => rearF (Λ (n + 1)) (F (n + 1)) (y / rearL (Λ (n + 1)) (F (n + 1))))
          (rearL (Λ (n + 1)) (F (n + 1))) := by
        simp only [X, zero_div]
        rw [← hθ n, ← hΛ n, ← hF n]
      have := unitTangent_rear_curve (θ := θ (n + 1)) hKc hKp hKi hδd hδp
        (fun s => hcA.trans_le (hcos s)) hkc hkp hki hxL hkx (G t)
      rw [hG1] at this
      rw [hXn, this]
      rfl
  choose ψ hψs hψpos hψper hψstep using hrep
  refine ⟨X, fun n => 2 * Λ n, ψ, ⟨fun n => ?_, fun n => by linarith [(hA n).1], fun n => ?_,
    fun n => ?_, hψs, hψpos, hψper, hψstep⟩, fun n => ?_⟩
  · exact isOval_curveOfCurvature (hA n).1 (hKs n) (fun s => hpos n _) (hKdata n).2.1
      (hKdata n).2.2
  · exact curveOfCurvature_periodic (hKdata n).1 (hKdata n).2.1 (hKdata n).2.2
  · exact injOn_curveOfCurvature (hKdata n).1 (fun s => (hpos n _).le) (hKdata n).2.1
      (hKdata n).2.2
  · exact width_rotate (θ := 0) (hW n)

end Ovals

end
