import UnitTangentIterates.UnitTangent

/-!
# Strict convexity without the third derivative

§76 recorded the manifest's finding: `LimitStrictnessData` needs
`curvature_deriv`, hence effectively `C³` curve regularity, while the
normal-path limit delivers only `C²`.  That gap is what
`UnitTangent.curvature_pos_of_next_track_convex` creates — it asks for
`Differentiable ℝ k` in order to run the differential inequality `u' + u ≥ 0`
for `u = k/√(1+k²)`.

This file trades that hypothesis for its integrated form.

* `curvature_pos_of_harnack` — the same conclusion `0 < k` from
  `e^{a−b}u(a) ≤ u(b)` for `a ≤ b`, **with no differentiability at all**.  The
  argument is the same Gronwall comparison, read off the integrated inequality
  instead of derived from the differential one.
* `harnack_of_next_nonneg` — the differential form implies the integrated form,
  so nothing is lost for the smooth model curves that satisfy it.
* `harnack_of_tendsto` — **the integrated form is closed under pointwise
  limits**, because `t ↦ t/√(1+t²)` is continuous.

That last point is the reason this is the right reformulation.  A `C²` limit of
smooth curves inherits the integrated inequality from its approximants, whereas
the derivative condition has nothing to pass to the limit.  So the strictness
data can be established for the limit from the model curves that converge to it,
without a regularity bootstrap.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real Function

namespace UnitTangent


/-- **Strict convexity from the integrated form — no derivative needed.**
`curvature_pos_of_next_track_convex` asks for `Differentiable ℝ k`, because it
runs the differential inequality `u' + u ≥ 0` for `u = k/√(1+k²)`.  The
*integrated* form of that inequality, `e^{a−b}u(a) ≤ u(b)` for `a ≤ b`, gives
the same conclusion from continuity alone. -/
theorem curvature_pos_of_harnack {k : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hper : Periodic k L) (hnn : ∀ x, 0 ≤ k x)
    (hharnack : ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (k a / Real.sqrt (1 + k a ^ 2))
        ≤ k b / Real.sqrt (1 + k b ^ 2))
    (hne : ∃ x₁, k x₁ ≠ 0) : ∀ x, 0 < k x := by
  obtain ⟨x₁, hx₁⟩ := hne
  intro x
  have hspos : ∀ t : ℝ, 0 < Real.sqrt (1 + k t ^ 2) := fun t => by positivity
  have hu1 : 0 < k x₁ / Real.sqrt (1 + k x₁ ^ 2) :=
    div_pos (lt_of_le_of_ne (hnn x₁) (Ne.symm hx₁)) (hspos x₁)
  obtain ⟨n, hn⟩ := exists_nat_gt ((x₁ - x) / L)
  have hxn : x₁ ≤ x + n * L := by
    have := (div_lt_iff₀ hL).mp hn
    linarith
  have hkper : k (x + n * L) = k x := by
    have := (hper.nat_mul n) x
    simpa [mul_comm] using this
  have hstep := hharnack x₁ (x + n * L) hxn
  rw [hkper] at hstep
  have hpos : 0 < k x / Real.sqrt (1 + k x ^ 2) :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hu1) hstep
  by_contra hcon
  push_neg at hcon
  have : k x = 0 := le_antisymm hcon (hnn x)
  rw [this] at hpos
  simp at hpos

/-- The differential form implies the integrated form, so nothing is lost: a
smooth curve satisfying `next_nonnegative` satisfies the Harnack inequality. -/
theorem harnack_of_next_nonneg {k : ℝ → ℝ} (hdiff : Differentiable ℝ k)
    (hK : ∀ x, 0 ≤ deriv (fun t => k t / Real.sqrt (1 + k t ^ 2)) x
        + k x / Real.sqrt (1 + k x ^ 2)) :
    ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (k a / Real.sqrt (1 + k a ^ 2))
        ≤ k b / Real.sqrt (1 + k b ^ 2) := by
  set u : ℝ → ℝ := fun t => k t / Real.sqrt (1 + k t ^ 2) with hu
  have hupos : ∀ t, (0:ℝ) < Real.sqrt (1 + k t ^ 2) := fun t => by positivity
  have hud : Differentiable ℝ u := by
    apply Differentiable.div hdiff
    · exact (differentiable_const 1 |>.add (hdiff.pow 2)).sqrt
        (fun t => (by positivity : (0:ℝ) < 1 + k t ^ 2).ne')
    · exact fun t => (hupos t).ne'
  intro a b hab
  have hmono : MonotoneOn (fun t => Real.exp t * u t) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      ((Real.continuous_exp.mul hud.continuous).continuousOn)
      (f' := fun t => Real.exp t * (deriv u t + u t))
      (fun t _ => ?_) (fun t _ => ?_)
    · have h1 : HasDerivAt (fun r => Real.exp r * u r)
          (Real.exp t * u t + Real.exp t * deriv u t) t := by
        simpa [mul_comm] using (Real.hasDerivAt_exp t).mul (hud t).hasDerivAt
      have h2 : Real.exp t * u t + Real.exp t * deriv u t
          = Real.exp t * (deriv u t + u t) := by ring
      rw [h2] at h1
      exact h1.hasDerivWithinAt
    · exact mul_nonneg (Real.exp_pos t).le (hK t)
  have h := hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  simp only at h
  have hea : (0:ℝ) < Real.exp b := Real.exp_pos b
  rw [Real.exp_sub]
  rw [div_mul_eq_mul_div, div_le_iff₀ hea]
  calc Real.exp a * u a ≤ Real.exp b * u b := h
    _ = u b * Real.exp b := by ring

/-- **The integrated form is closed under limits.**  This is why it is the right
hypothesis for a `C²` limit: `u(t) = t/√(1+t²)` is continuous, so the inequality
`e^{a−b}u(kₙ a) ≤ u(kₙ b)` passes to a pointwise limit, whereas the differential
form does not. -/
theorem harnack_of_tendsto {kn : ℕ → ℝ → ℝ} {k : ℝ → ℝ}
    (hconv : ∀ x, Filter.Tendsto (fun n => kn n x) Filter.atTop (nhds (k x)))
    (hharn : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (kn n a / Real.sqrt (1 + kn n a ^ 2))
        ≤ kn n b / Real.sqrt (1 + kn n b ^ 2)) :
    ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (k a / Real.sqrt (1 + k a ^ 2))
        ≤ k b / Real.sqrt (1 + k b ^ 2) := by
  have hcont : Continuous fun t : ℝ => t / Real.sqrt (1 + t ^ 2) := by
    apply Continuous.div continuous_id
    · exact (continuous_const.add (continuous_pow 2)).sqrt
    · exact fun t => (by positivity : (0:ℝ) < Real.sqrt (1 + t ^ 2)).ne'
  intro a b hab
  have hA : Filter.Tendsto
      (fun n => Real.exp (a - b) * (kn n a / Real.sqrt (1 + kn n a ^ 2)))
      Filter.atTop (nhds (Real.exp (a - b) * (k a / Real.sqrt (1 + k a ^ 2)))) :=
    ((hcont.tendsto (k a)).comp (hconv a)).const_mul _
  have hB : Filter.Tendsto
      (fun n => kn n b / Real.sqrt (1 + kn n b ^ 2))
      Filter.atTop (nhds (k b / Real.sqrt (1 + k b ^ 2))) :=
    (hcont.tendsto (k b)).comp (hconv b)
  exact le_of_tendsto_of_tendsto hA hB
    (Filter.Eventually.of_forall fun n => hharn n a b hab)

end UnitTangent

