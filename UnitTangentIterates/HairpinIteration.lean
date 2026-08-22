import Mathlib
import UnitTangentIterates.HairpinLimit

/-!
# The monotone iteration scheme for the translating hairpin

This file formalizes the order-theoretic part of the proof of the theorem
*Translating hairpin* of the paper *A Noncircular Oval with Convex Unit-Tangent
Iterates*, together with the sign of the translation vector.

The proof starts the iteration at the lower barrier, `f₀ = f⁻`, and sets
`f_{n+1} = 𝒫 f_n`.  The lemma *Monotone translator operator* (order
preservation of `𝒫`, formalized in `UnitTangentIterates.Translator`) and the lemma
*Explicit barriers* (`f⁻ ≤ 𝒫f⁻` and `𝒫f⁺ ≤ f⁺`, formalized in
`UnitTangentIterates.Barriers`) then give

```
   f⁻ ≤ f₀ ≤ f₁ ≤ ⋯ ≤ f⁺ ,
```

so the iterates increase and stay trapped under the upper barrier; combined
with `UnitTangentIterates.HairpinLimit` this produces the pointwise limit `f` with
`f⁻ ≤ f ≤ f⁺`.

The last display of the proof computes the translation

```
   V = -∫_{π/2}^{g(π/2)} f(t) cot t dt > 0 ,
```

positive because `cot` is negative on `(π/2, π)` and `f > 0`.

Main results:

* `iterate_le_upper` : the iterates stay below the upper barrier;
* `iterate_le_succ` : the iterates increase;
* `exists_monotone_limit` : the pointwise limit exists and is trapped between
  the two barriers;
* `translation_pos` : positivity of the translation `V`.
-/

noncomputable section

open Filter Topology Set

namespace HairpinIteration

/-! ### The trapped monotone iteration -/

section Iteration

variable {Op : (ℝ → ℝ) → (ℝ → ℝ)} {low up : ℝ → ℝ}

/-- The iterates of an order-preserving operator started at a subsolution stay
below any supersolution above it. -/
theorem iterate_le_upper (hmono : ∀ u v : ℝ → ℝ, (∀ θ, u θ ≤ v θ) → ∀ θ, Op u θ ≤ Op v θ)
    (hup : ∀ θ, Op up θ ≤ up θ) (hlu : ∀ θ, low θ ≤ up θ) :
    ∀ n θ, Op^[n] low θ ≤ up θ := by
  intro n
  induction n with
  | zero => simpa using hlu
  | succ n ih =>
    intro θ
    have h1 : Op (Op^[n] low) θ ≤ Op up θ := hmono _ _ ih θ
    have h2 : Op^[n + 1] low θ = Op (Op^[n] low) θ := by
      rw [Function.iterate_succ_apply']
    rw [h2]
    exact le_trans h1 (hup θ)

/-- The iterates of an order-preserving operator started at a subsolution
increase. -/
theorem iterate_le_succ (hmono : ∀ u v : ℝ → ℝ, (∀ θ, u θ ≤ v θ) → ∀ θ, Op u θ ≤ Op v θ)
    (hlow : ∀ θ, low θ ≤ Op low θ) :
    ∀ n θ, Op^[n] low θ ≤ Op^[n + 1] low θ := by
  intro n
  induction n with
  | zero => simpa using hlow
  | succ n ih =>
    intro θ
    have h1 : Op (Op^[n] low) θ ≤ Op (Op^[n + 1] low) θ := hmono _ _ ih θ
    rw [Function.iterate_succ_apply' (n := n) (f := Op),
      Function.iterate_succ_apply' (n := n + 1) (f := Op)]
    exact h1

/-- **The monotone iteration converges.**  For an order-preserving operator
with a subsolution `f⁻` and a supersolution `f⁺` above it, the iterates
`f_n = 𝒫ⁿ f⁻` converge pointwise to a limit trapped between the barriers. -/
theorem exists_monotone_limit
    (hmono : ∀ u v : ℝ → ℝ, (∀ θ, u θ ≤ v θ) → ∀ θ, Op u θ ≤ Op v θ)
    (hlow : ∀ θ, low θ ≤ Op low θ) (hup : ∀ θ, Op up θ ≤ up θ) (hlu : ∀ θ, low θ ≤ up θ) :
    ∃ f : ℝ → ℝ, (∀ θ, Tendsto (fun n => Op^[n] low θ) atTop (𝓝 (f θ))) ∧
      (∀ θ, low θ ≤ f θ) ∧ (∀ θ, f θ ≤ up θ) := by
  refine ⟨fun θ => ⨆ n, Op^[n] low θ, ?_, ?_, ?_⟩
  · exact fun θ => HairpinLimit.tendsto_iterates (fseq := fun n => Op^[n] low) (M := up)
      (iterate_le_succ hmono hlow) (iterate_le_upper hmono hup hlu) θ
  · intro θ
    have := HairpinLimit.le_iSup_iterates (fseq := fun n => Op^[n] low) (M := up)
      (iterate_le_upper hmono hup hlu) 0 θ
    simpa using this
  · intro θ
    exact ciSup_le fun n => iterate_le_upper hmono hup hlu n θ

end Iteration

/-! ### Positivity of the translation -/

/-- **The translation is positive.**  On the interval `[π/2, b] ⊆ [π/2, π)`
the cotangent is negative, so for a positive profile `f` the translation
`V = -∫ f cot` is positive. -/
theorem translation_pos {f : ℝ → ℝ} {b : ℝ} (hf : Continuous f) (hfpos : ∀ t, 0 < f t)
    (hb1 : Real.pi / 2 < b) (hb2 : b < Real.pi) :
    0 < -∫ t in (Real.pi / 2)..b, f t * (Real.cos t / Real.sin t) := by
  have hsin : ∀ t ∈ Ioo (Real.pi / 2) b, 0 < Real.sin t := by
    intro t ht
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos, ht.1]
    · linarith [ht.2]
  have hcos : ∀ t ∈ Ioo (Real.pi / 2) b, Real.cos t < 0 := by
    intro t ht
    apply Real.cos_neg_of_pi_div_two_lt_of_lt ht.1
    linarith [Real.pi_pos, ht.2]
  have hneg : ∀ t ∈ Ioo (Real.pi / 2) b, 0 < -(f t * (Real.cos t / Real.sin t)) := by
    intro t ht
    have h1 : Real.cos t / Real.sin t < 0 := div_neg_of_neg_of_pos (hcos t ht) (hsin t ht)
    have := mul_neg_of_pos_of_neg (hfpos t) h1
    linarith
  have hcont : ContinuousOn (fun t => -(f t * (Real.cos t / Real.sin t)))
      (uIcc (Real.pi / 2) b) := by
    apply ContinuousOn.neg
    apply hf.continuousOn.mul
    apply ContinuousOn.div Real.continuous_cos.continuousOn Real.continuous_sin.continuousOn
    intro t ht
    rw [uIcc_of_le hb1.le] at ht
    have h0 : 0 < Real.sin t := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [Real.pi_pos, ht.1]
      · linarith [ht.2]
    exact ne_of_gt h0
  have hpos : 0 < ∫ t in (Real.pi / 2)..b, -(f t * (Real.cos t / Real.sin t)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable) hneg hb1
  rwa [intervalIntegral.integral_neg] at hpos

end HairpinIteration
