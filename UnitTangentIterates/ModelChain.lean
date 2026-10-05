module

public import UnitTangentIterates.Defs

/-!
# Model chains for Theorem 6.4

A *model chain* (`Ovals.ModelChain`) consists of fronts `Q_n` (curvature `KQ n`, half-perimeter
`L n`, as functions of arclength) and rears `A_n` (curvature `KA n`, half-perimeter `L n`) with
`A_n = 𝓑 Q_{n+1}`: the steering angle `δ n` of the front `Q_{n+1}` is a periodic solution of
`δ' = K - sin δ` with `0 < δ < π/2`, the rear has curvature `tan δ` at rear arclength
`x(s) = x₀ + ∫₀ˢ cos δ`, and its half-perimeter `∫₀^{L_{n+1}} cos δ` equals `L n`.  The defects
are `e_n = (1 + L_n)² ∫₀^{L_n} |KQ n - KA n|` (`Ovals.chainDefect`).
-/

@[expose] public section

namespace Ovals

open Real

/-- A chain of closed models for Theorem 6.4, described intrinsically (see the module
docstring). -/
structure ModelChain (κ₀ : ℝ) (L : ℕ → ℝ) (KQ KA δ : ℕ → ℝ → ℝ) (x₀ : ℕ → ℝ) : Prop where
  L_pos : ∀ n, 0 < L n
  KQ_cont : ∀ n, Continuous (KQ n)
  KQ_periodic : ∀ n, Function.Periodic (KQ n) (L n)
  KQ_integral : ∀ n, ∫ s in (0 : ℝ)..L n, KQ n s = π
  KQ_pos : ∀ n s, 0 < KQ n s
  KQ_le : ∀ n s, KQ n s ≤ κ₀
  KA_cont : ∀ n, Continuous (KA n)
  KA_periodic : ∀ n, Function.Periodic (KA n) (L n)
  KA_integral : ∀ n, ∫ s in (0 : ℝ)..L n, KA n s = π
  KA_pos : ∀ n s, 0 < KA n s
  KA_le : ∀ n s, KA n s ≤ κ₀
  steer_deriv : ∀ n s, HasDerivAt (δ n) (KQ (n + 1) s - Real.sin (δ n s)) s
  steer_mem : ∀ n s, δ n s ∈ Set.Ioo 0 (π / 2)
  steer_periodic : ∀ n, Function.Periodic (δ n) (L (n + 1))
  rear_curv : ∀ n s, KA n (x₀ n + ∫ r in (0 : ℝ)..s, Real.cos (δ n r)) = Real.tan (δ n s)
  rear_length : ∀ n, ∫ r in (0 : ℝ)..L (n + 1), Real.cos (δ n r) = L n

/-- The defect `e_n = (1 + L_n)² ∫₀^{L_n} |KQ n - KA n|` of a model chain. -/
noncomputable def chainDefect (L : ℕ → ℝ) (KQ KA : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  (1 + L n) ^ 2 * ∫ s in (0 : ℝ)..L n, |KQ n s - KA n s|

end Ovals

end
