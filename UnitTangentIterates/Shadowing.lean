module

public import UnitTangentIterates.Reparam
public import UnitTangentIterates.Reduction
public import UnitTangentIterates.CurveFromCurvature
public import UnitTangentIterates.ModelChain
public import UnitTangentIterates.ShadowOrbit

/-!
# Theorem 6.4 (backward shadowing), intrinsic form

A centered, centrally symmetric closed curve is determined, up to rotation, by its
half-perimeter `L` and its curvature `K` as an `L`-periodic function of arclength with
`∫₀ᴸ K = π` (`Ovals.curveOfCurvature`).  We state the paper's Theorem 6.4 in these intrinsic
terms.

A *model chain* (`Ovals.ModelChain`) consists of fronts `Q_n` (curvature `KQ n`, half-perimeter
`L n`) and rears `A_n` (curvature `KA n`, half-perimeter `L n`) with `A_n = 𝓑 Q_{n+1}`: the
steering angle `δ n` of the front `Q_{n+1}` is a periodic solution of `δ' = K - sin δ` with
`0 < δ < π/2` (so it is the selected one, Lemma 2.1), the rear has curvature `tan δ` at rear
arclength `x(s) = x₀ + ∫₀ˢ cos δ`, and its half-perimeter `∫₀^{L_{n+1}} cos δ` equals `L n`.
All curvatures are at most `κ₀ < 1`.  The arclength origins of `Q_n` and `A_n` are the ones in
which the defects

`e_n = (1 + L_n)² ∫₀^{L_n} |KQ n - KA n|`

are measured.

**Theorem 6.4.**  If `∑ e_n` is small enough (depending only on `κ₀`), the backward iterates
`𝓑^{N-n} Q_N` converge to an exact orbit of ovals `X_n`, `𝒯 X_n = X_{n+1}` (up to
reparametrization).  We also record the width consequence used in Section 7: rears are never
wider than their fronts, so if every `Q_N` lies in a strip of width `W`, so does every `X_n`.
-/

@[expose] public section

namespace Ovals

open Real

/-- **Theorem 6.4 (backward shadowing).**  For every `κ₀ < 1` there is `η > 0` such that every
model chain with curvatures at most `κ₀` and total defect `∑ e_n ≤ η` is shadowed by an exact
orbit of ovals of the unit-tangent transform.  If all fronts `Q_n` lie in strips of width `W`,
so do all the ovals of the orbit. -/
theorem backward_shadowing {κ₀ : ℝ} (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1) :
    ∃ η > 0, ∀ (L : ℕ → ℝ) (KQ KA δ : ℕ → ℝ → ℝ) (x₀ : ℕ → ℝ) (W : ℝ),
      ModelChain κ₀ L KQ KA δ x₀ → Summable (chainDefect L KQ KA) →
      ∑' n, chainDefect L KQ KA n ≤ η →
      (∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ s s', coord v (curveOfCurvature 0 (KQ n) (L n) s -
        curveOfCurvature 0 (KQ n) (L n) s') ≤ W) →
      ∃ (X : ℕ → ℝ → ℂ) (p : ℕ → ℝ) (ψ : ℕ → ℝ → ℝ), IsOvalOrbit X p ψ ∧
        ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ t t', coord v (X n t - X n t') ≤ W := by
  refine ⟨etaC κ₀, etaC_pos hκ₀ hκ₀1, fun L KQ KA δ x₀ W hM hs hη hW => ?_⟩
  obtain ⟨Λ, F, h⟩ := limit_orbit_data hM hκ₀ hκ₀1 hs hη hW
  exact orbit_of_data (khat_pos hκ₀).le (khat_lt_one hκ₀1) (fun n => (h n).1)
    (fun n => (h n).2.1) (fun n => (h n).2.2)

end Ovals

end
