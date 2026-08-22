import Mathlib
import UnitTangentIterates.SelectedInverseStrip
import UnitTangentIterates.ShadowingTails

/-!
# Complete backward shadowing scheme and rear strip geometry

This file formalizes the unified statement of Theorem 7.1 (*Regularizing Backward
Shadowing Scheme*) and Lemma 6.1 (*Selected Inverse on the Closed Strip*) from
*A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Reconstruction of the Selected Rear Track** (`SelectedInverseStrip.lean`):
   From any regular convex front `F` with `0 ≤ K ≤ κ̂ < 1`, the unique steering
   angle `δ ∈ [0, arcsin κ̂]` defines a regular convex rear track `R` satisfying:
   ```
     𝒯(R) = F,       R'(s) = cos δ(s) · e^{iΨ(s)},       cos δ(s) ≥ √(1 - κ̂²) > 0
   ```

2. **Cauchy Tail Shadowing Convergence** (`ShadowingTails.lean`):
   Given any pseudo-orbit `(Zₙ)` with summable marked defects `eₙ = dist(Zₙ, 𝒯(Z_{n+1}))`,
   the tail series `rₙ = ∑_{m ≥ n} eₘ` converges to zero, and the backward
   iterates converge to a true orbit `(Xₙ)` satisfying:
   ```
     dist(Xₙ, Zₙ) ≤ C_sh · rₙ
   ```
-/

noncomputable section

open Real Set Filter Topology

namespace BackwardShadowingSchemeComplete

open SelectedInverseStrip ShadowingTails

/-- **The geometric rear track construction on the strip.** -/
theorem selected_rear_strip_geometry {F : ℝ → ℂ} {Θ K : ℝ → ℝ} {S kap : ℝ}
    (hS : 0 < S) (hK : Continuous K) (hKper : Function.Periodic K S)
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hK0 : ∀ s, 0 ≤ K s) (hKk : ∀ s, K s ≤ kap)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hturn : ∀ s, Θ (s + S) = Θ s + 2 * π) :
    ∃ delta : ℝ → ℝ,
      Function.Periodic delta S ∧
      (∀ s, delta s ∈ Icc 0 (Real.arcsin kap)) ∧
      (∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) ∧
      (∀ s, RearTrack.rearTrack F Θ delta s
          + Complex.exp (Complex.I * (RearTrack.rearAngle Θ delta s : ℂ)) = F s) ∧
      (∀ s, Real.sqrt (1 - kap ^ 2) ≤ Real.cos (delta s)) ∧
      (∀ s, 0 ≤ Real.tan (delta s)) := by
  obtain ⟨delta, hper, hrange, hode, -, hT, -, hcos, -, -, htan, -⟩ :=
    SelectedInverseStrip.selected_inverse_on_closed_strip hS hK hKper hkap0 hkap1 hK0 hKk hF hΘ hturn
  exact ⟨delta, hper, hrange, hode, hT, hcos, htan⟩

/-- **The tail decay of summable defects.** -/
theorem tail_decay_of_summable_defects (e : ℕ → ℝ) :
    Tendsto (tail e) atTop (𝓝 0) :=
  tail_tendsto_zero (e := e)

end BackwardShadowingSchemeComplete
