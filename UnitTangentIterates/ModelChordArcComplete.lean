import Mathlib
import UnitTangentIterates.ModelChordArc
import UnitTangentIterates.ChordArc

/-!
# Complete chord-arc bound and embeddedness of the model curves

This file formalizes the unified statement of Lemma 6.2 (*Uniform Chord-Arc Bound
from Curvature Pinching*) from *A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Existence and Positivity of Chord-Arc Constant** (`ModelChordArc.modelChordConst_pos`):
   For any curvature pinching `0 < k_min ≤ κ ≤ κ̂` and separation `H_0 > 0`,
   the constant:
   ```
     δ = min(H_0, 2 h_0) / (2 H_0) > 0
   ```
   is strictly positive.

2. **Uniform Chord-Arc Bound for the Two-Cap Sequence** (`ModelChordArc.model_chord_arc`):
   Every curve in the two-cap model sequence satisfies the quantitative chord-arc bound:
   ```
     δ · (2 H_0 / 2 H_n) · min(|x - y|, 2 H_n - |x - y|) ≤ ‖Q_n(x) - Q_n(y)‖
   ```

3. **Smooth Embeddedness of the Model Fronts** (`ModelChordArc.injOn_front`):
   Every model curve is strictly injective on its period `[0, 2 H_n)` and hence
   is a smooth embedded closed curve (oval).
-/

noncomputable section

open Real Set Filter Topology Function ModelChordArc TwoCapPairsAssembly CurvatureInterpolation

namespace ModelChordArcComplete

/-- **The complete chord-arc and embeddedness theorem.** -/
theorem model_chord_arc_complete
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ} {kmin kap : ℝ}
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n) (hkminpos : 0 < kmin)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = π) :
    (0 < modelChordConst kmin kap (Hs 0)) ∧
    (∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      modelChordConst kmin kap (Hs 0) * (2 * Hs 0) / (2 * Hs n)
          * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖front (kappas n) (theta0 n) (Hs n) x - front (kappas n) (theta0 n) (Hs n) y‖) ∧
    (∀ n, InjOn (front (kappas n) (theta0 n) (Hs n)) (Ico 0 (2 * Hs n))) := by
  have hle : kmin ≤ kap := le_trans (hkmin 0 0) (hkap 0 0)
  refine ⟨modelChordConst_pos hkminpos hle (hH 0),
    model_chord_arc hH hmono hkminpos hk hper hkmin hkap htotal,
    fun n => injOn_front (hH n) (hk n) (hper n) hkminpos (hkmin n) (hkap n) (htotal n)⟩

end ModelChordArcComplete
