import Mathlib
import UnitTangentIterates.TwoCapPairsExistence
import UnitTangentIterates.LargeSeparation

/-!
# Complete large-separation threshold and two-cap model sequence

This file formalizes the unified statement of Definition 4.1 (*Two-Cap Asymmetric Hairpin Pair*)
and Lemma 4.3 (*Recurrence Relation & Large-Separation Threshold*) from
*A Noncircular Oval with Convex Unit-Tangent Iterates*:

1. **Exact Two-Cap Front/Rear Pair** (`TwoCapPairsExistence.exact_two_cap_pair`):
   For every separation `H > 0`, the two-cap front is a unit-speed, centrally symmetric
   oval of perimeter `2H`, and the rear `R = F - e^{iΨ}` is a regular, centrally symmetric
   oval of perimeter `2P(H) = 2 ∫₀^H cos δ` satisfying `𝒯(R) = F`.

2. **Large-Separation Linear Growth & Contradiction Gap** (`LargeSeparation.exists_large_separation_threshold`):
   Past a threshold `H_*`, the perimeter map `P` is strictly increasing with `P(H) ≤ H - Δ/2`,
   the recurrence `P(H_{n+1}) = H_n` defines a sequence with:
   ```
     H_n ≥ H_0 + (Δ/2) n
   ```
   and the tail defect satisfies `r_0 ≤ η_*` while opening the width contradiction gap:
   ```
     C_W + 2 C_sh r_0 < (2 H_0 - C_sh r_0) / π
   ```
-/

noncomputable section

open Real Set Filter Topology LargeSeparation

namespace LargeSeparationComplete

/-- **The complete large-separation threshold and recurrence theorem.** -/
theorem large_separation_complete
    {P Pp : ℝ → ℝ} {Delta beta C Cr beta' eta Cw Csh : ℝ}
    (hDelta : 0 < Delta) (hbeta : 0 < beta) (hbeta' : 0 < beta') (heta : 0 < eta)
    (hd : ∀ H, HasDerivAt P (Pp H) H)
    (hP : ∀ H, |P H - (H - Delta)| ≤ C * Real.exp (-beta * H))
    (hPp : ∀ H, |Pp H - 1| ≤ C * Real.exp (-beta * H)) :
    ∃ Hs : ℝ, 0 ≤ Hs ∧ ∀ H0, Hs ≤ H0 →
      (∃ H : ℕ → ℝ, H 0 = H0 ∧ (∀ n, H0 ≤ H n) ∧ (∀ n, P (H (n + 1)) = H n) ∧
        (∀ n : ℕ, H0 + Delta / 2 * n ≤ H n)) ∧
      Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)) ≤ eta ∧
      Cw + 2 * Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)))
        < (2 * H0 - Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)))) / Real.pi := by
  obtain ⟨Hs, hHs0, hHs⟩ :=
    exists_large_separation_threshold (Cr := Cr) (beta' := beta') (eta := eta) (Cw := Cw) (Csh := Csh)
      (P := P) (Pp := Pp) (Delta := Delta) (beta := beta) (C := C)
      hDelta hbeta hbeta' heta hd hP hPp
  refine ⟨Hs, hHs0, ?_⟩
  intro H0 hH0
  obtain ⟨⟨-, -, H, hH0_eq, hHge, hPrec, hHgrowth⟩, hsm, hgp⟩ := hHs H0 hH0
  exact ⟨⟨H, hH0_eq, hHge, hPrec, hHgrowth⟩, hsm, hgp⟩

end LargeSeparationComplete
