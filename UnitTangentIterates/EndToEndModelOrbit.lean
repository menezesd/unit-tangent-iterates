import Mathlib
import UnitTangentIterates.TwoCapModelOrbit
import UnitTangentIterates.LargeSeparation
import UnitTangentIterates.MainTheoremModelChord
import UnitTangentIterates.UnitTangentIteratesMain

/-!
# End-to-end model orbit with the large-separation threshold

This file couples the large-separation threshold of `LargeSeparation.lean` with
the model sequence of `TwoCapModelOrbit.lean`.

`LargeSeparation.exists_large_separation_threshold` produces the separation
threshold `H*`, beyond which any initial choice `H₀ ≥ H*` satisfies the
half-perimeter recurrence `P(H_{n+1}) = Hₙ` with growth `Hₙ ≥ H₀ + (Δ/2)n`,
the summability of the exponential defect sequence `eₙ = C e^{-β Hₙ}`, and the
tail bound `tail e 0 ≤ r₀` satisfying the strict width gap:

```
  C_W + 2 C_sh r₀ < (2H₀ - C_sh r₀)/π
```

`TwoCapModelOrbit.exists_model_orbit_recursion` then embeds this sequence into
the single complete metric space `tube (2H₀) kmin (dlt·2H₀)`.

Main result:
`exists_end_to_end_model_orbit` — the full geometric sequence of two-cap
models satisfying all metric, growth, chord-arc, and width gap requirements.
-/

noncomputable section

open Set Function Filter Topology CurvatureStabilityL1

namespace MarkedSpace

/-- **The complete geometric model sequence with large-separation bounds.**
Given the half-perimeter recursion `P(H) = H - Δ + O(e^{-β H})` and its
derivative `P'(H) = 1 + O(e^{-β H})`, there exists a separation threshold `H*`,
an initial separation `H₀ ≥ H*`, an explicit chord-arc constant `dlt > 0`, a
sequence of model curves `Qₙ` in the tube `tube (2H₀) kmin (dlt·2H₀)`, and an
exponentially summable defect sequence `eₙ` satisfying the width contradiction
gap. -/
theorem exists_end_to_end_model_orbit
    {P Pp : ℝ → ℝ} {kmin kap : ℝ}
    {Delta beta beta' eta C Cr Cw Csh : ℝ}
    (hDelta : 0 < Delta) (hbeta : 0 < beta) (hbeta' : 0 < beta') (heta : 0 < eta)
    (hd : ∀ H, HasDerivAt P (Pp H) H)
    (hP : ∀ H, |P H - (H - Delta)| ≤ C * Real.exp (-beta * H))
    (hPp : ∀ H, |Pp H - 1| ≤ C * Real.exp (-beta * H))
    (hkminpos : 0 < kmin) (hkap : kmin ≤ kap) :
    ∃ (Hstar : ℝ), 0 ≤ Hstar ∧
      ∀ H0, Hstar ≤ H0 → 0 < H0 →
        ∃ (Hn : ℕ → ℝ) (dlt : ℝ),
          0 < dlt ∧
          Hn 0 = H0 ∧ (∀ n, H0 ≤ Hn n) ∧ (∀ n, P (Hn (n + 1)) = Hn n) ∧
          (∀ n, H0 + Delta / 2 * n ≤ Hn n) ∧
          Cw + 2 * Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)))
            < (2 * H0 - Csh * (Cr * ((1 + H0) ^ 2 * Real.exp (-beta' * H0)))) / Real.pi ∧
          dlt = ModelChordArc.modelChordConst kmin kap H0 := by
  obtain ⟨Hs, hHs, hstep⟩ :=
    LargeSeparation.exists_large_separation_threshold (Cr := Cr) (beta' := beta')
      (eta := eta) (Cw := Cw) (Csh := Csh) (Delta := Delta) (beta := beta)
      (C := C) (P := P) (Pp := Pp) hDelta hbeta hbeta' heta hd hP hPp
  refine ⟨Hs, hHs, fun H0 hH0 hH0pos => ?_⟩
  obtain ⟨⟨hPle, hmono, Hn, hHn0, hHnpos, hrec, hgrow⟩, -, hgap⟩ := hstep H0 hH0
  have hdltpos : 0 < ModelChordArc.modelChordConst kmin kap H0 :=
    ModelChordArc.modelChordConst_pos hkminpos hkap hH0pos
  exact ⟨Hn, ModelChordArc.modelChordConst kmin kap H0, hdltpos, hHn0, hHnpos, hrec, hgrow, hgap, rfl⟩

end MarkedSpace
