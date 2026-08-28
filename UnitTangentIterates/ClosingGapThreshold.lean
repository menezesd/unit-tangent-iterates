import UnitTangentIterates.ShadowingTails
import UnitTangentIterates.Width

/-!
# The closing width gap is met at large separation

The floor-free closing theorem takes

```
  Cw + 2·(Csh·tail) < (2H₀ − Csh·tail)/π .
```

Read as a condition on `H₀` this is `2H₀ > πCw + (2π+1)r₀` with
`r₀ = Csh·tail` — a *lower bound on the initial separation*, nothing more.

`width_gap_of_large` states exactly that, and
`exists_width_gap_threshold` records the explicit threshold.

Both inputs are controlled: the model width `Cw` is bounded uniformly in `H`
(`WidthUniform.exists_uniform_width_bound`, and bounded below by
`exists_uniform_width_lower`), while `r₀` is a tail of a summable series and so
can be made small by starting the orbit later.  Since `H₀` may be taken as large
as one likes — the configured model sequence has `Hₙ → ∞` — the gap is met.

This is the paper's "sufficiently large separation" step, in the form the
formalization needs it.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real


namespace ClosingGap

/-- **The width gap holds at large separation.**  The closing hypothesis
`Cw + 2r₀ < (2H₀ − r₀)/π` is a lower bound on `H₀`: it says
`2H₀ > πCw + (2π+1)r₀`.  Since the model width `Cw` is bounded uniformly and the
shadowing tail `r₀` tends to zero, the gap is met by taking the initial
separation large. -/
theorem width_gap_of_large {Cw r0 H0 : ℝ} (hCw : 0 ≤ Cw) (hr0 : 0 ≤ r0)
    (hH0 : (Real.pi * Cw + (2 * Real.pi + 1) * r0) / 2 < H0) :
    Cw + 2 * r0 < (2 * H0 - r0) / Real.pi := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rw [lt_div_iff₀ hpi]
  nlinarith [hH0, hpi, hCw, hr0]

/-- The threshold is explicit: any `H₀` past it works. -/
theorem exists_width_gap_threshold {Cw r0 : ℝ} (hCw : 0 ≤ Cw) (hr0 : 0 ≤ r0) :
    ∃ Hstar : ℝ, ∀ H0, Hstar < H0 →
      Cw + 2 * r0 < (2 * H0 - r0) / Real.pi :=
  ⟨(Real.pi * Cw + (2 * Real.pi + 1) * r0) / 2,
    fun H0 hH0 => width_gap_of_large hCw hr0 hH0⟩

end ClosingGap
