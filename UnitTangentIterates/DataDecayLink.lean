import Mathlib
import UnitTangentIterates.PaperHairpinQuantitativeData

/-!
# The decay constant of `Data` is used only as an opaque scalar

A census of the projections of `PaperHairpinQuantitativeData.Data` across the
whole development shows that the field

```
  decay : ∀ j s, |iteratedDeriv j (fun r => pulseField f (θ (x r))) s|
            ≤ decayConst j * Real.exp (-|s| / M)
```

is **never cited**: the only consumer of anything decay-related is
`Data.exists_profileConstants_of_wide`, which takes `CU := d.decayConst 0` and
feeds it, as a bare real number, into `PaperHairpinConfig.ProfileConstants`.

That makes the field look removable — and removing it would indeed leave the
development compiling, which would materially shorten the interior-regularity
route, since exponential tails are the half of the relative-derivative work that
the endpoint-free Harnack argument has not yet been carried through for.

**It must not be removed.**  `CU` is not an inert scalar downstream: it appears
in `PaperHairpinConfig.PulsePairAnalyticData.previous_decay`,

```
  previous_decay : ∀ s, yu s ≤ CU * Real.exp (-alpha * |s|),
```

a genuine bound on the prior pulse.  If `decayConst 0` were an arbitrary
constant — say `0` — the `ProfileConstants` obligations would still be
satisfiable, but the `previous_decay` hypothesis at the point of use would
become unsatisfiable for any positive pulse.  The field is load-bearing through
its *meaning*, not through any citation.

This file removes the trap by recording the link explicitly, so that the
constant handed to `ProfileConstants` is visibly a decay constant.

Main result: `decayConst_zero_bound`.
-/

noncomputable section

namespace PaperHairpinQuantitativeData

/-- **`decayConst 0` really is a decay constant for the pulse.**  This is the
`j = 0` case of `Data.decay`, stated without the `iteratedDeriv` wrapper.  It is
the fact that justifies `Data.exists_profileConstants_of_wide` taking
`CU := d.decayConst 0`, and hence the `previous_decay` field of
`PulsePairAnalyticData` downstream. -/
theorem Data.decayConst_zero_bound {f theta x : ℝ → ℝ}
    {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (d : Data f theta x M Delta beta C Ht P Pp) (s : ℝ) :
    |HairpinRelative.pulseField f (theta (x s))|
      ≤ d.decayConst 0 * Real.exp (-|s| / M) := by
  simpa using d.decay 0 (by norm_num) s

/-- The same bound without the absolute value, using nonnegativity of the
pulse along the hairpin angles. -/
theorem Data.pulse_le_decayConst_zero {f theta x : ℝ → ℝ}
    {M Delta beta C Ht : ℝ} {P Pp : ℝ → ℝ}
    (d : Data f theta x M Delta beta C Ht P Pp) (s : ℝ) :
    HairpinRelative.pulseField f (theta (x s))
      ≤ d.decayConst 0 * Real.exp (-|s| / M) :=
  (le_abs_self _).trans (d.decayConst_zero_bound s)

end PaperHairpinQuantitativeData
