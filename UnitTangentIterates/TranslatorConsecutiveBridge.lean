import Mathlib
import UnitTangentIterates.PaperHairpinQuantitativeData
import UnitTangentIterates.TranslatorTranslation

/-!
# From the translating hairpin to the consecutive quantitative package

The model-orbit defect estimate of the paper — item (b) of the open list — is
assembled by `CanonicalConfiguredModelCapstone` from a
`PaperHairpinQuantitativeData.ConsecutiveData` on one fixed profile, and that
package is produced by `ConsecutiveData.exists_of_smooth_extension`.  Feeding
the constructed translating hairpin into it is blocked by an API mismatch, and
this file makes the mismatch precise, closing the half of it that is closable.

`TranslatorTranslation.exists_translating_hairpin_translation` produces the
profile with

* `∀ t, 0 < f t` — positivity on the whole line, from the barriers;
* `∀ n : ℕ, ContDiffOn ℝ n f (Ioo 0 π)` — smoothness of every finite order on
  the **open angle interval**;

while `exists_of_smooth_extension` asks for

* `ContDiffOn ℝ ∞ f (Ioo (-r) (π + r))` for some `r > 0`.

Two things separate them, and only one is real:

1. `∀ n : ℕ, ContDiffOn ℝ n f s` and `ContDiffOn ℝ ∞ f s` are *equivalent*
   (`contDiffOn_infty`); this file discharges that half.
2. The interval must be widened past the endpoints.  That is a genuine
   analytic statement — smoothness on `(0, π)` does not by itself extend to a
   neighbourhood of `[0, π]` — and the paper never needs it, because every
   angle it uses lies in `(0, π)`.  It is *not* proved here and is not assumed
   anywhere: `exists_consecutiveData_of_profile` below takes the widened
   interval as an explicit hypothesis, in exactly the form the translator
   construction would have to deliver it.

Main results: `contDiffOn_infty_of_forall_nat`,
`exists_consecutiveData_of_profile`.
-/

noncomputable section

open Set
open scoped ContDiff

namespace TranslatorConsecutiveBridge

/-- Smoothness of every finite order is smoothness of infinite order.  This is
the half of the profile-regularity mismatch that is purely notational. -/
theorem contDiffOn_infty_of_forall_nat {f : ℝ → ℝ} {s : Set ℝ}
    (h : ∀ n : ℕ, ContDiffOn ℝ n f s) : ContDiffOn ℝ ∞ f s :=
  contDiffOn_infty.mpr h

/-- **The consecutive quantitative package from a translator profile.**  This
is `ConsecutiveData.exists_of_smooth_extension` restated in exactly the shape
the translating-hairpin construction delivers its output: smoothness of every
finite order, and positivity on the whole line rather than on the interval.

The only hypothesis that the construction of
`TranslatorTranslation.exists_translating_hairpin_translation` does not yet
supply is the *width* of the interval: it proves smoothness on `Ioo 0 π`,
whereas a neighbourhood `Ioo (-r) (π + r)` of the closed angle interval is
required in order to extend the profile smoothly to the line. -/
theorem exists_consecutiveData_of_profile {r : ℝ} (hr : 0 < r)
    {f g gp : ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n f (Ioo (-r) (Real.pi + r)))
    (hfpos : ∀ t, 0 < f t)
    (translator : PaperHairpinQuantitativeData.TranslatorData f g gp) :
    ∃ (F theta x yp : ℝ → ℝ) (M Delta beta C Ht : ℝ) (P Pp : ℝ → ℝ),
      ContDiff ℝ ∞ F ∧ (∀ t, 0 < F t) ∧
      Nonempty (PaperHairpinQuantitativeData.Data F theta x M Delta beta C Ht P Pp) ∧
      Nonempty (PaperHairpinQuantitativeData.ConsecutiveData
        F theta x g gp yp M Delta beta C Ht P Pp) :=
  PaperHairpinQuantitativeData.ConsecutiveData.exists_of_smooth_extension hr
    (contDiffOn_infty_of_forall_nat hsmooth) (fun t _ => hfpos t) translator

end TranslatorConsecutiveBridge
