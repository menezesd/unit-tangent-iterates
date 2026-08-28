import UnitTangentIterates.ConfiguredActualHalfScalarStart

/-!
# Canonical scalar choices for the actual-half start

The scalar start does not select the analytic row coefficients.  It works for
every nonnegative pair of envelope parameters.  This module records that fact
without coupling it to either the legacy affine correlated provider or the
marking-aware physical-front recursion.
-/

noncomputable section

namespace ConfiguredActualHalfScalarChoice

/-- A permitted pair of scalar envelope parameters.  The genuine analytic row
producer may choose a larger pair; no scalar separation theorem constrains the
choice beyond nonnegativity. -/
structure Choice where
  MA0 : ℝ
  NA0 : ℝ
  MA0_nonnegative : 0 ≤ MA0
  NA0_nonnegative : 0 ≤ NA0

/-- The canonical scalar-only choice.  This is sufficient to construct the
model, width, large-separation, and pair-source output.  It is not asserted to
dominate the coefficients of the still-missing marking-aware row producer. -/
def zero : Choice where
  MA0 := 0
  NA0 := 0
  MA0_nonnegative := le_rfl
  NA0_nonnegative := le_rfl

/-- Scalar start for any envelope choice supplied by the analytic producer. -/
theorem exists_output_of_choice
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10)
    (C : Choice) :
    Nonempty (ConfiguredActualHalfScalarStart.Output C.MA0 C.NA0) :=
  ConfiguredActualHalfScalarStart.exists_output_of_eps
    heps heps10 C.MA0_nonnegative C.NA0_nonnegative

/-- In particular, scalar construction itself has a completely explicit
choice of envelope parameters. -/
theorem exists_output_zero_of_eps
    {eps : ℝ} (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) :
    Nonempty (ConfiguredActualHalfScalarStart.Output zero.MA0 zero.NA0) :=
  exists_output_of_choice heps heps10 zero

end ConfiguredActualHalfScalarChoice

