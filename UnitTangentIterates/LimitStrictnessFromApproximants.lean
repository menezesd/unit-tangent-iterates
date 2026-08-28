import UnitTangentIterates.LimitStrictnessHarnack
set_option maxHeartbeats 1000000
open Set Real Filter Topology Function MarkedSpace

namespace UnconditionalAssembly

/-- **The strictness data of a `C²` limit, from its approximants.**  Every field
is either a `C²` datum of the limit — the curve, angle and curvature derivative
relations, periodicity, nonnegativity — or the Harnack inequality, which passes
to the limit from the approximating curvatures by `harnack_of_tendsto`.

No third derivative, no pointwise bicycle identity, and no arclength
correspondence between the levels is used: the approximants enter only through
pointwise convergence of their curvatures. -/
def limitStrictnessDataH_of_tendsto {p : MarkedSpace.Data} {theta k : ℝ → ℝ}
    {kn : ℕ → ℝ → ℝ}
    (hcurve : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I * (theta s : ℂ))) s)
    (hangle : ∀ s, HasDerivAt theta (k s) s)
    (hper : Periodic k (MarkedSpace.perim p))
    (hnn : ∀ s, 0 ≤ k s)
    (hconv : ∀ x, Tendsto (fun n => kn n x) atTop (nhds (k x)))
    (hharn : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (kn n a / Real.sqrt (1 + kn n a ^ 2))
        ≤ kn n b / Real.sqrt (1 + kn n b ^ 2))
    (hne : ∃ s, k s ≠ 0) : LimitStrictnessDataH p where
  theta := theta
  k := k
  curve_deriv := hcurve
  angle_deriv := hangle
  curvature_periodic := hper
  curvature_nonnegative := hnn
  curvature_harnack := UnitTangent.harnack_of_tendsto hconv hharn
  curvature_nonzero := hne

/-- Hence the limit is an oval, with the same inputs. -/
theorem isOval_ev_of_tendsto {p : MarkedSpace.Data} {c dlt : ℝ}
    {theta k : ℝ → ℝ} {kn : ℕ → ℝ → ℝ}
    (hc : 0 < c) (hdlt : 0 < dlt)
    (hp : MarkedSpace.IsTubeMember c 0 dlt p)
    (hcurve : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I * (theta s : ℂ))) s)
    (hangle : ∀ s, HasDerivAt theta (k s) s)
    (hper : Periodic k (MarkedSpace.perim p))
    (hnn : ∀ s, 0 ≤ k s)
    (hconv : ∀ x, Tendsto (fun n => kn n x) atTop (nhds (k x)))
    (hharn : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (kn n a / Real.sqrt (1 + kn n a ^ 2))
        ≤ kn n b / Real.sqrt (1 + kn n b ^ 2))
    (hne : ∃ s, k s ≠ 0) : MainTheoremConditional.IsOval (ev p) :=
  isOval_ev_of_limitStrictnessDataH hc hdlt hp
    (limitStrictnessDataH_of_tendsto hcurve hangle hper hnn hconv hharn hne)

end UnconditionalAssembly
