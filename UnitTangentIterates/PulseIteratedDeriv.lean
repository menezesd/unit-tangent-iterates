import Mathlib
import UnitTangentIterates.PulseRelativeHigherOrder

/-!
# The front-arclength pulse derivatives are the iterated derivatives

`PulseFromCurvature` and `ShiftedCurvatureJetMajorant` build the successive
front-arclength derivatives of the steering pulse `y` as *named functions*
`pulseD`, `pulseDD`, `pulseDDD`, `pulseDDDD`, each proved to be the derivative
of the previous one.  The quantitative packages, however, state their bounds
against `iteratedDeriv j y`
(`PaperHairpinQuantitativeData.Data.relative`, `decay`).

This file identifies the two, so that the relative bounds obtained on the
paper's endpoint-free route — the bounded-shift Harnack estimate and the
shifted curvature identity — can be read as bounds on `iteratedDeriv j y`.

That matters because it is the only thing standing between the Harnack route and
`Data.relative` at the orders the development actually consumes: a grep shows
`relative` is used at `j = 0,1,2,3,4` and nowhere else
(`CanonicalConsecutivePulseJet`).  The alternative route, through
`RelativeDerivatives.abs_iteratedDeriv_le`, obtains its constants from
compactness of `Icc 0 π` and is what forces the global `ContDiff ℝ ∞ f`
hypothesis on the profile.

Main results: `iteratedDeriv_one_pulse` … `iteratedDeriv_four_pulse`,
and the relative bounds `abs_iteratedDeriv_three_pulse_le`,
`abs_iteratedDeriv_four_pulse_le`.
-/

noncomputable section

open PulseFromCurvature ShiftedCurvatureJetMajorant

namespace PulseIteratedDeriv

variable {K K1 K2 K3 K4 x : ℝ → ℝ}

section Chain

variable (hKc : Continuous K) (hxinv : ∀ s, frontLen K (x s) = s)

include hKc hxinv

/-- `y' = pulseD`. -/
theorem iteratedDeriv_one_pulse (hK : ∀ u, HasDerivAt K (K1 u) u) :
    iteratedDeriv 1 (pulse K x) = pulseD K K1 x := by
  funext s
  rw [iteratedDeriv_one]
  exact (hasDerivAt_pulse hKc hxinv hK s).deriv

/-- `y'' = pulseDD`. -/
theorem iteratedDeriv_two_pulse (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u) :
    iteratedDeriv 2 (pulse K x) = pulseDD K K1 K2 x := by
  funext s
  rw [iteratedDeriv_succ, iteratedDeriv_one_pulse hKc hxinv hK]
  exact (hasDerivAt_pulseD hKc hxinv hK hK1 s).deriv

/-- `y''' = pulseDDD`. -/
theorem iteratedDeriv_three_pulse (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hx : ∀ s, HasDerivAt x (1 / Real.sqrt (1 + K (x s) ^ 2)) s) :
    iteratedDeriv 3 (pulse K x) = pulseDDD K K1 K2 x := by
  funext s
  rw [iteratedDeriv_succ, iteratedDeriv_two_pulse hKc hxinv hK hK1]
  exact (hasDerivAt_pulseDD_pulseDDD (K3 := K3) hK hK1 hK2 hx s).deriv

/-- `y'''' = pulseDDDD`. -/
theorem iteratedDeriv_four_pulse (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hx : ∀ s, HasDerivAt x (1 / Real.sqrt (1 + K (x s) ^ 2)) s)
    (hddd : ∀ s, HasDerivAt (pulseDDD K K1 K2 x) (pulseDDDD K K1 K2 x s) s) :
    iteratedDeriv 4 (pulse K x) = pulseDDDD K K1 K2 x := by
  funext s
  rw [iteratedDeriv_succ, iteratedDeriv_three_pulse hKc hxinv hK hK1 hK2 hx]
  exact (hddd s).deriv

end Chain

/-- **`eq:relative-y-derivatives` at order three, for `iteratedDeriv`.**  The
bound obtained on the paper's endpoint-free route, in the form the quantitative
packages consume. -/
theorem abs_iteratedDeriv_three_pulse_le {B D1 D2 D3 : ℝ}
    (hKc : Continuous K) (hxinv : ∀ s, frontLen K (x s) = s)
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hx : ∀ s, HasDerivAt x (1 / Real.sqrt (1 + K (x s) ^ 2)) s)
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hRK1 : RelMajorant K K1 D1) (hRK2 : RelMajorant K K2 D2)
    (hRK3 : RelMajorant K K3 D3) (s : ℝ) :
    |iteratedDeriv 3 (pulse K x) s|
      ≤ (pulseThirdConstant B D1 D2 D3 * Real.sqrt (1 + B ^ 2)) *
          pulse K x s := by
  rw [iteratedDeriv_three_pulse hKc hxinv hK hK1 hK2 hx]
  exact PulseRelativeHigherOrder.rel_pulse_third hK hK1 hK2 hx hK0 hKB hB
    hD1 hD2 hD3 hRK1 hRK2 hRK3 s

/-- **`eq:relative-y-derivatives` at order four, for `iteratedDeriv`.** -/
theorem abs_iteratedDeriv_four_pulse_le {B D1 D2 D3 D4 : ℝ}
    (hKc : Continuous K) (hxinv : ∀ s, frontLen K (x s) = s)
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3 : ∀ u, HasDerivAt K3 (K4 u) u)
    (hx : ∀ s, HasDerivAt x (1 / Real.sqrt (1 + K (x s) ^ 2)) s)
    (hddd : ∀ s, HasDerivAt (pulseDDD K K1 K2 x) (pulseDDDD K K1 K2 x s) s)
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) (hD4 : 0 ≤ D4)
    (hRK1 : RelMajorant K K1 D1) (hRK2 : RelMajorant K K2 D2)
    (hRK3 : RelMajorant K K3 D3) (hRK4 : RelMajorant K K4 D4)
    (hC4 : 0 ≤ PulseHigherDerivativeBridge.pulseFourthConstant B D1 D2 D3 D4)
    (s : ℝ) :
    |iteratedDeriv 4 (pulse K x) s|
      ≤ (PulseHigherDerivativeBridge.pulseFourthConstant B D1 D2 D3 D4 *
          Real.sqrt (1 + B ^ 2)) * pulse K x s := by
  rw [iteratedDeriv_four_pulse hKc hxinv hK hK1 hK2 hx hddd]
  exact PulseRelativeHigherOrder.rel_pulse_fourth hK hK1 hK2 hK3 hx hK0 hKB hB
    hD1 hD2 hD3 hD4 hRK1 hRK2 hRK3 hRK4 hC4 s

/-! ### Identification with the hairpin fields -/

/-- With `K = G ∘ θ` the abstract pulse of `PulseFromCurvature` **is** the
hairpin pulse: `pulse (curvField f ∘ θ) x s = pulseField f (θ (x s))`.  Both
sides are `G/√(1+G²)` evaluated at the same angle, so this is definitional. -/
theorem pulse_eq_pulseField (f theta x : ℝ → ℝ) :
    pulse (fun u => HairpinRelative.curvField f (theta u)) x
      = fun s => HairpinRelative.pulseField f (theta (x s)) := rfl

/-- Likewise the abstract front length is the hairpin front arclength. -/
theorem frontLen_eq_frontArclength (f theta : ℝ → ℝ) :
    frontLen (fun u => HairpinRelative.curvField f (theta u))
      = HairpinRelative.frontArclength f theta := rfl

/-- **The order-three relative bound in the shape `Data.relative` asks for.**
The left-hand side is literally
`|iteratedDeriv 3 (fun r => pulseField f (θ (x r))) s|`. -/
theorem abs_iteratedDeriv_three_pulseField_le {f theta : ℝ → ℝ}
    {B D1 D2 D3 : ℝ}
    (hKc : Continuous fun u => HairpinRelative.curvField f (theta u))
    (hxinv : ∀ s, HairpinRelative.frontArclength f theta (x s) = s)
    (hK : ∀ u, HasDerivAt (fun v => HairpinRelative.curvField f (theta v))
      (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hx : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + HairpinRelative.curvField f (theta (x s)) ^ 2)) s)
    (hK0 : ∀ u, 0 ≤ HairpinRelative.curvField f (theta u))
    (hKB : ∀ u, HairpinRelative.curvField f (theta u) ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hRK1 : RelMajorant (fun u => HairpinRelative.curvField f (theta u)) K1 D1)
    (hRK2 : RelMajorant (fun u => HairpinRelative.curvField f (theta u)) K2 D2)
    (hRK3 : RelMajorant (fun u => HairpinRelative.curvField f (theta u)) K3 D3)
    (s : ℝ) :
    |iteratedDeriv 3 (fun r => HairpinRelative.pulseField f (theta (x r))) s|
      ≤ (pulseThirdConstant B D1 D2 D3 * Real.sqrt (1 + B ^ 2)) *
          HairpinRelative.pulseField f (theta (x s)) :=
  abs_iteratedDeriv_three_pulse_le hKc hxinv hK hK1 hK2 hx hK0 hKB hB
    hD1 hD2 hD3 hRK1 hRK2 hRK3 s

end PulseIteratedDeriv
