import Mathlib
import UnitTangentIterates.MatchingExponential
import UnitTangentIterates.FrontPeriodizationIntegral

/-!
# Curvature-measure matching with all four error terms produced

`MatchingExponential.curvature_measure_matching_exp_of_pulse` states the
theorem *Curvature-measure matching* of *A Noncircular Oval with Convex
Unit-Tangent Iterates* in the paper's exponential form

```
  ∫_{J_H} |k_H − K_P| ≤ C e^{−βH} ,
```

with three of its four error terms produced from the exponential
periodization: the two pulse errors and the omitted mass.  The fourth — the
*front periodization error* — was carried as a hypothesis.

`FrontPeriodizationIntegral.front_periodization_error_exp` now produces that
term as well, and this file combines the two: the matching estimate with
**every** error term produced, the only inputs being the exponential decay of
the pulses and the elementary structural relations of the configuration.

* `frontConst` : the explicit constant of the front periodization error;
* `curvature_measure_matching_complete` : the matching theorem, with all four
  errors produced.
-/

noncomputable section

open MeasureTheory Set Function

namespace MatchingComplete

open FrontPeriodization FrontPeriodizationIntegral MatchingExponential

/-- The constant of the front periodization error: with the front pulse in the
rear arclength bounded by `CU e^{−α|·|}`, relative derivative bound `DU`,
periodization below `au < 1`, and `P ≥ H − 2B`, the error is at most
`frontConst · e^{−βH}`. -/
def frontConst (au CU DU alpha beta B : ℝ) : ℝ :=
  lipConst au * DU * (8 * CU ^ 2 / (alpha - beta)) * Real.exp (2 * beta * B)

/-- **Curvature-measure matching, with all four error terms produced.**

The hypotheses are those of
`MatchingExponential.curvature_measure_matching_exp_of_pulse`, except that the
front periodization error is no longer assumed: instead, the periodized front
curvature `K_P` is exhibited as `Y + G(Y)Y'` for the periodization `Y` of the
front pulse `yu` read in the rear arclength, and the isolated profile `K_*` as
`yu + G(yu)yu'`, with `yu` exponentially decaying and `|yu'| ≤ DU · yu`.  The
conclusion is the paper's

`∫_{J_H} |k_H − K_P| ≤ C e^{−βH}`,

with the explicit constant `pulseConst + rearTailConst + frontConst`. -/
theorem curvature_measure_matching_complete
    {Y y xH x Kstar Kstar' kH Kbar KP yu yu' : ℝ → ℝ}
    {a au C CU CK DU alpha beta H P B Km Kd : ℝ}
    (ha : 0 < alpha) (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hH : 0 < H) (hq2 : Real.exp (-alpha * H) ≤ 1 / 2)
    (hYdef : ∀ s, Y s = ∑' m : ℤ, y (s - m * H))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hY : Continuous Y) (hy : Continuous y)
    (hYa : ∀ s, |Y s| ≤ a) (hya : ∀ s, |y s| ≤ a)
    (hxH : ∀ t, HasDerivAt xH (Real.sqrt (1 - (Y t) ^ 2)) t)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t)
    (h0 : xH 0 = x 0)
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKderiv : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (hKcont : Continuous Kstar)
    (hbeta0 : 0 < beta) (hbeta : beta < alpha / 2)
    (hk : ∀ t, kH (xH t) * Real.sqrt (1 - (Y t) ^ 2) = Y t)
    (hkcont : Continuous fun u => |kH u - Kbar u|)
    (hKbar : ∀ u, Kbar u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P))
    (hD : IntervalIntegrable
      (fun s => Real.sqrt (1 - (Y s) ^ 2) *
        ∑' j : {j : ℤ // j ≠ 0}, Kstar (xH s - (j : ℤ) * P)) volume (-(H / 2)) (H / 2))
    (hi0 : IntervalIntegrable (fun u => |kH u - KP u|) volume (xH (-(H / 2))) (xH (H / 2)))
    (hi2 : IntervalIntegrable (fun u => |Kbar u - KP u|) volume (xH (-(H / 2))) (xH (H / 2)))
    (hP : xH (H / 2) = xH (-(H / 2)) + P) (hPpos : 0 < P)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hp : xH (-(H / 2)) ≤ 0) (hqe : 0 ≤ xH (-(H / 2)) + P)
    (hpB : xH (-(H / 2)) ≤ -(H / 2) + B) (hqB : H / 2 - B ≤ xH (-(H / 2)) + P)
    -- the front of period `P`, read in the rear arclength
    (hhalf : Real.exp (-(beta * P)) ≤ 1 / 2)
    (hyu : Continuous yu) (hyu' : Continuous yu')
    (hyu0 : ∀ s, 0 ≤ yu s) (hyub : ∀ s, yu s ≤ CU * Real.exp (-alpha * |s|))
    (hDU : 0 ≤ DU) (hyu'b : ∀ s, |yu' s| ≤ DU * yu s)
    (hau0 : 0 ≤ au) (hau1 : au < 1) (hYau : ∀ u, (∑' m : ℤ, yu (u - m * P)) ≤ au)
    (hKstaru : ∀ s, Kstar s = yu s + G (yu s) * yu' s)
    (hKPu : ∀ u, KP u = (∑' m : ℤ, yu (u - m * P))
      + G (∑' m : ℤ, yu (u - m * P)) * (∑' m : ℤ, yu' (u - m * P)))
    (hPH : H - 2 * B ≤ P) :
    (∫ u in (xH (-(H / 2)))..(xH (H / 2)), |kH u - KP u|)
      ≤ (pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
          + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
        * Real.exp (-(beta * H)) := by
  have h4 : (∫ u in (xH (-(H / 2)))..(xH (H / 2)), |Kbar u - KP u|)
      ≤ frontConst au CU DU alpha beta B * Real.exp (-(beta * H)) := by
    rw [hP]
    exact front_periodization_error_exp (y := yu) (yp := yu') (C := CU) (alpha := alpha)
      (beta := beta) (a := au) (D := DU) (P := P) (Kstar := Kstar) (Kbar := Kbar) (KP := KP)
      (H := H) (B := B) (q := xH (-(H / 2)))
      ha hPpos hbeta0 (by linarith) hhalf hyu hyu' hyu0 hyub hDU hyu'b hau0 hau1 hYau
      hKstaru hKbar hKPu hPH
  exact curvature_measure_matching_exp_of_pulse ha hy0 hyb hH hq2 hYdef ha0 ha1 hY hy
    hYa hya hxH hx h0 hid hK hKderiv hKd' hKcont hbeta hk hkcont hKbar hD hi0 hi2
    hP hPpos hKint hK0 hKbd hp hqe hpB hqB h4

end MatchingComplete
