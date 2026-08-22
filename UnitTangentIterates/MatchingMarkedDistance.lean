import Mathlib
import UnitTangentIterates.MatchingComplete
import UnitTangentIterates.CurvatureStabilityL1

/-!
# The matching estimate in the metric of the space of marked curves

`MatchingComplete.curvature_measure_matching_complete` proves the paper's
theorem *Curvature-measure matching* in the form

```
  ∫_{J_H} |k_H − K_P| ≤ C e^{−βH} ,
```

an `L¹` comparison of the rear curvature of the two-cap pair at separation `H`
with the periodized front curvature over one fundamental interval `J_H`, of
length `P`.  The defect estimate of the model pseudo-orbit, on the other hand,
is asked in the **metric of the space of marked curves**.

`CurvatureStabilityL1.dist_le_of_L1_curvature_close` is the passage between the
two, and this file applies it to the output of the matching theorem: for two
members of the tube of the same perimeter `L`, aligned in position and
direction at the marked point, carrying the two curvatures of the matching
estimate — `P`-periodic, with derivatives bounded by `M/2` — the marked
distance is at most

`l1Modulus M (C e^{−βH}) P · L² (1 + kb L)`,
`l1Modulus M ε P = max (√(2Mε), 4ε/P)`.

This is the form consumed by `MainTheoremModelL1.lean`.  What is still not
supplied is the identification of the two marked curves themselves — that the
`n`-th model front and the marked selected inverse of the `(n+1)`-st are the
two curves of a matching configuration — so the paper's main theorem remains
**not** formalized.  For the same reason the statement below carries two blocks
of hypotheses, those of the matching estimate and those of the two marked
curves, whose *joint* satisfiability is not checked here; each block is checked
separately (`MatchingCompleteInstance.lean` for the first), and the paper's
two-cap pairs are the intended common instance.
-/

noncomputable section

open MeasureTheory Set Function

namespace MatchingMarkedDistance

open FrontPeriodization MatchingExponential MatchingComplete CurvatureStabilityL1 MarkedSpace

/-- **The matching estimate in the marked distance.**  All the hypotheses of
`MatchingComplete.curvature_measure_matching_complete` are kept, and the two
curvatures of that estimate are carried by two members `p`, `q` of the tube of
the same perimeter `L`, aligned at the marked point; both curvatures are
`P`-periodic with derivatives bounded by `M/2`, and the second is bounded by
`kb`.  Then the two marked curves are at distance at most
`l1Modulus M (C e^{−βH}) P · L²(1 + kb L)`, `C` being the explicit constant of
the matching theorem. -/
theorem dist_le_of_matching
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
    (hPeriod : xH (H / 2) = xH (-(H / 2)) + P) (hPpos : 0 < P)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hp : xH (-(H / 2)) ≤ 0) (hqe : 0 ≤ xH (-(H / 2)) + P)
    (hpB : xH (-(H / 2)) ≤ -(H / 2) + B) (hqB : H / 2 - B ≤ xH (-(H / 2)) + P)
    (hhalf : Real.exp (-(beta * P)) ≤ 1 / 2)
    (hyu : Continuous yu) (hyu' : Continuous yu')
    (hyu0 : ∀ s, 0 ≤ yu s) (hyub : ∀ s, yu s ≤ CU * Real.exp (-alpha * |s|))
    (hDU : 0 ≤ DU) (hyu'b : ∀ s, |yu' s| ≤ DU * yu s)
    (hau0 : 0 ≤ au) (hau1 : au < 1) (hYau : ∀ u, (∑' m : ℤ, yu (u - m * P)) ≤ au)
    (hKstaru : ∀ s, Kstar s = yu s + G (yu s) * yu' s)
    (hKPu : ∀ u, KP u = (∑' m : ℤ, yu (u - m * P))
      + G (∑' m : ℤ, yu (u - m * P)) * (∑' m : ℤ, yu' (u - m * P)))
    (hPH : H - 2 * B ≤ P)
    -- the two marked curves carrying the two curvatures
    {cc kmin delta L kb M : ℝ} {pt qt : Data} {Θp Θq kH' KP' : ℝ → ℝ}
    (hcc : 0 < cc) (hpt : IsTubeMember cc kmin delta pt) (hqt : IsTubeMember cc kmin delta qt)
    (hLp : perim pt = L) (hLq : perim qt = L)
    (hevp : ∀ s, HasDerivAt (ev pt) (Complex.exp (Complex.I * (Θp s : ℂ))) s)
    (hevq : ∀ s, HasDerivAt (ev qt) (Complex.exp (Complex.I * (Θq s : ℂ))) s)
    (hΘp : ∀ s, HasDerivAt Θp (kH s) s) (hΘq : ∀ s, HasDerivAt Θq (KP s) s)
    (hF0 : ev pt 0 = ev qt 0) (hΘ0 : Θp 0 = Θq 0)
    (hMpos : 0 < M)
    (hperp : Periodic kH P) (hperq : Periodic KP P)
    (hdp : ∀ u, HasDerivAt kH (kH' u) u) (hdq : ∀ u, HasDerivAt KP (KP' u) u)
    (hbp : ∀ u, |kH' u| ≤ M / 2) (hbq : ∀ u, |KP' u| ≤ M / 2)
    (hkb : ∀ u, |KP u| ≤ kb) :
    dist pt qt ≤ l1Modulus M ((pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
          + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
        * Real.exp (-(beta * H))) P * L ^ 2 * (1 + kb * L) := by
  have hmatch := curvature_measure_matching_complete ha hy0 hyb hH hq2 hYdef ha0 ha1 hY hy
    hYa hya hxH hx h0 hid hK hKderiv hKd' hKcont hbeta0 hbeta hk hkcont hKbar hD hi0 hi2
    hPeriod hPpos hKint hK0 hKbd hp hqe hpB hqB hhalf hyu hyu' hyu0 hyub hDU hyu'b hau0
    hau1 hYau hKstaru hKPu hPH
  rw [hPeriod] at hmatch
  exact dist_le_of_L1_curvature_close hcc hpt hqt hLp hLq hevp hevq hΘp hΘq hF0 hΘ0
    hPpos hMpos hperp hperq hdp hdq hbp hbq hmatch hkb

end MatchingMarkedDistance
