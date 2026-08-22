import Mathlib
import UnitTangentIterates.MatchingPathDist
import UnitTangentIterates.PeriodizedCurvatureDeriv

/-!
# The matching estimate with the model side produced from its pulse

`MatchingPathDist.pathDist_le_of_matching` bounds the marked path
pseudodistance of the two curves of a matching configuration, but it *assumes*
that the periodized model curvature `K_P` is the curvature of a marked oval:
continuous, `C¹` with a bounded derivative, `P`-periodic, of total turning `π`
and pinched between `0` and `κ_*`.

`PeriodizedCurvatureDeriv.frontCurv_marked_oval_data` derives all of that from
the model pulse.  This file substitutes it, so that on the model side only
hypotheses about the pulse `y_u` remain — nonnegative, `C²`, with the relative
derivative bounds `|y_u'| ≤ D_U y_u` and `|y_u''| ≤ D_U2 y_u`, of mass `π`,
with a periodization below `a_u < 1` and `G(a_u)D_U ≤ 1` — together with the
requirement that the constants `κ_*` and `k'` of the interpolation dominate the
explicit constants produced from the pulse.
-/

noncomputable section

open Real MeasureTheory Set Function MarkedSpace PathMetric

namespace MatchingPathDistModel

open FrontPeriodization MatchingExponential MatchingComplete
  CurvatureInterpolation InterpolationEstimate InterpolationPathDist
  InterpolationPathDistL1 InterpolationPathDistSummable MatchingPathDist
  PeriodizedCurvatureDeriv

/-- **The matching estimate in the marked path pseudodistance, with the model
side produced from its pulse.**  Every hypothesis of
`MatchingPathDist.pathDist_le_of_matching` about the model curvature `K_P` is
replaced by hypotheses on the model pulse, from which
`PeriodizedCurvatureDeriv.frontCurv_marked_oval_data` produces them. -/
theorem pathDist_le_of_matching_model
    {Y y xH x Kstar Kstar' kH Kbar KP yu yu' yu'' : ℝ → ℝ}
    {a au C CU CK DU DU2 alpha beta H P B Km Kd : ℝ}
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
    -- the hairpin curvature as the curvature of a marked oval of half-perimeter `P`
    {kH' : ℝ → ℝ} {theta0 kstar kd eps0 : ℝ}
    (hkHc : Continuous kH) (hkH'c : Continuous kH')
    (hperp : Periodic kH P)
    (htot0 : (∫ r in (0:ℝ)..P, kH r) = Real.pi)
    (hkd : 0 < kd) (hkstar : 0 ≤ kstar)
    (hd0 : ∀ r, HasDerivAt kH (kH' r) r) (hkd0 : ∀ r, |kH' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ kH r) (hk0le : ∀ r, kH r ≤ kstar)
    -- the model curvature, produced from the model pulse alone
    (hyuderiv : ∀ s, HasDerivAt yu (yu' s) s) (hyu2 : ∀ s, HasDerivAt yu' (yu'' s) s)
    (hyu''c : Continuous yu'') (hDU2 : 0 ≤ DU2) (hyu''b : ∀ s, |yu'' s| ≤ DU2 * yu s)
    (hyuint : Integrable yu) (hyumass : (∫ s : ℝ, yu s) = Real.pi)
    (hsmall : G au * DU ≤ 1)
    (hkstarge : (1 + G au * DU) * au ≤ kstar)
    (hkdge : DU * au + lipConst au * (DU ^ 2 * au ^ 2) + G au * (DU2 * au) ≤ kd)
    (heps0 : (pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
        + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
      * Real.exp (-(beta * H)) ≤ eps0) :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * P) ∧
      ∀ p q : Data, (∀ u, p.1 u = interpCurve kH theta0 P (2 * P * u)) →
        (∀ u, q.1 u = interpCurve KP theta0 P (psi u)) →
        pathDist p q ≤ interpCostL1 kstar kd P eps0
          ((pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
              + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
            * Real.exp (-(beta * H))) := by
  have hCU0 : 0 ≤ CU := by
    have h := hyub 0
    have h0 := hyu0 0
    simp at h
    linarith
  set CC : ℝ := CU * (1 + DU + DU2) with hCC
  have hyuabs : ∀ s, |yu s| ≤ CC * Real.exp (-alpha * |s|) := by
    intro s
    have hexp : (0:ℝ) < Real.exp (-alpha * |s|) := Real.exp_pos _
    rw [abs_of_nonneg (hyu0 s)]
    refine le_trans (hyub s) ?_
    have hle : CU ≤ CC := by nlinarith
    exact mul_le_mul_of_nonneg_right hle hexp.le
  have hyu'abs : ∀ s, |yu' s| ≤ CC * Real.exp (-alpha * |s|) := by
    intro s
    have hexp : (0:ℝ) < Real.exp (-alpha * |s|) := Real.exp_pos _
    refine le_trans (hyu'b s) (le_trans (mul_le_mul_of_nonneg_left (hyub s) hDU) ?_)
    have hle : DU * CU ≤ CC := by nlinarith
    calc DU * (CU * Real.exp (-alpha * |s|)) = DU * CU * Real.exp (-alpha * |s|) := by ring
      _ ≤ CC * Real.exp (-alpha * |s|) := mul_le_mul_of_nonneg_right hle hexp.le
  have hyu''abs : ∀ s, |yu'' s| ≤ CC * Real.exp (-alpha * |s|) := by
    intro s
    have hexp : (0:ℝ) < Real.exp (-alpha * |s|) := Real.exp_pos _
    refine le_trans (hyu''b s) (le_trans (mul_le_mul_of_nonneg_left (hyub s) hDU2) ?_)
    have hle : DU2 * CU ≤ CC := by nlinarith
    calc DU2 * (CU * Real.exp (-alpha * |s|)) = DU2 * CU * Real.exp (-alpha * |s|) := by ring
      _ ≤ CC * Real.exp (-alpha * |s|) := mul_le_mul_of_nonneg_right hle hexp.le
  obtain ⟨K, K', hKu, hKc, hK'c, hKper, hKtot, hKderiv2, hK'b, hKnn, hKle⟩ :=
    frontCurv_marked_oval_data (y := yu) (y' := yu') (y'' := yu'') (C := CC) (a := au)
      (P := P) ha hPpos hDU hDU2 hyuderiv hyu2 hyu''c hyuabs hyu'abs hyu''abs hyu0
      hyuint hyumass hyu'b hyu''b hau0 hau1 hYau hsmall
  have hKPeq : KP = K := funext fun u => (hKPu u).trans (hKu u).symm
  subst hKPeq
  exact pathDist_le_of_matching ha hy0 hyb hH hq2 hYdef ha0 ha1 hY hy hYa hya hxH hx h0 hid
    hK hKderiv hKd' hKcont hbeta0 hbeta hk hkcont hKbar hD hi0 hi2 hPeriod hPpos hKint
    hK0 hKbd hp hqe hpB hqB hhalf hyu hyu' hyu0 hyub hDU hyu'b hau0 hau1 hYau hKstaru
    hKPu hPH hkHc hKc hkH'c hK'c hperp hKper htot0 hKtot hkd hkstar hd0 hKderiv2 hkd0
    (fun r => le_trans (hK'b r) hkdge) hk0nn hKnn hk0le
    (fun r => le_trans (hKle r) hkstarge) heps0

end MatchingPathDistModel
