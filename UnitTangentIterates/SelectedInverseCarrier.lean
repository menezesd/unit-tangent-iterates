import Mathlib
import UnitTangentIterates.MatchingPathDistRigid
import UnitTangentIterates.SelectedInverseRearOwn

/-!
# The selected inverse and the model front as carriers of the two curvatures

`MatchingPathDistRigid.pathDistRigid_le_of_matching` bounds the path
pseudodistance, modulo a rigid motion, of **any** two marked curves carrying the
two curvatures `k_H` and `K_P` of a matching configuration.  This file supplies
the two carriers the paper actually compares.

* On the model side there is nothing to do: the model front
  `TwoCapPairsAssembly.front κ θ₀ H` **is** the reconstruction
  `CurvatureInterpolation.interpCurve`, which is a carrier of its own curvature
  by construction (`interpCurve_carrier`).
* On the rear side the carrier is the **marked selected inverse**: the rear
  track written in its own arclength, `x ↦ R(sf x)`, which
  `SelectedInverseRearOwn.lean` identifies with the marked selected inverse of
  the front.  It has unit speed with tangent angle `Ψ ∘ sf` and curvature
  `tan δ ∘ sf`, and the curvature relation `k_H(x_H)·cos δ = sin δ` of the
  matching theorem says exactly that `tan δ ∘ sf` **is** `k_H`
  (`curvature_eq_tan_of_matching`), so the rear track in its own arclength is a
  carrier of `k_H` (`rearOwn_carrier`).

Results:

* `curvature_eq_tan_of_matching` — the rear curvature of a matching
  configuration is `tan δ` read in the rear arclength;
* `rearOwn_carrier` — the rear track in its own arclength carries it;
* `pathDistRigid_rearOwn_front_le` — hence a bound proved for the two
  reconstructions holds, modulo a rigid motion, between the marked rear track
  of the selected inverse and the marked model front;
* `pathDistRigid_rearOwn_front_le_of_matching` — the matching configuration
  itself bounds that pseudodistance by
  `interpCostL1 κ_* k' P ε₀ (Ce^{−βH})`.

What is still missing for the paper's defect estimate is the identification of
the *front* of the configuration with the next model of the orbit; the
comparison here is between the selected inverse of a given front and a given
model curvature.  As in `MatchingPathDist.lean`, the *joint* satisfiability of
the long hypothesis block of
`pathDistRigid_rearOwn_front_le_of_matching` — those of the matching estimate
together with those of the rear geometry — is not checked here; the hypotheses
of `rearOwn_carrier` alone are checked on the circle
(`SelectedInverseCarrierCircle.lean`).
-/

noncomputable section

open Real MeasureTheory Set Function MarkedSpace PathMetric

namespace SelectedInverseCarrier

open CurvatureInterpolation CurvatureRigidity MarkedRigid RearTrack
  SelectedInverseRearOwn FrontPeriodization MatchingExponential MatchingComplete
  InterpolationPathDist InterpolationPathDistSummable MatchingPathDist
  MatchingPathDistRigid

variable {Θ K dl sf kH : ℝ → ℝ} {F : ℝ → ℂ}

/-! ### The two carriers -/

/-- The tangent direction in the exponential form used by the rear-track files. -/
theorem tau_eq_exp (θ : ℝ) : tau θ = Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [tau, mul_comm]

/-- **The reconstruction is a carrier of its own curvature.** -/
theorem interpCurve_carrier {kappa : ℝ → ℝ} {θ₀ L : ℝ} (hk : Continuous kappa) :
    (∀ s, HasDerivAt (interpCurve kappa θ₀ L) (tau (tangentAngle kappa θ₀ s)) s) ∧
      ∀ s, HasDerivAt (tangentAngle kappa θ₀) (kappa s) s :=
  ⟨fun s => hasDerivAt_interpCurve (θ₀ := θ₀) (L := L) hk s,
    fun s => hasDerivAt_tangentAngle (θ₀ := θ₀) hk s⟩

/-- **The rear curvature of a matching configuration is `tan δ`, read in the
rear arclength.**  The relation `k_H(x_H(t))·cos δ(t) = sin δ(t)` of the theorem
*Curvature-measure matching*, together with the inversion `x_H ∘ sf = id` of the
rear arclength, determines `k_H` on the whole line. -/
theorem curvature_eq_tan_of_matching {c : ℝ} (hc : 0 < c) (hcos : ∀ s, c ≤ Real.cos (dl s))
    (hsfinv : ∀ x, rearArclength dl (sf x) = x)
    (hk : ∀ t, kH (rearArclength dl t) * Real.cos (dl t) = Real.sin (dl t)) (x : ℝ) :
    kH x = Real.tan (dl (sf x)) := by
  have hcospos : 0 < Real.cos (dl (sf x)) := lt_of_lt_of_le hc (hcos (sf x))
  have h := hk (sf x)
  rw [hsfinv x] at h
  rw [Real.tan_eq_sin_div_cos, ← h]
  field_simp

/-- **The rear track written in its own arclength is a carrier of the rear
curvature of the matching configuration.**  It has unit speed with tangent angle
`Ψ ∘ sf`, whose derivative is `tan δ ∘ sf = k_H`. -/
theorem rearOwn_carrier {c : ℝ} (hc : 0 < c) (hdc : Continuous dl)
    (hcos : ∀ s, c ≤ Real.cos (dl s)) (hsfinv : ∀ x, rearArclength dl (sf x) = x)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s)
    (hk : ∀ t, kH (rearArclength dl t) * Real.cos (dl t) = Real.sin (dl t)) :
    (∀ x, HasDerivAt (fun z => rearTrack F Θ dl (sf z))
        (tau ((fun z => rearAngle Θ dl (sf z)) x)) x) ∧
      ∀ x, HasDerivAt (fun z => rearAngle Θ dl (sf z)) (kH x) x := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [tau_eq_exp]
    exact hasDerivAt_rearOwnCurve hc hdc hcos hsfinv hF hΘ hode x
  · rw [curvature_eq_tan_of_matching hc hcos hsfinv hk x]
    exact hasDerivAt_rearOwnAngleSf hc hdc hcos hsfinv hΘ hode x

/-! ### The comparison of the selected inverse with the model front -/

/-- **A bound proved for the two reconstructions holds between the marked
selected inverse and the marked model front.**  The first marked curve is the
rear track written in its own arclength, marked at `x = 0` and read in the
normalized parameter; the second is the model front, the reconstruction from the
model curvature read in the common phase. -/
theorem pathDistRigid_rearOwn_front_le {KP : ℝ → ℝ} {θ₀ L d : ℝ} {psi : ℝ → ℝ}
    {c : ℝ} (hc : 0 < c) (hdc : Continuous dl) (hcos : ∀ s, c ≤ Real.cos (dl s))
    (hsfinv : ∀ x, rearArclength dl (sf x) = x)
    (hF : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s)
    (hkrel : ∀ t, kH (rearArclength dl t) * Real.cos (dl t) = Real.sin (dl t))
    (hkH : Continuous kH) (hKP : Continuous KP)
    (hper0 : Periodic kH L) (hper1 : Periodic KP L)
    (htot0 : (∫ r in (0:ℝ)..L, kH r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, KP r) = Real.pi)
    (hpsic : Continuous psi) (hpsi : ∀ u, psi (u + 1) = psi u + 2 * L)
    (hbound : ∀ p q : Data, (∀ u, p.1 u = interpCurve kH θ₀ L (2 * L * u)) →
      (∀ u, q.1 u = interpCurve KP θ₀ L (psi u)) → pathDist p q ≤ d)
    {p' q' : Data}
    (hp' : ∀ u, p'.1 u = rearTrack F Θ dl (sf (2 * L * u)))
    (hq' : ∀ u, q'.1 u = interpCurve KP θ₀ L (psi u)) :
    pathDistRigid p' q' ≤ d := by
  obtain ⟨hX, hthX⟩ := rearOwn_carrier (kH := kH) hc hdc hcos hsfinv hF hΘ hode hkrel
  obtain ⟨hY, hthY⟩ := interpCurve_carrier (θ₀ := θ₀) (L := L) hKP
  exact pathDistRigid_le_of_carriers (θ₀ := θ₀) hkH hKP hper0 hper1 htot0 htot1 hpsic hpsi
    hbound hX hthX hY hthY hp' hq'

/-- **The matching estimate between the marked selected inverse and the marked
model front.**  Every hypothesis of `MatchingPathDist.pathDist_le_of_matching`
is kept, and the rear side of the configuration is given its geometric form: the
rear arclength is `x_H = ∫ cos δ`, the steering pulse is `Y = sin δ`, and `sf`
inverts the rear arclength.  Then the rear track written in its own arclength —
the marked selected inverse of the front — and the model front are at path
pseudodistance modulo a rigid motion at most the explicit interpolation cost of
the `L¹` matching bound. -/
theorem pathDistRigid_rearOwn_front_le_of_matching
    {Y y xH x Kstar Kstar' Kbar KP yu yu' : ℝ → ℝ}
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
    -- the two curvatures as curvatures of marked ovals of half-perimeter `P`
    {kH' KP' : ℝ → ℝ} {theta0 kstar kd eps0 : ℝ}
    (hkHc : Continuous kH) (hKPc : Continuous KP)
    (hkH'c : Continuous kH') (hKP'c : Continuous KP')
    (hperp : Periodic kH P) (hperq : Periodic KP P)
    (htot0 : (∫ r in (0:ℝ)..P, kH r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..P, KP r) = Real.pi)
    (hkd : 0 < kd) (hkstar : 0 ≤ kstar)
    (hd0 : ∀ r, HasDerivAt kH (kH' r) r) (hd1 : ∀ r, HasDerivAt KP (KP' r) r)
    (hkd0 : ∀ r, |kH' r| ≤ kd) (hkd1 : ∀ r, |KP' r| ≤ kd)
    (hk0nn : ∀ r, 0 ≤ kH r) (hk1nn : ∀ r, 0 ≤ KP r)
    (hk0le : ∀ r, kH r ≤ kstar) (hk1le : ∀ r, KP r ≤ kstar)
    (heps0 : (pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
        + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
      * Real.exp (-(beta * H)) ≤ eps0)
    -- the rear side of the configuration, in its geometric form
    {c : ℝ} (hc : 0 < c) (hdc : Continuous dl) (hcos : ∀ s, c ≤ Real.cos (dl s))
    (hsfinv : ∀ z, rearArclength dl (sf z) = z)
    (hFd : ∀ s, HasDerivAt F (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s)
    (hxHdef : ∀ t, xH t = rearArclength dl t) (hYsin : ∀ t, Y t = Real.sin (dl t)) :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * P) ∧
      ∀ p' q' : Data,
        (∀ u, p'.1 u = rearTrack F Θ dl (sf (2 * P * u))) →
        (∀ u, q'.1 u = interpCurve KP theta0 P (psi u)) →
        pathDistRigid p' q' ≤ interpCostL1 kstar kd P eps0
          ((pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
              + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
            * Real.exp (-(beta * H))) := by
  -- the curvature relation of the matching theorem, in its geometric form
  have hcosnn : ∀ t, 0 ≤ Real.cos (dl t) := fun t => le_trans hc.le (hcos t)
  have hsq : ∀ t, Real.sqrt (1 - (Y t) ^ 2) = Real.cos (dl t) := by
    intro t
    rw [hYsin t, ← Real.cos_sq' (dl t), Real.sqrt_sq (hcosnn t)]
  have hkrel : ∀ t, kH (rearArclength dl t) * Real.cos (dl t) = Real.sin (dl t) := by
    intro t
    have h := hk t
    rwa [hsq t, hxHdef t, hYsin t] at h
  obtain ⟨psi, hpsic, hpsi, hmain⟩ :=
    pathDistRigid_le_of_matching (theta0 := theta0) (kstar := kstar) (kd := kd) (eps0 := eps0)
      ha hy0 hyb hH hq2 hYdef ha0 ha1 hY hy hYa hya hxH hx h0 hid hK hKderiv hKd' hKcont
      hbeta0 hbeta hk hkcont hKbar hD hi0 hi2 hPeriod hPpos hKint hK0 hKbd hp hqe hpB hqB
      hhalf hyu hyu' hyu0 hyub hDU hyu'b hau0 hau1 hYau hKstaru hKPu hPH hkHc hKPc hkH'c
      hKP'c hperp hperq htot0 htot1 hkd hkstar hd0 hd1 hkd0 hkd1 hk0nn hk1nn hk0le hk1le
      heps0
  refine ⟨psi, hpsic, hpsi, fun p' q' hp' hq' => ?_⟩
  obtain ⟨hXc, hthX⟩ := rearOwn_carrier (kH := kH) hc hdc hcos hsfinv hFd hΘ hode hkrel
  obtain ⟨hYc, hthY⟩ := interpCurve_carrier (θ₀ := theta0) (L := P) hKPc
  exact hmain p' q' (fun z => rearTrack F Θ dl (sf z)) (interpCurve KP theta0 P)
    (fun z => rearAngle Θ dl (sf z)) (tangentAngle KP theta0) hXc hthX hYc hthY hp' hq'

end SelectedInverseCarrier
