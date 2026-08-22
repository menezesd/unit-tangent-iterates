import Mathlib
import UnitTangentIterates.MatchingPathDist
import UnitTangentIterates.MarkedRigid
import UnitTangentIterates.CurvatureRigidity

/-!
# The matching estimate for arbitrary carriers of the two curvatures

`MatchingPathDist.pathDist_le_of_matching` bounds the marked path
pseudodistance of the two curves of a matching configuration, but only for the
**particular** curves reconstructed from the two curvatures by the explicit
formula of the lemma *Curvature interpolation*,
`CurvatureInterpolation.interpCurve`.  A curvature determines its curve only up
to a rigid motion of the plane, so the curves the paper actually compares — the
rear of a two-cap pair and the model front — are those reconstructions only
after a rotation and a translation, which the lemma *Compatible markings*
supplies.

This file removes that restriction, using

* `CurvatureRigidity.exists_rigid_interpCurve_reparam`: a unit-speed curve with
  curvature `κ` is a rigid image of the reconstruction, in any parameter, and
* `MarkedRigid.pathDistRigid`: the path pseudodistance taken modulo a rigid
  motion, for which two rigid images of curves at pseudodistance `d` are again
  at pseudodistance at most `d`.

Results:

* `pathDistRigid_le_of_carriers` — the transfer itself: a bound valid for the
  two reconstructions holds, modulo a rigid motion, for **any** two marked
  curves carrying the two curvatures in the same two parameters;
* `pathDistRigid_le_of_matching` — consequently the matching configuration
  bounds the pseudodistance modulo a rigid motion of arbitrary marked carriers
  of its two curvatures by `interpCostL1 κ_* k' P ε₀ (Ce^{−βH})`.

This does *not* close the remaining gap of the project: the curves of the
matching configuration still have to be identified with the `n`-th model and
the marked selected inverse of the `(n+1)`-st.  What it removes is the demand
that they be identified with one particular normalization of those curves: only
their curvatures, and the parameters in which they are marked, now matter.
-/

noncomputable section

open Real MeasureTheory Set Function MarkedSpace PathMetric

namespace MatchingPathDistRigid

open CurvatureInterpolation CurvatureRigidity MarkedRigid FrontPeriodization
  MatchingExponential MatchingComplete InterpolationPathDist
  InterpolationPathDistSummable MatchingPathDist

/-- The reconstruction from a curvature, read in the normalized parameter, is a
closed curve of period one. -/
theorem periodic_interpCurve_normalized {kappa : ℝ → ℝ} {θ₀ L : ℝ} (hk : Continuous kappa)
    (hper : Periodic kappa L) (htot : (∫ r in (0:ℝ)..L, kappa r) = Real.pi) :
    Periodic (fun u => interpCurve kappa θ₀ L (2 * L * u)) 1 := by
  intro u
  have h := interpCurve_periodic (θ₀ := θ₀) hk hper htot (2 * L * u)
  simpa [mul_add, add_comm, add_left_comm, add_assoc] using h

/-- The reconstruction from a curvature, read in a parameter advancing by one
period, is a closed curve of period one. -/
theorem periodic_interpCurve_psi {kappa : ℝ → ℝ} {θ₀ L : ℝ} {psi : ℝ → ℝ}
    (hk : Continuous kappa) (hper : Periodic kappa L)
    (htot : (∫ r in (0:ℝ)..L, kappa r) = Real.pi)
    (hpsi : ∀ u, psi (u + 1) = psi u + 2 * L) :
    Periodic (fun u => interpCurve kappa θ₀ L (psi u)) 1 := by
  intro u
  have h := interpCurve_periodic (θ₀ := θ₀) hk hper htot (psi u)
  simp only [hpsi u]
  exact h

theorem continuous_interpCurve {kappa : ℝ → ℝ} {θ₀ L : ℝ} (hk : Continuous kappa) :
    Continuous (interpCurve kappa θ₀ L) :=
  continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_interpCurve (θ₀ := θ₀) (L := L) hk s).continuousAt

/-- **Transfer of a path-distance bound to arbitrary carriers of the two
curvatures.**  Suppose a bound `d` holds for the path pseudodistance of the two
marked curves reconstructed from the curvatures `k₀`, `k₁` — in the normalized
parameter `2Lu` for the first and in the parameter `psi` for the second.  Then
any two marked curves whose curves are unit-speed curves of the same two
curvatures, read in the same two parameters, are at pseudodistance at most `d`
**modulo a rigid motion of the plane**. -/
theorem pathDistRigid_le_of_carriers {k0 k1 : ℝ → ℝ} {θ₀ L d : ℝ} {psi : ℝ → ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ r in (0:ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0:ℝ)..L, k1 r) = Real.pi)
    (hpsic : Continuous psi) (hpsi : ∀ u, psi (u + 1) = psi u + 2 * L)
    (hbound : ∀ p q : Data, (∀ u, p.1 u = interpCurve k0 θ₀ L (2 * L * u)) →
      (∀ u, q.1 u = interpCurve k1 θ₀ L (psi u)) → pathDist p q ≤ d)
    {p' q' : Data} {X Y : ℝ → ℂ} {thX thY : ℝ → ℝ}
    (hX : ∀ s, HasDerivAt X (tau (thX s)) s) (hthX : ∀ s, HasDerivAt thX (k0 s) s)
    (hY : ∀ s, HasDerivAt Y (tau (thY s)) s) (hthY : ∀ s, HasDerivAt thY (k1 s) s)
    (hp : ∀ u, p'.1 u = X (2 * L * u)) (hq : ∀ u, q'.1 u = Y (psi u)) :
    pathDistRigid p' q' ≤ d := by
  -- the two reconstructions, as marked curves
  obtain ⟨p, hpdef⟩ :=
    exists_data_of_periodic_curve (g := fun u => interpCurve k0 θ₀ L (2 * L * u))
      ((continuous_interpCurve (θ₀ := θ₀) (L := L) hk0).comp (by fun_prop))
      (periodic_interpCurve_normalized (θ₀ := θ₀) hk0 hper0 htot0)
  obtain ⟨q, hqdef⟩ :=
    exists_data_of_periodic_curve (g := fun u => interpCurve k1 θ₀ L (psi u))
      ((continuous_interpCurve (θ₀ := θ₀) (L := L) hk1).comp hpsic)
      (periodic_interpCurve_psi (θ₀ := θ₀) hk1 hper1 htot1 hpsi)
  -- the two carriers are rigid images of them
  obtain ⟨a₁, w₁, hw₁, hrig1⟩ :=
    exists_rigid_interpCurve_reparam (X := X) (theta := thX) (kappa := k0)
      (phi := fun u => 2 * L * u) (Z := fun u => p'.1 u) θ₀ L hk0 hX hthX hp
  obtain ⟨a₂, w₂, hw₂, hrig2⟩ :=
    exists_rigid_interpCurve_reparam (X := Y) (theta := thY) (kappa := k1)
      (phi := psi) (Z := fun u => q'.1 u) θ₀ L hk1 hY hthY hq
  have hp' : ∀ u, p'.1 u = a₁ + w₁ * p.1 u := by
    intro u
    rw [hpdef u]
    exact hrig1 u
  have hq' : ∀ u, q'.1 u = a₂ + w₂ * q.1 u := by
    intro u
    rw [hqdef u]
    exact hrig2 u
  exact le_trans (pathDistRigid_le_of_rigid_images hw₁ hw₂ hp' hq') (hbound p q hpdef hqdef)

/-- **The matching estimate for arbitrary carriers of the two curvatures.**
Every hypothesis of `MatchingPathDist.pathDist_le_of_matching` is kept; its
conclusion is now stated for arbitrary marked curves carrying the two
curvatures — the rear curvature `k_H` of the two-cap pair in the normalized
parameter and the periodized model curvature `K_P` in the common phase — the
comparison being taken modulo a rigid motion of the plane, as the lemma
*Compatible markings* allows. -/
theorem pathDistRigid_le_of_matching
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
      * Real.exp (-(beta * H)) ≤ eps0) :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * P) ∧
      ∀ (p' q' : Data) (Xc Yc : ℝ → ℂ) (thX thY : ℝ → ℝ),
        (∀ s, HasDerivAt Xc (tau (thX s)) s) → (∀ s, HasDerivAt thX (kH s) s) →
        (∀ s, HasDerivAt Yc (tau (thY s)) s) → (∀ s, HasDerivAt thY (KP s) s) →
        (∀ u, p'.1 u = Xc (2 * P * u)) → (∀ u, q'.1 u = Yc (psi u)) →
        pathDistRigid p' q' ≤ interpCostL1 kstar kd P eps0
          ((pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
              + rearTailConst CK alpha B + frontConst au CU DU alpha beta B)
            * Real.exp (-(beta * H))) := by
  obtain ⟨psi, hpsic, hpsi, hbound⟩ :=
    pathDist_le_of_matching (theta0 := theta0) (kstar := kstar) (kd := kd) (eps0 := eps0)
      ha hy0 hyb hH hq2 hYdef ha0 ha1 hY hy hYa hya hxH hx h0 hid hK hKderiv hKd' hKcont
      hbeta0 hbeta hk hkcont hKbar hD hi0 hi2 hPeriod hPpos hKint hK0 hKbd hp hqe hpB hqB
      hhalf hyu hyu' hyu0 hyub hDU hyu'b hau0 hau1 hYau hKstaru hKPu hPH hkHc hKPc hkH'c
      hKP'c hperp hperq htot0 htot1 hkd hkstar hd0 hd1 hkd0 hkd1 hk0nn hk1nn hk0le hk1le
      heps0
  refine ⟨psi, hpsic, hpsi, ?_⟩
  intro p' q' Xc Yc thX thY hXc hthX hYc hthY hp' hq'
  exact pathDistRigid_le_of_carriers (θ₀ := theta0) hkHc hKPc hperp hperq htot0 htot1
    hpsic hpsi hbound hXc hthX hYc hthY hp' hq'

end MatchingPathDistRigid
