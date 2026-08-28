import Mathlib
import UnitTangentIterates.GaugeFrameBundleFundamental
import UnitTangentIterates.GaugeMarkedDataOfTangential

/-!
# The comparison path from the tangential component, with the bounds on one period

`GaugeMarkedDataOfTangential.exists_variableSpeed_normalPath_of_tangential`
removes the bundle of frame data from the interface of the assembly: the
marking is the flow of `−ξ`, and everything the bundle asked for is asked of the
tangential component `ξ` of the motion alone.  Its bounds are global in the
arclength.

This file is its fundamental-domain form.  For a family of closed curves whose
arclength period `Q t` moves, the tangential component drifts,
`ξ(t, x + Q t) = ξ(t, x) − Q'(t)`, so it is bounded globally only when the
period stands still.  Its *arclength derivatives* carry no drift, however: they
are honestly `Q t`-periodic, so a bound on one period is a bound everywhere
(`GaugeFlowFundamentalDomain.bound_of_periodic`), and the bundle of frame data
can still be produced.  Every bound is therefore asked on `[0, Q t]` only, and
nothing is assumed about the motion of the period.

Main results: `exists_variableSpeed_normalPath_of_tangential_fundamental` and
its form `exists_variableSpeed_normalPath_of_tangential_const_fundamental` with
the two tangential estimates given as multiples of the cost density.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeTangentialFundamental

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugeMarkedDataOfTangential
  NormalPathC2IncrementVariableSpeed RearOwnFrameDrift UniformFrameBounds
  GaugeFlowFundamentalDomain GaugeFrameBundleFundamental

variable {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS g gS alphaT kT kX xi : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 Dd m Q Q' : ℝ → ℝ} {turn T : ℝ} {P0 khat kappa2 c d r kx : ℝ}

/-! ### The periodicity of the arclength derivatives of the tangential component -/

/-- The first arclength derivative of a quasi-periodic tangential component is
periodic. -/
theorem periodic_partialX_xi (hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi))
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t) (t : ℝ) :
    Function.Periodic (partialX xi t) (Q t) :=
  periodic_deriv_of_quasiPeriodic (Q' := fun s => -Q' s)
    (fun a x => hasDerivAt_partialX hxi1 a x)
    (fun a x => by rw [hxiqp a x]; ring) t

/-- The second arclength derivative of a quasi-periodic tangential component is
periodic. -/
theorem periodic_partialX_partialX_xi (hxi2 : ContDiff ℝ (2 : ℕ) (uncurry xi))
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t) (t : ℝ) :
    Function.Periodic (partialX (partialX xi) t) (Q t) := by
  have hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi) :=
    hxi2.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
  have hpx1 : ContDiff ℝ (1 : ℕ) (uncurry (partialX xi)) := by
    have : ContDiff ℝ ((1 : ℕ) + 1) (uncurry xi) := by exact_mod_cast hxi2
    exact contDiff_partialX this
  exact periodic_deriv_of_periodic (fun a x => hasDerivAt_partialX hpx1 a x)
    (fun a => periodic_partialX_xi hxi1 hxiqp a) t

/-- The first spatial jet of a quasi-periodic field is periodic; no time
derivative is needed. -/
theorem periodic_spatialC2_xi1 (S : SpatialC2 xi)
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t) (t : ℝ) :
    Function.Periodic (S.xi1 t) (Q t) :=
  periodic_deriv_of_quasiPeriodic (Q' := fun s => -Q' s)
    S.deriv1 (fun a x => by rw [hxiqp a x]; ring) t

/-- The second spatial jet of a quasi-periodic field is periodic. -/
theorem periodic_spatialC2_xi2 (S : SpatialC2 xi)
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t) (t : ℝ) :
    Function.Periodic (S.xi2 t) (Q t) :=
  periodic_deriv_of_periodic S.deriv2
    (fun a => periodic_spatialC2_xi1 S hxiqp a) t

/-! ### The path -/

/-- **The comparison path of the `C²` estimate, produced from the tangential
component of the motion, with every bound asked on one period only.**

The family `Y` is written in its own arclength, with tangent angle `α` and
curvature `k`, and moves with tangential component `ξ` and normal rate `η`
solving the inverse Jacobi ODE `∂_sη = g − η`.  The family closes up: the
curvature is `Q t`-periodic, the tangent angle increases by the constant `turn`
over one period, the tangential component drifts by `−Q'(t)` and vanishes at the
base point.  Nothing is assumed about the motion of the period `Q`, and every
pointwise bound is asked only for `x ∈ [0, Q t]`.

The marking produced is the flow of `−ξ`; it fixes the base point and carries
the unit parameter interval onto one period. -/
theorem exists_variableSpeed_normalPath_of_tangential_fundamental_with_eta_c2flow
    (Sxi : SpatialC2 xi)
    -- the family, in its own arclength, and its motion
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hkappa2 : 0 ≤ kappa2)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    -- the frame data of the slices
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the inverse Jacobi ODE
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    -- the closing structure of the family
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn)
    (hxi0 : ∀ t, xi t 0 = 0)
    -- the bounds, on one period only
    (hk : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |k t x| ≤ khat)
    (hC : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |Sxi.xi1 t x| ≤ C t)
    (hC2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |Sxi.xi2 t x| ≤ C2 t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |xi t x| ≤ Rb t)
    (hgbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |g t x| ≤ S0 t)
    (henbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |en t x| ≤ S0 t)
    (hgSbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |gS t x| ≤ Dd t)
    -- the comparisons with the cost density and the numerical conditions
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t) ∧
      (∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
          (∀ t u, Γ.eta t u = en t (Phi t u)) ∧
          (∀ t u, Phi t (u + 1) = Phi t u + Q t) ∧
          (∃ phi1 phi2 : ℝ → ℝ → ℝ,
            (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
            (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
            (∀ t, Continuous (phi1 t)) ∧ (∀ t, Continuous (phi2 t)) ∧
            (∀ t u, phi1 t u ≤ costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) ∧
            (∀ t u, |phi2 t u| ≤
              costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t))) ∧
          Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ) ∧
      (∃ D : GaugeFrameData, (∀ t x, D.v t x = 1) ∧ (∀ t x, D.xi t x = xi t x)) := by
  -- the two arclength derivatives of the tangential component are periodic, so
  -- the bounds on one period are bounds everywhere
  have hCall : ∀ t x, |Sxi.xi1 t x| ≤ C t := fun t =>
    bound_of_periodic (hQpos t) (periodic_spatialC2_xi1 Sxi hxiqp t) (hC t)
  have hC2all : ∀ t x, |Sxi.xi2 t x| ≤ C2 t := fun t =>
    bound_of_periodic (hQpos t) (periodic_spatialC2_xi2 Sxi hxiqp t) (hC2 t)
  -- the densities vanish outside the time window, hence are bounded
  have hCnn : ∀ t, 0 ≤ C t := fun t => (abs_nonneg _).trans (hCall t 0)
  have hC2nn : ∀ t, 0 ≤ C2 t := fun t => (abs_nonneg _).trans (hC2all t 0)
  have hCstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0 := by
    intro s hs
    have := (hCm s).trans_eq (by rw [hmstop s hs, mul_zero])
    exact le_antisymm this (hCnn s)
  have hC2stop : ∀ s ∉ Ioo (0 : ℝ) T, C2 s = 0 := by
    intro s hs
    have := (hC2m s).trans_eq (by rw [hmstop s hs, mul_zero])
    exact le_antisymm this (hC2nn s)
  obtain ⟨B, hBnn, hB⟩ := exists_bound_of_stop hCc hCnn hCstop hT
  obtain ⟨B2, hB2nn, hB2⟩ := exists_bound_of_stop hC2c hC2nn hC2stop hT
  -- the bundle of frame data of the family
  obtain ⟨D, hDv, hDxi, hDxi1, hDxi2, hDv1, hDv2, -, -⟩ :=
    exists_gaugeFrameData_unitSpeed_of_spatialC2_bounds (rL := B)
    (rB := B2) Sxi (fun a x => (hCall a x).trans (hB a))
    (fun a x => (hC2all a x).trans (hB2 a))
  have hrate1 : ∀ a x, GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 a x = -Sxi.xi1 a x := by
    intro a x
    simp [GaugeRate.gaugeRate1, hDv, hDxi, hDxi1, hDv1]
  have hrate2 : ∀ a x, GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 a x
      = -Sxi.xi2 a x := by
    intro a x
    simp [GaugeRate.gaugeRate2, hDv, hDxi, hDxi1, hDxi2, hDv1, hDv2]
  have hrate : ∀ a x, GaugeRate.gaugeRate D.xi D.v a x = -xi a x := by
    intro a x
    rw [GaugeRate.gaugeRate, hDv a x, hDxi a x, div_one]
  -- the motion, written with the tangential component of the bundle
  have hYt' : ∀ t s, HasDerivAt (fun r => Y r s)
      ((D.xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t := by
    intro t s
    rw [hDxi t s]
    exact hYt t s
  have hmixed' : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s := by
    intro t s
    obtain ⟨W, hW1, hW2⟩ := hmixed t s
    refine ⟨W, hW1, ?_⟩
    have hfun : (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))))
        = fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
          + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))) := by
      funext x
      rw [hDxi t x]
    rw [hfun]
    exact hW2
  obtain ⟨Phi, hPhi0, hbase, hPhid, hmain⟩ :=
    exists_variableSpeed_normalPath_of_frameBundle_fundamental_with_eta_c2flow (Y := Y) (alpha := alpha)
      (k := k) (en := en) (enS := enS) (enSS := enSS) (g := g) (gS := gS)
      (alphaT := alphaT) (kT := kT) (kX := kX) (C := C) (C2 := C2) (Kx := Kx) (Rb := Rb)
      (S0 := S0) (Dd := Dd) (m := m) (Q := Q) (Q' := Q') (turn := turn) (T := T)
      (P0 := P0) (khat := khat) (kappa2 := kappa2) (c := c) (d := d) (r := r) (kx := kx)
      D hDv hYC1 hY hYt' halpha hkappa2 hCc hC2c hCm hC2m halphaC1 hkC1 halphaT hkT hkX
      halphaTc hkTc hkXc hkc hKxnn henS henSS halphaTS hmixed' hgSd hjacobi hQpos hQd
      (fun t x => by rw [hDxi t (x + Q t), hDxi t x]; exact hxiqp t x)
      hkper halphaper (fun t => by rw [hDxi t 0]; exact hxi0 t) hk
      (fun t x hx => by rw [hrate1 t x, abs_neg]; exact hC t x hx)
      (fun t x hx => by rw [hrate2 t x, abs_neg]; exact hC2 t x hx)
      hKxbd (fun t x hx => by rw [hDxi t x]; exact hRbd t x hx) hgbd henbd hgSbd
      hS0m hDm hRbm hKxm hr hm0 hnumA hnumK hT hencont hmc hmstop
  refine ⟨Phi, hPhi0, hbase, fun u t => ?_, ?_, ⟨D, hDv, hDxi⟩⟩
  · have := hPhid u t
    rwa [hrate t (Phi t u)] at this
  · intro a b hstart hfinish hmbd hmsup
    obtain ⟨Gamma, hGammaT, hGammaX, hGammaEta, htrans, hphi1, hphi2, hphi1c, hphi2c,
      hphi1bd, hphi2bd, hGammam, hGammacost, hGammavar⟩ :=
      hmain a b hstart hfinish hmbd hmsup
    exact ⟨Gamma, hGammaT, hGammaX, hGammaEta, htrans,
      ⟨_, _, hphi1, hphi2, hphi1c, hphi2c, hphi1bd, hphi2bd⟩,
      hGammam, hGammacost, hGammavar⟩



theorem exists_variableSpeed_normalPath_of_tangential_fundamental_with_eta
    (hxi3 : ContDiff ℝ (2 : ℕ) (uncurry xi))
    -- the family, in its own arclength, and its motion
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hkappa2 : 0 ≤ kappa2)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    -- the frame data of the slices
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the inverse Jacobi ODE
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    -- the closing structure of the family
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn)
    (hxi0 : ∀ t, xi t 0 = 0)
    -- the bounds, on one period only
    (hk : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |k t x| ≤ khat)
    (hC : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |partialX xi t x| ≤ C t)
    (hC2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |partialX (partialX xi) t x| ≤ C2 t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |xi t x| ≤ Rb t)
    (hgbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |g t x| ≤ S0 t)
    (henbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |en t x| ≤ S0 t)
    (hgSbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |gS t x| ≤ Dd t)
    -- the comparisons with the cost density and the numerical conditions
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
          (∀ t u, Γ.eta t u = en t (Phi t u)) ∧ Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ := by
  have hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi) :=
    hxi3.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
  have hxi2 : ContDiff ℝ (2 : ℕ) (uncurry xi) :=
    hxi3
  -- the two arclength derivatives of the tangential component are periodic, so
  -- the bounds on one period are bounds everywhere
  have hCall : ∀ t x, |partialX xi t x| ≤ C t := fun t =>
    bound_of_periodic (hQpos t) (periodic_partialX_xi hxi1 hxiqp t) (hC t)
  have hC2all : ∀ t x, |partialX (partialX xi) t x| ≤ C2 t := fun t =>
    bound_of_periodic (hQpos t) (periodic_partialX_partialX_xi hxi2 hxiqp t) (hC2 t)
  -- the densities vanish outside the time window, hence are bounded
  have hCnn : ∀ t, 0 ≤ C t := fun t => (abs_nonneg _).trans (hCall t 0)
  have hC2nn : ∀ t, 0 ≤ C2 t := fun t => (abs_nonneg _).trans (hC2all t 0)
  have hCstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0 := by
    intro s hs
    have := (hCm s).trans_eq (by rw [hmstop s hs, mul_zero])
    exact le_antisymm this (hCnn s)
  have hC2stop : ∀ s ∉ Ioo (0 : ℝ) T, C2 s = 0 := by
    intro s hs
    have := (hC2m s).trans_eq (by rw [hmstop s hs, mul_zero])
    exact le_antisymm this (hC2nn s)
  obtain ⟨B, hBnn, hB⟩ := exists_bound_of_stop hCc hCnn hCstop hT
  obtain ⟨B2, hB2nn, hB2⟩ := exists_bound_of_stop hC2c hC2nn hC2stop hT
  -- the bundle of frame data of the family
  obtain ⟨D, hDv, hDxi, -, -⟩ := exists_gaugeFrameData_unitSpeed_of_bounds_c2 (rL := B)
    (rB := B2) hxi3 (fun a x => (hCall a x).trans (hB a))
    (fun a x => (hC2all a x).trans (hB2 a))
  have hrate1 : ∀ a x, GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 a x = -partialX xi a x :=
    fun a x => gaugeRate1_eq hDv hDxi hxi1 a x
  have hrate2 : ∀ a x, GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 a x
      = -partialX (partialX xi) a x := fun a x => gaugeRate2_eq hDv hDxi hxi2 a x
  have hrate : ∀ a x, GaugeRate.gaugeRate D.xi D.v a x = -xi a x := by
    intro a x
    rw [GaugeRate.gaugeRate, hDv a x, hDxi a x, div_one]
  -- the motion, written with the tangential component of the bundle
  have hYt' : ∀ t s, HasDerivAt (fun r => Y r s)
      ((D.xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t := by
    intro t s
    rw [hDxi t s]
    exact hYt t s
  have hmixed' : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s := by
    intro t s
    obtain ⟨W, hW1, hW2⟩ := hmixed t s
    refine ⟨W, hW1, ?_⟩
    have hfun : (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))))
        = fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
          + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))) := by
      funext x
      rw [hDxi t x]
    rw [hfun]
    exact hW2
  obtain ⟨Phi, hPhi0, hbase, hPhid, hmain⟩ :=
    exists_variableSpeed_normalPath_of_frameBundle_fundamental_with_eta (Y := Y) (alpha := alpha)
      (k := k) (en := en) (enS := enS) (enSS := enSS) (g := g) (gS := gS)
      (alphaT := alphaT) (kT := kT) (kX := kX) (C := C) (C2 := C2) (Kx := Kx) (Rb := Rb)
      (S0 := S0) (Dd := Dd) (m := m) (Q := Q) (Q' := Q') (turn := turn) (T := T)
      (P0 := P0) (khat := khat) (kappa2 := kappa2) (c := c) (d := d) (r := r) (kx := kx)
      D hDv hYC1 hY hYt' halpha hkappa2 hCc hC2c hCm hC2m halphaC1 hkC1 halphaT hkT hkX
      halphaTc hkTc hkXc hkc hKxnn henS henSS halphaTS hmixed' hgSd hjacobi hQpos hQd
      (fun t x => by rw [hDxi t (x + Q t), hDxi t x]; exact hxiqp t x)
      hkper halphaper (fun t => by rw [hDxi t 0]; exact hxi0 t) hk
      (fun t x hx => by rw [hrate1 t x, abs_neg]; exact hC t x hx)
      (fun t x hx => by rw [hrate2 t x, abs_neg]; exact hC2 t x hx)
      hKxbd (fun t x hx => by rw [hDxi t x]; exact hRbd t x hx) hgbd henbd hgSbd
      hS0m hDm hRbm hKxm hr hm0 hnumA hnumK hT hencont hmc hmstop
  refine ⟨Phi, hPhi0, hbase, fun u t => ?_, hmain⟩
  have := hPhid u t
  rwa [hrate t (Phi t u)] at this


/-- Compatibility form retaining the historical result shape. -/
theorem exists_variableSpeed_normalPath_of_tangential_fundamental
    (hxi3 : ContDiff ℝ (2 : ℕ) (uncurry xi))
    -- the family, in its own arclength, and its motion
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hkappa2 : 0 ≤ kappa2)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    -- the frame data of the slices
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the inverse Jacobi ODE
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    -- the closing structure of the family
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn)
    (hxi0 : ∀ t, xi t 0 = 0)
    -- the bounds, on one period only
    (hk : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |k t x| ≤ khat)
    (hC : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |partialX xi t x| ≤ C t)
    (hC2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |partialX (partialX xi) t x| ≤ C2 t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |xi t x| ≤ Rb t)
    (hgbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |g t x| ≤ S0 t)
    (henbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |en t x| ≤ S0 t)
    (hgSbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |gS t x| ≤ Dd t)
    -- the comparisons with the cost density and the numerical conditions
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
          Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ := by
  have hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi) :=
    hxi3.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
  have hxi2 : ContDiff ℝ (2 : ℕ) (uncurry xi) :=
    hxi3
  -- the two arclength derivatives of the tangential component are periodic, so
  -- the bounds on one period are bounds everywhere
  have hCall : ∀ t x, |partialX xi t x| ≤ C t := fun t =>
    bound_of_periodic (hQpos t) (periodic_partialX_xi hxi1 hxiqp t) (hC t)
  have hC2all : ∀ t x, |partialX (partialX xi) t x| ≤ C2 t := fun t =>
    bound_of_periodic (hQpos t) (periodic_partialX_partialX_xi hxi2 hxiqp t) (hC2 t)
  -- the densities vanish outside the time window, hence are bounded
  have hCnn : ∀ t, 0 ≤ C t := fun t => (abs_nonneg _).trans (hCall t 0)
  have hC2nn : ∀ t, 0 ≤ C2 t := fun t => (abs_nonneg _).trans (hC2all t 0)
  have hCstop : ∀ s ∉ Ioo (0 : ℝ) T, C s = 0 := by
    intro s hs
    have := (hCm s).trans_eq (by rw [hmstop s hs, mul_zero])
    exact le_antisymm this (hCnn s)
  have hC2stop : ∀ s ∉ Ioo (0 : ℝ) T, C2 s = 0 := by
    intro s hs
    have := (hC2m s).trans_eq (by rw [hmstop s hs, mul_zero])
    exact le_antisymm this (hC2nn s)
  obtain ⟨B, hBnn, hB⟩ := exists_bound_of_stop hCc hCnn hCstop hT
  obtain ⟨B2, hB2nn, hB2⟩ := exists_bound_of_stop hC2c hC2nn hC2stop hT
  -- the bundle of frame data of the family
  obtain ⟨D, hDv, hDxi, -, -⟩ := exists_gaugeFrameData_unitSpeed_of_bounds_c2 (rL := B)
    (rB := B2) hxi3 (fun a x => (hCall a x).trans (hB a))
    (fun a x => (hC2all a x).trans (hB2 a))
  have hrate1 : ∀ a x, GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 a x = -partialX xi a x :=
    fun a x => gaugeRate1_eq hDv hDxi hxi1 a x
  have hrate2 : ∀ a x, GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 a x
      = -partialX (partialX xi) a x := fun a x => gaugeRate2_eq hDv hDxi hxi2 a x
  have hrate : ∀ a x, GaugeRate.gaugeRate D.xi D.v a x = -xi a x := by
    intro a x
    rw [GaugeRate.gaugeRate, hDv a x, hDxi a x, div_one]
  -- the motion, written with the tangential component of the bundle
  have hYt' : ∀ t s, HasDerivAt (fun r => Y r s)
      ((D.xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t := by
    intro t s
    rw [hDxi t s]
    exact hYt t s
  have hmixed' : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s := by
    intro t s
    obtain ⟨W, hW1, hW2⟩ := hmixed t s
    refine ⟨W, hW1, ?_⟩
    have hfun : (fun x => (D.xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))))
        = fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
          + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ))) := by
      funext x
      rw [hDxi t x]
    rw [hfun]
    exact hW2
  obtain ⟨Phi, hPhi0, hbase, hPhid, hmain⟩ :=
    exists_variableSpeed_normalPath_of_frameBundle_fundamental (Y := Y) (alpha := alpha)
      (k := k) (en := en) (enS := enS) (enSS := enSS) (g := g) (gS := gS)
      (alphaT := alphaT) (kT := kT) (kX := kX) (C := C) (C2 := C2) (Kx := Kx) (Rb := Rb)
      (S0 := S0) (Dd := Dd) (m := m) (Q := Q) (Q' := Q') (turn := turn) (T := T)
      (P0 := P0) (khat := khat) (kappa2 := kappa2) (c := c) (d := d) (r := r) (kx := kx)
      D hDv hYC1 hY hYt' halpha hkappa2 hCc hC2c hCm hC2m halphaC1 hkC1 halphaT hkT hkX
      halphaTc hkTc hkXc hkc hKxnn henS henSS halphaTS hmixed' hgSd hjacobi hQpos hQd
      (fun t x => by rw [hDxi t (x + Q t), hDxi t x]; exact hxiqp t x)
      hkper halphaper (fun t => by rw [hDxi t 0]; exact hxi0 t) hk
      (fun t x hx => by rw [hrate1 t x, abs_neg]; exact hC t x hx)
      (fun t x hx => by rw [hrate2 t x, abs_neg]; exact hC2 t x hx)
      hKxbd (fun t x hx => by rw [hDxi t x]; exact hRbd t x hx) hgbd henbd hgSbd
      hS0m hDm hRbm hKxm hr hm0 hnumA hnumK hT hencont hmc hmstop
  refine ⟨Phi, hPhi0, hbase, fun u t => ?_, hmain⟩
  have := hPhid u t
  rwa [hrate t (Phi t u)] at this

/-- **The comparison path from the tangential component on one period, with the
two tangential estimates given as multiples of the cost density.**  This is the
shape in which the estimates of a path of rears come: `|∂ₓξ(t,·)| ≤ κ₁·m t` and
`|∂²ₓξ(t,·)| ≤ κ₂·m t` on one period, with `κ₁` dominated by the curvature bound
`κ̂`. -/
theorem exists_variableSpeed_normalPath_of_tangential_const_fundamental {kappa1 : ℝ}
    (hxi3 : ContDiff ℝ (2 : ℕ) (uncurry xi))
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hkappa2 : 0 ≤ kappa2) (hkappa1 : kappa1 ≤ khat)
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    (hQpos : ∀ t, 0 < Q t) (hQd : ∀ t, HasDerivAt Q (Q' t) t)
    (hxiqp : ∀ t x, xi t (x + Q t) = xi t x - Q' t)
    (hkper : ∀ t, Function.Periodic (k t) (Q t))
    (halphaper : ∀ t x, alpha t (x + Q t) = alpha t x + turn)
    (hxi0 : ∀ t, xi t 0 = 0)
    (hk : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |k t x| ≤ khat)
    (hC : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |partialX xi t x| ≤ kappa1 * m t)
    (hC2 : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |partialX (partialX xi) t x| ≤ kappa2 * m t)
    (hKxbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |kX t x| ≤ Kx t)
    (hRbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |xi t x| ≤ Rb t)
    (hgbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |g t x| ≤ S0 t)
    (henbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |en t x| ≤ S0 t)
    (hgSbd : ∀ t, ∀ x ∈ Icc (0 : ℝ) (Q t), |gS t x| ≤ Dd t)
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Q 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ (∀ t u, Γ.X t u = Y t (Phi t u)) ∧
          Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 (Q 0) khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 (Q 0) khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ :=
  exists_variableSpeed_normalPath_of_tangential_fundamental (C := fun t => kappa1 * m t)
    (C2 := fun t => kappa2 * m t) hxi3 hYC1 hY hYt halpha hkappa2
    (continuous_const.mul hmc) (continuous_const.mul hmc)
    (fun t => mul_le_mul_of_nonneg_right hkappa1 (hm0 t)) (fun _ => le_rfl)
    halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc hKxnn henS henSS halphaTS
    hmixed hgSd hjacobi hQpos hQd hxiqp hkper halphaper hxi0 hk hC hC2 hKxbd hRbd hgbd
    henbd hgSbd hS0m hDm hRbm hKxm hr hm0 hnumA hnumK hT hencont hmc hmstop

end GaugeTangentialFundamental
