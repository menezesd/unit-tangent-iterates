import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfFrameBundle
import UnitTangentIterates.RearOwnFrameDrift

/-!
# The variable-speed normal path of a family, from its tangential component

`GaugeMarkedDataOfFrameBundle.exists_variableSpeed_normalPath_of_frameBundle`
produces the marking of the comparison path from a bundle of frame data.  For a
family carried in its own arclength that bundle is itself produced by the
tangential component `ξ` of the motion alone
(`RearOwnFrameDrift.exists_gaugeFrameData_unitSpeed_of_bounds`): the speed is
`1`, so the rate of the gauge flow is `−ξ` and the two bounds the bundle asks
for are bounds on the two arclength derivatives of `ξ`.

This file removes the bundle from the interface.  What is asked of the
tangential component is exactly what the tangential estimates of a path of rears
provide (`RearOwnTangential.lean`, `RearOwnTangentialCost.lean`,
`RearOwnTangentialCostC2.lean`): joint `C³` regularity, and two densities
dominating `∂ₓξ` and `∂²ₓξ` which are themselves dominated by `κ̂` and `κ₂` times
the cost density.  The global bounds the bundle needs are then produced, since a
density dominated by a multiple of the cost density vanishes outside the time
window and is therefore bounded (`GaugeFlowDerivCost.exists_bound_of_stop`).

The marking produced is the flow of `−ξ`, and the two constants of the
comparison are again `costP1 ℓ κ̂ M` and `costG1 ℓ κ̂ κ₂ M`.

Main result: `exists_variableSpeed_normalPath_of_tangential`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfTangential

open GaugeFlowDerivCost GaugeFlowVariableSpeedPath GaugeMarkedDataOfFrameBundle
  NormalPathC2IncrementVariableSpeed RearOwnFrameDrift UniformFrameBounds

variable {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS g gS alphaT kT kX xi : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 Dd m : ℝ → ℝ} {ell T : ℝ} {P0 khat kappa2 c d r kx : ℝ}

/-! ### The frame data of a unit-speed bundle -/

/-- In a bundle of unit-speed frame data whose tangential component is `ξ`, the
first space derivative of the tangential rate is `−∂ₓξ`. -/
theorem gaugeRate1_eq {D : GaugeFrameData} (hv1 : ∀ a x, D.v a x = 1)
    (hxiD : ∀ a x, D.xi a x = xi a x) (hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi)) (a x : ℝ) :
    GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1 a x = -partialX xi a x := by
  have hfun : D.xi a = xi a := funext fun y => hxiD a y
  have h1 : D.xi1 a x = partialX xi a x := by
    have hd : HasDerivAt (D.xi a) (D.xi1 a x) x := D.hxi a x
    rw [hfun] at hd
    exact hd.unique (hasDerivAt_partialX hxi1 a x)
  have hv : D.v1 a x = 0 := by
    have hd : HasDerivAt (D.v a) (D.v1 a x) x := D.hv a x
    have hfunv : D.v a = fun _ => (1 : ℝ) := funext fun y => hv1 a y
    rw [hfunv] at hd
    exact hd.unique (hasDerivAt_const x (1 : ℝ))
  rw [GaugeRate.gaugeRate1, h1, hv1 a x, hv]
  ring

/-- In a bundle of unit-speed frame data whose tangential component is `ξ`, the
second space derivative of the tangential rate is `−∂²ₓξ`. -/
theorem gaugeRate2_eq {D : GaugeFrameData} (hv1 : ∀ a x, D.v a x = 1)
    (hxiD : ∀ a x, D.xi a x = xi a x) (hxi2 : ContDiff ℝ (2 : ℕ) (uncurry xi)) (a x : ℝ) :
    GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2 a x
      = -partialX (partialX xi) a x := by
  have hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi) :=
    hxi2.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
  have hpx1 : ContDiff ℝ (1 : ℕ) (uncurry (partialX xi)) := by
    have : ContDiff ℝ ((1 : ℕ) + 1) (uncurry xi) := by exact_mod_cast hxi2
    exact contDiff_partialX this
  have hfun : D.xi a = xi a := funext fun y => hxiD a y
  have h1 : ∀ y, D.xi1 a y = partialX xi a y := by
    intro y
    have hd : HasDerivAt (D.xi a) (D.xi1 a y) y := D.hxi a y
    rw [hfun] at hd
    exact hd.unique (hasDerivAt_partialX hxi1 a y)
  have h2 : D.xi2 a x = partialX (partialX xi) a x := by
    have hd : HasDerivAt (D.xi1 a) (D.xi2 a x) x := D.hxi1 a x
    have hfun1 : D.xi1 a = partialX xi a := funext fun y => h1 y
    rw [hfun1] at hd
    exact hd.unique (hasDerivAt_partialX hpx1 a x)
  have hv : D.v1 a x = 0 := by
    have hd : HasDerivAt (D.v a) (D.v1 a x) x := D.hv a x
    have hfunv : D.v a = fun _ => (1 : ℝ) := funext fun y => hv1 a y
    rw [hfunv] at hd
    exact hd.unique (hasDerivAt_const x (1 : ℝ))
  have hv2 : D.v2 a x = 0 := by
    have hd : HasDerivAt (D.v1 a) (D.v2 a x) x := D.hv1 a x
    have hfunv : D.v1 a = fun _ => (0 : ℝ) := by
      funext y
      have hdy : HasDerivAt (D.v a) (D.v1 a y) y := D.hv a y
      have hfunv : D.v a = fun _ => (1 : ℝ) := funext fun z => hv1 a z
      rw [hfunv] at hdy
      exact hdy.unique (hasDerivAt_const y (1 : ℝ))
    rw [hfunv] at hd
    exact hd.unique (hasDerivAt_const x (0 : ℝ))
  rw [GaugeRate.gaugeRate2, h2, hv1 a x, hv, hv2]
  ring

/-! ### The path -/

/-- **The comparison path of the `C²` estimate, produced from the tangential
component of the motion.**

The family `Y` is written in its own arclength, with tangent angle `α` and
curvature `k`, and moves with tangential component `ξ` and normal rate `η`
solving the inverse Jacobi ODE `∂_sη = g − η`.  Nothing about the marking is
assumed: it is produced as the flow of `−ξ`, started at the affine marking of
period `ℓ`, and the constants of the estimate are the explicit functions
`costP1 ℓ κ̂ M`, `costG1 ℓ κ̂ κ₂ M` of the total cost `M = ∫₀^T m`. -/
theorem exists_variableSpeed_normalPath_of_tangential
    (hxi3 : ContDiff ℝ (3 : ℕ) (uncurry xi)) (hell : 0 < ell)
    -- the family, in its own arclength, and its motion
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hk : ∀ t x, |k t x| ≤ khat) (hkappa2 : 0 ≤ kappa2)
    -- the two densities dominating the arclength derivatives of the tangential
    -- component
    (hC : ∀ t x, |partialX xi t x| ≤ C t)
    (hC2 : ∀ t x, |partialX (partialX xi) t x| ≤ C2 t)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    -- the frame data of the slices
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |xi t x| ≤ Rb t)
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => (xi t x : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the inverse Jacobi ODE and the bounds it carries
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    (hgbd : ∀ t x, |g t x| ≤ S0 t) (henbd : ∀ t x, |en t x| ≤ S0 t)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t)
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = ell * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 ell khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 ell khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 ell khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 ell khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ := by
  -- the densities vanish outside the time window, hence are bounded
  have hCnn : ∀ t, 0 ≤ C t := fun t => (abs_nonneg _).trans (hC t 0)
  have hC2nn : ∀ t, 0 ≤ C2 t := fun t => (abs_nonneg _).trans (hC2 t 0)
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
  obtain ⟨D, hDv, hDxi, -, -⟩ := exists_gaugeFrameData_unitSpeed_of_bounds (rL := B)
    (rB := B2) hxi3 (fun a x => (hC a x).trans (hB a)) (fun a x => (hC2 a x).trans (hB2 a))
  have hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi) :=
    hxi3.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3))
  have hxi2 : ContDiff ℝ (2 : ℕ) (uncurry xi) :=
    hxi3.of_le (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3))
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
  obtain ⟨Phi, hPhi0, hPhid, hmain⟩ :=
    exists_variableSpeed_normalPath_of_frameBundle (Y := Y) (alpha := alpha) (k := k)
      (en := en) (enS := enS) (enSS := enSS) (g := g) (gS := gS) (alphaT := alphaT)
      (kT := kT) (kX := kX) (C := C) (C2 := C2) (Kx := Kx) (Rb := Rb) (S0 := S0)
      (Dd := Dd) (m := m) (ell := ell) (T := T) (P0 := P0) (khat := khat)
      (kappa2 := kappa2) (c := c) (d := d) (r := r) (kx := kx)
      D hDv hell hYC1 hY hYt' halpha hk hkappa2
      (fun t x => by rw [hrate1 t x, abs_neg]; exact hC t x)
      (fun t x => by rw [hrate2 t x, abs_neg]; exact hC2 t x)
      hCc hC2c hCm hC2m halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc hKxbd
      (fun t x => by rw [hDxi t x]; exact hRbd t x) hKxnn henS henSS halphaTS hmixed'
      hgSd hjacobi hgbd henbd hgSbd hS0m hDm hRbm hKxm hr hm0 hnumA hnumK hT hencont
      hmc hmstop
  refine ⟨Phi, hPhi0, fun u t => ?_, hmain⟩
  have := hPhid u t
  rwa [hrate t (Phi t u)] at this

/-- **The comparison path, with the two tangential estimates given as multiples
of the cost density.**  This is the shape in which the estimates of a path of
rears come: `|∂ₓξ(t,·)| ≤ κ₁·m t` and `|∂²ₓξ(t,·)| ≤ κ₂·m t`, with `κ₁` the
growth coefficient `κ̂/(1−κ̂²)` of the gauge field and `κ₂` its second-order
counterpart.  The curvature bound `κ̂` of the slices is asked to dominate `κ₁`,
as the variable-speed estimate uses one constant for both. -/
theorem exists_variableSpeed_normalPath_of_tangential_const {kappa1 : ℝ}
    (hxi3 : ContDiff ℝ (3 : ℕ) (uncurry xi)) (hell : 0 < ell)
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      ((xi t s : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hk : ∀ t x, |k t x| ≤ khat) (hkappa2 : 0 ≤ kappa2) (hkappa1 : kappa1 ≤ khat)
    (hC : ∀ t x, |partialX xi t x| ≤ kappa1 * m t)
    (hC2 : ∀ t x, |partialX (partialX xi) t x| ≤ kappa2 * m t)
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |xi t x| ≤ Rb t)
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
    (hgbd : ∀ t x, |g t x| ≤ S0 t) (henbd : ∀ t x, |en t x| ≤ S0 t)
    (hgSbd : ∀ t x, |gS t x| ≤ Dd t)
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, Dd t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = ell * u) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u) (-xi t (Phi t u)) t) ∧
      ∀ a b : Data, (∀ u, Y 0 (Phi 0 u) = a.1 u) → (∀ u, Y T (Phi T u) = b.1 u) →
        (∀ t u, |en t (Phi t u)| ≤ m t) →
        (∀ t, ∀ j ≤ 2,
          MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) →
        ∃ Γ : NormalPath a b, Γ.T = T ∧ Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
          IsVariableSpeedNormalPath P0 (costP1 ell khat (∫ t in (0 : ℝ)..T, m t)) khat
            (costG1 ell khat kappa2 (∫ t in (0 : ℝ)..T, m t))
            (khat * costG1 ell khat kappa2 (∫ t in (0 : ℝ)..T, m t)
              + kappa2 * costP1 ell khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ :=
  exists_variableSpeed_normalPath_of_tangential (C := fun t => kappa1 * m t)
    (C2 := fun t => kappa2 * m t) hxi3 hell hYC1 hY hYt halpha hk hkappa2 hC hC2
    (continuous_const.mul hmc) (continuous_const.mul hmc)
    (fun t => mul_le_mul_of_nonneg_right hkappa1 (hm0 t)) (fun _ => le_rfl)
    halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc hkc hKxbd hRbd hKxnn henS henSS
    halphaTS hmixed hgSd hjacobi hgbd henbd hgSbd hS0m hDm hRbm hKxm hr hm0 hnumA hnumK
    hT hencont hmc hmstop

end GaugeMarkedDataOfTangential
