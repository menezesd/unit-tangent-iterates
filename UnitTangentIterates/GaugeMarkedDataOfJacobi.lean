import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfNormalRate
import UnitTangentIterates.JacobiNormalRateBounds

/-!
# The variable-speed normal path of a family of rears, from the Jacobi ODE

`GaugeMarkedDataOfNormalRate.exists_variableSpeed_normalPath_of_normal_rate`
produces the path `Γ'` of the `C²` comparison from bounds `S₀, S₁, S₂` on the
normal rate of the moving family and on its first two arclength derivatives.
For a family of *rears* those three bounds are not independent: the normal rate
solves the inverse Jacobi ODE `∂_sη = g − η`, and
`JacobiNormalRateBounds.jacobi_normal_rate_bounds` reduces them to the single
bound `S₀` shared by `η` and by the inhomogeneity `g` — the bound the maximum
principle provides — together with a bound `D` on `∂_sg`.

This file composes the two, so that the path is produced from the Jacobi ODE
directly, the numerical conditions being read with the constants `c₀ = c`,
`c₁ = 2c`, `c₂ = d + 2c` of `JacobiNormalRateBounds.jacobi_cost_constants`.

Main result: `exists_variableSpeed_normalPath_of_jacobi`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfJacobi

open GaugeFlowVariableSpeedPath GaugeMarkedDataOfNormalRate JacobiNormalRateBounds
  NormalPathC2IncrementVariableSpeed

variable {a b : Data} {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS g gS h hx hxx Phi alphaT kT kX : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 D m : ℝ → ℝ} {K K2 : NNReal} {ell T : ℝ}
  {P0 P1 khat G1 Cg c d r kx : ℝ}

/-- **The normal path with slices of variable speed produced by a family of
rears.**  The bounds on the normal rate and on its two arclength derivatives are
no longer assumed separately: they come from the inverse Jacobi ODE
`∂_sη = g − η`, from the sup bound `S₀` shared by `η` and `g`, and from a bound
`D` on `∂_sg`. -/
theorem exists_variableSpeed_normalPath_of_jacobi
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-h t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : Continuous (uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hxxK : ∀ s x, |hxx s x| ≤ (K2 : ℝ))
    (hP1 : ∀ t u, FlowDerivative.flowDeriv hx Phi ell t u ≤ P1)
    (hG1 : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2 hx hxx Phi ell t u| ≤ G1)
    (hk : ∀ t x, |k t x| ≤ khat)
    (hC : ∀ t x, |hx t x| ≤ C t) (hC2 : ∀ t x, |hxx t x| ≤ C2 t)
    (hCnn : ∀ t, 0 ≤ C t) (hC2nn : ∀ t, 0 ≤ C2 t)
    (hcost : ∀ t, C t * P1 ≤ khat * P1 * m t)
    (hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2 ≤ Cg * m t)
    (halphaC1 : ContDiff ℝ 1 (uncurry alpha)) (hkC1 : ContDiff ℝ 1 (uncurry k))
    (halphaT : ∀ t x, HasDerivAt (fun r => alpha r x) (alphaT t x) t)
    (hkT : ∀ t x, HasDerivAt (fun r => k r x) (kT t x) t)
    (hkX : ∀ t x, HasDerivAt (k t) (kX t x) x)
    (halphaTc : Continuous (uncurry alphaT)) (hkTc : Continuous (uncurry kT))
    (hkXc : Continuous (uncurry kX)) (hkc : Continuous (uncurry k))
    (hKxbd : ∀ t x, |kX t x| ≤ Kx t) (hRbd : ∀ t x, |h t x| ≤ Rb t)
    (hKxnn : ∀ t, 0 ≤ Kx t)
    (henS : ∀ t x, HasDerivAt (en t) (enS t x) x)
    (henSS : ∀ t x, HasDerivAt (enS t) (enSS t x) x)
    (halphaTS : ∀ t s, HasDerivAt (alphaT t) (kT t s) s)
    (hmixed : ∀ t s, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (alpha r s : ℂ))) W t ∧
      HasDerivAt (fun x => ((-h t x : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t x : ℂ))
        + (en t x : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t x : ℂ)))) W s)
    -- the inverse Jacobi ODE and the bounds it carries
    (hgSd : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hjacobi : ∀ t x, HasDerivAt (en t) (g t x - en t x) x)
    (hgbd : ∀ t x, |g t x| ≤ S0 t) (henbd : ∀ t x, |en t x| ≤ S0 t)
    (hgSbd : ∀ t x, |gS t x| ≤ D t)
    (hS0m : ∀ t, S0 t ≤ c * m t) (hDm : ∀ t, D t ≤ d * m t)
    (hRbm : ∀ t, Rb t ≤ r * m t) (hKxm : ∀ t, Kx t ≤ kx) (hr : 0 ≤ r) (hm0 : ∀ t, 0 ≤ m t)
    (hnumA : 2 * c + 2 * khat * r ≤ 1 / P0)
    (hnumK : (d + 2 * c) + khat ^ 2 * c + 2 * r * kx ≤ 1 / P0 ^ 2 + khat ^ 2)
    (hT : 0 < T) (hencont : Continuous (uncurry en))
    (hstart : ∀ u, Y 0 (Phi 0 u) = a.1 u) (hfinish : ∀ u, Y T (Phi T u) = b.1 u)
    (hmc : Continuous m) (hmstop : ∀ t ∉ Ioo (0 : ℝ) T, m t = 0)
    (hmbd : ∀ t u, |en t (Phi t u)| ≤ m t)
    (hmsup : ∀ t, ∀ j ≤ 2,
      MarkedTopology.supNorm (iteratedDeriv j (fun u => en t (Phi t u))) ≤ m t) :
    ∃ Γ : NormalPath a b, Γ.T = T ∧ Γ.m = m ∧ cost Γ = (∫ t in (0 : ℝ)..T, m t) ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ := by
  obtain ⟨hb0, hb1, hb2⟩ :=
    jacobi_normal_rate_bounds hgSd hjacobi henS henSS hgbd henbd hgSbd
  obtain ⟨hm0', hm1, hm2⟩ := jacobi_cost_constants (S0 := S0) (D := D) (m := m) hS0m hDm
  exact exists_variableSpeed_normalPath_of_normal_rate
    (S0 := S0) (S1 := fun t => 2 * S0 t) (S2 := fun t => D t + 2 * S0 t)
    (c0 := c) (c1 := 2 * c) (c2 := d + 2 * c)
    hYC1 hY hYt halpha hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxK hP1 hG1
    hk hC hC2 hCnn hC2nn hcost hcost2 halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc
    hkc hKxbd hRbd hKxnn henS henSS halphaTS hmixed hb0 hb1 hb2 hm0' hm1 hm2 hRbm hKxm
    hr hm0 hnumA hnumK hT hencont hstart hfinish hmc hmstop hmbd hmsup

end GaugeMarkedDataOfJacobi
