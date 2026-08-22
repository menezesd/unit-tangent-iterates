import Mathlib
import UnitTangentIterates.GaugeMarkedDataOfJacobi
import UnitTangentIterates.GaugeFlowDerivCost

/-!
# The variable-speed normal path of a family of rears, with the gauge constants
produced by the cost

`GaugeMarkedDataOfJacobi.exists_variableSpeed_normalPath_of_jacobi` still asks
the caller for four data about the *marking*: the two uniform bounds

`∂_uΦ ≤ P₁`, `|∂²_uΦ| ≤ G₁`

for the flow derivatives, a global Lipschitz constant `K` for the field of the
flow, a global bound `K₂` for its second space derivative, and the two numerical
comparisons `C·P₁ ≤ κ̂P₁·m` and `C·G₁ + C₂·P₁² ≤ C_g·m` with the cost density.

None of these is extra information.  Along a normal path the field of the gauge
flow obeys `|∂ₓh(t,·)| ≤ C t` and `|∂²ₓh(t,·)| ≤ C₂ t` with `C ≤ κ̂·m` and
`C₂ ≤ κ₂·m` (`RearOwnTangentialCost.lean`, `RearOwnTangentialCostC2.lean`), and
the cost density `m` of a normal path vanishes outside the time window.  Hence

* `C` and `C₂` vanish outside the window, so they are globally bounded
  (`GaugeFlowDerivCost.exists_bound_of_stop`), which gives `K` and `K₂`;
* the primitives of `∂ₓh` and of `∂²ₓh` along a flow line cannot grow outside
  the window, so `flowDeriv ≤ costP1 ℓ κ̂ M` and
  `|flowDeriv2| ≤ costG1 ℓ κ̂ κ₂ M` with `M = ∫₀^T m` the total cost
  (`GaugeFlowDerivCost.flowDeriv_le_costP1`,
  `GaugeFlowDerivCost.abs_flowDeriv2_le_costG1`);
* the two numerical comparisons hold with
  `C_g = κ̂·costG1 ℓ κ̂ κ₂ M + κ₂·(costP1 ℓ κ̂ M)²`.

So the whole block reduces to the two density bounds, and the constants of the
resulting variable-speed path are explicit functions of the tube data, of the
initial period `ℓ` and of the cost of the path.

Main result: `exists_variableSpeed_normalPath_of_jacobi_cost`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeMarkedDataOfJacobiCost

open GaugeFlowVariableSpeedPath GaugeFlowDerivCost GaugeMarkedDataOfJacobi
  NormalPathC2IncrementVariableSpeed

variable {a b : Data} {Y : ℝ → ℝ → ℂ}
  {alpha k en enS enSS g gS h hx hxx Phi alphaT kT kX : ℝ → ℝ → ℝ}
  {C C2 Kx Rb S0 D m : ℝ → ℝ} {ell T : ℝ}
  {P0 khat kappa2 c d r kx : ℝ}

/-- **The normal path with slices of variable speed produced by a family of
rears, with every constant of the marking produced by the cost.**

Beyond the geometry of the family — the inverse Jacobi ODE `∂_sη = g − η` and
the bounds it carries — the only hypotheses on the field `h` of the gauge flow
are that its first two space derivatives are dominated by `κ̂` and by `κ₂` times
the cost density of the path.  The Lipschitz constant of the field, the bound on
its second space derivative and the two uniform bounds on the flow derivatives
are all produced, the last two being the explicit constants
`costP1 ℓ κ̂ M` and `costG1 ℓ κ̂ κ₂ M` of the total cost `M = ∫₀^T m`. -/
theorem exists_variableSpeed_normalPath_of_jacobi_cost
    (hYC1 : ContDiff ℝ 1 (uncurry Y))
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (hYt : ∀ t s, HasDerivAt (fun r => Y r s)
      (((-h t s : ℝ) : ℂ) * Complex.exp (Complex.I * (alpha t s : ℂ))
        + (en t s : ℂ) * (Complex.I * Complex.exp (Complex.I * (alpha t s : ℂ)))) t)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    (hcont : Continuous (uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x) (hxcont : Continuous (uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x) (hxxcont : Continuous (uncurry hxx))
    (hk : ∀ t x, |k t x| ≤ khat) (hkappa2 : 0 ≤ kappa2)
    -- the two densities dominating the space derivatives of the field
    (hC : ∀ t x, |hx t x| ≤ C t) (hC2 : ∀ t x, |hxx t x| ≤ C2 t)
    (hCc : Continuous C) (hC2c : Continuous C2)
    (hCm : ∀ t, C t ≤ khat * m t) (hC2m : ∀ t, C2 t ≤ kappa2 * m t)
    -- the frame data of the slices
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
      IsVariableSpeedNormalPath P0 (costP1 ell khat (∫ t in (0 : ℝ)..T, m t)) khat
        (costG1 ell khat kappa2 (∫ t in (0 : ℝ)..T, m t))
        (khat * costG1 ell khat kappa2 (∫ t in (0 : ℝ)..T, m t)
          + kappa2 * costP1 ell khat (∫ t in (0 : ℝ)..T, m t) ^ 2) Γ := by
  set M : ℝ := ∫ t in (0 : ℝ)..T, m t with hMdef
  set P1 : ℝ := costP1 ell khat M with hP1def
  set G1 : ℝ := costG1 ell khat kappa2 M with hG1def
  -- the densities are nonnegative and vanish outside the time window
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
  -- the global bounds for the field and its second space derivative
  obtain ⟨B, hBnn, hB⟩ := exists_bound_of_stop hCc hCnn hCstop hT
  obtain ⟨B2, hB2nn, hB2⟩ := exists_bound_of_stop hC2c hC2nn hC2stop hT
  have hlip : ∀ t, LipschitzWith (Real.toNNReal B) (h t) :=
    lipschitzWith_of_deriv_bound hBnn hxd (fun s x => (hC s x).trans (hB s))
  have hxxK : ∀ s x, |hxx s x| ≤ ((Real.toNNReal B2 : NNReal) : ℝ) := by
    intro s x
    rw [Real.coe_toNNReal _ hB2nn]
    exact (hC2 s x).trans (hB2 s)
  -- the two flow derivatives
  have hP1 : ∀ t u, FlowDerivative.flowDeriv hx Phi ell t u ≤ P1 := fun t u =>
    flowDeriv_le_costP1 hPhid hxcont hell hC hCc hCstop hmc hCm hT t u
  have hG1 : ∀ t u, |GaugeFlowTimeDerivative.flowDeriv2 hx hxx Phi ell t u| ≤ G1 :=
    fun t u => abs_flowDeriv2_le_costG1 hPhid hxcont hxxcont hell hC hCc hCstop hC2 hC2c
      hC2stop hmc hCm hC2m hT t u
  -- the two numerical comparisons
  have hMnn : 0 ≤ M := intervalIntegral.integral_nonneg hT.le fun s _ => hm0 s
  have hP1nn : 0 ≤ P1 := (costP1_pos hell).le
  have hG1nn : 0 ≤ G1 := by
    have : 0 ≤ kappa2 * M := mul_nonneg hkappa2 hMnn
    exact mul_nonneg (by positivity) this
  have hcost : ∀ t, C t * P1 ≤ khat * P1 * m t := by
    intro t
    calc C t * P1 ≤ (khat * m t) * P1 := mul_le_mul_of_nonneg_right (hCm t) hP1nn
      _ = khat * P1 * m t := by ring
  have hcost2 : ∀ t, C t * G1 + C2 t * P1 ^ 2
      ≤ (khat * G1 + kappa2 * P1 ^ 2) * m t := by
    intro t
    have h1 : C t * G1 ≤ khat * m t * G1 := mul_le_mul_of_nonneg_right (hCm t) hG1nn
    have h2 : C2 t * P1 ^ 2 ≤ kappa2 * m t * P1 ^ 2 :=
      mul_le_mul_of_nonneg_right (hC2m t) (by positivity)
    nlinarith [h1, h2]
  exact exists_variableSpeed_normalPath_of_jacobi (K := Real.toNNReal B)
    (K2 := Real.toNNReal B2) (C := C) (C2 := C2) (Cg := khat * G1 + kappa2 * P1 ^ 2)
    hYC1 hY hYt halpha hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxK hP1 hG1
    hk hC hC2 hCnn hC2nn hcost hcost2 halphaC1 hkC1 halphaT hkT hkX halphaTc hkTc hkXc
    hkc hKxbd hRbd hKxnn henS henSS halphaTS hmixed hgSd hjacobi hgbd henbd hgSbd hS0m
    hDm hRbm hKxm hr hm0 hnumA hnumK hT hencont hstart hfinish hmc hmstop hmbd hmsup

end GaugeMarkedDataOfJacobiCost
