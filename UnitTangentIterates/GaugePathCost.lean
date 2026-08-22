import Mathlib
import UnitTangentIterates.GaugeFunctionals
import UnitTangentIterates.PathFunctionalsCost

/-!
# The path functionals of a path put in normal gauge

The last step of the comparison: the bounds that `GaugeRate.lean` and
`FlowDerivative.lean` give for the gauge flow of a frame, fed into the
path-level comparison of `PathFunctionalsCost.lean`.  Over the time interval
`[0,1]` of a normal path the distortion of the gauge flow is bounded by its
value at `|t| = 1`, so with

`C₁ = A₁/v₀ + A₀B₁/v₀²`,  `C₂ = A₂/v₀ + 2A₁B₁/v₀² + A₀(V₁B₂ + 2B₁²)/v₀³`,
`M = ℓe^{C₁}`,  `N = C₂ℓ²e^{2C₁}`,  `m = ℓe^{−C₁}`,

the functionals of the normal velocity read in the gauge parameter satisfy

`S₀ ≤ S₀`,  `S₁ ≤ M S₁`,  `S₂ ≤ M²S₂ + N S₁`,  `W ≤ m⁻¹∫₀¹∫|η_t|`.

Main result: `gauge_path_functionals_le`.
-/

noncomputable section

open Set MeasureTheory Function MarkedTopology FlowDerivative GaugeRate PathFunctionalsCost

namespace GaugePathCost

variable {xi xi1 xi2 v v1 v2 : ℝ → ℝ → ℝ} {A0 A1 A2 B1 B2 V1 v0 ell : ℝ}
  {eta eta1 eta2 : ℝ → ℝ → ℝ} {Phi : ℝ → ℝ → ℝ}

/-- **The path functionals of a path read in the normal gauge.**  All the
hypotheses on the flow are bounds on the frame data; the constants of the
comparison are explicit in them. -/
theorem gauge_path_functionals_le
    (hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x)
    (hxi1 : ∀ a x, HasDerivAt (xi1 a) (xi2 a x) x)
    (hv : ∀ a x, HasDerivAt (v a) (v1 a x) x)
    (hv1 : ∀ a x, HasDerivAt (v1 a) (v2 a x) x)
    (hvne : ∀ a x, v a x ≠ 0)
    (hxic : Continuous (uncurry xi)) (hxi1c : Continuous (uncurry xi1))
    (hxi2c : Continuous (uncurry xi2)) (hvc : Continuous (uncurry v))
    (hv1c : Continuous (uncurry v1)) (hv2c : Continuous (uncurry v2))
    (hv0 : 0 < v0) (hvlow : ∀ a x, v0 ≤ |v a x|) (hvup : ∀ a x, |v a x| ≤ V1)
    (hA0 : ∀ a x, |xi a x| ≤ A0) (hA1 : ∀ a x, |xi1 a x| ≤ A1)
    (hA2 : ∀ a x, |xi2 a x| ≤ A2)
    (hB1 : ∀ a x, |v1 a x| ≤ B1) (hB2 : ∀ a x, |v2 a x| ≤ B2)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u) (gaugeRate xi v t (Phi t u)) t)
    -- the normal velocity of the path
    (heta1 : ∀ t x, HasDerivAt (eta t) (eta1 t x) x)
    (heta2 : ∀ t x, HasDerivAt (eta1 t) (eta2 t x) x)
    (hetac : ∀ t ∈ Icc (0:ℝ) 1, Continuous (eta t))
    (hbdd : ∀ t ∈ Icc (0:ℝ) 1, BddAbove (Set.range fun x => |eta t x|))
    (hbdd1 : ∀ t ∈ Icc (0:ℝ) 1, BddAbove (Set.range fun x => |eta1 t x|))
    (hbdd2 : ∀ t ∈ Icc (0:ℝ) 1, BddAbove (Set.range fun x => |eta2 t x|))
    -- the integrability of the densities in the time
    (hi0 : IntervalIntegrable (fun t => supNorm fun u => eta t (Phi t u)) volume 0 1)
    (hi0' : IntervalIntegrable (fun t => supNorm (eta t)) volume 0 1)
    (hi1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 fun u => eta t (Phi t u))) volume 0 1)
    (hi1' : IntervalIntegrable (fun t => supNorm (eta1 t)) volume 0 1)
    (hi2 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 fun u => eta t (Phi t u))) volume 0 1)
    (hi2' : IntervalIntegrable (fun t => supNorm (eta2 t)) volume 0 1)
    {L : ℝ} (hL : 0 ≤ L)
    (hiW : IntervalIntegrable (fun t => ∫ u in (0:ℝ)..L, |eta t (Phi t u)|) volume 0 1)
    (hiW' : IntervalIntegrable
      (fun t => ∫ x in (Phi t 0)..(Phi t L), |eta t x|) volume 0 1) :
    S 0 (fun t u => eta t (Phi t u)) ≤ S 0 eta ∧
    S 1 (fun t u => eta t (Phi t u))
      ≤ (ell * Real.exp (A1 / v0 + A0 * B1 / v0 ^ 2)) * S 1 eta ∧
    S 2 (fun t u => eta t (Phi t u))
      ≤ (ell * Real.exp (A1 / v0 + A0 * B1 / v0 ^ 2)) ^ 2 * S 2 eta
        + ((A2 / v0 + 2 * (A1 * B1) / v0 ^ 2 + A0 * (V1 * B2 + 2 * B1 ^ 2) / v0 ^ 3)
            * ell ^ 2 * Real.exp (2 * (A1 / v0 + A0 * B1 / v0 ^ 2))) * S 1 eta ∧
    W (fun t u => eta t (Phi t u)) L
      ≤ (1 / (ell * Real.exp (-(A1 / v0 + A0 * B1 / v0 ^ 2))))
          * ∫ t in (0:ℝ)..1, ∫ x in (Phi t 0)..(Phi t L), |eta t x| := by
  obtain ⟨hlip, hcont, hxd, hxcont, hxxd, hxxcont, hxxbd⟩ :=
    gaugeRate_flow_hypotheses hxi hxi1 hv hv1 hvne hxic hxi1c hxi2c hvc hv1c hv2c
      hv0 hvlow hvup hA0 hA1 hA2 hB1 hB2
  set C1 : ℝ := A1 / v0 + A0 * B1 / v0 ^ 2 with hC1def
  set C2 : ℝ := A2 / v0 + 2 * (A1 * B1) / v0 ^ 2 + A0 * (V1 * B2 + 2 * B1 ^ 2) / v0 ^ 3
    with hC2def
  have hC1 : (0:ℝ) ≤ C1 :=
    le_trans (abs_nonneg _) (abs_gaugeRate1_le hv0 hvlow hA0 hA1 hB1 0 0)
  have hC2 : (0:ℝ) ≤ C2 := le_trans (abs_nonneg _) (hxxbd 0 0)
  have hcoe : ((Real.toNNReal C1 : NNReal) : ℝ) = C1 := Real.coe_toNNReal _ hC1
  have hxbd : ∀ s x, |gaugeRate1 xi xi1 v v1 s x| ≤ ((Real.toNNReal C1 : NNReal) : ℝ) := by
    intro s x
    rw [hcoe]
    exact abs_gaugeRate1_le hv0 hvlow hA0 hA1 hB1 s x
  -- the flow and its two derivatives in the parameter
  set D : ℝ → ℝ → ℝ := flowDeriv (gaugeRate1 xi xi1 v v1) Phi ell with hDdef
  set D2 : ℝ → ℝ → ℝ := fun t u => D t u
      * ∫ s in (0:ℝ)..t, gaugeRate2 xi xi1 xi2 v v1 v2 s (Phi s u) * D s u with hD2def
  have hphi1 : ∀ t u, HasDerivAt (Phi t) (D t u) u := fun t u =>
    hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u t
  have hphi2 : ∀ t u, HasDerivAt (D t) (D2 t u) u := fun t u =>
    hasDerivAt_flowDeriv hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd u t
  have hphi1c : ∀ t, Continuous (D t) := by
    intro t
    have hd : Differentiable ℝ (D t) := fun u => (hphi2 t u).differentiableAt
    exact hd.continuous
  -- the uniform bounds on the time interval of the path
  have habs_le_one : ∀ t ∈ Icc (0:ℝ) 1, |t| ≤ 1 := fun t ht => by
    rw [abs_of_nonneg ht.1]; exact ht.2
  have hM : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, |D t u| ≤ ell * Real.exp C1 := by
    intro t ht u
    rw [abs_of_pos (flowDeriv_pos hell t u)]
    refine le_trans ((flowDeriv_bounds (K := Real.toNNReal C1) hell hxbd t u).2) ?_
    rw [hcoe]
    have : C1 * |t| ≤ C1 := by nlinarith [habs_le_one t ht, abs_nonneg t]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) hell.le
  have hm : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, ell * Real.exp (-C1) ≤ D t u := by
    intro t ht u
    refine le_trans ?_ ((flowDeriv_bounds (K := Real.toNNReal C1) hell hxbd t u).1)
    rw [hcoe]
    have : -C1 ≤ -(C1 * |t|) := by nlinarith [habs_le_one t ht, abs_nonneg t]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) hell.le
  have hN : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, |D2 t u| ≤ C2 * ell ^ 2 * Real.exp (2 * C1) := by
    intro t ht u
    refine le_trans (abs_flowDeriv_deriv_le (K := Real.toNNReal C1) hell hxbd hxxbd u t) ?_
    rw [hcoe]
    have h1 : Real.exp (2 * C1 * |t|) ≤ Real.exp (2 * C1) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [habs_le_one t ht, abs_nonneg t]
    have h2 : C2 * ell ^ 2 * |t| ≤ C2 * ell ^ 2 := by
      nlinarith [habs_le_one t ht, abs_nonneg t, sq_nonneg ell,
        mul_nonneg hC2 (sq_nonneg ell)]
    calc C2 * ell ^ 2 * |t| * Real.exp (2 * C1 * |t|)
        ≤ C2 * ell ^ 2 * |t| * Real.exp (2 * C1) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ C2 * ell ^ 2 * Real.exp (2 * C1) := by
          exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  refine ⟨S_zero_comp_le hbdd hi0 hi0',
    S_one_comp_le heta1 hphi1 hbdd1 hM hi1 hi1',
    S_two_comp_le heta1 heta2 hphi1 hphi2 hbdd1 hbdd2 hM hN hi2 hi1' hi2',
    W_comp_le (mul_pos hell (Real.exp_pos _)) hL hetac hphi1 hphi1c hm hiW hiW'⟩

end GaugePathCost
