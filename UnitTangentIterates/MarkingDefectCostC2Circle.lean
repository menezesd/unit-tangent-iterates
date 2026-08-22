import Mathlib
import UnitTangentIterates.MarkingDefectCostC2
import UnitTangentIterates.PathMetricCircle
import UnitTangentIterates.SelectedInverseTubeCircle

/-!
# Non-vacuity of the `C²` marking defect along a normal path

`MarkingDefectCostC2.dist_le_of_gauge_flow_cost` bounds, in the metric of the
space of marked curves, the defect of a gauge marking produced by a flow whose
field is bounded by the cost density of a normal path.  This file checks that
its hypothesis block is satisfiable, with a nonzero field and a normal path of
nonzero cost.

The path is the radial dilation of `PathMetricCircle.lean` from the circle of
radius `1` to the circle of radius `2`, whose cost density is the bump `w` and
whose cost is `1`.  The gauge field is the *linear* field

```
  R(t, x) = λ w(t) · x ,
```

which vanishes at the base point and grows linearly, exactly as the tangential
rate of a family of closed curves does; its flow is
`Φ(t, u) = L₀ u e^{λ B(t)}`, `B` the primitive of `w`.  Started at the affine
marking of period `L₀ = L e^{−λ}` it reaches, at the final time, the affine
marking of period `L` — so the curve it reads is the circle of perimeter `L`
itself, and the general bound applies with the position defect
`2Lλ`, the `C¹` defect `flowDefectC1Int L₀ λ` and the `C²` defect
`flowDefectC2Int L₀ λ 0`.

Main result: `gauge_flow_cost_circle`.
-/

noncomputable section

open Set Function

namespace MarkingDefectCostC2Circle

open MarkedSpace PathMetric PathMetric.NormalPath PathMetricCircle
  MarkingDeviationC2 MarkingFlowDefectC2 MarkingDefectCostC2
  SelectedInverseCircle SelectedInverseTubeCircle

/-! ### The linear gauge field along the dilation -/

/-- The linear gauge field of rate `λ` along the time profile of the dilation. -/
def linField (lam : ℝ) : ℝ → ℝ → ℝ := fun t x => lam * w t * x

/-- Its flow, started at the affine marking of period `ell`. -/
def linFlow (lam ell : ℝ) : ℝ → ℝ → ℝ := fun t u => ell * u * Real.exp (lam * B t)

theorem w_le : ∀ t, w t ≤ 3 / 2 := by
  intro t
  rw [w]
  refine max_le (by norm_num) ?_
  nlinarith [sq_nonneg (t - 1 / 2)]

/-- **The hypothesis block of the `C²` marking defect along a normal path is
satisfiable.**  For the dilation from the circle of radius `1` to the circle of
radius `2`, the linear gauge field `λ w(t)·x` and the circle of radius `ρ` read
in its flow, the field is a genuine gauge field for that path — it drives the
stated flow and is bounded by `λ` times the cost density of the path — the flow
reaches at the final time the affine marking of the perimeter of the circle, and
the general bound of `MarkingDefectCostC2.dist_le_of_gauge_flow_cost` holds.

The curve read at the final marking is the circle itself, so the left-hand side
of the last conjunct is `0`: the content of the statement is that the hypothesis
block of the general theorem is satisfiable with a nonzero field along a path of
nonzero cost, which is what the first three conjuncts record. -/
theorem gauge_flow_cost_circle {rho lam : ℝ} (hrho : 0 < rho) (hlam : 0 ≤ lam) :
    (∀ u t, HasDerivAt
        (fun s => linFlow lam ((2 * Real.pi * rho) * Real.exp (-lam)) s u)
        (linField lam t (linFlow lam ((2 * Real.pi * rho) * Real.exp (-lam)) t u)) t)
      ∧ (∀ t x, |linField lam t x| ≤ lam * (dilation 1 2).m t * |x|)
      ∧ linFlow lam ((2 * Real.pi * rho) * Real.exp (-lam)) (dilation 1 2).T 1
          = 2 * Real.pi * rho
      ∧ dist (circleData rho) (circleData rho)
      ≤ markingC2Bound (2 * (2 * Real.pi * rho) * lam * cost (dilation 1 2))
          (flowDefectC1Int ((2 * Real.pi * rho) * Real.exp (-lam))
            (lam * cost (dilation 1 2)))
          (flowDefectC2Int ((2 * Real.pi * rho) * Real.exp (-lam))
            (lam * cost (dilation 1 2)) (0 * cost (dilation 1 2)))
          (2 * Real.pi * rho) (1 / rho) 0 := by
  set L : ℝ := 2 * Real.pi * rho with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  set L0 : ℝ := L * Real.exp (-lam) with hL0def
  have hL0pos : 0 < L0 := by rw [hL0def]; positivity
  set b : Data := circleData rho with hb
  have hbmem : IsTubeMember (2 * Real.pi * rho) (1 / rho) (4 * rho) b :=
    circleData_mem_tube hrho
  have hperim : perim b = L := perim_circleData hrho
  have hev : ∀ s, HasDerivAt (ev b)
      (Complex.exp (Complex.I * ((circleAngle rho s : ℝ) : ℂ))) s := by
    intro s
    rw [hb, ev_circleData hrho]
    exact hasDerivAt_circleFront hrho s
  -- the flow of the linear field
  have hflowT : linFlow lam L0 1 1 = L := by
    rw [linFlow, B_one, mul_one, hL0def]
    rw [mul_one, mul_assoc, ← Real.exp_add]
    simp
  have hd : ∀ u t, HasDerivAt (fun s => linFlow lam L0 s u)
      (linField lam t (linFlow lam L0 t u)) t := by
    intro u t
    have hB : HasDerivAt (fun s => lam * B s) (lam * w t) t :=
      (hasDerivAt_B t).const_mul lam
    have h := (hB.exp).const_mul (L0 * u)
    refine h.congr_deriv ?_
    rw [linField, linFlow]
    ring
  have hflowT' : linFlow lam L0 (dilation 1 2).T 1 = L := hflowT
  have hgrow' : ∀ t x, |linField lam t x| ≤ lam * (dilation 1 2).m t * |x| := by
    intro t x
    have hm : (dilation 1 2).m t = |(2 : ℝ) - 1| * w t := rfl
    rw [linField, abs_mul, abs_of_nonneg (mul_nonneg hlam (w_nonneg t)), hm]
    norm_num
  have hlip : ∀ t, LipschitzWith (Real.toNNReal (lam * (3 / 2))) (linField lam t) := by
    intro t
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hwt : |lam * w t| ≤ lam * (3 / 2) := by
      rw [abs_of_nonneg (mul_nonneg hlam (w_nonneg t))]
      exact mul_le_mul_of_nonneg_left (w_le t) hlam
    have hnn : (0 : ℝ) ≤ lam * (3 / 2) := by positivity
    rw [Real.coe_toNNReal _ hnn, Real.dist_eq, Real.dist_eq, linField, linField, ← mul_sub,
      abs_mul]
    exact mul_le_mul_of_nonneg_right hwt (abs_nonneg _)
  -- the bound
  have hmain := MarkingDefectCostC2.dist_le_of_gauge_flow_cost
    (Γ := dilation 1 2) (b := b) (q' := b)
    (R := linField lam) (Rx := fun t _ => lam * w t) (Rxx := fun _ _ => 0)
    (C := fun t => lam * w t) (C2 := fun _ => 0) (Phi := linFlow lam L0)
    (Klip := Real.toNNReal (lam * (3 / 2))) (K2 := 0) (L0 := L0) (Lmax := L)
    (kappa := lam) (kappa2 := 0) (L := L) (kb := 1 / rho) (kL := 0)
    (Θ := circleAngle rho) (k := fun _ => 1 / rho)
    hlip
    (by
      have : Continuous fun p : ℝ × ℝ => lam * w p.1 * p.2 := by
        exact ((continuous_const.mul (continuous_w.comp continuous_fst)).mul continuous_snd)
      exact this)
    hd
    (fun u => by
      have : Continuous fun t : ℝ => lam * w t * linFlow lam L0 t u := by
        unfold linFlow
        exact (continuous_const.mul continuous_w).mul
          ((continuous_const.mul continuous_const).mul
            (Real.continuous_exp.comp (continuous_const.mul continuous_B)))
      exact this)
    (fun s x => by
      simpa using (hasDerivAt_id x).const_mul (lam * w s))
    (by
      show Continuous fun p : ℝ × ℝ => lam * w p.1
      exact continuous_const.mul (continuous_w.comp continuous_fst))
    (fun s x => hasDerivAt_const x (lam * w s))
    (by
      show Continuous fun _ : ℝ × ℝ => (0 : ℝ)
      exact continuous_const)
    (fun s x => by norm_num)
    (continuous_const.mul continuous_w)
    (fun t x => by rw [linField, abs_mul, abs_of_nonneg (mul_nonneg hlam (w_nonneg t))])
    (fun t => mul_nonneg hlam (w_nonneg t))
    (fun s x => by rw [abs_of_nonneg (mul_nonneg hlam (w_nonneg s))])
    continuous_const (fun s x => by norm_num)
    (fun t => by
      show lam * w t ≤ lam * (dilation 1 2).m t
      have hm : (dilation 1 2).m t = |(2 : ℝ) - 1| * w t := rfl
      rw [hm]
      norm_num)
    (fun t => by
      show (0 : ℝ) ≤ 0 * (dilation 1 2).m t
      norm_num)
    (fun u => by rw [linFlow, B_zero, mul_zero, Real.exp_zero, mul_one])
    hL0pos
    (fun t => by rw [linFlow, mul_zero, zero_mul])
    (fun t u => by rw [linFlow, linFlow, linFlow]; ring)
    (fun t => by
      show L0 * 1 * Real.exp (lam * B t) ≤ L
      have h1 : Real.exp (lam * B t) ≤ Real.exp lam :=
        Real.exp_le_exp.2 (by nlinarith [B_le_one t, B_nonneg t])
      have h2 : L0 * Real.exp lam = L := by
        rw [hL0def, mul_assoc, ← Real.exp_add]
        simp
      calc L0 * 1 * Real.exp (lam * B t) = L0 * Real.exp (lam * B t) := by ring
        _ ≤ L0 * Real.exp lam := mul_le_mul_of_nonneg_left h1 hL0pos.le
        _ = L := h2)
    (by
      show linFlow lam L0 (dilation 1 2).T 1 = L
      show linFlow lam L0 1 1 = L
      exact hflowT)
    (by positivity) hbmem hperim hev (fun s => hasDerivAt_circleAngle s)
    (fun _ => by rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / rho)])
    (fun s t => by simp)
    (fun u => by
      show b.1 u = ev b (linFlow lam L0 (dilation 1 2).T u)
      have hval : linFlow lam L0 (dilation 1 2).T u = L * u := by
        show linFlow lam L0 1 u = L * u
        rw [linFlow, B_one, mul_one, hL0def]
        have hx : Real.exp (-lam) * Real.exp lam = 1 := by
          rw [← Real.exp_add]; simp
        calc L * Real.exp (-lam) * u * Real.exp lam
            = L * u * (Real.exp (-lam) * Real.exp lam) := by ring
          _ = L * u := by rw [hx, mul_one]
      rw [hval, ev, hperim]
      congr 1
      field_simp)
    (fun u => hbmem.hasDerivAt_curve u) (fun u => hbmem.hasDerivAt_vel u)
  exact ⟨hd, hgrow', hflowT', hmain⟩

end MarkingDefectCostC2Circle
