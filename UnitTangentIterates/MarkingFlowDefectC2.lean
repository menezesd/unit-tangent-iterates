import Mathlib
import UnitTangentIterates.FlowDerivative
import UnitTangentIterates.MarkingDeviationC2

/-!
# The `C²` defect of a gauge marking produced by a flow

`MarkingDeviationC2.dist_le_of_marking_defect_c2` bounds the marked distance
between a member `q` of the tube and the same curve read in a marking `φ`, in
terms of three defects: the deviation `ε₀` of `φ` from the affine marking
`u ↦ L·u`, the deviation `ε₁` of `φ'` from `L`, and a bound `ε₂` for `φ''`.
The `C⁰` defect `ε₀` is estimated along a normal path in `MarkingDefectCost.lean`;
this file estimates the other two, for the markings the gauge assembly produces
— the flow of a scalar field.

For a flow `Φ` of a globally Lipschitz field `h` started at the affine marking
`Φ(0,u) = ℓ·u`, `FlowDerivative.lean` computes the derivative in the initial
condition in closed form, `∂_uΦ(t,u) = ℓ exp ∫₀^t ∂ₓh`, and bounds its
derivative.  Since the period `L = Φ(T,1) − Φ(T,0)` is a mean value of
`∂_uΦ(T,·)` over one period, both it and `∂_uΦ(T,u)` lie in
`[ℓe^{−KT}, ℓe^{KT}]`, whence

```
  |∂_uΦ(T,u) − L| ≤ ℓ(e^{KT} − e^{−KT}) ,   |∂²_uΦ(T,u)| ≤ K₂ℓ²T e^{2KT} .
```

Feeding these into the `C²` comparison gives `dist_le_of_flow_marking`: the
curve read in the gauge marking of the terminal time is at marked distance at
most `markingC2Bound ε₀ (flowDefectC1 …) (flowDefectC2 …) L k_b k_L` from the
curve itself.  Both flow defects vanish when the field does (`K = K₂ = 0`), so
a marking flowed by a field that does not move is the affine one and the bound
is the `C⁰` defect alone.

Main results: `abs_flowDeriv_sub_period_le`, `abs_flowDeriv_deriv_le'`,
`dist_le_of_flow_marking`.
-/

noncomputable section

open Set Function

namespace MarkingFlowDefectC2

open MarkedSpace FlowDerivative MarkingDeviationC2

variable {h hx hxx : ℝ → ℝ → ℝ} {K : NNReal} {ell : ℝ} {Phi : ℝ → ℝ → ℝ}

/-! ### The two flow defects -/

/-- The `C¹` defect of a flow marking: the spread of `ℓe^{±KT}`. -/
def flowDefectC1 (ell K T : ℝ) : ℝ := ell * (Real.exp (K * T) - Real.exp (-(K * T)))

/-- The `C²` defect of a flow marking. -/
def flowDefectC2 (ell K K2 T : ℝ) : ℝ := K2 * ell ^ 2 * T * Real.exp (2 * K * T)

theorem flowDefectC1_nonneg {T : ℝ} (hell : 0 ≤ ell) (hK : 0 ≤ (K : ℝ)) (hT : 0 ≤ T) :
    0 ≤ flowDefectC1 ell K T := by
  have h : Real.exp (-((K : ℝ) * T)) ≤ Real.exp ((K : ℝ) * T) :=
    Real.exp_le_exp.2 (by nlinarith)
  have := mul_nonneg hell (sub_nonneg.2 h)
  simpa [flowDefectC1] using this

/-- **The derivative of a flow marking deviates from the period of the marking
by at most the spread of the Grönwall bounds.**  The period `L = Φ(T,1) −
Φ(T,0)` is a mean value of `∂_uΦ(T,·)`, and both lie in `[ℓe^{−KT}, ℓe^{KT}]`. -/
theorem abs_flowDeriv_sub_period_le (hell : 0 < ell) (hbd : ∀ s x, |hx s x| ≤ (K : ℝ))
    {T : ℝ} (hT : 0 ≤ T)
    (hphi : ∀ u, HasDerivAt (fun u' => Phi T u') (flowDeriv hx Phi ell T u) u) (u : ℝ) :
    |flowDeriv hx Phi ell T u - (Phi T 1 - Phi T 0)| ≤ flowDefectC1 ell K T := by
  have habsT : |T| = T := abs_of_nonneg hT
  -- the mean value: the period is a value of the derivative
  obtain ⟨c, -, hcs⟩ := exists_hasDerivAt_eq_slope (fun u' => Phi T u')
    (fun u' => flowDeriv hx Phi ell T u') (zero_lt_one)
    (fun x _ => ((hphi x).continuousAt).continuousWithinAt)
    (fun x _ => hphi x)
  have hper : flowDeriv hx Phi ell T c = Phi T 1 - Phi T 0 := by
    rw [hcs]; norm_num
  have hbu := flowDeriv_bounds (hx := hx) (Phi := Phi) hell hbd T u
  have hbc := flowDeriv_bounds (hx := hx) (Phi := Phi) hell hbd T c
  rw [habsT] at hbu hbc
  rw [← hper, abs_le]
  constructor <;> simp only [flowDefectC1] <;> nlinarith [hbu.1, hbu.2, hbc.1, hbc.2]

/-- **The second derivative of a flow marking is bounded by the second
derivative of the field.**  A restatement of
`FlowDerivative.abs_flowDeriv_deriv_le` in the form used by the `C²`
comparison. -/
theorem abs_flowDeriv_deriv_le' (hell : 0 < ell) (hbd : ∀ s x, |hx s x| ≤ (K : ℝ))
    {K2 : ℝ} (hxxbd : ∀ s x, |hxx s x| ≤ K2) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    |flowDeriv hx Phi ell T u
        * ∫ s in (0 : ℝ)..T, hxx s (Phi s u) * flowDeriv hx Phi ell s u|
      ≤ flowDefectC2 ell K K2 T := by
  have h := FlowDerivative.abs_flowDeriv_deriv_le (hx := hx) (hxx := hxx) (Phi := Phi)
    hell hbd hxxbd u T
  rwa [abs_of_nonneg hT] at h

/-! ### The marked distance of a curve read in a flow marking -/

variable {c kmin dlt : ℝ} {q r : Data} {Θ k : ℝ → ℝ} {e0 L kb kL : ℝ}

/-- **A curve read in a gauge marking produced by a flow is close to the curve
in the metric of the space of marked curves.**  The two flow defects of the
marking are produced from the Lipschitz constant `K` of the field and the bound
`K₂` for its second space derivative; only the `C⁰` defect `ε₀` is assumed. -/
theorem dist_le_of_flow_marking
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : Continuous (Function.uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun s => Phi s u) (h t (Phi t u)) t)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x)
    (hxcont : Continuous (Function.uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x)
    (hxxcont : Continuous (Function.uncurry hxx))
    {K2 : ℝ} (hxxbd : ∀ s x, |hxx s x| ≤ K2) {T : ℝ} (hT : 0 ≤ T)
    (hc : 0 < c) (hq : IsTubeMember c kmin dlt q) (hL : perim q = L)
    (hev : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hr1 : ∀ u, r.1 u = ev q (Phi T u))
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u)
    (hrv : ∀ u, HasDerivAt (⇑r.2.1) (r.2.2 u) u)
    (hdev : ∀ u, |Phi T u - L * u| ≤ e0) (hperiod : Phi T 1 - Phi T 0 = L) :
    dist r q ≤ markingC2Bound e0 (flowDefectC1 ell K T) (flowDefectC2 ell K K2 T) L kb kL := by
  have hbd : ∀ s x, |hx s x| ≤ (K : ℝ) := FlowDerivative.abs_hx_le hlip hxd
  have hphi : ∀ u, HasDerivAt (fun u' => Phi T u') (flowDeriv hx Phi ell T u) u := fun u =>
    FlowDerivative.hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u T
  have hphi1 : ∀ u, HasDerivAt (fun u' => flowDeriv hx Phi ell T u')
      (flowDeriv hx Phi ell T u
        * ∫ s in (0 : ℝ)..T, hxx s (Phi s u) * flowDeriv hx Phi ell s u) u := fun u =>
    FlowDerivative.hasDerivAt_flowDeriv hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont
      hxxbd u T
  refine MarkingDeviationC2.dist_le_of_marking_defect_c2
    (phi := fun u => Phi T u) (phi1 := fun u => flowDeriv hx Phi ell T u)
    (phi2 := fun u => flowDeriv hx Phi ell T u
      * ∫ s in (0 : ℝ)..T, hxx s (Phi s u) * flowDeriv hx Phi ell s u)
    hc hq hL hev hΘ hkb hklip hr1 hrd hrv hphi hphi1 hdev ?_ ?_
  · intro u
    have h := abs_flowDeriv_sub_period_le (hx := hx) (Phi := Phi) hell hbd hT hphi u
    rwa [hperiod] at h
  · exact fun u => abs_flowDeriv_deriv_le' (hx := hx) (hxx := hxx) (Phi := Phi)
      hell hbd hxxbd hT u

/-! ### The defects from a time-dependent bound for the field

A uniform Lipschitz constant `K` gives defects of size `KT`, which need not be
small along a path of small cost.  The bounds below use instead a time-dependent
bound `|∂ₓh(s,·)| ≤ C s`, `|∂²ₓh(s,·)| ≤ C₂ s`, and are governed by the two time
integrals `c₀ = ∫₀^T C` and `c₂ = ∫₀^T C₂`; along a normal path these are
bounded by multiples of its cost, so the defects tend to zero with it. -/

/-- The `C¹` defect of a flow marking, from the time integral of a bound for the
space derivative of the field. -/
def flowDefectC1Int (ell c0 : ℝ) : ℝ := ell * (Real.exp c0 - Real.exp (-c0))

/-- The `C²` defect of a flow marking, from the time integrals of bounds for the
first two space derivatives of the field. -/
def flowDefectC2Int (ell c0 c2 : ℝ) : ℝ := ell ^ 2 * Real.exp (2 * c0) * c2

/-- On a bounded nonnegative cost interval the two exponential flow defects
are linear in the cost, with explicit uniform coefficients. -/
theorem flowDefectInt_linear_bounds
    {ell kappa kappa2 x M : ℝ}
    (hell : 0 ≤ ell) (hk : 0 ≤ kappa) (hk2 : 0 ≤ kappa2)
    (hx0 : 0 ≤ x) (hxM : x ≤ M) :
    flowDefectC1Int ell (kappa * x) ≤
        (ell * kappa * (Real.exp (kappa * M) + 1)) * x ∧
      flowDefectC2Int ell (kappa * x) (kappa2 * x) ≤
        (ell ^ 2 * Real.exp (2 * kappa * M) * kappa2) * x := by
  have hy0 : 0 ≤ kappa * x := mul_nonneg hk hx0
  have hyM : kappa * x ≤ kappa * M := mul_le_mul_of_nonneg_left hxM hk
  have hexp : Real.exp (kappa * x) ≤ Real.exp (kappa * M) :=
    Real.exp_le_exp.2 hyM
  have hplus : Real.exp (kappa * x) - 1 ≤
      (kappa * x) * Real.exp (kappa * M) := by
    have h1 : (-(kappa * x)) + 1 ≤ Real.exp (-(kappa * x)) := Real.add_one_le_exp _
    have hpos : (0:ℝ) < Real.exp (kappa * x) := Real.exp_pos _
    have h2 : Real.exp (-(kappa * x)) * Real.exp (kappa * x) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : Real.exp (kappa * x) - 1 ≤ (kappa * x) * Real.exp (kappa * x) := by
      nlinarith [mul_le_mul_of_nonneg_right h1 hpos.le, h2]
    exact h3.trans (mul_le_mul_of_nonneg_left hexp hy0)
  have hminus : 1 - Real.exp (-(kappa * x)) ≤ kappa * x := by
    nlinarith [Real.add_one_le_exp (-(kappa * x))]
  constructor
  · unfold flowDefectC1Int
    have hsplit : Real.exp (kappa * x) - Real.exp (-(kappa * x)) =
        (Real.exp (kappa * x) - 1) + (1 - Real.exp (-(kappa * x))) := by ring
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hplus hminus) hell]
  · unfold flowDefectC2Int
    have he2 : Real.exp (2 * (kappa * x)) ≤ Real.exp (2 * kappa * M) :=
      Real.exp_le_exp.2 (by nlinarith)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he2 (sq_nonneg ell)) (mul_nonneg hk2 hx0)

theorem flowDefectC1Int_nonneg {c0 : ℝ} (hell : 0 ≤ ell) (hc0 : 0 ≤ c0) :
    0 ≤ flowDefectC1Int ell c0 := by
  have h : Real.exp (-c0) ≤ Real.exp c0 := Real.exp_le_exp.2 (by linarith)
  have := mul_nonneg hell (sub_nonneg.2 h)
  simpa [flowDefectC1Int] using this

/-- The `C¹` flow defect is monotone in the time integral of the bound. -/
theorem flowDefectC1Int_mono {c0 c0' : ℝ} (hell : 0 ≤ ell) (h : c0 ≤ c0') :
    flowDefectC1Int ell c0 ≤ flowDefectC1Int ell c0' := by
  have h1 : Real.exp c0 ≤ Real.exp c0' := Real.exp_le_exp.2 h
  have h2 : Real.exp (-c0') ≤ Real.exp (-c0) := Real.exp_le_exp.2 (by linarith)
  have : Real.exp c0 - Real.exp (-c0) ≤ Real.exp c0' - Real.exp (-c0') := by linarith
  exact mul_le_mul_of_nonneg_left this hell

/-- The `C²` flow defect is monotone in the two time integrals. -/
theorem flowDefectC2Int_mono {c0 c0' c2 c2' : ℝ} (hc2 : 0 ≤ c2) (h0 : c0 ≤ c0') (h2 : c2 ≤ c2') :
    flowDefectC2Int ell c0 c2 ≤ flowDefectC2Int ell c0' c2' := by
  have hexp : Real.exp (2 * c0) ≤ Real.exp (2 * c0') := Real.exp_le_exp.2 (by linarith)
  have h1 : ell ^ 2 * Real.exp (2 * c0) ≤ ell ^ 2 * Real.exp (2 * c0') :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  exact mul_le_mul h1 h2 hc2 (by positivity)

/-- The `C¹` flow defect vanishes with the time integral of the bound. -/
theorem tendsto_flowDefectC1Int_zero {ι : Type*} {l : Filter ι} {c0 : ι → ℝ}
    (hc0 : Filter.Tendsto c0 l (nhds 0)) :
    Filter.Tendsto (fun n => flowDefectC1Int ell (c0 n)) l (nhds 0) := by
  have h1 : Filter.Tendsto (fun n => Real.exp (c0 n)) l (nhds 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp hc0
  have h2 : Filter.Tendsto (fun n => Real.exp (-(c0 n))) l (nhds 1) := by
    have hneg : Filter.Tendsto (fun n => -(c0 n)) l (nhds 0) := by simpa using hc0.neg
    simpa using (Real.continuous_exp.tendsto 0).comp hneg
  have := (h1.sub h2).const_mul ell
  simpa [flowDefectC1Int] using this

/-- The `C²` flow defect vanishes with the time integrals of the bounds. -/
theorem tendsto_flowDefectC2Int_zero {ι : Type*} {l : Filter ι} {c0 c2 : ι → ℝ}
    (hc0 : Filter.Tendsto c0 l (nhds 0)) (hc2 : Filter.Tendsto c2 l (nhds 0)) :
    Filter.Tendsto (fun n => flowDefectC2Int ell (c0 n) (c2 n)) l (nhds 0) := by
  have h1 : Filter.Tendsto (fun n => Real.exp (2 * c0 n)) l (nhds 1) := by
    have h2c : Filter.Tendsto (fun n => 2 * c0 n) l (nhds 0) := by simpa using hc0.const_mul 2
    simpa using (Real.continuous_exp.tendsto 0).comp h2c
  have := ((h1.const_mul (ell ^ 2)).mul hc2)
  simpa [flowDefectC2Int] using this

/-- **The whole `C²` defect bound of a flow marking vanishes with the position
defect and the two time integrals.**  Along a family of normal paths whose cost
tends to zero — so that the field of the gauge flow, being bounded by the cost
density, has vanishing integrals — the curve read in the gauge marking converges
to the curve itself in the metric of the space of marked curves. -/
theorem tendsto_flow_marking_bound_zero {ι : Type*} {l : Filter ι} {e0 c0 c2 : ι → ℝ}
    {L kb kL : ℝ} (he0 : Filter.Tendsto e0 l (nhds 0))
    (hc0 : Filter.Tendsto c0 l (nhds 0)) (hc2 : Filter.Tendsto c2 l (nhds 0)) :
    Filter.Tendsto (fun n => markingC2Bound (e0 n) (flowDefectC1Int ell (c0 n))
      (flowDefectC2Int ell (c0 n) (c2 n)) L kb kL) l (nhds 0) :=
  MarkingDeviationC2.tendsto_markingC2Bound_zero he0
    (tendsto_flowDefectC1Int_zero hc0) (tendsto_flowDefectC2Int_zero hc0 hc2)

/-- The logarithmic rate of the flow over `[0,t]` is bounded by the time
integral of a bound for the space derivative of the field. -/
theorem abs_integral_hx_le {C : ℝ → ℝ} (hbdC : ∀ s x, |hx s x| ≤ C s) (hC : Continuous C)
    {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (u : ℝ) :
    |∫ s in (0 : ℝ)..t, hx s (Phi s u)| ≤ ∫ s in (0 : ℝ)..T, C s := by
  have hCnn : ∀ s, 0 ≤ C s := fun s => le_trans (abs_nonneg _) (hbdC s 0)
  have h1 : |∫ s in (0 : ℝ)..t, hx s (Phi s u)| ≤ ∫ s in (0 : ℝ)..t, C s := by
    have := intervalIntegral.norm_integral_le_of_norm_le (f := fun s => hx s (Phi s u))
      (g := C) (μ := MeasureTheory.volume) ht0
      (Filter.Eventually.of_forall fun s _ => by simpa [Real.norm_eq_abs] using hbdC s (Phi s u))
      (hC.intervalIntegrable 0 t)
    simpa [Real.norm_eq_abs] using this
  have h2 : (∫ s in (0 : ℝ)..t, C s) ≤ ∫ s in (0 : ℝ)..T, C s :=
    intervalIntegral.integral_mono_interval le_rfl ht0 htT
      (Filter.Eventually.of_forall fun s => hCnn s) (hC.intervalIntegrable 0 T)
  linarith

/-- **Two-sided bounds for the derivative of the flow in its initial condition**,
from a time-dependent bound for the space derivative of the field. -/
theorem flowDeriv_bounds_int (hell : 0 < ell) {C : ℝ → ℝ} (hbdC : ∀ s x, |hx s x| ≤ C s)
    (hC : Continuous C) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (u : ℝ) :
    ell * Real.exp (-(∫ s in (0 : ℝ)..T, C s)) ≤ flowDeriv hx Phi ell t u ∧
      flowDeriv hx Phi ell t u ≤ ell * Real.exp (∫ s in (0 : ℝ)..T, C s) := by
  have h := abs_integral_hx_le (hx := hx) (Phi := Phi) hbdC hC ht0 htT u
  rw [abs_le] at h
  exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h.1) hell.le,
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h.2) hell.le⟩

/-- **The `C¹` defect of a flow marking, in terms of the time integral of a
bound for the space derivative of the field.** -/
theorem abs_flowDeriv_sub_period_le_int (hell : 0 < ell) {C : ℝ → ℝ}
    (hbdC : ∀ s x, |hx s x| ≤ C s) (hC : Continuous C) {T : ℝ} (hT : 0 ≤ T)
    (hphi : ∀ u, HasDerivAt (fun u' => Phi T u') (flowDeriv hx Phi ell T u) u) (u : ℝ) :
    |flowDeriv hx Phi ell T u - (Phi T 1 - Phi T 0)|
      ≤ flowDefectC1Int ell (∫ s in (0 : ℝ)..T, C s) := by
  obtain ⟨c, -, hcs⟩ := exists_hasDerivAt_eq_slope (fun u' => Phi T u')
    (fun u' => flowDeriv hx Phi ell T u') zero_lt_one
    (fun x _ => ((hphi x).continuousAt).continuousWithinAt) (fun x _ => hphi x)
  have hper : flowDeriv hx Phi ell T c = Phi T 1 - Phi T 0 := by
    rw [hcs]; norm_num
  have hbu := flowDeriv_bounds_int (hx := hx) (Phi := Phi) hell hbdC hC hT le_rfl u
  have hbc := flowDeriv_bounds_int (hx := hx) (Phi := Phi) hell hbdC hC hT le_rfl c
  rw [← hper, abs_le]
  constructor <;> simp only [flowDefectC1Int] <;>
    nlinarith [hbu.1, hbu.2, hbc.1, hbc.2]

/-- **The `C²` defect of a flow marking, in terms of the time integrals of
bounds for the first two space derivatives of the field.** -/
theorem abs_flowDeriv_deriv_le_int (hell : 0 < ell) {C C2 : ℝ → ℝ}
    (hbdC : ∀ s x, |hx s x| ≤ C s) (hC : Continuous C)
    (hbdC2 : ∀ s x, |hxx s x| ≤ C2 s) (hC2 : Continuous C2) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    |flowDeriv hx Phi ell T u
        * ∫ s in (0 : ℝ)..T, hxx s (Phi s u) * flowDeriv hx Phi ell s u|
      ≤ flowDefectC2Int ell (∫ s in (0 : ℝ)..T, C s) (∫ s in (0 : ℝ)..T, C2 s) := by
  set c0 : ℝ := ∫ s in (0 : ℝ)..T, C s with hc0
  set M : ℝ := ell * Real.exp c0 with hM
  have hM0 : 0 ≤ M := by positivity
  have hC2nn : ∀ s, 0 ≤ C2 s := fun s => le_trans (abs_nonneg _) (hbdC2 s 0)
  have h1 : |flowDeriv hx Phi ell T u| ≤ M := by
    rw [abs_of_pos (flowDeriv_pos hell T u)]
    exact (flowDeriv_bounds_int (hx := hx) (Phi := Phi) hell hbdC hC hT le_rfl u).2
  have h2 : |∫ s in (0 : ℝ)..T, hxx s (Phi s u) * flowDeriv hx Phi ell s u|
      ≤ (∫ s in (0 : ℝ)..T, C2 s) * M := by
    have hb : ∀ s ∈ Set.Ioc (0 : ℝ) T,
        ‖hxx s (Phi s u) * flowDeriv hx Phi ell s u‖ ≤ C2 s * M := by
      intro s hs
      have hfl : |flowDeriv hx Phi ell s u| ≤ M := by
        rw [abs_of_pos (flowDeriv_pos hell s u)]
        exact (flowDeriv_bounds_int (hx := hx) (Phi := Phi) hell hbdC hC hs.1.le hs.2 u).2
      have := mul_le_mul (hbdC2 s (Phi s u)) hfl (abs_nonneg _) (hC2nn s)
      simpa [Real.norm_eq_abs, abs_mul] using this
    have hint := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun s => hxx s (Phi s u) * flowDeriv hx Phi ell s u)
      (g := fun s => C2 s * M) (μ := MeasureTheory.volume) hT (Filter.Eventually.of_forall fun s hs => hb s hs)
      ((hC2.mul continuous_const).intervalIntegrable 0 T)
    rw [intervalIntegral.integral_mul_const] at hint
    simpa [Real.norm_eq_abs] using hint
  have hprod : |flowDeriv hx Phi ell T u| *
      |∫ s in (0 : ℝ)..T, hxx s (Phi s u) * flowDeriv hx Phi ell s u|
      ≤ M * ((∫ s in (0 : ℝ)..T, C2 s) * M) :=
    mul_le_mul h1 h2 (abs_nonneg _) hM0
  have hval : M * ((∫ s in (0 : ℝ)..T, C2 s) * M)
      = flowDefectC2Int ell c0 (∫ s in (0 : ℝ)..T, C2 s) := by
    rw [hM, flowDefectC2Int, two_mul, Real.exp_add]
    ring
  rw [abs_mul]
  rw [hval] at hprod
  exact hprod

/-- **A curve read in a gauge marking produced by a flow is close to the curve in
the metric of the space of marked curves**, with the two flow defects governed by
the time integrals `c₀ = ∫₀^T C` and `c₂ = ∫₀^T C₂` of bounds for the first two
space derivatives of the field. -/
theorem dist_le_of_flow_marking_int
    (hlip : ∀ t, LipschitzWith K (h t)) (hcont : Continuous (Function.uncurry h))
    (hPhid : ∀ u t, HasDerivAt (fun s => Phi s u) (h t (Phi t u)) t)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hxd : ∀ s x, HasDerivAt (h s) (hx s x) x)
    (hxcont : Continuous (Function.uncurry hx))
    (hxxd : ∀ s x, HasDerivAt (hx s) (hxx s x) x)
    (hxxcont : Continuous (Function.uncurry hxx))
    {K2 : ℝ} (hxxbd : ∀ s x, |hxx s x| ≤ K2)
    {C C2 : ℝ → ℝ} (hbdC : ∀ s x, |hx s x| ≤ C s) (hC : Continuous C)
    (hbdC2 : ∀ s x, |hxx s x| ≤ C2 s) (hC2 : Continuous C2)
    {T : ℝ} (hT : 0 ≤ T)
    (hc : 0 < c) (hq : IsTubeMember c kmin dlt q) (hL : perim q = L)
    (hev : ∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (k s) s) (hkb : ∀ s, |k s| ≤ kb)
    (hklip : ∀ s t, |k s - k t| ≤ kL * |s - t|)
    (hr1 : ∀ u, r.1 u = ev q (Phi T u))
    (hrd : ∀ u, HasDerivAt (⇑r.1) (r.2.1 u) u)
    (hrv : ∀ u, HasDerivAt (⇑r.2.1) (r.2.2 u) u)
    (hdev : ∀ u, |Phi T u - L * u| ≤ e0) (hperiod : Phi T 1 - Phi T 0 = L) :
    dist r q ≤ markingC2Bound e0 (flowDefectC1Int ell (∫ s in (0 : ℝ)..T, C s))
      (flowDefectC2Int ell (∫ s in (0 : ℝ)..T, C s) (∫ s in (0 : ℝ)..T, C2 s)) L kb kL := by
  have hphi : ∀ u, HasDerivAt (fun u' => Phi T u') (flowDeriv hx Phi ell T u) u := fun u =>
    FlowDerivative.hasDerivAt_flow_initial hlip hcont hPhid hell hPhi0 hxd u T
  have hphi1 : ∀ u, HasDerivAt (fun u' => flowDeriv hx Phi ell T u')
      (flowDeriv hx Phi ell T u
        * ∫ s in (0 : ℝ)..T, hxx s (Phi s u) * flowDeriv hx Phi ell s u) u := fun u =>
    FlowDerivative.hasDerivAt_flowDeriv hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont
      hxxbd u T
  refine MarkingDeviationC2.dist_le_of_marking_defect_c2
    (phi := fun u => Phi T u) (phi1 := fun u => flowDeriv hx Phi ell T u)
    (phi2 := fun u => flowDeriv hx Phi ell T u
      * ∫ s in (0 : ℝ)..T, hxx s (Phi s u) * flowDeriv hx Phi ell s u)
    hc hq hL hev hΘ hkb hklip hr1 hrd hrv hphi hphi1 hdev ?_ ?_
  · intro u
    have h := abs_flowDeriv_sub_period_le_int (hx := hx) (Phi := Phi) hell hbdC hC hT hphi u
    rwa [hperiod] at h
  · exact fun u => abs_flowDeriv_deriv_le_int (hx := hx) (hxx := hxx) (Phi := Phi)
      hell hbdC hC hbdC2 hC2 hT u

end MarkingFlowDefectC2
