import Mathlib
import UnitTangentIterates.GeometricLimit
import UnitTangentIterates.Oval

/-!
# The space of marked curves: a concrete complete tube of ovals

The shadowing scheme of *A Noncircular Oval with Convex Unit-Tangent Iterates*
(`ShadowingScheme.lean`) is run in a **complete
metric space of marked curves**: a tube of closed convex curves, compared in
one common periodic parameter with the `C²` distance of the marked geometric
topology.  `MarkedTopology.lean` formalizes the functionals of that topology
and the fact that summable normal paths converge; this file constructs the
space itself.

A **marked curve** is carried by a triple `p = (X, V, A)` of bounded continuous
maps `ℝ → ℂ`, thought of as a curve in the normalized parameter `u ∈ ℝ/ℤ`
together with its first two derivatives.  The ambient space of such triples is
a complete metric space for the uniform (`C²`) distance, being a product of
spaces of bounded continuous functions.  The **tube** `tube c kmin delta` cuts
out of it the triples that

* are genuine `C²` data: `X' = V`, `V' = A`;
* are `1`-periodic;
* have constant speed `‖V‖ ≡ L ≥ c` (so `u` is arclength rescaled by the
  perimeter `L`);
* have curvature at least `kmin`, in the form `kmin‖V‖³ ≤ Im(V̄A)`;
* satisfy the quantitative chord-arc bound `delta·d(u,v) ≤ ‖X u − X v‖`, `d`
  the distance of `ℝ/ℤ`.

Main results:

* `exists_angle` : a `C¹` unit vector field along a curve has a differentiable
  angle, `τ = e^{iθ}` with `θ' = Im(τ̄τ')` — the tangent-angle lifting behind
  the definition of an oval;
* `isClosed_tube` : the tube is closed in the ambient space, hence
* `completeSpace_tube` : **the tube is a complete metric space**;
* `dist_apply_le`, `abs_perim_sub_le_dist` : the marked distance dominates the
  uniform distance of the curves and the difference of the perimeters, so
  evaluation and the perimeter functional are `1`-Lipschitz;
* `isOval_ev` : **every member of the tube is an oval**, once reparametrized by
  arclength — the tube really is a space of ovals.

Together these provide, for the abstract hypotheses of the shadowing scheme,
the complete space of marked ovals
with its Lipschitz evaluation and perimeter.  What is still not constructed
here is the selected inverse `B` on this space.
-/

noncomputable section

open Set Function Filter Topology
open scoped BoundedContinuousFunction

namespace MarkedSpace

/-! ### The tangent-angle lifting -/

/-- Along a curve of constant unit speed the acceleration is orthogonal to the
velocity: `Re(τ̄ τ') = 0`. -/
theorem re_conj_mul_deriv_eq_zero {tau D : ℝ → ℂ} (hnorm : ∀ s, ‖tau s‖ = 1)
    (hderiv : ∀ s, HasDerivAt tau (D s) s) (s : ℝ) :
    ((starRingEnd ℂ) (tau s) * D s).re = 0 := by
  have hx : ∀ t, HasDerivAt (fun t => (tau t).re) (D t).re t := fun t =>
    (Complex.reCLM.hasFDerivAt).comp_hasDerivAt t (hderiv t)
  have hy : ∀ t, HasDerivAt (fun t => (tau t).im) (D t).im t := fun t =>
    (Complex.imCLM.hasFDerivAt).comp_hasDerivAt t (hderiv t)
  have hsq : ∀ t, (tau t).re ^ 2 + (tau t).im ^ 2 = 1 := by
    intro t
    have h2 : ‖tau t‖ ^ 2 = 1 := by rw [hnorm t]; ring
    rw [Complex.sq_norm] at h2
    simpa [Complex.normSq_apply, sq] using h2
  have hd : HasDerivAt (fun t => (tau t).re ^ 2 + (tau t).im ^ 2)
      (2 * (tau s).re * (D s).re + 2 * (tau s).im * (D s).im) s := by
    have h := ((hx s).pow 2).add ((hy s).pow 2)
    convert h using 1
    ring
  have hconst : HasDerivAt (fun t => (tau t).re ^ 2 + (tau t).im ^ 2) 0 s := by
    have he : (fun t => (tau t).re ^ 2 + (tau t).im ^ 2) = fun _ : ℝ => (1 : ℝ) := funext hsq
    rw [he]
    exact hasDerivAt_const _ _
  have hu := hd.unique hconst
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  linarith

/-- The Frenet relation `τ' = i k τ` for a unit vector field, `k = Im(τ̄τ')`. -/
theorem deriv_eq_curvature_mul {tau D : ℝ → ℂ} (hnorm : ∀ s, ‖tau s‖ = 1) (s : ℝ)
    (hre : ((starRingEnd ℂ) (tau s) * D s).re = 0) :
    D s = Complex.I * (((starRingEnd ℂ) (tau s) * D s).im : ℂ) * tau s := by
  set k : ℝ := ((starRingEnd ℂ) (tau s) * D s).im with hk
  have hkey : (starRingEnd ℂ) (tau s) * D s = Complex.I * (k : ℂ) := by
    apply Complex.ext
    · simpa using hre
    · simp [hk]
  have hns : (starRingEnd ℂ) (tau s) * tau s = 1 := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hnorm s]
    norm_num
  calc D s = ((starRingEnd ℂ) (tau s) * tau s) * D s := by rw [hns, one_mul]
    _ = ((starRingEnd ℂ) (tau s) * D s) * tau s := by ring
    _ = Complex.I * (k : ℂ) * tau s := by rw [hkey]

/-- **The tangent-angle lifting.**  A `C¹` field `τ` of unit vectors along the
line is `e^{iθ}` for a differentiable angle `θ` whose derivative is the
curvature `Im(τ̄ τ')`. -/
theorem exists_angle {tau D : ℝ → ℂ} (hnorm : ∀ s, ‖tau s‖ = 1)
    (hderiv : ∀ s, HasDerivAt tau (D s) s) (hcont : Continuous D) :
    ∃ theta : ℝ → ℝ, (∀ s, HasDerivAt theta (((starRingEnd ℂ) (tau s) * D s).im) s) ∧
      ∀ s, Complex.exp (Complex.I * (theta s : ℂ)) = tau s := by
  have hDeq : ∀ s, D s = Complex.I * (((starRingEnd ℂ) (tau s) * D s).im : ℂ) * tau s := fun s =>
    deriv_eq_curvature_mul hnorm s (re_conj_mul_deriv_eq_zero hnorm hderiv s)
  have hcontTau : Continuous tau := continuous_iff_continuousAt.2 fun s => (hderiv s).continuousAt
  set k : ℝ → ℝ := fun s => ((starRingEnd ℂ) (tau s) * D s).im with hkdef
  have hkcont : Continuous k := by
    have h : Continuous fun s => (starRingEnd ℂ) (tau s) * D s :=
      (Complex.continuous_conj.comp hcontTau).mul hcont
    exact Complex.continuous_im.comp h
  set theta : ℝ → ℝ := fun s => (tau 0).arg + ∫ x in (0 : ℝ)..s, k x with hthetadef
  have hthetaderiv : ∀ s, HasDerivAt theta (k s) s := by
    intro s
    have h := (hkcont.integral_hasStrictDerivAt 0 s).hasDerivAt
    simpa [hthetadef] using h.const_add ((tau 0).arg)
  refine ⟨theta, hthetaderiv, ?_⟩
  set g : ℝ → ℂ := fun s => tau s * Complex.exp (-(Complex.I * (theta s : ℂ))) with hgdef
  have hgderiv : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => -(Complex.I * (theta s : ℂ)))
        (-(Complex.I * (k s : ℂ))) s := (((hthetaderiv s).ofReal_comp).const_mul Complex.I).neg
    have h3 := (hderiv s).mul h1.cexp
    have hz : D s * Complex.exp (-(Complex.I * (theta s : ℂ)))
        + tau s * (Complex.exp (-(Complex.I * (theta s : ℂ))) * -(Complex.I * (k s : ℂ))) = 0 := by
      rw [hDeq s]; ring
    rw [hgdef]
    convert h3 using 1
    rw [← hz]
  have hgconst : ∀ s, g s = g 0 := by
    intro s
    have hdiff : Differentiable ℝ g := fun x => (hgderiv x).differentiableAt
    exact is_const_of_deriv_eq_zero hdiff (fun x => (hgderiv x).deriv) s 0
  have hg0 : g 0 = 1 := by
    have harg : Complex.exp (Complex.I * ((tau 0).arg : ℂ)) = tau 0 := by
      have h := Complex.norm_mul_exp_arg_mul_I (tau 0)
      rw [hnorm 0] at h
      rw [mul_comm]
      simpa using h
    have hth0 : theta 0 = (tau 0).arg := by simp [hthetadef]
    rw [hgdef]
    simp only [hth0]
    set a : ℝ := (tau 0).arg with ha
    rw [← harg, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  intro s
  have hs := hgconst s
  rw [hg0, hgdef] at hs
  simp only at hs
  rw [Complex.exp_neg] at hs
  have hexp : Complex.exp (Complex.I * (theta s : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  field_simp at hs
  exact hs.symm

/-! ### The tube of marked curves -/

/-- The distance of `u` and `v` in the circle `ℝ/ℤ`, for parameters in the
fundamental interval `[0,1]`. -/
def cyc (u v : ℝ) : ℝ := min |u - v| (1 - |u - v|)

theorem cyc_eq_zero_iff {u v : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (hv : v ∈ Ico (0 : ℝ) 1)
    (h : cyc u v ≤ 0) : u = v := by
  rcases hu with ⟨hu0, hu1⟩
  rcases hv with ⟨hv0, hv1⟩
  have hlt : |u - v| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have h' := min_le_iff.1 h
  rcases h' with h1 | h2
  · have : |u - v| = 0 := le_antisymm h1 (abs_nonneg _)
    have := abs_eq_zero.1 this
    linarith
  · linarith

/-- The carrier of the space of marked curves: a curve, its velocity and its
acceleration in the normalized parameter, as bounded continuous maps. -/
abbrev Data : Type := (ℝ →ᵇ ℂ) × (ℝ →ᵇ ℂ) × (ℝ →ᵇ ℂ)

/-- Membership in the tube of marked curves with speed at least `c`, curvature
at least `kmin` and chord-arc constant `delta`. -/
structure IsTubeMember (c kmin delta : ℝ) (p : Data) : Prop where
  /-- `X' = V`. -/
  hasDerivAt_curve : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u
  /-- `V' = A`. -/
  hasDerivAt_vel : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u
  /-- the curve is closed, of period one in the normalized parameter. -/
  periodic : Periodic (⇑p.1) 1
  /-- the normalized parameter is arclength rescaled: the speed is constant. -/
  speed_const : ∀ u v, ‖p.2.1 u‖ = ‖p.2.1 v‖
  /-- the perimeter is at least `c`. -/
  speed_lb : ∀ u, c ≤ ‖p.2.1 u‖
  /-- the curvature is at least `kmin`. -/
  curv_lb : ∀ u, kmin * ‖p.2.1 u‖ ^ 3 ≤ ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im
  /-- the quantitative chord-arc bound, a closed form of embeddedness. -/
  chord : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, delta * cyc u v ≤ ‖p.1 u - p.1 v‖

/-- **The space of marked curves**: the tube of closed `C²` curves of constant
speed at least `c`, curvature at least `kmin` and chord-arc constant `delta`,
in the normalized parameter. -/
def tube (c kmin delta : ℝ) : Set Data := {p | IsTubeMember c kmin delta p}

/-- Evaluation is `1`-Lipschitz for the marked distance. -/
theorem dist_apply_le (p q : Data) (u : ℝ) : ‖p.1 u - q.1 u‖ ≤ dist p q := by
  have h1 : dist (p.1 u) (q.1 u) ≤ dist p.1 q.1 := BoundedContinuousFunction.dist_coe_le_dist u
  have h2 : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  rw [← dist_eq_norm]; linarith

/-- The velocities, too, are compared by the marked distance. -/
theorem dist_vel_apply_le (p q : Data) (u : ℝ) : ‖p.2.1 u - q.2.1 u‖ ≤ dist p q := by
  have h1 : dist (p.2.1 u) (q.2.1 u) ≤ dist p.2.1 q.2.1 :=
    BoundedContinuousFunction.dist_coe_le_dist u
  have h2 : dist p.2.1 q.2.1 ≤ dist p.2 q.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h3 : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
  rw [← dist_eq_norm]; linarith

/-- The perimeter of a marked curve: the (constant) speed in the normalized
parameter. -/
def perim (p : Data) : ℝ := ‖p.2.1 0‖

theorem perim_pos {c kmin delta : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c kmin delta p) : 0 < perim p :=
  lt_of_lt_of_le hc (hp.speed_lb 0)

theorem norm_vel_eq_perim {c kmin delta : ℝ} {p : Data} (hp : IsTubeMember c kmin delta p)
    (u : ℝ) : ‖p.2.1 u‖ = perim p := hp.speed_const u 0

/-- **The perimeter is `1`-Lipschitz** for the marked distance. -/
theorem abs_perim_sub_le_dist (p q : Data) : |perim p - perim q| ≤ dist p q := by
  have h := dist_vel_apply_le p q 0
  have := abs_norm_sub_norm_le (p.2.1 0) (q.2.1 0)
  exact le_trans this h

/-! ### Completeness of the tube -/

/-- **The tube is closed** in the ambient space of `C²` data. -/
theorem isClosed_tube (c kmin delta : ℝ) : IsClosed (tube c kmin delta) := by
  apply IsSeqClosed.isClosed
  intro pn p hmem hlim
  have h1 : TendstoUniformly (fun n => ⇑(pn n).1) (⇑p.1) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 ((continuous_fst.tendsto p).comp hlim)
  have h2 : TendstoUniformly (fun n => ⇑(pn n).2.1) (⇑p.2.1) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
      (((continuous_fst.comp continuous_snd).tendsto p).comp hlim)
  have h3 : TendstoUniformly (fun n => ⇑(pn n).2.2) (⇑p.2.2) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
      (((continuous_snd.comp continuous_snd).tendsto p).comp hlim)
  have hp1 : ∀ u, Tendsto (fun n => (pn n).1 u) atTop (𝓝 (p.1 u)) := fun u => h1.tendsto_at u
  have hp2 : ∀ u, Tendsto (fun n => (pn n).2.1 u) atTop (𝓝 (p.2.1 u)) := fun u => h2.tendsto_at u
  have hp3 : ∀ u, Tendsto (fun n => (pn n).2.2 u) atTop (𝓝 (p.2.2 u)) := fun u => h3.tendsto_at u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun u => GeometricLimit.hasDerivAt_of_uniform_limit
      (fun n u => (hmem n).hasDerivAt_curve u) h2 hp1 u
  · exact fun u => GeometricLimit.hasDerivAt_of_uniform_limit
      (fun n u => (hmem n).hasDerivAt_vel u) h3 hp2 u
  · intro u
    refine tendsto_nhds_unique (hp1 (u + 1)) ?_
    simpa [(hmem _).periodic u] using hp1 u
  · intro u v
    have hu : Tendsto (fun n => ‖(pn n).2.1 u‖) atTop (𝓝 ‖p.2.1 u‖) :=
      (continuous_norm.tendsto _).comp (hp2 u)
    have hv : Tendsto (fun n => ‖(pn n).2.1 v‖) atTop (𝓝 ‖p.2.1 v‖) :=
      (continuous_norm.tendsto _).comp (hp2 v)
    refine tendsto_nhds_unique hu ?_
    simpa [fun n => (hmem n).speed_const u v] using hv
  · intro u
    have hu : Tendsto (fun n => ‖(pn n).2.1 u‖) atTop (𝓝 ‖p.2.1 u‖) :=
      (continuous_norm.tendsto _).comp (hp2 u)
    exact ge_of_tendsto hu (Eventually.of_forall fun n => (hmem n).speed_lb u)
  · intro u
    have hlhs : Tendsto (fun n => kmin * ‖(pn n).2.1 u‖ ^ 3) atTop (𝓝 (kmin * ‖p.2.1 u‖ ^ 3)) :=
      ((continuous_const.mul ((continuous_norm.comp continuous_id).pow 3)).tendsto _).comp (hp2 u)
    have hrhs : Tendsto (fun n => ((starRingEnd ℂ) ((pn n).2.1 u) * (pn n).2.2 u).im) atTop
        (𝓝 (((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im)) := by
      have hc : Continuous fun z : ℂ × ℂ => ((starRingEnd ℂ) z.1 * z.2).im :=
        Complex.continuous_im.comp ((Complex.continuous_conj.comp continuous_fst).mul continuous_snd)
      exact (hc.tendsto _).comp ((hp2 u).prodMk_nhds (hp3 u))
    exact le_of_tendsto_of_tendsto' hlhs hrhs (fun n => (hmem n).curv_lb u)
  · intro u hu v hv
    have hrhs : Tendsto (fun n => ‖(pn n).1 u - (pn n).1 v‖) atTop (𝓝 ‖p.1 u - p.1 v‖) :=
      (continuous_norm.tendsto _).comp ((hp1 u).sub (hp1 v))
    exact ge_of_tendsto hrhs (Eventually.of_forall fun n => (hmem n).chord u hu v hv)

/-- **The space of marked curves is a complete metric space.** -/
instance completeSpace_tube (c kmin delta : ℝ) : CompleteSpace (tube c kmin delta) :=
  haveI : IsClosed (tube c kmin delta) := isClosed_tube c kmin delta
  IsClosed.completeSpace_coe

/-! ### Members of the tube are ovals -/

/-- The arclength parametrization of a marked curve. -/
def ev (p : Data) : ℝ → ℂ := fun s => p.1 (s / perim p)

/-- The arclength parametrization is periodic with period the perimeter. -/
theorem periodic_ev {c kmin delta : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c kmin delta p) : Periodic (ev p) (perim p) := by
  have hLpos : 0 < perim p := perim_pos hc hp
  intro s
  have h : (s + perim p) / perim p = s / perim p + 1 := by field_simp
  simp only [ev, h]
  exact hp.periodic (s / perim p)

/-- Reparametrizing by arclength does not change the image of the curve.  Only
nondegeneracy of the perimeter is used. -/
theorem range_ev_of_perim_ne_zero {p : Data} (hp : perim p ≠ 0) :
    range (ev p) = range (⇑p.1) := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s / perim p, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨u * perim p, ?_⟩
    simp only [ev]
    rw [mul_div_assoc, div_self hp, mul_one]

/-- Reparametrizing by arclength does not change the image of the curve. -/
theorem range_ev {c kmin delta : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c kmin delta p) : range (ev p) = range (⇑p.1) :=
  range_ev_of_perim_ne_zero (ne_of_gt (perim_pos hc hp))

/-- **Every member of the tube is an oval.**  Reparametrized by arclength, a
marked curve of the tube is a closed embedded curve of unit speed and positive
curvature, of period its perimeter. -/
theorem isOval_ev {c kmin delta : ℝ} (hc : 0 < c) (hkmin : 0 < kmin) (hdelta : 0 < delta)
    {p : Data} (hp : IsTubeMember c kmin delta p) :
    MainTheoremConditional.IsOval (ev p) := by
  set L : ℝ := perim p with hL
  have hLpos : 0 < L := perim_pos hc hp
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- the derivative of the reparametrization
  have hinner : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s / L) (1 / L) s := by
    intro s
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id s).div_const L
  have hev : ∀ s, HasDerivAt (ev p) (p.2.1 (s / L) / L) s := by
    intro s
    have h := (hp.hasDerivAt_curve (s / L)).scomp s (hinner s)
    simpa [ev, hL, Function.comp, div_eq_mul_inv, one_div, smul_eq_mul, mul_comm] using h
  set tau : ℝ → ℂ := fun s => p.2.1 (s / L) / L with htaudef
  set D : ℝ → ℂ := fun s => p.2.2 (s / L) / (L ^ 2) with hDdef
  have hDderiv : ∀ s, HasDerivAt tau (D s) s := by
    intro s
    have h0 := (hp.hasDerivAt_vel (s / L)).scomp s (hinner s)
    have h := h0.div_const L
    simpa [htaudef, hDdef, Function.comp, div_eq_mul_inv, one_div, smul_eq_mul, sq, mul_comm,
      mul_assoc, mul_left_comm] using h
  have hnorm : ∀ s, ‖tau s‖ = 1 := by
    intro s
    rw [htaudef]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
    rw [norm_vel_eq_perim hp, ← hL]
    field_simp
  have hDcont : Continuous D := by
    have h : Continuous fun s : ℝ => p.2.2 (s / L) :=
      p.2.2.continuous.comp (continuous_id.div_const L)
    exact h.div_const _
  -- the curvature in arclength
  have hcurv : ∀ s, 0 < ((starRingEnd ℂ) (tau s) * D s).im := by
    intro s
    have hkey : (starRingEnd ℂ) (tau s) * D s
        = ((starRingEnd ℂ) (p.2.1 (s / L)) * p.2.2 (s / L)) / ((L ^ 3 : ℝ) : ℂ) := by
      rw [htaudef, hDdef]
      simp only [map_div₀, Complex.conj_ofReal]
      push_cast
      field_simp
    rw [hkey, Complex.div_ofReal_im]
    have hb := hp.curv_lb (s / L)
    rw [norm_vel_eq_perim hp, ← hL] at hb
    have hL3 : 0 < L ^ 3 := by positivity
    have : 0 < kmin * L ^ 3 := by positivity
    exact div_pos (lt_of_lt_of_le this hb) hL3
  obtain ⟨theta, hthetaderiv, hthetaexp⟩ := exists_angle hnorm hDderiv hDcont
  refine ⟨L, hLpos, ?_, ?_, theta, ?_, _, hthetaderiv, hcurv⟩
  · -- periodicity
    exact periodic_ev hc hp
  · -- injectivity on a period
    intro s hs t ht hst
    have hsmem : s / L ∈ Ico (0 : ℝ) 1 := by
      rcases hs with ⟨h0, h1⟩
      constructor
      · positivity
      · rw [div_lt_one hLpos]; exact h1
    have htmem : t / L ∈ Ico (0 : ℝ) 1 := by
      rcases ht with ⟨h0, h1⟩
      constructor
      · positivity
      · rw [div_lt_one hLpos]; exact h1
    have hzero : ‖p.1 (s / L) - p.1 (t / L)‖ = 0 := by
      simp only [ev] at hst
      rw [← hL] at hst
      rw [hst]
      simp
    have hchord := hp.chord (s / L) (Ico_subset_Icc_self hsmem) (t / L)
      (Ico_subset_Icc_self htmem)
    rw [hzero] at hchord
    have hcz : cyc (s / L) (t / L) ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      nlinarith
    have := cyc_eq_zero_iff hsmem htmem hcz
    field_simp at this
    exact this
  · -- unit speed with tangent angle `theta`
    intro s
    have h := hev s
    rw [hthetaexp s]
    simpa [htaudef, ← hL] using h

end MarkedSpace
