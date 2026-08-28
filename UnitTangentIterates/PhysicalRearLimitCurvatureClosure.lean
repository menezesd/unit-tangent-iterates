import UnitTangentIterates.CurvatureFromMarkedDistance
import UnitTangentIterates.PhysicalRearLimitKinematicClosure
import UnitTangentIterates.TubeHarnackStrictness

/-!
# Uniform curvature closure for marked pullback limits

Convergence in the marked `Data` metric already implies uniform convergence of
normalized curvature on a fixed positive-speed tube.  Thus curvature
convergence is not an extra topology assumption in the physical rear limit.
-/

noncomputable section

open Filter Topology MarkedSpace

namespace PathMetric

open CurvatureFromMarkedDistance
open NormalizedSteeringPhysicalRescaling

/-- Intrinsic normalized curvature is continuous in its parameter on a
positive-speed marked tube member. -/
theorem continuous_dataCurv_of_tube
    {c kmin dlt : ℝ} {p : Data} (hc : 0 < c)
    (hp : IsTubeMember c kmin dlt p) : Continuous (dataCurv p) := by
  have hvel : Continuous fun t => p.2.1 t := p.2.1.continuous
  have hacc : Continuous fun t => p.2.2 t := p.2.2.continuous
  have hnum : Continuous fun t =>
      ((starRingEnd ℂ) (p.2.1 t) * p.2.2 t).im :=
    Complex.continuous_im.comp ((Complex.continuous_conj.comp hvel).mul hacc)
  have hden : Continuous fun t => ‖p.2.1 t‖ ^ 3 := hvel.norm.pow 3
  have hden_ne : ∀ t, ‖p.2.1 t‖ ^ 3 ≠ 0 := by
    intro t
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hc (hp.speed_lb t)))
  exact hnum.div hden hden_ne

/-- The perimeter coordinate is continuous for marked `Data` convergence. -/
theorem tendsto_perim_of_marked_tendsto
    {P : ℕ → Data} {p : Data} (hP : Tendsto P atTop (nhds p)) :
    Tendsto (fun n => perim (P n)) atTop (nhds (perim p)) := by
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hP eps heps
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact (abs_perim_sub_le_dist (P n) p).trans_lt (hN n hn)

/-- Marked convergence inside a common positive-speed tube gives uniform
convergence of `dataCurv`.  Eventual uniform velocity and acceleration bounds
come directly from the product sup metric; the curvature quotient is then
controlled by `CurvatureFromMarkedDistance.abs_dataCurv_sub_le`. -/
theorem tendstoUniformly_dataCurv_of_marked_tendsto
    {P : ℕ → Data} {p : Data} {c kmin dlt : ℝ}
    (hc : 0 < c) (hP : Tendsto P atTop (nhds p))
    (hPmem : ∀ n, IsTubeMember c kmin dlt (P n))
    (hpmem : IsTubeMember c kmin dlt p) :
    TendstoUniformly (fun n u => dataCurv (P n) u) (dataCurv p) atTop := by
  let Vb : ℝ := ‖p.2.1‖ + 1
  let Ab : ℝ := ‖p.2.2‖ + 1
  let C : ℝ := curvLip c Vb Ab
  have hdist : Tendsto (fun n => dist (P n) p) atTop (nhds 0) := by
    simpa using (tendsto_iff_dist_tendsto_zero.mp hP)
  have hscaled : Tendsto (fun n => C * dist (P n) p) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hdist
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have hsmall : ∀ᶠ n in atTop, dist (P n) p < 1 :=
    hdist.eventually (eventually_lt_nhds zero_lt_one)
  have hcurvsmall : ∀ᶠ n in atTop, C * dist (P n) p < eps :=
    hscaled.eventually (eventually_lt_nhds heps)
  filter_upwards [hsmall, hcurvsmall] with n hn hnC
  intro u
  have hpV : ‖p.2.1 u‖ ≤ Vb := by
    dsimp [Vb]
    exact (BoundedContinuousFunction.norm_coe_le_norm (p.2.1) u).trans (by linarith)
  have hpA : ‖p.2.2 u‖ ≤ Ab := by
    dsimp [Ab]
    exact (BoundedContinuousFunction.norm_coe_le_norm (p.2.2) u).trans (by linarith)
  have hPV : ‖(P n).2.1 u‖ ≤ Vb := by
    calc
      ‖(P n).2.1 u‖ ≤ ‖p.2.1 u‖ + ‖(P n).2.1 u - p.2.1 u‖ := by
        simpa [add_comm] using norm_le_norm_add_norm_sub' ((P n).2.1 u) (p.2.1 u)
      _ ≤ ‖p.2.1 u‖ + dist (P n) p :=
        add_le_add le_rfl (dist_vel_apply_le (P n) p u)
      _ ≤ Vb := by
        dsimp [Vb]
        simpa [add_comm] using (add_lt_add_left hn ‖p.2.1 u‖).le.trans
          (add_le_add_right (BoundedContinuousFunction.norm_coe_le_norm (p.2.1) u) 1)
  have hacc : ‖(P n).2.2 u - p.2.2 u‖ ≤ dist (P n) p := by
    have h1 : dist ((P n).2.2 u) (p.2.2 u) ≤ dist (P n).2.2 p.2.2 :=
      BoundedContinuousFunction.dist_coe_le_dist u
    have h2 : dist (P n).2.2 p.2.2 ≤ dist (P n).2 p.2 := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    have h3 : dist (P n).2 p.2 ≤ dist (P n) p := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    rw [← dist_eq_norm]
    exact h1.trans (h2.trans h3)
  have hPA : ‖(P n).2.2 u‖ ≤ Ab := by
    calc
      ‖(P n).2.2 u‖ ≤ ‖p.2.2 u‖ + ‖(P n).2.2 u - p.2.2 u‖ := by
        simpa [add_comm] using norm_le_norm_add_norm_sub' ((P n).2.2 u) (p.2.2 u)
      _ ≤ ‖p.2.2 u‖ + dist (P n) p :=
        add_le_add le_rfl hacc
      _ ≤ Ab := by
        dsimp [Ab]
        simpa [add_comm] using (add_lt_add_left hn ‖p.2.2 u‖).le.trans
          (add_le_add_right (BoundedContinuousFunction.norm_coe_le_norm (p.2.2) u) 1)
  have hcurv := abs_dataCurv_sub_le hc
    ((hPmem n).speed_lb u) (hpmem.speed_lb u) hPV hpV hPA hpA
  simpa [Real.dist_eq, abs_sub_comm] using hcurv.trans_lt hnC

/-- The physical curvature stored by a selected-rear kinematic witness is not
an independent field: its Frenet presentation identifies it with the
intrinsic curvature of the marked front, at the physical-to-normalized
parameter `s / perim front`. -/
theorem PhysicalRearLimitKinematics.curvaturePhys_eq_dataCurv
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front) (s : ℝ) :
    curvaturePhys K.steering (perim front) s =
      dataCurv front (s / perim front) := by
  let L := perim front
  change curvaturePhys K.steering L s = dataCurv front (s / L)
  have hL : 0 < L := perim_pos hc hfront
  have hLn : L ≠ 0 := ne_of_gt hL
  have hinner : ∀ x : ℝ, HasDerivAt (fun t : ℝ => t / L) (1 / L) x := by
    intro x
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id x).div_const L
  have hvel : ∀ x, HasDerivAt (ev front)
      (front.2.1 (x / L) / L) x := by
    intro x
    have h := (hfront.hasDerivAt_curve (x / L)).scomp x (hinner x)
    simpa [ev, L, Function.comp, div_eq_mul_inv, one_div,
      smul_eq_mul, mul_comm] using h
  have htangent : ∀ x, front.2.1 (x / L) / L =
      Complex.exp (Complex.I *
        (thetaPhys K.steering L K.theta0 x : ℂ)) := fun x =>
    (hvel x).unique (K.front_frenet x)
  have hacc : HasDerivAt (fun t => front.2.1 (t / L) / L)
      (front.2.2 (s / L) / (L ^ 2)) s := by
    have h0 := (hfront.hasDerivAt_vel (s / L)).scomp s (hinner s)
    have h1 := h0.div_const L
    simpa [Function.comp, div_eq_mul_inv, one_div, smul_eq_mul, sq,
      mul_comm, mul_assoc, mul_left_comm] using h1
  have hexp : HasDerivAt
      (fun t => Complex.exp (Complex.I *
        (thetaPhys K.steering L K.theta0 t : ℂ)))
      (Complex.exp (Complex.I *
          (thetaPhys K.steering L K.theta0 s : ℂ)) *
        (Complex.I * (curvaturePhys K.steering L s : ℂ))) s := by
    have hi := ((hasDerivAt_thetaPhys (P := L) (theta0 := K.theta0)
      K.steering K.curvature_continuous s).ofReal_comp).const_mul Complex.I
    simpa [mul_comm, mul_assoc] using hi.cexp
  have haccEq : front.2.2 (s / L) / (L ^ 2) =
      Complex.exp (Complex.I *
          (thetaPhys K.steering L K.theta0 s : ℂ)) *
        (Complex.I * (curvaturePhys K.steering L s : ℂ)) := by
    apply hacc.unique
    have hfun : (fun t : ℝ => front.2.1 (t / L) / L) =
        fun t => Complex.exp (Complex.I *
          (thetaPhys K.steering L K.theta0 t : ℂ)) := funext htangent
    rw [hfun]
    exact hexp
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hLn
  have hvelEq : front.2.1 (s / L) = (L : ℂ) *
      Complex.exp (Complex.I *
        (thetaPhys K.steering L K.theta0 s : ℂ)) := by
    rw [← htangent s]
    field_simp
  have haccMul : front.2.2 (s / L) = ((L : ℂ) ^ 2) *
      (Complex.exp (Complex.I *
          (thetaPhys K.steering L K.theta0 s : ℂ)) *
        (Complex.I * (curvaturePhys K.steering L s : ℂ))) := by
    rw [← haccEq]
    field_simp
  have hce : (starRingEnd ℂ) (Complex.exp (Complex.I *
        (thetaPhys K.steering L K.theta0 s : ℂ))) *
      Complex.exp (Complex.I *
        (thetaPhys K.steering L K.theta0 s : ℂ)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp
  have hVA : (starRingEnd ℂ) (front.2.1 (s / L)) * front.2.2 (s / L) =
      ((L ^ 3 * curvaturePhys K.steering L s : ℝ) : ℂ) * Complex.I := by
    rw [hvelEq, haccMul, map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination ((L : ℂ) ^ 3 *
      (curvaturePhys K.steering L s : ℂ) * Complex.I) * hce
  have hnorm : ‖front.2.1 (s / L)‖ = L := by
    rw [hvelEq, norm_mul]
    simp [abs_of_pos hL]
  rw [dataCurv, hVA, hnorm]
  simp only [Complex.mul_I_im, Complex.ofReal_re]
  field_simp

/-- In normalized period-one coordinates the steering equation is forced
directly by the intrinsic marked curvature, with the physical perimeter as
coefficient.  This is the form that supplies equicontinuity in the compactness
argument. -/
theorem PhysicalRearLimitKinematics.normalized_steering
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front) (u : ℝ) :
    HasDerivAt K.steering.delta
      (perim front *
        (dataCurv front u - Real.sin (K.steering.delta u))) u := by
  have hP : 0 < perim front := perim_pos hc hfront
  have hid := K.curvaturePhys_eq_dataCurv hc hfront (perim front * u)
  have harg : perim front * u / perim front = u := by
    field_simp [ne_of_gt hP]
  have hK : K.steering.K u = perim front * dataCurv front u -
      (perim front - 1) * Real.sin (K.steering.delta u) := by
    simp only [curvaturePhys, deltaPhys, harg] at hid
    apply (eq_sub_iff_add_eq).2
    field_simp [ne_of_gt hP] at hid
    linarith
  convert K.steering.steering u using 1
  rw [hK]
  ring

/-- Fundamental-theorem form of the intrinsic normalized steering equation.
This is the finite-stage identity used when passing to an Arzela--Ascoli
limit; no convergence of steering derivatives is needed. -/
theorem PhysicalRearLimitKinematics.normalized_steering_integral_identity
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front) (u v : ℝ) :
    K.steering.delta v - K.steering.delta u =
      ∫ t in u..v, perim front *
        (dataCurv front t - Real.sin (K.steering.delta t)) := by
  let rhs : ℝ → ℝ := fun t => perim front *
    (dataCurv front t - Real.sin (K.steering.delta t))
  have hdeltaDiff : Differentiable ℝ K.steering.delta :=
    fun t => (K.normalized_steering hc hfront t).differentiableAt
  have hderiv : deriv K.steering.delta = rhs := by
    funext t
    exact (K.normalized_steering hc hfront t).deriv
  have hvel : Continuous fun t => front.2.1 t := front.2.1.continuous
  have hacc : Continuous fun t => front.2.2 t := front.2.2.continuous
  have hnum : Continuous fun t =>
      ((starRingEnd ℂ) (front.2.1 t) * front.2.2 t).im :=
    Complex.continuous_im.comp ((Complex.continuous_conj.comp hvel).mul hacc)
  have hden : Continuous fun t => ‖front.2.1 t‖ ^ 3 := hvel.norm.pow 3
  have hden_ne : ∀ t, ‖front.2.1 t‖ ^ 3 ≠ 0 := by
    intro t
    apply pow_ne_zero
    exact ne_of_gt (lt_of_lt_of_le hc (hfront.speed_lb t))
  have hcurv : Continuous (dataCurv front) := by
    exact hnum.div hden hden_ne
  have hdeltaCont : Continuous K.steering.delta := hdeltaDiff.continuous
  have hrhs : Continuous rhs := by
    dsimp [rhs]
    exact continuous_const.mul
      (hcurv.sub (Real.continuous_sin.comp hdeltaCont))
  have hi := intervalIntegral.integral_deriv_eq_sub'
    (a := u) (b := v) (f' := rhs) K.steering.delta hderiv
    (fun t _ => hdeltaDiff t) hrhs.continuousOn
  simpa [rhs] using hi.symm

/-- Uniform perimeter and intrinsic-curvature bounds give the common
Lipschitz modulus for normalized steering lifts used by Arzela--Ascoli. -/
theorem PhysicalRearLimitKinematics.normalizedSteering_lipschitz
    {kh c dlt C Pmax : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front)
    (hC : 0 ≤ C) (hPmax : perim front ≤ Pmax)
    (hcurv : ∀ u, |dataCurv front u| ≤ C) :
    LipschitzWith (Real.toNNReal (Pmax * (C + 1))) K.steering.delta := by
  have hP : 0 < perim front := perim_pos hc hfront
  have hPmax0 : 0 ≤ Pmax := hP.le.trans hPmax
  have hB0 : 0 ≤ Pmax * (C + 1) := mul_nonneg hPmax0 (by linarith)
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun u => (K.normalized_steering hc hfront u).differentiableAt) (fun u => ?_)
  rw [(K.normalized_steering hc hfront u).deriv, ← NNReal.coe_le_coe,
    coe_nnnorm, Real.coe_toNNReal _ hB0, Real.norm_eq_abs, abs_mul,
    abs_of_pos hP]
  calc
    perim front * |dataCurv front u - Real.sin (K.steering.delta u)|
        ≤ perim front * (|dataCurv front u| + |Real.sin (K.steering.delta u)|) := by
          gcongr
          exact abs_sub _ _
    _ ≤ perim front * (C + 1) := by
      gcongr
      exact hcurv u
      exact Real.abs_sin_le_one _
    _ ≤ Pmax * (C + 1) := by
      exact mul_le_mul_of_nonneg_right hPmax (by linarith)

/-- Restriction of a normalized steering lift to one compact period. -/
def steeringOnUnit {kh : ℝ}
    (d : NormalizedSelectedRearClosure.SteeringData kh) :
    BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun u => d.delta u.1,
      (Differentiable.continuous fun x => (d.steering x).differentiableAt).comp
        continuous_subtype_val⟩

@[simp] theorem steeringOnUnit_apply {kh : ℝ}
    (d : NormalizedSelectedRearClosure.SteeringData kh)
    (u : Set.Icc (0 : ℝ) 1) : steeringOnUnit d u = d.delta u.1 := rfl

/-- Arzela--Ascoli extraction for normalized selected steering lifts.  The
selected strip supplies a common compact range, and a common Lipschitz bound
supplies equicontinuity.  Convergence is in the sup metric on one full period. -/
theorem exists_uniformSteering_subseq
    {kh : ℝ} {C : NNReal}
    (d : ℕ → NormalizedSelectedRearClosure.SteeringData kh)
    (hLip : ∀ n, LipschitzWith C (d n).delta) :
    ∃ deltaUnit : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ,
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        Tendsto (fun n => steeringOnUnit (d (phi n))) atTop (nhds deltaUnit) ∧
        (∀ u, deltaUnit u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh)) ∧
        deltaUnit ⟨1, by norm_num⟩ = deltaUnit ⟨0, by norm_num⟩ := by
  let f : ℕ → BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ := fun n => steeringOnUnit (d n)
  let A : Set (BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) := Set.range f
  have hLip' : ∀ n, LipschitzWith C (f n) := by
    intro n
    simpa only [mul_one, f, steeringOnUnit_apply] using
      (hLip n).comp (LipschitzWith.subtype_val _)
  have hEq : Equicontinuous ((↑) : A → Set.Icc (0 : ℝ) 1 → ℝ) := by
    let pick : A → ℕ := fun g => Classical.choose g.2
    have hpick : ∀ g : A, f (pick g) = g.1 := fun g => Classical.choose_spec g.2
    have hbase :=
      (LipschitzWith.uniformEquicontinuous (fun n => ⇑(f n)) C hLip').equicontinuous.comp pick
    convert hbase using 1
    funext g u
    change g.1 u = f (pick g) u
    rw [hpick g]
  have hRange : ∀ (g : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) (u : Set.Icc (0 : ℝ) 1),
      g ∈ A → g u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh) := by
    intro g u hg
    rcases hg with ⟨n, rfl⟩
    exact (d n).delta_mem u.1
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli _ isCompact_Icc A hRange hEq
  obtain ⟨deltaUnit, -, phi, hphi, hconv⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  have hconv' : Tendsto (fun n => steeringOnUnit (d (phi n))) atTop
      (nhds deltaUnit) := by simpa [f] using hconv
  have hstrip : ∀ u, deltaUnit u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh) := by
    intro u
    have heval := (continuous_eval_const u).continuousAt.tendsto.comp hconv'
    exact isClosed_Icc.mem_of_tendsto heval
      (Eventually.of_forall fun n => (d (phi n)).delta_mem u.1)
  let u0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let u1 : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have h0 := (continuous_eval_const u0).continuousAt.tendsto.comp hconv'
  have h1 := (continuous_eval_const u1).continuousAt.tendsto.comp hconv'
  have heq : (fun n => steeringOnUnit (d (phi n)) u1) =
      fun n => steeringOnUnit (d (phi n)) u0 := by
    funext n
    change (d (phi n)).delta 1 = (d (phi n)).delta 0
    simpa using (d (phi n)).delta_periodic 0
  have hend : deltaUnit u1 = deltaUnit u0 := by
    apply tendsto_nhds_unique h1
    have h0' : Tendsto (fun n => steeringOnUnit (d (phi n)) u0) atTop
        (nhds (deltaUnit u0)) := by simpa [Function.comp_def] using h0
    change Tendsto (fun n => steeringOnUnit (d (phi n)) u1) atTop
      (nhds (deltaUnit u0))
    rw [heq]
    exact h0'
  exact ⟨deltaUnit, phi, hphi, hconv', hstrip, hend⟩

/-- Periodic extension of a continuous function on the closed unit interval.
The value is read at the canonical representative in `[0,1)`. -/
def unitPeriodicExtension
    (f : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) (x : ℝ) : ℝ :=
  f ⟨toIcoMod one_pos 0 x,
    Set.Ico_subset_Icc_self (by simpa using toIcoMod_mem_Ico one_pos 0 x)⟩

@[simp] theorem unitPeriodicExtension_apply_Ico
    (f : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ)
    {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    unitPeriodicExtension f x = f ⟨x, Set.Ico_subset_Icc_self hx⟩ := by
  unfold unitPeriodicExtension
  congr 2
  exact (toIcoMod_eq_self one_pos).mpr (by simpa using hx)

theorem unitPeriodicExtension_periodic
    (f : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) :
    Function.Periodic (unitPeriodicExtension f) 1 := by
  intro x
  unfold unitPeriodicExtension
  congr 2
  exact (toIcoMod_periodic one_pos 0 x)

/-- Endpoint compatibility removes the only seam in the canonical periodic
extension. -/
theorem continuous_unitPeriodicExtension
    (f : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ)
    (hend : f ⟨1, by norm_num⟩ = f ⟨0, by norm_num⟩) :
    Continuous (unitPeriodicExtension f) := by
  let g : ℝ → ℝ := fun x => f (Set.projIcc 0 1 zero_le_one x)
  have hg : Continuous g := f.continuous.comp continuous_projIcc
  have hgend : g 0 = g 1 := by
    dsimp [g]
    simpa [Set.projIcc_left, Set.projIcc_right] using hend.symm
  let G : AddCircle (1 : ℝ) → ℝ := AddCircle.liftIco (1 : ℝ) 0 g
  have hG : Continuous G := AddCircle.liftIco_zero_continuous hgend hg.continuousOn
  have heq : unitPeriodicExtension f =
      fun x : ℝ => G (x : AddCircle (1 : ℝ)) := by
    funext x
    unfold unitPeriodicExtension G
    rw [show (x : AddCircle (1 : ℝ)) =
        ((toIcoMod (p := (1 : ℝ)) one_pos 0 x : ℝ) : AddCircle (1 : ℝ)) by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      rw [self_sub_toIcoMod]
      apply AddSubgroup.zsmul_mem_zmultiples]
    rw [AddCircle.liftIco_zero_coe_apply]
    · dsimp [g]
      rw [Set.projIcc_of_mem]
    · simpa using toIcoMod_mem_Ico one_pos 0 x
  rw [heq]
  exact hG.comp (AddCircle.continuous_mk' (1 : ℝ))

/-- Sup-metric convergence on one compact period upgrades to global uniform
convergence after canonical periodic extension. -/
theorem tendstoUniformly_unitPeriodicExtension
    {kh : ℝ}
    (d : ℕ → NormalizedSelectedRearClosure.SteeringData kh)
    (f : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ)
    (hconv : Tendsto (fun n => steeringOnUnit (d n)) atTop (nhds f)) :
    TendstoUniformly (fun n => (d n).delta) (unitPeriodicExtension f) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have hev := (Metric.tendsto_nhds.1 hconv) eps heps
  filter_upwards [hev] with n hn
  intro x
  let u : Set.Icc (0 : ℝ) 1 :=
    ⟨toIcoMod one_pos 0 x,
      Set.Ico_subset_Icc_self (by simpa using toIcoMod_mem_Ico one_pos 0 x)⟩
  have hrepr : (d n).delta x = (d n).delta u.1 := by
    have hmod := (toIcoMod_eq_iff one_pos).1
      (show toIcoMod one_pos 0 x = u.1 from rfl)
    obtain ⟨z, hz⟩ := hmod.2
    rw [hz]
    simpa using ((d n).delta_periodic.zsmul z u.1)
  rw [hrepr]
  change dist (f u) (steeringOnUnit (d n) u) < eps
  exact (BoundedContinuousFunction.dist_coe_le_dist u).trans_lt (by
    simpa [dist_comm] using hn)

/-- Cosine primitive in the normalized front parameter. -/
def normalizedCosinePrimitive (delta : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.cos (delta t)

/-- A uniform steering error on `[0,1]` gives the same uniform error for its
cosine primitive there. -/
theorem abs_normalizedCosinePrimitive_sub_le_on_unit
    {deltaN delta : ℝ → ℝ} {e x : ℝ}
    (hdeltaN : Continuous deltaN) (hdelta : Continuous delta)
    (he : 0 ≤ e)
    (hclose : ∀ t ∈ Set.Icc (0 : ℝ) 1, |deltaN t - delta t| ≤ e)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |normalizedCosinePrimitive deltaN x -
      normalizedCosinePrimitive delta x| ≤ e := by
  rw [normalizedCosinePrimitive, normalizedCosinePrimitive]
  have hint :
      (∫ t in (0 : ℝ)..x, Real.cos (deltaN t)) -
          ∫ t in (0 : ℝ)..x, Real.cos (delta t) =
        ∫ t in (0 : ℝ)..x, Real.cos (deltaN t) - Real.cos (delta t) := by
    simpa [Function.comp_apply] using (intervalIntegral.integral_sub
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      ((Real.continuous_cos.comp hdeltaN).intervalIntegrable 0 x)
      ((Real.continuous_cos.comp hdelta).intervalIntegrable 0 x)).symm
  rw [hint]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => Real.cos (deltaN t) - Real.cos (delta t))
    (C := e) (a := (0 : ℝ)) (b := x) (fun (t : ℝ) ht => by
      have ht' : t ∈ Set.Ioc (0 : ℝ) x := by
        simpa [Set.uIoc_of_le hx.1] using ht
      rw [Real.norm_eq_abs]
      exact (Real.abs_cos_sub_cos_le _ _).trans
        (hclose t ⟨ht'.1.le, ht'.2.trans hx.2⟩))
  rw [Real.norm_eq_abs, sub_zero] at hb
  calc
    |∫ t in (0 : ℝ)..x, Real.cos (deltaN t) - Real.cos (delta t)|
        ≤ e * |x| := by simpa using hb
    _ ≤ e := by
      have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
      simpa using mul_le_of_le_one_right he hxabs

/-- Uniform convergence of steering lifts passes to uniform convergence of
their cosine primitives on the normalized compact period. -/
theorem tendstoUniformlyOn_normalizedCosinePrimitive
    {deltaN : ℕ → ℝ → ℝ} {delta : ℝ → ℝ}
    (hdeltaN : ∀ n, Continuous (deltaN n)) (hdeltaC : Continuous delta)
    (hdelta : TendstoUniformly deltaN delta atTop) :
    TendstoUniformlyOn
      (fun n => normalizedCosinePrimitive (deltaN n))
      (normalizedCosinePrimitive delta) atTop (Set.Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have he2 : 0 < eps / 2 := half_pos heps
  have hev := (Metric.tendstoUniformly_iff.1 hdelta) (eps / 2) he2
  filter_upwards [hev] with n hn
  intro x hx
  rw [Real.dist_eq]
  have hb := abs_normalizedCosinePrimitive_sub_le_on_unit
    (hdeltaN n) hdeltaC he2.le
    (fun t ht => by
      have := hn t
      simpa [Real.dist_eq, abs_sub_comm] using this.le) hx
  rw [abs_sub_comm]
  exact hb.trans_lt (half_lt_self heps)

/-- The normalized rear-arclength primitive. -/
def unitRearPrimitive (delta : ℝ → ℝ) (x : ℝ) : ℝ :=
  normalizedCosinePrimitive delta x / normalizedCosinePrimitive delta 1

/-- The actual finite physical rear-arclength map, normalized to carry the
front and rear periods to the unit interval. -/
def PhysicalRearLimitKinematics.physicalUnitRearPrimitive
    {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front) (u : ℝ) : ℝ :=
  RearTrack.rearArclength
      (deltaPhys K.steering (perim front)) (perim front * u) /
    perim rear

/-- The stored finite physical inverse, rescaled from rear arclength and front
arclength to `[0,1]`. -/
def PhysicalRearLimitKinematics.physicalUnitRearInverse
    {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front) (x : ℝ) : ℝ :=
  K.sf (perim rear * x) / perim front

/-- The normalized finite physical inverse is a genuine right inverse and
maps the compact unit interval to itself. -/
theorem PhysicalRearLimitKinematics.physicalUnitRearInverse_data
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) :
    (∀ x, K.physicalUnitRearPrimitive
        (K.physicalUnitRearInverse x) = x) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        K.physicalUnitRearInverse x ∈ Set.Icc (0 : ℝ) 1) := by
  let P := perim front
  let Q := perim rear
  let dl := deltaPhys K.steering P
  have hP : 0 < P := perim_pos hc hfront
  have hQ : 0 < Q := perim_pos hc hrear
  have hdlC : Continuous dl := by
    dsimp [dl, deltaPhys]
    exact (Differentiable.continuous fun u =>
      (K.steering.steering u).differentiableAt).comp
        (continuous_id.div_const P)
  have hdl0 : ∀ s, 0 ≤ dl s := fun s => (deltaPhys_mem K.steering s).1
  have hdl1 : ∀ s, dl s ≤ Real.arcsin kh :=
    fun s => (deltaPhys_mem K.steering s).2
  have hcos0 : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcos : ∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (dl s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdl0 s) (hdl1 s)
  have hsfMono : StrictMono K.sf :=
    SelectedInverseRearOwn.sf_strictMono hcos0 hdlC hcos K.arclength_rightInverse
  have hsf0 : K.sf 0 = 0 := by
    have harcMono : StrictMono (RearTrack.rearArclength dl) :=
      RearTrack.strictMono_rearArclength hdlC hkh1 hkh0 hdl0 hdl1
    apply harcMono.injective
    simpa [dl, RearTrack.rearArclength] using K.arclength_rightInverse 0
  have hsfQ : K.sf Q = P := by
    have hleft : K.sf (RearTrack.rearArclength dl P) = P := by
      have harcMono : StrictMono (RearTrack.rearArclength dl) :=
        RearTrack.strictMono_rearArclength hdlC hkh1 hkh0 hdl0 hdl1
      apply harcMono.injective
      exact K.arclength_rightInverse _
    change K.sf (perim rear) = perim front
    rw [K.rear_perimeter]
    exact hleft
  constructor
  · intro x
    unfold physicalUnitRearPrimitive physicalUnitRearInverse
    change RearTrack.rearArclength dl
        (P * (K.sf (Q * x) / P)) / Q = x
    rw [show P * (K.sf (Q * x) / P) = K.sf (Q * x) by
      field_simp [ne_of_gt hP]]
    rw [K.arclength_rightInverse]
    field_simp [ne_of_gt hQ]
  · intro x hx
    unfold physicalUnitRearInverse
    change K.sf (Q * x) / P ∈ Set.Icc (0 : ℝ) 1
    have hQx0 : 0 ≤ Q * x := mul_nonneg hQ.le hx.1
    have hQxQ : Q * x ≤ Q := mul_le_of_le_one_right hQ.le hx.2
    have hsfLo : 0 ≤ K.sf (Q * x) := by
      rw [← hsf0]
      exact hsfMono.monotone hQx0
    have hsfHi : K.sf (Q * x) ≤ P := by
      rw [← hsfQ]
      exact hsfMono.monotone hQxQ
    exact ⟨div_nonneg hsfLo hP.le, (div_le_one hP).2 hsfHi⟩

/-- The physical normalized primitive is exactly the unit cosine quotient of
the normalized steering lift. -/
theorem PhysicalRearLimitKinematics.physicalUnitRearPrimitive_eq
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front) (u : ℝ) :
    K.physicalUnitRearPrimitive u = unitRearPrimitive K.steering.delta u := by
  have hP : 0 < perim front := perim_pos hc hfront
  have hP0 : perim front ≠ 0 := ne_of_gt hP
  unfold physicalUnitRearPrimitive unitRearPrimitive
  rw [K.rear_perimeter]
  unfold RearTrack.rearArclength deltaPhys normalizedCosinePrimitive
  rw [intervalIntegral.integral_comp_div (fun x => Real.cos (K.steering.delta x)) hP0,
    intervalIntegral.integral_comp_div (fun x => Real.cos (K.steering.delta x)) hP0]
  simp only [zero_div, mul_div_cancel_left₀ u hP0, div_self hP0]
  simp only [smul_eq_mul]
  exact mul_div_mul_left _ _ hP0

/-- Quantitative passage from an unnormalized primitive error to the
normalized primitive error.  This form keeps the exact denominators, so no
artificial common-period equality is assumed. -/
theorem abs_unitRearPrimitive_sub_le
    {deltaN delta : ℝ → ℝ} {e x : ℝ}
    (hN0 : normalizedCosinePrimitive deltaN 1 ≠ 0)
    (h0 : normalizedCosinePrimitive delta 1 ≠ 0)
    (hx : |normalizedCosinePrimitive deltaN x -
      normalizedCosinePrimitive delta x| ≤ e)
    (h1 : |normalizedCosinePrimitive deltaN 1 -
      normalizedCosinePrimitive delta 1| ≤ e) :
    |unitRearPrimitive deltaN x - unitRearPrimitive delta x| ≤
      e / |normalizedCosinePrimitive deltaN 1| +
      |normalizedCosinePrimitive delta x| * e /
        (|normalizedCosinePrimitive deltaN 1| *
          |normalizedCosinePrimitive delta 1|) := by
  have hdecomp :
      normalizedCosinePrimitive deltaN x /
          normalizedCosinePrimitive deltaN 1 -
        normalizedCosinePrimitive delta x /
          normalizedCosinePrimitive delta 1 =
      (normalizedCosinePrimitive deltaN x -
          normalizedCosinePrimitive delta x) /
          normalizedCosinePrimitive deltaN 1 +
        normalizedCosinePrimitive delta x *
          (normalizedCosinePrimitive delta 1 -
            normalizedCosinePrimitive deltaN 1) /
          (normalizedCosinePrimitive deltaN 1 *
            normalizedCosinePrimitive delta 1) := by
    field_simp [hN0, h0]
    ring
  rw [unitRearPrimitive, unitRearPrimitive, hdecomp]
  calc
    _ ≤
        |(normalizedCosinePrimitive deltaN x -
            normalizedCosinePrimitive delta x) /
            normalizedCosinePrimitive deltaN 1| +
          |normalizedCosinePrimitive delta x *
            (normalizedCosinePrimitive delta 1 -
              normalizedCosinePrimitive deltaN 1) /
            (normalizedCosinePrimitive deltaN 1 *
              normalizedCosinePrimitive delta 1)| := abs_add_le _ _
    _ = |normalizedCosinePrimitive deltaN x -
            normalizedCosinePrimitive delta x| /
            |normalizedCosinePrimitive deltaN 1| +
          |normalizedCosinePrimitive delta x| *
            |normalizedCosinePrimitive delta 1 -
              normalizedCosinePrimitive deltaN 1| /
            (|normalizedCosinePrimitive deltaN 1| *
              |normalizedCosinePrimitive delta 1|) := by
        rw [abs_div, abs_div, abs_mul, abs_mul]
    _ ≤ _ := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right hx (abs_nonneg _)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa [abs_sub_comm] using h1)
            (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Compact-domain version of monotone inverse stability.  This is the honest
estimate for normalized rear-arclength maps `[0,1] -> [0,1]`; it does not
require an impossible global bound when the unnormalized period drifts. -/
theorem abs_rightInverse_sub_le_on_unit
    {A AN sf sfN : ℝ → ℝ} {m e x : ℝ}
    (hm : 0 < m)
    (hslope : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      a ≤ b → m * (b - a) ≤ A b - A a)
    (hclose : ∀ y ∈ Set.Icc (0 : ℝ) 1, |AN y - A y| ≤ e)
    (hinv : A (sf x) = x) (hinvN : AN (sfN x) = x)
    (hsf : sf x ∈ Set.Icc (0 : ℝ) 1)
    (hsfN : sfN x ∈ Set.Icc (0 : ℝ) 1) :
    |sfN x - sf x| ≤ e / m := by
  have hA : |A (sfN x) - A (sf x)| ≤ e := by
    calc
      |A (sfN x) - A (sf x)| = |A (sfN x) - AN (sfN x)| := by
        rw [hinv, hinvN]
      _ = |AN (sfN x) - A (sfN x)| := abs_sub_comm _ _
      _ ≤ e := hclose _ hsfN
  have hmetric : m * |sfN x - sf x| ≤ |A (sfN x) - A (sf x)| := by
    rcases le_total (sfN x) (sf x) with hle | hle
    · have hs := hslope _ hsfN _ hsf hle
      have hmono : A (sfN x) ≤ A (sf x) := by nlinarith [hm]
      rw [abs_of_nonpos (sub_nonpos.mpr hle),
        abs_of_nonpos (sub_nonpos.mpr hmono)]
      nlinarith
    · have hs := hslope _ hsf _ hsfN hle
      have hmono : A (sf x) ≤ A (sfN x) := by nlinarith [hm]
      rw [abs_of_nonneg (sub_nonneg.mpr hle),
        abs_of_nonneg (sub_nonneg.mpr hmono)]
      nlinarith
  rw [le_div_iff₀ hm, mul_comm]
  exact hmetric.trans hA

/-- Uniform convergence of normalized primitives on `[0,1]`, together with a
common positive slope for the limit primitive, gives uniform convergence of
their right inverses on `[0,1]`. -/
theorem tendstoUniformlyOn_rightInverse_on_unit
    {AN : ℕ → ℝ → ℝ} {A : ℝ → ℝ}
    {sfN : ℕ → ℝ → ℝ} {sf : ℝ → ℝ} {m : ℝ}
    (hm : 0 < m)
    (hslope : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      a ≤ b → m * (b - a) ≤ A b - A a)
    (hA : TendstoUniformlyOn AN A atTop (Set.Icc (0 : ℝ) 1))
    (hinv : ∀ x ∈ Set.Icc (0 : ℝ) 1, A (sf x) = x)
    (hinvN : ∀ n x, x ∈ Set.Icc (0 : ℝ) 1 → AN n (sfN n x) = x)
    (hsf : ∀ x ∈ Set.Icc (0 : ℝ) 1, sf x ∈ Set.Icc (0 : ℝ) 1)
    (hsfN : ∀ n x, x ∈ Set.Icc (0 : ℝ) 1 →
      sfN n x ∈ Set.Icc (0 : ℝ) 1) :
    TendstoUniformlyOn sfN sf atTop (Set.Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  let e : ℝ := eps * m / 2
  have he : 0 < e := div_pos (mul_pos heps hm) (by norm_num)
  have hev := (Metric.tendstoUniformlyOn_iff.1 hA) e he
  filter_upwards [hev] with n hn
  intro x hx
  rw [Real.dist_eq]
  rw [abs_sub_comm]
  have hb := abs_rightInverse_sub_le_on_unit hm hslope
    (fun y hy => by
      have := hn y hy
      simpa [Real.dist_eq, abs_sub_comm] using this.le)
    (hinv x hx) (hinvN n x hx) (hsf x hx) (hsfN n x hx)
  calc
    |sfN n x - sf x| ≤ e / m := hb
    _ = eps / 2 := by dsimp [e]; field_simp
    _ < eps := half_lt_self heps

/-- A limiting steering solving the intrinsic normalized equation cannot
collapse to zero: that would force the curvature of a positive-speed closed
front to vanish identically. -/
theorem steering_nonzero_of_normalized_intrinsic_ode
    {c kmin dlt P : ℝ} {front : Data} {delta : ℝ → ℝ}
    (hc : 0 < c) (hfront : IsTubeMember c kmin dlt front)
    (hP : P = perim front)
    (hode : ∀ u, HasDerivAt delta
      (P * (dataCurv front u - Real.sin (delta u))) u) :
    ∃ u, delta u ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  obtain ⟨s, hs⟩ := UnconditionalAssembly.arcCurv_nonzero hc hfront
  have hPpos : 0 < P := hP.symm ▸ perim_pos hc hfront
  let u := s / P
  have hconst : HasDerivAt delta 0 u := by
    have hdelta : delta = fun _ => 0 := funext hzero
    rw [hdelta]
    exact hasDerivAt_const u 0
  have heq := (hode u).unique hconst
  have hcurv : dataCurv front u = 0 := by
    rw [hzero u, Real.sin_zero, sub_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_left (ne_of_gt hPpos)
  apply hs
  change dataCurv front (s / perim front) = 0
  simpa [u, hP] using hcurv

/-- Passing to an integral identity is enough to recover the limiting ODE;
no convergence of steering derivatives is required. -/
theorem hasDerivAt_of_integral_identity
    {delta force : ℝ → ℝ} (hforce : Continuous force)
    (hid : ∀ u, delta u = delta 0 + ∫ t in (0 : ℝ)..u, force t) :
    ∀ u, HasDerivAt delta (force u) u := by
  have hfun : delta = fun u => delta 0 + ∫ t in (0 : ℝ)..u, force t := funext hid
  intro u
  rw [hfun]
  exact (hforce.integral_hasStrictDerivAt (0 : ℝ) u).hasDerivAt.const_add (delta 0)

/-- Uniform limits preserve fundamental-theorem integral identities. -/
theorem integral_identity_of_tendstoUniformly
    {deltaN rhsN : ℕ → ℝ → ℝ} {delta rhs : ℝ → ℝ}
    (hdelta : TendstoUniformly deltaN delta atTop)
    (hrhs : TendstoUniformly rhsN rhs atTop)
    (hrhsN : ∀ n, Continuous (rhsN n)) (hrhsC : Continuous rhs)
    (hfinite : ∀ n u v, deltaN n v - deltaN n u =
      ∫ t in u..v, rhsN n t) :
    (∀ u v, delta v - delta u = ∫ t in u..v, rhs t) ∧
      (∀ u, HasDerivAt delta (rhs u) u) := by
  have hint : ∀ u v, Tendsto (fun n => ∫ t in u..v, rhsN n t) atTop
      (nhds (∫ t in u..v, rhs t)) := by
    intro u v
    apply Metric.tendsto_atTop.2
    intro eps heps
    let L : ℝ := |v - u|
    let eta : ℝ := eps / (L + 1)
    have hL0 : 0 ≤ L := abs_nonneg _
    have heta : 0 < eta := div_pos heps (by dsimp [L]; linarith)
    have hev := (Metric.tendstoUniformly_iff.1 hrhs eta heta)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hnN => ?_⟩
    have hn := hN n hnN
    rw [Real.dist_eq, ← intervalIntegral.integral_sub
      ((hrhsN n).intervalIntegrable u v) (hrhsC.intervalIntegrable u v)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => rhsN n t - rhs t) (C := eta) (a := u) (b := v)
      (fun t _ => by
        simpa [Real.norm_eq_abs, abs_sub_comm, Real.dist_eq] using (hn t).le)
    rw [Real.norm_eq_abs] at hb
    calc
      |∫ t in u..v, rhsN n t - rhs t| ≤ eta * L := by simpa [L] using hb
      _ < eta * (L + 1) := mul_lt_mul_of_pos_left (lt_add_one L) heta
      _ = eps := by dsimp [eta]; field_simp
  have hident : ∀ u v, delta v - delta u = ∫ t in u..v, rhs t := by
    intro u v
    have hl := (hdelta.tendsto_at v).sub (hdelta.tendsto_at u)
    have hr := hint u v
    have heq : (fun n => deltaN n v - deltaN n u) =
        fun n => ∫ t in u..v, rhsN n t := by
      funext n
      exact hfinite n u v
    have hr' : Tendsto (fun n => deltaN n v - deltaN n u) atTop
        (nhds (∫ t in u..v, rhs t)) := by rw [heq]; exact hr
    exact tendsto_nhds_unique hl hr'
  refine ⟨hident, ?_⟩
  apply hasDerivAt_of_integral_identity hrhsC
  intro u
  have h := hident 0 u
  simp only [sub_eq_iff_eq_add] at h
  simpa [add_comm] using h

/-- Marked front convergence and uniform convergence of the periodically
extended Arzela--Ascoli steering lifts pass the finite normalized steering
identities to the limit. -/
theorem normalized_steering_integral_identity_limit
    {kh c dlt : ℝ}
    {frontN rearN : ℕ → Data} {front : Data}
    (K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n))
    (hc : 0 < c)
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hfront : IsTubeMember c 0 dlt front)
    (hfrontConv : Tendsto frontN atTop (nhds front))
    {delta : ℝ → ℝ} (hdeltaC : Continuous delta)
    (hdelta : TendstoUniformly (fun n => (K n).steering.delta) delta atTop) :
    (∀ u v, delta v - delta u =
      ∫ t in u..v, perim front *
        (dataCurv front t - Real.sin (delta t))) ∧
    (∀ u, HasDerivAt delta
      (perim front * (dataCurv front u - Real.sin (delta u))) u) := by
  let rhsN : ℕ → ℝ → ℝ := fun n t => perim (frontN n) *
    (dataCurv (frontN n) t - Real.sin ((K n).steering.delta t))
  let rhs : ℝ → ℝ := fun t => perim front *
    (dataCurv front t - Real.sin (delta t))
  have hcurv : TendstoUniformly
      (fun n t => dataCurv (frontN n) t) (dataCurv front) atTop :=
    tendstoUniformly_dataCurv_of_marked_tendsto hc hfrontConv hfrontN hfront
  have hsin : TendstoUniformly
      (fun n t => Real.sin ((K n).steering.delta t))
      (fun t => Real.sin (delta t)) atTop := by
    exact Real.lipschitzWith_sin.uniformContinuous.comp_tendstoUniformly hdelta
  have hsub : TendstoUniformly
      (fun n t => dataCurv (frontN n) t -
        Real.sin ((K n).steering.delta t))
      (fun t => dataCurv front t - Real.sin (delta t)) atTop := by
    simpa only [Pi.sub_apply] using hcurv.sub hsin
  have hp := tendsto_perim_of_marked_tendsto hfrontConv
  have hrhs : TendstoUniformly rhsN rhs atTop := by
    have hc3 : 0 < c ^ 3 := pow_pos hc _
    let C : ℝ := ‖front.2.1‖ * ‖front.2.2‖ / c ^ 3
    have hC : 0 ≤ C := div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc3.le
    have hcurvBound : ∀ t, |dataCurv front t| ≤ C := by
      intro t
      have hv : 0 < ‖front.2.1 t‖ := lt_of_lt_of_le hc (hfront.speed_lb t)
      have hnum :
          |((starRingEnd ℂ) (front.2.1 t) * front.2.2 t).im| ≤
            ‖front.2.1‖ * ‖front.2.2‖ := by
        calc
          |((starRingEnd ℂ) (front.2.1 t) * front.2.2 t).im| ≤
              ‖(starRingEnd ℂ) (front.2.1 t) * front.2.2 t‖ :=
            Complex.abs_im_le_norm _
          _ = ‖front.2.1 t‖ * ‖front.2.2 t‖ := by
            rw [norm_mul, RCLike.norm_conj]
          _ ≤ ‖front.2.1‖ * ‖front.2.2‖ := by
            exact mul_le_mul
              (BoundedContinuousFunction.norm_coe_le_norm front.2.1 t)
              (BoundedContinuousFunction.norm_coe_le_norm front.2.2 t)
              (norm_nonneg _) (norm_nonneg _)
      have hden : c ^ 3 ≤ ‖front.2.1 t‖ ^ 3 := by
        gcongr
        exact hfront.speed_lb t
      unfold dataCurv
      rw [abs_div, abs_of_pos (pow_pos hv _)]
      change _ ≤ ‖front.2.1‖ * ‖front.2.2‖ / c ^ 3
      exact (div_le_div_iff₀ (pow_pos hv _) hc3).2
        (mul_le_mul hnum hden hc3.le
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    let M : ℝ := C + 1
    have hM : 0 < M := add_pos_of_nonneg_of_pos hC zero_lt_one
    let P : ℝ := |perim front| + 1
    have hP : 0 < P := add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
    rw [Metric.tendstoUniformly_iff]
    intro eps heps
    have heM : 0 < eps / (2 * M) := div_pos heps (mul_pos (by norm_num) hM)
    have heP : 0 < eps / (2 * P) := div_pos heps (mul_pos (by norm_num) hP)
    have hNsub := (Metric.tendstoUniformly_iff.1 hsub) (eps / (2 * P)) heP
    obtain ⟨Np, hNp⟩ := Metric.tendsto_atTop.1 hp (eps / (2 * M)) heM
    obtain ⟨Np1, hNp1⟩ := Metric.tendsto_atTop.1 hp 1 zero_lt_one
    have hNpEv : ∀ᶠ n in atTop,
        dist (perim (frontN n)) (perim front) < eps / (2 * M) :=
      eventually_atTop.2 ⟨Np, hNp⟩
    have hNp1Ev : ∀ᶠ n in atTop,
        dist (perim (frontN n)) (perim front) < 1 :=
      eventually_atTop.2 ⟨Np1, hNp1⟩
    filter_upwards [hNsub, hNpEv, hNp1Ev] with n hnsub hnp hnp1
    intro t
    have hq :
        |(dataCurv front t - Real.sin (delta t)) -
          (dataCurv (frontN n) t - Real.sin ((K n).steering.delta t))| <
            eps / (2 * P) := by
      rw [← Real.dist_eq]
      exact hnsub t
    have hp' : |perim front - perim (frontN n)| < eps / (2 * M) := by
      simpa [Real.dist_eq, abs_sub_comm] using hnp
    have hp1' : |perim (frontN n)| ≤ P := by
      have hd : |perim (frontN n) - perim front| < 1 := by
        simpa [Real.dist_eq] using hnp1
      calc
        |perim (frontN n)| = |(perim (frontN n) - perim front) + perim front| := by
          congr 1 <;> ring
        _ ≤ |perim (frontN n) - perim front| + |perim front| := abs_add_le _ _
        _ ≤ P := by dsimp [P]; linarith
    have hqBound : |dataCurv front t - Real.sin (delta t)| ≤ M := by
      calc
        |dataCurv front t - Real.sin (delta t)| ≤
            |dataCurv front t| + |Real.sin (delta t)| := abs_sub _ _
        _ ≤ C + 1 := add_le_add (hcurvBound t) (Real.abs_sin_le_one _)
        _ = M := rfl
    rw [Real.dist_eq]
    change |perim front * (dataCurv front t - Real.sin (delta t)) -
      perim (frontN n) *
        (dataCurv (frontN n) t - Real.sin ((K n).steering.delta t))| < eps
    calc
      _ = |perim (frontN n) *
              ((dataCurv front t - Real.sin (delta t)) -
                (dataCurv (frontN n) t - Real.sin ((K n).steering.delta t))) +
            (perim front - perim (frontN n)) *
              (dataCurv front t - Real.sin (delta t))| := by
          congr 1 <;> ring
      _ ≤ |perim (frontN n)| *
              |(dataCurv front t - Real.sin (delta t)) -
                (dataCurv (frontN n) t - Real.sin ((K n).steering.delta t))| +
            |perim front - perim (frontN n)| *
              |dataCurv front t - Real.sin (delta t)| := by
          simpa only [abs_mul] using abs_add_le
            (perim (frontN n) *
              ((dataCurv front t - Real.sin (delta t)) -
                (dataCurv (frontN n) t - Real.sin ((K n).steering.delta t))))
            ((perim front - perim (frontN n)) *
              (dataCurv front t - Real.sin (delta t)))
      _ < P * (eps / (2 * P)) + (eps / (2 * M)) * M := by
          exact add_lt_add
            (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hp1' (abs_nonneg _))
              (mul_lt_mul_of_pos_left hq hP))
            (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hqBound (abs_nonneg _))
              (mul_lt_mul_of_pos_right hp' hM))
      _ = eps := by field_simp; ring
  have hrhsN : ∀ n, Continuous (rhsN n) := by
    intro n
    have hd : Continuous (K n).steering.delta :=
      (Differentiable.continuous fun t => ((K n).steering.steering t).differentiableAt)
    dsimp [rhsN]
    exact continuous_const.mul
      ((continuous_dataCurv_of_tube hc (hfrontN n)).sub
        (Real.continuous_sin.comp hd))
  have hrhsC : Continuous rhs := by
    dsimp [rhs]
    exact continuous_const.mul
      ((continuous_dataCurv_of_tube hc hfront).sub
        (Real.continuous_sin.comp hdeltaC))
  apply integral_identity_of_tendstoUniformly hdelta hrhs hrhsN hrhsC
  intro n u v
  exact (K n).normalized_steering_integral_identity hc (hfrontN n) u v

/-- Direct compact-domain form of the limiting normalized steering equation. -/
theorem normalized_steering_integral_identity_limit_of_unit
    {kh c dlt : ℝ}
    {frontN rearN : ℕ → Data} {front : Data}
    (K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n))
    (hc : 0 < c)
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hfront : IsTubeMember c 0 dlt front)
    (hfrontConv : Tendsto frontN atTop (nhds front))
    (deltaUnit : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ)
    (hdeltaUnit : Tendsto
      (fun n => steeringOnUnit (K n).steering) atTop (nhds deltaUnit))
    (hend : deltaUnit ⟨1, by norm_num⟩ = deltaUnit ⟨0, by norm_num⟩) :
    (let delta := unitPeriodicExtension deltaUnit;
      (∀ u v, delta v - delta u =
        ∫ t in u..v, perim front *
          (dataCurv front t - Real.sin (delta t))) ∧
      (∀ u, HasDerivAt delta
        (perim front * (dataCurv front u - Real.sin (delta u))) u)) := by
  dsimp only
  apply normalized_steering_integral_identity_limit K hc hfrontN hfront hfrontConv
    (continuous_unitPeriodicExtension deltaUnit hend)
  exact tendstoUniformly_unitPeriodicExtension (fun n => (K n).steering)
    deltaUnit hdeltaUnit

/-! ### Intrinsic reconstruction of the limiting front data -/

/-- A periodic limit of normalized steering solutions determines its own
normalized curvature coefficient from the marked front.  This avoids carrying
the finite tangent phases through the compactness argument. -/
def intrinsicLimitSteeringData
    {kh c dlt : ℝ} {front : Data}
    (hfront : IsTubeMember c 0 dlt front)
    (delta : ℝ → ℝ) (hperiod : Function.Periodic delta 1)
    (hmem : ∀ u, delta u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh))
    (hode : ∀ u, HasDerivAt delta
      (perim front * (dataCurv front u - Real.sin (delta u))) u) :
    NormalizedSelectedRearClosure.SteeringData kh where
  K := fun u => perim front * dataCurv front u -
    (perim front - 1) * Real.sin (delta u)
  delta := delta
  K_periodic := by
    intro u
    simp only [MarkedSpace.periodic_dataCurv hfront u, hperiod u]
  delta_periodic := hperiod
  delta_mem := hmem
  steering := by
    intro u
    convert hode u using 1
    ring

@[simp] theorem intrinsicLimitSteeringData_delta
    {kh c dlt : ℝ} {front : Data}
    (hfront : IsTubeMember c 0 dlt front)
    (delta : ℝ → ℝ) (hperiod : Function.Periodic delta 1)
    (hmem : ∀ u, delta u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh))
    (hode : ∀ u, HasDerivAt delta
      (perim front * (dataCurv front u - Real.sin (delta u))) u) (u : ℝ) :
    (intrinsicLimitSteeringData hfront delta hperiod hmem hode).delta u = delta u := rfl

/-- The reconstructed normalized coefficient is continuous. -/
theorem continuous_intrinsicLimitSteeringData_K
    {kh c dlt : ℝ} {front : Data}
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front)
    (delta : ℝ → ℝ) (hperiod : Function.Periodic delta 1)
    (hmem : ∀ u, delta u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh))
    (hode : ∀ u, HasDerivAt delta
      (perim front * (dataCurv front u - Real.sin (delta u))) u) :
    Continuous (intrinsicLimitSteeringData hfront delta hperiod hmem hode).K := by
  have hdelta : Continuous delta :=
    Differentiable.continuous fun u => (hode u).differentiableAt
  dsimp [intrinsicLimitSteeringData]
  exact continuous_const.mul (continuous_dataCurv_of_tube hc hfront) |>.sub
    (continuous_const.mul (Real.continuous_sin.comp hdelta))

/-- Physical rescaling of the reconstructed coefficient recovers exactly the
intrinsic curvature of the marked front. -/
theorem intrinsicLimitSteeringData_curvaturePhys
    {kh c dlt : ℝ} {front : Data}
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front)
    (delta : ℝ → ℝ) (hperiod : Function.Periodic delta 1)
    (hmem : ∀ u, delta u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh))
    (hode : ∀ u, HasDerivAt delta
      (perim front * (dataCurv front u - Real.sin (delta u))) u)
    (s : ℝ) :
    curvaturePhys (intrinsicLimitSteeringData hfront delta hperiod hmem hode)
      (perim front) s = dataCurv front (s / perim front) := by
  have hP : perim front ≠ 0 := ne_of_gt (perim_pos hc hfront)
  unfold curvaturePhys intrinsicLimitSteeringData
  dsimp
  field_simp [hP]
  ring

/-- The limiting front Frenet phase is reconstructed from the marked front
itself.  Neither a convergent sequence of finite phases nor a choice of
complex argument is needed. -/
theorem exists_intrinsicLimitFrontFrenet
    {kh c dlt : ℝ} {front : Data}
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front)
    (delta : ℝ → ℝ) (hperiod : Function.Periodic delta 1)
    (hmem : ∀ u, delta u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh))
    (hode : ∀ u, HasDerivAt delta
      (perim front * (dataCurv front u - Real.sin (delta u))) u) :
    ∃ theta0 : ℝ,
      let d := intrinsicLimitSteeringData hfront delta hperiod hmem hode
      Continuous d.K ∧
      ∀ s, HasDerivAt (ev front)
        (Complex.exp (Complex.I *
          (thetaPhys d (perim front) theta0 s : ℂ))) s := by
  obtain ⟨theta, hcurve, htheta⟩ := MarkedSpace.exists_arclength_angle hc hfront
  let d := intrinsicLimitSteeringData hfront delta hperiod hmem hode
  let theta0 := theta 0
  have hdC : Continuous d.K := by
    simpa [d] using continuous_intrinsicLimitSteeringData_K hc hfront delta
      hperiod hmem hode
  have hcurv : ∀ s, curvaturePhys d (perim front) s =
      dataCurv front (s / perim front) := by
    intro s
    simpa [d] using intrinsicLimitSteeringData_curvaturePhys hc hfront delta
      hperiod hmem hode s
  have hangle : ∀ s, thetaPhys d (perim front) theta0 s = theta s := by
    intro s
    have hz : ∀ x, HasDerivAt
        (fun y => thetaPhys d (perim front) theta0 y - theta y) 0 x := by
      intro x
      simpa [hcurv x] using
        (hasDerivAt_thetaPhys (P := perim front) (theta0 := theta0) d hdC x).sub
          (htheta x)
    have hconst := is_const_of_deriv_eq_zero
      (fun x => (hz x).differentiableAt) (fun x => (hz x).deriv) s 0
    have hzero : thetaPhys d (perim front) theta0 0 - theta 0 = 0 := by
      simp [theta0, thetaPhys]
    linarith
  refine ⟨theta0, hdC, ?_⟩
  intro s
  rw [show thetaPhys
      (intrinsicLimitSteeringData hfront delta hperiod hmem hode)
        (perim front) theta0 s = theta s by simpa [d] using hangle s]
  exact hcurve s

/-- The reconstructed limiting steering has a global physical rear-arclength
inverse, and the steering cannot collapse after composition with that inverse.
The only remaining physical closure identities are therefore the rear period
and rear-track position formulas. -/
theorem exists_intrinsicLimitRearInverse_nonzero
    {kh c dlt : ℝ} {front : Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front)
    (delta : ℝ → ℝ) (hperiod : Function.Periodic delta 1)
    (hmem : ∀ u, delta u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh))
    (hode : ∀ u, HasDerivAt delta
      (perim front * (dataCurv front u - Real.sin (delta u))) u) :
    let d := intrinsicLimitSteeringData hfront delta hperiod hmem hode
    ∃ sf : ℝ → ℝ,
      (∀ x, RearTrack.rearArclength (deltaPhys d (perim front)) (sf x) = x) ∧
      ∃ x, deltaPhys d (perim front) (sf x) ≠ 0 := by
  dsimp only
  let d := intrinsicLimitSteeringData hfront delta hperiod hmem hode
  let dl := deltaPhys d (perim front)
  have hP : 0 < perim front := perim_pos hc hfront
  have hdlC : Continuous dl := by
    dsimp [dl, deltaPhys, d]
    exact (Differentiable.continuous fun u => (hode u).differentiableAt).comp
      (continuous_id.div_const (perim front))
  have hdl0 : ∀ s, 0 ≤ dl s := fun s => (deltaPhys_mem d s).1
  have hdl1 : ∀ s, dl s ≤ Real.arcsin kh := fun s => (deltaPhys_mem d s).2
  obtain ⟨sf, hsf⟩ := ArclengthInverse.exists_inverse_rearArclength
    hkh0 hkh1 hdlC hdl0 hdl1
  refine ⟨sf, hsf, ?_⟩
  obtain ⟨u, hu⟩ := steering_nonzero_of_normalized_intrinsic_ode
    hc hfront rfl hode
  let s := perim front * u
  let x := RearTrack.rearArclength dl s
  have hmono : StrictMono (RearTrack.rearArclength dl) :=
    RearTrack.strictMono_rearArclength hdlC hkh1 hkh0 hdl0 hdl1
  have hleft : sf x = s := by
    apply hmono.injective
    simpa [x] using hsf x
  refine ⟨x, ?_⟩
  rw [hleft]
  change delta (s / perim front) ≠ 0
  have hs : s / perim front = u := by
    dsimp [s]
    field_simp [ne_of_gt hP]
  simpa [hs] using hu

/-- One physical steering period has rear arclength equal to the front period
times the normalized cosine mass. -/
theorem rearArclength_period_eq_mul_normalizedCosinePrimitive
    {kh P : ℝ} (d : NormalizedSelectedRearClosure.SteeringData kh)
    (hP : 0 < P) :
    RearTrack.rearArclength (deltaPhys d P) P =
      P * normalizedCosinePrimitive d.delta 1 := by
  have hP0 : P ≠ 0 := ne_of_gt hP
  unfold RearTrack.rearArclength deltaPhys normalizedCosinePrimitive
  rw [intervalIntegral.integral_comp_div (fun x => Real.cos (d.delta x)) hP0]
  simp [hP0, smul_eq_mul]

/-- The finite rear-period identities pass to a marked limit using only
uniform convergence of the normalized steering lifts. -/
theorem rear_perimeter_limit_of_uniformSteering
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    (K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n))
    (hc : 0 < c)
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfrontConv : Tendsto frontN atTop (nhds front))
    {delta : ℝ → ℝ} (hdeltaC : Continuous delta)
    (hdelta : TendstoUniformly (fun n => (K n).steering.delta) delta atTop) :
    perim rear = RearTrack.rearArclength
      (fun s => delta (s / perim front)) (perim front) := by
  have hdeltaNC : ∀ n, Continuous (K n).steering.delta := fun n =>
    Differentiable.continuous fun u => ((K n).steering.steering u).differentiableAt
  have hprim := tendstoUniformlyOn_normalizedCosinePrimitive hdeltaNC hdeltaC hdelta
  have hprim1 : Tendsto
      (fun n => normalizedCosinePrimitive (K n).steering.delta 1) atTop
      (nhds (normalizedCosinePrimitive delta 1)) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    have hev := (Metric.tendstoUniformlyOn_iff.1 hprim) eps heps
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact ⟨N, fun n hn => by simpa [dist_comm] using hN n hn 1 (by norm_num)⟩
  have hpFront := tendsto_perim_of_marked_tendsto hfrontConv
  have hpRear := tendsto_perim_of_marked_tendsto hrearConv
  have hprod : Tendsto
      (fun n => perim (frontN n) *
        normalizedCosinePrimitive (K n).steering.delta 1) atTop
      (nhds (perim front * normalizedCosinePrimitive delta 1)) :=
    hpFront.mul hprim1
  have hfinite : ∀ n, perim (rearN n) = perim (frontN n) *
      normalizedCosinePrimitive (K n).steering.delta 1 := by
    intro n
    rw [(K n).rear_perimeter]
    exact rearArclength_period_eq_mul_normalizedCosinePrimitive
      (K n).steering (perim_pos hc (hfrontN n))
  have hprod' : Tendsto (fun n => perim (rearN n)) atTop
      (nhds (perim front * normalizedCosinePrimitive delta 1)) := by
    exact hprod.congr' (Eventually.of_forall fun n => (hfinite n).symm)
  have hlimit : perim rear =
      perim front * normalizedCosinePrimitive delta 1 :=
    tendsto_nhds_unique hpRear hprod'
  rw [hlimit]
  have hP := perim_pos hc hfront
  symm
  simpa [deltaPhys] using
    rearArclength_period_eq_mul_normalizedCosinePrimitive
      (intrinsicLimitSteeringData hfront delta
        (by
          intro u
          apply tendsto_nhds_unique (hdelta.tendsto_at (u + 1))
          exact (hdelta.tendsto_at u).congr' (Eventually.of_forall fun n => by
            exact ((K n).steering.delta_periodic u).symm))
        (fun u => by
          exact isClosed_Icc.mem_of_tendsto (hdelta.tendsto_at u)
            (Eventually.of_forall fun n => (K n).steering.delta_mem u))
        (normalized_steering_integral_identity_limit K hc hfrontN hfront
          hfrontConv hdeltaC hdelta).2)
      hP

end PathMetric
