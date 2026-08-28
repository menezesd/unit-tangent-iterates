import UnitTangentIterates.PhysicalRearLocalShiftedStageClosure

/-!
# Synchronized extraction for physical rear limits

The older partial-closure theorem hides the Arzela--Ascoli subsequence.  This
module exposes that subsequence together with the partial kinematic limit and
uniform steering convergence, so inverse and rear-track closure can use the
same finite stages.
-/

noncomputable section

open Filter Set Topology MarkedSpace

namespace PathMetric

open CurvatureFromMarkedDistance
open NormalizedSelectedRearClosure
open NormalizedSteeringPhysicalRescaling

structure ExtractedKinematicLimit
    (kh : ℝ) (rearN frontN : ℕ → Data) (rear front : Data)
    (K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n)) where
  phi : ℕ → ℕ
  phi_strictMono : StrictMono phi
  limit : PhysicalRearLimitKinematicsWithoutTrack kh rear front
  steering_tendsto : TendstoUniformly
    (fun n => (K (phi n)).steering.delta) limit.steering.delta atTop

/-- Arzela--Ascoli steering extraction with its index map retained. -/
theorem exists_extractedKinematicLimit_of_lipschitz
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    (K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n))
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfrontConv : Tendsto frontN atTop (nhds front))
    {C : NNReal}
    (hLip : ∀ n, LipschitzWith C (K n).steering.delta) :
    Nonempty (ExtractedKinematicLimit kh rearN frontN rear front K) := by
  obtain ⟨deltaUnit, phi, hphi, hdeltaUnit, hmemUnit, hend⟩ :=
    exists_uniformSteering_subseq (fun n => (K n).steering) hLip
  let rearS : ℕ → Data := fun n => rearN (phi n)
  let frontS : ℕ → Data := fun n => frontN (phi n)
  let KS : ∀ n, PhysicalRearLimitKinematics kh (rearS n) (frontS n) :=
    fun n => K (phi n)
  have hrearS : Tendsto rearS atTop (nhds rear) := by
    simpa [rearS, Function.comp_def] using
      hrearConv.comp hphi.tendsto_atTop
  have hfrontS : Tendsto frontS atTop (nhds front) := by
    simpa [frontS, Function.comp_def] using
      hfrontConv.comp hphi.tendsto_atTop
  have hfrontSN : ∀ n, IsTubeMember c 0 dlt (frontS n) :=
    fun n => hfrontN (phi n)
  have hdeltaUnitS : Tendsto
      (fun n => steeringOnUnit (KS n).steering) atTop (nhds deltaUnit) := by
    simpa [KS] using hdeltaUnit
  let delta := unitPeriodicExtension deltaUnit
  have hdeltaC : Continuous delta := by
    simpa [delta] using continuous_unitPeriodicExtension deltaUnit hend
  have hperiod : Function.Periodic delta 1 := by
    simpa [delta] using unitPeriodicExtension_periodic deltaUnit
  have hmem : ∀ u, delta u ∈ Set.Icc (0 : ℝ) (Real.arcsin kh) := by
    intro u
    exact hmemUnit _
  have hlimit := normalized_steering_integral_identity_limit_of_unit
    KS hc hfrontSN hfront hfrontS deltaUnit hdeltaUnitS hend
  have hode : ∀ u, HasDerivAt delta
      (perim front * (dataCurv front u - Real.sin (delta u))) u := by
    simpa [delta] using hlimit.2
  let d := intrinsicLimitSteeringData hfront delta hperiod hmem hode
  obtain ⟨theta0, hdC, hfrontFrenet⟩ :=
    exists_intrinsicLimitFrontFrenet hc hfront delta hperiod hmem hode
  obtain ⟨sf, hsf, hnonzero⟩ :=
    exists_intrinsicLimitRearInverse_nonzero hkh0 hkh1 hc hfront
      delta hperiod hmem hode
  have hdeltaUniform : TendstoUniformly
      (fun n => (KS n).steering.delta) delta atTop := by
    simpa [delta] using tendstoUniformly_unitPeriodicExtension
      (fun n => (KS n).steering) deltaUnit hdeltaUnitS
  have hrearPerimRaw := rear_perimeter_limit_of_uniformSteering
    KS hc hfrontSN hfront hrearS hfrontS hdeltaC hdeltaUniform
  have hrearPerim : perim rear =
      RearTrack.rearArclength (deltaPhys d (perim front)) (perim front) := by
    simpa [d, deltaPhys, intrinsicLimitSteeringData] using hrearPerimRaw
  let L : PhysicalRearLimitKinematicsWithoutTrack kh rear front := {
    theta0 := theta0
    steering := d
    sf := sf
    curvature_continuous := by simpa [d] using hdC
    arclength_rightInverse := by simpa [d] using hsf
    front_frenet := by simpa [d] using hfrontFrenet
    rear_perimeter := hrearPerim
    steering_nonzero := by simpa [d] using hnonzero }
  refine ⟨{
    phi := phi
    phi_strictMono := hphi
    limit := L
    steering_tendsto := ?_ }⟩
  simpa [KS, L, d] using hdeltaUniform

/-! ### Normalized primitive and inverse convergence on one period -/

theorem normalizedCosineMass_bounds {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (d : SteeringData kh) :
    let m := Real.sqrt (1 - kh ^ 2)
    m ≤ normalizedCosinePrimitive d.delta 1 ∧
      normalizedCosinePrimitive d.delta 1 ≤ 1 := by
  dsimp only
  let m := Real.sqrt (1 - kh ^ 2)
  have hm : 0 < m := Real.sqrt_pos.mpr (by nlinarith)
  have hdC : Continuous d.delta :=
    Differentiable.continuous fun u => (d.steering u).differentiableAt
  have hcosLo : ∀ u, m ≤ Real.cos (d.delta u) := fun u =>
    Shadowing.cos_ge_of_mem_strip (d.delta_mem u).1 (d.delta_mem u).2
  have hlo := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1)
    intervalIntegrable_const
    ((Real.continuous_cos.comp hdC).intervalIntegrable 0 1)
    (fun u _ => hcosLo u)
  have hhi := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((Real.continuous_cos.comp hdC).intervalIntegrable 0 1)
    intervalIntegrable_const
    (fun u _ => Real.cos_le_one (d.delta u))
  constructor
  · calc
      m = ∫ _u in (0 : ℝ)..1, m := by simp
      _ ≤ ∫ u in (0 : ℝ)..1, Real.cos (d.delta u) := by
        simpa [Function.comp_def] using hlo
      _ = normalizedCosinePrimitive d.delta 1 := rfl
  · calc
      normalizedCosinePrimitive d.delta 1 =
          ∫ u in (0 : ℝ)..1, Real.cos (d.delta u) := rfl
      _ ≤ ∫ _u in (0 : ℝ)..1, (1 : ℝ) := by
        simpa [Function.comp_def] using hhi
      _ = 1 := by simp

theorem abs_normalizedCosinePrimitive_le_one
    {delta : ℝ → ℝ} (hdelta : Continuous delta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |normalizedCosinePrimitive delta x| ≤ 1 := by
  unfold normalizedCosinePrimitive
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => Real.cos (delta t)) (C := (1 : ℝ))
    (a := (0 : ℝ)) (b := x) (fun t _ => by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs] at hb
  have hb' : |∫ t in (0 : ℝ)..x, Real.cos (delta t)| ≤ |x| := by
    simpa using hb
  rw [abs_of_nonneg hx.1] at hb'
  exact hb'.trans hx.2

theorem unitRearPrimitive_slope {kh : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (d : SteeringData kh) :
    let m := Real.sqrt (1 - kh ^ 2)
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      a ≤ b → m * (b - a) ≤
        unitRearPrimitive d.delta b - unitRearPrimitive d.delta a := by
  dsimp only
  let m := Real.sqrt (1 - kh ^ 2)
  have hm : 0 < m := Real.sqrt_pos.mpr (by nlinarith)
  have hdC : Continuous d.delta :=
    Differentiable.continuous fun u => (d.steering u).differentiableAt
  have hmass := normalizedCosineMass_bounds hkh0 hkh1 d
  have hmass0 : 0 < normalizedCosinePrimitive d.delta 1 :=
    lt_of_lt_of_le hm hmass.1
  intro a ha b hb hab
  have hcosLo : ∀ u, m ≤ Real.cos (d.delta u) := fun u =>
    Shadowing.cos_ge_of_mem_strip (d.delta_mem u).1 (d.delta_mem u).2
  have hint := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) hab
    intervalIntegrable_const
    ((Real.continuous_cos.comp hdC).intervalIntegrable a b)
    (fun u _ => hcosLo u)
  have hdiff : normalizedCosinePrimitive d.delta b -
      normalizedCosinePrimitive d.delta a =
      ∫ u in a..b, Real.cos (d.delta u) := by
    unfold normalizedCosinePrimitive
    have hadd :
        (∫ u in (0 : ℝ)..a, Real.cos (d.delta u)) +
            ∫ u in a..b, Real.cos (d.delta u) =
          ∫ u in (0 : ℝ)..b, Real.cos (d.delta u) := by
      simpa only [Function.comp_def] using
        (intervalIntegral.integral_add_adjacent_intervals
          (μ := MeasureTheory.volume)
          ((Real.continuous_cos.comp hdC).intervalIntegrable 0 a)
          ((Real.continuous_cos.comp hdC).intervalIntegrable a b))
    linarith
  rw [unitRearPrimitive, unitRearPrimitive, div_sub_div_same, hdiff]
  have hnum : m * (b - a) ≤ ∫ u in a..b, Real.cos (d.delta u) := by
    simpa [mul_comm] using hint
  calc
    m * (b - a) ≤
        (m * (b - a)) / normalizedCosinePrimitive d.delta 1 := by
      rw [le_div_iff₀ hmass0]
      exact mul_le_of_le_one_right
        (mul_nonneg hm.le (sub_nonneg.mpr hab)) hmass.2
    _ ≤ (∫ u in a..b, Real.cos (d.delta u)) /
        normalizedCosinePrimitive d.delta 1 :=
      div_le_div_of_nonneg_right hnum hmass0.le

/-- The normalized rear-arclength map has the same quantitative lower slope
on the whole line, not only on a chosen period. -/
theorem unitRearPrimitive_slope_global
    {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (d : SteeringData kh) :
    let m := Real.sqrt (1 - kh ^ 2)
    ∀ a b : ℝ, a ≤ b →
      m * (b - a) ≤ unitRearPrimitive d.delta b -
        unitRearPrimitive d.delta a := by
  dsimp only
  let m := Real.sqrt (1 - kh ^ 2)
  have hm : 0 < m := Real.sqrt_pos.mpr (by nlinarith)
  have hdC : Continuous d.delta :=
    Differentiable.continuous fun u => (d.steering u).differentiableAt
  have hmass := normalizedCosineMass_bounds hkh0 hkh1 d
  have hmass0 : 0 < normalizedCosinePrimitive d.delta 1 :=
    lt_of_lt_of_le hm hmass.1
  intro a b hab
  have hcosLo : ∀ u, m ≤ Real.cos (d.delta u) := fun u =>
    Shadowing.cos_ge_of_mem_strip (d.delta_mem u).1 (d.delta_mem u).2
  have hint := intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) hab intervalIntegrable_const
    ((Real.continuous_cos.comp hdC).intervalIntegrable a b)
    (fun u _ => hcosLo u)
  have hdiff : normalizedCosinePrimitive d.delta b -
      normalizedCosinePrimitive d.delta a =
      ∫ u in a..b, Real.cos (d.delta u) := by
    unfold normalizedCosinePrimitive
    have hadd :
        (∫ u in (0 : ℝ)..a, Real.cos (d.delta u)) +
            ∫ u in a..b, Real.cos (d.delta u) =
          ∫ u in (0 : ℝ)..b, Real.cos (d.delta u) := by
      simpa only [Function.comp_def] using
        (intervalIntegral.integral_add_adjacent_intervals
          (μ := MeasureTheory.volume)
          ((Real.continuous_cos.comp hdC).intervalIntegrable 0 a)
          ((Real.continuous_cos.comp hdC).intervalIntegrable a b))
    linarith
  rw [unitRearPrimitive, unitRearPrimitive, div_sub_div_same, hdiff]
  have hnum : m * (b - a) ≤ ∫ u in a..b, Real.cos (d.delta u) := by
    simpa [mul_comm] using hint
  calc
    m * (b - a) ≤
        (m * (b - a)) / normalizedCosinePrimitive d.delta 1 := by
      rw [le_div_iff₀ hmass0]
      exact mul_le_of_le_one_right
        (mul_nonneg hm.le (sub_nonneg.mpr hab)) hmass.2
    _ ≤ (∫ u in a..b, Real.cos (d.delta u)) /
        normalizedCosinePrimitive d.delta 1 :=
      div_le_div_of_nonneg_right hnum hmass0.le

/-- A right inverse of a globally lower-slope map has the reciprocal global
Lipschitz bound. -/
theorem lipschitzWith_rightInverse_of_slope
    {A sf : ℝ → ℝ} {m : ℝ} (hm : 0 < m)
    (hslope : ∀ a b : ℝ, a ≤ b → m * (b - a) ≤ A b - A a)
    (hinv : ∀ x, A (sf x) = x) :
    LipschitzWith (Real.toNNReal (1 / m)) sf := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hcoef : (Real.toNNReal (1 / m) : ℝ) = 1 / m := by
    rw [Real.coe_toNNReal]
    exact div_nonneg zero_le_one hm.le
  rw [hcoef, Real.dist_eq, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · have hsfxy : sf x ≤ sf y := by
      by_contra h
      have hlt := hslope (sf y) (sf x) (le_of_not_ge h)
      rw [hinv, hinv] at hlt
      nlinarith
    have h := hslope (sf x) (sf y) hsfxy
    rw [hinv, hinv] at h
    rw [abs_of_nonpos (sub_nonpos.mpr hsfxy),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hd : sf y - sf x ≤ (y - x) / m := by
      apply (le_div_iff₀ hm).2
      nlinarith
    calc
      -(sf x - sf y) = sf y - sf x := by ring
      _ ≤ (y - x) / m := hd
      _ = 1 / m * -(x - y) := by field_simp; ring
  · have hsfyx : sf y ≤ sf x := by
      by_contra h
      have hlt := hslope (sf x) (sf y) (le_of_not_ge h)
      rw [hinv, hinv] at hlt
      nlinarith
    have h := hslope (sf y) (sf x) hsfyx
    rw [hinv, hinv] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hsfyx),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hd : sf x - sf y ≤ (x - y) / m := by
      apply (le_div_iff₀ hm).2
      nlinarith
    calc
      sf x - sf y ≤ (x - y) / m := hd
      _ = 1 / m * (x - y) := by field_simp

/-- Uniform steering convergence implies uniform convergence of the normalized
rear-arclength maps on the unit period. -/
theorem tendstoUniformlyOn_unitRearPrimitive
    {kh : ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (dN : ℕ → SteeringData kh) (d : SteeringData kh)
    (hdelta : TendstoUniformly (fun n => (dN n).delta) d.delta atTop) :
    TendstoUniformlyOn (fun n => unitRearPrimitive (dN n).delta)
      (unitRearPrimitive d.delta) atTop (Set.Icc (0 : ℝ) 1) := by
  let m := Real.sqrt (1 - kh ^ 2)
  have hm : 0 < m := Real.sqrt_pos.mpr (by nlinarith)
  let C0 : ℝ := 1 / m + 1 / (m * m)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hdNC : ∀ n, Continuous (dN n).delta := fun n =>
    Differentiable.continuous fun u => ((dN n).steering u).differentiableAt
  have hdC : Continuous d.delta :=
    Differentiable.continuous fun u => (d.steering u).differentiableAt
  have hprim := tendstoUniformlyOn_normalizedCosinePrimitive hdNC hdC hdelta
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  let eta := eps / (2 * C0)
  have heta : 0 < eta := div_pos heps (mul_pos (by norm_num) hC0)
  have hev := (Metric.tendstoUniformlyOn_iff.1 hprim) eta heta
  filter_upwards [hev] with n hn
  intro x hx
  have hmassN := normalizedCosineMass_bounds hkh0 hkh1 (dN n)
  have hmass := normalizedCosineMass_bounds hkh0 hkh1 d
  have hmassN0 : normalizedCosinePrimitive (dN n).delta 1 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hm hmassN.1)
  have hmass0 : normalizedCosinePrimitive d.delta 1 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hm hmass.1)
  have hxclose : |normalizedCosinePrimitive (dN n).delta x -
      normalizedCosinePrimitive d.delta x| ≤ eta := by
    simpa [Real.dist_eq, abs_sub_comm] using (hn x hx).le
  have h1close : |normalizedCosinePrimitive (dN n).delta 1 -
      normalizedCosinePrimitive d.delta 1| ≤ eta := by
    simpa [Real.dist_eq, abs_sub_comm] using (hn 1 (by norm_num)).le
  have hb := abs_unitRearPrimitive_sub_le hmassN0 hmass0 hxclose h1close
  have habsN : m ≤ |normalizedCosinePrimitive (dN n).delta 1| := by
    rw [abs_of_pos (lt_of_lt_of_le hm hmassN.1)]
    exact hmassN.1
  have habs : m ≤ |normalizedCosinePrimitive d.delta 1| := by
    rw [abs_of_pos (lt_of_lt_of_le hm hmass.1)]
    exact hmass.1
  have hxbound := abs_normalizedCosinePrimitive_le_one hdC hx
  have hfirst :
      eta / |normalizedCosinePrimitive (dN n).delta 1| ≤ eta / m :=
    div_le_div_of_nonneg_left heta.le hm habsN
  have hnum2 :
      |normalizedCosinePrimitive d.delta x| * eta ≤ eta :=
    mul_le_of_le_one_left heta.le hxbound
  have hden2 :
      m * m ≤ |normalizedCosinePrimitive (dN n).delta 1| *
        |normalizedCosinePrimitive d.delta 1| :=
    mul_le_mul habsN habs hm.le (abs_nonneg _)
  have hsecond :
      |normalizedCosinePrimitive d.delta x| * eta /
          (|normalizedCosinePrimitive (dN n).delta 1| *
            |normalizedCosinePrimitive d.delta 1|) ≤ eta / (m * m) := by
    calc
      |normalizedCosinePrimitive d.delta x| * eta /
            (|normalizedCosinePrimitive (dN n).delta 1| *
              |normalizedCosinePrimitive d.delta 1|) ≤
          eta / (|normalizedCosinePrimitive (dN n).delta 1| *
            |normalizedCosinePrimitive d.delta 1|) :=
        div_le_div_of_nonneg_right hnum2
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ eta / (m * m) :=
        div_le_div_of_nonneg_left heta.le (mul_pos hm hm) hden2
  have hbound :
    eta / |normalizedCosinePrimitive (dN n).delta 1| +
        |normalizedCosinePrimitive d.delta x| * eta /
          (|normalizedCosinePrimitive (dN n).delta 1| *
            |normalizedCosinePrimitive d.delta 1|) < eps := by
    calc
      eta / |normalizedCosinePrimitive (dN n).delta 1| +
            |normalizedCosinePrimitive d.delta x| * eta /
              (|normalizedCosinePrimitive (dN n).delta 1| *
                |normalizedCosinePrimitive d.delta 1|) ≤
          eta / m + eta / (m * m) := add_le_add hfirst hsecond
      _ = eta * C0 := by dsimp [C0]; field_simp
      _ = eps / 2 := by dsimp [eta]; field_simp
      _ < eps := half_lt_self heps
  simpa [Real.dist_eq, abs_sub_comm] using hb.trans_lt hbound

namespace PhysicalRearLimitKinematicsWithoutTrack

/-- The normalized physical rear-arclength map associated to a partial
limiting kinematic package. -/
def physicalUnitRearPrimitive {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematicsWithoutTrack kh rear front) (u : ℝ) : ℝ :=
  RearTrack.rearArclength (deltaPhys K.steering (perim front))
    (perim front * u) / perim rear

/-- The normalized inverse rear-arclength map associated to a partial
limiting kinematic package. -/
def physicalUnitRearInverse {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematicsWithoutTrack kh rear front) (x : ℝ) : ℝ :=
  K.sf (perim rear * x) / perim front

theorem physicalUnitRearPrimitive_eq
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hc : 0 < c) (hfront : IsTubeMember c 0 dlt front) (u : ℝ) :
    K.physicalUnitRearPrimitive u = unitRearPrimitive K.steering.delta u := by
  have hP := perim_pos hc hfront
  have hP0 := ne_of_gt hP
  unfold physicalUnitRearPrimitive unitRearPrimitive normalizedCosinePrimitive
  rw [K.rear_perimeter]
  unfold RearTrack.rearArclength deltaPhys
  rw [intervalIntegral.integral_comp_div
    (fun x => Real.cos (K.steering.delta x)) hP0]
  rw [intervalIntegral.integral_comp_div
    (fun x => Real.cos (K.steering.delta x)) hP0]
  simp only [zero_div, mul_div_cancel_left₀ _ hP0, div_self hP0]
  exact mul_div_mul_left _ _ hP0

theorem physicalUnitRearInverse_data
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) :
    (∀ x, K.physicalUnitRearPrimitive (K.physicalUnitRearInverse x) = x) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        K.physicalUnitRearInverse x ∈ Set.Icc (0 : ℝ) 1) := by
  let P := perim front
  let Q := perim rear
  let dl := deltaPhys K.steering P
  have hP : 0 < P := perim_pos hc hfront
  have hQ : 0 < Q := perim_pos hc hrear
  have hdlC : Continuous dl :=
    (Differentiable.continuous fun u =>
      (K.steering.steering u).differentiableAt).comp
        (continuous_id.div_const P)
  have hdl0 : ∀ s, 0 ≤ dl s := fun s => (deltaPhys_mem K.steering s).1
  have hdl1 : ∀ s, dl s ≤ Real.arcsin kh := fun s =>
    (deltaPhys_mem K.steering s).2
  have hcos0 : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have hcos : ∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (dl s) := fun s =>
    Shadowing.cos_ge_of_mem_strip (hdl0 s) (hdl1 s)
  have hsfMono := SelectedInverseRearOwn.sf_strictMono
    hcos0 hdlC hcos K.arclength_rightInverse
  have harcMono := RearTrack.strictMono_rearArclength
    hdlC hkh1 hkh0 hdl0 hdl1
  have hsf0 : K.sf 0 = 0 := by
    apply harcMono.injective
    simpa [RearTrack.rearArclength] using K.arclength_rightInverse 0
  have hsfQ : K.sf Q = P := by
    apply harcMono.injective
    rw [K.arclength_rightInverse]
    simpa [P, Q, dl] using K.rear_perimeter
  constructor
  · intro x
    unfold physicalUnitRearPrimitive physicalUnitRearInverse
    rw [mul_div_cancel₀ _ (ne_of_gt hP)]
    rw [K.arclength_rightInverse]
    exact mul_div_cancel_left₀ x (ne_of_gt hQ)
  · intro x hx
    have hQx0 : 0 ≤ Q * x := mul_nonneg hQ.le hx.1
    have hQxQ : Q * x ≤ Q := mul_le_of_le_one_right hQ.le hx.2
    have hsfLo : 0 ≤ K.sf (Q * x) := by
      rw [← hsf0]
      exact hsfMono.monotone hQx0
    have hsfHi : K.sf (Q * x) ≤ P := by
      rw [← hsfQ]
      exact hsfMono.monotone hQxQ
    exact ⟨div_nonneg hsfLo hP.le, (div_le_one hP).2 hsfHi⟩

end PhysicalRearLimitKinematicsWithoutTrack

/-- Along the exact steering subsequence exposed by compactness, the
normalized inverse rear-arclength maps converge uniformly on one period. -/
theorem ExtractedKinematicLimit.unitRearInverse_tendsto
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    {K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n)}
    (E : ExtractedKinematicLimit kh rearN frontN rear front K)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrearN : ∀ n, IsTubeMember c 0 dlt (rearN n))
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) :
    TendstoUniformlyOn
      (fun n => (K (E.phi n)).physicalUnitRearInverse)
      E.limit.physicalUnitRearInverse atTop (Set.Icc (0 : ℝ) 1) := by
  let m := Real.sqrt (1 - kh ^ 2)
  have hm : 0 < m := Real.sqrt_pos.mpr (by nlinarith)
  have hprimitive := tendstoUniformlyOn_unitRearPrimitive
    hkh0 hkh1 (fun n => (K (E.phi n)).steering) E.limit.steering
      E.steering_tendsto
  have hlimitData := E.limit.physicalUnitRearInverse_data
    hkh0 hkh1 hc hrear hfront
  have hfiniteData : ∀ n,
      (∀ x, (K (E.phi n)).physicalUnitRearPrimitive
          ((K (E.phi n)).physicalUnitRearInverse x) = x) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1,
          (K (E.phi n)).physicalUnitRearInverse x ∈ Set.Icc (0 : ℝ) 1) :=
    fun n => (K (E.phi n)).physicalUnitRearInverse_data
      hkh0 hkh1 hc (hrearN (E.phi n)) (hfrontN (E.phi n))
  apply tendstoUniformlyOn_rightInverse_on_unit hm
    (unitRearPrimitive_slope hkh0 hkh1 E.limit.steering)
    hprimitive
  · intro x hx
    rw [← E.limit.physicalUnitRearPrimitive_eq hc hfront]
    exact hlimitData.1 x
  · intro n x hx
    rw [← (K (E.phi n)).physicalUnitRearPrimitive_eq hc
      (hfrontN (E.phi n))]
    exact (hfiniteData n).1 x
  · exact hlimitData.2
  · exact fun n => (hfiniteData n).2

/-- Iteration of an additive one-step shift through any integral translate. -/
theorem add_int_of_add_one (f : ℝ → ℝ)
    (h : ∀ x, f (x + 1) = f x + 1) (x : ℝ) (z : ℤ) :
    f (x + (z : ℝ)) = f x + (z : ℝ) := by
  induction z using Int.induction_on with
  | zero => simp
  | succ i hi =>
      rw [Int.cast_add, Int.cast_one]
      rw [← add_assoc, h, hi]
      ring
  | pred i hi =>
      have hs := h (x + (-(i : ℤ) - 1 : ℤ))
      push_cast at hs hi ⊢
      have heq : x + (-(i : ℝ) - 1) + 1 = x + -(i : ℝ) := by ring
      rw [heq, hi] at hs
      linarith

namespace PhysicalRearLimitKinematicsWithoutTrack

theorem physicalUnitRearInverse_add_one
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) (x : ℝ) :
    K.physicalUnitRearInverse (x + 1) =
      K.physicalUnitRearInverse x + 1 := by
  have hP : 0 < perim front := perim_pos hc hfront
  let D := RearArclengthInverseBridge.data_of_rightInverse hkh0 hkh1
    ((Differentiable.continuous fun u =>
      (K.steering.steering u).differentiableAt).comp
        (continuous_id.div_const (perim front)))
    (deltaPhys_periodic K.steering)
    (fun s => (deltaPhys_mem K.steering s).1)
    (fun s => (deltaPhys_mem K.steering s).2)
    K.arclength_rightInverse
  have hperiod : D.rearPeriod = perim rear := by
    change RearTrack.rearArclength
      (deltaPhys K.steering (perim front)) (perim front) = perim rear
    exact K.rear_perimeter.symm
  unfold physicalUnitRearInverse
  calc
    K.sf (perim rear * (x + 1)) / perim front =
        K.sf (perim rear * x + D.rearPeriod) / perim front := by
      rw [hperiod]
      congr 2
      ring
    _ = (K.sf (perim rear * x) + perim front) / perim front := by
      rw [D.sf_shift]
    _ = K.sf (perim rear * x) / perim front + 1 := by
      field_simp

theorem physicalUnitRearInverse_add_int
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) (x : ℝ) (z : ℤ) :
    K.physicalUnitRearInverse (x + (z : ℝ)) =
      K.physicalUnitRearInverse x + (z : ℝ) :=
  add_int_of_add_one K.physicalUnitRearInverse
    (K.physicalUnitRearInverse_add_one hkh0 hkh1 hc hrear hfront) x z

theorem physicalUnitRearInverse_lipschitz
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematicsWithoutTrack kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) :
    LipschitzWith (Real.toNNReal (1 / Real.sqrt (1 - kh ^ 2)))
      K.physicalUnitRearInverse := by
  apply lipschitzWith_rightInverse_of_slope
    (Real.sqrt_pos.mpr (by nlinarith))
    (unitRearPrimitive_slope_global hkh0 hkh1 K.steering)
  intro x
  rw [← K.physicalUnitRearPrimitive_eq hc hfront]
  exact (K.physicalUnitRearInverse_data hkh0 hkh1 hc hrear hfront).1 x

end PhysicalRearLimitKinematicsWithoutTrack

namespace PhysicalRearLimitKinematics

theorem physicalUnitRearInverse_add_one
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) (x : ℝ) :
    K.physicalUnitRearInverse (x + 1) =
      K.physicalUnitRearInverse x + 1 := by
  have hP : 0 < perim front := perim_pos hc hfront
  let D := RearArclengthInverseBridge.data_of_rightInverse hkh0 hkh1
    ((Differentiable.continuous fun u =>
      (K.steering.steering u).differentiableAt).comp
        (continuous_id.div_const (perim front)))
    (deltaPhys_periodic K.steering)
    (fun s => (deltaPhys_mem K.steering s).1)
    (fun s => (deltaPhys_mem K.steering s).2)
    K.arclength_rightInverse
  have hperiod : D.rearPeriod = perim rear := by
    change RearTrack.rearArclength
      (deltaPhys K.steering (perim front)) (perim front) = perim rear
    exact K.rear_perimeter.symm
  unfold physicalUnitRearInverse
  calc
    K.sf (perim rear * (x + 1)) / perim front =
        K.sf (perim rear * x + D.rearPeriod) / perim front := by
      rw [hperiod]
      congr 2
      ring
    _ = (K.sf (perim rear * x) + perim front) / perim front := by
      rw [D.sf_shift]
    _ = K.sf (perim rear * x) / perim front + 1 := by
      field_simp

theorem physicalUnitRearInverse_add_int
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) (x : ℝ) (z : ℤ) :
    K.physicalUnitRearInverse (x + (z : ℝ)) =
      K.physicalUnitRearInverse x + (z : ℝ) :=
  add_int_of_add_one K.physicalUnitRearInverse
    (K.physicalUnitRearInverse_add_one hkh0 hkh1 hc hrear hfront) x z

theorem physicalUnitRearInverse_lipschitz
    {kh c dlt : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) :
    LipschitzWith (Real.toNNReal (1 / Real.sqrt (1 - kh ^ 2)))
      K.physicalUnitRearInverse := by
  apply lipschitzWith_rightInverse_of_slope
    (Real.sqrt_pos.mpr (by nlinarith))
    (unitRearPrimitive_slope_global hkh0 hkh1 K.steering)
  intro x
  rw [← K.physicalUnitRearPrimitive_eq hc hfront]
  exact (K.physicalUnitRearInverse_data hkh0 hkh1 hc hrear hfront).1 x

end PhysicalRearLimitKinematics

/-- A uniformly Lipschitz sequence may be evaluated at moving arguments once
it converges at the limiting fixed argument. -/
theorem tendsto_comp_of_uniform_lipschitz
    {fN : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {xN : ℕ → ℝ} {x : ℝ} {C : NNReal}
    (hLip : ∀ n, LipschitzWith C (fN n))
    (hx : Tendsto xN atTop (nhds x))
    (hfixed : Tendsto (fun n => fN n x) atTop (nhds (f x))) :
    Tendsto (fun n => fN n (xN n)) atTop (nhds (f x)) := by
  rw [Metric.tendsto_atTop] at hx hfixed ⊢
  intro eps heps
  let eta := eps / (2 * ((C : ℝ) + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨N1, hN1⟩ := hx eta heta
  obtain ⟨N2, hN2⟩ := hfixed (eps / 2) (half_pos heps)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  have hlip := (hLip n).dist_le_mul (xN n) x
  have hfirst : dist (fN n (xN n)) (fN n x) ≤ eps / 2 := by
    calc
      dist (fN n (xN n)) (fN n x) ≤ (C : ℝ) * dist (xN n) x := hlip
      _ ≤ (C : ℝ) * eta :=
        mul_le_mul_of_nonneg_left (hN1 n hn1).le C.coe_nonneg
      _ ≤ ((C : ℝ) + 1) * eta := by
        gcongr
        linarith
      _ = eps / 2 := by
        dsimp [eta]
        field_simp
  have hsum := add_lt_add_of_le_of_lt hfirst (hN2 n hn2)
  have hsum' : dist (fN n (xN n)) (fN n x) +
      dist (fN n x) (f x) < eps := by
    nlinarith
  exact (dist_triangle _ (fN n x) _).trans_lt hsum'

/-- Unit-interval inverse convergence plus exact integral quasi-periodicity
gives pointwise convergence at every normalized rear coordinate. -/
theorem ExtractedKinematicLimit.unitRearInverse_tendsto_at
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    {K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n)}
    (E : ExtractedKinematicLimit kh rearN frontN rear front K)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrearN : ∀ n, IsTubeMember c 0 dlt (rearN n))
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front) (y : ℝ) :
    Tendsto (fun n => (K (E.phi n)).physicalUnitRearInverse y) atTop
      (nhds (E.limit.physicalUnitRearInverse y)) := by
  let r : ℝ := Int.fract y
  let z : ℤ := Int.floor y
  have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩
  have hbase := (E.unitRearInverse_tendsto hkh0 hkh1 hc
    hrearN hfrontN hrear hfront).tendsto_at hr
  have hy : r + (z : ℝ) = y := Int.fract_add_floor y
  have haddN : ∀ n,
      (K (E.phi n)).physicalUnitRearInverse (r + (z : ℝ)) =
        (K (E.phi n)).physicalUnitRearInverse r + (z : ℝ) := fun n =>
    (K (E.phi n)).physicalUnitRearInverse_add_int
      hkh0 hkh1 hc (hrearN (E.phi n)) (hfrontN (E.phi n)) r z
  have hadd := E.limit.physicalUnitRearInverse_add_int
    hkh0 hkh1 hc hrear hfront r z
  have hbase' := hbase.add_const (z : ℝ)
  convert hbase' using 1
  · funext n
    rw [← haddN n, hy]
  · rw [← hadd, hy]

/-- The normalized inverse remains convergent when evaluated at the physical
rear coordinate divided by the varying rear perimeter. -/
theorem ExtractedKinematicLimit.unitRearInverse_tendsto_physicalArg
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    {K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n)}
    (E : ExtractedKinematicLimit kh rearN frontN rear front K)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrearN : ∀ n, IsTubeMember c 0 dlt (rearN n))
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear)) (x : ℝ) :
    Tendsto
      (fun n => (K (E.phi n)).physicalUnitRearInverse
        (x / perim (rearN (E.phi n)))) atTop
      (nhds (E.limit.physicalUnitRearInverse (x / perim rear))) := by
  have hrearS := hrearConv.comp E.phi_strictMono.tendsto_atTop
  have hQ := tendsto_perim_of_marked_tendsto hrearS
  have hxarg : Tendsto (fun n => x / perim (rearN (E.phi n))) atTop
      (nhds (x / perim rear)) :=
    tendsto_const_nhds.div hQ (ne_of_gt (perim_pos hc hrear))
  apply tendsto_comp_of_uniform_lipschitz
    (C := Real.toNNReal (1 / Real.sqrt (1 - kh ^ 2)))
  · intro n
    exact (K (E.phi n)).physicalUnitRearInverse_lipschitz
      hkh0 hkh1 hc (hrearN (E.phi n)) (hfrontN (E.phi n))
  · exact hxarg
  · exact E.unitRearInverse_tendsto_at hkh0 hkh1 hc
      hrearN hfrontN hrear hfront (x / perim rear)

/-- Physical inverse rear-arclength convergence along the exact exposed
subsequence. -/
theorem ExtractedKinematicLimit.sf_tendsto
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    {K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n)}
    (E : ExtractedKinematicLimit kh rearN frontN rear front K)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrearN : ∀ n, IsTubeMember c 0 dlt (rearN n))
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfrontConv : Tendsto frontN atTop (nhds front)) (x : ℝ) :
    Tendsto (fun n => (K (E.phi n)).sf x) atTop (nhds (E.limit.sf x)) := by
  have hfrontS := hfrontConv.comp E.phi_strictMono.tendsto_atTop
  have hP := tendsto_perim_of_marked_tendsto hfrontS
  have hinv := E.unitRearInverse_tendsto_physicalArg hkh0 hkh1 hc
    hrearN hfrontN hrear hfront hrearConv x
  have hmul := hP.mul hinv
  convert hmul using 1
  · funext n
    unfold PhysicalRearLimitKinematics.physicalUnitRearInverse
    simp only [Function.comp_apply]
    field_simp [ne_of_gt (perim_pos hc (hfrontN (E.phi n))),
      ne_of_gt (perim_pos hc (hrearN (E.phi n)))]
  · unfold PhysicalRearLimitKinematicsWithoutTrack.physicalUnitRearInverse
    congr 1
    field_simp [ne_of_gt (perim_pos hc hfront),
      ne_of_gt (perim_pos hc hrear)]

/-- Steering evaluated at the inverse rear-arclength converges along the same
subsequence, as a direct continuous-composition consequence. -/
theorem ExtractedKinematicLimit.deltaPhys_sf_tendsto
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    {K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n)}
    (E : ExtractedKinematicLimit kh rearN frontN rear front K)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrearN : ∀ n, IsTubeMember c 0 dlt (rearN n))
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear)) (x : ℝ) :
    Tendsto
      (fun n => deltaPhys (K (E.phi n)).steering
        (perim (frontN (E.phi n))) ((K (E.phi n)).sf x)) atTop
      (nhds (deltaPhys E.limit.steering (perim front) (E.limit.sf x))) := by
  have hinv := E.unitRearInverse_tendsto_physicalArg hkh0 hkh1 hc
    hrearN hfrontN hrear hfront hrearConv x
  have hcomp := E.steering_tendsto.tendsto_comp
    ((Differentiable.continuous fun u =>
      (E.limit.steering.steering u).differentiableAt).continuousAt) hinv
  convert hcomp using 1
  · funext n
    unfold deltaPhys PhysicalRearLimitKinematics.physicalUnitRearInverse
    congr 2
    field_simp [ne_of_gt (perim_pos hc (hrearN (E.phi n)))]
  · unfold deltaPhys
    unfold PhysicalRearLimitKinematicsWithoutTrack.physicalUnitRearInverse
    congr 2
    field_simp [ne_of_gt (perim_pos hc hrear)]

/-- Automatic synchronized limit built from steering compactness and exact
normalized inverse stability.  The output sequences are indexed by the
publicly exposed subsequence map `E.phi`. -/
def ExtractedKinematicLimit.toSynchronizedKinematicLimit
    {kh c dlt : ℝ}
    {rearN frontN : ℕ → Data} {rear front : Data}
    {K : ∀ n, PhysicalRearLimitKinematics kh (rearN n) (frontN n)}
    (E : ExtractedKinematicLimit kh rearN frontN rear front K)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hrearN : ∀ n, IsTubeMember c 0 dlt (rearN n))
    (hfrontN : ∀ n, IsTubeMember c 0 dlt (frontN n))
    (hrear : IsTubeMember c 0 dlt rear)
    (hfront : IsTubeMember c 0 dlt front)
    (hrearConv : Tendsto rearN atTop (nhds rear))
    (hfrontConv : Tendsto frontN atTop (nhds front)) :
    PhysicalRearLocalShiftedStageClosure.SynchronizedKinematicLimit kh
      (fun n => rearN (E.phi n)) (fun n => frontN (E.phi n)) rear front
      (fun n => K (E.phi n)) where
  limit := E.limit
  sf_tendsto := E.sf_tendsto hkh0 hkh1 hc hrearN hfrontN
    hrear hfront hrearConv hfrontConv
  delta_tendsto := E.deltaPhys_sf_tendsto hkh0 hkh1 hc hrearN hfrontN
    hrear hfront hrearConv

end PathMetric
