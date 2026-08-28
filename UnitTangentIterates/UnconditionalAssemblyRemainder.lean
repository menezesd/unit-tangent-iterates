import Mathlib
import UnitTangentIterates.PaperHairpinConfig
import UnitTangentIterates.UnitTangentIteratesMain
import UnitTangentIterates.CurveDistance
import UnitTangentIterates.TubePullbackLimit
import UnitTangentIterates.SelectedInverseMap
import UnitTangentIterates.InterpolationVariableSpeedSelInvAdapter

/-!
# Exact remainder for the unconditional paper theorem

This record is an audit boundary, not an unconditional theorem.  It records
that every model-orbit configuration comes from `PaperHairpinData`, then lists
the marked interpolation and backward-shadowing hypotheses still required by
`unit_tangent_iterates_main_theorem`.
-/

noncomputable section

open Set Function Filter Topology Metric CurvatureStabilityL1

namespace UnconditionalAssembly

open MarkedSpace ModelOrbitDefect PaperHairpinConfig

/-- A coherent sequence of the paper's transition configurations.  The model
curvature at level `n` is the periodized curvature on the previous side of the
`n`-th transition.  Consequently its regularity, period, upper bound, and
turning mass are consequences of `Config`, rather than independent capstone
hypotheses. -/
structure ConfiguredModelSequence
    (kappas : ℕ → ℝ → ℝ) (Hs : ℕ → ℝ) (eps : ℕ → ℝ) where
  alpha : ℝ
  beta : ℝ
  a : ℝ
  au : ℝ
  C : ℝ
  CU : ℝ
  CK : ℝ
  DU : ℝ
  DU2 : ℝ
  D : ℝ
  Km : ℝ
  Kd : ℝ
  Bcell : ℝ
  thetaBase : ℝ
  kstar : ℝ
  kd : ℝ
  configs : ∀ n, Config alpha beta a au C CU CK DU DU2 D Km Kd Bcell thetaBase
    kstar kd (eps n) (Hs (n + 1)) (Hs n)
  config_from_paper : ∀ n, ∃ y yu yu' : ℝ → ℝ,
    ∃ d : PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := Bcell) (theta0 := thetaBase)
      (kstar := kstar) (kd := kd) (eps0 := eps n) (H := Hs (n + 1))
      (P := Hs n) y yu yu', d.toConfig.1 = configs n
  curvature_eq : ∀ n,
    kappas n = modelCurvature (configs n).yu (configs n).yu' (Hs n)
  separation_mono : ∀ n, Hs 0 ≤ Hs n

namespace ConfiguredModelSequence

theorem separation_pos {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ} {eps : ℕ → ℝ}
    (m : ConfiguredModelSequence kappas Hs eps) (n : ℕ) : 0 < Hs n :=
  (m.configs n).Ppos

theorem curvature_continuous {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ} {eps : ℕ → ℝ}
    (m : ConfiguredModelSequence kappas Hs eps) (n : ℕ) : Continuous (kappas n) := by
  rw [m.curvature_eq n]
  exact (m.configs n).continuous_KP

theorem curvature_periodic {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ} {eps : ℕ → ℝ}
    (m : ConfiguredModelSequence kappas Hs eps) (n : ℕ) : Periodic (kappas n) (Hs n) := by
  rw [m.curvature_eq n]
  exact (m.configs n).periodic_KP

theorem curvature_upper {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ} {eps : ℕ → ℝ}
    (m : ConfiguredModelSequence kappas Hs eps) (n : ℕ) (s : ℝ) :
    kappas n s ≤ m.kstar := by
  rw [m.curvature_eq n]
  exact (m.configs n).KP_le s

theorem total_turning {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ} {eps : ℕ → ℝ}
    (m : ConfiguredModelSequence kappas Hs eps) (n : ℕ) :
    (∫ r in (0 : ℝ)..(Hs n), kappas n r) = Real.pi := by
  rw [m.curvature_eq n]
  exact (m.configs n).integral_KP_eq_pi

end ConfiguredModelSequence

structure UnconditionalAssemblyRemainder
    (kappas : ℕ → ℝ → ℝ) (Hs theta0 : ℕ → ℝ)
    (kmin kap Cw Csh kb M : ℝ) (eps cw P : ℕ → ℝ) (dir : ℂ)
    (B T : tube (2 * Hs 0) kmin
      (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0)) →
      tube (2 * Hs 0) kmin
        (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0))) where
  alpha : ℝ
  beta : ℝ
  a : ℝ
  au : ℝ
  C : ℝ
  CU : ℝ
  CK : ℝ
  DU : ℝ
  DU2 : ℝ
  D : ℝ
  Km : ℝ
  Kd : ℝ
  Bcell : ℝ
  thetaBase : ℝ
  kstar : ℝ
  kd : ℝ
  configs : ∀ n, Config alpha beta a au C CU CK DU DU2 D Km Kd Bcell thetaBase
    kstar kd (eps n) (Hs (n + 1)) (Hs n)
  config_from_paper : ∀ n, ∃ y yu yu' : ℝ → ℝ,
    ∃ d : PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
      (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
      (Km := Km) (Kd := Kd) (B := Bcell) (theta0 := thetaBase)
      (kstar := kstar) (kd := kd) (eps0 := eps n) (H := Hs (n + 1))
      (P := Hs n) y yu yu', d.toConfig.1 = configs n
  kmin_pos : 0 < kmin
  separation_pos : ∀ n, 0 < Hs n
  separation_mono : ∀ n, Hs 0 ≤ Hs n
  curvature_continuous : ∀ n, Continuous (kappas n)
  curvature_periodic : ∀ n, Periodic (kappas n) (Hs n)
  curvature_lower : ∀ n s, kmin ≤ kappas n s
  curvature_upper : ∀ n s, kappas n s ≤ kap
  total_turning : ∀ n, (∫ r in (0 : ℝ)..(Hs n), kappas n r) = Real.pi
  selected_inverse_nonexpansive : ∀ x y, dist (B x) (B y) ≤ dist x y
  selected_inverse_continuous : Continuous B
  front_right_inverse : ∀ x, T (B x) = x
  front_realizes_unit_tangent : ∀ m,
    range (ev ((T m : Data))) = range (UnitTangent.unitTangentMap (ev ((m : Data))))
  derivative_bound_pos : 0 < M
  rear_period_pos : ∀ n, 0 < P n
  marked_defect_summable : Summable fun n =>
    l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n))
  /-- The presently missing concrete interpolation-to-marked-tube bridge. -/
  marked_interpolation_defect : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin
      (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0))),
    ev ((p : Data)) = TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) →
    ev ((q : Data)) = TwoCapPairsAssembly.front (kappas (n + 1)) (theta0 (n + 1)) (Hs (n + 1)) →
    perim ((p : Data)) = 2 * Hs n ∧ perim ((B q : Data)) = 2 * Hs n ∧
    ∃ Θp Θq kp kq kp' kq' : ℝ → ℝ,
      (∀ s, HasDerivAt (ev ((p : Data))) (Complex.exp (Complex.I * (Θp s : ℂ))) s) ∧
      (∀ s, HasDerivAt (ev ((B q : Data))) (Complex.exp (Complex.I * (Θq s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θp (kp s) s) ∧ (∀ s, HasDerivAt Θq (kq s) s) ∧
      ev ((p : Data)) 0 = ev ((B q : Data)) 0 ∧ Θp 0 = Θq 0 ∧
      Periodic kp (P n) ∧ Periodic kq (P n) ∧
      (∀ x, HasDerivAt kp (kp' x) x) ∧ (∀ x, HasDerivAt kq (kq' x) x) ∧
      (∀ x, |kp' x| ≤ M / 2) ∧ (∀ x, |kq' x| ≤ M / 2) ∧
      (∫ x in (cw n)..(cw n + P n), |kp x - kq x|) ≤ eps n ∧
      (∀ s, |kq s| ≤ kb)
  shadow_factor : 1 ≤ Csh
  direction_unit : ‖dir‖ = 1
  model_width : Width.width
    (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw
  transverse_gap : Cw + 2 * (Csh * ShadowingTails.tail
      (fun n => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 *
        (1 + kb * (2 * Hs n))) 0) <
    (2 * Hs 0 - Csh * ShadowingTails.tail
      (fun n => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 *
        (1 + kb * (2 * Hs n))) 0) / Real.pi

/-! ## Paper-faithful capstone

The fixed metric-tube record above assumes one positive lower curvature bound
for every model.  The expanding hairpin orbit in the paper instead has one
upper ceiling below one, while strict positivity is only pointwise for each
finite model and need not be uniform in the separation. -/

/-- The remaining regularizing-shadowing theorem in the paper's quantifiers.
The shadowing output includes the strictness recovered after taking the `C²`
limit and using the exact unit-tangent relation. -/
structure PaperFaithfulAssemblyRemainder
    (kappas : ℕ → ℝ → ℝ) (Hs theta0 eps : ℕ → ℝ)
  (Cw Csh : ℝ) (dir : ℂ) where
  model : ConfiguredModelSequence kappas Hs eps
  shadow_error : ℝ
  shadow_error_nonneg : 0 ≤ shadow_error
  shadow_factor_nonneg : 0 ≤ Csh
  direction_unit : ‖dir‖ = 1
  model_width : Width.width
    (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw
  transverse_gap : Cw + 2 * (Csh * shadow_error) <
    (2 * Hs 0 - Csh * shadow_error) / Real.pi
  shadowing_orbit : ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
    (∀ n, MainTheoremConditional.IsOval (X n)) ∧
    (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
    0 < LX ∧ Periodic (X 0) LX ∧
    hausdorffDist (range (X 0))
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤
        Csh * shadow_error ∧
    2 * Hs 0 - Csh * shadow_error ≤ LX

/-- Differential data supplied by the selected-inverse regularity gain for a
marked limit.  Nonnegativity is the closed tube condition written in intrinsic
curvature coordinates; `next_nonnegative` is convexity of its unit-tangent
successor. -/
structure LimitStrictnessData (p : MarkedSpace.Data) where
  theta : ℝ → ℝ
  k : ℝ → ℝ
  k' : ℝ → ℝ
  curve_deriv : ∀ s, HasDerivAt (ev p)
    (Complex.exp (Complex.I * (theta s : ℂ))) s
  angle_deriv : ∀ s, HasDerivAt theta (k s) s
  curvature_deriv : ∀ s, HasDerivAt k (k' s) s
  curvature_periodic : Periodic k (perim p)
  curvature_nonnegative : ∀ s, 0 ≤ k s
  next_nonnegative : ∀ s,
    0 ≤ (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2)
  curvature_nonzero : ∃ s, k s ≠ 0

/-- A nonnegative marked limit in an embedded tube is an oval once the
selected-inverse regularity data are available.  Strict positivity is not an
assumption: it follows from convexity of the next unit-tangent track. -/
theorem isOval_ev_of_limitStrictnessData
    {p : MarkedSpace.Data} {c dlt : ℝ}
    (hc : 0 < c) (hdlt : 0 < dlt)
    (hp : MarkedSpace.IsTubeMember c 0 dlt p)
    (d : LimitStrictnessData p) : MainTheoremConditional.IsOval (ev p) := by
  let L := perim p
  have hL : 0 < L := MarkedSpace.perim_pos hc hp
  have hpos : ∀ s, 0 < d.k s :=
    UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg hL
      d.curvature_periodic d.curvature_deriv d.curvature_nonnegative
      d.next_nonnegative d.curvature_nonzero
  have hinj : InjOn (ev p) (Ico 0 L) := by
    intro s hs t ht hst
    have hsmem : s / L ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg hs.1 hL.le
      · exact (div_lt_one hL).2 hs.2
    have htmem : t / L ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg ht.1 hL.le
      · exact (div_lt_one hL).2 ht.2
    have hzero : ‖p.1 (s / L) - p.1 (t / L)‖ = 0 := by
      have h : p.1 (s / L) = p.1 (t / L) := hst
      rw [h, sub_self, norm_zero]
    have hchord := hp.chord (s / L) (Ico_subset_Icc_self hsmem) (t / L)
      (Ico_subset_Icc_self htmem)
    rw [hzero] at hchord
    have hcyc : MarkedSpace.cyc (s / L) (t / L) ≤ 0 := by
      by_contra h
      push_neg at h
      nlinarith
    have heq := MarkedSpace.cyc_eq_zero_iff hsmem htmem hcyc
    field_simp at heq
    exact heq
  exact ⟨L, hL, MarkedSpace.periodic_ev hc hp, hinj, d.theta,
    d.curve_deriv, d.k, d.angle_deriv, hpos⟩

/-- The precise closure/regularity statement needed for the paper's canonical
selected inverse at a nonnegative-curvature limit.  This is intentionally
specialized to `SelectedInverseMap.selInv`: an arbitrary continuous map with a
right inverse cannot imply any curvature regularity.

Existing `TerminalCertificate`s establish the corresponding facts at finite
positive-curvature stages, but their constructor assumes `0 < kmin`; proving
this property requires passing the selected steering equation to the marked
`C²` limit and then applying the rear regularity gain. -/
def SelectedInverseLimitRegularity (kh c dlt : ℝ) : Prop :=
  ∀ X : ℕ → MarkedSpace.Data,
    (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) →
    (∀ n, X n = SelectedInverseMap.selInv kh (X (n + 1))) →
    ∀ n, Nonempty (LimitStrictnessData (X n))

namespace PaperFaithfulAssemblyRemainder

/-! ### Intrinsic endpoint data of a marked curve -/

/-- Intrinsic speed in the normalized marked parameter. -/
def intrinsicSpeed (p : MarkedSpace.Data) (u : ℝ) : ℝ := ‖p.2.1 u‖

/-- Intrinsic unit tangent; tube membership guarantees the denominator is
nonzero in every use below. -/
def intrinsicTangent (p : MarkedSpace.Data) (u : ℝ) : ℂ :=
  p.2.1 u / (intrinsicSpeed p u : ℂ)

/-- Intrinsic signed curvature obtained from the stored velocity and
acceleration. -/
def intrinsicCurvature (p : MarkedSpace.Data) (u : ℝ) : ℝ :=
  ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im / intrinsicSpeed p u ^ 3

/-- The period witness of a constant-speed path certificate is the intrinsic
speed of every marked slice. -/
theorem intrinsicSpeed_eq_period_of_slice
    {p q r : MarkedSpace.Data} {P : ℝ → ℝ} {theta : ℝ → ℝ → ℝ}
    {c kmin dlt : ℝ} (Γ : PathMetric.NormalPath p q) (t u : ℝ)
    (hr : MarkedSpace.IsTubeMember c kmin dlt r)
    (hXr : Γ.X t = ⇑r.1)
    (hXu : ∀ u, HasDerivAt (Γ.X t)
      ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hP : 0 ≤ P t) : intrinsicSpeed r u = P t := by
  rw [intrinsicSpeed,
    NormalPathC2Increment.vel_eq_of_slice Γ t hr hXr hXu u,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP,
    Complex.norm_exp]
  simp

/-- The normalized tangent witness is intrinsic, so tangent-angle lift
constants never enter endpoint compatibility. -/
theorem intrinsicTangent_eq_exp_of_slice
    {p q r : MarkedSpace.Data} {P : ℝ → ℝ} {theta : ℝ → ℝ → ℝ}
    {c kmin dlt : ℝ} (Γ : PathMetric.NormalPath p q) (t u : ℝ)
    (hr : MarkedSpace.IsTubeMember c kmin dlt r)
    (hXr : Γ.X t = ⇑r.1)
    (hXu : ∀ u, HasDerivAt (Γ.X t)
      ((P t : ℂ) * Complex.exp (Complex.I * (theta t u : ℂ))) u)
    (hP : 0 < P t) :
    intrinsicTangent r u = Complex.exp (Complex.I * (theta t u : ℂ)) := by
  rw [intrinsicTangent,
    NormalPathC2Increment.vel_eq_of_slice Γ t hr hXr hXu u,
    intrinsicSpeed_eq_period_of_slice Γ t u hr hXr hXu hP.le]
  have hne : (P t : ℂ) ≠ 0 := by
    simpa using hP.ne'
  field_simp


/-! ### Uniform stability of the rear-arclength inverse -/

/-- A uniform inverse estimate requiring no compactness argument.  If the
limiting rear-arclength primitive has slope at least `m > 0`, two primitives
are uniformly `e`-close, and `sfN`, `sf` are right inverses at the same target,
then their inverse values differ by at most `e / m`. -/
theorem abs_rightInverse_sub_le_of_uniform
    {A AN sf sfN : ℝ → ℝ} {m e : ℝ}
    (hm : 0 < m)
    (hslope : ∀ x y, x ≤ y → m * (y - x) ≤ A y - A x)
    (hclose : ∀ y, |AN y - A y| ≤ e)
    (hinv : ∀ x, A (sf x) = x)
    (hinvN : ∀ x, AN (sfN x) = x) (x : ℝ) :
    |sfN x - sf x| ≤ e / m := by
  have hA : |A (sfN x) - A (sf x)| ≤ e := by
    calc
      |A (sfN x) - A (sf x)| = |A (sfN x) - AN (sfN x)| := by
        rw [hinv x, hinvN x]
      _ = |AN (sfN x) - A (sfN x)| := abs_sub_comm _ _
      _ ≤ e := hclose (sfN x)
  have hmetric : m * |sfN x - sf x| ≤ |A (sfN x) - A (sf x)| := by
    rcases le_total (sfN x) (sf x) with hle | hle
    · have hs := hslope (sfN x) (sf x) hle
      have hAmono : A (sfN x) ≤ A (sf x) := by nlinarith [hm]
      rw [abs_of_nonpos (sub_nonpos.mpr hle),
        abs_of_nonpos (sub_nonpos.mpr hAmono)]
      nlinarith
    · have hs := hslope (sf x) (sfN x) hle
      have hAmono : A (sf x) ≤ A (sfN x) := by nlinarith [hm]
      rw [abs_of_nonneg (sub_nonneg.mpr hle),
        abs_of_nonneg (sub_nonneg.mpr hAmono)]
      nlinarith
  rw [le_div_iff₀ hm, mul_comm]
  exact hmetric.trans hA

/-! ### Continuous extension of the finite-stage selected inverse -/

/-- Data for extending a map from a dense inducing subspace.  The `hasLimit`
field is the completion estimate: in the paper it follows because images of
positive-curvature approximants are Cauchy under the additive Jacobi/path
cost. -/
structure DenseExtensionData
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] (i : α → β) (f : α → γ) where
  denseInducing : IsDenseInducing i
  hasLimit : ∀ b, ∃ c, Tendsto f (Filter.comap i (𝓝 b)) (𝓝 c)

namespace DenseExtensionData

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
  [TopologicalSpace γ] [T3Space γ] {i : α → β} {f : α → γ}

/-- The canonical extension obtained by taking the unique limit along the
dense positive-curvature subspace. -/
def extension (d : DenseExtensionData i f) : β → γ :=
  d.denseInducing.extend f

theorem continuous_extension (d : DenseExtensionData i f) :
    Continuous d.extension :=
  d.denseInducing.continuous_extend d.hasLimit

theorem extension_eq (d : DenseExtensionData i f) (a : α) :
    d.extension (i a) = f a :=
  d.denseInducing.extend_eq' d.hasLimit a

/-- A continuous right-inverse identity verified at every finite positive
stage passes to the completed operator by density. -/
theorem rightInverse_extension [T2Space β]
    (d : DenseExtensionData i f) {T : γ → β}
    (hT : Continuous T) (hTf : ∀ a, T (f a) = i a) :
    ∀ b, T (d.extension b) = b := by
  have heq : T ∘ d.extension = id :=
    d.denseInducing.dense.equalizer
      (hT.comp d.continuous_extension) continuous_id (by
        funext a
        simp only [Function.comp_apply, id_eq, d.extension_eq a, hTf a])
  exact fun b => congr_fun heq b

/-- More flexible closure principle: two continuous maps out of the completed
domain agree everywhere if their finite-stage values agree densely. -/
theorem map_extension_eq
    {δ : Type*} [TopologicalSpace δ] [T2Space δ]
    (d : DenseExtensionData i f) {T : γ → δ} {j : β → δ}
    (hT : Continuous T) (hj : Continuous j)
    (hfinite : ∀ a, T (f a) = j (i a)) :
    ∀ b, T (d.extension b) = j b := by
  have heq : T ∘ d.extension = j :=
    d.denseInducing.dense.equalizer
      (hT.comp d.continuous_extension) hj (by
        funext a
        simp only [Function.comp_apply, d.extension_eq a, hfinite a])
  exact fun b => congr_fun heq b

end DenseExtensionData

/-- Positive-curvature members of a fixed marked tube, allowing the lower
bound to depend on the member. -/
abbrev PositiveTube (c dlt : ℝ) :=
  {p : MarkedSpace.Data // ∃ kmin : ℝ, 0 < kmin ∧
    MarkedSpace.IsTubeMember c kmin dlt p}

/-- The closed nonnegative-curvature tube used for the shadowing limit. -/
abbrev NonnegativeTube (c dlt : ℝ) := MarkedSpace.tube c 0 dlt

/-- Forgetting a member-dependent positive lower bound places a curve in the
closed nonnegative tube. -/
def positiveToNonnegative {c dlt : ℝ} : PositiveTube c dlt → NonnegativeTube c dlt :=
  fun p => ⟨p.1, by
    obtain ⟨kmin, hkmin, hp⟩ := p.2
    exact
      { hasDerivAt_curve := hp.hasDerivAt_curve
        hasDerivAt_vel := hp.hasDerivAt_vel
        periodic := hp.periodic
        speed_const := hp.speed_const
        speed_lb := hp.speed_lb
        curv_lb := fun u => by
          have h := hp.curv_lb u
          have hs : 0 ≤ ‖p.1.2.1 u‖ ^ 3 := by positivity
          simpa using le_trans (mul_nonneg hkmin.le hs) h
        chord := hp.chord }⟩

/-- Completion package for the canonical selected inverse on one fixed tube.
`denseInducing` is the positive-approximation theorem and `hasLimit` is the
additive Jacobi/path Cauchy estimate. -/
abbrev SelectedInverseCompletionData (kh c dlt : ℝ) :=
  DenseExtensionData (positiveToNonnegative (c := c) (dlt := dlt))
    (fun p : PositiveTube c dlt => SelectedInverseMap.selInv kh p.1)

/-- The paper's completed selected inverse on the `kmin=0` closure. -/
def completedSelInv {kh c dlt : ℝ}
    (d : SelectedInverseCompletionData kh c dlt) :
    NonnegativeTube c dlt → MarkedSpace.Data :=
  d.extension

theorem continuous_completedSelInv {kh c dlt : ℝ}
    (d : SelectedInverseCompletionData kh c dlt) :
    Continuous (completedSelInv d) :=
  d.continuous_extension

/-- The completed operator agrees with the ordinary canonical selected
inverse at every positive-curvature stage. -/
theorem completedSelInv_eq_selInv {kh c dlt : ℝ}
    (d : SelectedInverseCompletionData kh c dlt) (p : PositiveTube c dlt) :
    (completedSelInv d) (positiveToNonnegative p) = SelectedInverseMap.selInv kh p.1 :=
  d.extension_eq p

/-- The finite-stage unit-tangent/right-inverse identity extends continuously
to the nonnegative tube. -/
theorem completedSelInv_rightInverse
    {kh c dlt : ℝ} (d : SelectedInverseCompletionData kh c dlt)
    {T : MarkedSpace.Data → MarkedSpace.Data} (hT : Continuous T)
    (hfinite : ∀ p : PositiveTube c dlt,
      T (SelectedInverseMap.selInv kh p.1) = p.1) :
    ∀ p : NonnegativeTube c dlt, T ((completedSelInv d) p) = p.1 :=
  d.map_extension_eq hT continuous_subtype_val hfinite

/-- Completion data when the finite selected inverse preserves the chosen
closed invariant tube.  Tube invariance supplies `finite`; its equality with
the canonical positive-stage `selInv` records that no new operator is being
introduced. -/
structure SelectedInverseSelfCompletionData (kh c dlt : ℝ) where
  finite : PositiveTube c dlt → NonnegativeTube c dlt
  finite_eq : ∀ p, (finite p).1 = SelectedInverseMap.selInv kh p.1
  completion : DenseExtensionData (positiveToNonnegative (c := c) (dlt := dlt)) finite

/-- Exact paper-level inputs for completing the canonical selected inverse on
the closed tube.  `preserves` is the finite weak-convex tube theorem, while
`denseInducing` and `hasLimit` are respectively positive-curvature
regularization and the additive Jacobi/path-cost Cauchy estimate. -/
structure SelectedInverseDenseCauchyData (kh c dlt : ℝ) where
  preserves : ∀ p : PositiveTube c dlt,
    MarkedSpace.IsTubeMember c 0 dlt (SelectedInverseMap.selInv kh p.1)
  denseInducing : IsDenseInducing (positiveToNonnegative (c := c) (dlt := dlt))
  hasLimit : ∀ b : NonnegativeTube c dlt, ∃ q : NonnegativeTube c dlt,
    Tendsto (fun p : PositiveTube c dlt =>
      (⟨SelectedInverseMap.selInv kh p.1, preserves p⟩ : NonnegativeTube c dlt))
      (Filter.comap positiveToNonnegative (𝓝 b)) (𝓝 q)

/-- Build the closed-tube selected inverse directly from the dense
positive-curvature construction and its Jacobi/path-cost Cauchy estimate. -/
def SelectedInverseDenseCauchyData.toSelfCompletion
    {kh c dlt : ℝ} (a : SelectedInverseDenseCauchyData kh c dlt) :
    SelectedInverseSelfCompletionData kh c dlt :=
  { finite := fun p => ⟨SelectedInverseMap.selInv kh p.1, a.preserves p⟩
    finite_eq := fun _ => rfl
    completion :=
      { denseInducing := a.denseInducing
        hasLimit := a.hasLimit } }

namespace SelectedInverseSelfCompletionData

/-- The continuous selected inverse as a self-map of the invariant closed
tube. -/
def closedSelInv {kh c dlt : ℝ} (d : SelectedInverseSelfCompletionData kh c dlt) :
    NonnegativeTube c dlt → NonnegativeTube c dlt :=
  d.completion.extension

theorem continuous_closedSelInv {kh c dlt : ℝ}
    (d : SelectedInverseSelfCompletionData kh c dlt) :
    Continuous d.closedSelInv :=
  d.completion.continuous_extension

theorem closedSelInv_eq_finite {kh c dlt : ℝ}
    (d : SelectedInverseSelfCompletionData kh c dlt) (p : PositiveTube c dlt) :
    d.closedSelInv (positiveToNonnegative p) = d.finite p :=
  d.completion.extension_eq p

/-- The finite-stage right-inverse identity passes to the completed self-map
without defining anything outside the invariant tube. -/
theorem closedSelInv_rightInverse
    {kh c dlt : ℝ} (d : SelectedInverseSelfCompletionData kh c dlt)
    {T : NonnegativeTube c dlt → NonnegativeTube c dlt}
    (hT : Continuous T) (hfinite : ∀ p, T (d.finite p) = positiveToNonnegative p) :
    ∀ p, T (d.closedSelInv p) = p :=
  d.completion.rightInverse_extension hT hfinite

/-- The completed right-inverse identity is not an additional shadowing
hypothesis: continuity transfers the canonical finite-stage identity from the
dense positive tube. -/
theorem closedSelInv_rightInverse_of_selInv
    {kh c dlt : ℝ} (d : SelectedInverseSelfCompletionData kh c dlt)
    {T : NonnegativeTube c dlt → NonnegativeTube c dlt}
    (hT : Continuous T)
    (hfinite : ∀ p : PositiveTube c dlt,
      T (d.finite p) = positiveToNonnegative p) :
    ∀ p, T (d.closedSelInv p) = p :=
  d.closedSelInv_rightInverse hT hfinite

end SelectedInverseSelfCompletionData

/-! ### Pullbacks entirely inside the closed tube -/

/-- The `k`-fold terminal pullback, defined directly in the invariant closed
tube. -/
def closedPullback {c dlt : ℝ}
    (B : NonnegativeTube c dlt → NonnegativeTube c dlt)
    (Q : ℕ → NonnegativeTube c dlt) (n : ℕ) : ℕ → NonnegativeTube c dlt
  | 0 => Q n
  | k + 1 => B (closedPullback B Q (n + 1) k)

@[simp] theorem closedPullback_zero {c dlt : ℝ}
    (B : NonnegativeTube c dlt → NonnegativeTube c dlt)
    (Q : ℕ → NonnegativeTube c dlt) (n : ℕ) :
    closedPullback B Q n 0 = Q n := rfl

theorem closedPullback_succ {c dlt : ℝ}
    (B : NonnegativeTube c dlt → NonnegativeTube c dlt)
    (Q : ℕ → NonnegativeTube c dlt) (n k : ℕ) :
    closedPullback B Q n (k + 1) = B (closedPullback B Q (n + 1) k) := rfl

/-- Summable consecutive pullback increments converge in the complete closed
tube and form an exact inverse orbit. -/
theorem exists_closedTube_shadowingLimit
    {c dlt : ℝ} {B : NonnegativeTube c dlt → NonnegativeTube c dlt}
    {Q : ℕ → NonnegativeTube c dlt} {d : ℕ → ℝ}
    (hsum : Summable d)
    (hstep : ∀ n k, dist (closedPullback B Q n k) (closedPullback B Q n (k + 1))
      ≤ d (n + k))
    (hB : Continuous B) :
    ∃ X : ℕ → NonnegativeTube c dlt,
      (∀ n, Tendsto (closedPullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n, dist (Q n) (X n) ≤ ShadowingTails.tail d n) := by
  have hlim : ∀ n, ∃ x : NonnegativeTube c dlt,
      Tendsto (closedPullback B Q n) atTop (𝓝 x) ∧
      ∀ k, dist (closedPullback B Q n k) x ≤ ShadowingTails.tail d (n + k) := by
    intro n
    simpa [ShadowingTails.tail, add_assoc] using
      (ShadowingTails.exists_limit_of_summable_increments
        (Z := closedPullback B Q n) (d := fun k => d (n + k)) (C := 1)
        (ShadowingTails.summable_shift hsum n)
        (fun k => by simpa using hstep n k))
  choose X hXlim hXdist using hlim
  have hinv : ∀ n, X n = B (X (n + 1)) := by
    intro n
    have hshift := (hXlim n).comp (tendsto_add_atTop_nat 1)
    have hBlim := (hB.tendsto _).comp (hXlim (n + 1))
    exact tendsto_nhds_unique hshift hBlim
  exact ⟨X, hXlim, hinv, fun n => by simpa using hXdist n 0⟩

/-- A right inverse on the closed tube turns the inverse limit orbit into the
forward orbit, still without leaving the subtype. -/
theorem closedTube_forwardOrbit
    {c dlt : ℝ} {B T : NonnegativeTube c dlt → NonnegativeTube c dlt}
    {X : ℕ → NonnegativeTube c dlt}
    (hTB : ∀ p, T (B p) = p) (hinv : ∀ n, X n = B (X (n + 1))) :
    ∀ n, T (X n) = X (n + 1) := by
  intro n
  rw [hinv n, hTB]

/-- Geometric shadowing output produced directly by the completed closed-tube
selected inverse. -/
theorem shadowingOrbit_of_closedTubeSteps
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {c dlt Csh : ℝ}
    {B T : NonnegativeTube c dlt → NonnegativeTube c dlt}
    {Q : ℕ → NonnegativeTube c dlt} {d : ℕ → ℝ}
    (hc : 0 < c) (hdlt : 0 < dlt) (hCsh : 1 ≤ Csh) (hsum : Summable d)
    (hstep : ∀ n k, dist (closedPullback B Q n k) (closedPullback B Q n (k + 1))
      ≤ d (n + k))
    (hB : Continuous B) (hTB : ∀ p, T (B p) = p)
    (hTev : ∀ p, range (ev (T p).1) =
      range (UnitTangent.unitTangentMap (ev p.1)))
    (hQfront : ∀ n, ev (Q n).1 =
      TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n))
    (hregularity : ∀ X : ℕ → NonnegativeTube c dlt,
      (∀ n, X n = B (X (n + 1))) → ∀ n, Nonempty (LimitStrictnessData (X n).1))
    (hQperim : perim (Q 0).1 = 2 * Hs 0) :
    ∃ (Y : ℕ → ℝ → ℂ) (LY : ℝ),
      (∀ n, MainTheoremConditional.IsOval (Y n)) ∧
      (∀ n, range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n))) ∧
      0 < LY ∧ Periodic (Y 0) LY ∧
      hausdorffDist (range (Y 0))
        (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤
          Csh * ShadowingTails.tail d 0 ∧
      2 * Hs 0 - Csh * ShadowingTails.tail d 0 ≤ LY := by
  obtain ⟨X, -, hinv, hdist⟩ := exists_closedTube_shadowingLimit hsum hstep hB
  let Y : ℕ → ℝ → ℂ := fun n => ev (X n).1
  let LY := perim (X 0).1
  have hoval : ∀ n, MainTheoremConditional.IsOval (Y n) := fun n => by
    obtain ⟨dn⟩ := hregularity X hinv n
    exact isOval_ev_of_limitStrictnessData hc hdlt (X n).2 dn
  have hforward := closedTube_forwardOrbit hTB hinv
  have horbit : ∀ n, range (Y (n + 1)) =
      range (UnitTangent.unitTangentMap (Y n)) := by
    intro n
    change range (ev (X (n + 1)).1) = _
    rw [← hforward n]
    exact hTev (X n)
  have htail0 : 0 ≤ ShadowingTails.tail d 0 := ShadowingTails.tail_nonneg
    (fun n => by simpa using le_trans dist_nonneg (hstep n 0)) 0
  have hdistData : dist (Q 0).1 (X 0).1 ≤ Csh * ShadowingTails.tail d 0 := by
    calc
      dist (Q 0).1 (X 0).1 = dist (Q 0) (X 0) := rfl
      _ ≤ ShadowingTails.tail d 0 := hdist 0
      _ ≤ Csh * ShadowingTails.tail d 0 := by nlinarith
  have hdistXQ : dist (X 0).1 (Q 0).1 ≤ Csh * ShadowingTails.tail d 0 := by
    rw [dist_comm]
    exact hdistData
  have hXR : range (Y 0) = range (⇑(X 0).1.1) := MarkedSpace.range_ev hc (X 0).2
  have hQR : range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0)) =
      range (⇑(Q 0).1.1) := by
    rw [← hQfront 0]
    exact MarkedSpace.range_ev hc (Q 0).2
  have hhaus : hausdorffDist (range (Y 0))
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤
      Csh * ShadowingTails.tail d 0 := by
    rw [hXR, hQR]
    refine CurveDistance.hausdorffDist_range_le
      (mul_nonneg (by linarith) htail0) fun u => ?_
    have h1 : ‖(X 0).1.1 u - (Q 0).1.1 u‖ ≤ Csh * ShadowingTails.tail d 0 :=
      (MarkedSpace.dist_apply_le (X 0).1 (Q 0).1 u).trans hdistXQ
    simpa [dist_eq_norm] using h1
  have hperim : 2 * Hs 0 - Csh * ShadowingTails.tail d 0 ≤ LY := by
    have hp := MarkedSpace.abs_perim_sub_le_dist (X 0).1 (Q 0).1
    have hlo := (abs_le.mp (hp.trans hdistXQ)).1
    dsimp [LY]
    rw [hQperim] at hlo
    linarith
  exact ⟨Y, LY, hoval, horbit, MarkedSpace.perim_pos hc (X 0).2,
    MarkedSpace.periodic_ev hc (X 0).2, hhaus, hperim⟩


/-- Completeness step for variable-speed shadowing.  It deliberately asks
only for the marked distance between consecutive terminal pullbacks.  Hence
`InterpolationVariableSpeedSelInvAdapter` can supply the step estimate without
converting its nonaffine rear marking into the constant-speed path predicate
hard-coded by the older `TubePullbackLimit.exists_shadowing_limit`.

The two hypotheses not supplied by completeness are now visible: `hstep` is
the propagated variable-speed defect estimate and `hmem` is shrinking-tube
invariance. -/
theorem exists_markedLimit_of_summable_pullbackSteps
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ} {c dlt : ℝ}
    (hsum : Summable d)
    (hstep : ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ d (n + k))
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → MarkedSpace.Data,
      (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n, dist (Q n) (X n) ≤ ShadowingTails.tail d n) := by
  have hlim : ∀ n, ∃ x : MarkedSpace.Data,
      Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 x) ∧
      ∀ k, dist (TubePullbackLimit.pullback B Q n k) x ≤
        ShadowingTails.tail d (n + k) := by
    intro n
    simpa [ShadowingTails.tail, add_assoc] using
      (ShadowingTails.exists_limit_of_summable_increments
        (Z := TubePullbackLimit.pullback B Q n)
        (d := fun k => d (n + k)) (C := 1)
        (ShadowingTails.summable_shift hsum n)
        (fun k => by simpa using hstep n k))
  choose X hXlim hXdist using hlim
  have hXmem : ∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n) := by
    intro n
    exact (MarkedSpace.isClosed_tube c 0 dlt).mem_of_tendsto (hXlim n)
      (Eventually.of_forall (hmem n))
  have hinv : ∀ n, X n = B (X (n + 1)) := by
    intro n
    have hshift : Tendsto
        (fun k => TubePullbackLimit.pullback B Q n (k + 1)) atTop (𝓝 (X n)) :=
      (hXlim n).comp (tendsto_add_atTop_nat 1)
    have hBlim : Tendsto
        (fun k => B (TubePullbackLimit.pullback B Q (n + 1) k)) atTop
        (𝓝 (B (X (n + 1)))) :=
      (hBcont.tendsto _).comp (hXlim (n + 1))
    have heq : (fun k => TubePullbackLimit.pullback B Q n (k + 1)) =
        fun k => B (TubePullbackLimit.pullback B Q (n + 1) k) :=
      funext fun k => TubePullbackLimit.pullback_succ B Q n k
    rw [heq] at hshift
    exact tendsto_nhds_unique hshift hBlim
  refine ⟨X, hXmem, hXlim, hinv, fun n => ?_⟩
  simpa using hXdist n 0

/-- **Hybrid gauge/canonical pullback completeness.**  The recursively
transported variable-speed path may terminate at a gauge-marked datum `G n k`.
Its C² endpoint increment and the metric correction from `G n k` to the next
canonical pullback are kept separate.  Their triangle sum is enough for
completeness and preserves the exact inverse identity; no normal path realizing
the marking correction is required. -/
theorem exists_markedLimit_of_summable_hybrid_pullbackSteps
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {G : ℕ → ℕ → MarkedSpace.Data} {a b : ℕ → ℝ} {c dlt : ℝ}
    (hsumA : Summable a) (hsumB : Summable b)
    (hgauge : ∀ n k, dist (TubePullbackLimit.pullback B Q n k) (G n k)
      ≤ a (n + k))
    (hcanonical : ∀ n k, dist (G n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ b (n + k))
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → MarkedSpace.Data,
      (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n, dist (Q n) (X n) ≤
        ShadowingTails.tail (fun j => a j + b j) n) := by
  refine exists_markedLimit_of_summable_pullbackSteps
    (hsumA.add hsumB) ?_ hmem hBcont
  intro n k
  exact (dist_triangle (TubePullbackLimit.pullback B Q n k) (G n k)
    (TubePullbackLimit.pullback B Q n (k + 1))).trans
      (add_le_add (hgauge n k) (hcanonical n k))

/-- Common-majorant specialization used by the exponentially separated model
sequence.  Both the variable-speed endpoint estimate and the marking-flow
defect are fixed multiples of the same L¹ interpolation majorant, so their
summability follows formally from that of the model defects. -/
theorem exists_markedLimit_of_hybrid_pullbackSteps_of_L1_majorant
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {G : ℕ → ℕ → MarkedSpace.Data} {d : ℕ → ℝ}
    {Cgauge Cmark c dlt : ℝ}
    (hsum : Summable d)
    (hgauge : ∀ n k, dist (TubePullbackLimit.pullback B Q n k) (G n k)
      ≤ Cgauge * d (n + k))
    (hcanonical : ∀ n k, dist (G n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ Cmark * d (n + k))
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → MarkedSpace.Data,
      (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n, dist (Q n) (X n) ≤
        ShadowingTails.tail
          (fun j => Cgauge * d j + Cmark * d j) n) := by
  exact exists_markedLimit_of_summable_hybrid_pullbackSteps
    (hsum.mul_left Cgauge) (hsum.mul_left Cmark) hgauge hcanonical hmem hBcont

/-- Sequence adapter for the actual output of uniform raw gauge transport.
The variable-speed certificate supplies the first endpoint increment, while
the canonical marking estimate supplies the second. -/
theorem exists_markedLimit_of_uniform_gaugePaths_and_marking
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {G : ℕ → ℕ → MarkedSpace.Data} {d : ℕ → ℝ}
    {Cmark c dlt P0 P1 khat G1 Cg : ℝ}
    (hsum : Summable d)
    (hC : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (Gamma : ∀ n k, PathMetric.NormalPath
      (TubePullbackLimit.pullback B Q n k) (G n k))
    (hcost : ∀ n k, PathMetric.NormalPath.cost (Gamma n k) ≤ d (n + k))
    (hgeom : ∀ n k,
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg (Gamma n k))
    (hcanonical : ∀ n k, dist (G n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ Cmark * d (n + k))
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hGmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt (G n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → MarkedSpace.Data,
      (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n, dist (Q n) (X n) ≤ ShadowingTails.tail
        (fun j => NormalPathC2IncrementVariableSpeed.c2ConstVar
            P0 P1 khat G1 Cg * d j + Cmark * d j) n) := by
  apply exists_markedLimit_of_hybrid_pullbackSteps_of_L1_majorant
    hsum (hcanonical := hcanonical) (hmem := hmem) (hBcont := hBcont)
  intro n k
  exact (NormalPathC2IncrementVariableSpeed.dist_le_cost_variableSpeed
    (Gamma n k) (hmem n k).hasDerivAt_curve (hGmem n k).hasDerivAt_curve
    (hmem n k).hasDerivAt_vel (hGmem n k).hasDerivAt_vel (hgeom n k)).trans
      (mul_le_mul_of_nonneg_left (hcost n k) hC)

/-- Raw gauge transport plus its canonical marking correction gives a direct
metric transport estimate.  This is the path-free interface needed for
iteration: the intermediate gauge endpoint is eliminated by triangle. -/
theorem dist_map_le_of_gaugePath_and_marking
    {B : MarkedSpace.Data → MarkedSpace.Data} {p q g : MarkedSpace.Data}
    {P0 P1 khat G1 Cg Cmark : ℝ}
    (Gamma : PathMetric.NormalPath (B p) g)
    (hp : MarkedSpace.IsTubeMember c 0 dlt (B p))
    (hg : MarkedSpace.IsTubeMember c 0 dlt g)
    (hgeom : NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
      P0 P1 khat G1 Cg Gamma)
    (hC : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg)
    (hmark : dist g (B q) ≤ Cmark * PathMetric.NormalPath.cost Gamma) :
    dist (B p) (B q) ≤
      (NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg + Cmark) *
        PathMetric.NormalPath.cost Gamma := by
  calc
    dist (B p) (B q) ≤ dist (B p) g + dist g (B q) := dist_triangle _ _ _
    _ ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg *
          PathMetric.NormalPath.cost Gamma + Cmark * PathMetric.NormalPath.cost Gamma :=
      add_le_add
        (NormalPathC2IncrementVariableSpeed.dist_le_cost_variableSpeed Gamma
          hp.hasDerivAt_curve hg.hasDerivAt_curve hp.hasDerivAt_vel
          hg.hasDerivAt_vel hgeom) hmark
    _ = _ := by ring

/-- Iteration of a direct metric transport estimate.  A base interpolation
defect at level `n+k` is amplified by exactly `Ctransport^k`; no correction
path is constructed or transported. -/
theorem pullbackSteps_of_metric_transport
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ} {Ctransport : ℝ}
    (hC0 : 0 ≤ Ctransport)
    (hB : ∀ x y, dist (B x) (B y) ≤ Ctransport * dist x y)
    (hbase : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ d n) :
    ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤
        Ctransport ^ k * d (n + k) := by
  intro n k
  induction k generalizing n with
  | zero => simpa [TubePullbackLimit.pullback] using hbase n
  | succ k ih =>
      rw [TubePullbackLimit.pullback_succ, TubePullbackLimit.pullback_succ]
      calc
        dist (B (TubePullbackLimit.pullback B Q (n + 1) k))
            (B (TubePullbackLimit.pullback B Q (n + 1) (k + 1))) ≤
            Ctransport * dist (TubePullbackLimit.pullback B Q (n + 1) k)
              (TubePullbackLimit.pullback B Q (n + 1) (k + 1)) := hB _ _
        _ ≤ Ctransport * (Ctransport ^ k * d ((n + 1) + k)) :=
          mul_le_mul_of_nonneg_left (ih (n + 1)) hC0
        _ = Ctransport ^ (k + 1) * d (n + (k + 1)) := by ring

/-- Distance-based weighted pullback limit driven by the direct metric
transport constant. -/
theorem exists_markedLimit_of_metric_transport
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ} {Ctransport c dlt : ℝ}
    (hC0 : 0 ≤ Ctransport) (hC1 : 1 ≤ Ctransport)
    (hweighted : Summable fun j => Ctransport ^ j * d j)
    (hB : ∀ x y, dist (B x) (B y) ≤ Ctransport * dist x y)
    (hbase : ∀ n, dist (Q n) (B (Q (n + 1))) ≤ d n)
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → MarkedSpace.Data,
      (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n, dist (Q n) (X n) ≤
        ShadowingTails.tail (fun j => Ctransport ^ j * d j) n) := by
  apply exists_markedLimit_of_summable_pullbackSteps hweighted ?_ hmem hBcont
  intro n k
  have hd0 : 0 ≤ d (n + k) :=
    le_trans dist_nonneg (hbase (n + k))
  have hp : Ctransport ^ k ≤ Ctransport ^ (n + k) := by
    exact pow_le_pow_right₀ hC1 (Nat.le_add_left k n)
  exact (pullbackSteps_of_metric_transport hC0 hB hbase n k).trans
    (mul_le_mul_of_nonneg_right hp hd0)

/-- **Variable-speed pullback-limit theorem.**  Once the recursively
transported interpolation paths have uniform variable-speed constants, their
weighted cost bounds imply the exact marked pullback increments.  Completeness,
the inverse-orbit identity, and the sharp tail estimate then follow without
pretending that the transported rear paths have constant-speed slices. -/
theorem exists_markedLimit_of_variableSpeed_pullbackPaths
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {e : ℕ → ℝ} {c dlt P0 P1 khat G1 Cg : ℝ}
    (hsum : Summable e)
    (hC : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
      P0 P1 khat G1 Cg)
    (Γ : ∀ n k, PathMetric.NormalPath
      (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)))
    (hcost : ∀ n k, PathMetric.NormalPath.cost (Γ n k) ≤ e (n + k))
    (hgeom : ∀ n k,
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg (Γ n k))
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → MarkedSpace.Data,
      (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n, dist (Q n) (X n) ≤
        ShadowingTails.tail
          (fun j => NormalPathC2IncrementVariableSpeed.c2ConstVar
            P0 P1 khat G1 Cg * e j) n) := by
  let C := NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg
  have hsteps : ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ C * e (n + k) := by
    intro n k
    exact (NormalPathC2IncrementVariableSpeed.dist_le_cost_variableSpeed (Γ n k)
      (hmem n k).hasDerivAt_curve (hmem n (k + 1)).hasDerivAt_curve
      (hmem n k).hasDerivAt_vel (hmem n (k + 1)).hasDerivAt_vel
      (hgeom n k)).trans (mul_le_mul_of_nonneg_left (hcost n k) (by
        simpa [C] using hC))
  simpa [C] using exists_markedLimit_of_summable_pullbackSteps
    (hsum.mul_left C) hsteps hmem hBcont

/-- Recursively transport the base interpolation defects through the selected
rear operator.  The fixed variable-speed certificate is the uniformized form
of the path-dependent `costP1/costG1/Cg` output of
`GaugeRearFamilyFromFront`. -/
theorem exists_variableSpeed_pullbackPath
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ} {K P0 P1 khat G1 Cg : ℝ}
    (hK : 0 ≤ K)
    (hbase : ∀ n, ∃ Λ : PathMetric.NormalPath (Q n) (B (Q (n + 1))),
      PathMetric.NormalPath.cost Λ ≤ d n ∧
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg Λ)
    (htransport : ∀ {p q : MarkedSpace.Data} (Γ : PathMetric.NormalPath p q),
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg Γ →
      ∃ Δ : PathMetric.NormalPath (B p) (B q),
        PathMetric.NormalPath.cost Δ ≤ K * PathMetric.NormalPath.cost Γ ∧
        NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
          P0 P1 khat G1 Cg Δ) :
    ∀ n k, ∃ Γ : PathMetric.NormalPath
        (TubePullbackLimit.pullback B Q n k)
        (TubePullbackLimit.pullback B Q n (k + 1)),
      PathMetric.NormalPath.cost Γ ≤ K ^ k * d (n + k) ∧
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg Γ := by
  intro n k
  induction k generalizing n with
  | zero =>
      simpa [TubePullbackLimit.pullback] using hbase n
  | succ k ih =>
      obtain ⟨Γ, hΓcost, hΓgeom⟩ := ih (n + 1)
      obtain ⟨Δ, hΔcost, hΔgeom⟩ := htransport Γ hΓgeom
      rw [TubePullbackLimit.pullback_succ B Q n k,
        TubePullbackLimit.pullback_succ B Q n (k + 1)]
      refine ⟨Δ, ?_, hΔgeom⟩
      calc
        PathMetric.NormalPath.cost Δ ≤ K * PathMetric.NormalPath.cost Γ := hΔcost
        _ ≤ K * (K ^ k * d ((n + 1) + k)) :=
          mul_le_mul_of_nonneg_left hΓcost hK
        _ = K ^ (k + 1) * d (n + (k + 1)) := by
          rw [show (n + 1) + k = n + (k + 1) by omega]
          ring

/-- Sequence-ready composition of recursive variable-speed transport with the
pullback-limit theorem. -/
theorem exists_markedLimit_of_variableSpeed_transport
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ} {K c dlt P0 P1 khat G1 Cg : ℝ}
    (hK : 0 ≤ K) (hweighted : ∀ n, Summable fun k => K ^ k * d (n + k))
    (hbase : ∀ n, ∃ Λ : PathMetric.NormalPath (Q n) (B (Q (n + 1))),
      PathMetric.NormalPath.cost Λ ≤ d n ∧
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg Λ)
    (htransport : ∀ {p q : MarkedSpace.Data} (Γ : PathMetric.NormalPath p q),
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg Γ →
      ∃ Δ : PathMetric.NormalPath (B p) (B q),
        PathMetric.NormalPath.cost Δ ≤ K * PathMetric.NormalPath.cost Γ ∧
        NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
          P0 P1 khat G1 Cg Δ)
    (hC : 0 ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg)
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k)) (hBcont : Continuous B) :
    ∀ n, ∃ X : MarkedSpace.Data,
      MarkedSpace.IsTubeMember c 0 dlt X ∧
      Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 X) ∧
      dist (Q n) X ≤ ShadowingTails.tail
        (fun k => NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg *
          (K ^ k * d (n + k))) 0 := by
  intro n
  choose Γ hΓcost hΓgeom using
    exists_variableSpeed_pullbackPath hK hbase htransport
  let C := NormalPathC2IncrementVariableSpeed.c2ConstVar P0 P1 khat G1 Cg
  have hstep : ∀ k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤
        C * (K ^ k * d (n + k)) := by
    intro k
    exact (NormalPathC2IncrementVariableSpeed.dist_le_cost_variableSpeed (Γ n k)
      (hmem n k).hasDerivAt_curve (hmem n (k + 1)).hasDerivAt_curve
      (hmem n k).hasDerivAt_vel (hmem n (k + 1)).hasDerivAt_vel
      (hΓgeom n k)).trans
        (mul_le_mul_of_nonneg_left (hΓcost n k) (by simpa [C] using hC))
  obtain ⟨X, hXlim, hXdist⟩ := ShadowingTails.exists_limit_of_summable_increments
    (C := 1) ((hweighted n).mul_left C) (fun k => by simpa using hstep k)
  have hXmem : MarkedSpace.IsTubeMember c 0 dlt X :=
    (MarkedSpace.isClosed_tube c 0 dlt).mem_of_tendsto hXlim
      (Eventually.of_forall (hmem n))
  exact ⟨X, hXmem, hXlim, by simpa using hXdist 0⟩

/-! ### The closed curvature condition inherited by the shadowing limit -/

/-- A one-step interpolation/selected-rear defect propagates through every
number of pullbacks without loss when the selected inverse is nonexpansive.
This is exactly the `hstep` input of `ofPullbackSteps`. -/
theorem pullbackSteps_of_baseDefects
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ}
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y)
    (hbase : ∀ j, dist (Q j) (B (Q (j + 1))) ≤ d j) :
    ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ d (n + k) := by
  intro n k
  simpa [TubePullbackLimit.pullback, ShadowingScheme.pullback] using
    (ShadowingScheme.dist_pullback_succ hB hbase n k)

/-- The sequence-level package consumed by the paper-faithful pullback
constructor: summability is unchanged by propagation. -/
theorem summable_pullbackSteps_of_baseDefects
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ}
    (hsum : Summable d)
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y)
    (hbase : ∀ j, dist (Q j) (B (Q (j + 1))) ≤ d j) :
    Summable d ∧ ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ d (n + k) :=
  ⟨hsum, pullbackSteps_of_baseDefects hB hbase⟩

/-- Normalize the detailed variable-speed gauge bound by the summable L1
matching majorant.  The inequality `raw j <= d j` is exactly the standard
smallness-threshold calculation; after it, no analytic information is lost in
the pullback propagation. -/
theorem summable_pullbackSteps_of_selectedRearBounds
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {raw d : ℕ → ℝ}
    (hsum : Summable d)
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y)
    (hgauge : ∀ j, dist (Q j) (B (Q (j + 1))) ≤ raw j)
    (hL1major : ∀ j, raw j ≤ d j) :
    Summable d ∧ ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ d (n + k) := by
  apply summable_pullbackSteps_of_baseDefects hsum hB
  intro j
  exact (hgauge j).trans (hL1major j)

/-- Exact residual for the closed, nonnegative-curvature tube.  The model
membership and one-step preservation clauses are geometric; once supplied,
all terminal pullbacks remain in the fixed closed tube. -/
structure ClosedTubeInvarianceResidual
    (B : MarkedSpace.Data → MarkedSpace.Data) (Q : ℕ → MarkedSpace.Data)
    (c dlt : ℝ) : Prop where
  model_mem : ∀ n, MarkedSpace.IsTubeMember c 0 dlt (Q n)
  selectedRear_mem : ∀ x, MarkedSpace.IsTubeMember c 0 dlt x →
    MarkedSpace.IsTubeMember c 0 dlt (B x)

/-- Build the exact closed-tube residual for the canonical selected inverse
from pointwise weak-convex marked-rear certificates.  The certificate may be
obtained from nonnegative steering curvature and turning-one embeddedness; no
strict-positive selected-inverse API or universal rear-injectivity hypothesis
is used in this adapter. -/
theorem closedTubeInvarianceResidual_selInv
    {Q : ℕ → MarkedSpace.Data} {kh c dlt : ℝ}
    (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hQ : ∀ n, MarkedSpace.IsTubeMember c 0 dlt (Q n))
    (hweak : ∀ x, MarkedSpace.IsTubeMember c 0 dlt x →
      ∃ q, SelectedInverseMap.IsMarkedSelectedInverse kh x q ∧
        MarkedSpace.IsTubeMember c 0 dlt q) :
    ClosedTubeInvarianceResidual (SelectedInverseMap.selInv kh) Q c dlt := by
  refine ⟨hQ, ?_⟩
  intro x hx
  obtain ⟨q, hq, hqmem⟩ := hweak x hx
  exact SelectedInverseMap.selInv_spec_of_markedRear hc hkh0 hkh1 hx hq hqmem

/-- Feed the finite closed-tube invariance theorem into the dense completion
package.  After this adapter, the only inputs are density and the image-filter
limit furnished by the additive Jacobi/path-cost Cauchy estimate. -/
def selectedInverseDenseCauchyData_of_invariance
    {Q : ℕ → MarkedSpace.Data} {kh c dlt : ℝ}
    (r : ClosedTubeInvarianceResidual (SelectedInverseMap.selInv kh) Q c dlt)
    (hdense : IsDenseInducing
      (positiveToNonnegative (c := c) (dlt := dlt)))
    (hlimit : ∀ b : NonnegativeTube c dlt, ∃ q : NonnegativeTube c dlt,
      Tendsto (fun p : PositiveTube c dlt =>
        (⟨SelectedInverseMap.selInv kh p.1,
          r.selectedRear_mem p.1 (positiveToNonnegative p).2⟩ :
            NonnegativeTube c dlt))
        (Filter.comap positiveToNonnegative (𝓝 b)) (𝓝 q)) :
    SelectedInverseDenseCauchyData kh c dlt :=
  { preserves := fun p =>
      r.selectedRear_mem p.1 (positiveToNonnegative p).2
    denseInducing := hdense
    hasLimit := hlimit }

/-- **Strongest sequence-level `kmin = 0` tube invariance theorem.**

No positive curvature lower bound is used in the induction.  In particular,
the theorem matches the `hmem` field of `ofPullbackSteps` exactly. -/
theorem pullback_mem_closedTube
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {c dlt : ℝ} (r : ClosedTubeInvarianceResidual B Q c dlt) :
    ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k) := by
  intro n k
  induction k generalizing n with
  | zero => simpa [TubePullbackLimit.pullback] using r.model_mem n
  | succ k ih =>
      rw [TubePullbackLimit.pullback, Function.iterate_succ_apply']
      apply r.selectedRear_mem
      have hmem := ih (n + 1)
      simpa [TubePullbackLimit.pullback, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hmem

/-- **Primary paper route: completeness of summable transported normal
paths.**  This is the `kmin = 0` specialization of the pullback construction
used in the TeX proof.  The paths themselves, rather than a globally completed
selected-inverse map on a fixed chord subtype, provide the Cauchy control.

Internally `TubePullbackLimit.exists_shadowing_limit_of_radii` concatenates the
transported paths, bounds their costs by `K^k d_(n+k)`, invokes
`SummableNormalPathLimit.exists_limit_of_summable_costs` (uniform C2
completeness and positive limiting speed), and transfers the inverse identity
by continuity. -/
theorem exists_nonnegative_shadowing_of_summable_normalPaths
    {B : MarkedSpace.Data → MarkedSpace.Data}
    {Q : ℕ → MarkedSpace.Data} {d a : ℕ → ℝ}
    {K c dlt P0 P1 khat : ℝ}
    (hK : 0 ≤ K)
    (hsum : ∀ n, Summable fun k => K ^ k * d (n + k))
    (ha : ∀ n k, ∑ j ∈ Finset.range k, K ^ j * d (n + j) ≤ a n)
    (hmap : ∀ (p q : MarkedSpace.Data) (Γ : PathMetric.NormalPath p q),
      NormalPathC2Increment.IsConstantSpeedNormalPath P0 P1 khat Γ →
      ∃ Δ : PathMetric.NormalPath (B p) (B q),
        PathMetric.NormalPath.cost Δ ≤ K * PathMetric.NormalPath.cost Γ ∧
        NormalPathC2Increment.IsConstantSpeedNormalPath P0 P1 khat Δ)
    (hdefect : ∀ n, ∃ Λ : PathMetric.NormalPath (Q n) (B (Q (n + 1))),
      PathMetric.NormalPath.cost Λ ≤ d n ∧
      NormalPathC2Increment.IsConstantSpeedNormalPath P0 P1 khat Λ)
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B) :
    ∃ X : ℕ → MarkedSpace.Data,
      (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) ∧
      (∀ n, Tendsto (TubePullbackLimit.pullback B Q n) atTop (𝓝 (X n))) ∧
      (∀ n, X n = B (X (n + 1))) ∧
      (∀ n u, ‖(X n).1 u - (Q n).1 u‖ ≤ a n) ∧
      (∀ n, |MarkedSpace.perim (X n) - MarkedSpace.perim (Q n)| ≤
        NormalPathC2Increment.c2Const P0 P1 khat * a n) := by
  obtain ⟨X, hXm, hXlim, hXinv, -, hXpos, -, hXper⟩ :=
    TubePullbackLimit.exists_shadowing_limit_of_radii hK hsum ha hmap hdefect
      hmem hBcont
  exact ⟨X, hXm, hXlim, hXinv, hXpos, hXper⟩

/-- A summable nonnegative defect majorant remains summable after every shift
and after insertion of the pullback weight `K^k`, provided `K ≤ 1`. -/
theorem summable_weighted_shift_of_summable
    {d : ℕ → ℝ} {K : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    (hd0 : ∀ n, 0 ≤ d n) (hdsum : Summable d) :
    ∀ n, Summable fun k => K ^ k * d (n + k) := by
  intro n
  have hshift : Summable fun k => d (n + k) := hdsum.comp_injective
    (add_right_injective n)
  refine hshift.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hK0 _) (hd0 _)) ?_
  intro k
  have hpow : K ^ k ≤ 1 := pow_le_one₀ hK0 hK1
  nlinarith [hd0 (n + k)]

/-- Choose the interpolation defect paths simultaneously and transfer the
summable L¹-derived majorant to their actual costs.  This is the sequence
adapter consumed by `SummableNormalPathLimit` and the weighted pullback
constructor. -/
theorem choose_summable_defect_normalPaths
    {B : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ} {P0 P1 khat : ℝ}
    (hd0 : ∀ n, 0 ≤ d n) (hdsum : Summable d)
    (hex : ∀ n, ∃ Λ : PathMetric.NormalPath (Q n) (B (Q (n + 1))),
      PathMetric.NormalPath.cost Λ ≤ d n ∧
      NormalPathC2Increment.IsConstantSpeedNormalPath P0 P1 khat Λ) :
    ∃ Λ : ∀ n, PathMetric.NormalPath (Q n) (B (Q (n + 1))),
      (∀ n, PathMetric.NormalPath.cost (Λ n) ≤ d n) ∧
      (∀ n, NormalPathC2Increment.IsConstantSpeedNormalPath P0 P1 khat (Λ n)) ∧
      Summable fun n => PathMetric.NormalPath.cost (Λ n) := by
  choose Λ hΛcost hΛgeom using hex
  refine ⟨Λ, hΛcost, hΛgeom, ?_⟩
  exact hdsum.of_nonneg_of_le (fun n => (Λ n).cost_nonneg) hΛcost

theorem model_nonnegative
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 eps : ℕ → ℝ}
    {Cw Csh : ℝ} {dir : ℂ}
    (r : PaperFaithfulAssemblyRemainder kappas Hs theta0 eps Cw Csh dir)
    (n : ℕ) (s : ℝ) : 0 ≤ kappas n s := by
  rw [r.model.curvature_eq n]
  exact (r.model.configs n).KP_nonneg s

/-- Convert the actual output of the marked pullback-limit construction into
the geometric shadowing output used by the paper-faithful capstone.  Thus the
exact orbit, its period, and its model closeness are not assumptions: they are
derived from the marked limit, continuity of the inverse, its right-inverse
identity, and its realization by the unit-tangent map.

The only geometric upgrade left as an input is `hoval`: proving that the
nonnegative-curvature marked limits are smooth strict ovals by regularity gain
and `UnitTangentSpeed.curvature_pos_of_transform_curvature_nonneg`. -/
theorem shadowingOrbit_of_markedLimit
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {B T : MarkedSpace.Data → MarkedSpace.Data} {Q X : ℕ → MarkedSpace.Data}
    {c dlt Csh e0 : ℝ}
    (hc : 0 < c)
    (hQmem : ∀ n, MarkedSpace.IsTubeMember c 0 dlt (Q n))
    (hXmem : ∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n))
    (hQfront : ∀ n, ev (Q n) =
      TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n))
    (hinv : ∀ n, X n = B (X (n + 1)))
    (hTB : ∀ p, T (B p) = p)
    (hTev : ∀ p, range (ev (T p)) =
      range (UnitTangent.unitTangentMap (ev p)))
    (hoval : ∀ n, MainTheoremConditional.IsOval (ev (X n)))
    (hclose : ∀ u, ‖(X 0).1 u - (Q 0).1 u‖ ≤ Csh * e0)
    (hperim : |perim (X 0) - perim (Q 0)| ≤ Csh * e0)
    (hQperim : perim (Q 0) = 2 * Hs 0) :
    ∃ (Y : ℕ → ℝ → ℂ) (LY : ℝ),
      (∀ n, MainTheoremConditional.IsOval (Y n)) ∧
      (∀ n, range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n))) ∧
      0 < LY ∧ Periodic (Y 0) LY ∧
      hausdorffDist (range (Y 0))
        (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤ Csh * e0 ∧
      2 * Hs 0 - Csh * e0 ≤ LY := by
  let Y : ℕ → ℝ → ℂ := fun n => ev (X n)
  let LY := perim (X 0)
  have hLY : 0 < LY := MarkedSpace.perim_pos hc (hXmem 0)
  have hYper : Periodic (Y 0) LY := MarkedSpace.periodic_ev hc (hXmem 0)
  have horbit : ∀ n,
      range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n)) := by
    intro n
    have hforward : T (X n) = X (n + 1) :=
      TubePullbackLimit.forward_orbit_of_inverse_orbit hTB hinv n
    show range (ev (X (n + 1))) = range (UnitTangent.unitTangentMap (ev (X n)))
    rw [← hforward]
    exact hTev (X n)
  have hXR : range (Y 0) = range (⇑(X 0).1) :=
    MarkedSpace.range_ev hc (hXmem 0)
  have hQR : range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0)) =
      range (⇑(Q 0).1) := by
    rw [← hQfront 0]
    exact MarkedSpace.range_ev hc (hQmem 0)
  have hhaus : hausdorffDist (range (Y 0))
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤ Csh * e0 := by
    rw [hXR, hQR]
    refine CurveDistance.hausdorffDist_range_le
      (le_trans (norm_nonneg _) (hclose 0)) fun u => ?_
    simpa [dist_eq_norm] using hclose u
  have hperiodLower : 2 * Hs 0 - Csh * e0 ≤ LY := by
    rw [← hQperim]
    have := (abs_le.mp hperim).1
    dsimp [LY]
    linarith
  exact ⟨Y, LY, hoval, horbit, hLY, hYper, hhaus, hperiodLower⟩

/-- Assemble the regularizing-shadowing output from summable propagated
variable-speed defects.  This theorem factors the remaining paper proof into
exactly three theorem-level inputs:

* `hstep`: propagation of the interpolation defect through `k` selected
  inverse steps;
* `hmem`: invariance of the shrinking nonnegative-curvature/chord-arc tubes;
* `hregularity`: the differentiable intrinsic-curvature data supplied by the
  selected-inverse regularity gain.

Completeness, strict convexity, the exact inverse and forward orbit identities,
the shadowing tail estimate, period control, and Hausdorff closing bound are
all derived. -/
theorem shadowingOrbit_of_summable_pullbackSteps
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {B T : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ} {c dlt Csh : ℝ}
    (hc : 0 < c) (hCsh : 1 ≤ Csh) (hsum : Summable d)
    (hstep : ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ d (n + k))
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B)
    (hQfront : ∀ n, ev (Q n) =
      TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n))
    (hTB : ∀ p, T (B p) = p)
    (hTev : ∀ p, range (ev (T p)) =
      range (UnitTangent.unitTangentMap (ev p)))
    (hregularity : ∀ X : ℕ → MarkedSpace.Data,
      (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) →
      (∀ n, X n = B (X (n + 1))) →
      ∀ n, Nonempty (LimitStrictnessData (X n)))
    (hdlt : 0 < dlt)
    (hQperim : perim (Q 0) = 2 * Hs 0) :
    ∃ (Y : ℕ → ℝ → ℂ) (LY : ℝ),
      (∀ n, MainTheoremConditional.IsOval (Y n)) ∧
      (∀ n, range (Y (n + 1)) = range (UnitTangent.unitTangentMap (Y n))) ∧
      0 < LY ∧ Periodic (Y 0) LY ∧
      hausdorffDist (range (Y 0))
        (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) ≤
          Csh * ShadowingTails.tail d 0 ∧
      2 * Hs 0 - Csh * ShadowingTails.tail d 0 ≤ LY := by
  obtain ⟨X, hXmem, -, hinv, hdist⟩ :=
    exists_markedLimit_of_summable_pullbackSteps hsum hstep hmem hBcont
  have hQmem : ∀ n, MarkedSpace.IsTubeMember c 0 dlt (Q n) := by
    intro n
    simpa [TubePullbackLimit.pullback] using hmem n 0
  have htail0 : 0 ≤ ShadowingTails.tail d 0 :=
    ShadowingTails.tail_nonneg (fun n => by
      simpa using le_trans dist_nonneg (hstep n 0)) 0
  have hclose : ∀ u, ‖(X 0).1 u - (Q 0).1 u‖ ≤
      Csh * ShadowingTails.tail d 0 := by
    intro u
    calc
      ‖(X 0).1 u - (Q 0).1 u‖ ≤ dist (X 0) (Q 0) :=
        MarkedSpace.dist_apply_le (X 0) (Q 0) u
      _ = dist (Q 0) (X 0) := dist_comm _ _
      _ ≤ ShadowingTails.tail d 0 := hdist 0
      _ ≤ Csh * ShadowingTails.tail d 0 := by nlinarith
  have hperim : |perim (X 0) - perim (Q 0)| ≤
      Csh * ShadowingTails.tail d 0 := by
    calc
      |perim (X 0) - perim (Q 0)| ≤ dist (X 0) (Q 0) :=
        MarkedSpace.abs_perim_sub_le_dist _ _
      _ = dist (Q 0) (X 0) := dist_comm _ _
      _ ≤ ShadowingTails.tail d 0 := hdist 0
      _ ≤ Csh * ShadowingTails.tail d 0 := by nlinarith
  have hoval : ∀ n, MainTheoremConditional.IsOval (ev (X n)) := fun n => by
    obtain ⟨dn⟩ := hregularity X hXmem hinv n
    exact isOval_ev_of_limitStrictnessData hc hdlt (hXmem n) dn
  exact shadowingOrbit_of_markedLimit hc hQmem hXmem hQfront hinv hTB hTev
    hoval hclose hperim hQperim

/-- Smart constructor which fills the paper-faithful capstone's shadowing
field from the marked pullback scheme. -/
def ofPullbackSteps
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 eps : ℕ → ℝ}
    {Cw Csh : ℝ} {dir : ℂ}
    {B T : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ} {c dlt : ℝ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (hceiling : model.kstar < 1) (hstrict : ∀ n s, 0 < kappas n s)
    (hc : 0 < c) (hCsh : 1 ≤ Csh) (hsum : Summable d)
    (hstep : ∀ n k, dist (TubePullbackLimit.pullback B Q n k)
      (TubePullbackLimit.pullback B Q n (k + 1)) ≤ d (n + k))
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hBcont : Continuous B)
    (hQfront : ∀ n, ev (Q n) =
      TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n))
    (hTB : ∀ p, T (B p) = p)
    (hTev : ∀ p, range (ev (T p)) =
      range (UnitTangent.unitTangentMap (ev p)))
    (hregularity : ∀ X : ℕ → MarkedSpace.Data,
      (∀ n, MarkedSpace.IsTubeMember c 0 dlt (X n)) →
      (∀ n, X n = B (X (n + 1))) →
      ∀ n, Nonempty (LimitStrictnessData (X n)))
    (hdlt : 0 < dlt)
    (hQperim : perim (Q 0) = 2 * Hs 0)
    (hdir : ‖dir‖ = 1)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail d 0) <
      (2 * Hs 0 - Csh * ShadowingTails.tail d 0) / Real.pi) :
    PaperFaithfulAssemblyRemainder kappas Hs theta0 eps Cw Csh dir :=
  { model := model
    shadow_error := ShadowingTails.tail d 0
    shadow_error_nonneg := ShadowingTails.tail_nonneg (fun n => by
      simpa using le_trans dist_nonneg (hstep n 0)) 0
    shadow_factor_nonneg := le_trans zero_le_one hCsh
    direction_unit := hdir
    model_width := hwidth
    transverse_gap := hgap
    shadowing_orbit := shadowingOrbit_of_summable_pullbackSteps hc hCsh hsum hstep
      hmem hBcont hQfront hTB hTev hregularity hdlt hQperim }

/-- Paper-specific specialization of `ofPullbackSteps` to the canonical
selected inverse.  No nonexpansiveness in the marked metric is assumed: the
propagated estimate `hstep` may contain the actual Jacobi/path-cost factor and
is only required to be summable through `d`. -/
def ofSelectedInversePullbackSteps
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 eps : ℕ → ℝ}
    {Cw Csh kh : ℝ} {dir : ℂ}
    {T : MarkedSpace.Data → MarkedSpace.Data} {Q : ℕ → MarkedSpace.Data}
    {d : ℕ → ℝ} {c dlt : ℝ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (hceiling : model.kstar < 1) (hstrict : ∀ n s, 0 < kappas n s)
    (hc : 0 < c) (hCsh : 1 ≤ Csh) (hsum : Summable d)
    (hstep : ∀ n k,
      dist (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k)
        (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n (k + 1)) ≤
          d (n + k))
    (hmem : ∀ n k, MarkedSpace.IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k))
    (hBcont : Continuous (SelectedInverseMap.selInv kh))
    (hQfront : ∀ n, ev (Q n) =
      TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n))
    (hTB : ∀ p, T (SelectedInverseMap.selInv kh p) = p)
    (hTev : ∀ p, range (ev (T p)) =
      range (UnitTangent.unitTangentMap (ev p)))
    (hregularity : SelectedInverseLimitRegularity kh c dlt)
    (hdlt : 0 < dlt)
    (hQperim : perim (Q 0) = 2 * Hs 0)
    (hdir : ‖dir‖ = 1)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail d 0) <
      (2 * Hs 0 - Csh * ShadowingTails.tail d 0) / Real.pi) :
    PaperFaithfulAssemblyRemainder kappas Hs theta0 eps Cw Csh dir :=
  ofPullbackSteps model hceiling hstrict hc hCsh hsum hstep hmem hBcont
    hQfront hTB hTev hregularity hdlt hQperim hdir hwidth hgap

/-- Final paper-specific constructor using the completed selected inverse as a
continuous self-map of the closed tube.  No total `Data → Data` fallback and
no global continuity hypothesis occur. -/
def ofCompletedSelectedInverseSteps
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 eps : ℕ → ℝ}
    {Cw Csh kh c dlt : ℝ} {dir : ℂ}
    (model : ConfiguredModelSequence kappas Hs eps)
    (completion : SelectedInverseSelfCompletionData kh c dlt)
    {T : NonnegativeTube c dlt → NonnegativeTube c dlt}
    {Q : ℕ → NonnegativeTube c dlt} {d : ℕ → ℝ}
    (hceiling : model.kstar < 1) (hstrict : ∀ n s, 0 < kappas n s)
    (hc : 0 < c) (hdlt : 0 < dlt) (hCsh : 1 ≤ Csh) (hsum : Summable d)
    (hstep : ∀ n k,
      dist (closedPullback completion.closedSelInv Q n k)
        (closedPullback completion.closedSelInv Q n (k + 1)) ≤ d (n + k))
    (hTB : ∀ p, T (completion.closedSelInv p) = p)
    (hTev : ∀ p, range (ev (T p).1) =
      range (UnitTangent.unitTangentMap (ev p.1)))
    (hQfront : ∀ n, ev (Q n).1 =
      TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n))
    (hregularity : ∀ X : ℕ → NonnegativeTube c dlt,
      (∀ n, X n = completion.closedSelInv (X (n + 1))) →
      ∀ n, Nonempty (LimitStrictnessData (X n).1))
    (hQperim : perim (Q 0).1 = 2 * Hs 0)
    (hdir : ‖dir‖ = 1)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail d 0) <
      (2 * Hs 0 - Csh * ShadowingTails.tail d 0) / Real.pi) :
    PaperFaithfulAssemblyRemainder kappas Hs theta0 eps Cw Csh dir :=
  { model := model
    shadow_error := ShadowingTails.tail d 0
    shadow_error_nonneg := ShadowingTails.tail_nonneg (fun n => by
      simpa using le_trans dist_nonneg (hstep n 0)) 0
    shadow_factor_nonneg := le_trans zero_le_one hCsh
    direction_unit := hdir
    model_width := hwidth
    transverse_gap := hgap
    shadowing_orbit := shadowingOrbit_of_closedTubeSteps hc hdlt hCsh hsum hstep
      completion.continuous_closedSelInv hTB hTev hQfront hregularity hQperim }

/-- Paper-faithful final assembly, with no fixed positive lower curvature
parameter. -/
theorem conclude
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 eps : ℕ → ℝ}
    {Cw Csh : ℝ} {dir : ℂ}
    (r : PaperFaithfulAssemblyRemainder kappas Hs theta0 eps Cw Csh dir) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX := by
  obtain ⟨X, LX, hoval, horbit, hLX, hXper, hhaus, hperim⟩ := r.shadowing_orbit
  have hQcont : Continuous
      (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0)) :=
    Differentiable.continuous fun s =>
      (TwoCapPairsAssembly.front_hasDerivAt
        (theta0 := theta0 0) (H := Hs 0) (r.model.curvature_continuous 0) s).differentiableAt
  have hQper : Periodic
      (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0)) (2 * Hs 0) :=
    TwoCapPairsAssembly.front_periodic (r.model.curvature_continuous 0)
      (r.model.curvature_periodic 0) (r.model.total_turning 0)
  have hnot := ClosingArgument.not_isCircleOfPerimeter_of_hausdorffDist_le
    (range_nonempty (X 0))
    (range_nonempty (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0)))
    (CurveDistance.isBounded_range_of_periodic
      (MainTheoremConditional.IsOval.continuous (hoval 0)) hXper hLX)
    (CurveDistance.isBounded_range_of_periodic hQcont hQper
      (by linarith [r.model.separation_pos 0]))
    r.direction_unit hhaus r.model_width hperim r.transverse_gap
  exact ⟨X, LX, hoval, horbit, hLX, hXper, hnot⟩

end PaperFaithfulAssemblyRemainder

/-- Smart constructor for the capstone from a coherent paper model sequence.
It eliminates the five model-curvature fields and period positivity which are
already theorems of `ModelOrbitDefect.Config`.  The remaining arguments are
precisely the uniform positive pinching, quantitative tail/width estimates,
and the marked selected-inverse bridge. -/
def UnconditionalAssemblyRemainder.ofConfiguredModel
    {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin Cw Csh kb M : ℝ} {eps cw P : ℕ → ℝ} {dir : ℂ}
    (m : ConfiguredModelSequence kappas Hs eps)
    {B T : tube (2 * Hs 0) kmin
      (ModelChordArc.modelChordConst kmin m.kstar (Hs 0) * (2 * Hs 0)) →
      tube (2 * Hs 0) kmin
        (ModelChordArc.modelChordConst kmin m.kstar (Hs 0) * (2 * Hs 0))}
    (hkmin : 0 < kmin) (hlower : ∀ n s, kmin ≤ kappas n s)
    (hB : ∀ x y, dist (B x) (B y) ≤ dist x y) (hBc : Continuous B)
    (hT : ∀ x, T (B x) = x)
    (hTev : ∀ x, range (ev ((T x : Data))) =
      range (UnitTangent.unitTangentMap (ev ((x : Data)))))
    (hM : 0 < M) (hP : ∀ n, 0 < P n)
    (hsum : Summable fun n =>
      l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 * (1 + kb * (2 * Hs n)))
    (hbridge : ∀ (n : ℕ) (p q : tube (2 * Hs 0) kmin
        (ModelChordArc.modelChordConst kmin m.kstar (Hs 0) * (2 * Hs 0))),
      ev ((p : Data)) = TwoCapPairsAssembly.front (kappas n) (theta0 n) (Hs n) →
      ev ((q : Data)) = TwoCapPairsAssembly.front (kappas (n + 1)) (theta0 (n + 1)) (Hs (n + 1)) →
      perim ((p : Data)) = 2 * Hs n ∧ perim ((B q : Data)) = 2 * Hs n ∧
      ∃ Θp Θq kp kq kp' kq' : ℝ → ℝ,
        (∀ s, HasDerivAt (ev ((p : Data))) (Complex.exp (Complex.I * (Θp s : ℂ))) s) ∧
        (∀ s, HasDerivAt (ev ((B q : Data))) (Complex.exp (Complex.I * (Θq s : ℂ))) s) ∧
        (∀ s, HasDerivAt Θp (kp s) s) ∧ (∀ s, HasDerivAt Θq (kq s) s) ∧
        ev ((p : Data)) 0 = ev ((B q : Data)) 0 ∧ Θp 0 = Θq 0 ∧
        Periodic kp (P n) ∧ Periodic kq (P n) ∧
        (∀ x, HasDerivAt kp (kp' x) x) ∧ (∀ x, HasDerivAt kq (kq' x) x) ∧
        (∀ x, |kp' x| ≤ M / 2) ∧ (∀ x, |kq' x| ≤ M / 2) ∧
        (∫ x in (cw n)..(cw n + P n), |kp x - kq x|) ≤ eps n ∧
        (∀ s, |kq s| ≤ kb))
    (hCsh : 1 ≤ Csh) (hdir : ‖dir‖ = 1)
    (hwidth : Width.width
      (range (TwoCapPairsAssembly.front (kappas 0) (theta0 0) (Hs 0))) dir ≤ Cw)
    (hgap : Cw + 2 * (Csh * ShadowingTails.tail
        (fun n => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 *
          (1 + kb * (2 * Hs n))) 0) <
      (2 * Hs 0 - Csh * ShadowingTails.tail
        (fun n => l1Modulus M (eps n) (P n) * (2 * Hs n) ^ 2 *
          (1 + kb * (2 * Hs n))) 0) / Real.pi) :
    UnconditionalAssemblyRemainder kappas Hs theta0 kmin m.kstar Cw Csh kb M
      eps cw P dir B T :=
  { alpha := m.alpha, beta := m.beta, a := m.a, au := m.au, C := m.C,
    CU := m.CU, CK := m.CK, DU := m.DU, DU2 := m.DU2, D := m.D,
    Km := m.Km, Kd := m.Kd, Bcell := m.Bcell, thetaBase := m.thetaBase,
    kstar := m.kstar, kd := m.kd, configs := m.configs,
    config_from_paper := m.config_from_paper, kmin_pos := hkmin,
    separation_pos := m.separation_pos, separation_mono := m.separation_mono,
    curvature_continuous := m.curvature_continuous,
    curvature_periodic := m.curvature_periodic, curvature_lower := hlower,
    curvature_upper := m.curvature_upper, total_turning := m.total_turning,
    selected_inverse_nonexpansive := hB, selected_inverse_continuous := hBc,
    front_right_inverse := hT, front_realizes_unit_tangent := hTev,
    derivative_bound_pos := hM, rear_period_pos := hP,
    marked_defect_summable := hsum, marked_interpolation_defect := hbridge,
    shadow_factor := hCsh, direction_unit := hdir, model_width := hwidth,
    transverse_gap := hgap }

/-- Legacy fixed-positive-tube endpoint.  It is not the paper-faithful route
for an expanding hairpin sequence; use
`PaperFaithfulAssemblyRemainder.conclude` for the paper's quantifiers. -/
theorem conclude {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {kmin kap Cw Csh kb M : ℝ} {eps cw P : ℕ → ℝ} {dir : ℂ}
    {B T : tube (2 * Hs 0) kmin
      (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0)) →
      tube (2 * Hs 0) kmin
        (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0))}
    (r : UnconditionalAssemblyRemainder kappas Hs theta0 kmin kap Cw Csh kb M
      eps cw P dir B T) :
    ∃ (X : ℕ → ℝ → ℂ) (LX : ℝ),
      (∀ n, MainTheoremConditional.IsOval (X n)) ∧
      (∀ n, range (X (n + 1)) = range (UnitTangent.unitTangentMap (X n))) ∧
      0 < LX ∧ Periodic (X 0) LX ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (X 0)) LX :=
  MarkedSpace.unit_tangent_iterates_main_theorem
    r.kmin_pos r.separation_pos r.separation_mono r.curvature_continuous
    r.curvature_periodic r.curvature_lower r.curvature_upper r.total_turning
    r.selected_inverse_nonexpansive r.selected_inverse_continuous
    r.front_right_inverse r.front_realizes_unit_tangent r.derivative_bound_pos
    r.rear_period_pos r.marked_defect_summable r.marked_interpolation_defect
    r.shadow_factor r.direction_unit r.model_width r.transverse_gap

end UnconditionalAssembly
