import UnitTangentIterates.GaugeRearFamilyVariableTerminal
import UnitTangentIterates.PhysicalRearLimitCurvatureClosure
import UnitTangentIterates.VariableMarkedPhysicalLength

/-!
# Compactness closure for terminal gauge markings

For one fixed triangular row, the canonical arclength data and the actual
gauge-marked endpoints converge in marked `C2`.  The missing scalar
compactness input is isolated here: the normalized marking maps and their
first derivatives have a common pointwise `C1` limit.  From that input, all
of the reparametrization identities, the degree-one shift law, the derivative
bounds, and surjectivity pass to the limit.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace

namespace GaugeRearFamilyVariableTerminal

/-- The one honest residual in compactness of a fixed row's normalized
marking maps.  The finite maps, their bounds, and their normalization remain
outside this structure.  This structure only selects their pointwise `C1`
limit and records the derivative closure which does not follow from marked
`C2` convergence of the curves alone. -/
structure NormalizedMarkingC1Limit
    {baseN rearN : ℕ → Data} {lambda Lambda : ℝ}
    (R : ∀ k, OrientedReparametrization (baseN k) (rearN k) lambda Lambda) where
  psi : ℝ → ℝ
  dpsi : ℝ → ℝ
  psi_tendsto : ∀ u,
    Tendsto (fun k => (R k).psi u) atTop (nhds (psi u))
  dpsi_tendsto : ∀ u,
    Tendsto (fun k => (R k).dpsi u) atTop (nhds (dpsi u))
  hasDerivAt : ∀ u, HasDerivAt psi (dpsi u) u
  dpsi_continuous : Continuous dpsi

/-- Restriction of a normalized marking derivative to one compact period. -/
def markingDerivativeOnUnit
    {base rear : Data} {lambda Lambda : ℝ}
    (R : OrientedReparametrization base rear lambda Lambda)
    {ddpsi : ℝ → ℝ} (hddpsi : ∀ u, HasDerivAt R.dpsi (ddpsi u) u) :
    BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun u => R.dpsi u.1,
      (Differentiable.continuous fun x => (hddpsi x).differentiableAt).comp
        continuous_subtype_val⟩

@[simp] theorem markingDerivativeOnUnit_apply
    {base rear : Data} {lambda Lambda : ℝ}
    (R : OrientedReparametrization base rear lambda Lambda)
    {ddpsi : ℝ → ℝ} (hddpsi : ∀ u, HasDerivAt R.dpsi (ddpsi u) u)
    (u : Set.Icc (0 : ℝ) 1) :
    markingDerivativeOnUnit R hddpsi u = R.dpsi u.1 := rfl

/-- Differentiating the degree-one shift law makes the normalized marking
derivative one-periodic. -/
theorem markingDerivative_periodic
    {base rear : Data} {lambda Lambda : ℝ}
    (R : OrientedReparametrization base rear lambda Lambda)
    (hpsi : ∀ u, HasDerivAt R.psi (R.dpsi u) u) :
    Periodic R.dpsi 1 := by
  intro u
  have hleft : HasDerivAt (fun x => R.psi (x + 1)) (R.dpsi (u + 1)) u := by
    simpa [Function.comp_def] using
      (hpsi (u + 1)).comp u ((hasDerivAt_id u).add_const 1)
  have heq : (fun x => R.psi (x + 1)) = fun x => R.psi x + 1 := by
    funext x
    exact R.translate x
  rw [heq] at hleft
  exact hleft.unique ((hpsi u).add_const 1)

/-- A generic periodic version of compact-period sup convergence. -/
theorem tendstoUniformly_periodicExtension
    {fN : ℕ → ℝ → ℝ}
    (hperiodic : ∀ n, Periodic (fN n) 1)
    (hcontinuous : ∀ n, Continuous (fN n))
    (f : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ)
    (hconv : Tendsto
      (fun n => BoundedContinuousFunction.mkOfCompact
        ⟨fun u : Set.Icc (0 : ℝ) 1 => fN n u.1,
          (hcontinuous n).comp continuous_subtype_val⟩)
      atTop (nhds f)) :
    TendstoUniformly fN (PathMetric.unitPeriodicExtension f) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have hev := (Metric.tendsto_nhds.1 hconv) eps heps
  filter_upwards [hev] with n hn
  intro x
  let u : Set.Icc (0 : ℝ) 1 :=
    ⟨toIcoMod one_pos 0 x,
      Set.Ico_subset_Icc_self (by simpa using toIcoMod_mem_Ico one_pos 0 x)⟩
  have hrepr : fN n x = fN n u.1 := by
    have hmod := (toIcoMod_eq_iff one_pos).1
      (show toIcoMod one_pos 0 x = u.1 from rfl)
    obtain ⟨z, hz⟩ := hmod.2
    rw [hz]
    simpa using ((hperiodic n).zsmul z u.1)
  rw [hrepr]
  change dist (f u)
      (BoundedContinuousFunction.mkOfCompact
        ⟨fun v : Set.Icc (0 : ℝ) 1 => fN n v.1,
          (hcontinuous n).comp continuous_subtype_val⟩ u) < eps
  exact (BoundedContinuousFunction.dist_coe_le_dist u).trans_lt (by
    simpa [dist_comm] using hn)

/-- Uniform convergence permits passage to a fixed finite interval integral. -/
theorem tendsto_intervalIntegral_of_tendstoUniformly
    {fN : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hfN : ∀ n, Continuous (fN n)) (hf : Continuous f)
    (hconv : TendstoUniformly fN f atTop) (a b : ℝ) :
    Tendsto (fun n => ∫ t in a..b, fN n t) atTop
      (nhds (∫ t in a..b, f t)) := by
  apply Metric.tendsto_atTop.2
  intro eps heps
  let A := |b - a|
  let eta := eps / (A + 1)
  have hA : 0 ≤ A := abs_nonneg _
  have hA1 : 0 < A + 1 := by dsimp [A]; linarith
  have heta : 0 < eta := div_pos heps hA1
  have hev := (Metric.tendstoUniformly_iff.1 hconv) eta heta
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hev
  refine ⟨n0, fun n hn => ?_⟩
  have hnclose := hn0 n hn
  have heq : (∫ t in a..b, fN n t) - ∫ t in a..b, f t =
      ∫ t in a..b, fN n t - f t := by
    simpa using (intervalIntegral.integral_sub
      (μ := MeasureTheory.volume) ((hfN n).intervalIntegrable a b)
      (hf.intervalIntegrable a b)).symm
  rw [Real.dist_eq, heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => fN n t - f t) (C := eta) (a := a) (b := b)
    (fun t _ => by
      rw [Real.norm_eq_abs]
      exact le_of_lt (by
        simpa [Real.dist_eq, abs_sub_comm] using hnclose t))
  rw [Real.norm_eq_abs] at hb
  refine hb.trans_lt ?_
  calc
    eta * |b - a| = eta * A := rfl
    _ < eta * (A + 1) := mul_lt_mul_of_pos_left (lt_add_one A) heta
    _ = eps := by
      dsimp [eta]
      exact div_mul_cancel₀ eps hA1.ne'

/-- Arzela--Ascoli on the marking derivatives, followed by periodic extension
and integration from the normalized basepoint, constructs a compatible `C1`
limit along one subsequence. -/
theorem exists_normalizedMarkingC1Limit_subseq
    {baseN rearN : ℕ → Data} {lambda Lambda N : ℝ}
    (hN : 0 ≤ N)
    (R : ∀ k, OrientedReparametrization (baseN k) (rearN k) lambda Lambda)
    (hzero : ∀ k, (R k).psi 0 = 0)
    (hpsi : ∀ k u, HasDerivAt (R k).psi ((R k).dpsi u) u)
    (ddpsi : ℕ → ℝ → ℝ)
    (hddpsi : ∀ k u, HasDerivAt (R k).dpsi (ddpsi k u) u)
    (hddBound : ∀ k u, |ddpsi k u| ≤ N) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Nonempty (NormalizedMarkingC1Limit (fun n => R (phi n))) := by
  let C : NNReal := Real.toNNReal N
  let f : ℕ → BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ :=
    fun n => markingDerivativeOnUnit (R n) (hddpsi n)
  let A : Set (BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) := range f
  have hLip : ∀ n, LipschitzWith C ((R n).dpsi) := by
    intro n
    refine lipschitzWith_of_nnnorm_deriv_le
      (fun u => (hddpsi n u).differentiableAt) (fun u => ?_)
    rw [(hddpsi n u).deriv, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _ hN, Real.norm_eq_abs]
    exact hddBound n u
  have hLipUnit : ∀ n, LipschitzWith C (f n) := by
    intro n
    convert (hLip n).comp (LipschitzWith.subtype_val _) using 1 <;>
      simp [f, Function.comp_def]
  have hEq : Equicontinuous ((↑) : A → Set.Icc (0 : ℝ) 1 → ℝ) := by
    let pick : A → ℕ := fun g => Classical.choose g.2
    have hpick : ∀ g : A, f (pick g) = g.1 := fun g => Classical.choose_spec g.2
    have hbase :=
      (LipschitzWith.uniformEquicontinuous (fun n => ⇑(f n)) C hLipUnit).equicontinuous.comp pick
    convert hbase using 1
    funext g u
    change g.1 u = f (pick g) u
    rw [hpick g]
  have hlambdaLambda : lambda ≤ Lambda :=
    ((R 0).lower 0).trans ((R 0).upper 0)
  have hRange : ∀ (g : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ)
      (u : Set.Icc (0 : ℝ) 1), g ∈ A → g u ∈ Set.Icc lambda Lambda := by
    intro g u hg
    rcases hg with ⟨n, rfl⟩
    exact ⟨(R n).lower u.1, (R n).upper u.1⟩
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc lambda Lambda)
      (isCompact_Icc) A hRange hEq
  obtain ⟨dUnit, -, phi, hphi, hconv⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  have hconv' : Tendsto (fun n => f (phi n)) atTop (nhds dUnit) := by
    simpa using hconv
  have hdperiodic : ∀ n, Periodic (R n).dpsi 1 :=
    fun n => markingDerivative_periodic (R n) (hpsi n)
  let u0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let u1 : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have h0 := (continuous_eval_const u0).continuousAt.tendsto.comp hconv'
  have h1 := (continuous_eval_const u1).continuousAt.tendsto.comp hconv'
  have hend : dUnit u1 = dUnit u0 := by
    apply tendsto_nhds_unique h1
    have heq : (fun n => f (phi n) u1) = fun n => f (phi n) u0 := by
      funext n
      change (R (phi n)).dpsi 1 = (R (phi n)).dpsi 0
      simpa using hdperiodic (phi n) 0
    have h0' : Tendsto (fun n => f (phi n) u0) atTop (nhds (dUnit u0)) := by
      simpa [Function.comp_def] using h0
    change Tendsto (fun n => f (phi n) u1) atTop (nhds (dUnit u0))
    rw [heq]
    exact h0'
  let dlim : ℝ → ℝ := PathMetric.unitPeriodicExtension dUnit
  have hdlimContinuous : Continuous dlim :=
    PathMetric.continuous_unitPeriodicExtension dUnit hend
  have hdlimUniform : TendstoUniformly (fun n => (R (phi n)).dpsi)
      dlim atTop := by
    apply tendstoUniformly_periodicExtension
      (fun n => hdperiodic (phi n))
      (fun n => Differentiable.continuous fun u =>
        (hddpsi (phi n) u).differentiableAt) dUnit
    simpa only [f] using hconv'
  let psilim : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, dlim t
  have hpsiTendsto : ∀ x, Tendsto (fun n => (R (phi n)).psi x) atTop
      (nhds (psilim x)) := by
    intro x
    have hint := tendsto_intervalIntegral_of_tendstoUniformly
      (fun n => Differentiable.continuous fun u =>
        (hddpsi (phi n) u).differentiableAt)
      hdlimContinuous hdlimUniform 0 x
    have heq : (fun n => (R (phi n)).psi x) =
        fun n => ∫ t in (0 : ℝ)..x, (R (phi n)).dpsi t := by
      funext n
      have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hpsi (phi n) u)
        ((Differentiable.continuous fun u =>
          (hddpsi (phi n) u).differentiableAt).intervalIntegrable 0 x)
      simpa [hzero (phi n)] using hfund.symm
    rw [heq]
    exact hint
  refine ⟨phi, hphi, ⟨{
    psi := psilim
    dpsi := dlim
    psi_tendsto := hpsiTendsto
    dpsi_tendsto := fun u => (hdlimUniform.tendsto_at u)
    hasDerivAt := fun u => by
      simpa [psilim] using intervalIntegral.integral_hasDerivAt_right
        (hdlimContinuous.intervalIntegrable 0 u)
        hdlimContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hdlimContinuous.continuousAt
    dpsi_continuous := hdlimContinuous }⟩⟩

/-- Marked `C2` convergence of both curve sequences and `C1` compactness of
their normalized terminal markings produce the exact surjective oriented
reparametrization required by the variable-terminal closure theorem.

The basepoint hypothesis is the standard normalization of the gauge flow.
The shift law, limit bounds, position and velocity identities, and
surjectivity are conclusions. -/
def limitOrientedReparametrization_of_normalizedMarkingC1Limit
    {baseN rearN : ℕ → Data} {base rear : Data}
    {lambda Lambda : ℝ}
    (hlambda : 0 < lambda)
    (R : ∀ k, OrientedReparametrization (baseN k) (rearN k) lambda Lambda)
    (hbase : Tendsto baseN atTop (nhds base))
    (hrear : Tendsto rearN atTop (nhds rear))
    (hzero : ∀ k, (R k).psi 0 = 0)
    (K : NormalizedMarkingC1Limit R) :
    LimitOrientedReparametrization base rear := by
  have htranslate : ∀ u, K.psi (u + 1) = K.psi u + 1 := by
    intro u
    have hright : Tendsto (fun k => (R k).psi (u + 1)) atTop
        (nhds (K.psi u + 1)) := by
      have h := (K.psi_tendsto u).add
        (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ)))
      simpa only [(R _).translate u] using h
    exact tendsto_nhds_unique (K.psi_tendsto (u + 1)) hright
  have hlower : ∀ u, lambda ≤ K.dpsi u := by
    intro u
    exact ge_of_tendsto (K.dpsi_tendsto u)
      (Eventually.of_forall fun k => (R k).lower u)
  have hupper : ∀ u, K.dpsi u ≤ Lambda := by
    intro u
    exact le_of_tendsto (K.dpsi_tendsto u)
      (Eventually.of_forall fun k => (R k).upper u)
  have hposition : ∀ u, rear.1 u = base.1 (K.psi u) := by
    intro u
    have hrearFun : Tendsto (fun k => (rearN k).1) atTop (nhds rear.1) :=
      (continuous_fst.tendsto rear).comp hrear
    have hrearEval : Tendsto (fun k => (rearN k).1 u) atTop
        (nhds (rear.1 u)) :=
      (continuous_eval_const u).continuousAt.tendsto.comp hrearFun
    have hbaseFun : Tendsto (fun k => (baseN k).1) atTop (nhds base.1) :=
      (continuous_fst.tendsto base).comp hbase
    have hpair : Tendsto (fun k => ((baseN k).1, (R k).psi u)) atTop
        (nhds (base.1, K.psi u)) := by
      simpa only [nhds_prod_eq] using hbaseFun.prodMk (K.psi_tendsto u)
    have hbaseEval : Tendsto (fun k => (baseN k).1 ((R k).psi u)) atTop
        (nhds (base.1 (K.psi u))) :=
      continuous_eval.continuousAt.tendsto.comp hpair
    have hseq : (fun k => (rearN k).1 u) =
        (fun k => (baseN k).1 ((R k).psi u)) := by
      funext k
      exact (R k).position u
    rw [hseq] at hrearEval
    exact tendsto_nhds_unique hrearEval hbaseEval
  have hvelocity : ∀ u,
      rear.2.1 u = (K.dpsi u : ℂ) * base.2.1 (K.psi u) := by
    intro u
    have hrearVelFun : Tendsto (fun k => (rearN k).2.1) atTop
        (nhds rear.2.1) :=
      ((continuous_fst.comp continuous_snd).tendsto rear).comp hrear
    have hrearVel : Tendsto (fun k => (rearN k).2.1 u) atTop
        (nhds (rear.2.1 u)) :=
      (continuous_eval_const u).continuousAt.tendsto.comp hrearVelFun
    have hbaseVelFun : Tendsto (fun k => (baseN k).2.1) atTop
        (nhds base.2.1) :=
      ((continuous_fst.comp continuous_snd).tendsto base).comp hbase
    have hpair : Tendsto (fun k => ((baseN k).2.1, (R k).psi u)) atTop
        (nhds (base.2.1, K.psi u)) := by
      simpa only [nhds_prod_eq] using hbaseVelFun.prodMk (K.psi_tendsto u)
    have hbaseVel : Tendsto
        (fun k => (baseN k).2.1 ((R k).psi u)) atTop
        (nhds (base.2.1 (K.psi u))) :=
      continuous_eval.continuousAt.tendsto.comp hpair
    have hdpsi : Tendsto (fun k => ((R k).dpsi u : ℂ)) atTop
        (nhds (K.dpsi u : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp (K.dpsi_tendsto u)
    have hproduct : Tendsto
        (fun k => ((R k).dpsi u : ℂ) * (baseN k).2.1 ((R k).psi u)) atTop
        (nhds ((K.dpsi u : ℂ) * base.2.1 (K.psi u))) :=
      hdpsi.mul hbaseVel
    have hseq : (fun k => (rearN k).2.1 u) =
        (fun k => ((R k).dpsi u : ℂ) * (baseN k).2.1 ((R k).psi u)) := by
      funext k
      exact (R k).velocity u
    rw [hseq] at hrearVel
    exact tendsto_nhds_unique hrearVel hproduct
  have hzeroLimit : K.psi 0 = 0 := by
    have hz : Tendsto (fun _k : ℕ => (0 : ℝ)) atTop (nhds (K.psi 0)) := by
      simpa only [hzero] using K.psi_tendsto 0
    exact tendsto_nhds_unique hz tendsto_const_nhds
  let Rlimit : OrientedReparametrization base rear lambda Lambda :=
    { psi := K.psi
      dpsi := K.dpsi
      position := hposition
      velocity := hvelocity
      translate := htranslate
      lower := hlower
      upper := hupper }
  have hcontinuous : Continuous Rlimit.psi :=
    continuous_iff_continuousAt.2 fun u => (K.hasDerivAt u).continuousAt
  have hstrictMono : StrictMono Rlimit.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(K.hasDerivAt u).deriv]
    exact lt_of_lt_of_le hlambda (hlower u)
  have hsurjective : Surjective Rlimit.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcontinuous hstrictMono Rlimit.translate hzeroLimit
  exact
    { lambda := lambda
      Lambda := Lambda
      lambda_pos := hlambda
      reparametrization := Rlimit
      psi_hasDerivAt := K.hasDerivAt
      dpsi_continuous := K.dpsi_continuous
      surjective := hsurjective }

/-- Direct fixed-row closure: the scalar Arzela--Ascoli theorem may pass to a
subsequence because both marked curve sequences already converge to unique
limits.  The resulting reparametrization therefore relates those original
row limits. -/
def limitOrientedReparametrization_of_rowwise_bounds
    {baseN rearN : ℕ → Data} {base rear : Data}
    {lambda Lambda N : ℝ}
    (hlambda : 0 < lambda) (hN : 0 ≤ N)
    (R : ∀ k, OrientedReparametrization (baseN k) (rearN k) lambda Lambda)
    (hbase : Tendsto baseN atTop (nhds base))
    (hrear : Tendsto rearN atTop (nhds rear))
    (hzero : ∀ k, (R k).psi 0 = 0)
    (hpsi : ∀ k u, HasDerivAt (R k).psi ((R k).dpsi u) u)
    (ddpsi : ℕ → ℝ → ℝ)
    (hddpsi : ∀ k u, HasDerivAt (R k).dpsi (ddpsi k u) u)
    (hddBound : ∀ k u, |ddpsi k u| ≤ N) :
    LimitOrientedReparametrization base rear := by
  let E := exists_normalizedMarkingC1Limit_subseq
    hN R hzero hpsi ddpsi hddpsi hddBound
  let phi : ℕ → ℕ := Classical.choose E
  have hphi : StrictMono phi := (Classical.choose_spec E).1
  let K : NormalizedMarkingC1Limit (fun n => R (phi n)) :=
    Nonempty.some (Classical.choose_spec E).2
  exact limitOrientedReparametrization_of_normalizedMarkingC1Limit
    hlambda (fun n => R (phi n))
    (hbase.comp hphi.tendsto_atTop) (hrear.comp hphi.tendsto_atTop)
    (fun n => hzero (phi n)) K

/-- Rowwise compactness data for the terminal normalized gauge markings.  All
bounds are allowed to depend on the triangular row; only the recursive depth
within a fixed row is uniform. -/
structure RowwiseNormalizedMarkingBounds
    (Q P : ℕ → ℕ → Data) where
  lambda : ℕ → ℝ
  Lambda : ℕ → ℝ
  secondBound : ℕ → ℝ
  lambda_pos : ∀ n, 0 < lambda n
  secondBound_nonneg : ∀ n, 0 ≤ secondBound n
  reparametrization : ∀ n k,
    OrientedReparametrization (Q n k) (P n k) (lambda n) (Lambda n)
  basepoint : ∀ n k, (reparametrization n k).psi 0 = 0
  psi_hasDerivAt : ∀ n k u,
    HasDerivAt (reparametrization n k).psi
      ((reparametrization n k).dpsi u) u
  ddpsi : ℕ → ℕ → ℝ → ℝ
  dpsi_hasDerivAt : ∀ n k u,
    HasDerivAt (reparametrization n k).dpsi (ddpsi n k u) u
  ddpsi_bound : ∀ n k u, |ddpsi n k u| ≤ secondBound n

/-- Choose the limit oriented reparametrization simultaneously in every row.
This is the compactness bridge consumed by both terminal Harnack closure and
the stronger unit-tangent-range representative closure. -/
def rowwiseLimitOrientedReparametrization
    {Q P : ℕ → ℕ → Data} {X Y : ℕ → Data}
    (B : RowwiseNormalizedMarkingBounds Q P)
    (hX : ∀ n, Tendsto (Q n) atTop (nhds (X n)))
    (hY : ∀ n, Tendsto (P n) atTop (nhds (Y n))) :
    ∀ n, LimitOrientedReparametrization (X n) (Y n) := by
  intro n
  exact limitOrientedReparametrization_of_rowwise_bounds
    (B.lambda_pos n) (B.secondBound_nonneg n)
    (B.reparametrization n) (hX n) (hY n)
    (B.basepoint n) (B.psi_hasDerivAt n) (B.ddpsi n)
    (B.dpsi_hasDerivAt n) (B.ddpsi_bound n)

/-- Paper-facing rowwise output.  Finite physical pullback kinematics supply
strictness of the canonical arclength limits; scalar marking compactness then
transports it to oriented arclength representatives of every variable row
limit.  Their physical length is the representative's constant-speed
perimeter (equivalently the variable curve's `totalLength`), never
`MarkedSpace.perim` of the variable marking. -/
def orientedRepresentatives_of_rowwise_marking_bounds
    {kh cb db : ℝ} {P Q : ℕ → ℕ → Data} {X Y : ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (htube : ∀ i k, IsTubeMember cb 0 db (Q i k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh Q)
    (hX : ∀ i, Tendsto (Q i) atTop (nhds (X i)))
    (hY : ∀ i, Tendsto (P i) atTop (nhds (Y i)))
    (B : RowwiseNormalizedMarkingBounds Q P) :
    ∀ n, VariableMarkedTube.OrientedArclengthRepresentative (Y n) := by
  let limitReparam : ∀ n x, Tendsto (P n) atTop (nhds x) →
      LimitOrientedReparametrization (X n) x := by
    intro n x hx
    exact limitOrientedReparametrization_of_rowwise_bounds
      (B.lambda_pos n) (B.secondBound_nonneg n)
      (B.reparametrization n) (hX n) hx
      (B.basepoint n) (B.psi_hasDerivAt n) (B.ddpsi n)
      (B.dpsi_hasDerivAt n) (B.ddpsi_bound n)
  exact fun n => orientedRepresentativeClosed_of_finitePullbackLimit
    hkh0 hkh1 hcb hdb htube finite hX limitReparam n (Y n) (hY n)

end GaugeRearFamilyVariableTerminal
