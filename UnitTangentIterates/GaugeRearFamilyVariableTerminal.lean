import UnitTangentIterates.GaugeRearFamilyTriangularStageAdapter
import UnitTangentIterates.VariableMarkedTubeGeometry
import UnitTangentIterates.GaugeMarkedSelectedInverseEndpoint
import UnitTangentIterates.PhysicalRearLimitHarnackAdapter

/-!
# Gauge rear-family stages with variable terminal markings

This is the honest nonaffine analogue of
`GaugeRearFamilyTriangularStageAdapter.TerminalResidual`.  It does not force a
gauge endpoint into the constant-speed marked tube.
-/

noncomputable section

open Set Function MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearOwnArclength RearFamilyFrame
  NormalPathC2IncrementVariableSpeed GaugeFlowDerivCost

namespace GaugeRearFamilyVariableTerminal

open GaugeMarkedDataOfRearFamily VariableMarkedTube
  GaugeMarkedSelectedInverseEndpoint

/-- The terminal geometric facts not supplied merely by construction of the
normal path. -/
structure TerminalResidual
    (front rear : Data) (c C dlt : ℝ) where
  rear_variable_tube : IsVariableTubeMember c C 0 dlt rear
  range_edge : GeometricUnitTangentRangeEdge front rear
  rear_harnack : ArclengthHarnackCertificate rear

/-- Terminal facts needed by recursion before compact-class membership has
been proved by the rowwise distance budget. -/
structure RawTerminalResidual
    (front rear : Data) where
  rear_curve_deriv : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u
  rear_vel_deriv : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u
  rear_periodic : Periodic (⇑rear.1) 1
  rear_curvature_nonnegative : ∀ u, 0 ≤
    ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im
  range_edge : GeometricUnitTangentRangeEdge front rear
  rear_harnack : ArclengthHarnackCertificate rear

/-- A terminal gauge marking with explicit two-sided derivative distortion.
The derivative identities are exactly those returned by the rear-family flow;
only the oriented-curvature and embedded-chord estimates below are geometric
analytic inputs. -/
structure OrientedReparametrization
    (base rear : Data) (lambda Lambda : ℝ) where
  psi : ℝ → ℝ
  dpsi : ℝ → ℝ
  position : ∀ u, rear.1 u = base.1 (psi u)
  velocity : ∀ u, rear.2.1 u = (dpsi u : ℂ) * base.2.1 (psi u)
  translate : ∀ u, psi (u + 1) = psi u + 1
  lower : ∀ u, lambda ≤ dpsi u
  upper : ∀ u, dpsi u ≤ Lambda

/-- A positively oriented reparametrization of an ordinary tube member is a
variable-tube member.  The speed constants display the precise distortion:
`lambda * c` and `Lambda * perim base`. -/
theorem variableTube_of_orientedReparametrization
    {base rear : Data} {cb db lambda Lambda dlt : ℝ}
    (hcb : 0 < cb) (hlambda : 0 < lambda)
    (hbase : IsTubeMember cb 0 db base)
    (R : OrientedReparametrization base rear lambda Lambda)
    (hcurve : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u)
    (hcurv : ∀ u, 0 ≤
      ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im)
    (hchord : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dlt * cyc u v ≤ ‖rear.1 u - rear.1 v‖) :
    IsVariableTubeMember (lambda * cb) (Lambda * perim base) 0 dlt rear := by
  have hP : 0 < perim base := perim_pos hcb hbase
  refine ⟨hcurve, hvel, ?_, ?_, ?_, ?_, hchord⟩
  · intro u
    rw [R.position (u + 1), R.translate u, hbase.periodic (R.psi u),
      R.position u]
  · intro u
    have hd : 0 < R.dpsi u := lt_of_lt_of_le hlambda (R.lower u)
    have hcbP : cb ≤ perim base := by
      simpa [norm_vel_eq_perim hbase] using hbase.speed_lb (R.psi u)
    rw [R.velocity u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hd, norm_vel_eq_perim hbase]
    exact mul_le_mul (R.lower u) hcbP hcb.le hd.le
  · intro u
    have hd : 0 ≤ R.dpsi u :=
      (lt_of_lt_of_le hlambda (R.lower u)).le
    rw [R.velocity u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hd, norm_vel_eq_perim hbase]
    exact mul_le_mul_of_nonneg_right (R.upper u) hP.le
  · intro u
    simpa using hcurv u

/-- Pointwise orientation preservation identifies the geometric unit tangent
of the gauge endpoint with the normalized unit tangent of its canonical
constant-speed representative. -/
theorem geometricUnitTangent_eq_normalized_of_orientedReparametrization
    {base rear : Data} {cb db lambda Lambda : ℝ}
    (hcb : 0 < cb) (hlambda : 0 < lambda)
    (hbase : IsTubeMember cb 0 db base)
    (R : OrientedReparametrization base rear lambda Lambda) (u : ℝ) :
    geometricUnitTangent rear u = normalizedUnitTangent base (R.psi u) := by
  have hd : 0 < R.dpsi u := lt_of_lt_of_le hlambda (R.lower u)
  have hP : 0 < perim base := perim_pos hcb hbase
  rw [geometricUnitTangent, normalizedUnitTangent, R.position u,
    R.velocity u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hd, norm_vel_eq_perim hbase]
  push_cast
  field_simp [hd.ne', hP.ne']

/-- Surjectivity of the terminal marking transports the canonical selected
rear range edge to the actual gauge endpoint. -/
theorem geometricRangeEdge_of_orientedReparametrization
    {front base rear : Data} {cb db lambda Lambda : ℝ}
    (hcb : 0 < cb) (hlambda : 0 < lambda)
    (hbase : IsTubeMember cb 0 db base)
    (R : OrientedReparametrization base rear lambda Lambda)
    (hsurj : Surjective R.psi)
    (hcanonical : range (⇑front.1) =
      range (UnitTangent.unitTangentMap (ev base))) :
    GeometricUnitTangentRangeEdge front rear := by
  have hrange : range (geometricUnitTangent rear) =
      range (normalizedUnitTangent base) := by
    apply Set.Subset.antisymm
    · rintro z ⟨u, rfl⟩
      exact ⟨R.psi u,
        (geometricUnitTangent_eq_normalized_of_orientedReparametrization
          hcb hlambda hbase R u).symm⟩
    · rintro z ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := hsurj x
      exact ⟨u,
        geometricUnitTangent_eq_normalized_of_orientedReparametrization
          hcb hlambda hbase R u⟩
  rw [GeometricUnitTangentRangeEdge, hcanonical,
    range_unitTangentMap_ev_eq_normalized hcb hbase, hrange]

/-- The standard continuous/strictly-monotone/quasi-periodic flow hypotheses
produce the surjectivity needed by `geometricRangeEdge_of_orientedReparametrization`.
The terminal physical period has already been normalized to one here. -/
theorem geometricRangeEdge_of_flowMarking
    {front base rear : Data} {cb db lambda Lambda : ℝ}
    (hcb : 0 < cb) (hlambda : 0 < lambda)
    (hbase : IsTubeMember cb 0 db base)
    (R : OrientedReparametrization base rear lambda Lambda)
    (hcont : Continuous R.psi) (hmono : StrictMono R.psi)
    (hzero : R.psi 0 = 0)
    (hcanonical : range (⇑front.1) =
      range (UnitTangent.unitTangentMap (ev base))) :
    GeometricUnitTangentRangeEdge front rear := by
  apply geometricRangeEdge_of_orientedReparametrization hcb hlambda hbase R
  · exact surjective_of_continuous_strictMono_quasiPeriodic one_pos hcont hmono
        R.translate hzero
  · exact hcanonical

/-- A canonical rear representative carrying the physical limiting Harnack
certificate supplies parameter-invariant Harnack data for its gauge marking. -/
def arclengthHarnack_of_orientedReparametrization
    {base rear : Data} {cb db lambda Lambda : ℝ}
    (hcb : 0 < cb) (hdb : 0 < db)
    (hbase : IsTubeMember cb 0 db base)
    (R : OrientedReparametrization base rear lambda Lambda)
    (hsurj : Surjective R.psi)
    (hstrict : UnconditionalAssembly.LimitStrictnessDataH base) :
    ArclengthHarnackCertificate rear := by
  have hrange : range (⇑rear.1) = range (⇑base.1) := by
    apply Set.Subset.antisymm
    · rintro z ⟨u, rfl⟩
      exact ⟨R.psi u, (R.position u).symm⟩
    · rintro z ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := hsurj x
      exact ⟨u, R.position u⟩
  exact {
    q := base
    c := cb
    dlt := db
    c_pos := hcb
    dlt_pos := hdb
    tube := hbase
    same_range := hrange.symm
    strictness := hstrict }

/-- The same physical arclength representative also retains the oriented
unit-tangent range needed to turn a geometric variable-marked orbit into the
paper-facing orbit of arclength-parametrized ovals. -/
def orientedArclengthRepresentative_of_orientedReparametrization
    {base rear : Data} {cb db lambda Lambda : ℝ}
    (hcb : 0 < cb) (hdb : 0 < db) (hlambda : 0 < lambda)
    (hbase : IsTubeMember cb 0 db base)
    (R : OrientedReparametrization base rear lambda Lambda)
    (hpsi : ∀ u, HasDerivAt R.psi (R.dpsi u) u)
    (hdpsi : Continuous R.dpsi)
    (hsurj : Surjective R.psi)
    (hstrict : UnconditionalAssembly.LimitStrictnessDataH base) :
    OrientedArclengthRepresentative rear := by
  let H := arclengthHarnack_of_orientedReparametrization
    hcb hdb hbase R hsurj hstrict
  refine {
    toArclengthHarnackCertificate := H
    unitTangent_range := ?_
    physical_length := ?_
  }
  · have hrange : range (geometricUnitTangent rear) =
        range (normalizedUnitTangent base) := by
      apply Set.Subset.antisymm
      · rintro z ⟨u, rfl⟩
        exact ⟨R.psi u,
          (geometricUnitTangent_eq_normalized_of_orientedReparametrization
            hcb hlambda hbase R u).symm⟩
      · rintro z ⟨x, rfl⟩
        obtain ⟨u, hu⟩ := hsurj x
        refine ⟨u, ?_⟩
        rw [geometricUnitTangent_eq_normalized_of_orientedReparametrization
          hcb hlambda hbase R u, hu]
    change range (UnitTangent.unitTangentMap (ev base)) =
      range (geometricUnitTangent rear)
    rw [range_unitTangentMap_ev_eq_normalized hcb hbase]
    exact hrange.symm
  · have hint : (∫ u in (0 : ℝ)..1, R.dpsi u) = 1 := by
      have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hpsi u) (hdpsi.intervalIntegrable 0 1)
      have hshift := R.translate 0
      norm_num at hshift
      calc
        (∫ u in (0 : ℝ)..1, R.dpsi u) = R.psi 1 - R.psi 0 := hfund
        _ = 1 := by linarith
    have hnorm : ∀ u, ‖rear.2.1 u‖ = R.dpsi u * perim base := by
      intro u
      have hdu : 0 < R.dpsi u :=
        lt_of_lt_of_le hlambda (R.lower u)
      rw [R.velocity u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hdu, norm_vel_eq_perim hbase]
    rw [MarkedReparam.totalLength]
    simp_rw [hnorm]
    rw [intervalIntegral.integral_mul_const, hint, one_mul]
    rfl

/-- The aligned finite physical pullback package constructs the Harnack field
for a nonaffine marking of a row limit. -/
def arclengthHarnack_of_finitePullbackLimit
    {kh cb db lambda Lambda : ℝ} {Q : ℕ → ℕ → Data}
    {X : ℕ → Data} {rear : Data} (n : ℕ)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (htube : ∀ i k, IsTubeMember cb 0 db (Q i k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh Q)
    (hX : ∀ i, Filter.Tendsto (Q i) Filter.atTop (nhds (X i)))
    (R : OrientedReparametrization (X n) rear lambda Lambda)
    (hsurj : Surjective R.psi) : ArclengthHarnackCertificate rear := by
  have hbase : IsTubeMember cb 0 db (X n) :=
    (isClosed_tube cb 0 db).mem_of_tendsto (hX n)
      (Filter.Eventually.of_forall (htube n))
  exact arclengthHarnack_of_orientedReparametrization hcb hdb hbase R hsurj
    (PathMetric.limitStrictnessDataH_of_finitePullbackPhysicalRearKinematics
      hkh0 hkh1 hcb htube finite X hX n)

/-- Constructive output of compactness for terminal marking maps. -/
structure LimitOrientedReparametrization (base rear : Data) where
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  reparametrization : OrientedReparametrization base rear lambda Lambda
  psi_hasDerivAt : ∀ u, HasDerivAt reparametrization.psi
    (reparametrization.dpsi u) u
  dpsi_continuous : Continuous reparametrization.dpsi
  surjective : Surjective reparametrization.psi

/-- Aligned finite physical kinematics discharge the terminal scheme's
Harnack-closure field once compactness of the terminal markings identifies
each variable row limit as a surjective oriented reparametrization of the
corresponding arclength row limit.  No convergence of arbitrarily chosen
finite certificate representatives is required. -/
def harnackClosed_of_finitePullbackLimit
    {kh cb db : ℝ} {P Q : ℕ → ℕ → Data} {X : ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (htube : ∀ i k, IsTubeMember cb 0 db (Q i k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh Q)
    (hX : ∀ i, Filter.Tendsto (Q i) Filter.atTop (nhds (X i)))
    (limitReparam : ∀ n x,
      Filter.Tendsto (P n) Filter.atTop (nhds x) →
      LimitOrientedReparametrization (X n) x) :
    ∀ n x, Filter.Tendsto (P n) Filter.atTop (nhds x) →
      (∀ k, ArclengthHarnackCertificate (P n k)) →
      ArclengthHarnackCertificate x := by
  intro n x hx _hfinite
  let W := limitReparam n x hx
  exact arclengthHarnack_of_finitePullbackLimit n hkh0 hkh1 hcb hdb
    htube finite hX W.reparametrization W.surjective

/-- Strong terminal closure output used by the final representative/orbit
bridge.  Besides ovality it preserves the orientation of the unit-tangent
range, which position-range equality alone cannot recover. -/
def orientedRepresentativeClosed_of_finitePullbackLimit
    {kh cb db : ℝ} {P Q : ℕ → ℕ → Data} {X : ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (htube : ∀ i k, IsTubeMember cb 0 db (Q i k))
    (finite : PathMetric.FinitePullbackPhysicalRearKinematics kh Q)
    (hX : ∀ i, Filter.Tendsto (Q i) Filter.atTop (nhds (X i)))
    (limitReparam : ∀ n x,
      Filter.Tendsto (P n) Filter.atTop (nhds x) →
      LimitOrientedReparametrization (X n) x) :
    ∀ n x, Filter.Tendsto (P n) Filter.atTop (nhds x) →
      OrientedArclengthRepresentative x := by
  intro n x hx
  let W := limitReparam n x hx
  have hbase : IsTubeMember cb 0 db (X n) :=
    (isClosed_tube cb 0 db).mem_of_tendsto (hX n)
      (Filter.Eventually.of_forall (htube n))
  exact orientedArclengthRepresentative_of_orientedReparametrization
      hcb hdb W.lambda_pos
    hbase W.reparametrization W.psi_hasDerivAt W.dpsi_continuous W.surjective
    (PathMetric.limitStrictnessDataH_of_finitePullbackPhysicalRearKinematics
      hkh0 hkh1 hcb htube finite X hX n)

/-- Concrete constructor for all three variable terminal fields. -/
def terminalResidual_of_orientedReparametrization
    {front base rear : Data} {cb db lambda Lambda dlt : ℝ}
    (hcb : 0 < cb) (hdb : 0 < db) (hlambda : 0 < lambda)
    (hbase : IsTubeMember cb 0 db base)
    (R : OrientedReparametrization base rear lambda Lambda)
    (hcurve : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u)
    (hcurv : ∀ u, 0 ≤
      ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im)
    (hchord : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dlt * cyc u v ≤ ‖rear.1 u - rear.1 v‖)
    (hsurj : Surjective R.psi)
    (hcanonical : range (⇑front.1) =
      range (UnitTangent.unitTangentMap (ev base)))
    (hstrict : UnconditionalAssembly.LimitStrictnessDataH base) :
    TerminalResidual front rear (lambda * cb) (Lambda * perim base) dlt :=
  { rear_variable_tube := variableTube_of_orientedReparametrization
      hcb hlambda hbase R hcurve hvel hcurv hchord
    range_edge := geometricRangeEdge_of_orientedReparametrization
      hcb hlambda hbase R hsurj hcanonical
    rear_harnack := arclengthHarnack_of_orientedReparametrization
      hcb hdb hbase R hsurj hstrict }

/-- The orientation and physical representative construct every terminal fact
except the chord/tube estimate, which is intentionally deferred to the row
budget. -/
def rawTerminalResidual_of_orientedReparametrization
    {front base rear : Data} {cb db lambda Lambda : ℝ}
    (hcb : 0 < cb) (hdb : 0 < db) (hlambda : 0 < lambda)
    (hbase : IsTubeMember cb 0 db base)
    (R : OrientedReparametrization base rear lambda Lambda)
    (hcurve : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u)
    (hcurv : ∀ u, 0 ≤
      ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im)
    (hsurj : Surjective R.psi)
    (hcanonical : range (⇑front.1) =
      range (UnitTangent.unitTangentMap (ev base)))
    (hstrict : UnconditionalAssembly.LimitStrictnessDataH base) :
    RawTerminalResidual front rear where
  rear_curve_deriv := hcurve
  rear_vel_deriv := hvel
  rear_periodic := by
    intro u
    rw [R.position (u + 1), R.translate u, hbase.periodic (R.psi u), R.position u]
  rear_curvature_nonnegative := hcurv
  range_edge := geometricRangeEdge_of_orientedReparametrization
    hcb hlambda hbase R hsurj hcanonical
  rear_harnack := arclengthHarnack_of_orientedReparametrization
    hcb hdb hbase R hsurj hstrict

/-- A recursion stage before the rowwise tube budget is applied. -/
structure RawStageOutput
    (p front rear : Data) (bound P0 P1 kh G1 Cg : ℝ) where
  increment : NormalPath p rear
  increment_geometry : IsVariableSpeedNormalPath P0 P1 kh G1 Cg increment
  increment_cost : cost increment ≤ bound
  rear_curve_deriv : ∀ u, HasDerivAt (⇑rear.1) (rear.2.1 u) u
  rear_vel_deriv : ∀ u, HasDerivAt (⇑rear.2.1) (rear.2.2 u) u
  rear_periodic : Periodic (⇑rear.1) 1
  rear_curvature_nonnegative : ∀ u, 0 ≤
    ((starRingEnd ℂ) (rear.2.1 u) * rear.2.2 u).im
  range_edge : GeometricUnitTangentRangeEdge front rear
  rear_harnack : ArclengthHarnackCertificate rear

/-- The rear-family continuation supplies the complete raw recursion stage. -/
theorem rawStageOutput_of_rearFamilyContinuation
    {p front rear : Data}
    {F : ℝ → ℝ → ℂ} {Theta delta sf : ℝ → ℝ → ℝ}
    {Ydot : ℝ → ℝ → ℂ} {Phi : ℝ → ℝ → ℝ}
    {T M bound : ℝ} {m : ℝ → ℝ}
    {P0 ell kh khat : ℝ}
    (hcontinue :
      GaugeRearFamilyTriangularStageAdapter.RearFamilyContinuation
        F Theta delta sf Ydot Phi T M m P0 ell kh khat)
    (hinitial : ∀ u, rearOwn F Theta delta sf 0 (Phi 0 u) = p.1 u)
    (hterminal : ∀ u, rearOwn F Theta delta sf T (Phi T u) = rear.1 u)
    (hsup : ∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j
        (fun u => frameNormal Ydot (rearOwnAngle Theta delta sf) t (Phi t u))) ≤ m t)
    (hcost : M ≤ bound)
    (R : RawTerminalResidual front rear) :
    Nonempty (RawStageOutput p front rear bound
      P0 (costP1 ell khat M) khat
      (costG1 ell khat (rearKappa2 kh) M)
      (khat * costG1 ell khat (rearKappa2 kh) M +
        rearKappa2 kh * costP1 ell khat M ^ 2)) := by
  obtain ⟨Delta, hDeltaCost, hDeltaGeometry⟩ :=
    hcontinue p rear hinitial hterminal hsup
  refine ⟨{
    increment := Delta
    increment_geometry := hDeltaGeometry
    increment_cost := ?_
    rear_curve_deriv := R.rear_curve_deriv
    rear_vel_deriv := R.rear_vel_deriv
    rear_periodic := R.rear_periodic
    rear_curvature_nonnegative := R.rear_curvature_nonnegative
    range_edge := R.range_edge
    rear_harnack := R.rear_harnack }⟩
  rw [hDeltaCost]
  exact hcost

/-- One recursive gauge stage retaining its actual variable-speed endpoint. -/
structure StageOutput
    (p front rear : Data) (bound P0 P1 kh G1 Cg c C dlt : ℝ) where
  rear_variable_tube : IsVariableTubeMember c C 0 dlt rear
  increment : NormalPath p rear
  increment_geometry : IsVariableSpeedNormalPath P0 P1 kh G1 Cg increment
  increment_cost : cost increment ≤ bound
  range_edge : GeometricUnitTangentRangeEdge front rear
  rear_harnack : ArclengthHarnackCertificate rear

/-- Forget tube membership from a completed stage. -/
def StageOutput.toRaw
    {p front rear : Data} {bound P0 P1 kh G1 Cg c C dlt : ℝ}
    (S : StageOutput p front rear bound P0 P1 kh G1 Cg c C dlt) :
    RawStageOutput p front rear bound P0 P1 kh G1 Cg where
  increment := S.increment
  increment_geometry := S.increment_geometry
  increment_cost := S.increment_cost
  rear_curve_deriv := S.rear_variable_tube.hasDerivAt_curve
  rear_vel_deriv := S.rear_variable_tube.hasDerivAt_vel
  rear_periodic := S.rear_variable_tube.periodic
  rear_curvature_nonnegative := fun u => by
    simpa using S.rear_variable_tube.curv_lb u
  range_edge := S.range_edge
  rear_harnack := S.rear_harnack

/-- The rear-family continuation already discharges the entire path part of a
variable-marking stage. -/
theorem stageOutput_of_rearFamilyContinuation
    {p front rear : Data}
    {F : ℝ → ℝ → ℂ} {Theta delta sf : ℝ → ℝ → ℝ}
    {Ydot : ℝ → ℝ → ℂ} {Phi : ℝ → ℝ → ℝ}
    {T M bound : ℝ} {m : ℝ → ℝ}
    {P0 ell kh khat c C dlt : ℝ}
    (hcontinue :
      GaugeRearFamilyTriangularStageAdapter.RearFamilyContinuation
        F Theta delta sf Ydot Phi T M m P0 ell kh khat)
    (hinitial : ∀ u, rearOwn F Theta delta sf 0 (Phi 0 u) = p.1 u)
    (hterminal : ∀ u, rearOwn F Theta delta sf T (Phi T u) = rear.1 u)
    (hsup : ∀ t, ∀ j ≤ 2, supNorm
      (iteratedDeriv j
        (fun u => frameNormal Ydot (rearOwnAngle Theta delta sf) t (Phi t u))) ≤ m t)
    (hcost : M ≤ bound)
    (R : TerminalResidual front rear c C dlt) :
    Nonempty (StageOutput p front rear bound
      P0 (costP1 ell khat M) khat
      (costG1 ell khat (rearKappa2 kh) M)
      (khat * costG1 ell khat (rearKappa2 kh) M +
        rearKappa2 kh * costP1 ell khat M ^ 2) c C dlt) := by
  obtain ⟨Delta, hDeltaCost, hDeltaGeometry⟩ :=
    hcontinue p rear hinitial hterminal hsup
  refine ⟨{
    rear_variable_tube := R.rear_variable_tube
    increment := Delta
    increment_geometry := hDeltaGeometry
    increment_cost := ?_
    range_edge := R.range_edge
    rear_harnack := R.rear_harnack }⟩
  rw [hDeltaCost]
  exact hcost

end GaugeRearFamilyVariableTerminal
