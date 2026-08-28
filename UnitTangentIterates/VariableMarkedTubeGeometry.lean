import UnitTangentIterates.VariableMarkedTube
import UnitTangentIterates.MarkedSpaceReparam
import UnitTangentIterates.LimitStrictnessHarnack

/-!
# Parameter-invariant geometry of the variable marked tube

Ovals are arclength-parametrized objects, so a nonaffine marked datum should
not itself be asserted to satisfy `IsOval`.  Instead we retain an arclength
representative with the same image and apply the existing ovality theory to
that representative.
-/

noncomputable section

open Set Function

namespace VariableMarkedTube

open MarkedSpace MarkedReparam

/-- Geometric ovality, independent of the chosen marking. -/
def IsGeometricOval (p : Data) : Prop :=
  ∃ Y : ℝ → ℂ, MainTheoremConditional.IsOval Y ∧ range Y = range (⇑p.1)

/-- The intrinsic quantitative chord estimate needed by the existing
arclength reparametrization theorem.  Gauge bi-Lipschitz estimates naturally
produce this form. -/
structure IntrinsicChordCertificate (delta : ℝ) (p : Data) : Prop where
  chord : ∀ x y,
    delta * min |arcLength (⇑p.2.1) x - arcLength (⇑p.2.1) y|
        (totalLength (⇑p.2.1) -
          |arcLength (⇑p.2.1) x - arcLength (⇑p.2.1) y|) ≤
      ‖p.1 x - p.1 y‖

/-- A standard constant-speed representative of a variable marking. -/
structure ArclengthRepresentative (kmin : ℝ) (p : Data) where
  q : Data
  c : ℝ
  dlt : ℝ
  c_pos : 0 < c
  dlt_pos : 0 < dlt
  tube : IsTubeMember c kmin dlt q
  same_range : range (⇑q.1) = range (⇑p.1)

/-- Existing arclength reparametrization converts a variable tube member with
an intrinsic chord certificate into an ordinary tube member. -/
theorem exists_arclengthRepresentative
    {c C kmin delta dIntrinsic : ℝ} {p : Data}
    (hc : 0 < c) (hdIntrinsic : 0 < dIntrinsic)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hchord : IntrinsicChordCertificate dIntrinsic p) :
    Nonempty (ArclengthRepresentative kmin p) := by
  obtain ⟨q, hq, hrange, hperim⟩ :=
    MarkedSpace.mem_tube_of_regular_closed_curve hc
      hp.hasDerivAt_curve hp.hasDerivAt_vel p.2.2.continuous
      hp.periodic (periodic_vel hp) (periodic_acc hp) hp.speed_lb hp.curv_lb
      hchord.chord
  have hLpos : 0 < totalLength (⇑p.2.1) :=
    totalLength_pos hc p.2.1.continuous hp.speed_lb
  refine ⟨{
    q := q
    c := totalLength (⇑p.2.1)
    dlt := dIntrinsic * totalLength (⇑p.2.1)
    c_pos := hLpos
    dlt_pos := mul_pos hdIntrinsic hLpos
    tube := hq
    same_range := hrange }⟩

theorem isGeometricOval_of_arclengthRepresentative
    {kmin : ℝ} {p : Data} (hkmin : 0 < kmin)
    (R : ArclengthRepresentative kmin p) : IsGeometricOval p := by
  refine ⟨ev R.q, MarkedSpace.isOval_ev R.c_pos hkmin R.dlt_pos R.tube, ?_⟩
  rw [MarkedSpace.range_ev R.c_pos R.tube, R.same_range]

theorem isGeometricOval_of_variableTube
    {c C kmin delta dIntrinsic : ℝ} {p : Data}
    (hc : 0 < c) (hkmin : 0 < kmin) (hdIntrinsic : 0 < dIntrinsic)
    (hp : IsVariableTubeMember c C kmin delta p)
    (hchord : IntrinsicChordCertificate dIntrinsic p) :
    IsGeometricOval p :=
  isGeometricOval_of_arclengthRepresentative hkmin
    (Nonempty.some (exists_arclengthRepresentative hc hdIntrinsic hp hchord))

/-- Harnack/strictness data are attached to an arclength representative, not
to the nonaffine marking.  This is the parameter-invariant finite-to-limit
certificate needed in the floor-free case. -/
structure ArclengthHarnackCertificate (p : Data) where
  q : Data
  c : ℝ
  dlt : ℝ
  c_pos : 0 < c
  dlt_pos : 0 < dlt
  tube : IsTubeMember c 0 dlt q
  same_range : range (⇑q.1) = range (⇑p.1)
  strictness : UnconditionalAssembly.LimitStrictnessDataH q

theorem isGeometricOval_of_arclengthHarnack
    {p : Data} (H : ArclengthHarnackCertificate p) : IsGeometricOval p := by
  refine ⟨ev H.q,
    UnconditionalAssembly.isOval_ev_of_limitStrictnessDataH
      H.c_pos H.dlt_pos H.tube H.strictness, ?_⟩
  rw [MarkedSpace.range_ev H.c_pos H.tube, H.same_range]

/-- A parameter-invariant finite range edge. -/
def GeometricUnitTangentRangeEdge (front rear : Data) : Prop :=
  range (⇑front.1) = range (geometricUnitTangent rear)

/-- A bridge to an ordinary arclength representative.  Orientation of the
marking is explicitly retained; equality of curve images alone is not enough
to identify unit-tangent images. -/
structure OrientedArclengthRepresentative (p : Data) extends
    ArclengthHarnackCertificate p where
  unitTangent_range :
    range (UnitTangent.unitTangentMap (ev toArclengthHarnackCertificate.q)) =
      range (geometricUnitTangent p)
  physical_length :
    MarkedReparam.totalLength (fun u => p.2.1 u) =
      perim toArclengthHarnackCertificate.q

end VariableMarkedTube
