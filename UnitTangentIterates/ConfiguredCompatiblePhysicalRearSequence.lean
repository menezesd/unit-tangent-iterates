import UnitTangentIterates.ConfiguredFiniteBasePhysicalRearCertificate
import UnitTangentIterates.CompatibleMarkings
import UnitTangentIterates.MarkedRigid
import UnitTangentIterates.SelectedInverseShiftEquivariance

/-!
# Compatible physical rear sequence

This is the sequence-level compatible-markings induction.  Its input is only
an unaligned exact rear/front pair at each level.  Starting from one marked
front, it rotates each pair so that the marked rear tangent agrees with the
current front tangent, translates the rear marked point to the current front
marked point, and carries the same rigid motion to the successor.

The output is a coherent family.  In particular, no all-level alignment or
choice residual remains: all choices are made by primitive recursion.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredCompatiblePhysicalRearSequence

open ConfiguredApproximateDefectPathActualTerminal

/-- Integrated strictness is invariant under a cyclic change of marking. -/
def shiftLimitStrictnessDataH {p : Data} {cr dr : ℝ}
    (hcr : 0 < cr) (hp : IsTubeMember cr 0 dr p)
    (H : UnconditionalAssembly.LimitStrictnessDataH p) (b : ℝ) :
    UnconditionalAssembly.LimitStrictnessDataH (MarkedShift.shiftData b p) := by
  let q := b * perim p
  have hL : perim p ≠ 0 :=
    ne_of_gt (perim_pos hcr hp)
  have hev : ev (MarkedShift.shiftData b p) = RigidMotions.shift q (ev p) := by
    funext s
    exact SelectedInverseShiftEquivariance.ev_shiftData hp hL b s
  refine
    { theta := fun s => H.theta (s + q)
      k := fun s => H.k (s + q)
      curve_deriv := ?_
      angle_deriv := ?_
      curvature_periodic := ?_
      curvature_nonnegative := fun s => H.curvature_nonnegative (s + q)
      curvature_harnack := ?_
      curvature_nonzero := ?_ }
  · intro s
    rw [hev]
    exact RigidMotions.hasDerivAt_shift H.curve_deriv q s
  · intro s
    have hinner : HasDerivAt (fun u : ℝ => u + q) 1 s := by
      simpa using (hasDerivAt_id s).add_const q
    simpa [Function.comp_def] using (H.angle_deriv (s + q)).scomp s hinner
  · intro s
    rw [SelectedInverseShiftEquivariance.perim_shiftData hp b]
    simpa [add_assoc, add_comm, add_left_comm] using H.curvature_periodic (s + q)
  · intro a z haz
    have h := H.curvature_harnack (a + q) (z + q) (by linarith)
    simpa only [add_sub_add_right_eq_sub] using h
  · obtain ⟨s, hs⟩ := H.curvature_nonzero
    exact ⟨s - q, by simpa using hs⟩

/-- A cyclic shift of a regular marked datum does not change the range of its
unit-tangent transform. -/
theorem range_unitTangent_shiftData {p : Data} {cr dr : ℝ}
    (hcr : 0 < cr) (hp : IsTubeMember cr 0 dr p)
    (H : UnconditionalAssembly.LimitStrictnessDataH p) (b : ℝ) :
    range (UnitTangent.unitTangentMap
      (ev (MarkedShift.shiftData b p))) =
      range (UnitTangent.unitTangentMap (ev p)) := by
  let q := b * perim p
  have hL : perim p ≠ 0 :=
    ne_of_gt (perim_pos hcr hp)
  have hev : ev (MarkedShift.shiftData b p) = RigidMotions.shift q (ev p) := by
    funext s
    exact SelectedInverseShiftEquivariance.ev_shiftData hp hL b s
  rw [hev]
  apply Set.Subset.antisymm
  · rintro z ⟨s, rfl⟩
    exact ⟨s + q, (RigidMotions.unitTangentMap_shift H.curve_deriv q s).symm⟩
  · rintro z ⟨s, rfl⟩
    refine ⟨s - q, ?_⟩
    rw [RigidMotions.unitTangentMap_shift H.curve_deriv]
    congr 1
    ring

/-- Unit tangent at the marked normalized parameter.  It is used only under a
positive-speed hypothesis, but is total so the recursive definition does not
depend on proof terms. -/
def markedUnitTangent (p : Data) : ℂ := p.2.1 0 / ‖p.2.1 0‖

theorem norm_markedUnitTangent {p : Data} (hp : 0 < ‖p.2.1 0‖) :
    ‖markedUnitTangent p‖ = 1 := by
  rw [markedUnitTangent, norm_div]
  simp [abs_of_pos hp, ne_of_gt hp]

/-- The unique rotation carrying the marked rear tangent to the current
marked front tangent.  This is the explicit witness selected by
`RigidMotions.existsUnique_rotation_of_marked_tangent`, the normalization core
of `RigidMotions.existsUnique_compatible_marking`. -/
def compatibleRotation (rear front : Data) : ℂ :=
  markedUnitTangent front / markedUnitTangent rear

theorem norm_compatibleRotation {rear front : Data}
    (hr : 0 < ‖rear.2.1 0‖) (hf : 0 < ‖front.2.1 0‖) :
    ‖compatibleRotation rear front‖ = 1 := by
  rw [compatibleRotation, norm_div, norm_markedUnitTangent hr,
    norm_markedUnitTangent hf, div_one]

theorem compatibleRotation_tangent {rear front : Data}
    (hr : 0 < ‖rear.2.1 0‖) (hf : 0 < ‖front.2.1 0‖) :
    compatibleRotation rear front * markedUnitTangent rear =
      markedUnitTangent front := by
  unfold compatibleRotation
  have hne : markedUnitTangent rear ≠ 0 := by
    intro h
    have := norm_markedUnitTangent hr
    rw [h, norm_zero] at this
    norm_num at this
  field_simp

/-- Translation accompanying the compatible rotation, chosen so that marked
points agree literally. -/
def compatibleTranslation (rear front : Data) : ℂ :=
  front.1 0 - compatibleRotation rear front * rear.1 0

/-- Pointwise exact physical pairs before compatible marking.  Each rear is a
rigid/phase image of the analytically normalized configured `kH` carrier.
Rigid equivariance of the physical pair is retained locally; the theorem below
constructs the coherent all-level choices from it. -/
structure PairSource
    (D : ConstructedConfiguredSequenceWeighted.Data) (kh c dlt : ℝ) where
  normalized : ∀ n, RearCarrier D n
  rear : ℕ → Data
  front : ℕ → Data
  rear_regular : ∀ n, 0 < ‖( rear n).2.1 0‖
  rear_tube : ∀ n, ∃ cr dr : ℝ, 0 < cr ∧ 0 < dr ∧
    IsTubeMember cr 0 dr (rear n)
  front_tube : ∀ n, IsTubeMember c 0 dlt (front n)
  normalized_alignment : ∀ n, ∃ a w : ℂ, ∃ b : ℝ,
    ‖w‖ = 1 ∧
    rear n = MarkedRigid.rigidData a w
      (MarkedShift.shiftData b (normalized n).data)
  physical_rigid : ∀ n (a w : ℂ), ‖w‖ = 1 → Nonempty
    (PhysicalRearLimitKinematics kh
      (MarkedRigid.rigidData a w (rear n))
      (MarkedRigid.rigidData a w (front n)))

namespace PairSource

variable {D : ConstructedConfiguredSequenceWeighted.Data} {kh c dlt : ℝ}
  (S : PairSource D kh c dlt) (q0 : Data)

/-- Compatible fronts, defined by primitive recursion. -/
def fronts : ℕ → Data
  | 0 => q0
  | n + 1 =>
      let w := compatibleRotation (S.rear n) (fronts n)
      let a := compatibleTranslation (S.rear n) (fronts n)
      MarkedRigid.rigidData a w (S.front n)

/-- The rear at edge `n`, moved by exactly the same rigid motion as its
successor front. -/
def rears (n : ℕ) : Data :=
  let w := compatibleRotation (S.rear n) (S.fronts q0 n)
  let a := compatibleTranslation (S.rear n) (S.fronts q0 n)
  MarkedRigid.rigidData a w (S.rear n)

theorem fronts_tube (hc : 0 < c) (hq0 : IsTubeMember c 0 dlt q0) :
    ∀ n, IsTubeMember c 0 dlt (S.fronts q0 n) := by
  intro n
  induction n with
  | zero => exact hq0
  | succ n ih =>
      have hreg : 0 < ‖(S.fronts q0 n).2.1 0‖ :=
        lt_of_lt_of_le hc (ih.speed_lb 0)
      exact MarkedRigid.isTubeMember_rigidData
        (norm_compatibleRotation (S.rear_regular n) hreg)
        (S.front_tube n)

theorem fronts_regular (hc : 0 < c) (hq0 : IsTubeMember c 0 dlt q0)
    (n : ℕ) : 0 < ‖(S.fronts q0 n).2.1 0‖ :=
  lt_of_lt_of_le hc ((S.fronts_tube q0 hc hq0 n).speed_lb 0)

theorem rears_tube (hc : 0 < c) (hq0 : IsTubeMember c 0 dlt q0)
    (n : ℕ) : ∃ cr dr : ℝ, 0 < cr ∧ 0 < dr ∧
      IsTubeMember cr 0 dr (S.rears q0 n) := by
  obtain ⟨cr, dr, hcr, hdr, hmem⟩ := S.rear_tube n
  refine ⟨cr, dr, hcr, hdr, ?_⟩
  exact MarkedRigid.isTubeMember_rigidData
    (norm_compatibleRotation (S.rear_regular n)
      (S.fronts_regular q0 hc hq0 n)) hmem

theorem rear_marked_point_eq (n : ℕ) :
    (S.rears q0 n).1 0 = (S.fronts q0 n).1 0 := by
  simp [rears, compatibleTranslation]

theorem rear_marked_tangent_eq (hc : 0 < c)
    (hq0 : IsTubeMember c 0 dlt q0) (n : ℕ) :
    markedUnitTangent (S.rears q0 n) =
      markedUnitTangent (S.fronts q0 n) := by
  let w := compatibleRotation (S.rear n) (S.fronts q0 n)
  have hw : ‖w‖ = 1 :=
    norm_compatibleRotation (S.rear_regular n)
      (S.fronts_regular q0 hc hq0 n)
  have hnorm : ‖w * (S.rear n).2.1 0‖ = ‖(S.rear n).2.1 0‖ := by
    rw [norm_mul, hw, one_mul]
  rw [markedUnitTangent, rears, MarkedRigid.rigidData_vel, hnorm]
  change w * (S.rear n).2.1 0 / ‖(S.rear n).2.1 0‖ = _
  rw [mul_div_assoc]
  exact compatibleRotation_tangent (S.rear_regular n)
    (S.fronts_regular q0 hc hq0 n)

theorem physical (hc : 0 < c) (hq0 : IsTubeMember c 0 dlt q0)
    (n : ℕ) : Nonempty
      (PhysicalRearLimitKinematics kh (S.rears q0 n)
        (S.fronts q0 (n + 1))) := by
  exact S.physical_rigid n
    (compatibleTranslation (S.rear n) (S.fronts q0 n))
    (compatibleRotation (S.rear n) (S.fronts q0 n))
    (norm_compatibleRotation (S.rear_regular n)
      (S.fronts_regular q0 hc hq0 n))

theorem rear_normalized_alignment (hc : 0 < c)
    (hq0 : IsTubeMember c 0 dlt q0) (n : ℕ) :
    ∃ a w : ℂ, ∃ b : ℝ, ‖w‖ = 1 ∧
      S.rears q0 n = MarkedRigid.rigidData a w
        (MarkedShift.shiftData b (S.normalized n).data) := by
  obtain ⟨a0, w0, b, hw0, hrear⟩ := S.normalized_alignment n
  let w := compatibleRotation (S.rear n) (S.fronts q0 n)
  let a := compatibleTranslation (S.rear n) (S.fronts q0 n)
  refine ⟨a + w * a0, w * w0, b, ?_, ?_⟩
  · rw [norm_mul,
      norm_compatibleRotation (S.rear_regular n)
        (S.fronts_regular q0 hc hq0 n), hw0, one_mul]
  · change MarkedRigid.rigidData a w (S.rear n) =
      MarkedRigid.rigidData (a + w * a0) (w * w0)
        (MarkedShift.shiftData b (S.normalized n).data)
    rw [hrear, MarkedRigid.rigidData_comp]

/-- The recursively aligned all-level output. -/
structure Output where
  Q : ℕ → Data
  A : ℕ → Data
  Q_zero : Q 0 = q0
  front_tube : ∀ n, IsTubeMember c 0 dlt (Q n)
  rear_tube : ∀ n, ∃ cr dr : ℝ, 0 < cr ∧ 0 < dr ∧
    IsTubeMember cr 0 dr (A n)
  physical : ∀ n, Nonempty (PhysicalRearLimitKinematics kh (A n) (Q (n + 1)))
  marked_point : ∀ n, (A n).1 0 = (Q n).1 0
  marked_tangent : ∀ n, markedUnitTangent (A n) = markedUnitTangent (Q n)
  normalized_alignment : ∀ n, ∃ a w : ℂ, ∃ b : ℝ, ‖w‖ = 1 ∧
    A n = MarkedRigid.rigidData a w
      (MarkedShift.shiftData b (S.normalized n).data)

/-- Compatible markings assemble every pointwise exact pair into one coherent
sequence by Nat recursion. -/
def compatibleSequence (hc : 0 < c) (hq0 : IsTubeMember c 0 dlt q0) :
    S.Output q0 where
  Q := S.fronts q0
  A := S.rears q0
  Q_zero := rfl
  front_tube := S.fronts_tube q0 hc hq0
  rear_tube := S.rears_tube q0 hc hq0
  physical := S.physical q0 hc hq0
  marked_point := S.rear_marked_point_eq q0
  marked_tangent := S.rear_marked_tangent_eq q0 hc hq0
  normalized_alignment := S.rear_normalized_alignment q0 hc hq0

end PairSource

/-- Provider-facing physical normalization for an aligned carrier.  Unlike the
legacy normalization record, this retains the exact rigid motion and phase
relating the aligned datum to the canonical configured `kH` carrier. -/
structure AlignedPhysicalRearNormalization
    (D : ConstructedConfiguredSequenceWeighted.Data) (Q : ℕ → Data) where
  normalized : ∀ n, RearCarrier D n
  carrier : ℕ → Data
  carrier_tube : ∀ n, ∃ cr dr : ℝ, 0 < cr ∧ 0 < dr ∧
    IsTubeMember cr 0 dr (carrier n)
  alignment : ∀ n, ∃ a w : ℂ, ∃ b : ℝ, ‖w‖ = 1 ∧
    carrier n = MarkedRigid.rigidData a w
      (MarkedShift.shiftData b (normalized n).data)
  range_shift : ∀ n b,
    range (ev (Q (n + 1))) =
      range (UnitTangent.unitTangentMap
        (ev (MarkedShift.shiftData b (carrier n))))
  strictness_shift : ∀ n b,
    UnconditionalAssembly.LimitStrictnessDataH
      (MarkedShift.shiftData b (carrier n))

namespace PairSource.Output

variable {D : ConstructedConfiguredSequenceWeighted.Data} {kh c dlt : ℝ}
  {S : PairSource D kh c dlt} {q0 : Data} (O : S.Output q0)

/-- The coherent compatible sequence supplies the aligned normalization API
consumed by the rich base-stage adapter. -/
def toAlignedPhysicalRearNormalization
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c) :
    AlignedPhysicalRearNormalization D O.Q where
  normalized := S.normalized
  carrier := O.A
  carrier_tube := O.rear_tube
  alignment := O.normalized_alignment
  range_shift := by
    intro n b
    obtain ⟨cr, dr, hcr, -, hrear⟩ := O.rear_tube n
    let K := Nonempty.some (O.physical n)
    let P := K.toStageComponents hkh0 hkh1 hc (O.front_tube (n + 1))
    let H := (P.limitStrictness hc (O.front_tube (n + 1))).toH
      (fun s => ((P.limitStrictness hc
        (O.front_tube (n + 1))).curvature_deriv s).differentiableAt)
    calc
      range (ev (O.Q (n + 1))) =
          range (UnitTangent.unitTangentMap (ev (O.A n))) :=
        P.range_front_eq_unitTangent_rear
      _ = range (UnitTangent.unitTangentMap
          (ev (MarkedShift.shiftData b (O.A n)))) :=
        (range_unitTangent_shiftData hcr hrear H b).symm
  strictness_shift := by
    intro n b
    let cr := Classical.choose (O.rear_tube n)
    let hcrRest := Classical.choose_spec (O.rear_tube n)
    let dr := Classical.choose hcrRest
    let hrest := Classical.choose_spec hcrRest
    have hcr : 0 < cr := hrest.1
    have hrear : IsTubeMember cr 0 dr (O.A n) := hrest.2.2
    let K := Nonempty.some (O.physical n)
    let P := K.toStageComponents hkh0 hkh1 hc (O.front_tube (n + 1))
    let H := (P.limitStrictness hc (O.front_tube (n + 1))).toH
      (fun s => ((P.limitStrictness hc
        (O.front_tube (n + 1))).curvature_deriv s).differentiableAt)
    exact shiftLimitStrictnessDataH hcr hrear H b

end PairSource.Output

end ConfiguredCompatiblePhysicalRearSequence
