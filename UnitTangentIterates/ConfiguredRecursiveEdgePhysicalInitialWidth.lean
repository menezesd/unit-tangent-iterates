import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalInitialData
import UnitTangentIterates.ComplexHausdorffWidthBridge
import UnitTangentIterates.PhysicalRearLimitKinematicClosure
import UnitTangentIterates.ConfiguredAlignedQGeometry

/-! # Truthful selected-rear width at the physical base -/

noncomputable section

open Function Metric Set MarkedSpace RearTrack PathMetric
open scoped Pointwise

namespace ConfiguredRecursiveEdgePhysicalInitialWidth

open NormalizedSteeringPhysicalRescaling

private theorem support_add_range
    (a : ℂ) (F : ℝ → ℂ) (e : ℂ)
    (hF : Bornology.IsBounded (range F)) (he : ‖e‖ ≤ 1) :
    Width.support (range fun u ↦ a + F u) e =
      (inner ℝ a e : ℝ) + Width.support (range F) e := by
  unfold Width.support
  have hset :
      (fun x : ℂ ↦ (inner ℝ x e : ℝ)) '' (range fun u ↦ a + F u) =
        ({(inner ℝ a e : ℝ)} : Set ℝ) +
          ((fun x : ℂ ↦ (inner ℝ x e : ℝ)) '' range F) := by
    rw [Set.singleton_add]
    ext r
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨(inner ℝ (F u) e : ℝ), ⟨F u, ⟨u, rfl⟩, rfl⟩, ?_⟩
      exact (inner_add_left a (F u) e).symm
    · rintro ⟨_, ⟨_, ⟨u, rfl⟩, rfl⟩, rfl⟩
      refine ⟨a + F u, ⟨u, rfl⟩, ?_⟩
      exact inner_add_left a (F u) e
  rw [hset, csSup_add (Set.singleton_nonempty _)
    bddAbove_singleton (range_nonempty _ |>.image _)
    (Width.bddAbove_image (range F) hF he)]
  simp

theorem width_add_range
    (a : ℂ) (F : ℝ → ℂ) (e : ℂ)
    (hF : Bornology.IsBounded (range F)) (he : ‖e‖ ≤ 1) :
    Width.width (range fun u ↦ a + F u) e = Width.width (range F) e := by
  have hneg : ‖-e‖ ≤ 1 := by simpa using he
  rw [Width.width, Width.width, support_add_range a F e hF he,
    support_add_range a F (-e) hF hneg, inner_neg_right]
  ring

theorem hausdorffDist_rear_front_le_one
    {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) :
    hausdorffDist (range (ev rear)) (range (ev front)) ≤ 1 := by
  let dl := deltaPhys K.steering (perim front)
  have hdlC : Continuous dl := by
    unfold dl deltaPhys
    exact (Differentiable.continuous fun u =>
      K.steering.steering u |>.differentiableAt).comp
        (continuous_id.div_const _)
  have hmono : StrictMono (rearArclength dl) :=
    RearTrack.strictMono_rearArclength hdlC hkh1 hkh0
      (fun s => (deltaPhys_mem K.steering (P := perim front) s).1)
      (fun s => (deltaPhys_mem K.steering (P := perim front) s).2)
  refine hausdorffDist_le_of_infDist (by norm_num) ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine le_trans (infDist_le_dist_of_mem
      (show ev front (K.sf x) ∈ range (ev front) from mem_range_self _)) ?_
    rw [K.rear_track]
    rw [dist_eq_norm]
    simp [RearTrack.rearTrack]
  · rintro _ ⟨s, rfl⟩
    let x := rearArclength dl s
    have hsfx : K.sf x = s := by
      apply hmono.injective
      rw [K.arclength_rightInverse]
    refine le_trans (infDist_le_dist_of_mem
      (show ev rear x ∈ range (ev rear) from mem_range_self _)) ?_
    rw [K.rear_track, hsfx]
    rw [dist_eq_norm]
    simp [RearTrack.rearTrack]

theorem width_rear_le_front_add_two
    {kh : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hRear : Bornology.IsBounded (range (ev rear)))
    (hFront : Bornology.IsBounded (range (ev front)))
    {e : ℂ} (he : ‖e‖ = 1) :
    Width.width (range (ev rear)) e ≤
      Width.width (range (ev front)) e + 2 := by
  have H := ComplexHausdorffWidthBridge.abs_width_range_sub_le_hausdorff
    (range_nonempty _) (range_nonempty _) hRear hFront he
    (hausdorffDist_rear_front_le_one K hkh0 hkh1)
  linarith [le_trans (le_abs_self
    (Width.width (range (ev rear)) e - Width.width (range (ev front)) e)) H]

variable {MA NA : ℝ}

/-- The actual shifted base representative pays exactly the unit selected-
rear width loss relative to its aligned physical front. -/
theorem initial_width_le_front_add_two
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (hInitial : Bornology.IsBounded
      (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.initial O n).1)))
    (hFront : Bornology.IsBounded
      (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.frontData O n).1)))
    {e : ℂ} (he : ‖e‖ = 1) :
    Width.width
        (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.initial O n).1)) e ≤
      Width.width
        (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.frontData O n).1)) e + 2 := by
  let rear := ConfiguredRecursiveEdgePhysicalInitialData.initial O n
  let unshifted := ConfiguredRecursiveEdgePhysicalInitialData.unshiftedRear O n
  let front := ConfiguredRecursiveEdgePhysicalInitialData.frontData O n
  have hunshiftedPos : perim unshifted ≠ 0 :=
    ne_of_gt (perim_pos
      (ConfiguredBaseProfiledEdgeSourceFamily.data O).separation_zero_pos
      (ConfiguredRecursiveEdgePhysicalInitialData.unshiftedRear_tube O n))
  have hfrontPos : perim front ≠ 0 :=
    ne_of_gt (perim_pos
      (ConfiguredBaseProfiledEdgeSourceFamily.data O).separation_zero_pos
      (ConfiguredRecursiveEdgePhysicalInitialData.front_tube O n))
  have hrearRange : range (⇑rear.1) = range (ev unshifted) :=
    (ConfiguredRecursiveEdgePhysicalInitialData.initial_range O n).trans
      (MarkedSpace.range_ev_of_perim_ne_zero hunshiftedPos).symm
  have hfrontRange : range (⇑front.1) = range (ev front) :=
    (MarkedSpace.range_ev_of_perim_ne_zero hfrontPos).symm
  rw [hrearRange, hfrontRange]
  exact width_rear_le_front_add_two
    (ConfiguredRecursiveEdgePhysicalInitialData.unshiftedKinematics O n)
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one
    (by simpa [rear, unshifted, hrearRange] using hInitial)
    (by simpa [front, hfrontRange] using hFront) he

/-- The transverse direction of the aligned front paired with base rear `n`.
The front is row `n+1`, while the rear itself is row `n`. -/
def initialDirection
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) : ℂ :=
  (ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.presentation O n).rotation *
    O.direction (O.large.N + n + 1)

theorem initialDirection_norm
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    ‖initialDirection O n‖ = 1 := by
  rw [initialDirection, norm_mul,
    (ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.presentation O n).rotation_norm,
    O.direction_unit (O.large.N + n + 1), one_mul]

set_option maxHeartbeats 600000 in
/-- Rigid presentation and phase do not change the model width when the
measuring direction is rotated with the presentation. -/
theorem frontData_width_eq_model
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    Width.width
        (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.frontData O n).1))
        (initialDirection O n) =
      Width.width
        (range (TwoCapPairsAssembly.front
          ((ConfiguredBaseProfiledEdgeSourceFamily.data O).kappas (n + 1))
          (ConfiguredBaseProfiledEdgeSourceFamily.data O).model.thetaBase
          ((ConfiguredBaseProfiledEdgeSourceFamily.data O).Hs (n + 1))))
        (O.direction (O.large.N + n + 1)) := by
  let A := ConfiguredRecursiveEdgeSourceP0PhysicalBaseSourceAdapter.presentation O n
  let Q := O.Q (n + 1)
  have hcurve (u : ℝ) :
      (ConfiguredRecursiveEdgePhysicalInitialData.frontData O n).1 u =
        A.translation + A.rotation * Q.1 (u + A.phase) := by
    rfl
  have hrange :
      range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.frontData O n).1) =
        range (fun u ↦ A.translation + A.rotation * Q.1 u) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u + A.phase, hcurve u⟩
    · rintro ⟨u, rfl⟩
      refine ⟨u - A.phase, ?_⟩
      rw [hcurve]
      congr 2
      ring
  have hQcont : Continuous Q.1 :=
    continuous_iff_continuousAt.2 fun u ↦
      ((O.pair.input.front_tube (n + 1)).hasDerivAt_curve u).continuousAt
  have hrotCont : Continuous (fun u ↦ A.rotation * Q.1 u) :=
    continuous_const.mul hQcont
  have hrotPer : Function.Periodic (fun u ↦ A.rotation * Q.1 u) 1 :=
    fun u ↦ by
      simpa [Q] using congrArg (fun z : ℂ ↦ A.rotation * z)
        ((O.pair.input.front_tube (n + 1)).periodic u)
  have hrotBounded : Bornology.IsBounded (range fun u ↦ A.rotation * Q.1 u) :=
    CurveDistance.isBounded_range_of_periodic hrotCont hrotPer one_pos
  have hQperim : perim Q ≠ 0 := by
    rw [(O.model_data (n + 1)).1]
    exact ne_of_gt (mul_pos (by norm_num)
      ((ConfiguredBaseProfiledEdgeSourceFamily.data O).model.separation_pos (n + 1)))
  have hQrange : range (⇑Q.1) =
      range (TwoCapPairsAssembly.front
        ((ConfiguredBaseProfiledEdgeSourceFamily.data O).kappas (n + 1))
        (ConfiguredBaseProfiledEdgeSourceFamily.data O).model.thetaBase
        ((ConfiguredBaseProfiledEdgeSourceFamily.data O).Hs (n + 1))) :=
    (MarkedSpace.range_ev_of_perim_ne_zero hQperim).symm.trans
      (congrArg range (O.model_data (n + 1)).2)
  rw [hrange, width_add_range A.translation
    (fun u ↦ A.rotation * Q.1 u) (initialDirection O n) hrotBounded]
  · change Width.width (range fun u ↦ A.rotation * Q.1 u)
        (A.rotation * O.direction (O.large.N + n + 1)) = _
    calc
      _ = Width.width (range (⇑Q.1)) (O.direction (O.large.N + n + 1)) :=
        ModelWidth.width_mul_range A.rotation Q.1
          (O.direction (O.large.N + n + 1))
          A.rotation_norm
      _ = _ := congrArg (fun S : Set ℂ ↦
        Width.width S (O.direction (O.large.N + n + 1))) hQrange
  · exact (initialDirection_norm O n).le

set_option maxHeartbeats 600000 in
theorem frontData_bounded
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    Bornology.IsBounded
      (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.frontData O n).1)) :=
  ConfiguredAlignedQGeometry.bounded_range O.pair O.model_data (n + 1)

set_option maxHeartbeats 600000 in
theorem frontData_width_add_two_le_Cw
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ) :
    Width.width
        (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.frontData O n).1))
        (initialDirection O n) + 2 ≤ O.Cw := by
  rw [frontData_width_eq_model O n]
  simpa [ConfiguredBaseProfiledEdgeSourceFamily.data,
    ConstructedConfiguredInductiveTubeBudget.WeightedData.shift,
    Nat.add_assoc] using
    O.model_width_add_two (O.large.N + n + 1)

set_option maxHeartbeats 600000 in
/-- The truthful selected rear satisfies the stored enlarged scalar width
ceiling.  No range equality with the model front is asserted. -/
theorem initial_width_le_Cw
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (hInitial : Bornology.IsBounded
      (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.initial O n).1))) :
    Width.width
        (range (⇑(ConfiguredRecursiveEdgePhysicalInitialData.initial O n).1))
        (initialDirection O n) ≤ O.Cw := by
  exact (initial_width_le_front_add_two O n hInitial
    (frontData_bounded O n) (initialDirection_norm O n)).trans
      (frontData_width_add_two_le_Cw O n)

end ConfiguredRecursiveEdgePhysicalInitialWidth
