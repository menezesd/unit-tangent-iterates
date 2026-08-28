import UnitTangentIterates.ConfiguredModelPairPhaseCarrier
import UnitTangentIterates.ConfiguredPairSourceAdapter
import UnitTangentIterates.FinitePullbackPhysicalRearKinematicsConstructor
import UnitTangentIterates.CurvatureFromMarkedDistance
import UnitTangentIterates.SelectedInverseShiftEquivariance
import UnitTangentIterates.PhysicalRearKinematicsShift

/-!
# Configured exact model pairs as a compatible pair source

This module performs the normalized-marking conversion left after the analytic
rigid/phase identity.  The raw front is the next configured model front shifted
by the retained phase and moved by the common front rigid motion.  The raw rear
is the canonical `kH` carrier moved by the rear rigid motion.  Uniqueness of the
marked selected inverse identifies this raw rear with `selInv`, after which the
existing physical-kinematics constructor and compatible-marking recursion apply.
-/

noncomputable section

open Function Set MarkedSpace PathMetric ModelOrbitDefect CurvatureInterpolation
open RearTrack

namespace ConfiguredModelPairSource

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredCompatiblePhysicalRearSequence
  ConfiguredModelPairPhaseCarrier

structure Input (D : ConstructedConfiguredSequenceWeighted.Data)
    (Q : ℕ → Data) (kh c dlt : ℝ) where
  carrier : ∀ n, RearCarrier D n
  front_model : ∀ n,
    perim (Q n) = 2 * D.Hs n ∧
    ev (Q n) = TwoCapPairsAssembly.front
      (D.kappas n) D.model.thetaBase (D.Hs n)
  front_tube : ∀ n, IsTubeMember c 0 dlt (Q n)
  c_pos : 0 < c
  kh_nonneg : 0 ≤ kh
  kh_lt_one : kh < 1
  steering_cap_le : D.model.a ≤ kh

namespace Input

variable {D : ConstructedConfiguredSequenceWeighted.Data}
  {Q : ℕ → Data} {kh c dlt : ℝ} (S : Input D Q kh c dlt)

def identity (S : Input D Q kh c dlt) (n : ℕ) : Identity D n :=
  Nonempty.some (ConfiguredModelPairPhaseCarrier.exists_identity D n)

def frontShift (S : Input D Q kh c dlt) (n : ℕ) : ℝ :=
  D.phase / (2 * D.Hs (n + 1))

def front (n : ℕ) : Data :=
  MarkedRigid.rigidData (S.identity n).frontTranslation
    (S.identity n).frontRotation
    (MarkedShift.shiftData (S.frontShift n) (Q (n + 1)))

def rear (n : ℕ) : Data :=
  MarkedRigid.rigidData (S.identity n).rearTranslation
    (S.identity n).rearRotation (S.carrier n).data

theorem front_tube_raw (n : ℕ) : IsTubeMember c 0 dlt (S.front n) := by
  exact MarkedRigid.isTubeMember_rigidData
    (S.identity n).frontRotation_norm
    (MarkedShift.isTubeMember_shiftData (S.front_tube (n + 1)) (S.frontShift n))

theorem rear_tube_raw (n : ℕ) :
    IsTubeMember (S.carrier n).c 0 (S.carrier n).dlt (S.rear n) := by
  exact MarkedRigid.isTubeMember_rigidData
    (S.identity n).rearRotation_norm (S.carrier n).tube

theorem front_perim (n : ℕ) : perim (S.front n) = 2 * D.Hs (n + 1) := by
  calc
    perim (S.front n) = perim (MarkedShift.shiftData (S.frontShift n) (Q (n + 1))) := by
      simp [front, MarkedSpace.perim, norm_mul,
        (S.identity n).frontRotation_norm]
    _ = perim (Q (n + 1)) :=
      SelectedInverseShiftEquivariance.perim_shiftData
        (S.front_tube (n + 1)) (S.frontShift n)
    _ = 2 * D.Hs (n + 1) := (S.front_model (n + 1)).1

theorem rear_perim (n : ℕ) : perim (S.rear n) = 2 * D.Hs n := by
  calc
    perim (S.rear n) = perim (S.carrier n).data := by
      simp [rear, MarkedSpace.perim, norm_mul,
        (S.identity n).rearRotation_norm]
    _ = 2 * D.Hs n := (S.carrier n).perim_eq

theorem front_ev (n : ℕ) : ev (S.front n) = currentFront D n := by
  funext s
  have hQpos : 0 < perim (Q (n + 1)) :=
    perim_pos S.c_pos (S.front_tube (n + 1))
  have hshift := SelectedInverseShiftEquivariance.ev_shiftData
    (S.front_tube (n + 1)) hQpos.ne' (S.frontShift n) s
  have hrig : ev (S.front n) s =
      (S.identity n).frontTranslation + (S.identity n).frontRotation *
        ev (MarkedShift.shiftData (S.frontShift n) (Q (n + 1))) s := by
    simp [front, ev, MarkedSpace.perim,
      (S.identity n).frontRotation_norm]
  rw [hrig, hshift, (S.front_model (n + 1)).2]
  have harg : s + S.frontShift n * perim (Q (n + 1)) = s + D.phase := by
    rw [(S.front_model (n + 1)).1]
    dsimp [frontShift]
    field_simp [ne_of_gt (D.model.separation_pos (n + 1))]
  rw [harg]
  exact ((S.identity n).front_eq_next_shift s).symm

theorem rear_ev (n : ℕ) : ev (S.rear n) = currentRearOwn D n := by
  funext x
  have hrig : ev (S.rear n) x =
      (S.identity n).rearTranslation + (S.identity n).rearRotation *
        ev (S.carrier n).data x := by
    simp [rear, ev, MarkedSpace.perim,
      (S.identity n).rearRotation_norm]
  rw [hrig, (S.carrier n).curve_eq]
  exact ((S.identity n).rearOwn_eq_carrier x).symm

theorem steering_mem (S : Input D Q kh c dlt) (n : ℕ) (s : ℝ) :
    currentSteering D n s ∈ Icc 0 (Real.arcsin kh) := by
  let cfg := D.model.configs n
  have hlow : 0 ≤ currentSteering D n s := by
    exact Real.arcsin_nonneg.mpr (cfg.Y_nonneg s)
  have hYle : cfg.Y s ≤ D.model.a :=
    (le_abs_self _).trans (cfg.hYa s)
  have hupp : currentSteering D n s ≤ Real.arcsin kh := by
    exact (Real.arcsin_le_arcsin hYle).trans
      (Real.arcsin_le_arcsin (Input.steering_cap_le S))
  exact ⟨hlow, hupp⟩

theorem isMarkedSelectedInverse (n : ℕ) :
    SelectedInverseMap.IsMarkedSelectedInverse kh (S.front n) (S.rear n) := by
  let cfg := D.model.configs n
  let H := D.Hs (n + 1)
  refine ⟨⟨(S.carrier n).c, 0, (S.carrier n).dlt, S.rear_tube_raw n⟩,
    currentAngle D n, currentCurvature D n, currentSteering D n, cfg.sf,
    ?_, ?_, ?_, S.steering_mem n, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [S.front_ev n]
    exact TwoCapPairsAssembly.front_hasDerivAt cfg.continuous_frontCurvature s
  · intro s
    exact hasDerivAt_tangentAngle cfg.continuous_frontCurvature s
  · rw [S.front_perim n]
    simpa using cfg.periodic_dl.nat_mul 2
  · exact cfg.hasDerivAt_dl
  · exact cfg.sf_rightInverse
  · rw [S.rear_perim n, S.front_perim n]
    change 2 * D.Hs n = rearArclength (modelSteering cfg.Y) (2 * H)
    rw [show 2 * H = H + H by ring,
      SelectedInverseShiftEquivariance.rearArclength_add_period
        cfg.continuous_dl cfg.periodic_dl H]
    have hperiod : rearArclength (modelSteering cfg.Y) H = D.Hs n := by
      simpa [ModelOrbitDefect.modelRearArclength] using cfg.rearPeriod_eq
    rw [hperiod]
    ring
  · intro x
    rw [S.rear_ev n, S.front_ev n]
    rfl

theorem rear_eq_selInv (n : ℕ) :
    S.rear n = SelectedInverseMap.selInv kh (S.front n) :=
  SelectedInverseMap.eq_selInv_of_isMarkedSelectedInverse
    S.c_pos S.kh_nonneg S.kh_lt_one (S.front_tube_raw n)
    (S.isMarkedSelectedInverse n)

theorem front_curvature_le (S : Input D Q kh c dlt)
    (hkstar : D.kstar ≤ kh) (n : ℕ) (s : ℝ) :
    currentCurvature D n s ≤ kh := by
  change ModelOrbitDefect.modelCurvature (D.model.configs n).y
    (D.model.configs n).yd (D.Hs (n + 1)) s ≤ kh
  rw [D.model_current_curvature_eq_next_shift n s]
  exact (D.model.curvature_upper (n + 1) (s + D.phase)).trans
    (by simpa [D.model_kstar] using hkstar)

theorem front_orientedCurvature_le
    (hkstar : D.kstar ≤ kh) (n : ℕ) (u : ℝ) :
    ((starRingEnd ℂ) ((S.front n).2.1 u) * (S.front n).2.2 u).im ≤
      kh * ‖(S.front n).2.1 u‖ ^ 3 := by
  have hv : 0 < ‖(S.front n).2.1 u‖ :=
    lt_of_lt_of_le S.c_pos ((S.front_tube_raw n).speed_lb u)
  let P := perim (S.front n)
  have hcurv : CurvatureFromMarkedDistance.dataCurv (S.front n) u =
      currentCurvature D n (P * u) := by
    have h := RearTrackEmbedded.curvature_eq_arcCurv S.c_pos
      (S.front_tube_raw n)
      (fun s => by
        rw [S.front_ev n]
        exact TwoCapPairsAssembly.front_hasDerivAt
          (theta0 := D.model.thetaBase) (H := D.Hs (n + 1))
          (D.model.configs n).continuous_frontCurvature s)
      (fun s => hasDerivAt_tangentAngle
        (θ₀ := D.model.thetaBase)
        (D.model.configs n).continuous_frontCurvature s) (P * u)
    rw [UnconditionalAssembly.arcCurv] at h
    have hP : 0 < P := perim_pos S.c_pos (S.front_tube_raw n)
    have harg : P * u / perim (S.front n) = u := by
      simpa only [P] using (mul_div_cancel_left₀ u (ne_of_gt hP))
    simpa [harg] using h.symm
  have him : ((starRingEnd ℂ) ((S.front n).2.1 u) * (S.front n).2.2 u).im =
      CurvatureFromMarkedDistance.dataCurv (S.front n) u *
        ‖(S.front n).2.1 u‖ ^ 3 := by
    unfold CurvatureFromMarkedDistance.dataCurv
    field_simp [ne_of_gt hv]
  rw [him, hcurv]
  exact mul_le_mul_of_nonneg_right
    (S.front_curvature_le hkstar n (P * u)) (by positivity)

theorem physical (hkstar : D.kstar ≤ kh) (n : ℕ) : Nonempty
    (PhysicalRearLimitKinematics kh (S.rear n) (S.front n)) := by
  have hturn : ∃ Theta K : ℝ → ℝ,
      (∀ s, HasDerivAt (ev (S.front n))
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta (K s) s) ∧
      (∀ s, Theta (s + perim (S.front n)) = Theta s + 2 * Real.pi) := by
    refine ⟨currentAngle D n, currentCurvature D n, ?_, ?_, ?_⟩
    · intro s
      rw [S.front_ev n]
      exact TwoCapPairsAssembly.front_hasDerivAt
        (D.model.configs n).continuous_frontCurvature s
    · exact hasDerivAt_tangentAngle
        (D.model.configs n).continuous_frontCurvature
    · intro s
      rw [S.front_perim n]
      exact TwoCapMarked.frontAngle_add_period
        (D.model.configs n).continuous_frontCurvature
        (periodic_modelCurvature _ _ _)
        (integral_modelCurvature_eq_pi
          (D.model.configs n).ha (D.model.configs n).hH
          (D.model.configs n).continuous_y (D.model.configs n).hydc
          (D.model.configs n).hyderiv (D.model.configs n).abs_y_le
          (D.model.configs n).hydb (D.model.configs n).hy0
          (D.model.configs n).hyint (D.model.configs n).ha0
          (D.model.configs n).ha1 (D.model.configs n).hYa
          (D.model.configs n).hmass) s
  let K := Nonempty.some
    (FinitePullbackPhysicalRearKinematicsConstructor.exists_kinematics_selInv_of_curvature_turning
      S.c_pos S.kh_nonneg S.kh_lt_one (S.front_tube_raw n)
      (S.front_orientedCurvature_le hkstar n) hturn)
  rw [S.rear_eq_selInv n]
  exact ⟨K⟩

/-- Physical kinematics for the configured raw pair retaining the model
configuration's exact inverse-arclength map. -/
theorem physicalExact (n : ℕ) :
    ∃ K : PhysicalRearLimitKinematics kh (S.rear n) (S.front n),
      K.sf = (D.model.configs n).sf := by
  let cfg := D.model.configs n
  apply PathMetric.exists_physicalRearLimitKinematics_of_components
    S.c_pos S.kh_nonneg S.kh_lt_one (S.front_tube_raw n)
    (currentAngle D n) (currentCurvature D n) (currentSteering D n) cfg.sf
  · intro s
    rw [S.front_ev n]
    exact TwoCapPairsAssembly.front_hasDerivAt cfg.continuous_frontCurvature s
  · exact hasDerivAt_tangentAngle cfg.continuous_frontCurvature
  · rw [S.front_perim n]
    simpa using cfg.periodic_dl.nat_mul 2
  · exact S.steering_mem n
  · exact cfg.hasDerivAt_dl
  · exact cfg.sf_rightInverse
  · rw [S.rear_perim n, S.front_perim n]
    change 2 * D.Hs n = rearArclength (modelSteering cfg.Y)
      (2 * D.Hs (n + 1))
    rw [show 2 * D.Hs (n + 1) = D.Hs (n + 1) + D.Hs (n + 1) by ring,
      SelectedInverseShiftEquivariance.rearArclength_add_period
        cfg.continuous_dl cfg.periodic_dl (D.Hs (n + 1))]
    have hperiod : rearArclength (modelSteering cfg.Y) (D.Hs (n + 1)) =
        D.Hs n := by
      simpa [ModelOrbitDefect.modelRearArclength] using cfg.rearPeriod_eq
    rw [hperiod]
    ring
  · intro x
    rw [S.rear_ev n, S.front_ev n]
    rfl

/-- The exact configured physical pair at an arbitrary rear marking.  The
front shift here is relative to the already phase-shifted raw current front;
its absolute phase against `Q (n+1)` is recorded by `frontPhase`. -/
def frontRelativePhase (S : Input D Q kh c dlt) (n : ℕ) (r : ℝ) : ℝ :=
  (D.model.configs n).sf (2 * D.Hs n * r) / (2 * D.Hs (n + 1))

def frontPhase (S : Input D Q kh c dlt) (n : ℕ) (r : ℝ) : ℝ :=
  ((D.model.configs n).sf (2 * D.Hs n * r) + D.phase) /
    (2 * D.Hs (n + 1))

theorem physicalAtPhase (n : ℕ) (r : ℝ) : Nonempty
    (PhysicalRearLimitKinematics kh
      (MarkedShift.shiftData r (S.rear n))
      (MarkedShift.shiftData (S.frontRelativePhase n r) (S.front n))) := by
  obtain ⟨K, hKsf⟩ := S.physicalExact n
  refine ⟨K.shift S.c_pos (S.front_tube_raw n)
    (S.carrier n).c_pos (S.rear_tube_raw n)
    (S.frontRelativePhase n r) r ?_⟩
  rw [hKsf, S.rear_perim n, S.front_perim n]
  unfold frontRelativePhase
  field_simp [ne_of_gt (D.model.separation_pos (n + 1))]

def pairSource : PairSource D kh c dlt where
  normalized := S.carrier
  rear := S.rear
  front := S.front
  rear_regular := fun n => lt_of_lt_of_le (S.carrier n).c_pos
    ((S.rear_tube_raw n).speed_lb 0)
  rear_tube := fun n => ⟨(S.carrier n).c, (S.carrier n).dlt,
    (S.carrier n).c_pos, (S.carrier n).dlt_pos, S.rear_tube_raw n⟩
  front_tube := S.front_tube_raw
  normalized_alignment := by
    intro n
    refine ⟨(S.identity n).rearTranslation, (S.identity n).rearRotation,
      0, (S.identity n).rearRotation_norm, ?_⟩
    simp [rear]
  physical_rigid := by
    intro n a w hw
    obtain ⟨K, -⟩ := S.physicalExact n
    exact ⟨ConfiguredPairSourceAdapter.physicalRearLimitKinematics_rigid
      K a w hw⟩

def compatibleSequence (q0 : Data) (hq0 : IsTubeMember c 0 dlt q0) :
    S.pairSource.Output q0 :=
  S.pairSource.compatibleSequence q0 S.c_pos hq0

/-- The configured exact-pair construction, compatible-marking recursion, and
physical finite-stage kinematics packaged in the aligned normalization API.
This is the provider-facing connection to the finite base physical rear
certificate chain; it retains the canonical `kH` carrier together with the
rigid/phase relation to the recursively aligned carrier. -/
def alignedPhysicalRearNormalization (q0 : Data)
    (hq0 : IsTubeMember c 0 dlt q0) :
    AlignedPhysicalRearNormalization D (S.compatibleSequence q0 hq0).Q :=
  (S.compatibleSequence q0 hq0).toAlignedPhysicalRearNormalization
    S.kh_nonneg S.kh_lt_one S.c_pos

end Input

end ConfiguredModelPairSource
