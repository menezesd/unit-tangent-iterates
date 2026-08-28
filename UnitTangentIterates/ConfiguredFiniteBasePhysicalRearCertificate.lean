import UnitTangentIterates.ConfiguredRichBaseStageProvider
import UnitTangentIterates.PhysicalRearLimitKinematicClosure
import UnitTangentIterates.MarkedDistanceCurvature
import UnitTangentIterates.CurvatureFromMarkedDistance

/-!
# Configured finite base physical rear certificate

The configured interpolation uses a canonically normalized carrier of the
model rear curvature `kH`.  A physical selected rear is determined by that
curvature only up to a rigid motion and a cyclic marking shift, so it is not
sound to identify the carrier with the canonical marked selected inverse.

`AlignedPhysicalCarrierFamily` isolates the one genuinely geometric input:
the exact `kH` carrier, after any cyclic marking shift, is a physical rear of
the chosen successor.  Everything else needed at the rich base stage is
derived below, including the ordinary tube certificate, exact unit-tangent
range, Harnack strictness, canonical normalized marking equations, and the
curvature and acceleration bounds.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredFiniteBasePhysicalRearCertificate

open ConfiguredApproximateDefectPathActualTerminal
  ConfiguredRichBaseStageProvider
  CurvatureInterpolation

/-- The minimal joint-alignment datum for the configured base family.

The successor tube is retained because it is the closed convexity input to
the physical rear Frenet chain.  `physical_shift` records the compatible
choice of rigid motion and marking; it deliberately does not assert equality
with `SelectedInverseMap.selInv` as marked data. -/
structure AlignedPhysicalCarrierFamily
    (D : ConstructedConfiguredSequenceWeighted.Data) (Q : ℕ → Data)
    (kh c dlt : ℝ) where
  carrier : ∀ n, RearCarrier D n
  front_tube : ∀ n, IsTubeMember c 0 dlt (Q (n + 1))
  physical_shift : ∀ n b, Nonempty
    (PhysicalRearLimitKinematics kh
      (MarkedShift.shiftData b (carrier n).data) (Q (n + 1)))

namespace AlignedPhysicalCarrierFamily

variable {D : ConstructedConfiguredSequenceWeighted.Data} {Q : ℕ → Data}
  {kh c dlt : ℝ} (F : AlignedPhysicalCarrierFamily D Q kh c dlt)

/-- The arclength derivative presentation of the exact configured carrier. -/
theorem carrier_curve_deriv (n : ℕ) (s : ℝ) :
    HasDerivAt (ev (F.carrier n).data)
      (Complex.exp (Complex.I *
        (tangentAngle (D.model.configs n).kH D.model.thetaBase s : ℂ))) s := by
  rw [(F.carrier n).curve_eq]
  simpa [SelectedInverseCarrier.tau_eq_exp] using
    (hasDerivAt_interpCurve
      (kappa := (D.model.configs n).kH)
      (θ₀ := D.model.thetaBase) (L := D.Hs n)
      (D.model.configs n).continuous_kH s)

/-- The tangent angle of the configured carrier has derivative `kH`. -/
theorem carrier_angle_deriv (n : ℕ) (s : ℝ) :
    HasDerivAt
      (tangentAngle (D.model.configs n).kH D.model.thetaBase)
      ((D.model.configs n).kH s) s :=
  hasDerivAt_tangentAngle (D.model.configs n).continuous_kH s

/-- Intrinsic arclength curvature of the carrier is exactly the configured
rear curvature. -/
theorem carrier_arcCurv_eq (n : ℕ) (s : ℝ) :
    UnconditionalAssembly.arcCurv (F.carrier n).data s =
      (D.model.configs n).kH s := by
  symm
  exact RearTrackEmbedded.curvature_eq_arcCurv
    (F.carrier n).c_pos (F.carrier n).tube
    (F.carrier_curve_deriv n) (carrier_angle_deriv (D := D) n) s

/-- The configured carrier written in the normalized marked parameter. -/
theorem carrier_marked_curve_eq (n : ℕ) (u : ℝ) :
    (F.carrier n).data.1 u =
      interpCurve (D.model.configs n).kH D.model.thetaBase (D.Hs n)
        ((2 * D.Hs n) * u) := by
  rw [MarkedSpace.curve_eq_ev _ _
    (ne_of_gt (perim_pos (F.carrier n).c_pos (F.carrier n).tube)),
    (F.carrier n).perim_eq, (F.carrier n).curve_eq]

/-- The exact constant-speed marking equation for the carrier velocity. -/
theorem carrier_marked_velocity_eq (n : ℕ) (u : ℝ) :
    (F.carrier n).data.2.1 u =
      (((2 * D.Hs n : ℝ) : ℂ) *
        Complex.exp (Complex.I *
          (tangentAngle (D.model.configs n).kH D.model.thetaBase
            ((2 * D.Hs n) * u) : ℂ))) := by
  rw [MarkedSpace.vel_eq (F.carrier n).c_pos
    (F.carrier n).tube (F.carrier_curve_deriv n) u,
    (F.carrier n).perim_eq]

/-- The exact constant-speed marking equation for the carrier acceleration. -/
theorem carrier_marked_acceleration_eq (n : ℕ) (u : ℝ) :
    (F.carrier n).data.2.2 u =
      ((((2 * D.Hs n) ^ 2 : ℝ) : ℂ) *
        (Complex.I *
          (((D.model.configs n).kH ((2 * D.Hs n) * u) : ℝ) : ℂ) *
          Complex.exp (Complex.I *
            (tangentAngle (D.model.configs n).kH D.model.thetaBase
              ((2 * D.Hs n) * u) : ℂ)))) := by
  rw [MarkedSpace.acc_eq (F.carrier n).c_pos
    (F.carrier n).tube (F.carrier_curve_deriv n)
    (carrier_angle_deriv (D := D) n) u, (F.carrier n).perim_eq]

/-- The intrinsic normalized-parameter curvature is the configured `kH`
evaluated at physical arclength. -/
theorem carrier_dataCurv_eq (n : ℕ) (u : ℝ) :
    CurvatureFromMarkedDistance.dataCurv (F.carrier n).data u =
      (D.model.configs n).kH ((2 * D.Hs n) * u) := by
  have h := F.carrier_arcCurv_eq n ((2 * D.Hs n) * u)
  have hH : 0 < D.Hs n := D.model.separation_pos n
  have hdiv : (2 * D.Hs n * u) / (2 * D.Hs n) = u := by
    field_simp
  simpa [UnconditionalAssembly.arcCurv, (F.carrier n).perim_eq, hdiv] using h

/-- The normalized-parameter curvature is nonnegative. -/
theorem carrier_dataCurv_nonnegative (n : ℕ) (u : ℝ) :
    0 ≤ CurvatureFromMarkedDistance.dataCurv (F.carrier n).data u := by
  rw [F.carrier_dataCurv_eq n u]
  exact (D.model.configs n).kH_nonneg _

/-- The normalized-parameter curvature is bounded by the configured uniform
curvature ceiling. -/
theorem carrier_dataCurv_le (n : ℕ) (u : ℝ) :
    CurvatureFromMarkedDistance.dataCurv (F.carrier n).data u ≤ D.kstar := by
  rw [F.carrier_dataCurv_eq n u]
  simpa [D.model_kstar] using (D.model.configs n).kH_le
    ((2 * D.Hs n) * u)

/-- The carrier acceleration has the canonical quadratic perimeter bound. -/
theorem carrier_acceleration_norm_le (n : ℕ) (u : ℝ) :
    ‖(F.carrier n).data.2.2 u‖ ≤ (2 * D.Hs n) ^ 2 * D.kstar := by
  have hv : 0 < ‖(F.carrier n).data.2.1 u‖ :=
    lt_of_lt_of_le (F.carrier n).c_pos ((F.carrier n).tube.speed_lb u)
  have hk : (D.model.configs n).kH ((2 * D.Hs n) * u) ≤ D.kstar := by
    simpa [D.model_kstar] using (D.model.configs n).kH_le
      ((2 * D.Hs n) * u)
  rw [CurvatureFromMarkedDistance.norm_acc_eq (F.carrier n).tube hv,
    F.carrier_dataCurv_eq n u,
    abs_of_nonneg ((D.model.configs n).kH_nonneg _),
    norm_vel_eq_perim (F.carrier n).tube u,
    (F.carrier n).perim_eq]
  calc
    (D.model.configs n).kH ((2 * D.Hs n) * u) * (2 * D.Hs n) ^ 2
        ≤ D.kstar * (2 * D.Hs n) ^ 2 :=
      mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    _ = (2 * D.Hs n) ^ 2 * D.kstar := by ring

/-- Physical alignment supplies exact range and integrated strictness for
every marking shift of the exact carrier. -/
def physicalRearNormalization (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c) :
    PhysicalRearNormalization D Q where
  carrier := F.carrier
  range_shift := by
    intro n b
    let K := Nonempty.some (F.physical_shift n b)
    let S := K.toStageComponents hkh0 hkh1 hc (F.front_tube n)
    rw [← range_ev_of_perim_ne_zero
      (ne_of_gt (perim_pos hc (F.front_tube n)))]
    exact S.range_front_eq_unitTangent_rear
  strictness_shift := by
    intro n b
    let K := Nonempty.some (F.physical_shift n b)
    let S := K.toStageComponents hkh0 hkh1 hc (F.front_tube n)
    let R := S.limitStrictness hc (F.front_tube n)
    exact R.toH (fun s => (R.curvature_deriv s).differentiableAt)

/-- The complete finite base certificate consumed by the configured rich
provider and by quantitative estimates on the exact `kH` carriers. -/
structure Certificate (F : AlignedPhysicalCarrierFamily D Q kh c dlt) where
  normalization : PhysicalRearNormalization D Q
  rear_tube : ∀ n, IsTubeMember (normalization.carrier n).c 0
    (normalization.carrier n).dlt (normalization.carrier n).data
  marked_curve_eq : ∀ n u,
    (normalization.carrier n).data.1 u =
      interpCurve (D.model.configs n).kH D.model.thetaBase (D.Hs n)
        ((2 * D.Hs n) * u)
  marked_velocity_eq : ∀ n u,
    (normalization.carrier n).data.2.1 u =
      (((2 * D.Hs n : ℝ) : ℂ) *
        Complex.exp (Complex.I *
          (tangentAngle (D.model.configs n).kH D.model.thetaBase
            ((2 * D.Hs n) * u) : ℂ)))
  marked_acceleration_eq : ∀ n u,
    (normalization.carrier n).data.2.2 u =
      ((((2 * D.Hs n) ^ 2 : ℝ) : ℂ) *
        (Complex.I *
          (((D.model.configs n).kH ((2 * D.Hs n) * u) : ℝ) : ℂ) *
          Complex.exp (Complex.I *
            (tangentAngle (D.model.configs n).kH D.model.thetaBase
              ((2 * D.Hs n) * u) : ℂ))))
  curvature_nonnegative : ∀ n u,
    0 ≤ CurvatureFromMarkedDistance.dataCurv
      (normalization.carrier n).data u
  curvature_le : ∀ n u,
    CurvatureFromMarkedDistance.dataCurv
      (normalization.carrier n).data u ≤ D.kstar
  acceleration_norm_le : ∀ n u,
    ‖(normalization.carrier n).data.2.2 u‖ ≤
      (2 * D.Hs n) ^ 2 * D.kstar

/-- Construct the full certificate from the single aligned-family residual. -/
def certificate (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c) :
    F.Certificate := by
  let R := F.physicalRearNormalization hkh0 hkh1 hc
  refine
    { normalization := R
      rear_tube := ?_
      marked_curve_eq := ?_
      marked_velocity_eq := ?_
      marked_acceleration_eq := ?_
      curvature_nonnegative := ?_
      curvature_le := ?_
      acceleration_norm_le := ?_ }
  · exact fun n => (F.carrier n).tube
  · exact F.carrier_marked_curve_eq
  · exact F.carrier_marked_velocity_eq
  · exact F.carrier_marked_acceleration_eq
  · exact F.carrier_dataCurv_nonnegative
  · exact F.carrier_dataCurv_le
  · exact F.carrier_acceleration_norm_le

end AlignedPhysicalCarrierFamily

end ConfiguredFiniteBasePhysicalRearCertificate
