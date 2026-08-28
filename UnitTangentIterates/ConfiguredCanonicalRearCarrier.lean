import UnitTangentIterates.ConfiguredApproximateDefectPathActualTerminal
import UnitTangentIterates.ConfiguredInductiveTubeBudget
import UnitTangentIterates.ConstructedConfiguredInductiveTubeBudget

/-!
# Canonical configured rear carriers

The configured transition already contains a periodic rear curvature `kH` at
every level.  This file applies the floor-free model-orbit constructor to
those curvatures and packages the resulting constant-speed marked curves as
the `RearCarrier`s used by the actual-terminal interpolation.

Unlike the earlier carrier-facing APIs, the output retains one genuine tube
for every level: speed constant `Hs 0` and chord constant `chordBase / 2`.
-/

noncomputable section

open Set Function Real MarkedSpace
open UnconditionalAssembly ModelOrbitDefect TwoCapPairsAssembly

namespace ConfiguredCanonicalRearCarrier

open ConfiguredApproximateDefectPathActualTerminal

/-- The curvature sequence of the configured physical rears. -/
def rearCurvature (D : ConstructedConfiguredSequenceWeighted.Data) :
    ℕ → ℝ → ℝ :=
  fun n => (D.model.configs n).kH

/-- Canonical constant-speed carriers for every configured rear, all in the
same floor-free tube used by the inductive tube budget. -/
theorem exists_carriers (D : ConstructedConfiguredSequenceWeighted.Data) :
    ∃ A : ∀ n, RearCarrier D n,
      ∀ n, IsTubeMember (D.Hs 0) 0
        (ConfiguredInductiveTubeBudget.chordBase D.model / 2) (A n).data := by
  let kr : ℕ → ℝ → ℝ := rearCurvature D
  have hH : ∀ n, 0 < D.Hs n := D.model.separation_pos
  have hk : ∀ n, Continuous (kr n) := fun n => by
    simpa [kr, rearCurvature] using (D.model.configs n).continuous_kH
  have hper : ∀ n, Periodic (kr n) (D.Hs n) := fun n => by
    simpa [kr, rearCurvature] using (D.model.configs n).periodic_kH
  have hk0 : ∀ n s, 0 ≤ kr n s := fun n s => by
    simpa [kr, rearCurvature] using (D.model.configs n).kH_nonneg s
  have hkap : ∀ n s, kr n s ≤ D.model.kstar := fun n s => by
    simpa [kr, rearCurvature] using (D.model.configs n).kH_le s
  have htotal : ∀ n, (∫ r in (0 : ℝ)..D.Hs n, kr n r) = Real.pi := fun n => by
    simpa [kr, rearCurvature] using (D.model.configs n).integral_kH_eq_pi
  have hkstar : 0 < D.model.kstar :=
    ConstructedConfiguredInductiveTubeBudget.configured_kstar_pos D.model
  have hchord := chord_arc_front_scaled
    (kappas := kr) (theta0 := fun _ => D.model.thetaBase)
    hH D.separation_lower hk hper htotal hk0 hkap hkstar
  obtain ⟨Q, hQ⟩ := TwoCapModelOrbit.exists_model_orbit
    (kappas := kr) (Hs := D.Hs) (theta0 := fun _ => D.model.thetaBase)
    (kmin := 0) (kap := D.model.kstar)
    (dlt := ConfiguredInductiveTubeBudget.chordCoeff D.model)
    hH D.separation_lower hk hper hk0 hkap htotal hchord
  let A : ∀ n, RearCarrier D n := fun n =>
    { data := Q n
      c := 2 * D.Hs 0
      dlt := ConfiguredInductiveTubeBudget.chordBase D.model
      c_pos := mul_pos (by norm_num) (hH 0)
      dlt_pos := by
        exact mul_pos (by
          dsimp [ConfiguredInductiveTubeBudget.chordCoeff]
          apply lt_min
          · norm_num
          · exact div_pos Real.pi_pos
              (mul_pos (mul_pos (by norm_num) hkstar) (hH 0)))
          (mul_pos (by norm_num) (hH 0))
      tube := by
        simpa [ConfiguredInductiveTubeBudget.chordBase] using (hQ n).1
      perim_eq := (hQ n).2.1
      curve_eq := by
        simpa [kr, rearCurvature, front] using (hQ n).2.2.1 }
  refine ⟨A, fun n => ?_⟩
  have hspeed : D.Hs 0 ≤ 2 * D.Hs 0 := by linarith [hH 0]
  have hchord0 : 0 ≤ ConfiguredInductiveTubeBudget.chordBase D.model := by
    exact (A n).dlt_pos.le
  exact (A n).tube.mono hspeed (by linarith)

end ConfiguredCanonicalRearCarrier
