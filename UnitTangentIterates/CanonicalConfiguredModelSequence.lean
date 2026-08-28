import UnitTangentIterates.CanonicalSeparationRecurrence
import UnitTangentIterates.UnconditionalAssemblyRemainder

/-! # Configured model sequence from retained paper witnesses -/

noncomputable section

namespace UnitTangentIterates.CanonicalConfiguredModelSequence

open ModelOrbitDefect PaperHairpinConfig

/-- A dependent family of paper configurations is already a configured model
sequence when each Config is chosen to be its witness's `toConfig`. -/
def ofPaperHairpinData
    {Hs eps : ℕ → ℝ} {y yu yu' : ℝ → ℝ}
    {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd : ℝ}
    (data : ∀ n, PaperHairpinData (alpha := alpha) (beta := beta)
      (a := a) (au := au) (C := C) (CU := CU) (CK := CK) (DU := DU)
      (DU2 := DU2) (D := D) (Km := Km) (Kd := Kd) (B := B)
      (theta0 := theta0) (kstar := kstar) (kd := kd) (eps0 := eps n)
      (H := Hs (n + 1)) (P := Hs n) y yu yu')
    (hmono : ∀ n, Hs 0 ≤ Hs n) :
    UnconditionalAssembly.ConfiguredModelSequence
      (fun n => modelCurvature (data n).toConfig.1.yu
        (data n).toConfig.1.yu' (Hs n)) Hs eps :=
  { alpha := alpha
    beta := beta
    a := a
    au := au
    C := C
    CU := CU
    CK := CK
    DU := DU
    DU2 := DU2
    D := D
    Km := Km
    Kd := Kd
    Bcell := B
    thetaBase := theta0
    kstar := kstar
    kd := kd
    configs := fun n => (data n).toConfig.1
    config_from_paper := fun n => ⟨y, yu, yu', data n, rfl⟩
    curvature_eq := fun n => rfl
    separation_mono := hmono }

/-- The strict rear-period recurrence plus a canonical paper-data constructor
at every recurrence edge produces the full configured sequence. -/
theorem exists_of_strict_recurrence
    {y yd yu yu' : ℝ → ℝ} {C alpha H0 : ℝ}
    {eps : ℕ → ℝ}
    {beta a au CU CK DU DU2 D Km Kd B theta0 kstar kd : ℝ}
    (halpha : 0 < alpha) (hH0 : 0 < H0)
    (hyc : Continuous y) (hyderiv : ∀ x, HasDerivAt y (yd x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hydb : ∀ x, |yd x| ≤ C * Real.exp (-alpha * |x|))
    (hlower : ∀ H, H0 ≤ H → H / 2 ≤
      ModelPeriodContinuity.rearPeriod y H)
    (hstrict : ∀ H, H0 ≤ H →
      ModelPeriodContinuity.rearPeriod y H < H)
    (hpaper : ∀ (n : ℕ) (Hnext Hcurr : ℝ),
      H0 ≤ Hcurr → Hcurr < Hnext →
      ModelPeriodContinuity.rearPeriod y Hnext = Hcurr →
      PaperHairpinData (alpha := alpha) (beta := beta) (a := a) (au := au)
        (C := C) (CU := CU) (CK := CK) (DU := DU) (DU2 := DU2) (D := D)
        (Km := Km) (Kd := Kd) (B := B) (theta0 := theta0)
        (kstar := kstar) (kd := kd) (eps0 := eps n) (H := Hnext)
        (P := Hcurr) y yu yu') :
    ∃ (Hs : ℕ → ℝ) (modelCurvatures : ℕ → ℝ → ℝ),
      Hs 0 = H0 ∧ (∀ n, Hs n < Hs (n + 1)) ∧
      (∀ n, ModelPeriodContinuity.rearPeriod y (Hs (n + 1)) = Hs n) ∧
      Nonempty (UnconditionalAssembly.ConfiguredModelSequence
        modelCurvatures Hs eps) := by
  obtain ⟨Hs, hHs0, hbase, hinc, hrec⟩ :=
    CanonicalSeparationRecurrence.exists_strict_sequence
      halpha hH0 hyc hyderiv hyb hydb hlower hstrict
  let data : ∀ n, PaperHairpinData (alpha := alpha) (beta := beta)
      (a := a) (au := au) (C := C) (CU := CU) (CK := CK) (DU := DU)
      (DU2 := DU2) (D := D) (Km := Km) (Kd := Kd) (B := B)
      (theta0 := theta0) (kstar := kstar) (kd := kd) (eps0 := eps n)
      (H := Hs (n + 1)) (P := Hs n) y yu yu' :=
    fun n => hpaper n (Hs (n + 1)) (Hs n) (hbase n) (hinc n) (hrec n)
  let kappas : ℕ → ℝ → ℝ := fun n =>
    modelCurvature (data n).toConfig.1.yu (data n).toConfig.1.yu' (Hs n)
  refine ⟨Hs, kappas, hHs0, hinc, hrec, ⟨?_⟩⟩
  exact ofPaperHairpinData data (fun n => by
    rw [hHs0]
    exact hbase n)

end UnitTangentIterates.CanonicalConfiguredModelSequence

