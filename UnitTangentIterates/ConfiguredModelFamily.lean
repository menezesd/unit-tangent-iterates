import UnitTangentIterates.UnconditionalAssemblyRemainder
import UnitTangentIterates.OrbitBudgetSharp

/-!
# Configured model sequences with level-dependent constants
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Filter Topology Metric CurvatureStabilityL1

namespace UnconditionalAssembly

open MarkedSpace ModelOrbitDefect PaperHairpinConfig

/-- **A configured model sequence whose constants vary with the level.**

`ConfiguredModelSequence` fixes one `alpha, beta, C, kstar, …` for the whole
sequence.  Sections 86-88 of the session log show that will not do: the level-`n`
model must have curvature ceiling below `1/√(n+1)`, so the ceiling — which
`ConfiguredModelSequence.curvature_upper` reads off the single constant `kstar` —
has to decay with the level.

This structure is the same data with every constant turned into a family.  It is
a strict generalization: `ofSequence` embeds the old structure as the constant
families, and each of the five basic lemmas carries over verbatim, because none
of them touches the constants except `curvature_upper`, which now yields the
level-dependent bound it must. -/
structure ConfiguredModelFamily
    (kappas : ℕ → ℝ → ℝ) (Hs : ℕ → ℝ) (eps : ℕ → ℝ) where
  alpha : ℕ → ℝ
  beta : ℕ → ℝ
  a : ℕ → ℝ
  au : ℕ → ℝ
  C : ℕ → ℝ
  CU : ℕ → ℝ
  CK : ℕ → ℝ
  DU : ℕ → ℝ
  DU2 : ℕ → ℝ
  D : ℕ → ℝ
  Km : ℕ → ℝ
  Kd : ℕ → ℝ
  Bcell : ℕ → ℝ
  thetaBase : ℕ → ℝ
  kstar : ℕ → ℝ
  kd : ℕ → ℝ
  configs : ∀ n, Config (alpha n) (beta n) (a n) (au n) (C n) (CU n) (CK n)
    (DU n) (DU2 n) (D n) (Km n) (Kd n) (Bcell n) (thetaBase n) (kstar n) (kd n)
    (eps n) (Hs (n + 1)) (Hs n)
  config_from_paper : ∀ n, ∃ y yu yu' : ℝ → ℝ,
    ∃ d : PaperHairpinData (alpha := alpha n) (beta := beta n) (a := a n)
      (au := au n) (C := C n) (CU := CU n) (CK := CK n) (DU := DU n)
      (DU2 := DU2 n) (D := D n) (Km := Km n) (Kd := Kd n) (B := Bcell n)
      (theta0 := thetaBase n) (kstar := kstar n) (kd := kd n) (eps0 := eps n)
      (H := Hs (n + 1)) (P := Hs n) y yu yu', d.toConfig.1 = configs n
  curvature_eq : ∀ n,
    kappas n = modelCurvature (configs n).yu (configs n).yu' (Hs n)
  separation_mono : ∀ n, Hs 0 ≤ Hs n

namespace ConfiguredModelFamily

variable {kappas : ℕ → ℝ → ℝ} {Hs : ℕ → ℝ} {eps : ℕ → ℝ}

/-- Every single-constant sequence is a family with constant families. -/
def ofSequence (m : ConfiguredModelSequence kappas Hs eps) :
    ConfiguredModelFamily kappas Hs eps where
  alpha := fun _ => m.alpha
  beta := fun _ => m.beta
  a := fun _ => m.a
  au := fun _ => m.au
  C := fun _ => m.C
  CU := fun _ => m.CU
  CK := fun _ => m.CK
  DU := fun _ => m.DU
  DU2 := fun _ => m.DU2
  D := fun _ => m.D
  Km := fun _ => m.Km
  Kd := fun _ => m.Kd
  Bcell := fun _ => m.Bcell
  thetaBase := fun _ => m.thetaBase
  kstar := fun _ => m.kstar
  kd := fun _ => m.kd
  configs := m.configs
  config_from_paper := m.config_from_paper
  curvature_eq := m.curvature_eq
  separation_mono := m.separation_mono

theorem separation_pos (m : ConfiguredModelFamily kappas Hs eps) (n : ℕ) :
    0 < Hs n := (m.configs n).Ppos

theorem curvature_continuous (m : ConfiguredModelFamily kappas Hs eps) (n : ℕ) :
    Continuous (kappas n) := by
  rw [m.curvature_eq n]; exact (m.configs n).continuous_KP

theorem curvature_periodic (m : ConfiguredModelFamily kappas Hs eps) (n : ℕ) :
    Periodic (kappas n) (Hs n) := by
  rw [m.curvature_eq n]; exact (m.configs n).periodic_KP

/-- **The levelwise curvature ceiling.**  This is the lemma the refactor exists
for: the bound is `kstar n`, not a single `kstar`. -/
theorem curvature_upper (m : ConfiguredModelFamily kappas Hs eps) (n : ℕ) (s : ℝ) :
    kappas n s ≤ m.kstar n := by
  rw [m.curvature_eq n]; exact (m.configs n).KP_le s

theorem total_turning (m : ConfiguredModelFamily kappas Hs eps) (n : ℕ) :
    (∫ r in (0 : ℝ)..(Hs n), kappas n r) = Real.pi := by
  rw [m.curvature_eq n]; exact (m.configs n).integral_KP_eq_pi

/-- **The backward-orbit threshold, met levelwise.**  If the family's constants
`kstar n` lie below `1/√(n+1)`, so does every value of the level-`n` model
curvature — which is what `OrbitCeiling.ceiling_lt_of_steps` requires of a model
that must admit `n` backward steps.  A single-constant sequence cannot satisfy
the hypothesis for all `n`, since `1/√(n+1) → 0`. -/
theorem curvature_lt_threshold (m : ConfiguredModelFamily kappas Hs eps)
    (h : ∀ n, m.kstar n < 1 / Real.sqrt ((n : ℝ) + 1)) (n : ℕ) (s : ℝ) :
    kappas n s < 1 / Real.sqrt ((n : ℝ) + 1) :=
  lt_of_le_of_lt (m.curvature_upper n s) (h n)


/-- **Diagonal assembly.**  Given, for each level `n`, a single-constant
configured sequence over the *same* `Hs` and `eps`, the diagonal — reading
level `n`'s data off the `n`-th sequence — is a `ConfiguredModelFamily`.

This isolates exactly what the level-dependent construction still owes.  The
constants of the `S n` may be completely unrelated to one another; nothing
about them is assumed.  What must be shared is only the level sequence `Hs` and
the defect parameters `eps`.  So the remaining obligation is not "make sixteen
constants into families" — that is done — but "produce the per-level
configurations over one common level sequence". -/
def ofDiagonal (S : ℕ → ConfiguredModelSequence kappas Hs eps) :
    ConfiguredModelFamily kappas Hs eps where
  alpha := fun n => (S n).alpha
  beta := fun n => (S n).beta
  a := fun n => (S n).a
  au := fun n => (S n).au
  C := fun n => (S n).C
  CU := fun n => (S n).CU
  CK := fun n => (S n).CK
  DU := fun n => (S n).DU
  DU2 := fun n => (S n).DU2
  D := fun n => (S n).D
  Km := fun n => (S n).Km
  Kd := fun n => (S n).Kd
  Bcell := fun n => (S n).Bcell
  thetaBase := fun n => (S n).thetaBase
  kstar := fun n => (S n).kstar
  kd := fun n => (S n).kd
  configs := fun n => (S n).configs n
  config_from_paper := fun n => (S n).config_from_paper n
  curvature_eq := fun n => (S n).curvature_eq n
  separation_mono := fun n => (S n).separation_mono n

@[simp] theorem ofDiagonal_kstar (S : ℕ → ConfiguredModelSequence kappas Hs eps)
    (n : ℕ) : (ofDiagonal S).kstar n = (S n).kstar := rfl

/-- The diagonal meets the backward-orbit threshold as soon as the `n`-th
sequence's own ceiling constant does. -/
theorem ofDiagonal_lt_threshold (S : ℕ → ConfiguredModelSequence kappas Hs eps)
    (h : ∀ n, (S n).kstar < 1 / Real.sqrt ((n : ℝ) + 1)) (n : ℕ) (s : ℝ) :
    kappas n s < 1 / Real.sqrt ((n : ℝ) + 1) :=
  (ofDiagonal S).curvature_lt_threshold (by simpa using h) n s

end ConfiguredModelFamily

end UnconditionalAssembly
