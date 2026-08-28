import Mathlib
import UnitTangentIterates.TwoCapModelOrbit
import UnitTangentIterates.TwoCapRearEmbedded
import UnitTangentIterates.ModelChordArc
import UnitTangentIterates.SelectedInverseMap

/-!
# The model pseudo-orbit of the paper, with no embeddedness hypotheses

Section 7 of *A Noncircular Oval with Convex Unit-Tangent Iterates* shadows the
pseudo-orbit

  `Qₙ = F_{Hₙ}`,   `Aₙ = 𝔅 Q_{n+1} = R_{H_{n+1}}`,

the exact two-cap pairs at the separations of the lemma *Large-separation
threshold*.  Two pieces of that data are constructed elsewhere in this project:

* `TwoCapModelOrbit.exists_model_orbit_tube` puts the fronts `Qₙ` into one
  complete tube, given a uniform chord-arc bound;
* `TwoCapRearEmbedded.exists_model_selected_rear_sequence` produces the selected
  rears `Aₙ`.

Both used to carry embeddedness hypotheses — of the front, and of every rear
track reconstructed from a steering solution.  Neither is needed: the two-cap
fronts are built from a prescribed curvature of total turning `π` over a half
period, so their tangent angle turns by exactly `2π`, which is what
embeddedness needs.  This file records the resulting pseudo-orbit.

What is **not** proved here is the metric defect `dist (Qₙ, Aₙ) ≤ eₙ` with `eₙ`
summable; that is the curvature-measure matching estimate of Section 5 fed
through `ModelOrbitDefect`, and it remains the open input of the unconditional
main theorem.  The statement below is exactly the part of the pseudo-orbit that
is unconditional: the two sequences exist, live in the tube, and the
unit-tangent transform of `Aₙ` retraces `Q_{n+1}` as a set.
-/

noncomputable section

open Set Function MarkedSpace

namespace TwoCapPseudoOrbit

open TwoCapPairsAssembly

/-- **The model pseudo-orbit of Section 7, unconditionally.**  For prescribed
curvatures `κₙ` pinched by `0 < kmin ≤ κₙ ≤ κ̂ < 1`, `Hₙ`-periodic, of total
turning `π` over one period, and satisfying the uniform chord-arc bound of
`TwoCapModelOrbit`, the fronts form a sequence in one tube and the selected
rears exist, with `𝒯 Aₙ` retracing `Q_{n+1}`. -/
theorem exists_model_pseudo_orbit {kappas : ℕ → ℝ → ℝ} {Hs theta0s : ℕ → ℝ}
    {kmin kap dlt : ℝ}
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖front (kappas n) (theta0s n) (Hs n) x
            - front (kappas n) (theta0s n) (Hs n) y‖) :
    ∃ (Q : ℕ → tube (2 * Hs 0) kmin (dlt * (2 * Hs 0))) (A : ℕ → Data), ∀ n,
      perim ((Q n : Data)) = 2 * Hs n ∧
      ev ((Q n : Data)) = front (kappas n) (theta0s n) (Hs n) ∧
      (∃ dR > 0, ∃ LR > 0, LR ≤ 2 * Hs (n + 1) ∧ perim (A n) = LR ∧
        IsTubeMember LR (kmin / Real.sqrt (1 - kmin ^ 2)) dR (A n)) ∧
      MainTheoremConditional.IsOval (ev (A n)) ∧
      range (UnitTangent.unitTangentMap (ev (A n)))
        = range (ev ((Q (n + 1) : Data))) := by
  obtain ⟨Q, hQ⟩ := TwoCapModelOrbit.exists_model_orbit_tube hH hmono hk hper
    hkmin hkap htotal hchord
  obtain ⟨A₀, hA₀⟩ :=
    TwoCapRearEmbedded.exists_model_selected_rear_sequence (theta0s := theta0s)
      hH hk hper hkminpos hkap1 hkmin hkap htotal
  refine ⟨Q, fun n => A₀ (n + 1), fun n => ⟨(hQ n).1, (hQ n).2, (hA₀ (n + 1)).1,
    (hA₀ (n + 1)).2.1, ?_⟩⟩
  rw [(hA₀ (n + 1)).2.2, (hQ (n + 1)).2]

/-- **The model pseudo-orbit from the prescribed curvature data alone.**  The
uniform chord-arc bound of `ModelChordArc.model_chord_arc` discharges the last
remaining geometric hypothesis of `exists_model_pseudo_orbit`, so the whole
Section 7 pseudo-orbit — fronts in one complete tube, selected rears, and the
range identity `𝒯 Aₙ = Q_{n+1}` — follows from exactly the data of Section 4:
continuous `Hₙ`-periodic curvatures pinched by `0 < kmin ≤ κₙ ≤ κ̂ < 1` with
total turning `π` over one period, and separations bounded below by `H₀`.

What is still missing for the unconditional main theorem is only the *metric*
defect `dist (Qₙ, Aₙ) ≤ eₙ` with `eₙ` summable. -/
theorem exists_model_pseudo_orbit_of_prescribed_curvature
    {kappas : ℕ → ℝ → ℝ} {Hs theta0s : ℕ → ℝ} {kmin kap : ℝ}
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi) :
    ∃ (Q : ℕ → tube (2 * Hs 0) kmin
        (ModelChordArc.modelChordConst kmin kap (Hs 0) * (2 * Hs 0)))
      (A : ℕ → Data), ∀ n,
      perim ((Q n : Data)) = 2 * Hs n ∧
      ev ((Q n : Data)) = front (kappas n) (theta0s n) (Hs n) ∧
      (∃ dR > 0, ∃ LR > 0, LR ≤ 2 * Hs (n + 1) ∧ perim (A n) = LR ∧
        IsTubeMember LR (kmin / Real.sqrt (1 - kmin ^ 2)) dR (A n)) ∧
      MainTheoremConditional.IsOval (ev (A n)) ∧
      range (UnitTangent.unitTangentMap (ev (A n)))
        = range (ev ((Q (n + 1) : Data))) :=
  exists_model_pseudo_orbit hH hmono hk hper hkminpos hkap1 hkmin hkap htotal
    (ModelChordArc.model_chord_arc (theta0 := theta0s) hH hmono hkminpos hk hper
      hkmin hkap htotal)

/-- **The pseudo-orbit with the canonical selected inverse.**  The paper writes
`Aₙ = 𝔅 Q_{n+1}` for a *map* `𝔅`, not a choice of rears.  This states the
pseudo-orbit in exactly that form, with `𝔅 = SelectedInverseMap.selInv κ̂`, the
canonical single-valued selected inverse: for each `n`, `selInv κ̂ Q_{n+1}` is a
tube member of curvature at least `kmin/√(1-kmin²)`, an oval, and its
unit-tangent transform retraces `Q_{n+1}` as a set. -/
theorem exists_model_pseudo_orbit_selInv {kappas : ℕ → ℝ → ℝ}
    {Hs theta0s : ℕ → ℝ} {kmin kap dlt : ℝ}
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkminpos : 0 < kmin) (hkap1 : kap < 1)
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖front (kappas n) (theta0s n) (Hs n) x
            - front (kappas n) (theta0s n) (Hs n) y‖) :
    ∃ Q : ℕ → Data, ∀ n,
      IsTubeMember (2 * Hs 0) kmin (dlt * (2 * Hs 0)) (Q n) ∧
      perim (Q n) = 2 * Hs n ∧
      ev (Q n) = front (kappas n) (theta0s n) (Hs n) ∧
      (∃ dR > 0, IsTubeMember (perim (SelectedInverseMap.selInv kap (Q (n + 1))))
          (kmin / Real.sqrt (1 - kmin ^ 2)) dR
          (SelectedInverseMap.selInv kap (Q (n + 1)))) ∧
      MainTheoremConditional.IsOval
        (ev (SelectedInverseMap.selInv kap (Q (n + 1)))) ∧
      range (UnitTangent.unitTangentMap
          (ev (SelectedInverseMap.selInv kap (Q (n + 1)))))
        = range (ev (Q (n + 1))) := by
  obtain ⟨Q, hQ⟩ := TwoCapModelOrbit.exists_model_orbit hH hmono hk hper hkmin
    hkap htotal hchord
  have hkap0 : (0 : ℝ) ≤ kap :=
    le_trans (le_trans hkminpos.le (hkmin 0 0)) (hkap 0 0)
  have hc : (0 : ℝ) < 2 * Hs 0 := by have := hH 0; linarith
  refine ⟨Q, fun n => ⟨(hQ n).1, (hQ n).2.1, (hQ n).2.2.1, ?_⟩⟩
  obtain ⟨dR, hdR, hmemR, hovalR, -, hrangeR⟩ :=
    TwoCapRearEmbedded.selInv_spec_two_cap (theta0 := theta0s (n + 1)) hc
      hkminpos hkap0 hkap1 (hQ (n + 1)).1 (hQ (n + 1)).2.2.2 (hk (n + 1))
      (hper (n + 1)) (htotal (n + 1)) (hQ (n + 1)).2.2.1 (hQ (n + 1)).2.1
  exact ⟨⟨dR, hdR, hmemR⟩, hovalR, by rw [hrangeR]⟩

/-- **The pseudo-orbit statement is not vacuous.**  The constant model — every
separation `2π`, every curvature `1/2`, the front being the circle of radius
`2` — satisfies every hypothesis, so its fronts and selected rears form the
pseudo-orbit above.  (This model is of course circular; it witnesses that the
hypotheses are consistent, not that the main theorem is proved.) -/
theorem exists_model_pseudo_orbit_instance :
    ∃ dlt : ℝ, 0 < dlt ∧
      ∃ (Q : ℕ → tube (2 * (2 * Real.pi)) (1 / 2)
          (dlt * (2 * (2 * Real.pi)))) (A : ℕ → Data), ∀ n,
        perim ((Q n : Data)) = 2 * (2 * Real.pi) ∧
        ev ((Q n : Data)) = front TwoCapMarked.kcirc 0 (2 * Real.pi) ∧
        MainTheoremConditional.IsOval (ev (A n)) ∧
        range (UnitTangent.unitTangentMap (ev (A n)))
          = range (ev ((Q (n + 1) : Data))) := by
  obtain ⟨q, d, hdpos, hmem, hperim, hev, -⟩ :=
    TwoCapMarked.marked_two_cap_front_circle
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcpos : (0 : ℝ) < 2 * (2 * Real.pi) := by positivity
  refine ⟨d / (2 * (2 * Real.pi)), by positivity, ?_⟩
  have hchord : ∀ x ∈ Icc (0 : ℝ) (2 * (2 * Real.pi)),
      ∀ y ∈ Icc (0 : ℝ) (2 * (2 * Real.pi)),
      (d / (2 * (2 * Real.pi))) * min |x - y| (2 * (2 * Real.pi) - |x - y|)
        ≤ ‖front TwoCapMarked.kcirc 0 (2 * Real.pi) x
            - front TwoCapMarked.kcirc 0 (2 * Real.pi) y‖ := by
    intro x hx y hy
    have h := chord_arclength_of_tube hcpos hmem
    rw [hperim] at h
    have hres := h x hx y hy
    rwa [hev] at hres
  obtain ⟨Q, A, hQA⟩ := exists_model_pseudo_orbit
    (kappas := fun _ => TwoCapMarked.kcirc) (Hs := fun _ => 2 * Real.pi)
    (theta0s := fun _ => 0) (kmin := 1 / 2) (kap := 1 / 2)
    (fun _ => by positivity) (fun _ => le_rfl)
    (fun _ => TwoCapMarked.continuous_kcirc)
    (fun _ => TwoCapMarked.kcirc_periodic) (by norm_num) (by norm_num)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ => TwoCapMarked.kcirc_total)
    (fun _ x hx y hy => by
      show d / (2 * (2 * Real.pi)) * (2 * (2 * Real.pi)) / (2 * (2 * Real.pi))
          * min |x - y| (2 * (2 * Real.pi) - |x - y|) ≤ _
      rw [div_mul_cancel₀ _ (by positivity : (2 * (2 * Real.pi)) ≠ 0)]
      exact hchord x hx y hy)
  exact ⟨Q, A, fun n => ⟨(hQA n).1, (hQA n).2.1, (hQA n).2.2.2.1,
    (hQA n).2.2.2.2⟩⟩

end TwoCapPseudoOrbit
