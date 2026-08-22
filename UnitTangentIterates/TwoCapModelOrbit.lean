import Mathlib
import UnitTangentIterates.MarkedSpaceChord
import UnitTangentIterates.TwoCapMarked

/-!
# The model curves as a sequence in one space of marked curves

The last section of *A Noncircular Oval with Convex Unit-Tangent Iterates*
shadows a **model pseudo-orbit**: the sequence of exact two-cap pairs at the
separations `H₀ < H₁ < ⋯` of the lemma *Large-separation threshold*.  The
shadowing scheme (`ShadowingScheme.lean`, `MarkedSchemeTheoremRange.lean`) needs
that sequence as a sequence of points of **one** complete metric space, namely
one tube `tube c kmin delta` of `MarkedSpace.lean`.

`TwoCapMarked.lean` puts a single two-cap pair into such a tube, but with a
chord-arc constant produced from embeddedness, hence depending on the curve.
Here the constant is prescribed instead, through a **uniform** quantitative
chord-arc bound for the family of model fronts, and the perimeters are bounded
below by that of the first model.

The uniformity asked of the family is the one that membership in a single tube
actually needs, that is uniformity of the chord-arc constant in the
**normalized** parameter: written in the arclength of the `n`-th model, the
bound is

`dlt·2H₀/2Hₙ · min(|x−y|, 2Hₙ−|x−y|) ≤ ‖Y x − Y y‖`,

with the constant of the model of separation `Hₙ` allowed to decay like
`1/Hₙ` — as it must for a family of long thin curves of bounded width, whose
two long sides stay at bounded distance while their arclength separation grows
with `Hₙ`.  The outcome is

* `exists_model_front_chord` : one model front, in the tube with the prescribed
  constant;
* `exists_model_orbit` and `exists_model_orbit_tube` : the whole family of model
  fronts as a sequence of points of the single tube
  `tube (2H₀) kmin (dlt·2H₀)`, the `n`-th having perimeter `2Hₙ` and the given
  front as its arclength parametrization.

What is *not* provided here is the defect estimate of the pseudo-orbit — that
`Qₙ` is close to the selected inverse of `Q_{n+1}` — which is the content of the
theorem *Curvature-measure matching* and is not assembled in this project; so
this is the model *sequence*, not yet the model *pseudo-orbit*.
-/

noncomputable section

open Set Function MarkedSpace

namespace TwoCapModelOrbit

open TwoCapPairsAssembly CurvatureInterpolation

/-- **A model front with a prescribed chord-arc constant.**  For a continuous
`H`-periodic front curvature pinched by `kmin ≤ K ≤ κ̂`, of total turning `π`
over one period, whose front satisfies the quantitative chord-arc bound with
constant `dlt`, the front is a member of the tube with chord-arc constant
`dlt·2H`, perimeter `2H` and curvature at most `κ̂`. -/
theorem exists_model_front_chord {kappa : ℝ → ℝ} {H kmin kap theta0 dlt : ℝ} (hH : 0 < H)
    (hk : Continuous kappa) (hper : Periodic kappa H)
    (hkmin : ∀ s, kmin ≤ kappa s) (hkap : ∀ s, kappa s ≤ kap)
    (htotal : (∫ r in (0:ℝ)..H, kappa r) = Real.pi)
    (hchord : ∀ x ∈ Icc (0:ℝ) (2 * H), ∀ y ∈ Icc (0:ℝ) (2 * H),
      dlt * min |x - y| (2 * H - |x - y|)
        ≤ ‖front kappa theta0 H x - front kappa theta0 H y‖) :
    ∃ q : Data, IsTubeMember (2 * H) kmin (dlt * (2 * H)) q ∧ perim q = 2 * H ∧
      ev q = front kappa theta0 H ∧
      ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kap * ‖q.2.1 u‖ ^ 3 := by
  have hper2 : Periodic kappa (2 * H) := by simpa using hper.nat_mul 2
  exact exists_tube_member_of_oval_chord (by linarith)
    (front_periodic hk hper htotal)
    (fun s => front_hasDerivAt (theta0 := theta0) (H := H) hk s)
    (fun s => hasDerivAt_tangentAngle (θ₀ := theta0) hk s) hk hper2 hkmin hkap hchord

/-- **The model curves are a sequence of points of one space of marked
curves.**  Given a family of admissible front curvatures — continuous,
`Hₙ`-periodic, pinched by `kmin ≤ Kₙ ≤ κ̂`, of total turning `π` over one
period — whose fronts satisfy a common quantitative chord-arc bound and whose
separations are at least `H₀`, the model fronts are members of the single tube
`tube (2H₀) kmin (dlt·2H₀)`, the `n`-th of perimeter `2Hₙ`. -/
theorem exists_model_orbit {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ} {kmin kap dlt : ℝ}
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖front (kappas n) (theta0 n) (Hs n) x - front (kappas n) (theta0 n) (Hs n) y‖) :
    ∃ Q : ℕ → Data, ∀ n,
      IsTubeMember (2 * Hs 0) kmin (dlt * (2 * Hs 0)) (Q n) ∧
      perim (Q n) = 2 * Hs n ∧ ev (Q n) = front (kappas n) (theta0 n) (Hs n) ∧
      ∀ u, ((starRingEnd ℂ) ((Q n).2.1 u) * (Q n).2.2 u).im ≤ kap * ‖(Q n).2.1 u‖ ^ 3 := by
  have hex : ∀ n : ℕ, ∃ q : Data,
      IsTubeMember (2 * Hs n) kmin (dlt * (2 * Hs 0)) q ∧ perim q = 2 * Hs n ∧
        ev q = front (kappas n) (theta0 n) (Hs n) ∧
        ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kap * ‖q.2.1 u‖ ^ 3 := by
    intro n
    have hne : (2 * Hs n) ≠ 0 := by have := hH n; positivity
    have h := exists_model_front_chord (dlt := dlt * (2 * Hs 0) / (2 * Hs n))
      (hH n) (hk n) (hper n) (hkmin n) (hkap n) (htotal n) (hchord n)
    rwa [div_mul_cancel₀ _ hne] at h
  choose Q hQ using hex
  refine ⟨Q, fun n => ⟨?_, (hQ n).2.1, (hQ n).2.2.1, (hQ n).2.2.2⟩⟩
  have hle : 2 * Hs 0 ≤ 2 * Hs n := by linarith [hmono n]
  exact (hQ n).1.mono hle le_rfl

/-- **The model curves as a sequence of points of the tube**, in the form the
shadowing scheme consumes: a sequence in the complete metric space
`tube (2H₀) kmin (dlt·2H₀)`, whose `n`-th member has perimeter `2Hₙ`. -/
theorem exists_model_orbit_tube {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ} {kmin kap dlt : ℝ}
    (hH : ∀ n, 0 < Hs n) (hmono : ∀ n, Hs 0 ≤ Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖front (kappas n) (theta0 n) (Hs n) x - front (kappas n) (theta0 n) (Hs n) y‖) :
    ∃ Q : ℕ → tube (2 * Hs 0) kmin (dlt * (2 * Hs 0)), ∀ n,
      perim ((Q n : Data)) = 2 * Hs n ∧
      ev ((Q n : Data)) = front (kappas n) (theta0 n) (Hs n) := by
  obtain ⟨Q, hQ⟩ := exists_model_orbit hH hmono hk hper hkmin hkap htotal hchord
  exact ⟨fun n => ⟨Q n, (hQ n).1⟩, fun n => ⟨(hQ n).2.1, (hQ n).2.2.1⟩⟩

/-- **The model curves of the recursion of the paper.**  When the separations
are the ones of the lemma *Large-separation threshold* — `P(H_{n+1}) = Hₙ` with
`P(x) ≤ x − Δ/2` past the threshold — the monotonicity of the separations is
automatic, and the perimeters of the model curves grow at least linearly. -/
theorem exists_model_orbit_recursion {kappas : ℕ → ℝ → ℝ} {Hs theta0 : ℕ → ℝ}
    {P : ℝ → ℝ} {Hstar Delta kmin kap dlt : ℝ}
    (hH : ∀ n, 0 < Hs n) (hDelta : 0 ≤ Delta)
    (hPle : ∀ x, Hstar ≤ x → P x ≤ x - Delta / 2)
    (hmem : ∀ n, Hstar ≤ Hs n) (hrec : ∀ n, P (Hs (n + 1)) = Hs n)
    (hk : ∀ n, Continuous (kappas n)) (hper : ∀ n, Periodic (kappas n) (Hs n))
    (hkmin : ∀ n s, kmin ≤ kappas n s) (hkap : ∀ n s, kappas n s ≤ kap)
    (htotal : ∀ n, (∫ r in (0:ℝ)..(Hs n), kappas n r) = Real.pi)
    (hchord : ∀ n, ∀ x ∈ Icc (0:ℝ) (2 * Hs n), ∀ y ∈ Icc (0:ℝ) (2 * Hs n),
      dlt * (2 * Hs 0) / (2 * Hs n) * min |x - y| (2 * Hs n - |x - y|)
        ≤ ‖front (kappas n) (theta0 n) (Hs n) x - front (kappas n) (theta0 n) (Hs n) y‖) :
    ∃ Q : ℕ → tube (2 * Hs 0) kmin (dlt * (2 * Hs 0)), ∀ n,
      perim ((Q n : Data)) = 2 * Hs n ∧
      ev ((Q n : Data)) = front (kappas n) (theta0 n) (Hs n) ∧
      2 * Hs 0 + Delta * n ≤ perim ((Q n : Data)) := by
  have hgrow : ∀ n : ℕ, Hs 0 + Delta / 2 * n ≤ Hs n :=
    MainThresholds.recursion_growth hPle hmem hrec
  have hmono : ∀ n, Hs 0 ≤ Hs n := by
    intro n
    have h := hgrow n
    have : 0 ≤ Delta / 2 * n := by positivity
    linarith
  obtain ⟨Q, hQ⟩ := exists_model_orbit_tube hH hmono hk hper hkmin hkap htotal hchord
  refine ⟨Q, fun n => ⟨(hQ n).1, (hQ n).2, ?_⟩⟩
  rw [(hQ n).1]
  have := hgrow n
  linarith

/-! ### The hypotheses are not vacuous -/

/-- **The constant model is admissible.**  Every separation equal to `2π` and
every curvature equal to `1/2` — the front being the circle of radius `2` — give
a family satisfying all the hypotheses above: the model curves are a sequence of
points of one tube. -/
theorem exists_model_orbit_instance :
    ∃ dlt : ℝ, 0 < dlt ∧
      ∃ Q : ℕ → tube (2 * (2 * Real.pi)) (1 / 2) (dlt * (2 * (2 * Real.pi))), ∀ n,
        perim ((Q n : Data)) = 2 * (2 * Real.pi) ∧
        ev ((Q n : Data)) = front TwoCapMarked.kcirc 0 (2 * Real.pi) := by
  obtain ⟨q, d, hdpos, hmem, hperim, hev, -⟩ := TwoCapMarked.marked_two_cap_front_circle
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcpos : (0:ℝ) < 2 * (2 * Real.pi) := by positivity
  refine ⟨d / (2 * (2 * Real.pi)), by positivity, ?_⟩
  have hchord : ∀ x ∈ Icc (0:ℝ) (2 * (2 * Real.pi)), ∀ y ∈ Icc (0:ℝ) (2 * (2 * Real.pi)),
      (d / (2 * (2 * Real.pi))) * min |x - y| (2 * (2 * Real.pi) - |x - y|)
        ≤ ‖front TwoCapMarked.kcirc 0 (2 * Real.pi) x
            - front TwoCapMarked.kcirc 0 (2 * Real.pi) y‖ := by
    intro x hx y hy
    have h := chord_arclength_of_tube hcpos hmem
    rw [hperim] at h
    have := h x hx y hy
    rwa [hev] at this
  obtain ⟨Q, hQ⟩ := exists_model_orbit_tube (kappas := fun _ => TwoCapMarked.kcirc)
    (Hs := fun _ => 2 * Real.pi) (theta0 := fun _ => 0) (kmin := 1 / 2) (kap := 1 / 2)
    (fun _ => by positivity) (fun _ => le_rfl)
    (fun _ => TwoCapMarked.continuous_kcirc) (fun _ => TwoCapMarked.kcirc_periodic)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ => TwoCapMarked.kcirc_total)
    (fun _ x hx y hy => by
      show d / (2 * (2 * Real.pi)) * (2 * (2 * Real.pi)) / (2 * (2 * Real.pi))
          * min |x - y| (2 * (2 * Real.pi) - |x - y|) ≤ _
      rw [div_mul_cancel₀ _ (by positivity : (2 * (2 * Real.pi)) ≠ 0)]
      exact hchord x hx y hy)
  exact ⟨Q, hQ⟩

end TwoCapModelOrbit
