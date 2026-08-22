import Mathlib
import UnitTangentIterates.SelectedInverseRearOwnShiftSteeringSpeed
import UnitTangentIterates.PathDataTaylorBounds

/-!
# The shift bound with the quantitative time bounds of the front data produced

`SelectedInverseRearOwnShiftSteeringSpeed.exists_steering_pathDistShift_selInv_le_speed`
carries, besides the regularity of the front data of the path, six constants
describing how that data moves in the time: sup bounds `Md`, `MP` for the first
time derivatives of the normalized curvature `Kn` and of the arclength period
`P`, Lipschitz constants `Klip`, `Plip` for the two, and first-order Taylor
constants `CK`, `CP`.  None of them appears in the conclusion.

None of them has to be assumed either.  A normal path is at rest outside its
time window (`PathDataTaylorBounds.path_X_rest` and its consequences), so the
front data is constant in the time there; being also periodic in the space
variable, it is bounded on the whole plane together with its time derivatives,
and the mean value inequality then produces the Lipschitz and Taylor bounds
globally.  The time derivatives themselves are not data of the statement
either: they are the canonical partial derivatives `partialT Kn` and `deriv P`.

Main result: `exists_steering_pathDistShift_selInv_le_regular`, the same bound
with `Kdn`, `Pd` and the six constants all removed, at the cost of one extra
derivative of the normalized curvature (`Kn` jointly `C⁴` instead of `C³`,
which is what the previous statement already asked of `P`, of the front and of
its tangent angle).
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace SelectedInverseShiftTaylor

open UniformFrameBounds GaugePathDistVariable RearOwnHigherRegularity
  FrontFromPath SelectedInverseRearOwn PathDataTaylorBounds

variable {V A : ℝ → ℝ → ℂ} {Kn : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {P0 P1 kh : ℝ}

/-- **The shift bound for the marked selected inverses of the two ends of a
normal path, with the quantitative time bounds of the front data produced.**

Same statement as
`SelectedInverseRearOwnShiftSteeringSpeed.exists_steering_pathDistShift_selInv_le_speed`,
with the time derivative of the normalized curvature and of the arclength
period taken to be the canonical ones, and with their sup, Lipschitz and Taylor
constants produced from the regularity of the front data together with the fact
that a normal path stands still outside its time window. -/
theorem exists_steering_pathDistShift_selInv_le_regular {p q : Data} (Γ : NormalPath p q)
    {c kmin dlt cq kminq dltq M : ℝ}
    (hc : 0 < c) (hkmin : 0 < kmin) (hp : IsTubeMember c kmin dlt p)
    (hub : ∀ u, ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤ kh * ‖p.2.1 u‖ ^ 3)
    (hinjR : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev p) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim p) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev p) Θ' dl) (Ico 0 (perim p)))
    (hcq : 0 < cq) (hkminq : 0 < kminq) (hq : IsTubeMember cq kminq dltq q)
    (hubq : ∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im ≤ kh * ‖q.2.1 u‖ ^ 3)
    (hinjRq : ∀ Θ' K' dl : ℝ → ℝ,
      (∀ s, HasDerivAt (ev q) (Complex.exp (Complex.I * (Θ' s : ℂ))) s) →
      (∀ s, HasDerivAt Θ' (K' s) s) →
      Function.Periodic dl (perim q) →
      (∀ s, dl s ∈ Icc 0 (Real.arcsin kh)) →
      (∀ s, HasDerivAt dl (K' s - Real.sin (dl s)) s) →
      InjOn (rearTrack (ev q) Θ' dl) (Ico 0 (perim q)))
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hKeq : ∀ t s, curvOfPath V A P t s = Kn t (s / P t))
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKn0 : ∀ t σ, 0 ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh)
    (hPC4 : ContDiff ℝ (4 : ℕ) P)
    (hKnC4 : ContDiff ℝ (4 : ℕ) (uncurry Kn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (angleOfPath V A P)))
    (hm : ∀ t, Γ.m t ≤ M) :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = perim (SelectedInverseMap.selInv kh p) * u) ∧
        ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
        ∀ (q' : Data) (dPhi : ℝ → ℝ) {cq' kq' dq' : ℝ},
          0 < cq' → 0 < kq' → 0 < dq' → IsTubeMember cq' kq' dq' q' →
          (∀ u, HasDerivAt (Phi Γ.T) (dPhi u) u) →
          (∀ u, q'.1 u
            = (SelectedInverseMap.selInv kh q).1
                (Phi Γ.T u / perim (SelectedInverseMap.selInv kh q))) →
          MarkedShift.pathDistShift (SelectedInverseMap.selInv kh p)
              (SelectedInverseMap.selInv kh q) ≤ gaugeJacobiConst P0 P1 kh
                (M / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                ((M / Real.sqrt (1 - kh ^ 2) + M / Real.sqrt (1 - kh ^ 2))
                    * (kh / Real.sqrt (1 - kh ^ 2))
                  + M / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
              (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hT : (0:ℝ) ≤ Γ.T := Γ.T_pos.le
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  -- the front data of a normal path is at rest outside its time window
  have hPrest : ∀ t, P t = P (clampT 0 Γ.T t) := path_P_rest Γ hV hspeed
  have hKnrest : ∀ t σ, Kn t σ = Kn (clampT 0 Γ.T t) σ :=
    path_Kn_rest Γ hV hA hspeed hPpos hKeq
  -- the two time derivatives of the normalized curvature
  have hKnC1 : ContDiff ℝ 1 (uncurry Kn) := hKnC4.of_le (by norm_num)
  have hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn) := hKnC4.of_le (by norm_num)
  have hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry (partialT Kn)) :=
    contDiff_partialT (n := 3) (by exact_mod_cast hKnC4)
  have hKdnC1 : ContDiff ℝ 1 (uncurry (partialT Kn)) := hKdnC3.of_le (by norm_num)
  have hKddnC2 : ContDiff ℝ (2 : ℕ) (uncurry (partialT (partialT Kn))) :=
    contDiff_partialT (n := 2) (by exact_mod_cast hKdnC3)
  have hKdn_der : ∀ t σ, HasDerivAt (fun a => Kn a σ) (partialT Kn t σ) t :=
    fun t σ => hasDerivAt_partialT hKnC1 t σ
  have hKddn_der : ∀ t σ,
      HasDerivAt (fun a => partialT Kn a σ) (partialT (partialT Kn) t σ) t :=
    fun t σ => hasDerivAt_partialT hKdnC1 t σ
  have hKdnper : ∀ t, Function.Periodic (partialT Kn t) 1 := periodic_partialT hKnC1 hKnper
  have hKddnper : ∀ t, Function.Periodic (partialT (partialT Kn) t) 1 :=
    periodic_partialT hKdnC1 hKdnper
  have hKdnvan := partialT_vanishing_of_rest hT hKnC1 hKnrest
  have hKddnvan := partialT_vanishing_of_vanishing hKdnC1 hKdnvan
  obtain ⟨Md, CK, -, hCK0, hKdnbd, hKnlip, hKntaylor⟩ :=
    exists_lip_taylor_of_vanishing_periodic (T := Γ.T) hKdn_der hKddn_der
      hKdnC1.continuous hKddnC2.continuous hKdnper hKddnper hKdnvan hKddnvan
  -- the two time derivatives of the arclength period
  have hPC4' : ContDiff ℝ ((3 : ℕ) + 1) P := by exact_mod_cast hPC4
  have hPdC3 : ContDiff ℝ (3 : ℕ) (deriv P) := (contDiff_succ_iff_deriv.mp hPC4').2.2
  have hPdC3' : ContDiff ℝ ((2 : ℕ) + 1) (deriv P) := by exact_mod_cast hPdC3
  have hPddC2 : ContDiff ℝ (2 : ℕ) (deriv (deriv P)) := (contDiff_succ_iff_deriv.mp hPdC3').2.2
  have hP_der : ∀ t, HasDerivAt P (deriv P t) t := fun t =>
    (hPC4.differentiable (by norm_num) t).hasDerivAt
  have hPd_der : ∀ t, HasDerivAt (deriv P) (deriv (deriv P) t) t := fun t =>
    (hPdC3.differentiable (by norm_num) t).hasDerivAt
  have hPdvan := deriv_vanishing_of_rest hT hPrest
  have hPddvan := deriv_vanishing_of_vanishing hPdvan
  obtain ⟨MP, CP, -, hCP0, hPdbd, hPlip, hPtaylor⟩ :=
    exists_lip_taylor_of_vanishing (T := Γ.T) hT hP_der hPd_der hPdC3.continuous
      hPddC2.continuous hPdvan hPddvan
  exact SelectedInverseRearOwnShiftSteeringSpeed.exists_steering_pathDistShift_selInv_le_speed
    Γ (M := M) hc hkmin hp hub hinjR hcq hkminq hq hubq hinjRq hP0 hkh0 hkh1 hPl hPu hV hA
    hAcont hspeed hXper hVper hAper hturn hnu hKeq hKnper hKdnper hKn0 hKnk hKdnbd hPdbd
    hKnlip hPlip hKntaylor hPtaylor hCK0 hCP0 hPC4 hPdC3 hKnC3 hKdnC3 hFc4 hΘc4 hm

end SelectedInverseShiftTaylor
