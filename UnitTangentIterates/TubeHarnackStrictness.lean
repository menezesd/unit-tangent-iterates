import UnitTangentIterates.TubeArclengthAngle
import UnitTangentIterates.LimitStrictnessFromApproximants

/-!
# Discharging the strictness hypothesis from tube membership and Harnack
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Filter Topology Complex MarkedSpace CurvatureFromMarkedDistance

namespace UnconditionalAssembly

/-- **The arclength curvature of a marked datum**: the normalized-parameter
curvature read at the rescaled time. -/
def arcCurv (p : Data) (s : ℝ) : ℝ := dataCurv p (s / perim p)

theorem periodic_arcCurv {c kmin dlt : ℝ} {p : Data}
    (hp : IsTubeMember c kmin dlt p) (hL : perim p ≠ 0) :
    Periodic (arcCurv p) (perim p) := by
  intro s
  have h : (s + perim p) / perim p = s / perim p + 1 := by field_simp
  simp only [arcCurv, h, periodic_dataCurv hp (s / perim p)]

theorem arcCurv_nonneg {c dlt : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c 0 dlt p) (s : ℝ) : 0 ≤ arcCurv p s := by
  have hb := hp.curv_lb (s / perim p)
  rw [zero_mul] at hb
  have hpos : 0 < ‖p.2.1 (s / perim p)‖ ^ 3 :=
    pow_pos (lt_of_lt_of_le hc (hp.speed_lb _)) 3
  exact div_nonneg hb (le_of_lt hpos)

/-- **The strictness datum of a tube member**, from the tangent-angle lift, the
curvature floor `0` of the tube, and the paper's bounded-shift Harnack
inequality.  Every field is `C2`: no derivative of the curvature appears. -/
def limitStrictnessDataH_of_tube {c dlt : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c 0 dlt p)
    (hharn : ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (arcCurv p a / Real.sqrt (1 + arcCurv p a ^ 2))
        ≤ arcCurv p b / Real.sqrt (1 + arcCurv p b ^ 2))
    (hne : ∃ s, arcCurv p s ≠ 0) : LimitStrictnessDataH p where
  theta := (exists_arclength_angle hc hp).choose
  k := arcCurv p
  curve_deriv := (exists_arclength_angle hc hp).choose_spec.1
  angle_deriv := (exists_arclength_angle hc hp).choose_spec.2
  curvature_periodic := periodic_arcCurv hp (ne_of_gt (perim_pos hc hp))
  curvature_nonnegative := arcCurv_nonneg hc hp
  curvature_harnack := hharn
  curvature_nonzero := hne

/-- Reading the velocity at the rescaled time is continuous at every datum of
positive perimeter. -/
theorem continuousAt_vel_scaled {X : Data} {s : ℝ} (hX : perim X ≠ 0) :
    ContinuousAt (fun p : Data => p.2.1 (s / perim p)) X := by
  have hperim : Continuous (perim : Data → ℝ) := by unfold perim; fun_prop
  have hpair : ContinuousAt (fun p : Data => (p.2.1, s / perim p)) X :=
    (continuous_fst.comp continuous_snd).continuousAt.prodMk
      (continuousAt_const.div hperim.continuousAt hX)
  exact continuous_eval.continuousAt.comp hpair

theorem continuousAt_acc_scaled {X : Data} {s : ℝ} (hX : perim X ≠ 0) :
    ContinuousAt (fun p : Data => p.2.2 (s / perim p)) X := by
  have hperim : Continuous (perim : Data → ℝ) := by unfold perim; fun_prop
  have hpair : ContinuousAt (fun p : Data => (p.2.2, s / perim p)) X :=
    (continuous_snd.comp continuous_snd).continuousAt.prodMk
      (continuousAt_const.div hperim.continuousAt hX)
  exact continuous_eval.continuousAt.comp hpair

/-- **The arclength curvature is continuous in the marked datum.**  Both the
datum and the time rescaling vary, so this is a joint statement; it holds at
every datum whose speed at the relevant parameter is nonzero. -/
theorem continuousAt_arcCurv {X : Data} {s : ℝ} (hL : perim X ≠ 0)
    (hV : ‖X.2.1 (s / perim X)‖ ≠ 0) : ContinuousAt (fun p : Data => arcCurv p s) X := by
  have hv := continuousAt_vel_scaled (X := X) (s := s) hL
  have ha := continuousAt_acc_scaled (X := X) (s := s) hL
  have hnum : ContinuousAt
      (fun p : Data => ((starRingEnd ℂ) (p.2.1 (s / perim p)) * p.2.2 (s / perim p)).im) X :=
    Complex.continuous_im.continuousAt.comp
      ((Complex.continuous_conj.continuousAt.comp hv).mul ha)
  have hden : ContinuousAt (fun p : Data => ‖p.2.1 (s / perim p)‖ ^ 3) X := hv.norm.pow 3
  exact hnum.div hden (by simpa using pow_ne_zero 3 hV)

theorem tendsto_arcCurv {P : ℕ → Data} {X : Data} {c kmin dlt : ℝ} (hc : 0 < c)
    (hX : IsTubeMember c kmin dlt X) (hP : Tendsto P atTop (𝓝 X)) (s : ℝ) :
    Tendsto (fun k => arcCurv (P k) s) atTop (𝓝 (arcCurv X s)) :=
  ((continuousAt_arcCurv (ne_of_gt (perim_pos hc hX))
    (ne_of_gt (lt_of_lt_of_le hc (hX.speed_lb _)))).tendsto).comp hP

/-- **The strictness datum of a shadowing limit.**  The Harnack inequality is
required only of the approximating data; being a closed condition on curvature
values, it passes to the limit.  No arclength correspondence between the
approximants and the limit, and no third derivative, is used. -/
def limitStrictnessDataH_of_limit {c dlt : ℝ} (hc : 0 < c) {P : ℕ → Data} {X : Data}
    (hX : IsTubeMember c 0 dlt X) (hP : Tendsto P atTop (𝓝 X))
    (hharn : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (arcCurv (P n) a / Real.sqrt (1 + arcCurv (P n) a ^ 2))
        ≤ arcCurv (P n) b / Real.sqrt (1 + arcCurv (P n) b ^ 2))
    (hne : ∃ s, arcCurv X s ≠ 0) : LimitStrictnessDataH X :=
  limitStrictnessDataH_of_tube hc hX
    (UnitTangent.harnack_of_tendsto (fun s => tendsto_arcCurv hc hX hP s) hharn) hne

/-- **A closed curve has somewhere-nonzero curvature.**  If the arclength
curvature vanished identically the tangent angle would be constant, the
arclength parametrization would be an affine line of unit speed, and no such
map is periodic with positive period. -/
theorem arcCurv_nonzero {c kmin dlt : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c kmin dlt p) : ∃ s, arcCurv p s ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨theta, hcurve, hangle⟩ := exists_arclength_angle hc hp
  have hL : 0 < perim p := perim_pos hc hp
  -- the angle is constant
  have hth0 : ∀ s, HasDerivAt theta 0 s := by
    intro s
    have h := hangle s
    rwa [show dataCurv p (s / perim p) = arcCurv p s from rfl, hcon s] at h
  have hthconst : ∀ s, theta s = theta 0 := by
    intro s
    have hdiff : Differentiable ℝ theta := fun s => (hth0 s).differentiableAt
    exact is_const_of_deriv_eq_zero hdiff (fun x => (hth0 x).deriv) s 0
  set w : ℂ := Complex.exp (Complex.I * (theta 0 : ℂ)) with hw
  have hcurve0 : ∀ s, HasDerivAt (ev p) w s := by
    intro s; rw [hw, ← hthconst s]; exact hcurve s
  -- hence the arclength parametrization is affine
  have hg : ∀ s, HasDerivAt (fun t : ℝ => ev p t - t * w) 0 s := by
    intro s
    have h := (hcurve0 s).sub (((hasDerivAt_id s).ofReal_comp).mul_const w)
    simpa using h
  have hgconst : ∀ s, ev p s - s * w = ev p 0 - (0 : ℝ) * w := by
    intro s
    have hdiff : Differentiable ℝ (fun t : ℝ => ev p t - t * w) :=
      fun t => (hg t).differentiableAt
    exact is_const_of_deriv_eq_zero hdiff (fun x => (hg x).deriv) s 0
  have hper : ev p (perim p) = ev p 0 := by simpa using periodic_ev hc hp 0
  have hkey := hgconst (perim p)
  rw [hper] at hkey
  have hwz : ((perim p : ℝ) : ℂ) * w = 0 := by push_cast at hkey ⊢; linear_combination -hkey
  have hwne : w ≠ 0 := Complex.exp_ne_zero _
  have : ((perim p : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hwz with h | h
    · exact h
    · exact absurd h hwne
  exact absurd (Complex.ofReal_eq_zero.mp this) (ne_of_gt hL)


/-- **The strictness datum of a tube member, from Harnack alone.**  Nonvanishing
of the curvature is not an assumption: it holds for every closed curve. -/
def limitStrictnessDataH_of_tube' {c dlt : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c 0 dlt p)
    (hharn : ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (arcCurv p a / Real.sqrt (1 + arcCurv p a ^ 2))
        ≤ arcCurv p b / Real.sqrt (1 + arcCurv p b ^ 2)) :
    LimitStrictnessDataH p :=
  limitStrictnessDataH_of_tube hc hp hharn (arcCurv_nonzero hc hp)

/-- **The strictness datum of a shadowing limit, from Harnack on the
approximants alone.**  This is the form the closing argument consumes: the only
input about the sequence is the paper's bounded-shift Harnack inequality at each
finite stage. -/
def limitStrictnessDataH_of_limit' {c dlt : ℝ} (hc : 0 < c) {P : ℕ → Data} {X : Data}
    (hX : IsTubeMember c 0 dlt X) (hP : Tendsto P atTop (𝓝 X))
    (hharn : ∀ n : ℕ, ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) * (arcCurv (P n) a / Real.sqrt (1 + arcCurv (P n) a ^ 2))
        ≤ arcCurv (P n) b / Real.sqrt (1 + arcCurv (P n) b ^ 2)) :
    LimitStrictnessDataH X :=
  limitStrictnessDataH_of_limit hc hX hP hharn (arcCurv_nonzero hc hX)

end UnconditionalAssembly
