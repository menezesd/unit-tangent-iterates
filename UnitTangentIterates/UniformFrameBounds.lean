import Mathlib
import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.GaugeFunctionals

/-!
# Uniform bounds for the frame data of a closed family, along a compact path

`GaugeFunctionals.lean` compares the path functionals in the normal gauge with
those in arclength, for frame data `(ξ, v)` whose first two **space**
derivatives are globally bounded:

`|ξ| ≤ A₀`, `|ξ'| ≤ A₁`, `|ξ''| ≤ A₂`, `v₀ ≤ |v| ≤ V₁`, `|v'| ≤ B₁`,
`|v''| ≤ B₂`, uniformly in the time parameter.

For the family of selected rears such bounds are not postulated in the paper:
they hold because each slice is a **closed** curve — the frame data is periodic
in the arclength — and the path parameter runs through a **compact** time
interval.  This file proves exactly that, in a form that can be fed into
`GaugeFunctionals.gauge_functionals_comparison_of_frame`.

Two points need care.

* The space derivatives must be produced as functions of the *pair* `(a, x)`,
  jointly continuous.  `partialX f a x = ∂ₓ f (a, x)`, read off the Fréchet
  derivative of the uncurried map, does this: it is the derivative of the slice
  (`hasDerivAt_partialX`), and it is one degree less smooth than `f`
  (`contDiff_partialX`).
* The bounds are required for *every* time `a ∈ ℝ`, while the data is only
  controlled on the time window `[t₀, t₁]`.  Composing the time variable with
  the clamp `a ↦ max t₀ (min a t₁)` changes nothing on the window, changes no
  space derivative, and makes the bounds global (`timeClamp`).

Main results:

* `exists_bound_of_periodic` — a jointly continuous function, periodic in the
  space variable, is bounded on `[t₀, t₁] × ℝ`;
* `GaugeFrameData` — the bundle of frame data and constants required by
  `GaugeFunctionals.gauge_functionals_comparison_of_frame`;
* `exists_gaugeFrameData` — such a bundle exists for any `C²`, space-periodic,
  nonvanishing-speed frame data, and agrees with the given data on the window;
* `GaugeFrameData.gauge_functionals_comparison` — the comparison of the path
  functionals, for the data of the bundle.
-/

noncomputable section

open Set Function

namespace UniformFrameBounds

/-! ### The partial derivative in the space variable -/

/-- The partial derivative of `f` in its second variable, as a function of the
pair. -/
def partialX (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun a x => fderiv ℝ (uncurry f) (a, x) (0, 1)

/-- `partialX f a` is the derivative of the slice `f a`. -/
theorem hasDerivAt_partialX {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (uncurry f)) (a x : ℝ) :
    HasDerivAt (f a) (partialX f a x) x := by
  have h1 : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (a, x)) (a, x) :=
    (hf.differentiable one_ne_zero _).hasFDerivAt
  have h2 : HasDerivAt (fun y : ℝ => ((a : ℝ), y)) (0, 1) x := by
    simpa using (hasDerivAt_const x a).prodMk (hasDerivAt_id x)
  exact h1.comp_hasDerivAt x h2

/-- The partial derivative is one degree less smooth than the function. -/
theorem contDiff_partialX {f : ℝ → ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ ((n : ℕ) + 1) (uncurry f)) :
    ContDiff ℝ (n : ℕ) (uncurry (partialX f)) := by
  have hd : ContDiff ℝ (n : ℕ) (fderiv ℝ (uncurry f)) := by
    refine hf.fderiv_right ?_
    exact_mod_cast le_rfl
  have := (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).contDiff.comp hd
  simpa [Function.uncurry, partialX] using this

/-- The partial derivative of a space-periodic function is space-periodic. -/
theorem periodic_partialX {f : ℝ → ℝ → ℝ} {P : ℝ} (hf : ContDiff ℝ 1 (uncurry f))
    (hper : ∀ a, Function.Periodic (f a) P) (a : ℝ) :
    Function.Periodic (partialX f a) P := by
  intro x
  have h1 : HasDerivAt (f a) (partialX f a (x + P)) (x + P) := hasDerivAt_partialX hf a _
  have h2 : HasDerivAt (fun y => f a (y + P)) (partialX f a (x + P)) x := by
    simpa using h1.comp x ((hasDerivAt_id x).add_const P)
  have h3 : HasDerivAt (f a) (partialX f a x) x := hasDerivAt_partialX hf a x
  have hfun : (fun y => f a (y + P)) = f a := funext fun y => hper a y
  rw [hfun] at h2
  exact h2.unique h3

/-! ### Boundedness from periodicity and compactness of the time window -/

/-- **A jointly continuous function, periodic in the space variable, is bounded
on a compact window of times.** -/
theorem exists_bound_of_periodic {f : ℝ → ℝ → ℝ} {P t0 t1 : ℝ} (hP : 0 < P)
    (hc : Continuous (uncurry f)) (hper : ∀ a, Function.Periodic (f a) P) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ Icc t0 t1, ∀ x, |f a x| ≤ M := by
  rcases le_or_gt t0 t1 with ht | ht
  · have hK : IsCompact (Icc t0 t1 ×ˢ Icc (0 : ℝ) P) :=
      (isCompact_Icc).prod isCompact_Icc
    have hne : (Icc t0 t1 ×ˢ Icc (0 : ℝ) P).Nonempty :=
      ⟨(t0, 0), ⟨left_mem_Icc.mpr ht, left_mem_Icc.mpr hP.le⟩⟩
    obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne (hc.abs.continuousOn)
    refine ⟨|uncurry f p|, abs_nonneg _, ?_⟩
    intro a ha x
    obtain ⟨y, hy, hxy⟩ := (hper a).exists_mem_Ico₀ hP x
    have hmem : (a, y) ∈ Icc t0 t1 ×ˢ Icc (0 : ℝ) P :=
      ⟨ha, ⟨hy.1, hy.2.le⟩⟩
    have := hmax hmem
    simpa [hxy, uncurry] using this
  · exact ⟨0, le_rfl, fun a ha => absurd (ha.1.trans ha.2) (not_le.mpr ht)⟩

/-! ### Clamping the time variable -/

/-- The clamp of the time variable to the window `[t₀, t₁]`. -/
def clampT (t0 t1 a : ℝ) : ℝ := max t0 (min a t1)

theorem clampT_mem {t0 t1 : ℝ} (ht : t0 ≤ t1) (a : ℝ) : clampT t0 t1 a ∈ Icc t0 t1 :=
  ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩

theorem clampT_of_mem {t0 t1 a : ℝ} (ha : a ∈ Icc t0 t1) : clampT t0 t1 a = a := by
  rw [clampT, min_eq_left ha.2, max_eq_right ha.1]

theorem continuous_clampT (t0 t1 : ℝ) : Continuous (clampT t0 t1) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- Reindexing the time variable of a family by the clamp. -/
def timeClamp (t0 t1 : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun a x => f (clampT t0 t1 a) x

theorem continuous_timeClamp {f : ℝ → ℝ → ℝ} {t0 t1 : ℝ} (hc : Continuous (uncurry f)) :
    Continuous (uncurry (timeClamp t0 t1 f)) :=
  hc.comp (((continuous_clampT t0 t1).comp continuous_fst).prodMk continuous_snd)

theorem timeClamp_bound {f : ℝ → ℝ → ℝ} {t0 t1 M : ℝ} (ht : t0 ≤ t1)
    (hM : ∀ a ∈ Icc t0 t1, ∀ x, |f a x| ≤ M) (a x : ℝ) :
    |timeClamp t0 t1 f a x| ≤ M :=
  hM _ (clampT_mem ht a) x

theorem timeClamp_eq {f : ℝ → ℝ → ℝ} {t0 t1 a : ℝ} (ha : a ∈ Icc t0 t1) (x : ℝ) :
    timeClamp t0 t1 f a x = f a x := by
  rw [timeClamp, clampT_of_mem ha]

theorem hasDerivAt_timeClamp {f f1 : ℝ → ℝ → ℝ} {t0 t1 : ℝ}
    (hf : ∀ a x, HasDerivAt (f a) (f1 a x) x) (a x : ℝ) :
    HasDerivAt (timeClamp t0 t1 f a) (timeClamp t0 t1 f1 a x) x :=
  hf (clampT t0 t1 a) x

/-! ### Boundedness of the derivatives of a closed slice -/

/-- The derivative of a `C²` function is `C¹`. -/
theorem contDiff_deriv_of_two {f : ℝ → ℝ} (hf : ContDiff ℝ (2 : ℕ) f) :
    ContDiff ℝ (1 : ℕ) (deriv f) := by
  have h : ContDiff ℝ ((1 : ℕ) + 1) f := by exact_mod_cast hf
  exact (contDiff_succ_iff_deriv.mp h).2.2

/-- **A `C²` periodic function is bounded together with its first two
derivatives.** -/
theorem bddAbove_abs_derivs_of_periodic {f : ℝ → ℝ} {Q : ℝ} (hQ : 0 < Q)
    (hf : ContDiff ℝ (2 : ℕ) f) (hper : Function.Periodic f Q) :
    BddAbove (Set.range fun x => |f x|) ∧ BddAbove (Set.range fun x => |deriv f x|) ∧
      BddAbove (Set.range fun x => |deriv (deriv f) x|) := by
  have hd1 : ContDiff ℝ (1 : ℕ) (deriv f) := contDiff_deriv_of_two hf
  have hd2 : Continuous (deriv (deriv f)) := by
    have h : ContDiff ℝ ((0 : ℕ) + 1) (deriv f) := by exact_mod_cast hd1
    exact ((contDiff_succ_iff_deriv.mp h).2.2).continuous
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hper1 : Function.Periodic (deriv f) Q :=
    ArclengthInverse.periodic_of_hasDerivAt (fun s => (hdiff s).hasDerivAt) hper
  have hper2 : Function.Periodic (deriv (deriv f)) Q :=
    ArclengthInverse.periodic_of_hasDerivAt
      (fun s => ((hd1.differentiable (by simp)) s).hasDerivAt) hper1
  exact ⟨ArclengthInverse.bddAbove_abs_of_periodic hQ hf.continuous hper,
    ArclengthInverse.bddAbove_abs_of_periodic hQ hd1.continuous hper1,
    ArclengthInverse.bddAbove_abs_of_periodic hQ hd2 hper2⟩

/-! ### The bundle of frame data required by the gauge comparison -/

/-- **The frame data and constants required by the comparison of the path
functionals in the normal gauge**: a tangential component `ξ` and a speed `v`,
each with two space derivatives, jointly continuous, with `v` nowhere zero, and
with global bounds for the two space derivatives of the tangential rate
`−ξ/v` — the Lipschitz constant `rateLip` of the gauge flow and the bound
`rateBound2` for its distortion.

Only the *rate* is asked to have bounded derivatives.  In particular no bound
for `ξ` itself is required, which matters: for a family of closed curves
written in its own arclength whose length changes, the closing relation makes
`ξ` drift by `Q'(t)` over each period, so `ξ` is unbounded while its arclength
derivatives — and hence, the speed being constant, the derivatives of the rate
— stay periodic.  For a bundle built from bounds on the frame data themselves,
see `exists_gaugeFrameData`. -/
structure GaugeFrameData where
  /-- The tangential component of the motion. -/
  xi : ℝ → ℝ → ℝ
  /-- Its space derivative. -/
  xi1 : ℝ → ℝ → ℝ
  /-- Its second space derivative. -/
  xi2 : ℝ → ℝ → ℝ
  /-- The speed of the slice. -/
  v : ℝ → ℝ → ℝ
  /-- Its space derivative. -/
  v1 : ℝ → ℝ → ℝ
  /-- Its second space derivative. -/
  v2 : ℝ → ℝ → ℝ
  /-- Bound for the space derivative of the tangential rate `−ξ/v`: the
  Lipschitz constant of the field of the gauge flow. -/
  rateLip : ℝ
  /-- Bound for the second space derivative of the tangential rate. -/
  rateBound2 : ℝ
  hxi : ∀ a x, HasDerivAt (xi a) (xi1 a x) x
  hxi1 : ∀ a x, HasDerivAt (xi1 a) (xi2 a x) x
  hv : ∀ a x, HasDerivAt (v a) (v1 a x) x
  hv1 : ∀ a x, HasDerivAt (v1 a) (v2 a x) x
  hvne : ∀ a x, v a x ≠ 0
  hxic : Continuous (uncurry xi)
  hxi1c : Continuous (uncurry xi1)
  hxi2c : Continuous (uncurry xi2)
  hvc : Continuous (uncurry v)
  hv1c : Continuous (uncurry v1)
  hv2c : Continuous (uncurry v2)
  hrate1 : ∀ a x, |GaugeRate.gaugeRate1 xi xi1 v v1 a x| ≤ rateLip
  hrate2 : ∀ a x, |GaugeRate.gaugeRate2 xi xi1 xi2 v v1 v2 a x| ≤ rateBound2

namespace GaugeFrameData

variable (D : GaugeFrameData)

theorem rateLip_nonneg : 0 ≤ D.rateLip := le_trans (abs_nonneg _) (D.hrate1 0 0)

theorem rateBound2_nonneg : 0 ≤ D.rateBound2 := le_trans (abs_nonneg _) (D.hrate2 0 0)

/-- The tangential rate of the bundle is globally Lipschitz in the arclength,
with constant `rateLip`. -/
theorem lipschitzWith_gaugeRate (a : ℝ) :
    LipschitzWith (Real.toNNReal D.rateLip) (GaugeRate.gaugeRate D.xi D.v a) :=
  GaugeRate.lipschitzWith_gaugeRate_of_bound D.rateLip_nonneg D.hxi D.hv D.hvne D.hrate1 a

/-- **The comparison of the path functionals in the normal gauge, for the data
of the bundle.**  This is `GaugeFunctionals.gauge_functionals_comparison` with
every hypothesis on the field of the gauge flow discharged by the bundle. -/
theorem gauge_functionals_comparison
    {eta eta1 eta2 : ℝ → ℝ} {Phi : ℝ → ℝ → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (heta1 : ∀ x, HasDerivAt eta (eta1 x) x)
    (heta2 : ∀ x, HasDerivAt eta1 (eta2 x) x)
    (hetac : Continuous eta)
    (hbdd : BddAbove (Set.range fun x => |eta x|))
    (hbdd1 : BddAbove (Set.range fun x => |eta1 x|))
    (hbdd2 : BddAbove (Set.range fun x => |eta2 x|)) {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    MarkedTopology.supNorm (fun u => eta (Phi t u)) ≤ MarkedTopology.supNorm eta ∧
    MarkedTopology.supNorm (deriv fun u => eta (Phi t u))
        ≤ MarkedTopology.supNorm eta1 * (ell * Real.exp (D.rateLip * |t|)) ∧
    MarkedTopology.supNorm (deriv (deriv fun u => eta (Phi t u)))
        ≤ MarkedTopology.supNorm eta2 * (ell * Real.exp (D.rateLip * |t|)) ^ 2
          + MarkedTopology.supNorm eta1
              * (D.rateBound2 * ell ^ 2 * |t| * Real.exp (2 * D.rateLip * |t|)) ∧
    (∫ u in a..b, |eta (Phi t u)|)
        ≤ (1 / (ell * Real.exp (-(D.rateLip * |t|))))
            * ∫ x in (Phi t a)..(Phi t b), |eta x| :=
  by
  obtain ⟨hlip, hcont, hxd, hxcont, hxxd, hxxcont, hxxbd⟩ :=
    GaugeRate.gaugeRate_flow_hypotheses_of_bounds D.rateLip_nonneg D.hxi D.hxi1 D.hv D.hv1
      D.hvne D.hxic D.hxi1c D.hxi2c D.hvc D.hv1c D.hv2c D.hrate1 D.hrate2
  have hkey := GaugeFunctionals.gauge_functionals_comparison
    (h := GaugeRate.gaugeRate D.xi D.v)
    (hx := GaugeRate.gaugeRate1 D.xi D.xi1 D.v D.v1)
    (hxx := GaugeRate.gaugeRate2 D.xi D.xi1 D.xi2 D.v D.v1 D.v2)
    (K := Real.toNNReal D.rateLip) (K2 := D.rateBound2) (Phi := Phi) (ell := ell)
    hlip hcont hPhid hell hPhi0 hxd hxcont hxxd hxxcont hxxbd
    heta1 heta2 hetac hbdd hbdd1 hbdd2 hab t
  rwa [Real.coe_toNNReal _ D.rateLip_nonneg] at hkey

/-- **The comparison of the path functionals for a closed slice.**  The three
boundedness hypotheses of `gauge_functionals_comparison` are automatic when the
normal velocity `η` of the slice is `C²` and periodic — that is, when the slice
is a closed curve. -/
theorem gauge_functionals_comparison_periodic
    {eta : ℝ → ℝ} {Phi : ℝ → ℝ → ℝ} {ell Q : ℝ} (hQ : 0 < Q)
    (heta : ContDiff ℝ (2 : ℕ) eta) (hper : Function.Periodic eta Q)
    (hell : 0 < ell) (hPhi0 : ∀ u, Phi 0 u = ell * u)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    MarkedTopology.supNorm (fun u => eta (Phi t u)) ≤ MarkedTopology.supNorm eta ∧
    MarkedTopology.supNorm (deriv fun u => eta (Phi t u))
        ≤ MarkedTopology.supNorm (deriv eta) * (ell * Real.exp (D.rateLip * |t|)) ∧
    MarkedTopology.supNorm (deriv (deriv fun u => eta (Phi t u)))
        ≤ MarkedTopology.supNorm (deriv (deriv eta)) * (ell * Real.exp (D.rateLip * |t|)) ^ 2
          + MarkedTopology.supNorm (deriv eta)
              * (D.rateBound2 * ell ^ 2 * |t| * Real.exp (2 * D.rateLip * |t|)) ∧
    (∫ u in a..b, |eta (Phi t u)|)
        ≤ (1 / (ell * Real.exp (-(D.rateLip * |t|))))
            * ∫ x in (Phi t a)..(Phi t b), |eta x| := by
  obtain ⟨hbdd, hbdd1, hbdd2⟩ := bddAbove_abs_derivs_of_periodic hQ heta hper
  have hdiff : Differentiable ℝ eta := heta.differentiable (by simp)
  have hdiff1 : Differentiable ℝ (deriv eta) :=
    (contDiff_deriv_of_two heta).differentiable (by simp)
  exact D.gauge_functionals_comparison hell hPhi0 hPhid
    (fun x => (hdiff x).hasDerivAt) (fun x => (hdiff1 x).hasDerivAt)
    heta.continuous hbdd hbdd1 hbdd2 hab t

end GaugeFrameData

/-! ### Existence of the bundle for a closed family over a compact time window -/

/-- **A `C²` frame data, periodic in the arclength, with nonvanishing speed,
obeys the bounds of the gauge comparison uniformly over a compact window of
times.**  The bundle produced agrees with the given data on the window; outside
it, the time variable is clamped, which changes no space derivative. -/
theorem exists_gaugeFrameData {xi v : ℝ → ℝ → ℝ} {P t0 t1 : ℝ}
    (hP : 0 < P) (ht : t0 ≤ t1)
    (hxi : ContDiff ℝ (3 : ℕ) (uncurry xi)) (hv : ContDiff ℝ (3 : ℕ) (uncurry v))
    (hxiper : ∀ a, Function.Periodic (xi a) P) (hvper : ∀ a, Function.Periodic (v a) P)
    (hvne : ∀ a x, v a x ≠ 0) :
    ∃ D : GaugeFrameData,
      (∀ a ∈ Icc t0 t1, ∀ x, D.xi a x = xi a x) ∧ (∀ a ∈ Icc t0 t1, ∀ x, D.v a x = v a x) ∧
      (∀ a, Function.Periodic (D.xi a) P) ∧ (∀ a, Function.Periodic (D.v a) P) := by
  -- the two space derivatives of the two functions
  have h3le2 : ((2 : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast
    (by norm_num : (2 : ℕ) ≤ 3)
  have h3le1 : ((1 : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞) := by exact_mod_cast
    (by norm_num : (1 : ℕ) ≤ 3)
  have hxi2 : ContDiff ℝ (2 : ℕ) (uncurry xi) := hxi.of_le h3le2
  have hv2 : ContDiff ℝ (2 : ℕ) (uncurry v) := hv.of_le h3le2
  have hxi1 : ContDiff ℝ (1 : ℕ) (uncurry xi) := hxi.of_le h3le1
  have hv1 : ContDiff ℝ (1 : ℕ) (uncurry v) := hv.of_le h3le1
  set xiD := partialX xi with hxiD
  set vD := partialX v with hvD
  have hxiD2 : ContDiff ℝ (2 : ℕ) (uncurry xiD) := by
    have : ContDiff ℝ ((2 : ℕ) + 1) (uncurry xi) := by exact_mod_cast hxi
    exact contDiff_partialX this
  have hvD2 : ContDiff ℝ (2 : ℕ) (uncurry vD) := by
    have : ContDiff ℝ ((2 : ℕ) + 1) (uncurry v) := by exact_mod_cast hv
    exact contDiff_partialX this
  have hxiD1 : ContDiff ℝ (1 : ℕ) (uncurry xiD) := hxiD2.of_le (by exact_mod_cast
    (by norm_num : (1 : ℕ) ≤ 2))
  have hvD1 : ContDiff ℝ (1 : ℕ) (uncurry vD) := hvD2.of_le (by exact_mod_cast
    (by norm_num : (1 : ℕ) ≤ 2))
  set xiDD := partialX xiD with hxiDD
  set vDD := partialX vD with hvDD
  have hxiDD0 : ContDiff ℝ (1 : ℕ) (uncurry xiDD) := by
    have : ContDiff ℝ ((1 : ℕ) + 1) (uncurry xiD) := by exact_mod_cast hxiD2
    exact contDiff_partialX this
  have hvDD0 : ContDiff ℝ (1 : ℕ) (uncurry vDD) := by
    have : ContDiff ℝ ((1 : ℕ) + 1) (uncurry vD) := by exact_mod_cast hvD2
    exact contDiff_partialX this
  -- periodicity of the derivatives
  have hxiDper : ∀ a, Function.Periodic (xiD a) P := periodic_partialX hxi1 hxiper
  have hvDper : ∀ a, Function.Periodic (vD a) P := periodic_partialX hv1 hvper
  have hxiDDper : ∀ a, Function.Periodic (xiDD a) P := periodic_partialX hxiD1 hxiDper
  have hvDDper : ∀ a, Function.Periodic (vDD a) P := periodic_partialX hvD1 hvDper
  -- the bounds on the window
  obtain ⟨A0, hA0nn, hA0⟩ := exists_bound_of_periodic (t0 := t0) (t1 := t1) hP
    (hxi1.continuous) hxiper
  obtain ⟨A1, hA1nn, hA1⟩ := exists_bound_of_periodic (t0 := t0) (t1 := t1) hP
    (hxiD1.continuous) hxiDper
  obtain ⟨A2, hA2nn, hA2⟩ := exists_bound_of_periodic (t0 := t0) (t1 := t1) hP
    (hxiDD0.continuous) hxiDDper
  obtain ⟨V1, hV1nn, hV1⟩ := exists_bound_of_periodic (t0 := t0) (t1 := t1) hP
    (hv1.continuous) hvper
  obtain ⟨B1, hB1nn, hB1⟩ := exists_bound_of_periodic (t0 := t0) (t1 := t1) hP
    (hvD1.continuous) hvDper
  obtain ⟨B2, hB2nn, hB2⟩ := exists_bound_of_periodic (t0 := t0) (t1 := t1) hP
    (hvDD0.continuous) hvDDper
  -- a positive lower bound for the speed: `1/|v|` is bounded above
  have hinvc : Continuous (uncurry fun a x => 1 / v a x) :=
    continuous_const.div hv1.continuous fun p => hvne p.1 p.2
  have hinvper : ∀ a, Function.Periodic (fun x => 1 / v a x) P := by
    intro a x; simp [hvper a x]
  obtain ⟨W, hWnn, hW⟩ := exists_bound_of_periodic (t0 := t0) (t1 := t1) hP hinvc hinvper
  have hWpos : 0 < W := by
    have h0 := hW t0 (left_mem_Icc.mpr ht) 0
    have hpos : 0 < |1 / v t0 0| := abs_pos.mpr (one_div_ne_zero (hvne t0 0))
    linarith
  have hvlow : ∀ a x, 1 / W ≤ |timeClamp t0 t1 v a x| := by
    intro a x
    have hb : |1 / v (clampT t0 t1 a) x| ≤ W := hW _ (clampT_mem ht a) x
    have habs : 0 < |v (clampT t0 t1 a) x| := abs_pos.mpr (hvne (clampT t0 t1 a) x)
    have hb' : 1 / |v (clampT t0 t1 a) x| ≤ W := by
      rwa [abs_div, abs_one] at hb
    rw [div_le_iff₀ habs] at hb'
    show 1 / W ≤ |v (clampT t0 t1 a) x|
    rw [div_le_iff₀ hWpos]
    linarith
  have hv0 : (0 : ℝ) < 1 / W := by positivity
  refine ⟨{
      xi := timeClamp t0 t1 xi
      xi1 := timeClamp t0 t1 xiD
      xi2 := timeClamp t0 t1 xiDD
      v := timeClamp t0 t1 v
      v1 := timeClamp t0 t1 vD
      v2 := timeClamp t0 t1 vDD
      rateLip := A1 / (1 / W) + A0 * B1 / (1 / W) ^ 2
      rateBound2 := A2 / (1 / W) + 2 * (A1 * B1) / (1 / W) ^ 2
        + A0 * (V1 * B2 + 2 * B1 ^ 2) / (1 / W) ^ 3
      hxi := hasDerivAt_timeClamp (hasDerivAt_partialX hxi1)
      hxi1 := hasDerivAt_timeClamp (hasDerivAt_partialX hxiD1)
      hv := hasDerivAt_timeClamp (hasDerivAt_partialX hv1)
      hv1 := hasDerivAt_timeClamp (hasDerivAt_partialX hvD1)
      hvne := fun a x => hvne _ x
      hxic := continuous_timeClamp hxi1.continuous
      hxi1c := continuous_timeClamp hxiD1.continuous
      hxi2c := continuous_timeClamp hxiDD0.continuous
      hvc := continuous_timeClamp hv1.continuous
      hv1c := continuous_timeClamp hvD1.continuous
      hv2c := continuous_timeClamp hvDD0.continuous
      hrate1 := fun a x => GaugeRate.abs_gaugeRate1_le hv0 hvlow
        (timeClamp_bound ht hA0) (timeClamp_bound ht hA1) (timeClamp_bound ht hB1) a x
      hrate2 := fun a x => GaugeRate.abs_gaugeRate2_le hv0 hvlow
        (timeClamp_bound ht hV1) (timeClamp_bound ht hA0) (timeClamp_bound ht hA1)
        (timeClamp_bound ht hA2) (timeClamp_bound ht hB1) (timeClamp_bound ht hB2) a x },
    fun a ha x => timeClamp_eq ha x, fun a ha x => timeClamp_eq ha x,
    fun a => hxiper _, fun a => hvper _⟩

end UniformFrameBounds
