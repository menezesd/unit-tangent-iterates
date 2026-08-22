import Mathlib
import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.SelectedInverseLipschitz

/-!
# The selected rears of a path of fronts, from the geometry of the slices

`UnitTangentIterates/SelectedInverseLipschitz.lean` shows that a family of selected
rears whose slices satisfy the hypotheses of the inverse Jacobi estimates *in
the normalized parameter*, with constants uniform in the time, is a normal path
of cost a fixed multiple of the cost of the front path.  Its hypotheses are
already the analytic ones of the paper's proof, but they are many, and the
constants have to be supplied by hand.

This file reduces them to the **geometry of one slice**, in the form the paper
uses, together with uniform bounds for the front period:

* the steering equation `δ_s = K − sin δ` with `δ` in the selected strip
  `0 ≤ δ ≤ arcsin κ̂` and `|K| ≤ κ̂`, `δ` periodic with the front period;
* the front normal velocity `η_F`, differentiable and periodic with the front
  period;
* the rear arclength `x(s) = ∫₀ˢ cos δ` and its inverse `sf`;
* the inverse Jacobi ODE `η_R' = sec δ · η_F ∘ sf − η_R` for the rear normal
  velocity, with `η_R` periodic with the rear period;
* two-sided bounds `0 < P₀ ≤ P t ≤ P₁` for the front period.

Everything else — the differentiability and the periodicity of the change of
variable, the bounds `cos δ ≥ √(1−κ̂²)` and `|sin δ| ≤ κ̂` on the strip, the
boundedness of the velocities, the derivative `δ_x = sec δ (K − sin δ)` in rear
arclength, the transport identity, and above all the *uniform* constants
`uconstW`, `uconst0`, `uconst1`, `uconst2` — is derived here.

Main results:

* `uconstW`, `uconst0`, `uconst1`, `uconst2` — constants depending only on the
  bounds `P₀ ≤ P ≤ P₁` for the front period and on the curvature ceiling `κ̂`,
  dominating the constants of `JacobiNormalized` for every slice
  (`constW_le_uconstW`, …);
* `exists_normalPath_of_geometry` — the selected rears of a normal path of
  fronts form a normal path of cost
  `jacobiConst (uconstW …) (uconst0 …) (uconst1 …) (uconst2 …)` times the cost
  of the front path;
* `pathDist_le_of_geometry` — the resulting Lipschitz bound for the path
  pseudodistance.

What is still assumed is the paper's lemma *Smooth dependence of the selected
rear*, in the shape of the hypotheses `hetaR`, `hderiv` below: that the rear
family really does move with a normal velocity solving the inverse Jacobi ODE.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath MarkedTopology RearTrack
  ArclengthInverse

namespace SelectedInversePathGeometry

/-! ### Uniform constants -/

/-- The uniform `L¹` constant of a path of fronts with period in `[P₀, P₁]`. -/
def uconstW (P0 P1 c : ℝ) : ℝ := P1 / (c * P0)

/-- The uniform `L¹ → L^∞` constant. -/
def uconst0 (P0 P1 c : ℝ) : ℝ := P1 / (1 - Real.exp (-(c * P0)))

/-- The uniform first-order constant. -/
def uconst1 (P0 P1 c : ℝ) : ℝ := P1 / c + P1 * P1 / (1 - Real.exp (-(c * P0)))

/-- The uniform second-order constant. -/
def uconst2 (P0 P1 c kh : ℝ) : ℝ :=
  P1 ^ 2 / (P0 * c ^ 2) + P1 ^ 2 * (2 * kh ^ 2 / c ^ 3 + 1 / c)
    + P1 ^ 2 * P1 / (1 - Real.exp (-(c * P0)))

section Constants

variable {P0 P1 c kh P l : ℝ}

theorem uconstW_nonneg (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hc : 0 < c) : 0 ≤ uconstW P0 P1 c := by
  unfold uconstW; positivity

theorem uconst0_nonneg (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hc : 0 < c) : 0 ≤ uconst0 P0 P1 c := by
  have := JacobiNormalized.one_sub_exp_pos (l0 := c * P0) (by positivity)
  unfold uconst0; positivity

theorem uconst1_nonneg (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hc : 0 < c) : 0 ≤ uconst1 P0 P1 c := by
  have := JacobiNormalized.one_sub_exp_pos (l0 := c * P0) (by positivity)
  unfold uconst1; positivity

theorem uconst2_nonneg (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hc : 0 < c) :
    0 ≤ uconst2 P0 P1 c kh := by
  have := JacobiNormalized.one_sub_exp_pos (l0 := c * P0) (by positivity)
  unfold uconst2; positivity

theorem constW_le_uconstW (hP0 : 0 < P0) (hc : 0 < c) (hP1 : 0 ≤ P1) (hPu : P ≤ P1)
    (hlc : c * P0 ≤ l) : JacobiNormalized.constW P l ≤ uconstW P0 P1 c := by
  unfold JacobiNormalized.constW uconstW
  exact div_le_div₀ hP1 hPu (by positivity) hlc

theorem const0_le_uconst0 (hP1 : 0 ≤ P1) (hPu : P ≤ P1)
    (hpos : 0 < 1 - Real.exp (-(c * P0))) :
    JacobiNormalized.const0 P (c * P0) ≤ uconst0 P0 P1 c := by
  unfold JacobiNormalized.const0 uconst0
  exact div_le_div₀ hP1 hPu hpos le_rfl

theorem const1_le_uconst1 (hc : 0 < c) (hP1 : 0 ≤ P1) (hPu : P ≤ P1) (hlu : l ≤ P1)
    (hl0 : 0 ≤ l) (hpos : 0 < 1 - Real.exp (-(c * P0))) :
    JacobiNormalized.const1 P l (c * P0) c ≤ uconst1 P0 P1 c := by
  unfold JacobiNormalized.const1 uconst1
  have h1 : l / c ≤ P1 / c := div_le_div₀ hP1 hlu hc le_rfl
  have h2 : l * P / (1 - Real.exp (-(c * P0))) ≤ P1 * P1 / (1 - Real.exp (-(c * P0))) :=
    div_le_div₀ (by positivity) (by nlinarith) hpos le_rfl
  linarith

theorem const2_le_uconst2 (hP0 : 0 < P0) (hc : 0 < c) (hP1 : 0 ≤ P1) (hPl : P0 ≤ P)
    (hPu : P ≤ P1) (hlu : l ≤ P1) (hl0 : 0 ≤ l)
    (hpos : 0 < 1 - Real.exp (-(c * P0))) :
    JacobiNormalized.const2 P l (c * P0) c kh ≤ uconst2 P0 P1 c kh := by
  have hP : 0 < P := lt_of_lt_of_le hP0 hPl
  have hl2 : l ^ 2 ≤ P1 ^ 2 := by nlinarith
  unfold JacobiNormalized.const2 uconst2
  have h1 : l ^ 2 / (P * c ^ 2) ≤ P1 ^ 2 / (P0 * c ^ 2) :=
    div_le_div₀ (by positivity) hl2 (by positivity) (by nlinarith)
  have h2 : l ^ 2 * (2 * kh ^ 2 / c ^ 3 + 1 / c) ≤ P1 ^ 2 * (2 * kh ^ 2 / c ^ 3 + 1 / c) :=
    mul_le_mul_of_nonneg_right hl2 (by positivity)
  have h3 : l ^ 2 * P / (1 - Real.exp (-(c * P0)))
      ≤ P1 ^ 2 * P1 / (1 - Real.exp (-(c * P0))) :=
    div_le_div₀ (by positivity) (by nlinarith) hpos le_rfl
  linarith

end Constants

/-! ### The geometry of one slice -/

section Slice

variable {kh : ℝ}

/-- On the selected strip the steering angle has `|sin δ| ≤ κ̂`. -/
theorem abs_sin_le_of_mem_strip (hkh0 : 0 ≤ kh) (hkh1 : kh ≤ 1) {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ Real.arcsin kh) : |Real.sin d| ≤ kh := by
  have harc : Real.arcsin kh ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two kh
  have hupper : Real.sin d ≤ kh := by
    have hmono : Real.sin d ≤ Real.sin (Real.arcsin kh) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) harc hd1
    rwa [Real.sin_arcsin (by linarith) hkh1] at hmono
  have hlower : 0 ≤ Real.sin d :=
    Real.sin_nonneg_of_nonneg_of_le_pi hd0 (by linarith [Real.pi_pos])
  rw [abs_of_nonneg hlower]
  exact hupper

end Slice

/-! ### The normal path of selected rears -/

/-- **The selected rears of a normal path of fronts form a normal path**, with
cost a uniform multiple of the cost of the front path.

The hypotheses are the geometry of the paper's proof at every time `t`: the
steering equation on the selected strip, the periodicity of the steering angle
and of the front normal velocity with the front period `P t`, the change of
variable `sf` inverting the rear arclength `x(s) = ∫₀ˢ cos δ`, the inverse
Jacobi ODE for the rear normal velocity `η_R` — the analytic content of the
lemma *Smooth dependence of the selected rear* — and two-sided bounds
`P₀ ≤ P t ≤ P₁` for the front period.  The constants are the uniform ones
above, with `c = √(1 − κ̂²)`. -/
theorem exists_normalPath_of_geometry {p q p' q' : Data} (Γ : NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {XR : ℝ → ℝ → ℂ} {nuR : ℝ → ℝ → ℂ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    -- the front period
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    -- the steering equation on the selected strip
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh)
    -- the front normal velocity
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    -- the change of variable
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    -- the inverse Jacobi ODE for the rear normal velocity
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hetaRper : ∀ t, Function.Periodic (etaR t) (rearArclength (delta t) (P t)))
    -- the front velocity of the given path
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    -- the structural data of the rear family
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u)
      ((etaR t (rearArclength (delta t) (P t) * u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t =>
      (etaR t (rearArclength (delta t) (P t) * u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧
      cost Δ = PathMetricJacobi.jacobiConst (uconstW P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (uconst0 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (uconst1 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (uconst2 P0 P1 (Real.sqrt (1 - kh ^ 2)) kh) * cost Γ := by
  set c : ℝ := Real.sqrt (1 - kh ^ 2) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact Real.sqrt_pos.mpr (by nlinarith)
  have hP1 : 0 ≤ P1 := le_trans hP0.le ((hPl 0).trans (hPu 0))
  set l : ℝ → ℝ := fun t => rearArclength (delta t) (P t) with hldef
  -- basic slice facts
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hdeltac : ∀ t, Continuous (delta t) := fun t =>
    Differentiable.continuous fun s => (hsteer t s).differentiableAt
  have hcos : ∀ t s, c ≤ Real.cos (delta t s) := fun t s =>
    Shadowing.cos_ge_of_mem_strip (hstrip0 t s) (hstrip1 t s)
  have hcospos : ∀ t s, 0 < Real.cos (delta t s) := fun t s =>
    lt_of_lt_of_le hcpos (hcos t s)
  have hcosne : ∀ t s, Real.cos (delta t s) ≠ 0 := fun t s => ne_of_gt (hcospos t s)
  have hsin : ∀ t s, |Real.sin (delta t s)| ≤ kh := fun t s =>
    abs_sin_le_of_mem_strip hkh0 hkh1.le (hstrip0 t s) (hstrip1 t s)
  -- the rear arclength and its inverse
  have hxfd : ∀ t s, HasDerivAt (rearArclength (delta t)) (Real.cos (delta t s)) s := fun t s =>
    hasDerivAt_rearArclength (hdeltac t) s
  have hmono : ∀ t, StrictMono (rearArclength (delta t)) := fun t =>
    strictMono_of_deriv_ge hcpos (hxfd t) (hcos t)
  have hsfleft : ∀ t s, sf t (rearArclength (delta t) s) = s := fun t s =>
    leftInverse_of_rightInverse (hmono t).injective (hsfinv t) s
  have hsfc : ∀ t, Continuous (sf t) := fun t =>
    continuous_of_rightInverse hcpos (hxfd t) (hcos t) (hsfinv t)
  have hsfd : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (delta t (sf t x))) x := fun t x =>
    hasDerivAt_of_rightInverse hcpos (hxfd t) (hcos t) (hsfinv t) x
  have hsfshift : ∀ t y, sf t (y + l t) = sf t y + P t := fun t y =>
    rightInverse_add_of_shift (hmono t).injective
      (fun s => rearArclength_add_period (hdeltac t) (hdper t) s) (hsfinv t) y
  -- the rear period
  have hlge : ∀ t, c * P0 ≤ l t := by
    intro t
    have h1 : c * P t ≤ l t :=
      rearArclength_ge (hdeltac t) (hcos t) (hPpos t).le
    have h2 : c * P0 ≤ c * P t := by nlinarith [hPl t]
    linarith
  have hlle : ∀ t, l t ≤ P1 := fun t =>
    (rearArclength_le_of_period (hdeltac t) (hPpos t).le).trans (hPu t)
  have hlpos : ∀ t, 0 < l t := fun t => lt_of_lt_of_le (by positivity) (hlge t)
  have hexppos : 0 < 1 - Real.exp (-(c * P0)) :=
    JacobiNormalized.one_sub_exp_pos (by positivity)
  -- the steering angle in rear arclength
  set dl : ℝ → ℝ → ℝ := fun t x => delta t (sf t x) with hdldef
  set dxv : ℝ → ℝ → ℝ := fun t x =>
    (K t (sf t x) - Real.sin (delta t (sf t x))) / Real.cos (delta t (sf t x)) with hdxvdef
  have hdld : ∀ t x, HasDerivAt (dl t) (dxv t x) x := by
    intro t x
    have h := (hsteer t (sf t x)).comp x (hsfd t x)
    refine h.congr_deriv ?_
    simp only [hdxvdef]
    field_simp
  -- the transported front velocity
  set G : ℝ → ℝ → ℝ := fun t y => etaF t (sf t y) / Real.cos (dl t y) with hGdef
  have hetaFc : ∀ t, Continuous (etaF t) := fun t =>
    Differentiable.continuous fun s => (hetaFd t s).differentiableAt
  have hGc : ∀ t, Continuous (G t) := by
    intro t
    refine Continuous.div ((hetaFc t).comp (hsfc t)) ?_ ?_
    · exact (Real.continuous_cos.comp ((hdeltac t).comp (hsfc t)))
    · intro y; exact hcosne t (sf t y)
  have hGper : ∀ t, Function.Periodic (G t) (l t) := by
    intro t y
    simp only [hGdef, hdldef, hsfshift t y]
    rw [hetaFper t (sf t y), hdper t (sf t y)]
  have htransport : ∀ t s, G t (rearArclength (delta t) s) * Real.cos (delta t s) = etaF t s := by
    intro t s
    simp only [hGdef, hdldef, hsfleft t s]
    field_simp [hcosne t s]
  -- boundedness of the velocities
  have hetaFsper : ∀ t, Function.Periodic (etaFs t) (P t) := fun t =>
    periodic_of_hasDerivAt (hetaFd t) (hetaFper t)
  have hFbdd : ∀ t, BddAbove (Set.range fun s => |etaF t s|) := fun t =>
    bddAbove_abs_of_periodic (hPpos t) (hetaFc t) (hetaFper t)
  have hF1bdd : ∀ t, BddAbove (Set.range fun s => |etaFs t s|) := fun t =>
    bddAbove_abs_of_periodic (hPpos t) (hetaFsc t) (hetaFsper t)
  have hetaRc : ∀ t, Continuous (etaR t) := fun t =>
    Differentiable.continuous fun x => (hetaR t x).differentiableAt
  have hRbdd : ∀ t, BddAbove (Set.range fun u => |etaR t (l t * u)|) := by
    intro t
    refine BddAbove.mono ?_ (bddAbove_abs_of_periodic (hlpos t) (hetaRc t) (hetaRper t))
    rintro y ⟨u, rfl⟩
    exact ⟨l t * u, rfl⟩
  -- assemble
  refine SelectedInverseLipschitz.exists_normalPath_of_selected_rears Γ
    (l0 := c * P0) (c := c) (kh := kh) (P := P) (l := l)
    (etaF := etaF) (etaFs := etaFs) (etaR := etaR) (delta := delta)
    (xf := fun t => rearArclength (delta t)) (G := G) (dl := dl) (sf := sf) (K := K)
    (dxv := dxv) (XR := XR) (nuR := nuR)
    (by positivity) hcpos
    (uconstW_nonneg hP0 hP1 hcpos) (uconst0_nonneg hP0 hP1 hcpos)
    (uconst1_nonneg hP0 hP1 hcpos) (uconst2_nonneg hP0 hP1 hcpos)
    hlge hPpos hetaFd hFbdd hF1bdd hK hdeltac hcospos
    (fun t x => hcos t (sf t x)) (fun t x => hsin t (sf t x))
    (fun t x => hsfd t x) hdld (fun t x => rfl)
    (fun t s => hxfd t s) (fun t => by simp [rearArclength]) (fun t => rfl)
    (fun t => rfl) hGc hGper hetaR hetaRper htransport hlink
    (fun t => constW_le_uconstW hP0 hcpos hP1 (hPu t) (hlge t))
    (fun t => const0_le_uconst0 hP1 (hPu t) hexppos)
    (fun t => const1_le_uconst1 hcpos hP1 (hPu t) (hlle t) (hlpos t).le hexppos)
    (fun t => const2_le_uconst2 hP0 hcpos hP1 (hPl t) (hPu t) (hlle t) (hlpos t).le hexppos)
    hstart hfinish hderiv hcont hnu hRbdd

/-- A check that the hypotheses of `exists_normalPath_of_geometry` are not
contradictory, on a nondegenerate slice: the constant path of fronts of
curvature `1/2`, with steering angle `arcsin(1/2)`, rear arclength
`x(s) = s·cos(arcsin ½)` and vanishing normal velocities, satisfies them all. -/
example (p p' : Data) :
    ∃ Δ : NormalPath p' p', Δ.T = (NormalPath.const p).T ∧
      cost Δ = PathMetricJacobi.jacobiConst
        (uconstW 1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
        (uconst0 1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
        (uconst1 1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2)))
        (uconst2 1 1 (Real.sqrt (1 - (1/2 : ℝ) ^ 2)) (1/2)) * cost (NormalPath.const p) := by
  set A : ℝ := Real.arcsin (1/2) with hA
  have hsinA : Real.sin A = 1/2 := Real.sin_arcsin (by norm_num) (by norm_num)
  have hcosA : Real.cos A = Real.sqrt (1 - (1/2 : ℝ) ^ 2) := by
    rw [hA, Real.cos_arcsin]
  have hcosApos : 0 < Real.cos A := by
    rw [hcosA]
    exact Real.sqrt_pos.mpr (by norm_num)
  have hArc : rearArclength (fun _ : ℝ => A) = fun y => y * Real.cos A := by
    funext y
    simp [rearArclength]
  refine exists_normalPath_of_geometry (p' := p') (q' := p') (NormalPath.const p)
    (P0 := 1) (P1 := 1) (kh := 1/2) (P := fun _ => 1) (delta := fun _ _ => A)
    (K := fun _ _ => 1/2) (etaF := fun _ _ => 0) (etaFs := fun _ _ => 0)
    (etaR := fun _ _ => 0) (sf := fun _ x => x / Real.cos A)
    (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    one_pos (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ s => (hasDerivAt_const s A).congr_deriv (by rw [hsinA]; ring))
    (fun _ _ => Real.arcsin_nonneg.mpr (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => rfl) (fun _ _ => by norm_num)
    (fun _ s => hasDerivAt_const s (0:ℝ)) (fun _ => continuous_const) (fun _ _ => rfl)
    (fun _ x => by rw [hArc]; field_simp)
    (fun _ x => (hasDerivAt_const x (0:ℝ)).congr_deriv (by simp))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun t u => by simpa using hasDerivAt_const t (p'.1 u))
    (fun _ => by simpa using continuous_const) (fun _ _ => by simp)

/-- **The Lipschitz bound for the path pseudodistance**, from the geometry of
the slices: if every normal path of fronts from `p` to `q` admits a family of
selected rears as in `exists_normalPath_of_geometry`, the selected inverse is
Lipschitz for the path pseudodistance with the uniform constant. -/
theorem pathDist_le_of_geometry {F : Data → Data} {p q : Data} {P0 P1 kh : ℝ}
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (h : ∀ Γ : NormalPath p q, ∃ Δ : NormalPath (F p) (F q),
      cost Δ ≤ PathMetricJacobi.jacobiConst (uconstW P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (uconst0 P0 P1 (Real.sqrt (1 - kh ^ 2))) (uconst1 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (uconst2 P0 P1 (Real.sqrt (1 - kh ^ 2)) kh) * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤
      PathMetricJacobi.jacobiConst (uconstW P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (uconst0 P0 P1 (Real.sqrt (1 - kh ^ 2))) (uconst1 P0 P1 (Real.sqrt (1 - kh ^ 2)))
        (uconst2 P0 P1 (Real.sqrt (1 - kh ^ 2)) kh) * pathDist p q := by
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  exact SelectedInverseLipschitz.pathDist_le_of_selected_rears
    (uconstW_nonneg hP0 hP1 hcpos) (uconst0_nonneg hP0 hP1 hcpos)
    (uconst1_nonneg hP0 hP1 hcpos) (uconst2_nonneg hP0 hP1 hcpos) h hne

end SelectedInversePathGeometry
