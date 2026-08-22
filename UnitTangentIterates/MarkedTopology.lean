import Mathlib
import UnitTangentIterates.ShadowingTails
import UnitTangentIterates.GeometricLimit

/-!
# The marked geometric topology and the completeness of summable normal paths

This file formalizes the definitions of Section *Regularizing backward
shadowing* of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*
that had been left implicit in the rest of the project, together with the
lemma *Completeness of summable normal paths*.

For a smooth path of curves written in normal gauge, `X_t = η ν`, the paper
sets

```
  W(Γ)   = ∫₀¹ ‖η_t‖_{L¹} dt,
  S_j(Γ) = ∫₀¹ ‖∂_s^j η_t‖_{L^∞} dt,
```

and calls *marked geometric `C²` convergence* the uniform convergence, in one
transported periodic parameter, of the curve `X`, its unit tangent `τ`, its
curvature `κ` and its speed `g`, with the limiting speed bounded away from
zero.

Main contents:

* `supNorm`, `W`, `S` : the path functionals of the paper;
* `MarkedC2Tendsto` : marked geometric `C²` convergence;
* `norm_sub_le_integral_of_hasDerivAt` : along a normal path, the displacement
  of a point is at most the time integral of the normal speed — the mechanism
  turning `S₀`, `S₁`, `S₂` into increments of `X`, `τ` and `κ`;
* `exists_tendstoUniformly_of_summable` : summable sup-norm increments give a
  uniform limit, with the tail bound;
* `exists_markedC2_limit` : summable increments of `X`, `τ`, `κ` and `g`, with
  a uniform positive lower bound on the speeds, give marked geometric `C²`
  convergence;
* `limit_of_summable_normal_paths` : **the lemma *Completeness of summable
  normal paths***: a sequence of curves with summable increments of the curve,
  the velocity and the acceleration, and with speeds bounded below, converges
  uniformly to a regular `C²` curve.
-/

noncomputable section

open Filter Topology MeasureTheory intervalIntegral

namespace MarkedTopology

/-! ### The path functionals -/

/-- The sup norm of a function of the arclength parameter. -/
def supNorm (f : ℝ → ℝ) : ℝ := ⨆ u, |f u|

theorem supNorm_nonneg (f : ℝ → ℝ) : 0 ≤ supNorm f :=
  Real.iSup_nonneg (fun _ => abs_nonneg _)

theorem le_supNorm {f : ℝ → ℝ} (hbdd : BddAbove (Set.range fun u => |f u|)) (u : ℝ) :
    |f u| ≤ supNorm f := le_ciSup hbdd u

/-- The functional `W(Γ) = ∫₀¹ ‖η_t‖_{L¹(0,L)} dt` of a normal path with normal
velocity `η`, the curve having period `L`. -/
def W (eta : ℝ → ℝ → ℝ) (L : ℝ) : ℝ := ∫ t in (0:ℝ)..1, ∫ u in (0:ℝ)..L, |eta t u|

/-- The functional `S_j(Γ) = ∫₀¹ ‖∂_s^j η_t‖_{L^∞} dt` of a normal path. -/
def S (j : ℕ) (eta : ℝ → ℝ → ℝ) : ℝ := ∫ t in (0:ℝ)..1, supNorm (iteratedDeriv j (eta t))

@[simp] theorem S_zero (eta : ℝ → ℝ → ℝ) : S 0 eta = ∫ t in (0:ℝ)..1, supNorm (eta t) := by
  simp [S, iteratedDeriv_zero]

theorem S_nonneg (j : ℕ) (eta : ℝ → ℝ → ℝ) : 0 ≤ S j eta :=
  intervalIntegral.integral_nonneg (by norm_num) (fun t _ => supNorm_nonneg _)

/-! ### Marked geometric `C²` convergence -/

/-- **Marked geometric `C²` convergence.**  In one transported periodic
parameter, the curves `X`, the unit tangents `tau`, the curvatures `kappa` and
the speeds `g` converge uniformly, and the limiting speed is bounded below by
`c > 0`. -/
def MarkedC2Tendsto (X : ℕ → ℝ → ℂ) (tau : ℕ → ℝ → ℂ) (kappa g : ℕ → ℝ → ℝ)
    (Xl taul : ℝ → ℂ) (kappal gl : ℝ → ℝ) (c : ℝ) : Prop :=
  TendstoUniformly X Xl atTop ∧ TendstoUniformly tau taul atTop ∧
    TendstoUniformly kappa kappal atTop ∧ TendstoUniformly g gl atTop ∧
    0 < c ∧ ∀ u, c ≤ gl u

/-! ### From the path functionals to increments -/

/-- **Displacement along a normal path.**  If the point `u` moves with velocity
of norm at most `m t`, then it moves a total distance at most `∫₀¹ m`.  Applied
to `X_t = ην` this bounds the increment of the curve by `S₀`, applied to
`τ_t = η_s ν` it bounds the increment of the tangent by `S₁`, and applied to
`κ_t = η_ss + κ²η` it bounds the increment of the curvature by
`S₂ + κ̂²S₀`. -/
theorem norm_sub_le_integral_of_hasDerivAt {F : ℝ → ℂ} {V : ℝ → ℂ} {m : ℝ → ℝ}
    (hF : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt F (V t) t)
    (hV : IntervalIntegrable V volume 0 1) (hm : IntervalIntegrable m volume 0 1)
    (hbd : ∀ t ∈ Set.uIcc (0:ℝ) 1, ‖V t‖ ≤ m t) :
    ‖F 1 - F 0‖ ≤ ∫ t in (0:ℝ)..1, m t := by
  have hint : (∫ t in (0:ℝ)..1, V t) = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF hV
  rw [← hint]
  refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    (Filter.Eventually.of_forall (fun t ht => hbd t ?_)) hm
  have hsub : Set.Ioc (0:ℝ) 1 ⊆ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Ioc_subset_Icc_self
  exact hsub ht

/-! ### Summable increments give uniform limits -/

/-- **A sequence with summable sup-norm increments converges uniformly**, and
the `n`-th term is within the tail `∑_{m ≥ n} d_m` of the limit. -/
theorem exists_tendstoUniformly_of_summable {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {f : ℕ → ℝ → E} {d : ℕ → ℝ} (hsum : Summable d)
    (hincr : ∀ n u, ‖f (n + 1) u - f n u‖ ≤ d n) :
    ∃ F : ℝ → E, TendstoUniformly f F atTop ∧
      ∀ n u, ‖f n u - F u‖ ≤ ShadowingTails.tail d n := by
  have hstep : ∀ u : ℝ, ∃ x : E, Tendsto (fun n => f n u) atTop (𝓝 x) ∧
      ∀ n, ‖f n u - x‖ ≤ ShadowingTails.tail d n := by
    intro u
    obtain ⟨x, hx, hdx⟩ := ShadowingTails.exists_limit_of_summable_increments
      (Z := fun n => f n u) (d := d) (C := 1) hsum
      (fun n => by simpa [dist_eq_norm, norm_sub_rev] using hincr n u)
    exact ⟨x, hx, fun n => by simpa [dist_eq_norm] using hdx n⟩
  choose F hFtendsto hFbound using hstep
  refine ⟨F, ?_, fun n u => hFbound u n⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htail : Tendsto (ShadowingTails.tail d) atTop (𝓝 0) :=
    ShadowingTails.tail_tendsto_zero
  have : ∀ᶠ n in atTop, ShadowingTails.tail d n < ε := by
    have := htail.eventually (eventually_lt_nhds hε)
    simpa using this
  filter_upwards [this] with n hn
  intro u
  calc dist (F u) (f n u) = ‖f n u - F u‖ := by rw [dist_comm, dist_eq_norm]
    _ ≤ ShadowingTails.tail d n := hFbound u n
    _ < ε := hn

/-- **Marked geometric `C²` convergence from summable increments.**  If the
increments of the curves, of the unit tangents, of the curvatures and of the
speeds are bounded by summable sequences, and every speed is at least `c > 0`,
then the four data converge uniformly and the limiting speed is still at least
`c`: the sequence converges in the marked geometric `C²` topology. -/
theorem exists_markedC2_limit {X tau : ℕ → ℝ → ℂ} {kappa g : ℕ → ℝ → ℝ}
    {dX dtau dkappa dg : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hsX : Summable dX) (hstau : Summable dtau) (hskappa : Summable dkappa)
    (hsg : Summable dg)
    (hX : ∀ n u, ‖X (n + 1) u - X n u‖ ≤ dX n)
    (htau : ∀ n u, ‖tau (n + 1) u - tau n u‖ ≤ dtau n)
    (hkappa : ∀ n u, |kappa (n + 1) u - kappa n u| ≤ dkappa n)
    (hg : ∀ n u, |g (n + 1) u - g n u| ≤ dg n)
    (hgpos : ∀ n u, c ≤ g n u) :
    ∃ (Xl taul : ℝ → ℂ) (kappal gl : ℝ → ℝ),
      MarkedC2Tendsto X tau kappa g Xl taul kappal gl c := by
  obtain ⟨Xl, hXl, -⟩ := exists_tendstoUniformly_of_summable hsX hX
  obtain ⟨taul, htaul, -⟩ := exists_tendstoUniformly_of_summable hstau htau
  obtain ⟨kappal, hkappal, -⟩ := exists_tendstoUniformly_of_summable (f := kappa) hskappa
    (fun n u => by simpa [Real.norm_eq_abs] using hkappa n u)
  obtain ⟨gl, hgl, -⟩ := exists_tendstoUniformly_of_summable (f := g) hsg
    (fun n u => by simpa [Real.norm_eq_abs] using hg n u)
  refine ⟨Xl, taul, kappal, gl, hXl, htaul, hkappal, hgl, hc, fun u => ?_⟩
  exact ge_of_tendsto (hgl.tendsto_at u) (Filter.Eventually.of_forall (fun n => hgpos n u))

/-- **Completeness of summable normal paths.**  Let `G n` be curves joined by
normal paths, and suppose the increments of the curves, of their velocities and
of their accelerations are bounded by summable sequences — this is exactly the
summability `∑ (S₀ + S₁ + S₂) < ∞` of the paper, by
`norm_sub_le_integral_of_hasDerivAt` — while all speeds are at least `c > 0`.
Then the curves converge uniformly to a curve `Gl` which is again a regular
`C²` curve: `Gl' = Vl`, `Vl' = Al`, and `‖Vl‖ ≥ c`. -/
theorem limit_of_summable_normal_paths {G V A : ℕ → ℝ → ℂ} {dG dV dA : ℕ → ℝ} {c : ℝ}
    (hderiv : ∀ n u, HasDerivAt (G n) (V n u) u)
    (hderiv2 : ∀ n u, HasDerivAt (V n) (A n u) u)
    (hsG : Summable dG) (hsV : Summable dV) (hsA : Summable dA)
    (hG : ∀ n u, ‖G (n + 1) u - G n u‖ ≤ dG n)
    (hV : ∀ n u, ‖V (n + 1) u - V n u‖ ≤ dV n)
    (hA : ∀ n u, ‖A (n + 1) u - A n u‖ ≤ dA n)
    (hspeed : ∀ n u, c ≤ ‖V n u‖) :
    ∃ (Gl Vl Al : ℝ → ℂ),
      TendstoUniformly G Gl atTop ∧ TendstoUniformly V Vl atTop ∧
      TendstoUniformly A Al atTop ∧
      ∀ u, HasDerivAt Gl (Vl u) u ∧ HasDerivAt Vl (Al u) u ∧ c ≤ ‖Vl u‖ := by
  obtain ⟨Gl, hGl, -⟩ := exists_tendstoUniformly_of_summable hsG hG
  obtain ⟨Vl, hVl, -⟩ := exists_tendstoUniformly_of_summable hsV hV
  obtain ⟨Al, hAl, -⟩ := exists_tendstoUniformly_of_summable hsA hA
  refine ⟨Gl, Vl, Al, hGl, hVl, hAl, fun u => ?_⟩
  exact GeometricLimit.limit_regular_C2 hderiv hderiv2 hVl hAl
    (fun x => hGl.tendsto_at x) hspeed u

end MarkedTopology
