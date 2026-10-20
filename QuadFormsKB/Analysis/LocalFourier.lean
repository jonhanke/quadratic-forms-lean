import QuadFormsKB.Analysis.GaussianSchwartz
import QuadFormsKB.Citation

/-!
# Local Fourier analysis on $\mathbb{Q}_p$ and $\mathbb{R}$

Notation: $e(t) = e^{2\pi i t}$ (Mathlib's `Real.fourierChar`, written `𝐞`, valued in the unit circle
$\mathbb{C}^1$ = `Circle`).

**The standard character of $\mathbb{Q}_p$.** Every $x \in \mathbb{Q}_p$ is congruent modulo $\mathbb{Z}_p$ to some
$r \in \mathbb{Z}[1/p]$ (`exists_pFrac`), unique modulo $\mathbb{Z}$ (`pFrac_sub_isInt`). This $r \bmod \mathbb{Z}$ is the
$p$-adic fractional part $\{x\}_p$, and $\psi_p(x) = e(-\{x\}_p)$ (`psiP`) is a continuous additive character
$\mathbb{Q}_p \to \mathbb{C}^1$ (`continuous_psiP`) with kernel exactly $\mathbb{Z}_p$ (`psiP_eq_one_iff`); `psiP_inv_p`:
$\psi_p(1/p) = e(-1/p) \ne 1$. The sign is Tate's: for $r \in \mathbb{Q}$, $e(r)\prod_p \psi_p(r) = 1$.

**Haar measure.** `haarP`: $\operatorname{vol}(\mathbb{Z}_p) = 1$; `haarP_closedBall`: $\operatorname{vol}(p^k\mathbb{Z}_p) = p^{-k}$,
$k \in \mathbb{Z}$. `annihP_latticeP`: $(p^k\mathbb{Z}_p)^\perp = p^{-k}\mathbb{Z}_p$ for the pairing $\psi_p(xy)$, and
`haarP_selfDual`: $\operatorname{vol}(L)\operatorname{vol}(L^\perp) = 1$, i.e. $dx$ is self-dual.

**Fourier transform** $\hat f(y) = \int f(x)\psi_p(xy)\,dx$ (`fourierP`). `setIntegral_addChar_addSubgroup` (any abelian
group): $\int_H \chi = \mu(H)$ or $0$. `fourierP_ballInd`:
$\widehat{\mathbf 1_{c+p^k\mathbb{Z}_p}}(y) = p^{-k}\psi_p(cy)\mathbf 1_{p^{-k}\mathbb{Z}_p}(y)$; `fourierInvP_fourierP_ballInd` and
`fourierInvP_fourierP_of_isSchwartzBruhat`: Fourier inversion $f(x) = \int\hat f(y)\psi_p(-xy)\,dy$ for Schwartz–Bruhat
functions (finite combinations of coset indicators, `IsSchwartzBruhatP`).

**The real place.** $\psi_\infty(x) = e(x)$ (`psiR`), `fourierR` $\hat f(y) = \int f(x)e(xy)\,dx$ (Mathlib's `𝓕⁻`),
`fourierInvR_fourierR` (inversion, Lebesgue measure is self-dual), `fourierR_gaussianSchwartz`
($\widehat{e^{-bx^2}}(y) = (\pi/b)^{1/2}e^{-\pi^2y^2/b}$, reusing `gaussianSchwartz`), `fourierR_gaussian_pi`
($e^{-\pi x^2}$ is self-dual).

The general completion $F_v$ of a number field is in `LocalFourierNF.lean`.

Sources: Tate's thesis, in Cassels–Fröhlich, *Algebraic Number Theory*, Ch. XV, §2.2 [unverified];
Weil, *Basic Number Theory*, Ch. II §5 [unverified].
-/

open MeasureTheory Metric
open scoped Real FourierTransform

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

/-! ## The $p$-adic fractional part and the character $\psi_p$ -/

section Character

variable (p : ℕ) [hp : Fact p.Prime]

/-- $r \in \mathbb{Z}[1/p]$: the rational $r$ is $n / p^k$ for some $n \in \mathbb{Z}$ and $k \in \mathbb{N}$. -/
def IsPFrac (r : ℚ) : Prop := ∃ (n : ℤ) (k : ℕ), r = n / (p : ℚ) ^ k

variable {p}

lemma IsPFrac.zero : IsPFrac p 0 := ⟨0, 0, by simp⟩

lemma IsPFrac.intCast (m : ℤ) : IsPFrac p m := ⟨m, 0, by simp⟩

lemma IsPFrac.add {r s : ℚ} (hr : IsPFrac p r) (hs : IsPFrac p s) : IsPFrac p (r + s) := by
  obtain ⟨n, k, rfl⟩ := hr
  obtain ⟨m, l, rfl⟩ := hs
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine ⟨n * p ^ l + m * p ^ k, k + l, ?_⟩
  field_simp
  push_cast
  ring

lemma IsPFrac.neg {r : ℚ} (hr : IsPFrac p r) : IsPFrac p (-r) := by
  obtain ⟨n, k, rfl⟩ := hr
  exact ⟨-n, k, by push_cast; ring⟩

lemma IsPFrac.sub {r s : ℚ} (hr : IsPFrac p r) (hs : IsPFrac p s) : IsPFrac p (r - s) := by
  rw [sub_eq_add_neg]; exact hr.add hs.neg

/-- An element of $\mathbb{Z}[1/p]$ that is a $p$-adic integer is an integer. -/
lemma IsPFrac.isInt {r : ℚ} (hr : IsPFrac p r) (h : ‖(r : ℚ_[p])‖ ≤ 1) : ∃ m : ℤ, r = m := by
  obtain ⟨n, k, rfl⟩ := hr
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpos : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast hp.out.pos) k
  have hn : ‖(n : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
    push_cast at h
    rw [norm_div, norm_pow, Padic.norm_p, inv_pow, div_inv_eq_mul] at h
    rw [zpow_neg, zpow_natCast, ← one_div, le_div_iff₀ hpos]
    exact h
  obtain ⟨c, hc⟩ := (Padic.norm_int_le_pow_iff_dvd n k).mp hn
  refine ⟨c, ?_⟩
  rw [hc]
  have : (p : ℚ) ^ k ≠ 0 := by have := hp.out.ne_zero; positivity
  push_cast
  field_simp

/-- **Existence of the $p$-adic fractional part:** every $x \in \mathbb{Q}_p$ is congruent modulo $\mathbb{Z}_p$ to
an element of $\mathbb{Z}[1/p]$. -/
lemma exists_pFrac (x : ℚ_[p]) : ∃ r : ℚ, IsPFrac p r ∧ ‖x - r‖ ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set y : ℚ_[p] := x * (p : ℚ_[p]) ^ k with hy
  have hy1 : ‖y‖ ≤ 1 := by
    rw [hy, norm_mul, norm_pow, Padic.norm_p, inv_pow]
    rw [← div_eq_mul_inv, div_le_one hpk]; exact hk.le
  set z : ℤ_[p] := ⟨y, hy1⟩
  set c : ℕ := PadicInt.appr z k
  have hc : ‖z - (c : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ k).mpr (PadicInt.appr_spec k z)
  refine ⟨(c : ℤ) / (p : ℚ) ^ k, ⟨c, k, rfl⟩, ?_⟩
  have hxe : x - (((c : ℤ) / (p : ℚ) ^ k : ℚ) : ℚ_[p]) = (y - c) / (p : ℚ_[p]) ^ k := by
    rw [hy]; push_cast; field_simp
  rw [hxe, norm_div, norm_pow, Padic.norm_p, inv_pow, div_inv_eq_mul]
  have hc' : ‖y - (c : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
    have := hc; rw [PadicInt.norm_def] at this; simpa using this
  rw [zpow_neg, zpow_natCast] at hc'
  calc ‖y - (c : ℚ_[p])‖ * (p : ℝ) ^ k ≤ ((p : ℝ) ^ k)⁻¹ * (p : ℝ) ^ k := by gcongr
    _ = 1 := inv_mul_cancel₀ hpk.ne'

/-- Two representatives in $\mathbb{Z}[1/p]$ of the same class of $\mathbb{Q}_p/\mathbb{Z}_p$ differ by an integer. -/
lemma pFrac_sub_isInt {x : ℚ_[p]} {r s : ℚ} (hr : IsPFrac p r) (hs : IsPFrac p s)
    (hxr : ‖x - r‖ ≤ 1) (hxs : ‖x - s‖ ≤ 1) : ∃ m : ℤ, r - s = m := by
  refine (hr.sub hs).isInt ?_
  have : ((r - s : ℚ) : ℚ_[p]) = (x - s) - (x - r) := by push_cast; ring
  rw [this]
  exact (Padic.nonarchimedean _ _ |>.trans_eq' (by rw [sub_eq_add_neg])).trans
    (by rw [norm_neg]; exact max_le hxs hxr)

/-- The $p$-adic fractional part, as a chosen representative $\{x\}_p \in \mathbb{Z}[1/p]$ of $x + \mathbb{Z}_p$
(well defined modulo $\mathbb{Z}$; only $e(\pm\{x\}_p)$ is used). -/
def padicFract (x : ℚ_[p]) : ℚ := (exists_pFrac x).choose

lemma padicFract_spec (x : ℚ_[p]) : IsPFrac p (padicFract x) ∧ ‖x - padicFract x‖ ≤ 1 :=
  (exists_pFrac x).choose_spec

lemma fourierChar_intCast (m : ℤ) : 𝐞 (m : ℝ) = 1 := by
  rw [Real.fourierChar_apply']
  exact Circle.exp_two_pi_mul_int m

/-- $e(t) = 1$ iff $t \in \mathbb{Z}$. -/
lemma fourierChar_eq_one_iff (t : ℝ) : 𝐞 t = 1 ↔ ∃ m : ℤ, t = m := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by nlinarith [Real.pi_pos]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

/-- The value $e(-r)$ does not depend on the representative $r \in \mathbb{Z}[1/p]$ of $x + \mathbb{Z}_p$. -/
lemma fourierChar_pFrac_eq {x : ℚ_[p]} {r s : ℚ} (hr : IsPFrac p r) (hs : IsPFrac p s)
    (hxr : ‖x - r‖ ≤ 1) (hxs : ‖x - s‖ ≤ 1) : 𝐞 (-(r : ℝ)) = 𝐞 (-(s : ℝ)) := by
  obtain ⟨m, hm⟩ := pFrac_sub_isInt hr hs hxr hxs
  have : -(r : ℝ) = -(s : ℝ) + ((-m : ℤ) : ℝ) := by
    have : (r : ℝ) = s + m := by rw [add_comm]; exact_mod_cast (sub_eq_iff_eq_add.mp hm)
    rw [this]; push_cast; ring
  rw [this, AddChar.map_add_eq_mul, fourierChar_intCast, mul_one]

/-- **The standard additive character of $\mathbb{Q}_p$:** $\psi_p(x) = e(-\{x\}_p)$, where $\{x\}_p \in \mathbb{Z}[1/p]$ is
the $p$-adic fractional part (`padicFract`, any $r \in \mathbb{Z}[1/p]$ with $x - r \in \mathbb{Z}_p$, see `psiP_eq`).
Tate's normalization: for $r \in \mathbb{Q}$, $e(r) \prod_p \psi_p(r) = 1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, the character $x \\mapsto e^{-2\\pi i\\lambda(x)}$ [unverified]"]
def psiP : AddChar ℚ_[p] Circle where
  toFun x := 𝐞 (-(padicFract x : ℝ))
  map_zero_eq_one' := by
    rw [fourierChar_pFrac_eq (padicFract_spec (0 : ℚ_[p])).1 IsPFrac.zero
      (padicFract_spec (0 : ℚ_[p])).2 (by simp)]
    simp
  map_add_eq_mul' x y := by
    obtain ⟨hx, hx'⟩ := padicFract_spec x
    obtain ⟨hy, hy'⟩ := padicFract_spec y
    have hxy : ‖(x + y) - ((padicFract x + padicFract y : ℚ) : ℚ_[p])‖ ≤ 1 := by
      have : (x + y) - ((padicFract x + padicFract y : ℚ) : ℚ_[p]) =
          (x - padicFract x) + (y - padicFract y) := by push_cast; ring
      rw [this]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hy')
    rw [fourierChar_pFrac_eq (padicFract_spec (x + y)).1 (hx.add hy) (padicFract_spec (x + y)).2 hxy]
    push_cast
    rw [neg_add, AddChar.map_add_eq_mul]

/-- $\psi_p(x) = e(-r)$ for **any** $r \in \mathbb{Z}[1/p]$ with $\|x - r\|_p \le 1$. -/
theorem psiP_eq {x : ℚ_[p]} {r : ℚ} (hr : IsPFrac p r) (hxr : ‖x - r‖ ≤ 1) :
    psiP x = 𝐞 (-(r : ℝ)) :=
  fourierChar_pFrac_eq (padicFract_spec x).1 hr (padicFract_spec x).2 hxr

/-- $\psi_p$ on rationals with $p$-power denominator: $\psi_p(r) = e(-r)$ for $r \in \mathbb{Z}[1/p]$. -/
theorem psiP_pFrac {r : ℚ} (hr : IsPFrac p r) : psiP (r : ℚ_[p]) = 𝐞 (-(r : ℝ)) :=
  psiP_eq hr (by simp)

/-- **The kernel of $\psi_p$ is exactly $\mathbb{Z}_p$:** $\psi_p(x) = 1 \iff \|x\|_p \le 1$ (conductor $\mathbb{Z}_p$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Lemma 2.2.1 [unverified]"]
theorem psiP_eq_one_iff (x : ℚ_[p]) : psiP x = 1 ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro h
    obtain ⟨hr, hxr⟩ := padicFract_spec x
    have h' : 𝐞 (-(padicFract x : ℝ)) = 1 := h
    obtain ⟨m, hm⟩ := (fourierChar_eq_one_iff _).mp h'
    have hrm : (padicFract x : ℝ) = ((-m : ℤ) : ℝ) := by push_cast; linarith
    have hrm' : padicFract x = ((-m : ℤ) : ℚ) := by exact_mod_cast hrm
    have : x = (x - padicFract x) + padicFract x := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hxr ?_)
    rw [hrm']; push_cast; exact_mod_cast Padic.norm_int_le_one _
  · intro h
    rw [psiP_eq IsPFrac.zero (by simpa using h)]
    simp

/-- $\psi_p$ is constant on cosets of $\mathbb{Z}_p$. -/
lemma psiP_add_of_norm_le_one (x : ℚ_[p]) {z : ℚ_[p]} (hz : ‖z‖ ≤ 1) : psiP (x + z) = psiP x := by
  rw [AddChar.map_add_eq_mul, (psiP_eq_one_iff z).mpr hz, mul_one]

/-- **$\psi_p$ is continuous** (indeed locally constant). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem continuous_psiP : Continuous (psiP (p := p)) := by
  refine continuous_iff_continuousAt.mpr fun x => (continuousAt_const (y := psiP x)).congr ?_
  filter_upwards [ball_mem_nhds x one_pos] with y hy
  rw [mem_ball, dist_eq_norm] at hy
  have := psiP_add_of_norm_le_one x (z := y - x) hy.le
  rw [add_sub_cancel] at this
  exact this.symm

/-- **$\psi_p$ is nontrivial just outside $\mathbb{Z}_p$:** $\psi_p(1/p) = e(-1/p) \ne 1$. -/
theorem psiP_inv_p : psiP ((p : ℚ_[p])⁻¹) = 𝐞 (-(1 / p : ℝ)) ∧ psiP ((p : ℚ_[p])⁻¹) ≠ 1 := by
  have hr : IsPFrac p (1 / p : ℚ) := ⟨1, 1, by simp⟩
  have h := psiP_pFrac hr
  push_cast at h
  rw [one_div] at h
  refine ⟨by rw [h], ?_⟩
  rw [Ne, psiP_eq_one_iff, norm_inv, Padic.norm_p, inv_inv]
  exact_mod_cast not_le.mpr hp.out.one_lt

end Character

/-! ## Haar measure on $\mathbb{Q}_p$ and the lattices $p^k\mathbb{Z}_p$ -/

section Haar

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Borel $\sigma$-algebra on $\mathbb{Q}_p$. -/
instance : MeasurableSpace ℚ_[p] := borel ℚ_[p]

instance : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- $\mathbb{Z}_p = \{\|x\|_p \le 1\}$, as a compact set with nonempty interior. -/
def zpCompacts : TopologicalSpace.PositiveCompacts ℚ_[p] where
  carrier := closedBall 0 1
  isCompact' := isCompact_closedBall 0 1
  interior_nonempty' := ⟨0, by
    rw [(IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).interior_eq]
    simp⟩

/-- **The Haar measure $dx$ on $\mathbb{Q}_p$ normalized by $\operatorname{vol}(\mathbb{Z}_p) = 1$.** Since the
conductor of $\psi_p$ is $\mathbb{Z}_p$ (the different of $\mathbb{Q}_p/\mathbb{Q}_p$ is trivial), this is the measure that
is self-dual for $\psi_p$ (`haarP_selfDual`, `fourierInvP_fourierP_of_isSchwartzBruhat`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, self-dual measure [unverified]"]
def haarP : Measure ℚ_[p] := Measure.addHaarMeasure (zpCompacts p)

instance : (haarP p).IsAddHaarMeasure := by unfold haarP; infer_instance

lemma haarP_closedBall_one : haarP p (closedBall 0 1) = 1 := Measure.addHaarMeasure_self

variable {p}

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos

lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

lemma zpow_p_pos (k : ℤ) : (0 : ℝ) < (p : ℝ) ^ k := zpow_pos p_pos k

/-- $\|p^k\|_p = p^{-k}$. -/
lemma norm_p_zpow (k : ℤ) : ‖(p : ℚ_[p]) ^ k‖ = (p : ℝ) ^ (-k) := Padic.norm_p_zpow k

/-- $\|x\|_p \le p^{n}$ iff $\|x\|_p < p^{n+1}$ (the norm takes values in $p^{\mathbb{Z}} \cup \{0\}$). -/
lemma norm_le_zpow_iff_lt (x : ℚ_[p]) (n : ℤ) :
    ‖x‖ ≤ (p : ℝ) ^ n ↔ ‖x‖ < (p : ℝ) ^ (n + 1) := Padic.norm_le_pow_iff_norm_lt_pow_add_one x n

/-- The ball $p^k\mathbb{Z}_p = \{x : \|x\|_p \le p^{-k}\}$ is the disjoint union of the $p$ translates
$jp^k + p^{k+1}\mathbb{Z}_p$, $0 \le j < p$. -/
lemma closedBall_eq_iUnion (k : ℤ) :
    closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-k)) =
      ⋃ j : Fin p, closedBall ((j : ℚ_[p]) * (p : ℚ_[p]) ^ k) ((p : ℝ) ^ (-(k + 1))) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  ext x
  simp only [mem_closedBall, Set.mem_iUnion, dist_eq_norm, sub_zero]
  constructor
  · intro hx
    set y : ℚ_[p] := x / (p : ℚ_[p]) ^ k
    have hy : ‖y‖ ≤ 1 := by
      rw [norm_div, norm_p_zpow, div_le_one (zpow_p_pos _)]; exact hx
    set z : ℤ_[p] := ⟨y, hy⟩
    obtain ⟨n, hnp, hn⟩ := PadicInt.exists_mem_range (x := z)
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hn
    have hn' : ‖y - n‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
      rw [norm_le_zpow_iff_lt]
      have : ‖z - (n : ℤ_[p])‖ = ‖y - n‖ := by
        rw [PadicInt.norm_def]; push_cast; rfl
      rw [← this]; simpa using hn
    refine ⟨⟨n, hnp⟩, ?_⟩
    have : x - (n : ℚ_[p]) * (p : ℚ_[p]) ^ k = (y - n) * (p : ℚ_[p]) ^ k := by
      simp only [y]; field_simp
    rw [this, norm_mul, norm_p_zpow]
    calc ‖y - n‖ * (p : ℝ) ^ (-k) ≤ (p : ℝ) ^ (-1 : ℤ) * (p : ℝ) ^ (-k) := by
          gcongr
      _ = (p : ℝ) ^ (-(k + 1)) := by rw [← zpow_add₀ p_pos.ne']; ring_nf
  · rintro ⟨j, hj⟩
    have hjn : ‖(j : ℚ_[p]) * (p : ℚ_[p]) ^ k‖ ≤ (p : ℝ) ^ (-k) := by
      rw [norm_mul, norm_p_zpow]
      exact mul_le_of_le_one_left (zpow_p_pos _).le (by exact_mod_cast Padic.norm_int_le_one (j : ℤ))
    have hle : (p : ℝ) ^ (-(k + 1)) ≤ (p : ℝ) ^ (-k) :=
      zpow_le_zpow_right₀ one_lt_p.le (by omega)
    have : x = (x - (j : ℚ_[p]) * (p : ℚ_[p]) ^ k) + (j : ℚ_[p]) * (p : ℚ_[p]) ^ k := by ring
    rw [this]
    exact (Padic.nonarchimedean _ _).trans (max_le (hj.trans hle) hjn)

lemma closedBall_disjoint (k : ℤ) :
    Pairwise (Function.onFun Disjoint fun j : Fin p =>
      closedBall ((j : ℚ_[p]) * (p : ℚ_[p]) ^ k) ((p : ℝ) ^ (-(k + 1)))) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  rw [mem_closedBall, dist_eq_norm] at hxi hxj
  apply hij
  have hd : ‖(((i : ℤ) - (j : ℤ) : ℤ) : ℚ_[p]) * (p : ℚ_[p]) ^ k‖ ≤ (p : ℝ) ^ (-(k + 1)) := by
    have : (((i : ℤ) - (j : ℤ) : ℤ) : ℚ_[p]) * (p : ℚ_[p]) ^ k =
        (x - (j : ℚ_[p]) * (p : ℚ_[p]) ^ k) - (x - (i : ℚ_[p]) * (p : ℚ_[p]) ^ k) := by
      push_cast; ring
    rw [this]
    refine (Padic.nonarchimedean _ _ |>.trans_eq' (by rw [sub_eq_add_neg])).trans ?_
    rw [norm_neg]; exact max_le hxj hxi
  have hd1 : ‖(((i : ℤ) - (j : ℤ) : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
    have e : (p : ℝ) ^ (-(k + 1)) = (p : ℝ) ^ (-((1 : ℕ) : ℤ)) * (p : ℝ) ^ (-k) := by
      rw [← zpow_add₀ p_pos.ne']; ring_nf
    rw [norm_mul, norm_p_zpow, e] at hd
    exact le_of_mul_le_mul_right hd (zpow_p_pos _)
  have hdvd : (p : ℤ) ∣ (i : ℤ) - (j : ℤ) := by
    simpa using (Padic.norm_int_le_pow_iff_dvd ((i : ℤ) - (j : ℤ)) 1).mp hd1
  obtain ⟨c, hc⟩ := hdvd
  have hi := i.isLt
  have hj := j.isLt
  have hc0 : c = 0 := by
    by_contra hc0
    rcases lt_or_gt_of_ne hc0 with h | h
    · have : (p : ℤ) * c ≤ -(p : ℤ) := by nlinarith
      omega
    · have : (p : ℤ) * c ≥ (p : ℤ) := by nlinarith
      omega
  ext
  rw [hc0, mul_zero, sub_eq_zero] at hc
  exact_mod_cast hc

/-- $\operatorname{vol}(p^k\mathbb{Z}_p) = p \cdot \operatorname{vol}(p^{k+1}\mathbb{Z}_p)$. -/
lemma haarP_closedBall_succ (k : ℤ) :
    haarP p (closedBall 0 ((p : ℝ) ^ (-k))) = p * haarP p (closedBall 0 ((p : ℝ) ^ (-(k + 1)))) := by
  rw [closedBall_eq_iUnion k, measure_iUnion (closedBall_disjoint k)
    (fun _ => measurableSet_closedBall)]
  simp_rw [Measure.addHaar_closedBall_center]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Volumes of the lattices:** $\operatorname{vol}(p^k\mathbb{Z}_p) = p^{-k}$ for all $k \in \mathbb{Z}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem haarP_closedBall (k : ℤ) :
    haarP p (closedBall 0 ((p : ℝ) ^ (-k))) = ENNReal.ofReal ((p : ℝ) ^ (-k)) := by
  have hpE : (p : ENNReal) = ENNReal.ofReal p := by simp
  induction k using Int.induction_on with
  | zero => simp [haarP_closedBall_one]
  | succ k ih =>
    have h := haarP_closedBall_succ (p := p) k
    rw [ih, hpE] at h
    have hp0 : ENNReal.ofReal p ≠ 0 := by simp [hp.out.ne_zero]
    rw [eq_comm, ← ENNReal.eq_div_iff hp0 ENNReal.ofReal_ne_top] at h
    rw [h, ← ENNReal.ofReal_div_of_pos p_pos]
    congr 1
    rw [neg_add, zpow_add₀ p_pos.ne', zpow_neg_one, div_eq_mul_inv]
  | pred k ih =>
    have h := haarP_closedBall_succ (p := p) (-(k : ℤ) - 1)
    have e : -(-(k : ℤ) - 1 + 1) = -(-(k : ℤ)) := by ring
    rw [e, ih, hpE, ← ENNReal.ofReal_mul p_pos.le] at h
    rw [h]
    congr 1
    rw [← zpow_one_add₀ p_pos.ne']
    congr 1
    ring

/-- The volume of $p^k\mathbb{Z}_p$, as a real number: $p^{-k}$. -/
theorem haarP_real_closedBall (k : ℤ) :
    (haarP p).real (closedBall 0 ((p : ℝ) ^ (-k))) = (p : ℝ) ^ (-k) := by
  rw [Measure.real, haarP_closedBall, ENNReal.toReal_ofReal (zpow_p_pos _).le]

end Haar

/-! ## Integrals of characters over subgroups -/

section CharIntegral

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

open scoped Classical in
/-- **Orthogonality of characters on a subgroup:** for a left-invariant measure $\mu$ on an abelian group $G$,
a measurable subgroup $H$ and a character $\chi : G \to \mathbb{C}^1$,
$$\int_H \chi(x)\, d\mu(x) = \begin{cases} \mu(H) & \chi|_H = 1,\\ 0 & \text{otherwise.}\end{cases}$$
(If $\mu(H) = \infty$, both sides are $0$ by Lean's conventions.) -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem setIntegral_addChar_addSubgroup (μ : Measure G) [μ.IsAddLeftInvariant] (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (χ : AddChar G Circle) :
    ∫ x in (H : Set G), (χ x : ℂ) ∂μ = if ∀ x ∈ H, χ x = 1 then (μ.real H : ℂ) else 0 := by
  split_ifs with h
  · rw [setIntegral_congr_fun hH (g := fun _ => (1 : ℂ)) (fun x hx => by simp [h x hx]),
      setIntegral_const, Complex.real_smul, mul_one]
  · push Not at h
    obtain ⟨a, ha, hχa⟩ := h
    set I := ∫ x in (H : Set G), (χ x : ℂ) ∂μ
    have key : I = (χ a : ℂ) * I := by
      simp only [I]
      rw [← integral_indicator hH, ← integral_const_mul]
      conv_lhs => rw [← integral_add_right_eq_self _ a]
      congr 1
      ext x
      by_cases hx : x ∈ H
      · have hxa : x + a ∈ H := H.add_mem hx ha
        rw [Set.indicator_of_mem (show x + a ∈ (H : Set G) from hxa),
          Set.indicator_of_mem (show x ∈ (H : Set G) from hx), AddChar.map_add_eq_mul, Circle.coe_mul,
          mul_comm]
      · have hxa : x + a ∉ H := fun h' => hx (by simpa using H.sub_mem h' ha)
        rw [Set.indicator_of_notMem (show x + a ∉ (H : Set G) from hxa),
          Set.indicator_of_notMem (show x ∉ (H : Set G) from hx), mul_zero]
    have h1 : (χ a : ℂ) ≠ 1 := fun h' => hχa (Circle.ext (by simpa using h'))
    have : (1 - (χ a : ℂ)) * I = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1.symm)

end CharIntegral

/-! ## The Fourier transform on $\mathbb{Q}_p$ -/

section FourierQp

variable {p : ℕ} [hp : Fact p.Prime]

variable (p) in
/-- The lattice $p^k\mathbb{Z}_p = \{x \in \mathbb{Q}_p : \|x\|_p \le p^{-k}\}$, $k \in \mathbb{Z}$, as an additive subgroup. -/
def latticeP (k : ℤ) : AddSubgroup ℚ_[p] where
  carrier := closedBall 0 ((p : ℝ) ^ (-k))
  add_mem' {x y} hx hy := by
    simp only [mem_closedBall, dist_zero_right] at hx hy ⊢
    exact (Padic.nonarchimedean x y).trans (max_le hx hy)
  zero_mem' := by simp [(zpow_p_pos (p := p) _).le]
  neg_mem' {x} hx := by simpa using hx

lemma mem_latticeP {k : ℤ} {x : ℚ_[p]} : x ∈ latticeP p k ↔ ‖x‖ ≤ (p : ℝ) ^ (-k) := by
  simp [latticeP]

lemma coe_latticeP (k : ℤ) : (latticeP p k : Set ℚ_[p]) = closedBall 0 ((p : ℝ) ^ (-k)) := rfl

variable (p) in
/-- The **annihilator** of $S \subseteq \mathbb{Q}_p$ under the pairing $(x, y) \mapsto \psi_p(xy)$:
$S^\perp = \{y : \psi_p(xy) = 1 \text{ for all } x \in S\}$. -/
def annihP (S : Set ℚ_[p]) : Set ℚ_[p] := {y | ∀ x ∈ S, psiP (x * y) = 1}

/-- **The dual lattice:** $(p^k\mathbb{Z}_p)^\perp = p^{-k}\mathbb{Z}_p$ for the pairing $\psi_p(xy)$ (the conductor of
$\psi_p$ is $\mathbb{Z}_p$, so the dual of $\mathbb{Z}_p$ is $\mathbb{Z}_p$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Lemma 2.2.1 [unverified]"]
theorem annihP_latticeP (k : ℤ) : annihP p (latticeP p k) = latticeP p (-k) := by
  ext y
  simp only [annihP, SetLike.mem_coe, mem_latticeP, Set.mem_ofPred_eq, psiP_eq_one_iff, neg_neg]
  constructor
  · intro h
    have := h ((p : ℚ_[p]) ^ k) (by rw [norm_p_zpow])
    rw [norm_mul, norm_p_zpow, zpow_neg, inv_mul_le_iff₀ (zpow_p_pos _), mul_one] at this
    exact this
  · intro hy x hx
    rw [norm_mul]
    calc ‖x‖ * ‖y‖ ≤ (p : ℝ) ^ (-k) * (p : ℝ) ^ k := by gcongr
      _ = 1 := by rw [← zpow_add₀ p_pos.ne', neg_add_cancel, zpow_zero]

/-- **Self-duality of $dx$:** $\operatorname{vol}(L)\cdot\operatorname{vol}(L^\perp) = 1$ for every lattice $L = p^k\mathbb{Z}_p$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem haarP_selfDual (k : ℤ) :
    (haarP p).real (latticeP p k) * (haarP p).real (annihP p (latticeP p k)) = 1 := by
  rw [annihP_latticeP, coe_latticeP, coe_latticeP, haarP_real_closedBall, haarP_real_closedBall,
    ← zpow_add₀ p_pos.ne', neg_neg, neg_add_cancel, zpow_zero]

variable (p) in
/-- **The Fourier transform on $\mathbb{Q}_p$** with respect to $\psi_p$ and the self-dual measure $dx$ (`haarP`):
$$\hat f(y) = \int_{\mathbb{Q}_p} f(x)\,\psi_p(xy)\,dx.$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
def fourierP (f : ℚ_[p] → ℂ) (y : ℚ_[p]) : ℂ := ∫ x, f x * (psiP (x * y) : ℂ) ∂haarP p

variable (p) in
/-- The inverse Fourier transform $\check g(x) = \int g(y)\,\psi_p(-xy)\,dy = \hat g(-x)$. -/
def fourierInvP (g : ℚ_[p] → ℂ) (x : ℚ_[p]) : ℂ := ∫ y, g y * (psiP (-(x * y)) : ℂ) ∂haarP p

/-- The character $x \mapsto \psi_p(xy)$. -/
def psiPMul (y : ℚ_[p]) : AddChar ℚ_[p] Circle :=
  (psiP (p := p)).compAddMonoidHom (AddMonoidHom.mulRight y)

@[simp] lemma psiPMul_apply (y x : ℚ_[p]) : psiPMul y x = psiP (x * y) := rfl

variable (p) in
/-- The indicator function $\mathbf 1_{c + p^k\mathbb{Z}_p}$ of the ball $\{x : \|x - c\|_p \le p^{-k}\}$. -/
def ballInd (c : ℚ_[p]) (k : ℤ) : ℚ_[p] → ℂ :=
  (closedBall c ((p : ℝ) ^ (-k))).indicator fun _ => 1

/-- **Fourier transform of a lattice coset:**
$$\widehat{\mathbf 1_{c + p^k\mathbb{Z}_p}}(y) = \operatorname{vol}(p^k\mathbb{Z}_p)\,\psi_p(cy)\,\mathbf 1_{p^{-k}\mathbb{Z}_p}(y)
  = p^{-k}\,\psi_p(cy)\,\mathbf 1_{(p^k\mathbb{Z}_p)^\perp}(y).$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem fourierP_ballInd (c : ℚ_[p]) (k : ℤ) (y : ℚ_[p]) :
    fourierP p (ballInd p c k) y =
      if ‖y‖ ≤ (p : ℝ) ^ k then ((p : ℝ) ^ (-k) : ℂ) * (psiP (c * y) : ℂ) else 0 := by
  unfold fourierP
  rw [← integral_add_right_eq_self _ c]
  have hfun : (fun x => ballInd p c k (x + c) * (psiP ((x + c) * y) : ℂ)) =
      fun x => (psiP (c * y) : ℂ) * (latticeP p k : Set ℚ_[p]).indicator
        (fun x => (psiPMul y x : ℂ)) x := by
    ext x
    by_cases hx : x ∈ (latticeP p k : Set ℚ_[p])
    · have hx' : x + c ∈ closedBall c ((p : ℝ) ^ (-k)) := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
        exact mem_latticeP.mp hx
      rw [ballInd, Set.indicator_of_mem hx', Set.indicator_of_mem hx, one_mul, psiPMul_apply,
        ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    · have hx' : x + c ∉ closedBall c ((p : ℝ) ^ (-k)) := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
        exact fun h => hx (mem_latticeP.mpr h)
      rw [ballInd, Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, zero_mul, mul_zero]
  have hmeas : MeasurableSet (latticeP p k : Set ℚ_[p]) := measurableSet_closedBall
  rw [hfun, integral_const_mul, integral_indicator hmeas,
    setIntegral_addChar_addSubgroup _ _ hmeas]
  have hiff : (∀ x ∈ latticeP p k, psiPMul y x = 1) ↔ ‖y‖ ≤ (p : ℝ) ^ k := by
    have := Set.ext_iff.mp (annihP_latticeP (p := p) k) y
    simp only [annihP, SetLike.mem_coe, mem_latticeP, neg_neg] at this
    simp only [psiPMul_apply, mem_latticeP]
    simpa using this
  simp only [hiff]
  split_ifs
  · rw [coe_latticeP, haarP_real_closedBall]; push_cast; ring
  · simp

/-- **Fourier inversion for lattice cosets:** $\check{\hat f} = f$ for $f = \mathbf 1_{c + p^k\mathbb{Z}_p}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Thm. 2.2.2 [unverified]"]
theorem fourierInvP_fourierP_ballInd (c : ℚ_[p]) (k : ℤ) :
    fourierInvP p (fourierP p (ballInd p c k)) = ballInd p c k := by
  ext x
  unfold fourierInvP
  have hfun : (fun y => fourierP p (ballInd p c k) y * (psiP (-(x * y)) : ℂ)) =
      fun y => ((p : ℝ) ^ (-k) : ℂ) * (ballInd p 0 (-k) y * (psiP (y * (c - x)) : ℂ)) := by
    ext y
    rw [fourierP_ballInd]
    by_cases hy : ‖y‖ ≤ (p : ℝ) ^ k
    · have hy' : y ∈ closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(-k))) := by simpa using hy
      simp only [hy, ↓reduceIte]
      rw [ballInd, Set.indicator_of_mem hy', one_mul, mul_assoc]
      congr 1
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    · have hy' : y ∉ closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(-k))) := by simpa using hy
      simp only [hy, ↓reduceIte]
      rw [ballInd, Set.indicator_of_notMem hy']
      simp
  rw [hfun, integral_const_mul]
  have h2 := fourierP_ballInd (p := p) 0 (-k) (c - x)
  unfold fourierP at h2
  rw [h2, neg_neg, zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  unfold ballInd
  by_cases hx : ‖c - x‖ ≤ (p : ℝ) ^ (-k)
  · have hx' : x ∈ closedBall c ((p : ℝ) ^ (-k)) := by rwa [mem_closedBall, dist_comm, dist_eq_norm]
    simp only [hx, ↓reduceIte]
    rw [Set.indicator_of_mem hx']
    have hp0 : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast p_pos.ne'
    rw [← zpow_add₀ hp0, neg_add_cancel, zpow_zero]
  · have hx' : x ∉ closedBall c ((p : ℝ) ^ (-k)) := by rwa [mem_closedBall, dist_comm, dist_eq_norm]
    simp only [hx, ↓reduceIte]
    rw [Set.indicator_of_notMem hx', mul_zero]

end FourierQp

/-! ## Schwartz–Bruhat functions on $\mathbb{Q}_p$ and Fourier inversion -/

section SchwartzBruhat

variable {p : ℕ} [hp : Fact p.Prime]

lemma continuous_psiP_comp {X : Type*} [TopologicalSpace X] {g : X → ℚ_[p]} (hg : Continuous g) :
    Continuous fun x => (psiP (g x) : ℂ) :=
  continuous_subtype_val.comp (continuous_psiP.comp hg)

/-- $\mathbf 1_{c + p^k\mathbb{Z}_p}\cdot g$ is integrable for continuous $g$ (the ball is compact). -/
lemma integrable_ballInd_mul (c : ℚ_[p]) (k : ℤ) {g : ℚ_[p] → ℂ} (hg : Continuous g) :
    Integrable (fun x => ballInd p c k x * g x) (haarP p) := by
  have h := (hg.continuousOn.integrableOn_compact (μ := haarP p) (isCompact_closedBall c ((p : ℝ) ^ (-k)))).integrable_indicator
    measurableSet_closedBall
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ closedBall c ((p : ℝ) ^ (-k))
  · show _ = ballInd p c k x * g x
    rw [ballInd, Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
  · show _ = ballInd p c k x * g x
    rw [ballInd, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

/-- `fourierP_ballInd` as an identity of functions: $\widehat{\mathbf 1_{c+p^k\mathbb{Z}_p}} =
\mathbf 1_{p^{-k}\mathbb{Z}_p}\cdot p^{-k}\psi_p(c\,\cdot)$. -/
lemma fourierP_ballInd_eq (c : ℚ_[p]) (k : ℤ) :
    fourierP p (ballInd p c k) =
      fun y => ballInd p 0 (-k) y * (((p : ℝ) ^ (-k) : ℂ) * (psiP (c * y) : ℂ)) := by
  ext y
  rw [fourierP_ballInd]
  by_cases hy : ‖y‖ ≤ (p : ℝ) ^ k
  · have hy' : y ∈ closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(-k))) := by simpa using hy
    simp only [hy, ↓reduceIte]
    rw [ballInd, Set.indicator_of_mem hy', one_mul]
  · have hy' : y ∉ closedBall (0 : ℚ_[p]) ((p : ℝ) ^ (-(-k))) := by simpa using hy
    simp only [hy, ↓reduceIte]
    rw [ballInd, Set.indicator_of_notMem hy', zero_mul]

variable (p) in
/-- **Schwartz–Bruhat functions on $\mathbb{Q}_p$:** the finite linear combinations
$f = \sum_{i<n} a_i\,\mathbf 1_{c_i + p^{k_i}\mathbb{Z}_p}$ of indicators of lattice cosets ($a_i \in \mathbb{C}$, $c_i \in \mathbb{Q}_p$,
$k_i \in \mathbb{Z}$). These are exactly the locally constant compactly supported functions (that converse is not
proved here). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 (the class of functions for local Fourier analysis) [unverified]"]
def IsSchwartzBruhatP (f : ℚ_[p] → ℂ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → ℂ) (c : Fin n → ℚ_[p]) (k : Fin n → ℤ),
    f = fun x => ∑ i, a i * ballInd p (c i) (k i) x

/-- The Fourier transform of a Schwartz–Bruhat function, term by term. -/
lemma fourierP_sum {n : ℕ} (a : Fin n → ℂ) (c : Fin n → ℚ_[p]) (k : Fin n → ℤ) :
    fourierP p (fun x => ∑ i, a i * ballInd p (c i) (k i) x) =
      fun y => ∑ i, a i * fourierP p (ballInd p (c i) (k i)) y := by
  ext y
  unfold fourierP
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro i _
    exact (integrable_ballInd_mul (c i) (k i)
      (continuous_psiP_comp (continuous_id.mul continuous_const))).const_mul (a i)

/-- **Fourier inversion for Schwartz–Bruhat functions on $\mathbb{Q}_p$:** with the self-dual measure,
$$f(x) = \int_{\mathbb{Q}_p} \hat f(y)\,\psi_p(-xy)\,dy, \qquad \hat f(y) = \int_{\mathbb{Q}_p} f(x)\,\psi_p(xy)\,dx.$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Thm. 2.2.2 (Fourier inversion, self-dual measure) [unverified]"]
theorem fourierInvP_fourierP_of_isSchwartzBruhat {f : ℚ_[p] → ℂ} (hf : IsSchwartzBruhatP p f) :
    fourierInvP p (fourierP p f) = f := by
  obtain ⟨n, a, c, k, rfl⟩ := hf
  rw [fourierP_sum]
  ext x
  unfold fourierInvP
  simp_rw [Finset.sum_mul, mul_assoc]
  have hint : ∀ i, Integrable (fun y => a i * (fourierP p (ballInd p (c i) (k i)) y *
      (psiP (-(x * y)) : ℂ))) (haarP p) := by
    intro i
    refine Integrable.const_mul ?_ _
    rw [fourierP_ballInd_eq]
    simp_rw [mul_assoc]
    exact integrable_ballInd_mul 0 (-k i) (continuous_const.mul
      ((continuous_psiP_comp (continuous_const.mul continuous_id)).mul
        (continuous_psiP_comp (continuous_const.mul continuous_id).neg)))
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  have := congrFun (fourierInvP_fourierP_ballInd (p := p) (c i) (k i)) x
  unfold fourierInvP at this
  rw [this]

end SchwartzBruhat

/-! ## The real place -/

section RealPlace

open Complex in
/-- **The standard character at a real place:** $\psi_\infty(x) = e(x) = e^{2\pi i x}$ on $\mathbb{R}$ (Mathlib's
`Real.fourierChar`). With Tate's sign convention $\psi_p(x) = e(-\{x\}_p)$ at the finite places, the product
$\psi_\infty(r)\prod_p\psi_p(r)$ is $1$ for $r \in \mathbb{Q}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, the character at $\\mathbb{R}$ [unverified]"]
def psiR : AddChar ℝ Circle := Real.fourierChar

lemma psiR_apply (x : ℝ) : psiR x = 𝐞 x := rfl

theorem continuous_psiR : Continuous psiR := Real.continuous_fourierChar

/-- **The Fourier transform at a real place:** $\hat f(y) = \int_{\mathbb{R}} f(x)\,\psi_\infty(xy)\,dx$, with Lebesgue
measure (which is self-dual for $\psi_\infty$, `fourierInvR_fourierR`). It is Mathlib's inverse transform
`𝓕⁻ f` (kernel $e(+xy)$), see `fourierR_eq`. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
def fourierR (f : ℝ → ℂ) (y : ℝ) : ℂ := ∫ x, f x * (psiR (x * y) : ℂ)

/-- The inverse transform $\check g(x) = \int_{\mathbb{R}} g(y)\,\psi_\infty(-xy)\,dy$ (Mathlib's `𝓕 g`). -/
def fourierInvR (g : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y, g y * (psiR (-(x * y)) : ℂ)

lemma fourierR_eq (f : ℝ → ℂ) : fourierR f = 𝓕⁻ f := by
  ext y
  rw [Real.fourierInv_eq, fourierR]
  congr 1
  ext x
  rw [Circle.smul_def, smul_eq_mul, mul_comm, psiR_apply, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

lemma fourierInvR_eq (g : ℝ → ℂ) : fourierInvR g = 𝓕 g := by
  ext x
  rw [Real.fourier_real_eq, fourierInvR]
  congr 1
  ext y
  rw [Circle.smul_def, smul_eq_mul, mul_comm, psiR_apply, mul_comm x y]

/-- **Fourier inversion at a real place** (Lebesgue measure is self-dual for $\psi_\infty$): for $f$ continuous and
integrable with $\hat f$ integrable, $\int \hat f(y)\psi_\infty(-xy)\,dy = f(x)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem fourierInvR_fourierR {f : ℝ → ℂ} (h : Continuous f) (hf : Integrable f)
    (hf' : Integrable (fourierR f)) : fourierInvR (fourierR f) = f := by
  rw [fourierR_eq, fourierInvR_eq]
  rw [fourierR_eq, Real.fourierInv_eq_fourier_comp_neg] at hf'
  refine h.fourier_fourierInv_eq hf ?_
  -- integrability of `𝓕 f` from that of `x ↦ 𝓕 f (-x)`... rewrite back
  have : 𝓕 f = fun x => 𝓕 (fun z => f (-z)) (-x) := by
    ext x
    rw [← Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_comp_neg]
    simp
  rw [this]
  exact hf'.comp_neg

/-- **Fourier transform of a complex Gaussian at a real place** (via `gaussianSchwartz` and Mathlib's
`fourier_gaussian_innerProductSpace`): for $\operatorname{Re} b > 0$,
$$\int_{\mathbb{R}} e^{-b x^2}\,e(xy)\,dx = (\pi/b)^{1/2}\,e^{-\pi^2 y^2/b}$$
(principal branch of the power). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, Gaussian at $\\mathbb{R}$ [unverified]"]
theorem fourierR_gaussianSchwartz (b : ℂ) (hb : 0 < b.re) (y : ℝ) :
    fourierR (gaussianSchwartz (E := ℝ) b hb) y =
      (π / b) ^ (1 / 2 : ℂ) * Complex.exp (-π ^ 2 * (y : ℂ) ^ 2 / b) := by
  rw [fourierR_eq, Real.fourierInv_eq_fourier_neg]
  have h := fourier_gaussian_innerProductSpace (V := ℝ) hb (-y)
  have hg : (gaussianSchwartz (E := ℝ) b hb : ℝ → ℂ) = fun v : ℝ => Complex.exp (-b * ((‖v‖ : ℂ)) ^ 2) := by
    ext v; rw [gaussianSchwartz_apply]; push_cast; rfl
  rw [hg, h]
  simp only [Module.finrank_self, Nat.cast_one, norm_neg, Real.norm_eq_abs]
  congr 3
  have : ((|y| : ℝ) : ℂ) ^ 2 = (y : ℂ) ^ 2 := by rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  rw [this]

/-- **The Gaussian $e^{-\pi x^2}$ is self-dual at a real place:** $\int_{\mathbb{R}} e^{-\pi x^2} e(xy)\,dx = e^{-\pi y^2}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem fourierR_gaussian_pi (y : ℝ) :
    fourierR (gaussianSchwartz (E := ℝ) (π : ℂ) (by simp [Real.pi_pos])) y =
      Complex.exp (-π * (y : ℂ) ^ 2) := by
  rw [fourierR_gaussianSchwartz]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [div_self hπ, Complex.one_cpow, one_mul]
  congr 1
  field_simp

end RealPlace

end

end QuadFormsKB.Analysis
