/-
# The reduced norm: local surjectivity and Eichler's norm theorem

For a quaternion algebra $D = (a,b)_F$ over a number field $F$ (`Tamagawa/Quaternion.lean`):

* **Split places.** If $(a,b)_K = 1$ then $\operatorname{nrd} \colon D_K^\times \to K^\times$ is surjective, over every
  field $K$ with $2 \ne 0$ (`Quat.exists_nrd_eq_of_hilbertSymbol_eq_one`): an isotropic nondegenerate form is
  universal.
* **Non-archimedean places.** $\operatorname{nrd}(D_v^\times) = F_v^\times$ at every finite place $v$, split or
  ramified (`Quat.exists_nrd_eq_finite`), given the named input `Quat.LocalRankFiveIsotropic F` (every
  nondegenerate form of rank $5$ over a non-archimedean completion $F_v$ is isotropic; O'Meara 63:19, Serre IV §2.2
  Thm. 6 for $\mathbb{Q}_p$, where it is proved in this repo: `RankFive.isotropic_padic_diag_odd`,
  `RankFive.isotropic_two_adic_diag`).
* **Eichler's norm theorem** (`Quat.eichler_norm_theorem`): if $D$ is totally definite over the totally real
  field $F$, then
  $$\operatorname{nrd}(D^\times) = F^\times_{+} = \{c \in F^\times : c \text{ is positive at every real place}\}.$$
  *Proof.* $\supseteq$: a totally positive $c$ is a square at each infinite place, and is a reduced norm at each
  finite place (input above); so the quaternary norm form $\langle 1,-a,-b,ab\rangle$ represents $c$ everywhere
  locally, hence over $F$ by Hasse–Minkowski over $F$ (`represents_iff_everywhere_nf`, proved in this repo).
  $\subseteq$: at a real place $\sigma(a), \sigma(b) < 0$ make $\sigma \circ \operatorname{nrd}$ positive definite.
  The general form (`Quat.exists_nrd_eq_of_totallyPositive`) needs no definiteness: every totally positive $c$ is
  a reduced norm from any $D$.

Weil uses Eichler's norm theorem in the proofs of Lemmas 3.3.2 and 3.6.1 (Weil 1982, §3.8, p. 65).

Sources: Eichler (1938), *Über die Idealklassenzahl total definiter Quaternionenalgebren*; Vignéras 1980, Ch. III,
Thm. 4.1 [unverified]; Voight 2021, Thm. 14.7.4 and Cor. 14.7.? [unverified]; Weil 1982, §3.8.
-/
import QuadFormsKB.Tamagawa.Quaternion

open Quaternion NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.Quat

/-! ### Isotropic norm forms are universal -/

section Field

variable {K : Type*} [Field K] {a b : K}

/-- The polar form of $\operatorname{nrd}$: $\operatorname{nrd}(x + y) - \operatorname{nrd}(x) - \operatorname{nrd}(y)
= 2(x_0y_0 - a x_1y_1 - b x_2y_2 + ab\,x_3y_3)$. -/
def nrdPolar (x y : ℍ[K,a,b]) : K :=
  2 * (x.re * y.re - a * x.imI * y.imI - b * x.imJ * y.imJ + a * b * x.imK * y.imK)

theorem nrd_smul_add (t : K) (x y : ℍ[K,a,b]) :
    nrd (t • x + y) = t ^ 2 * nrd x + t * nrdPolar x y + nrd y := by
  simp [nrd, nrdPolar]; ring

/-- **Isotropic $\Rightarrow$ universal:** if $\operatorname{nrd}(x) = 0$ for some $x \ne 0$ in $(a,b)_K$ ($a, b \ne 0$,
$2 \ne 0$), then every $c \in K$ is a reduced norm. -/
theorem exists_nrd_eq_of_isotropic (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) {x : ℍ[K,a,b]}
    (hx : x ≠ 0) (hx0 : nrd x = 0) (c : K) : ∃ y : ℍ[K,a,b], nrd y = c := by
  -- some basis vector `e` has `nrdPolar x e ≠ 0`
  obtain ⟨e, he⟩ : ∃ e : ℍ[K,a,b], nrdPolar x e ≠ 0 := by
    by_cases h0 : x.re = 0
    · by_cases h1 : x.imI = 0
      · by_cases h2' : x.imJ = 0
        · have h3 : x.imK ≠ 0 := by
            intro h3; exact hx (by ext <;> simp [h0, h1, h2', h3])
          exact ⟨⟨0, 0, 0, 1⟩, by simp [nrdPolar, h2, ha, hb, h3]⟩
        · exact ⟨⟨0, 0, 1, 0⟩, by simp [nrdPolar, h2, hb, h2']⟩
      · exact ⟨⟨0, 1, 0, 0⟩, by simp [nrdPolar, h2, ha, h1]⟩
    · exact ⟨⟨1, 0, 0, 0⟩, by simp [nrdPolar, h2, h0]⟩
  refine ⟨((c - nrd e) / nrdPolar x e) • x + e, ?_⟩
  rw [nrd_smul_add, hx0, mul_zero, zero_add, div_mul_cancel₀ _ he]
  ring

/-- **The reduced norm is surjective at a split place:** if $(a,b)_K = 1$ ($a, b \in K^\times$, $2 \ne 0$), then every
$c \in K$ is $\operatorname{nrd}(y)$ for some $y \in (a,b)_K$ (a unit when $c \ne 0$). Equivalently
$\operatorname{nrd}(M_2(K)^\times) = \det(GL_2(K)) = K^\times$.

Source: Voight 2021, §13.4 / Lemma 13.4.? [unverified]. -/
@[kb "voight2021" "§13.4 [unverified]"]
theorem exists_nrd_eq_of_hilbertSymbol_eq_one (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : hilbertSymbol K a b = 1) (c : K) : ∃ y : ℍ[K,a,b], nrd y = c := by
  obtain ⟨x, hx, hx0⟩ := (hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha hb).1 h
  exact exists_nrd_eq_of_isotropic h2 ha hb hx hx0 c

/-- Values of $\langle 1,-a,-b,ab\rangle$ over $K$ itself are reduced norms in $(a,b)_K$. -/
theorem eval_nrdForm (v : Fin 4 → K) :
    (nrdForm a b).eval v = nrd (⟨v 0, v 1, v 2, v 3⟩ : ℍ[K,a,b]) := by
  rw [QuadForm.eval, nrdForm, QuadForm.evalIn_diag, Fin.sum_univ_four, nrd_mk]
  simp; ring

/-- $\langle 1,-a,-b,ab\rangle$ represents $c$ over $K$ iff $c$ is a reduced norm from $(a,b)_K$. -/
theorem representsIn_nrdForm_iff (c : K) :
    (nrdForm a b).RepresentsIn K c ↔ ∃ y : ℍ[K,a,b], nrd y = c := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨⟨v 0, v 1, v 2, v 3⟩, by rw [← eval_nrdForm]; simpa using hv⟩
  · rintro ⟨y, hy⟩
    refine ⟨![y.re, y.imI, y.imJ, y.imK], ?_⟩
    change (nrdForm a b).eval _ = _
    rw [eval_nrdForm]
    simpa using hy

end Field

/-! ### Number fields -/

section NumberField

variable {F : Type} [Field F] [NumberField F]

/-- **Input: forms of rank $5$ over a non-archimedean completion are isotropic.** For every finite place $v$ of the
number field $F$ (a nonzero prime $\mathfrak{p}$ of $\mathcal{O}_F$) and every nondegenerate quadratic form $Q$ in
$5$ variables with coefficients in the completion $F_v$, $Q$ has a nontrivial zero in $F_v^5$.

This is the local theorem behind the surjectivity of the reduced norm at ramified places (field `isotropic`). It
is a standard result about local fields (O'Meara 63:19; Serre 1973, Ch. IV, §2.2, Thm. 6 for $\mathbb{Q}_p$; Lam
2005, Ch. VI, Thm. 2.12), assumed here, not proved, for general $F$. For $F = \mathbb{Q}$ it is proved in this repo
for diagonal forms with rational coefficients (`RankFive.isotropic_padic_diag_odd`,
`RankFive.isotropic_two_adic_diag`). It does not mention quaternion algebras, norms or Eichler's theorem. -/
@[kb "omeara1963" "63:19 [unverified]"]
structure LocalRankFiveIsotropic (F : Type) [Field F] [NumberField F] : Prop where
  isotropic : ∀ (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm (v.adicCompletion F) 5),
    Q.Nondegenerate → Q.IsotropicIn (v.adicCompletion F)

/-- **The reduced norm is surjective at every finite place** (given `LocalRankFiveIsotropic F`): for $a, b \in F^\times$,
a finite place $v$ and $c \in F_v^\times$, some $y \in D_v = (a,b)_{F_v}$ has $\operatorname{nrd}(y) = c$; so
$\operatorname{nrd}(D_v^\times) = F_v^\times$ whether $D_v$ is split or ramified.

*Proof.* $\langle 1,-a,-b,ab\rangle \perp \langle -c \rangle$ is nondegenerate of rank $5$, hence isotropic over $F_v$;
so $\langle 1,-a,-b,ab\rangle$ represents $c$ (`QuadForm.representsIn_iff_isotropicIn_orthSum`).

Source: Voight 2021, Lemma 13.4.? and Thm. 13.3.? [unverified]; Vignéras 1980, Ch. II, Thm. 1.? [unverified]. -/
@[kb "voight2021" "§13.4 [unverified]"]
theorem exists_nrd_eq_finite (I : LocalRankFiveIsotropic F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) {c : v.adicCompletion F} (hc : c ≠ 0) :
    ∃ y : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b], nrd y = c := by
  have h2 : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero_of_algebra (F := F) _
  have ha' : algebraMap F (v.adicCompletion F) a ≠ 0 := (map_ne_zero _).2 ha
  have hb' : algebraMap F (v.adicCompletion F) b ≠ 0 := (map_ne_zero _).2 hb
  have hQ := nrdForm_nondegenerate h2 ha' hb'
  have hc' : ∀ i, (![-c] : Fin 1 → v.adicCompletion F) i ≠ 0 := fun i => by
    rw [Subsingleton.elim i 0]; simpa using hc
  have h5 := I.isotropic v _ (QuadForm.nondegenerate_orthSum hQ (nondegenerate_diag_of_two h2 hc'))
  exact (representsIn_nrdForm_iff c).1
    ((QuadForm.representsIn_iff_isotropicIn_orthSum (v.adicCompletion F) hQ c).2 h5)

/-- **Totally positive:** $c \in F$ is positive under every real embedding $\sigma_w \colon F \to \mathbb{R}$
(`InfinitePlace.embedding_of_isReal`). (No condition at complex places.) -/
def IsTotallyPositive (c : F) : Prop :=
  ∀ (w : InfinitePlace F) (hw : w.IsReal), 0 < InfinitePlace.embedding_of_isReal hw c

/-- **$(a,b)_F$ is totally definite:** $F$ is totally real and $a, b$ are negative at every real place, i.e.
$D \otimes_{F,\sigma} \mathbb{R} \cong \mathbb{H}$ (Hamilton's quaternions) for every embedding $\sigma$
(equivalently $D$ is ramified at every infinite place). -/
def IsTotallyDefinite (a b : F) : Prop :=
  NumberField.IsTotallyReal F ∧ ∀ (w : InfinitePlace F) (hw : w.IsReal),
    InfinitePlace.embedding_of_isReal hw a < 0 ∧ InfinitePlace.embedding_of_isReal hw b < 0

omit [NumberField F] in
/-- At an infinite place a totally positive $c$ is a square in the completion $F_w$. -/
theorem isSquare_infinite_of_totallyPositive {c : F} (hc : IsTotallyPositive c) (w : InfinitePlace F) :
    ∃ s : w.Completion, s ^ 2 = algebraMap F w.Completion c := by
  rcases w.isReal_or_isComplex with hw | hw
  · set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have he : e (algebraMap F w.Completion c) = InfinitePlace.embedding_of_isReal hw c := by
      rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.algebraMap_apply]
      exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw _
    refine ⟨e.symm (Real.sqrt (InfinitePlace.embedding_of_isReal hw c)), ?_⟩
    apply e.injective
    rw [map_pow, RingEquiv.apply_symm_apply, Real.sq_sqrt (hc w hw).le, he]
  · set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e (algebraMap F w.Completion c)) (n := 2) (by norm_num)
    refine ⟨e.symm s, ?_⟩
    apply e.injective
    rw [map_pow, RingEquiv.apply_symm_apply, hs]

/-- **Every totally positive element is a reduced norm** (given `LocalRankFiveIsotropic F`): for any quaternion
algebra $D = (a,b)_F$ ($a, b \in F^\times$) and any totally positive $c \in F^\times$, $c = \operatorname{nrd}(\alpha)$
for some $\alpha \in D^\times$.

*Proof.* Hasse–Minkowski over $F$ for $\langle 1,-a,-b,ab\rangle$ (`represents_iff_everywhere_nf`): at infinite places
$c$ is a square (`isSquare_infinite_of_totallyPositive`), at finite places use `exists_nrd_eq_finite`.

Source: Vignéras 1980, Ch. III, Thm. 4.1 [unverified]; Voight 2021, Thm. 14.7.4 [unverified]. -/
@[kb "voight2021" "Thm. 14.7.4 [unverified]"]
theorem exists_nrd_eq_of_totallyPositive (I : LocalRankFiveIsotropic F) {a b : F} (ha : a ≠ 0)
    (hb : b ≠ 0) {c : F} (hc : c ≠ 0) (hpos : IsTotallyPositive c) :
    ∃ α : ℍ[F,a,b], IsUnit α ∧ nrd α = c := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hQ := nrdForm_nondegenerate h2 ha hb
  have hrep : (nrdForm a b).RepresentsIn F c := by
    rw [represents_iff_everywhere_nf _ hQ c hc]
    intro v
    cases v with
    | infinite w =>
      obtain ⟨s, hs⟩ := isSquare_infinite_of_totallyPositive hpos w
      refine ⟨![s, 0, 0, 0], ?_⟩
      rw [evalIn_nrdForm, nrd_mk]
      simpa using hs
    | finite v =>
      obtain ⟨y, hy⟩ := exists_nrd_eq_finite I ha hb v
        ((map_ne_zero (algebraMap F (v.adicCompletion F))).2 hc)
      refine ⟨![y.re, y.imI, y.imJ, y.imK], ?_⟩
      rw [evalIn_nrdForm, ← hy]
      rfl
  obtain ⟨α, hα⟩ := (representsIn_nrdForm_iff c).1 hrep
  exact ⟨α, (isUnit_iff_nrd_ne_zero α).2 (hα ▸ hc), hα⟩

/-- **In a totally definite algebra, reduced norms of nonzero elements are totally positive:** if $a, b$ are negative
at the real place $w$, then $\sigma_w(\operatorname{nrd}(\alpha)) = \sigma(x_0)^2 + |\sigma(a)|\sigma(x_1)^2 + |\sigma(b)|\sigma(x_2)^2
+ \sigma(a)\sigma(b)\sigma(x_3)^2 > 0$ for $\alpha \ne 0$. -/
theorem isTotallyPositive_nrd {a b : F} (hD : IsTotallyDefinite a b) {α : ℍ[F,a,b]} (hα : α ≠ 0) :
    IsTotallyPositive (nrd α) := by
  intro w hw
  set σ := InfinitePlace.embedding_of_isReal hw
  obtain ⟨hσa, hσb⟩ := hD.2 w hw
  have hσ : σ (nrd α) = σ α.re ^ 2 + (-σ a) * σ α.imI ^ 2 + (-σ b) * σ α.imJ ^ 2 +
      (σ a * σ b) * σ α.imK ^ 2 := by
    simp only [nrd, map_add, map_sub, map_mul, map_pow]; ring
  rw [hσ]
  have h1 : 0 < -σ a := neg_pos.2 hσa
  have h2 : 0 < -σ b := neg_pos.2 hσb
  have h3 : 0 < σ a * σ b := mul_pos_of_neg_of_neg hσa hσb
  have t0 : 0 ≤ σ α.re ^ 2 := sq_nonneg _
  have t1 : 0 ≤ (-σ a) * σ α.imI ^ 2 := mul_nonneg h1.le (sq_nonneg _)
  have t2 : 0 ≤ (-σ b) * σ α.imJ ^ 2 := mul_nonneg h2.le (sq_nonneg _)
  have t3 : 0 ≤ (σ a * σ b) * σ α.imK ^ 2 := mul_nonneg h3.le (sq_nonneg _)
  by_contra hle
  push Not at hle
  have z0 : σ α.re ^ 2 = 0 := by linarith
  have z1 : (-σ a) * σ α.imI ^ 2 = 0 := by linarith
  have z2 : (-σ b) * σ α.imJ ^ 2 = 0 := by linarith
  have z3 : (σ a * σ b) * σ α.imK ^ 2 = 0 := by linarith
  have hz : ∀ t : F, σ t ^ 2 = 0 → t = 0 := fun t ht =>
    σ.injective (by rw [map_zero]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ht)
  apply hα
  ext
  · exact hz _ z0
  · exact hz _ ((mul_eq_zero.1 z1).resolve_left h1.ne')
  · exact hz _ ((mul_eq_zero.1 z2).resolve_left h2.ne')
  · exact hz _ ((mul_eq_zero.1 z3).resolve_left h3.ne')

/-- **Eichler's norm theorem** (totally definite case): if $F$ is totally real and $D = (a,b)_F$ is totally definite
($a, b$ negative at every real place), then (given `LocalRankFiveIsotropic F`)
$$\operatorname{nrd}(D^\times) = F^\times_{+},$$
i.e. $c \in F$ is the reduced norm of a unit of $D$ iff $c \ne 0$ and $c$ is totally positive.

Source: Eichler 1938; Vignéras 1980, Ch. III, Thm. 4.1 [unverified]; Voight 2021, Thm. 14.7.4 [unverified];
used by Weil 1982, §3.3 and §3.6 (Lemmas 3.3.2, 3.6.1), cf. §3.8, p. 65. -/
@[kb "voight2021" "Thm. 14.7.4 [unverified]"]
theorem eichler_norm_theorem (I : LocalRankFiveIsotropic F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hD : IsTotallyDefinite a b) (c : F) :
    (∃ α : ℍ[F,a,b], IsUnit α ∧ nrd α = c) ↔ c ≠ 0 ∧ IsTotallyPositive c := by
  constructor
  · rintro ⟨α, hu, rfl⟩
    exact ⟨(isUnit_iff_nrd_ne_zero α).1 hu, isTotallyPositive_nrd hD hu.ne_zero⟩
  · rintro ⟨hc, hpos⟩
    exact exists_nrd_eq_of_totallyPositive I ha hb hc hpos

end NumberField

end QuadFormsKB.Quat
