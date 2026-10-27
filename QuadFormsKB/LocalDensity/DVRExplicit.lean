/-
# Local densities over a DVR: local representability, stability, anisotropy, (5.6) and (5.7)

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$, residue field of size $q$; e.g. the
completion $\mathfrak{o}_\mathfrak{p}$ of a number field at **any** prime, including dyadic ones).
**Defines** the DVR analogues of `Explicit.lean`: Hanke 2004, Def. 5.1 (`DVR.localDensityOf`, p. 368),
Def. 3.5 (locally represented, p. 362; `DVR.IsLocallyRepresentedAt`), Def. 3.6 ($\mathfrak{p}$-stable, p. 362;
`DVR.IsPStable`); Def. 3.7 (anisotropic, p. 363) is `¬ Q.IsotropicIn K` for a fraction field $K$ of $R$.
**Proves** Lemma 3.8 *corrected* (p. 363; `DVR.anisotropic_iff_zeroType`, $R$ complete), Cor. 3.8.2 (p. 364;
`DVR.repEquiv_mul_pow_sq` over $R$, and `DVR.card_rep_mul_pow_sq` for a global ring $A \to R$), (5.6) and (5.7)
(p. 369; `DVR.localDensity_le_mul_sq`, `DVR.localDensity_pow_sq`). None of these needs $\pi \nmid 2$: Lemma 3.8 and
Cor. 3.8.2 hold for every complete $R$ with finite residue field, and (5.6), (5.7) need only $2 \ne 0$ (for
stabilization, `DVR.localDensity_eventually_eq`). The non-dyadic explicit values (Tables 1–2, (5.10)) are in
`DVRTable2.lean`. **Depends on** `DVRGeneral.lean`.
-/
import QuadFormsKB.LocalDensity.DVRGeneral

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **Local density of solutions of a given type** over $R$ (Hanke 2004, Def. 5.1, p. 368):
$\beta^{T}_\pi(m) = \lim_k r^{T}_{\pi^k}(m)/q^{k(n-1)}$ for a type predicate $T$ at each level $k$. Normalized as
`DVR.localDensity`. -/
noncomputable def localDensityOf (Q : QuadForm R n) (π : R) (m : R)
    (T : (k : ℕ) → (Fin n → R ⧸ Ideal.span {π ^ k}) → Prop) : ℝ :=
  Filter.limUnder Filter.atTop fun k : ℕ => (repCountOf Q π k m (T k) : ℝ) / (q R : ℝ) ^ (k * (n - 1))

/-- **Locally represented at $\pi$** (Hanke 2004, Def. 3.5, p. 362): $r_{\pi^k}(m) > 0$ for all large $k$. -/
def IsLocallyRepresentedAt (Q : QuadForm R n) (π : R) (m : R) : Prop :=
  ∀ᶠ k in Filter.atTop, 0 < repCount Q π k m

set_option linter.unusedVariables false in
/-- **$\pi$-stable** (Hanke 2004, Def. 3.6, p. 362), as in `LocalDensity.IsPStable`: $m$ is locally represented
at $\pi$, and for all large $k$ the number of non-Zero-type solutions
$r^{\mathrm{Good}}_{\pi^k}(\pi^{2\nu}m) + r^{\mathrm{Bad}}_{\pi^k}(\pi^{2\nu}m)$ is the same for every $\nu \ge 1$. (The
unimodular coordinates $S_0$ of a normal form do not enter: Good $\cup$ Bad = non-Zero.) -/
def IsPStable (Q : QuadForm R n) (S₀ : Finset (Fin n)) (π : R) (m : R) : Prop :=
  IsLocallyRepresentedAt Q π m ∧
    ∀ᶠ k in Filter.atTop, ∀ ν ≥ 1,
      repCountOf Q π k (π ^ (2 * ν) * m) (fun x => ¬ IsZeroType π k x) =
        repCountOf Q π k (π ^ 2 * m) (fun x => ¬ IsZeroType π k x)

/-! ### Counting basics -/

/-- **Zero / non-Zero split** over $R$: $r_{\pi^k}(m) = r^{\mathrm{Zero}}_{\pi^k}(m) + r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(m)$. -/
theorem repCount_eq_zero_add_nonZero [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n)
    (π : R) (hπ : Irreducible π) (k : ℕ) (m : R) :
    repCount Q π k m = repCountOf Q π k m (IsZeroType π k) +
      repCountOf Q π k m (fun x => ¬ IsZeroType π k x) := by
  have := finite_quot_pow π hπ k
  unfold repCount repCountOf
  exact natCard_split _ _ _ (IsZeroType π k) (fun _ => Iff.rfl) (fun _ => Iff.rfl)

/-- Solutions of a given type are among all solutions: $r^{T}_{\pi^k}(m) \le r_{\pi^k}(m)$. -/
theorem repCountOf_le_repCount [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n) (π : R)
    (hπ : Irreducible π) (k : ℕ) (m : R) (T : (Fin n → R ⧸ Ideal.span {π ^ k}) → Prop) :
    repCountOf Q π k m T ≤ repCount Q π k m := by
  have := finite_quot_pow π hπ k
  unfold repCountOf repCount
  exact Nat.card_le_card_of_injective (fun x => ⟨x.1, x.2.1⟩)
    (fun x y h => Subtype.ext (congrArg Subtype.val h :))

/-- **Homogeneity** over any $R$-algebra: $Q(c\vec{y}) = c^2 Q(\vec{y})$. -/
theorem evalIn_const_mul {A K : Type*} [CommRing A] [CommRing K] [Algebra A K] (Q : QuadForm A n) (c : K)
    (y : Fin n → K) : Q.evalIn K (fun j => c * y j) = c ^ 2 * Q.evalIn K y := by
  simp only [QuadForm.evalIn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Evaluation commutes with `algebraMap`: $Q(\iota\vec{x}) = \iota(Q(\vec{x}))$. -/
theorem evalIn_algebraMap (K : Type*) [CommRing K] [Algebra R K] (Q : QuadForm R n)
    (x : Fin n → R) :
    Q.evalIn K (fun i => algebraMap R K (x i)) = algebraMap R K (Q.eval x) := by
  simp only [QuadForm.evalIn, map_sum, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- $x \equiv y$ modulo $\mathfrak{m}^j$ (as `SModEq`) iff $\pi^j \mid x - y$. -/
theorem smodEq_maximalIdeal_pow_iff (π : R) (hπ : Irreducible π) (j : ℕ) (x y : R) :
    x ≡ y [SMOD ((IsLocalRing.maximalIdeal R) ^ j • ⊤ : Submodule R R)] ↔ π ^ j ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

/-! ### Anisotropy (Def. 3.7) and primitive solutions -/

/-- **An isotropic form has a primitive integral zero**: if $Q(\vec{x}) = 0$ for some $\vec{x} \ne 0$ in $K^n$
($K$ a fraction field of $R$), then $Q(\vec{z}) = 0$ for some $\vec{z} \in R^n$ with $\pi \nmid z_i$ for some $i$
(clear denominators, then divide by the largest power of $\pi$ dividing all coordinates). -/
theorem exists_primitive_of_isotropicIn (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (hiso : Q.IsotropicIn K) :
    ∃ z : Fin n → R, (∃ i, ¬ π ∣ z i) ∧ Q.eval z = 0 := by
  classical
  obtain ⟨x, hx0, hx⟩ := hiso
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) x
  choose y hy using hb
  have hinj := IsFractionRing.injective R K
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hbK : algebraMap R K (b : R) ≠ 0 := fun h => hb0 (hinj (h.trans (map_zero _).symm))
  have hy' : ∀ i, algebraMap R K (y i) = algebraMap R K (b : R) * x i := fun i => by
    rw [hy i, Algebra.smul_def]
  obtain ⟨i0, hi0⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    funext i
    have := hy' i
    rw [h i, map_zero, eq_comm, mul_eq_zero] at this
    exact this.resolve_left hbK
  have hQy : Q.eval y = 0 := by
    apply hinj
    rw [map_zero, ← evalIn_algebraMap, funext hy', evalIn_const_mul, hx, mul_zero]
  have hex : ∃ d, ¬ ∀ i, π ^ (d + 1) ∣ y i := by
    obtain ⟨e, -, he⟩ := exists_pow_dvd_not_dvd π hπ hi0
    exact ⟨e, fun h => he (h i0)⟩
  set d := Nat.find hex with hd
  have hdiv : ∀ i, π ^ d ∣ y i := by
    by_cases h0 : d = 0
    · intro i; rw [h0, pow_zero]; exact one_dvd _
    · have := Nat.find_min hex (show d - 1 < d by omega)
      rw [not_not, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)] at this
      exact this
  refine ⟨fun i => divPow π d (y i), ?_, ?_⟩
  · obtain ⟨i, hi⟩ := not_forall.mp (Nat.find_spec hex)
    refine ⟨i, fun ⟨c, hc⟩ => hi ⟨c, ?_⟩⟩
    simp only at hc
    rw [eq_mul_divPow (hdiv i), hc, pow_succ]; ring
  · have h1 := evalIn_mul_left Q (π ^ d) y (fun i => divPow π d (y i))
      (fun i => eq_mul_divPow (hdiv i))
    rw [show Q.evalIn R y = 0 from hQy, eq_comm, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero))

/-- **An isotropic form has a primitive solution of $Q \equiv 0 \pmod{\pi^k}$** for every $k \ge 1$. -/
theorem exists_primitive_zero_mod_of_isotropicIn (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (hiso : Q.IsotropicIn K)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ x : Fin n → R ⧸ Ideal.span {π ^ k}, Q.evalIn _ x = 0 ∧ ¬ IsZeroType π k x := by
  obtain ⟨z, ⟨i, hi⟩, hz⟩ := exists_primitive_of_isotropicIn K Q π hπ hiso
  refine ⟨redV π k z, by rw [evalIn_redV, hz, map_zero], fun h => hi ?_⟩
  exact (mk_pi_dvd_iff π k hk (z i)).1 (h i)

/-- **Compactness of $R^n$ for complete $R$ with finite residue field** (König's lemma): if for every $C$ some
primitive $\vec{z} \in R^n$ has $\pi^C \mid Q(\vec{z})$, then $Q$ is isotropic over the fraction field $K$. *Proof:*
choose, level by level, classes mod $\pi^k$ that lift to primitive solutions of $Q \equiv 0 \pmod{\pi^C}$ for
every $C$ (pigeonhole over the finitely many classes mod $\pi^{k+1}$ above a class mod $\pi^k$); their limit
$\vec{L} \in R^n$ (precompleteness) is primitive with $\pi^k \mid Q(\vec{L})$ for all $k$, so $Q(\vec{L}) = 0$. -/
theorem isotropicIn_of_primitive_pow_dvd [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (h : ∀ C : ℕ, ∃ z : Fin n → R, (∃ i, ¬ π ∣ z i) ∧ π ^ C ∣ Q.eval z) :
    Q.IsotropicIn K := by
  classical
  -- `G k x`: the class of `x` mod `π ^ k` lifts to primitive solutions mod `π ^ C` for every `C`
  let G : ℕ → (Fin n → R) → Prop := fun k x =>
    ∀ C, ∃ z : Fin n → R, (∃ i, ¬ π ∣ z i) ∧ π ^ C ∣ Q.eval z ∧ ∀ i, π ^ k ∣ z i - x i
  have hG0 : G 0 0 := fun C => by
    obtain ⟨z, hz, hC⟩ := h C
    exact ⟨z, hz, hC, fun i => by simp⟩
  have step : ∀ k (x : {x // G k x}), ∃ y : {y // G (k + 1) y}, ∀ i, π ^ k ∣ y.1 i - x.1 i := by
    rintro k ⟨x, hx⟩
    have := finite_quot_pow π hπ (k + 1)
    have : Fintype (Fin n → R ⧸ Ideal.span {π ^ (k + 1)}) := Fintype.ofFinite _
    by_contra hcon
    push Not at hcon
    have hbad : ∀ c : Fin n → R ⧸ Ideal.span {π ^ (k + 1)}, ∃ C : ℕ,
        (∀ i, π ^ k ∣ liftV π (k + 1) c i - x i) → ∀ z : Fin n → R, (∃ i, ¬ π ∣ z i) →
          π ^ C ∣ Q.eval z → ¬ ∀ i, π ^ (k + 1) ∣ z i - liftV π (k + 1) c i := by
      intro c
      by_cases hc : ∀ i, π ^ k ∣ liftV π (k + 1) c i - x i
      · have hnG : ¬ G (k + 1) (liftV π (k + 1) c) := fun hG => by
          obtain ⟨i, hi⟩ := hcon ⟨_, hG⟩
          exact hi (hc i)
        simp only [G, not_forall, not_exists, not_and] at hnG
        obtain ⟨C, hC⟩ := hnG
        exact ⟨C, fun _ z hz hCz hzc => (hC z hz hCz).elim fun i hi => hi (hzc i)⟩
      · exact ⟨0, fun h' => absurd h' hc⟩
    choose Cb hCb using hbad
    obtain ⟨z, hz, hM, hzx⟩ := hx (Finset.univ.sup Cb)
    set c := redV π (k + 1) z
    have hcz : ∀ i, π ^ (k + 1) ∣ z i - liftV π (k + 1) c i := by
      have := (redV_eq_iff π (k + 1) (liftV π (k + 1) c) z).1 (by rw [redV_liftV])
      intro i
      have h1 := this i
      rw [← dvd_neg, neg_sub] at h1
      exact h1
    refine hCb c ?_ z hz ((pow_dvd_pow π (Finset.le_sup (Finset.mem_univ c))).trans hM) hcz
    intro i
    have h1 : π ^ k ∣ z i - liftV π (k + 1) c i := (pow_dvd_pow π (by omega)).trans (hcz i)
    have h2 := (hzx i).sub h1
    rw [show z i - x i - (z i - liftV π (k + 1) c i) = liftV π (k + 1) c i - x i by ring] at h2
    exact h2
  choose g hg using step
  let f : (k : ℕ) → {x // G k x} := fun k =>
    Nat.rec (motive := fun k => {x // G k x}) ⟨0, hG0⟩ (fun k xk => g k xk) k
  have hf : ∀ k, f (k + 1) = g k (f k) := fun k => rfl
  -- the coordinates form Cauchy sequences
  have hcauchy : ∀ i, ∀ a b, a ≤ b → π ^ a ∣ (f b).1 i - (f a).1 i := by
    intro i a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      rw [hf]
      have h1 := hg b (f b) i
      have h2 := ((pow_dvd_pow π hab).trans h1).add ih
      rwa [sub_add_sub_cancel] at h2
  have hL : ∀ i, ∃ L : R, ∀ k, π ^ k ∣ (f k).1 i - L := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal R) (fun k => (f k).1 i)
      (fun {a b} hab => by
        rw [smodEq_maximalIdeal_pow_iff π hπ, ← dvd_neg, neg_sub]
        exact hcauchy i a b hab)
    exact ⟨L, fun k => (smodEq_maximalIdeal_pow_iff π hπ k _ _).1 (hL k)⟩
  choose L hL using hL
  have hQL : Q.eval L = 0 := by
    by_contra hne
    obtain ⟨e, -, he⟩ := exists_pow_dvd_not_dvd π hπ hne
    apply he
    obtain ⟨z, -, hzC, hzx⟩ := (f (e + 1)).2 (e + 1)
    have h1 : redV π (e + 1) z = redV π (e + 1) L := by
      rw [redV_eq_iff]
      intro i
      have := (hzx i).add (hL i (e + 1))
      rwa [sub_add_sub_cancel] at this
    have h2 := congrArg (Q.evalIn (R ⧸ Ideal.span {π ^ (e + 1)})) h1
    rw [evalIn_redV, evalIn_redV, mk_eq_mk_iff] at h2
    have := hzC.sub h2
    rwa [sub_sub_cancel] at this
  obtain ⟨z, ⟨i, hi⟩, -, hzx⟩ := (f 1).2 0
  have hLi : ¬ π ∣ L i := by
    intro hd
    apply hi
    have h1 := (hzx i).add (hL i 1)
    rw [pow_one] at h1
    have := h1.add hd
    simpa using this
  refine ⟨fun j => algebraMap R K (L j), fun h0 => hLi ?_, ?_⟩
  · have : algebraMap R K (L i) = 0 := congrFun h0 i
    rw [IsFractionRing.injective R K (this.trans (map_zero _).symm)]
    exact dvd_zero _
  · rw [evalIn_algebraMap, hQL, map_zero]

/-- **Bounded valuation of primitive vectors** (Hanke 2004, p. 363, O'Meara 91:1) over a complete $R$ with
finite residue field: if $Q$ is anisotropic over $K$, there is $C$ such that for $k \ge C$ every solution of
$Q(\vec{x}) \equiv 0 \pmod{\pi^k}$ is of Zero type. -/
@[kb "omeara1963" "§91A, 91:1, p. 239 (the set {x : Q(x) ∈ 𝔞} is a lattice on an anisotropic space)"]
theorem exists_isZeroType_of_anisotropic [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (haniso : ¬ Q.IsotropicIn K) :
    ∃ C : ℕ, ∀ k ≥ C, ∀ x : Fin n → R ⧸ Ideal.span {π ^ k},
      Q.evalIn _ x = 0 → IsZeroType π k x := by
  by_contra hcon
  push Not at hcon
  apply haniso
  refine isotropicIn_of_primitive_pow_dvd K Q π hπ fun C => ?_
  obtain ⟨k, hk, x, hx, hxz⟩ := hcon (C + 1)
  refine ⟨liftV π k x, ?_, ?_⟩
  · unfold IsZeroType at hxz
    push Not at hxz
    obtain ⟨i, hi⟩ := hxz
    refine ⟨i, fun hd => hi ?_⟩
    have := (mk_pi_dvd_iff π k (by omega) (liftV π k x i)).2 hd
    rwa [show Ideal.Quotient.mk _ (liftV π k x i) = x i from congrFun (redV_liftV π k x) i] at this
  · have h1 := evalIn_redV Q π k (liftV π k x)
    rw [redV_liftV, hx, eq_comm, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
    exact (pow_dvd_pow π (by omega)).trans h1

/-! ### Lemma 3.8 (corrected) and Corollary 3.8.2 -/

/-- **No non-Zero-type solutions at $\pi^{2\nu}m$** ($\nu \ge 1$, $k \gg 1$) for $Q$ anisotropic, under the
constancy half of $\pi$-stability: the common count equals the count at $\pi^{2k}m \equiv 0 \pmod{\pi^k}$, which
vanishes beyond the valuation bound of `exists_isZeroType_of_anisotropic`. -/
theorem eventually_repCountOf_nonZero_eq_zero [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (haniso : ¬ Q.IsotropicIn K) (m : R)
    (hstab : ∀ᶠ k in Filter.atTop, ∀ ν ≥ 1,
      repCountOf Q π k (π ^ (2 * ν) * m) (fun x => ¬ IsZeroType π k x) =
        repCountOf Q π k (π ^ 2 * m) (fun x => ¬ IsZeroType π k x)) :
    ∀ᶠ k in Filter.atTop, ∀ ν ≥ 1,
      repCountOf Q π k (π ^ (2 * ν) * m) (fun x => ¬ IsZeroType π k x) = 0 := by
  obtain ⟨C, hC⟩ := exists_isZeroType_of_anisotropic K Q π hπ haniso
  filter_upwards [hstab, Filter.eventually_ge_atTop (max C 1)] with k hk hkC ν hν
  rw [hk ν hν, ← hk k (by omega)]
  rw [repCountOf, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨x, hx, hxz⟩ => hxz (hC k (by omega) x ?_)⟩
  rw [hx, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

/-- **Lemma 3.8, corrected** (Hanke 2004, p. 363; fix (b) of the erratum confirmed by the author, see
`LocalDensity.anisotropic_iff_zeroType`), over a complete DVR $R$ with finite
residue field and fraction field $K$ (e.g. $\mathfrak{o}_\mathfrak{p} \subset F_\mathfrak{p}$ at **any** prime
$\mathfrak{p}$, dyadic or not): for $m$ $\pi$-stable (Def. 3.6), $Q$ is anisotropic over $K$ iff for all large $k$
every solution of $Q(\vec{x}) \equiv \pi^2 m \pmod{\pi^k}$ is of Zero type.

*Erratum:* the paper states the conclusion for $m$ itself (with $\mathfrak{p} \mid m$), which is false (see the
$\mathbb{Q}$ version). *Update (candidate; pending author):* the paper's
nondegeneracy and the normal form are not needed; nor is
$\pi \nmid 2$. Completeness of $R$ is needed for ($\Rightarrow$) (over $\mathbb{Z}_{(5)}$, $x^2 + y^2$ is anisotropic
over $\mathbb{Q}$ but has primitive zeros mod every $5^k$); the paper's $\mathfrak{o}_\mathfrak{p}$ is complete.

*Proof* (pp. 363–364, applied at $\pi^2 m$). ($\Rightarrow$) primitive vectors have bounded valuation
(`exists_isZeroType_of_anisotropic`), and stability transports "no non-Zero solutions at $\pi^{2k}m$" to $\nu = 1$.
($\Leftarrow$) a primitive zero of $Q$ (`exists_primitive_of_isotropicIn`) is a non-Zero-type solution at
$\pi^{2k}m \equiv 0$, transported to $\pi^2 m$ by stability. -/
@[kb "hanke2004" "Lemma 3.8, p. 363 (corrected)"]
theorem anisotropic_iff_zeroType [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (S₀ : Finset (Fin n))
    (m : R) (hm : IsPStable Q S₀ π m) :
    ¬ Q.IsotropicIn K ↔
      ∀ᶠ k in Filter.atTop,
        repCount Q π k (π ^ 2 * m) = repCountOf Q π k (π ^ 2 * m) (IsZeroType π k) := by
  constructor
  · intro haniso
    filter_upwards [eventually_repCountOf_nonZero_eq_zero K Q π hπ haniso m hm.2] with k hk
    have := hk 1 le_rfl
    rw [mul_one] at this
    rw [repCount_eq_zero_add_nonZero Q π hπ, this, add_zero]
  · intro h hiso
    obtain ⟨k, hk, hks, hk1⟩ := (h.and (hm.2.and (Filter.eventually_ge_atTop 1))).exists
    obtain ⟨x, hx, hxz⟩ := exists_primitive_zero_mod_of_isotropicIn K Q π hπ hiso k hk1
    have hpos : 0 < repCountOf Q π k (π ^ (2 * k) * m) (fun x => ¬ IsZeroType π k x) := by
      have := finite_quot_pow π hπ k
      rw [repCountOf, Nat.card_pos_iff]
      refine ⟨⟨⟨x, ?_, hxz⟩⟩, inferInstance⟩
      rw [hx, eq_comm, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
    rw [hks k hk1] at hpos
    have := repCount_eq_zero_add_nonZero Q π hπ k (π ^ 2 * m)
    omega

/-- **Every solution of $Q(\vec{z}) = \pi^{2\nu}m$ in $R^n$ ($\nu \ge 1$) is divisible by $\pi$**, for $Q$ anisotropic
over $K$ and $m$ $\pi$-stable ($R$ complete, finite residue field): by Lemma 3.8 its reduction mod $\pi^k$ is
of Zero type for $k \gg 1$. -/
theorem dvd_of_eval_eq_pow_mul [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (S₀ : Finset (Fin n))
    (haniso : ¬ Q.IsotropicIn K) (m : R) (hm : IsPStable Q S₀ π m) (ν : ℕ) (hν : 1 ≤ ν)
    (z : Fin n → R) (hz : Q.eval z = π ^ (2 * ν) * m) (i : Fin n) : π ∣ z i := by
  obtain ⟨k, hk, hk1⟩ := ((eventually_repCountOf_nonZero_eq_zero K Q π hπ haniso m hm.2).and
    (Filter.eventually_ge_atTop 1)).exists
  have := finite_quot_pow π hπ k
  have hzt : IsZeroType π k (redV π k z) := by
    by_contra hzt
    have h0 := hk ν hν
    rw [repCountOf, Nat.card_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact h0.false ⟨_, by rw [evalIn_redV, hz], hzt⟩
    · exact absurd h0 (not_infinite_iff_finite.mpr inferInstance)
  exact (mk_pi_dvd_iff π k hk1 (z i)).1 (hzt i)

/-- Evaluation commutes with change of rings: $(\varphi Q)(\varphi\vec{x}) = \varphi(Q(\vec{x}))$. -/
theorem eval_map_apply {A : Type*} [CommRing A] (φ : A →+* R) (Q : QuadForm A n) (x : Fin n → A) :
    (Q.map φ).eval (fun i => φ (x i)) = φ (Q.eval x) := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, map_sum, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **Corollary 3.8.2** (Hanke 2004, p. 364), for a global ring: let $A$ be a domain (e.g. $\mathfrak{o}_F$) with
a ring map $\varphi : A \to R$ to the completion $R$ (complete DVR, finite residue field, fraction field
$K$), and $p \in A$ with $\varphi(p) = \pi$ generating the prime ($\pi \mid \varphi(a) \Rightarrow p \mid a$; the paper's
principal $\mathfrak{p} = (p)$). If $Q$ over $A$ is anisotropic at $\pi$ and $m \in A$ is $\pi$-stable, then
$r_Q(mp^{2\nu}) = r_Q(m)$ for all $\nu \ge 0$, where $r_Q(m) = \#\{\vec{x} \in A^n : Q(\vec{x}) = m\}$. *Proof:* by
`dvd_of_eval_eq_pow_mul` (*Update (candidate):* no nondegeneracy or normal form needed, see Lemma 3.8)
every representation of $mp^{2\nu}$, $\nu \ge 1$, is $p\vec{x}'$ with
$Q(\vec{x}') = mp^{2(\nu-1)}$; $\vec{x}' \mapsto p\vec{x}'$ is a bijection; induct. Valid at dyadic primes too. -/
@[kb "hanke2004" "Cor. 3.8.2, p. 364"]
theorem card_rep_mul_pow_sq [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] {A : Type*} [CommRing A] [IsDomain A] (φ : A →+* R)
    (Q : QuadForm A n) (p : A) (π : R) (hπ : Irreducible π)
    (hp : φ p = π) (hA : ∀ a : A, π ∣ φ a → p ∣ a) (S₀ : Finset (Fin n))
    (haniso : ¬ (Q.map φ).IsotropicIn K) (m : A) (hm : IsPStable (Q.map φ) S₀ π (φ m)) (e : ℕ) :
    Set.ncard {x : Fin n → A | Q.eval x = p ^ (2 * e) * m} =
      Set.ncard {x : Fin n → A | Q.eval x = m} := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hπ.ne_zero (by rw [← hp, map_zero])
  induction e with
  | zero => simp
  | succ e ih =>
    rw [← ih]
    symm
    refine Set.ncard_congr (fun x _ => fun i => p * x i) ?_ ?_ ?_
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      change Q.evalIn A (fun i => p * x i) = _
      rw [evalIn_const_mul, show Q.evalIn A x = _ from hx]
      ring
    · intro a b _ _ hab
      funext i
      exact mul_left_cancel₀ hp0 (congrFun hab i)
    · intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      have hd : ∀ i, p ∣ z i := fun i => hA _ (dvd_of_eval_eq_pow_mul K (Q.map φ) π hπ S₀ haniso
        (φ m) hm (e + 1) (by omega) (fun i => φ (z i))
        (by rw [eval_map_apply, hz, map_mul, map_pow, hp]) i)
      choose w hw using hd
      refine ⟨w, ?_, funext fun i => (hw i).symm⟩
      simp only [Set.mem_ofPred_eq]
      have h2 : Q.eval z = p ^ 2 * Q.eval w := by
        rw [show z = fun i => p * w i from funext hw]; exact evalIn_const_mul Q p w
      rw [h2, show 2 * (e + 1) = 2 + 2 * e by ring, pow_add, mul_assoc] at hz
      exact mul_left_cancel₀ (pow_ne_zero _ hp0) hz

/-! ### (5.6) and (5.7): the map $\pi_Z$ on densities -/

/-- A nondegenerate form in one variable is anisotropic over $K$; so an isotropic nondegenerate form has
$n \ne 1$. -/
theorem ne_one_of_isotropicIn (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (Q : QuadForm R n) (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn K) : n ≠ 1 := by
  rintro rfl
  obtain ⟨x, hx0, hx⟩ := hiso
  have hc : Q.coeff 0 0 ≠ 0 := by
    intro h; apply hQ; simp [hessian, Matrix.det_unique, h]
  have hx1 : x 0 ≠ 0 := fun h => hx0 (funext fun i => by fin_cases i; exact h)
  simp only [QuadForm.evalIn, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    le_refl, ↓reduceIte, mul_assoc, mul_eq_zero, or_self] at hx
  rcases hx with h | h
  · exact hc (IsFractionRing.injective R K (h.trans (map_zero _).symm))
  · exact hx1 h

/-- Exponent bookkeeping for the map $\pi_Z$: $n + (k-2)(n-1) + (n-2) = k(n-1)$ for $k \ge 2$, $n \ne 1$. -/
theorem exponent_piZ (n k : ℕ) (hn : n ≠ 1) (hk : 2 ≤ k) :
    n + (k - 2) * (n - 1) + (n - 2) = k * (n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rcases n with _ | _ | n
  · simp
  · exact absurd rfl hn
  · simp only [Nat.add_sub_cancel]
    ring_nf; omega

/-- **Normalized Zero-type count** (map $\pi_Z$, Hanke 2004, p. 359) over $R$: for $k \ge 2$ and $n \ne 1$,
$r^{\mathrm{Zero}}_{\pi^k}(\pi^2m)/q^{k(n-1)} = q^{-(n-2)}\, r_{\pi^{k-2}}(m)/q^{(k-2)(n-1)}$. -/
theorem repCountZero_normalized [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n) (π : R)
    (hπ : Irreducible π) (hn : n ≠ 1) (m : R) (k : ℕ) (hk : 2 ≤ k) :
    (repCountOf Q π k (π ^ 2 * m) (IsZeroType π k) : ℝ) / (q R : ℝ) ^ (k * (n - 1)) =
      ((q R : ℝ) ^ (n - 2))⁻¹ * ((repCount Q π (k - 2) m : ℝ) / (q R : ℝ) ^ ((k - 2) * (n - 1))) := by
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  rw [repCountZero_eq Q π hπ _ m rfl k hk, ← exponent_piZ n k hn hk, pow_add, pow_add]
  push_cast
  field_simp

/-- **Split of the normalized count** at $\pi^2m$ into the Zero part (via $\pi_Z$) and the Good ∪ Bad part,
for $k \ge 2$ and $n \ne 1$. -/
theorem normalized_split [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n) (π : R)
    (hπ : Irreducible π) (hn : n ≠ 1) (m : R) (k : ℕ) (hk : 2 ≤ k) :
    (repCount Q π k (π ^ 2 * m) : ℝ) / (q R : ℝ) ^ (k * (n - 1)) =
      ((q R : ℝ) ^ (n - 2))⁻¹ * ((repCount Q π (k - 2) m : ℝ) / (q R : ℝ) ^ ((k - 2) * (n - 1))) +
      (repCountOf Q π k (π ^ 2 * m) (fun x => ¬ IsZeroType π k x) : ℝ) /
        (q R : ℝ) ^ (k * (n - 1)) := by
  rw [repCount_eq_zero_add_nonZero Q π hπ, Nat.cast_add, add_div,
    repCountZero_normalized Q π hπ hn m k hk]

/-- **(5.6)** (Hanke 2004, p. 369) over $R$: for $Q$ nondegenerate, $n \ge 3$, $2 \ne 0$ in $R$ and $m \ne 0$,
$\beta_\pi(\pi^2 m) \ge q^{2-n}\beta_\pi(m)$. Every prime, dyadic or not. *Proof:* $r_{\pi^k}(\pi^2m) \ge
r^{\mathrm{Zero}}_{\pi^k}(\pi^2m) = q^n r_{\pi^{k-2}}(m)$ (`repCountZero_eq`); divide by $q^{k(n-1)}$ and let
$k \to \infty$ (`localDensity_eventually_eq`). -/
@[kb "hanke2004" "(5.6), p. 369"]
theorem localDensity_le_mul_sq [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n)
    (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (m : R)
    (hm : m ≠ 0) :
    localDensity Q π m ≤ (q R : ℝ) ^ (n - 2) * localDensity Q π (π ^ 2 * m) := by
  have hpZ : π ^ 2 ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hq0 : (0 : ℝ) < q R := by exact_mod_cast (q_pos (R := R))
  have h1 := localDensity_eventually_eq Q hQ π hπ (π ^ 2 * m) (mul_ne_zero hpZ hm) h20
  have h2 := (Filter.tendsto_sub_atTop_nat 2).eventually (localDensity_eventually_eq Q hQ π hπ m hm h20)
  obtain ⟨k, hk1, hk2, hk⟩ := (h1.and (h2.and (Filter.eventually_ge_atTop 2))).exists
  rw [← hk1, ← hk2, normalized_split Q π hπ (by omega) m k hk, mul_add,
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0.ne'), one_mul, le_add_iff_nonneg_right]
  positivity

/-- **Non-Zero-type density at $\pi^2T$ is a genuine limit** (Hanke 2004, p. 369):
$r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(\pi^2T)/q^{k(n-1)}$ is eventually $\beta_\pi(\pi^2T) - q^{-(n-2)}\beta_\pi(T)$, so
`localDensityOf` equals that value ($2 \ne 0$, $T \ne 0$, $n \ne 1$). -/
theorem localDensityOf_nonZero_eq [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n)
    (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (hn : n ≠ 1) (T : R)
    (hT0 : T ≠ 0) :
    localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) =
      localDensity Q π (π ^ 2 * T) - ((q R : ℝ) ^ (n - 2))⁻¹ * localDensity Q π T := by
  have hpZ : π ^ 2 ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have h1 := localDensity_eventually_eq Q hQ π hπ (π ^ 2 * T) (mul_ne_zero hpZ hT0) h20
  have h2 := (Filter.tendsto_sub_atTop_nat 2).eventually (localDensity_eventually_eq Q hQ π hπ T hT0 h20)
  apply Filter.Tendsto.limUnder_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h1, h2, Filter.eventually_ge_atTop 2] with k hk1 hk2 hk
  rw [← hk1, ← hk2, normalized_split Q π hπ hn T k hk]
  ring

/-- **One step of (5.7)** over $R$: under $\pi$-stability, for $e \ge 0$,
$\beta_\pi(\pi^{2(e+1)}T) = K + q^{-(n-2)}\beta_\pi(\pi^{2e}T)$ with $K = \beta_\pi(\pi^2T) - q^{-(n-2)}\beta_\pi(T)$. -/
theorem localDensity_pow_sq_step [Finite (IsLocalRing.ResidueField R)] (Q : QuadForm R n)
    (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (hn : n ≠ 1) (T : R)
    (hT0 : T ≠ 0)
    (hstab : ∀ᶠ k in Filter.atTop, ∀ ν ≥ 1,
      repCountOf Q π k (π ^ (2 * ν) * T) (fun x => ¬ IsZeroType π k x) =
        repCountOf Q π k (π ^ 2 * T) (fun x => ¬ IsZeroType π k x))
    (e : ℕ) :
    localDensity Q π (π ^ (2 * (e + 1)) * T) =
      (localDensity Q π (π ^ 2 * T) - ((q R : ℝ) ^ (n - 2))⁻¹ * localDensity Q π T) +
        ((q R : ℝ) ^ (n - 2))⁻¹ * localDensity Q π (π ^ (2 * e) * T) := by
  have hp : π ≠ 0 := hπ.ne_zero
  have hpZ : π ^ 2 ≠ 0 := pow_ne_zero _ hp
  have hpe : π ^ (2 * e) * T ≠ 0 := mul_ne_zero (pow_ne_zero _ hp) hT0
  have heq : π ^ (2 * (e + 1)) * T = π ^ 2 * (π ^ (2 * e) * T) := by ring
  have h1 := localDensity_eventually_eq Q hQ π hπ (π ^ 2 * T) (mul_ne_zero hpZ hT0) h20
  have h2 := (Filter.tendsto_sub_atTop_nat 2).eventually (localDensity_eventually_eq Q hQ π hπ T hT0 h20)
  have h3 := localDensity_eventually_eq Q hQ π hπ (π ^ (2 * (e + 1)) * T)
    (heq ▸ mul_ne_zero hpZ hpe) h20
  have h4 := (Filter.tendsto_sub_atTop_nat 2).eventually
    (localDensity_eventually_eq Q hQ π hπ (π ^ (2 * e) * T) hpe h20)
  obtain ⟨k, hk1, hk2, hk3, hk4, hk5, hk⟩ :=
    (h1.and (h2.and (h3.and (h4.and (hstab.and (Filter.eventually_ge_atTop 2)))))).exists
  rw [← hk1, ← hk2, ← hk3, ← hk4, normalized_split Q π hπ hn T k hk, heq,
    normalized_split Q π hπ hn _ k hk, ← heq, hk5 (e + 1) (by omega)]
  ring

/-- **(5.7)** (Hanke 2004, p. 369) over $R$: for $Q$ nondegenerate and isotropic over $K$, $2 \ne 0$ in $R$, and
$T'$ $\pi$-stable with $T' \ne 0$, writing $K_0 = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(\pi^2 T')$ and $q = \#R/\pi$,
$$\beta_\pi(T' \pi^{2\nu}) = K_0 \sum_{i=0}^{\nu-1} q^{-(n-2)i} + \frac{\beta_\pi(T')}{q^{(n-2)\nu}}.$$
Every prime, dyadic or not; no normal form needed. *Proof:* by stability the non-Zero-type part of
$\beta_\pi(T'\pi^{2i})$ is $K_0$ for $i \ge 1$, and the Zero-type part is $q^{-(n-2)}\beta_\pi(T'\pi^{2(i-1)})$ (map
$\pi_Z$); iterate. -/
@[kb "hanke2004" "(5.7), p. 369"]
theorem localDensity_pow_sq [Finite (IsLocalRing.ResidueField R)] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R)
    (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (S₀ : Finset (Fin n)) (hiso : Q.IsotropicIn K) (T : R)
    (hT0 : T ≠ 0) (hT : IsPStable Q S₀ π T) (e : ℕ) :
    localDensity Q π (π ^ (2 * e) * T) =
      localDensityOf Q π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) *
          ∑ i ∈ Finset.range e, ((q R : ℝ) ^ (n - 2))⁻¹ ^ i +
        localDensity Q π T / (q R : ℝ) ^ ((n - 2) * e) := by
  have hn := ne_one_of_isotropicIn K Q hQ hiso
  rw [localDensityOf_nonZero_eq Q hQ π hπ h20 hn T hT0]
  induction e with
  | zero => simp
  | succ e ih =>
    rw [localDensity_pow_sq_step Q hQ π hπ h20 hn T hT0 hT.2 e, ih, Finset.sum_range_succ', pow_mul,
      pow_mul, Finset.sum_congr rfl (fun i _ => pow_succ ((q R : ℝ) ^ (n - 2))⁻¹ i), ← Finset.sum_mul,
      pow_succ (_ ^ _) e, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring

end QuadFormsKB.LocalDensity.DVR
