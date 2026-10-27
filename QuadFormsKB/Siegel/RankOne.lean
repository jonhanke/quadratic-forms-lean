/-
# Rank one over $\mathbb Z$: $\langle a\rangle$, its genus, its mass, and why Siegel's formula degenerates

**Layer:** integral forms `QuadForm ℤ 1` (`Defs/QuadForm.lean`), with the genus, classes, automorphisms and masses of
`Siegel/Genus.lean`, `Siegel/Mass.lean` ($\mathrm{GL}_n(\mathbb Z)$-classes, $\mathrm{Aut} \subseteq \mathrm{GL}_1(\mathbb Z)$; the convention used throughout), the
local densities $\beta_p(m)$ of `LocalDensity/Basic.lean` and the Euler factors of `Siegel/LocalProduct.lean`.

**The form.** $\langle a\rangle = $ `unary a`, $Q(x_0) = a\,x_0^2$ (0-based: one variable $x_0$). Every
`QuadForm ℤ 1` is one of these (`eq_unary`).

**Proves (unconditionally)**
* `repNum_unary`: for $a, m \ne 0$, $r_{\langle a\rangle}(m) = 2$ if $m = a k^2$ for some $k \in \mathbb Z$, else $0$; and
  $r_{\langle a\rangle}(0) = 1$ (`repNum_unary_zero`);
* `aut_unary_eq_top`, `card_aut_unary`: $\mathrm{Aut}(\langle a\rangle) = \mathrm{GL}_1(\mathbb Z) = \{\pm 1\}$, of order $2$;
* `sameGenus_unary_iff`, `genusClasses_unary`: the genus of $\langle a\rangle$ is the single class $[\langle a\rangle]$
  ($\langle b\rangle$ in the genus of $\langle a\rangle$ forces $b = a$: $p$-adic norms give $|b| = |a|$, the real place
  gives the sign);
* `mass_unary`: $\mathrm{Mass}(\langle a\rangle) = \tfrac12$; `genusRepAvg_unary`: $a_E(m) = r_{\langle a\rangle}(m)$;
* the local densities: `localDensity_unary_good` ($\beta_p(\langle a\rangle, m) = 1 + \left(\frac{am}{p}\right)$ for
  $p \nmid 2am$), `one_le_localDensity_unary` ($\beta_p(\langle a\rangle, ak^2) \ge 1$ at **every** prime),
  `localDensity_unary_eq_zero` ($\beta_p = 0$ when $v_p(m) < v_p(a)$ or $v_p(m) - v_p(a)$ is odd);
* **the degeneration of Siegel's formula** (`siegel_rank_one_dichotomy`): for $a, m \ne 0$ exactly one of
  - $m = ak^2$ ($m$ is represented, $r(m) = 2$): the partial products $\prod_{p \le X}\beta_p(m) \to +\infty$
    (`tendsto_eulerPartialProd_atTop`), so the Euler product has no value in the natural order
    (`not_isEulerProductValue`) and is not unconditionally convergent (`not_multipliable_eulerFactor`);
  - $m \ne ak^2$ for all $k$ ($r(m) = 0$): some $\beta_p(m) = 0$ (`exists_eulerFactor_eq_zero`; a local obstruction
    at a prime dividing $am$, or, when $m = -ak^2$, a prime $p \equiv 3 \bmod 4$ from Dirichlet's theorem), so the
    product converges to $0$ (`hasProd_eulerFactor_zero`).

  Hence there is **no** Euler-product Siegel formula $a_E(m) = c\,\beta_\infty(m)\prod_p\beta_p(m)$ in rank $1$
  (`no_siegel_formula_rank_one`): the product diverges exactly when $m$ is represented.

*Why* (Siegel 1935, the factor $\varepsilon$; Weil 1982 §3.7 [unverified]): $\beta_p(m) = 1 + \chi_{am}(p)$ is
$1 + O(1)$, not $1 + O(p^{-2})$; the Euler product is an $L(1, \chi)$-type product with nothing to cancel the pole of
$\zeta$ when $\chi_{am}$ is trivial. In rank $1$, $SO_1$ is the trivial group, $\tau(SO_1) = 1$ (not $2$), and
Siegel's $\varepsilon = \tfrac12$ for $r = n$ appears as $\mathrm{Mass}(\langle a\rangle) = \tfrac12$ (see
`Tamagawa/RankOneNF.lean`).
-/
import QuadFormsKB.Siegel.Mass
import QuadFormsKB.Siegel.LocalProduct

open Matrix Filter Topology

namespace QuadFormsKB.Siegel.RankOne

/-! ### The unary form $\langle a\rangle$ -/

/-- **The unary form** $\langle a\rangle$: $Q(x_0) = a\,x_0^2$ over $\mathbb Z$ (one variable, 0-based index $0$;
Cassels 1978, Ch. 9, §1, p. 128: integral forms in $n \ge 1$ variables; Cassels has no separate discussion of rank
one). -/
@[kb "cassels1978" "Ch. 9, §1, p. 128 (integral forms, n ≥ 1)"]
def unary (a : ℤ) : QuadForm ℤ 1 := QuadForm.diag fun _ => a

/-- $\langle a\rangle$ after any base change $f : \mathbb Z \to S$: $Q(x) = f(a)\,x_0^2$. -/
theorem eval_unary_map {S : Type*} [CommRing S] (f : ℤ →+* S) (a : ℤ) (x : Fin 1 → S) :
    ((unary a).map f).eval x = f a * x 0 ^ 2 := by
  simp [QuadForm.map, unary, QuadForm.diag, QuadForm.evalIn]; ring

/-- $\langle a\rangle(x) = a\,x_0^2$ over any ring $K$. -/
theorem evalIn_unary (K : Type*) [CommRing K] (a : ℤ) (x : Fin 1 → K) :
    (unary a).evalIn K x = (a : K) * x 0 ^ 2 := by
  simp [unary, QuadForm.diag, QuadForm.evalIn]; ring

theorem eval_unary (a : ℤ) (x : Fin 1 → ℤ) : (unary a).eval x = a * x 0 ^ 2 := by
  simpa using evalIn_unary ℤ a x

/-- **Every integral form in one variable is unary:** $Q = \langle c_{00}\rangle$. -/
theorem eq_unary (Q : QuadForm ℤ 1) : Q = unary (Q.coeff 0 0) := by
  ext i j
  fin_cases i; fin_cases j
  simp [unary, QuadForm.diag]

/-- The Hessian of $\langle a\rangle$ is $(2a)$; so $\langle a\rangle$ is nondegenerate iff $a \ne 0$. -/
theorem nondegenerate_unary {a : ℤ} (ha : a ≠ 0) : (unary a).Nondegenerate := by
  simp [QuadForm.Nondegenerate, QuadForm.hessian, unary, QuadForm.diag, ha]

theorem mulVec_fin_one {R : Type*} [CommRing R] (g : Matrix (Fin 1) (Fin 1) R) (x : Fin 1 → R) :
    (g *ᵥ x) 0 = g 0 0 * x 0 := by
  simp [mulVec, dotProduct]

/-! ### Representation numbers -/

/-- **$r_{\langle a\rangle}(ak^2) = 2$** for $a, k \ne 0$: the representations are $x_0 = \pm k$. -/
theorem repNum_unary_of_eq {a : ℤ} (ha : a ≠ 0) {k : ℤ} (hk : k ≠ 0) : repNum (unary a) (a * k ^ 2) = 2 := by
  have hset : repSet (unary a) (a * k ^ 2) = {fun _ => k, fun _ => -k} := by
    ext x
    simp only [repSet, Set.mem_ofPred_eq, eval_unary, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h2 : x 0 ^ 2 = k ^ 2 := mul_left_cancel₀ ha h
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
      · left; funext i; fin_cases i; exact h3
      · right; funext i; fin_cases i; exact h3
    · rintro (rfl | rfl) <;> ring
  rw [repNum, hset, Nat.card_coe_set_eq, Set.ncard_pair]
  intro h
  have : k = -k := congrFun h 0
  omega

/-- **$r_{\langle a\rangle}(m) = 0$** if $m$ is not of the form $ak^2$ with $k \in \mathbb Z$. -/
theorem repNum_unary_eq_zero {a m : ℤ} (h : ∀ k : ℤ, m ≠ a * k ^ 2) : repNum (unary a) m = 0 := by
  have : repSet (unary a) m = ∅ := by
    ext x
    simp only [repSet, Set.mem_ofPred_eq, eval_unary, Set.mem_empty_iff_false, iff_false]
    exact fun hx => h (x 0) hx.symm
  rw [repNum, this]; simp

/-- **$r_{\langle a\rangle}(0) = 1$** for $a \ne 0$ (only $x_0 = 0$). -/
theorem repNum_unary_zero {a : ℤ} (ha : a ≠ 0) : repNum (unary a) 0 = 1 := by
  have : repSet (unary a) 0 = {0} := by
    ext x
    simp only [repSet, Set.mem_ofPred_eq, eval_unary, Set.mem_singleton_iff, mul_eq_zero, ha, false_or,
      pow_eq_zero_iff two_ne_zero]
    constructor
    · intro h; funext i; fin_cases i; exact h
    · rintro rfl; rfl
  rw [repNum, this]; simp

open Classical in
/-- **The representation numbers of $\langle a\rangle$** (representations as in Cassels 1978, Ch. 1, §2, (2.3), p. 5): for $a \ne 0$ and $m \ne 0$,
$$r_{\langle a\rangle}(m) = \#\{x_0 \in \mathbb Z : a x_0^2 = m\} = \begin{cases} 2 & m = ak^2 \text{ for some } k \in \mathbb Z,\\
0 & \text{otherwise}\end{cases}$$
($k \ne 0$ automatically since $m \ne 0$; equivalently, $m/a$ is the square of a nonzero integer). For $m = 0$,
$r(0) = 1$ (`repNum_unary_zero`). -/
@[kb "cassels1978" "Ch. 1, §2, (2.3), p. 5 (representations)"]
theorem repNum_unary {a m : ℤ} (ha : a ≠ 0) (hm : m ≠ 0) :
    repNum (unary a) m = if ∃ k : ℤ, m = a * k ^ 2 then 2 else 0 := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    have hk : k ≠ 0 := by rintro rfl; simp at hm
    exact repNum_unary_of_eq ha hk
  · push Not at h
    exact repNum_unary_eq_zero h

/-! ### The automorphism group -/

/-- The $(0,0)$ entry of $g \in \mathrm{GL}_1(\mathbb Z)$ is $\pm 1$. -/
theorem sq_entry_of_GL (g : GL (Fin 1) ℤ) : g.val 0 0 ^ 2 = 1 := by
  have h := congrFun (congrFun g.mul_inv 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq] at h
  have hu : IsUnit (g.val 0 0) := IsUnit.of_mul_eq_one _ h
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] <;> norm_num

/-- **$\mathrm{Aut}(\langle a\rangle) = \mathrm{GL}_1(\mathbb Z)$**: every $g = (\pm1)$ preserves $a x_0^2$. -/
theorem aut_unary_eq_top (a : ℤ) : Aut (unary a) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  intro x
  rw [eval_unary, eval_unary, mulVec_fin_one, mul_pow, sq_entry_of_GL, one_mul]

/-- $|\mathrm{GL}_1(\mathbb Z)| = |\mathbb Z^\times| = 2$. -/
theorem card_GL_one_int : Nat.card (GL (Fin 1) ℤ) = 2 := by
  rw [Nat.card_congr (Units.mapEquiv (Matrix.uniqueRingEquiv (m := Fin 1) (A := ℤ)).toMulEquiv).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- **$O(\langle a\rangle)(\mathbb Z) = \{\pm 1\}$ has order $2$** (for every $a$; $O(f)$ as in Cassels 1978, Ch. 9, §1, p. 127). -/
@[kb "cassels1978" "Ch. 9, §1, p. 127 (the group O(f) of integral automorphs)"]
theorem card_aut_unary (a : ℤ) : Nat.card (Aut (unary a)) = 2 := by
  rw [aut_unary_eq_top, Subgroup.card_top, card_GL_one_int]

/-! ### The genus is one class -/

/-- If $(p^j \mid a \iff p^j \mid b)$ for every prime power, then $|a| = |b|$. -/
theorem natAbs_eq_of_forall_prime_pow_dvd {a b : ℤ}
    (h : ∀ p j : ℕ, p.Prime → ((p : ℤ) ^ j ∣ a ↔ (p : ℤ) ^ j ∣ b)) : a.natAbs = b.natAbs := by
  refine Nat.dvd_antisymm ((Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr fun p j hp hd => ?_)
    ((Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr fun p j hp hd => ?_)
  · have := (h p j hp).mp (Int.natCast_dvd.mpr (by simpa using hd))
    simpa using Int.natCast_dvd.mp this
  · have := (h p j hp).mpr (Int.natCast_dvd.mpr (by simpa using hd))
    simpa using Int.natCast_dvd.mp this

/-- **The genus of $\langle a\rangle$:** $\langle b\rangle$ is in the genus of $\langle a\rangle$ (`SameGenus`: equivalent over
every $\mathbb Z_p$ and over $\mathbb R$) iff $b = a$. *Proof:* over $\mathbb Z_p$, $b = a u^2$ with $u \in \mathbb Z_p^\times$, so
$\|b\|_p = \|a\|_p$ for every $p$ and $|b| = |a|$; over $\mathbb R$, $b = a t^2$ with $t \ne 0$ fixes the sign. -/
@[kb "cassels1978" "Ch. 9, Lemma 4.1, p. 139"]
theorem sameGenus_unary_iff (a b : ℤ) : SameGenus (unary a) (unary b) ↔ b = a := by
  constructor
  · rintro ⟨hp, ⟨g, hg⟩⟩
    -- the real place
    have hR := hg (fun _ => 1)
    rw [eval_unary_map, eval_unary_map, mulVec_fin_one] at hR
    simp only [eq_intCast, mul_one, one_pow] at hR
    -- `hR : (a : ℝ) * (g 0 0) ^ 2 = b`
    have hg0 : g.val 0 0 ≠ 0 := by
      intro h0
      have := congrFun (congrFun g.mul_inv 0) 0
      simp [Matrix.mul_apply, h0] at this
    have habs : a.natAbs = b.natAbs := by
      refine natAbs_eq_of_forall_prime_pow_dvd fun p j hpp => ?_
      have : Fact p.Prime := ⟨hpp⟩
      obtain ⟨u, hu⟩ := hp p
      have h1 := hu (fun _ => 1)
      rw [eval_unary_map, eval_unary_map, mulVec_fin_one] at h1
      simp only [eq_intCast, mul_one, one_pow] at h1
      have hunit : IsUnit (u.val 0 0) := by
        have := congrFun (congrFun u.mul_inv 0) 0
        simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq] at this
        exact IsUnit.of_mul_eq_one _ this
      have hn : ‖((b : ℤ) : ℤ_[p])‖ = ‖((a : ℤ) : ℤ_[p])‖ := by
        rw [← h1, norm_mul, norm_pow, PadicInt.isUnit_iff.mp hunit, one_pow, mul_one]
      rw [← PadicInt.norm_int_le_pow_iff_dvd, ← PadicInt.norm_int_le_pow_iff_dvd, hn]
    rcases Int.natAbs_eq_natAbs_iff.mp habs with h | h
    · exact h.symm
    · -- `a = -b`: impossible unless `b = 0`
      subst h
      push_cast at hR
      have hpos : (0 : ℝ) < (g.val 0 0) ^ 2 := by positivity
      have h0 : (b : ℝ) * ((g.val 0 0) ^ 2 + 1) = 0 := by linarith
      have hb : (b : ℝ) = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact h
        · linarith
      have : b = 0 := by exact_mod_cast hb
      simp [this]
  · rintro rfl; exact SameGenus.refl _

/-- **The genus of $\langle a\rangle$ is a single class** (Cassels 1978, Ch. 9, Lemma 4.1, p. 139: the determinant is a genus invariant, and for $n = 1$ it is the form): the set of
$\mathrm{GL}_1(\mathbb Z)$-classes in the genus of $\langle a\rangle$ is $\{[\langle a\rangle]\}$, for every $a \in \mathbb Z$. -/
@[kb "cassels1978" "Ch. 9, Lemma 4.1, p. 139"]
theorem genusClasses_unary (a : ℤ) : genusClasses (unary a) = {classOf (unary a)} := by
  ext c
  induction c using Quotient.inductionOn with
  | h Q' =>
    change classOf Q' ∈ _ ↔ classOf Q' ∈ _
    rw [classOf_mem_genusClasses_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [eq_unary Q'] at h ⊢
      rw [(sameGenus_unary_iff _ _).mp h]
    · intro h
      exact (classOf_eq_classOf_iff.mp h.symm).sameGenus

/-- **The mass of $\langle a\rangle$ is $\tfrac12$** (Siegel 1935, $\varepsilon = \tfrac12$ for $r = n$ [unverified];
Weil 1982, §3.7 [unverified]): $\mathrm{Mass}(\langle a\rangle) = \sum_{[Q'] \in \mathrm{Gen}} 1/|\mathrm{Aut}(Q')| = 1/|\{\pm1\}| = \tfrac12$,
for every $a \in \mathbb Z$ (one class, `genusClasses_unary`; $|\mathrm{Aut}| = 2$, `card_aut_unary`). -/
@[kb "siegel1935" "ε = 1/2 for r = n (rank one) [unverified]"]
theorem mass_unary (a : ℤ) : mass (unary a) = 1 / 2 := by
  rw [mass, genusClasses_unary, finsum_mem_singleton, QClass.autCard_classOf, card_aut_unary]
  norm_num

/-- **One-class genus:** $a_E(m) = r_{\langle a\rangle}(m)$ for every $a$ and $m$. -/
theorem genusRepAvg_unary (a m : ℤ) : genusRepAvg (unary a) m = repNum (unary a) m := by
  rw [genusRepAvg, genusRepSum, mass_unary, genusClasses_unary, finsum_mem_singleton,
    QClass.autCard_classOf, QClass.repNum_classOf, card_aut_unary]
  ring

end QuadFormsKB.Siegel.RankOne
