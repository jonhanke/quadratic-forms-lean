/-
# Kitaoka 1993, §5.6: Siegel's count $A'_{p^r}(T, S)$ (Lemma 5.6.5) and Siegel's original local density

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Lemma 5.6.5, p. 97, the definition of
Siegel's local density, p. 98, and Proposition 5.6.1 (ii), p. 99 (printed pages).

**Setting** (as in `Ch5Densities.lean`). $p$ is a prime, $R = \mathbb Z_p$, $S$ an integral symmetric $n \times n$
matrix (the Gram matrix of $N$), $T$ an integral symmetric $m \times m$ matrix (the Gram matrix of $M$). Kitaoka's
count $\#A_{p^r}(T, S)$ (`countA`) uses the congruence $S[X] \equiv T \bmod p^rE_m$ (diagonal entries modulo $2p^r$).
Siegel's original count uses the plain congruence of all entries modulo $p^r$:
$$A'_{p^r}(T, S) = \{X \in M_{n,m}(R/p^rR) \mid S[X] \equiv T \bmod p^r\},$$
counted here by `countA' p r S T`, and Siegel's density is (p. 98)
$$\alpha_p(S, T) = 2^{-\delta_{m,n}}\lim_{r\to\infty}(p^r)^{m(m+1)/2 - mn}\#A'_{p^r}(T, S)$$
(`alphaSiegel`; $\delta$ is Kronecker's delta). Kitaoka *defines* $\alpha_p(M, N) := 2^{m\delta_{2,p} - \delta_{m,n}}
\beta_p(M, N)$ (`alphaP`) and asserts that the two agree.

**Proves**
* `countA'_eq_of_ne_two`: for $p \ne 2$, $\#A'_{p^r}(T, S) = \#A_{p^r}(T, S)$ for every $r$ (2 is a unit);
* `lemma565` (**Lemma 5.6.5**, case $e = 0$): $\#A'_{p^r}(T, S) = 2^{m\delta_{2,p}}\#A_{p^r}(T, S)$ for
  $r \ge h + 2$, where $p^hT^{-1} \in E_m$ (Kitaoka: "for a sufficiently large $r$");
* `proposition561_ii` (**Proposition 5.6.1 (ii)**, case $e = 0$):
  $\beta_p(M, N) = 2^{-m\delta_{2,p}}(p^r)^{m(m+1)/2-mn}\#A'_{p^r}(T, S)$ for $r \ge h + 2$;
* `tendsto_normA'` and `alphaSiegel_eq_alphaP`: Siegel's sequence converges and Siegel's original density equals
  Kitaoka's $\alpha_p(M, N)$, for every regular $T$ (p. 98, "$:= \alpha_p(M, N)$").

*Proof of Lemma 5.6.5 for $p = 2$.* Kitaoka splits $A'_{2^r}$ by the classes of $T' \bmod 2^{r+1}E_m$. Equivalently,
here: every $X \bmod 2^{r+1}$ with $S[X] \equiv T \bmod 2^{r+1}$ satisfies $S[X] - T \in 2^rE_m$, so it has a class
$c$ in $E_m/2E_m$ (`exists_class`, `class_unique` of `Ch5Stabilization.lean`), with
$S[X] - T \equiv 2^r(F_c + F_c^{\mathsf T}) \bmod 2^{r+1}E_m$. The plain congruence modulo $2^{r+1}$ holds exactly when
the off-diagonal values of $c$ vanish (the diagonal entries $2^{r+1}c_{ii}$ are already divisible by $2^{r+1}$). There
are $2^m$ such classes, and each class has $\#A_{2^{r+1}}(T, S)$ elements (`card_class`, the equinumerosity step of
Lemma 5.6.1). Hence $\#A'_{2^{r+1}} = 2^m\#A_{2^{r+1}}$ for $r \ge h + 1$.

The result is unconditional (no named input hypotheses).
-/
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5Stabilization

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {m n : ℕ}

/-- **Siegel's count $\#A'_{p^r}(T, S)$** (Kitaoka 1993, Lemma 5.6.5, p. 97, with $e = 0$): the number of
$X \in M_{n,m}(\mathbb Z_p/p^r\mathbb Z_p)$ with $S[X] \equiv T \bmod p^r$ entrywise (no extra condition on the
diagonal). Residues modulo $p^r$ are represented by $0, \dots, p^r - 1$, as in `countA`. -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.5, p. 97 (A'_{p^r}(T, S))"]
def countA' (p : ℕ) [Fact p.Prime] (r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) :
    ℕ :=
  Nat.card {X : Matrix (Fin n) (Fin m) (Fin (p ^ r)) //
    ∀ i j, (p : ℤ_[p]) ^ r ∣ ((liftRes p r X)ᵀ * S * liftRes p r X - T) i j}

/-- The sequence $(p^r)^{m(m+1)/2 - mn}\#A'_{p^r}(T, S)$ of Siegel's definition. -/
def normA' (p : ℕ) [Fact p.Prime] (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (r : ℕ) :
    ℝ :=
  ((p : ℝ) ^ r) ^ (((m * (m + 1) / 2 : ℕ) : ℤ) - (m : ℤ) * n) * (countA' p r S T : ℝ)

/-- **Siegel's original local density** (Kitaoka 1993, §5.6, p. 98):
$\alpha_p(S, T) = 2^{-\delta_{m,n}}\lim_{r\to\infty}(p^r)^{m(m+1)/2 - mn}\#A'_{p^r}(T, S)$ (Lean's `limUnder`). -/
@[kb "kitaoka1993" "§5.6, p. 98 (Siegel's original α_p(S, T))"]
def alphaSiegel (p : ℕ) [Fact p.Prime] (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) : ℝ :=
  (2 : ℝ) ^ (-(if m = n then 1 else 0 : ℤ)) * limUnder atTop (normA' p S T)

/-! ### Odd $p$ -/

theorem isUnit_two_of_ne_two (h2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  have : ‖((2 : ℕ) : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hp.out Nat.prime_two).mpr h2
  exact_mod_cast this

/-- For $p \ne 2$ the two counts agree: $\#A'_{p^r}(T, S) = \#A_{p^r}(T, S)$ (Kitaoka, proof of Lemma 5.6.5:
"When $p \ne 2$, $E_t(R)$ is simply $\{A = {}^tA \in M_t(R)\}$"). -/
theorem countA'_eq_of_ne_two (h2 : p ≠ 2) (r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p])
    (T : Matrix (Fin m) (Fin m) ℤ_[p]) : countA' p r S T = countA p r S T := by
  unfold countA' countA
  refine Nat.card_congr (Equiv.subtypeEquivRight fun X => forall₂_congr fun i j => ?_)
  obtain ⟨u, hu⟩ := isUnit_two_of_ne_two h2
  split_ifs
  · rw [mul_comm, ← hu]
    exact (Units.mul_left_dvd).symm
  · rw [mul_one]

/-! ### $p = 2$: the classes with vanishing off-diagonal values -/

/-- A chosen class of $X$ in $E_m/pE_m$ (meaningful when $S[X] - T \in p^rE_m$). -/
def classOf (r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p])
    (X : Matrix (Fin n) (Fin m) (Fin (p ^ (r + 1)))) : Sym2 (Fin m) → Fin (p ^ 1) :=
  Classical.epsilon fun c => GoodA p (r + 1) (r + 1) S (T + (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)) X

theorem good_class_iff {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} {r : ℕ}
    {X : Matrix (Fin n) (Fin m) (Fin (p ^ (r + 1)))} (c : Sym2 (Fin m) → Fin (p ^ 1)) :
    (GoodA p (r + 1) r S T X ∧ classOf r S T X = c) ↔
      GoodA p (r + 1) (r + 1) S (T + (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)) X := by
  set Fib : (Sym2 (Fin m) → Fin (p ^ 1)) → Prop := fun c =>
    GoodA p (r + 1) (r + 1) S (T + (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)) X
  constructor
  · rintro ⟨hX, rfl⟩
    obtain ⟨c, hc⟩ := exists_class hX
    exact Classical.epsilon_spec (p := Fib) ⟨c, by simp only [Fib, GoodA]; convert hc using 1; abel⟩
  · intro hX
    refine ⟨?_, ?_⟩
    · have := (ModE.mono hX (Nat.le_succ r)).add
        (⟨classF c, rfl⟩ : ModE p r ((p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)))
      convert this using 1
      abel
    · have hκ : Fib (classOf r S T X) := Classical.epsilon_spec (p := Fib) ⟨c, hX⟩
      exact class_unique (D := (liftRes p (r + 1) X)ᵀ * S * liftRes p (r + 1) X - T)
        (by simp only [Fib, GoodA] at hκ; convert hκ using 1; abel)
        (by simp only [GoodA] at hX; convert hX using 1; abel)

/-- **Counting by classes**: for $r \ge h + 1$ and any set $P$ of classes, the $X \bmod p^{r+1}$ with
$S[X] \equiv T \bmod p^rE_m$ whose class lies in $P$ number $\#P \cdot \#A_{p^{r+1}}(T, S)$. -/
theorem card_good_classes {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) (P : (Sym2 (Fin m) → Fin (p ^ 1)) → Prop) :
    Nat.card {X // GoodA p (r + 1) r S T X ∧ P (classOf r S T X)} =
      Nat.card {c // P c} * countA p (r + 1) S T := by
  classical
  have H : ∀ X ∈ Finset.univ.filter (fun X => GoodA p (r + 1) r S T X ∧ P (classOf r S T X)),
      classOf r S T X ∈ Finset.univ.filter P := fun X hX =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hX).2.2⟩
  have hc : ∀ c ∈ Finset.univ.filter P,
      ((Finset.univ.filter fun X => GoodA p (r + 1) r S T X ∧ P (classOf r S T X)).filter
        fun X => classOf r S T X = c).card = Nat.card {X // GoodA p (r + 1) (r + 1) S T X} := by
    intro c hc
    have hc' : P c := (Finset.mem_filter.mp hc).2
    rw [Finset.filter_filter, ← card_class hS hT hA hAE hr c, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← good_class_iff c]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, rfl⟩; exact ⟨⟨h1, hc'⟩, rfl⟩
  have key : (Finset.univ.filter fun X => GoodA p (r + 1) r S T X ∧ P (classOf r S T X)).card =
      (Finset.univ.filter P).card * Nat.card {X // GoodA p (r + 1) (r + 1) S T X} := by
    rw [Finset.card_eq_sum_card_fiberwise H, Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
  rw [countA_eq_card hS hT,
    Nat.card_eq_fintype_card (α := {X // GoodA p (r + 1) r S T X ∧ P (classOf r S T X)}),
    Fintype.card_subtype, key, Nat.card_eq_fintype_card (α := {c // P c}), Fintype.card_subtype]

/-- The classes whose off-diagonal values vanish. -/
def OffDiagZero (c : Sym2 (Fin m) → Fin (p ^ 1)) : Prop := ∀ i j, i ≠ j → c s(i, j) = 0

/-- There are $p^m$ classes with vanishing off-diagonal values (determined by their diagonal values). -/
theorem card_offDiagZero : Nat.card {c : Sym2 (Fin m) → Fin (p ^ 1) // OffDiagZero c} = p ^ m := by
  have e : {c : Sym2 (Fin m) → Fin (p ^ 1) // OffDiagZero c} ≃ (Fin m → Fin (p ^ 1)) :=
    { toFun := fun c i => c.1 s(i, i)
      invFun := fun f => ⟨Sym2.lift ⟨fun i j => if i = j then f i else 0, fun i j => by
          by_cases h : i = j
          · subst h; rfl
          · simp [h, Ne.symm h]⟩, fun i j hij => by simp [hij]⟩
      left_inv := fun c => by
        apply Subtype.ext
        funext s
        induction s using Sym2.ind with
        | _ i j =>
          by_cases h : i = j
          · subst h; simp
          · simp [h, c.2 i j h]
      right_inv := fun f => by funext i; simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_one]

/-- For $p = 2$ and symmetric $S$, $T$: $S[X] \equiv T \bmod 2^{r+1}$ holds exactly when $S[X] - T \in 2^rE_m$ and the
class of $X$ has vanishing off-diagonal values. -/
theorem plain_iff (h2 : p = 2) {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hS : Sᵀ = S) (hT : Tᵀ = T) {r : ℕ} (X : Matrix (Fin n) (Fin m) (Fin (p ^ (r + 1)))) :
    (∀ i j, (p : ℤ_[p]) ^ (r + 1) ∣ ((liftRes p (r + 1) X)ᵀ * S * liftRes p (r + 1) X - T) i j) ↔
      GoodA p (r + 1) r S T X ∧ OffDiagZero (classOf r S T X) := by
  subst h2
  set D := (liftRes 2 (r + 1) X)ᵀ * S * liftRes 2 (r + 1) X - T with hD
  have hDs : Dᵀ = D := by simp [D, transpose_sub, transpose_mul, hS, hT, Matrix.mul_assoc]
  have hp0 : ((2 : ℕ) : ℤ_[2]) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  -- the defining property of the class, once `D ∈ 2^r E`
  have hcls : ModE 2 r D → ModE 2 (r + 1) (D - ((2 : ℕ) : ℤ_[2]) ^ r •
      (classF (classOf r S T X) + (classF (classOf r S T X))ᵀ)) := by
    intro hgood
    have := (good_class_iff (S := S) (T := T) (X := X) (classOf r S T X)).mp ⟨hgood, rfl⟩
    simp only [GoodA] at this
    convert this using 1
    rw [hD]; abel
  have hsymE : (D - ((2 : ℕ) : ℤ_[2]) ^ r • (classF (classOf r S T X) + (classF (classOf r S T X))ᵀ))ᵀ =
      D - ((2 : ℕ) : ℤ_[2]) ^ r • (classF (classOf r S T X) + (classF (classOf r S T X))ᵀ) := by
    rw [transpose_sub, transpose_smul, classE_symm, hDs]
  have hval : ∀ a : Fin (2 ^ 1), ((2 : ℕ) : ℤ_[2]) ∣ ((a : ℕ) : ℤ_[2]) → a = 0 := by
    intro a ha
    have : (a : ℕ) < 2 := by simpa using a.2
    interval_cases h : (a : ℕ)
    · exact Fin.ext h
    · exfalso
      rw [Nat.cast_one] at ha
      have h1 := PadicInt.isUnit_iff.mp (isUnit_of_dvd_one ha)
      have h2 := PadicInt.norm_p (p := 2)
      rw [h1] at h2
      norm_num at h2
  constructor
  · intro hplain
    have hgood : ModE 2 r D := by
      rw [modE_iff_dvd hDs]
      intro i j
      refine dvd_trans ?_ (hplain i j)
      split_ifs
      · rw [pow_succ]; norm_num
      · rw [mul_one]; exact pow_dvd_pow _ (Nat.le_succ r)
    refine ⟨hgood, fun i j hij => ?_⟩
    have h1 := (modE_iff_dvd hsymE).mp (hcls hgood) i j
    rw [if_neg hij, mul_one, Matrix.sub_apply, Matrix.smul_apply, classE_apply, if_neg hij, smul_eq_mul] at h1
    have h3 : ((2 : ℕ) : ℤ_[2]) ^ (r + 1) ∣ ((2 : ℕ) : ℤ_[2]) ^ r * (((classOf r S T X s(i, j)) : ℕ) : ℤ_[2]) := by
      have := dvd_sub (hplain i j) h1
      rwa [sub_sub_cancel] at this
    rw [pow_succ] at h3
    exact hval _ ((mul_dvd_mul_iff_left hp0).mp h3)
  · rintro ⟨hgood, hoff⟩ i j
    have h1 := (modE_iff_dvd hsymE).mp (hcls hgood) i j
    rw [Matrix.sub_apply, Matrix.smul_apply, classE_apply, smul_eq_mul] at h1
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl] at h1
      have h4 : ((2 : ℕ) : ℤ_[2]) ^ (r + 1) ∣
          ((2 : ℕ) : ℤ_[2]) ^ r * (2 * (((classOf r S T X s(i, i)) : ℕ) : ℤ_[2])) :=
        ⟨(((classOf r S T X s(i, i)) : ℕ) : ℤ_[2]), by
          have e : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
          rw [e]; ring⟩
      have h5 : ((2 : ℕ) : ℤ_[2]) ^ (r + 1) ∣ ((2 : ℕ) : ℤ_[2]) ^ (r + 1) * 2 := dvd_mul_right _ _
      have := dvd_add (dvd_trans h5 h1) h4
      rwa [sub_add_cancel] at this
    · rw [if_neg hij, if_neg hij, mul_one, hoff i j hij, Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero] at h1
      exact h1

/-! ### Lemma 5.6.5 and Proposition 5.6.1 (ii) -/

/-- The factor $2^{m\delta_{2,p}}$. -/
def twoFactor (p m : ℕ) : ℕ := if p = 2 then 2 ^ m else 1

/-- **Kitaoka 1993, Lemma 5.6.5** (p. 97), case $e = 0$: for integral symmetric $S$ ($n \times n$) and $T$
($m \times m$) and $h$ with $p^hT^{-1} \in E_m$ ($TA = p^h1$, $A \in E_m$),
$$\#A'_{p^r}(T, S) = 2^{m\delta_{2,p}}\#A_{p^r}(T, S) \qquad (r \ge h + 2).$$
*Update:* the book says "for a sufficiently large $r$" and assumes $S$, $T$ regular; only $T$'s integer $h$ is needed here. For
$p \ne 2$ the equality holds for every $r$ (`countA'_eq_of_ne_two`). -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.5, p. 97"]
theorem lemma565 {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 2 ≤ r) : countA' p r S T = twoFactor p m * countA p r S T := by
  by_cases h2 : p = 2
  · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [twoFactor, if_pos h2, countA']
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun X => plain_iff h2 hS hT X),
      card_good_classes hS hT hA hAE (by omega), card_offDiagZero]
    exact congrArg (· * countA p (r + 1) S T) (by rw [h2])
  · rw [twoFactor, if_neg h2, one_mul, countA'_eq_of_ne_two h2]

theorem normA'_eq {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 2 ≤ r) : normA' p S T r = (twoFactor p m : ℝ) * betaP p S T := by
  rw [normA', lemma565 hS hT hA hAE hr, betaP_eq hS hT hA hAE (r := r) (by omega), normA]
  push_cast
  ring

/-- **Kitaoka 1993, Proposition 5.6.1 (ii)** (p. 99), case $e = 0$: for integral symmetric $S$, $T$ and $h$ with
$p^hT^{-1} \in E_m$,
$$\beta_p(M, N) = 2^{-m\delta_{2,p}}(p^r)^{m(m+1)/2 - mn}\#A'_{p^r}(T, S) \qquad (r \ge h + 2)$$
("if $S$ and $T$ are integral and $r$ is sufficiently large"). -/
@[kb "kitaoka1993" "§5.6, Prop. 5.6.1 (ii), p. 99"]
theorem proposition561_ii {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 2 ≤ r) :
    betaP p S T = (2 : ℝ) ^ (-(if p = 2 then (m : ℤ) else 0)) * normA' p S T r := by
  rw [normA'_eq hS hT hA hAE hr, twoFactor, ← mul_assoc]
  split_ifs
  · rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero,
      one_mul]
  · simp

/-- **Siegel's sequence converges**: $(p^r)^{m(m+1)/2-mn}\#A'_{p^r}(T, S) \to 2^{m\delta_{2,p}}\beta_p(M, N)$ for
integral symmetric $S$ and integral symmetric regular $T$; it is eventually constant. -/
theorem tendsto_normA' {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) :
    Tendsto (normA' p S T) atTop (nhds ((twoFactor p m : ℝ) * betaP p S T)) := by
  obtain ⟨h, A, hA, hAE⟩ := exists_h hT hdet
  exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨h + 2, fun r hr =>
    (normA'_eq hS hT hA hAE hr).symm⟩)

/-- **Siegel's original local density equals Kitaoka's $\alpha_p(M, N)$** (Kitaoka 1993, §5.6, p. 98:
$\alpha_p(S, T) = 2^{m\delta_{2,p} - \delta_{m,n}}\beta_p(M, N) =: \alpha_p(M, N)$), for integral symmetric $S$ and
integral symmetric regular $T$. -/
@[kb "kitaoka1993" "§5.6, p. 98 (Siegel's α_p(S, T) = α_p(M, N))"]
theorem alphaSiegel_eq_alphaP {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) : alphaSiegel p S T = alphaP p S T := by
  rw [alphaSiegel, (tendsto_normA' hS hT hdet).limUnder_eq, alphaP, twoFactor, ← mul_assoc]
  congr 1
  split_ifs <;> simp [zpow_sub₀, _root_.zpow_neg] <;> ring

end QuadFormsKB.Kitaoka.Density
