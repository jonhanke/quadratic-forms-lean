/-
# Maximal orders of class number one over $\mathbb Q$ (Voight, Theorem 25.4.1)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`), Theorem 25.4.1 (p. 423), with
Theorem 30.1.5 (p. 543).

**Contents.**
* `classNumberOneRat_of_eichlerClassNumberFormulaRat`: Theorem 25.4.1 (`ClassNumberOneRat`), **proved conditional on**
  the Eichler class number formula over $\mathbb Q$ (`EichlerClassNumberFormulaRat`, Theorem 30.1.5, stated in
  `Voight/MassFormula.lean`). The book leaves the proof as "a calculation by hand" (Exercise 25.5).
* `odd_card_ramFin`: a definite quaternion algebra over $\mathbb Q$ is ramified at an odd number of primes (Hilbert
  reciprocity, `ramified_finite_even`, and ramification at the real place).
* `absNorm_eq_natGenerator`, `absNorm_prime`, `absNorm_injective`: finite places of $\mathbb Q$ and their primes.
-/
import QuadFormsKB.Literature.Voight.Wave5.ClassNumber
import QuadFormsKB.Literature.Voight.Wave4.ClassSet
import QuadFormsKB.Equiv.NumberFieldRat
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Wave5

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Voight QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4

theorem absNorm_eq_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm v.asIdeal = Rat.HeightOneSpectrum.natGenerator v := by
  have h := Rat.HeightOneSpectrum.span_natGenerator v
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h1 : Ideal.absNorm v.asIdeal = Ideal.absNorm (v.asIdeal.map e) := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply]
    exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal (v.asIdeal.map e) e rfl).toEquiv
  rw [h1, ← h, Ideal.absNorm_span_singleton]
  simp

private theorem kron4 : ∀ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ),
    Siegel.kroneckerSym (-4) p = if p = 2 then 0 else if p % 4 = 1 then 1 else -1 := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [Siegel.kroneckerSym]

private theorem kron3 : ∀ p ∈ ({2, 3, 5, 7, 11, 13} : Finset ℕ),
    Siegel.kroneckerSym (-3) p = if p = 3 then 0 else if p % 3 = 1 then 1 else -1 := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [Siegel.kroneckerSym] <;> decide

private theorem kron_trich (a : ℤ) (ha : a = -4 ∨ a = -3) (b : ℕ) :
    Siegel.kroneckerSym a b = 0 ∨ Siegel.kroneckerSym a b = 1 ∨ Siegel.kroneckerSym a b = -1 := by
  unfold Siegel.kroneckerSym
  have hj := jacobiSym.trichotomy a (ordCompl[2] b)
  rcases ha with rfl | rfl
  · have he : Even (-4 : ℤ) := by decide
    rw [if_pos he]
    rcases Nat.eq_zero_or_pos (b.factorization 2) with h0 | h0
    · simpa [h0] using hj
    · rw [zero_pow h0.ne']; simp
  · have hχ : ZMod.χ₈ ((-3 : ℤ) : ZMod 8) = -1 := by
      norm_num <;> decide
    have he : ¬ Even (-3 : ℤ) := by decide
    rw [if_neg he, hχ]
    rcases neg_one_pow_eq_or ℤ (b.factorization 2) with h | h <;> rw [h] <;>
      rcases hj with hj | hj | hj <;> rw [hj] <;> simp

/-- Tabulated $\left(\frac{-4}{p}\right)$ for $p \in \{2,3,5,7,11,13\}$. -/
private def t4 (p : ℕ) : ℤ := if p = 2 then 0 else if p % 4 = 1 then 1 else -1
/-- Tabulated $\left(\frac{-3}{p}\right)$ for $p \in \{2,3,5,7,11,13\}$. -/
private def t3 (p : ℕ) : ℤ := if p = 3 then 0 else if p % 3 = 1 then 1 else -1

/-- Twelve times the class number, from the tabulated symbols. -/
private def G (S : Finset ℕ) : ℤ :=
  (∏ p ∈ S, ((p : ℤ) - 1)) + 3 * ∏ p ∈ S, (1 - t4 p) + 4 * ∏ p ∈ S, (1 - t3 p)

/-- The finitely many candidate primes. -/
private def Tset : Finset ℕ := {2, 3, 5, 7, 11, 13}

private theorem table : ∀ S ∈ Tset.powerset, Odd S.card →
    (G S = 12 ↔ ∏ p ∈ S, p ∈ ({2, 3, 5, 7, 13} : Finset ℕ)) := by
  unfold G Tset t4 t3
  decide

private theorem mem_Tset {p : ℕ} (hp : p.Prime) (h : p ≤ 13) : p ∈ Tset := by
  interval_cases p <;> first | (simp [Tset]; done) | (exfalso; norm_num at hp)

private theorem sub_of_eq {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime)
    (hA : 0 ≤ ∏ p ∈ S, (1 - Siegel.kroneckerSym (-4) p))
    (hB : 0 ≤ ∏ p ∈ S, (1 - Siegel.kroneckerSym (-3) p))
    (h : (∏ p ∈ S, ((p : ℤ) - 1)) + 3 * ∏ p ∈ S, (1 - Siegel.kroneckerSym (-4) p) +
      4 * ∏ p ∈ S, (1 - Siegel.kroneckerSym (-3) p) = 12) : S ⊆ Tset := by
  intro p hpS
  have hpos : 0 < ∏ p ∈ S, ((p : ℤ) - 1) :=
    Finset.prod_pos fun q hq => by have := (hp q hq).two_le; omega
  have hd : ((p : ℤ) - 1) ∣ ∏ p ∈ S, ((p : ℤ) - 1) := Finset.dvd_prod_of_mem _ hpS
  have := Int.le_of_dvd hpos hd
  exact mem_Tset (hp p hpS) (by omega)

private theorem sub_of_prod {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime)
    (h : ∏ p ∈ S, p ∈ ({2, 3, 5, 7, 13} : Finset ℕ)) : S ⊆ Tset := by
  intro p hpS
  have hd : p ∣ ∏ p ∈ S, p := Finset.dvd_prod_of_mem _ hpS
  have hq : ∏ p ∈ S, p ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hd
  have h13 : ∏ p ∈ S, p ≤ 13 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at h; omega
  exact mem_Tset (hp p hpS) (by omega)

private theorem real_iff (Φ A B : ℤ) :
    ((Φ : ℝ) / 12 + (A : ℝ) / 4 + (B : ℝ) / 3 = 1) ↔ Φ + 3 * A + 4 * B = 12 := by
  constructor
  · intro h
    have : ((Φ + 3 * A + 4 * B : ℤ) : ℝ) = 12 := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((Φ + 3 * A + 4 * B : ℤ) : ℝ) = 12 := by exact_mod_cast h
    push_cast at this; linarith

/-- **The arithmetic core.** For a finite set $S$ of primes of odd cardinality, the Eichler class number expression equals
$1$ iff $\prod_{p \in S} p \in \{2,3,5,7,13\}$. -/
private theorem arith {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) (hodd : Odd S.card) :
    ((∏ p ∈ S, ((p : ℝ) - 1)) / 12 + (∏ p ∈ S, (1 - (Siegel.kroneckerSym (-4) p : ℝ))) / 4 +
      (∏ p ∈ S, (1 - (Siegel.kroneckerSym (-3) p : ℝ))) / 3 = 1) ↔
      ∏ p ∈ S, p ∈ ({2, 3, 5, 7, 13} : Finset ℕ) := by
  have e1 : (∏ p ∈ S, ((p : ℝ) - 1)) = ((∏ p ∈ S, ((p : ℤ) - 1) : ℤ) : ℝ) := by push_cast; rfl
  have e2 : (∏ p ∈ S, (1 - (Siegel.kroneckerSym (-4) p : ℝ))) =
      ((∏ p ∈ S, (1 - Siegel.kroneckerSym (-4) p) : ℤ) : ℝ) := by push_cast; rfl
  have e3 : (∏ p ∈ S, (1 - (Siegel.kroneckerSym (-3) p : ℝ))) =
      ((∏ p ∈ S, (1 - Siegel.kroneckerSym (-3) p) : ℤ) : ℝ) := by push_cast; rfl
  rw [e1, e2, e3, real_iff]
  have hA : 0 ≤ ∏ p ∈ S, (1 - Siegel.kroneckerSym (-4) p) :=
    Finset.prod_nonneg fun q _ => by
      rcases kron_trich (-4) (Or.inl rfl) q with h | h | h <;> rw [h] <;> norm_num
  have hB : 0 ≤ ∏ p ∈ S, (1 - Siegel.kroneckerSym (-3) p) :=
    Finset.prod_nonneg fun q _ => by
      rcases kron_trich (-3) (Or.inr rfl) q with h | h | h <;> rw [h] <;> norm_num
  constructor
  · intro h
    have hS := sub_of_eq hp hA hB h
    have c4 : ∏ p ∈ S, (1 - Siegel.kroneckerSym (-4) p) = ∏ p ∈ S, (1 - t4 p) :=
      Finset.prod_congr rfl fun q hq => by rw [kron4 q (hS hq)]; rfl
    have c3 : ∏ p ∈ S, (1 - Siegel.kroneckerSym (-3) p) = ∏ p ∈ S, (1 - t3 p) :=
      Finset.prod_congr rfl fun q hq => by rw [kron3 q (hS hq)]; rfl
    rw [c4, c3] at h
    exact (table S (Finset.mem_powerset.2 hS) hodd).1 h
  · intro h
    have hS := sub_of_prod hp h
    have c4 : ∏ p ∈ S, (1 - Siegel.kroneckerSym (-4) p) = ∏ p ∈ S, (1 - t4 p) :=
      Finset.prod_congr rfl fun q hq => by rw [kron4 q (hS hq)]; rfl
    have c3 : ∏ p ∈ S, (1 - Siegel.kroneckerSym (-3) p) = ∏ p ∈ S, (1 - t3 p) :=
      Finset.prod_congr rfl fun q hq => by rw [kron3 q (hS hq)]; rfl
    rw [c4, c3]
    exact (table S (Finset.mem_powerset.2 hS) hodd).2 h

/-! ### From ramified places to a set of primes -/

theorem absNorm_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal).Prime := by
  rw [absNorm_eq_natGenerator]; exact Rat.HeightOneSpectrum.prime_natGenerator v

theorem absNorm_injective : Function.Injective (fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal) := by
  intro v w h
  simp only [absNorm_eq_natGenerator] at h
  have : Rat.HeightOneSpectrum.primesEquiv v = Rat.HeightOneSpectrum.primesEquiv w :=
    Subtype.ext h
  exact Rat.HeightOneSpectrum.primesEquiv.injective this

/-- The ramified finite places have odd cardinality: the real place is ramified in a definite algebra over $\mathbb Q$,
and the total number of ramified places is even. -/
theorem odd_card_ramFin {a b : 𝓞 ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) :
    Odd (ramFin ha hb).card := by
  have ha' : algebraMap (𝓞 ℚ) ℚ a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).2 ha
  have hb' : algebraMap (𝓞 ℚ) ℚ b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).2 hb
  obtain ⟨-, hev⟩ := ramified_finite_even ha' hb'
  set w : InfinitePlace ℚ := Rat.infinitePlace
  have hreal : w.IsReal := Rat.isReal_infinitePlace
  have hinf : IsRamifiedAt (algebraMap (𝓞 ℚ) ℚ a) (algebraMap (𝓞 ℚ) ℚ b) (NFPlace.infinite w) := by
    rw [isRamifiedAt_iff ha' hb']
    show hilbertSymbol w.Completion _ _ = -1
    let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hreal
    have hφ : ∀ q : ℚ, φ (algebraMap ℚ w.Completion q) = (q : ℝ) := fun q => by
      rw [eq_ratCast]; exact map_ratCast φ q
    rw [← QuadFormsKB.hilbertSymbol_ringEquiv φ, hφ, hφ]
    have h1 := (hdef (Rat.castHom ℝ)).1
    have h2 := (hdef (Rat.castHom ℝ)).2
    rw [hilbertSymbol_real _ _ (by exact_mod_cast ha') (by exact_mod_cast hb')]
    exact ⟨by simpa using h1, by simpa using h2⟩
  have hset : {v : NFPlace ℚ | IsRamifiedAt (algebraMap (𝓞 ℚ) ℚ a) (algebraMap (𝓞 ℚ) ℚ b) v} =
      insert (NFPlace.infinite w) (NFPlace.finite '' (ramFin ha hb : Set (HeightOneSpectrum (𝓞 ℚ)))) := by
    ext v
    rcases v with u | v
    · simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_image, reduceCtorEq, and_false,
        exists_false, or_false, NFPlace.infinite.injEq]
      exact ⟨fun _ => Subsingleton.elim _ _, fun h => by rw [h]; exact hinf⟩
    · simp only [Set.mem_setOf_eq, Set.mem_insert_iff, reduceCtorEq, Set.mem_image, Finset.mem_coe,
        NFPlace.finite.injEq, exists_eq_right, false_or]
      exact (mem_ramFin ha hb).symm
  rw [hset] at hev
  have hn : NFPlace.infinite w ∉ NFPlace.finite '' (ramFin ha hb : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    simp
  rw [Set.ncard_insert_of_notMem hn (Set.Finite.image _ (Finset.finite_toSet _)),
    Set.ncard_image_of_injective _ (fun x y h => by injection h), Set.ncard_coe_finset] at hev
  exact Nat.not_even_iff_odd.1 (Nat.even_add_one.1 hev)

/-- **Voight's Theorem 25.4.1, conditional on the Eichler class number formula over $\mathbb Q$.** Let
$B = (a, b \mid \mathbb Q)$ be a definite quaternion algebra over $\mathbb Q$ with discriminant
$D = \prod_{p \in \operatorname{Ram}_f B} p$ and let $\mathcal O \subset B$ be a maximal order. Assuming the Eichler class
number formula over $\mathbb Q$ (Voight's Theorem 30.1.5, `EichlerClassNumberFormulaRat`), the class number of $\mathcal O$
is $1$ if and only if $D \in \{2, 3, 5, 7, 13\}$.

*Proof.* The ramified finite places correspond to distinct primes, and their number is odd because the real place is
ramified in a definite algebra and the total number of ramified places is even (Hilbert reciprocity). With
$\varphi = \prod_{p \mid D}(p-1)$ the formula reads $\varphi/12 + A/4 + B/3$ where every factor of $A$ and $B$ lies in
$\{0, 1, 2\}$. The value $1$ forces $\varphi \le 12$, so every $p \mid D$ is at most $13$, and a finite check over the sets
of an odd number of primes among $\{2,3,5,7,11,13\}$ finishes the argument. -/
@[kb "voight2021" "Theorem 25.4.1, p. 423"]
theorem classNumberOneRat_of_eichlerClassNumberFormulaRat (h : EichlerClassNumberFormulaRat) :
    ClassNumberOneRat := by
  intro a b ha hb hdef O hO
  have hf := h a b ha hb hdef O hO
  rw [clsNum_eq ha hb hdef hO, ← Nat.cast_eq_one (R := ℝ), hf]
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal)
      (ramFin ha hb : Set _) := absNorm_injective.injOn
  set S := (ramFin ha hb).image (fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal) with hS
  have hcard : S.card = (ramFin ha hb).card := Finset.card_image_of_injOn hinj
  have hp : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
    exact absNorm_prime v
  have key := arith hp (hcard ▸ odd_card_ramFin ha hb hdef)
  have p1 : ∀ f : ℕ → ℝ, ∏ v ∈ ramFin ha hb, f (Ideal.absNorm v.asIdeal) = ∏ p ∈ S, f p :=
    fun f => (Finset.prod_image hinj).symm
  have p2 : ∏ v ∈ ramFin ha hb, Ideal.absNorm v.asIdeal = ∏ p ∈ S, p :=
    (Finset.prod_image (f := fun p : ℕ => p) hinj).symm
  rw [p1 (fun p => (p : ℝ) - 1), p1 (fun p => 1 - (Siegel.kroneckerSym (-4) p : ℝ)),
    p1 (fun p => 1 - (Siegel.kroneckerSym (-3) p : ℝ)), p2]
  exact key

end QuadFormsKB.Voight.Wave5
