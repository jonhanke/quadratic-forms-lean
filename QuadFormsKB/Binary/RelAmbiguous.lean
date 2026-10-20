import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelGenusGroup

/-!
# Ambiguous ideals of a quadratic extension and the strongly ambiguous classes

$E/F$ a quadratic extension of number fields, $\sigma$ its nontrivial automorphism (`conj`), $\iota\mathfrak a = \mathfrak a\mathcal O_E$
(`Ideal.map`), $T$ the ramified primes ($\chi_{E/F}(\mathfrak p) = 0$), $\mathfrak P_\mathfrak p$ the prime of $\mathcal O_E$ over
$\mathfrak p \in T$ (`primeAbove`).

* **`map_prime_eq`**: $\iota\mathfrak p = \mathfrak P_\mathfrak p^2$ ($\mathfrak p$ ramified), $\iota\mathfrak p = \mathfrak P$ (inert),
  $\iota\mathfrak p = \mathfrak P\,\sigma\mathfrak P$ with $\mathfrak P \ne \sigma\mathfrak P$ (split) — from $N(\iota\mathfrak p) = \mathfrak p^2$ only.
* **`exists_eq_map_mul_prod`** (*ambiguous ideals*): every nonzero ideal $\mathfrak A$ of $\mathcal O_E$ with $\sigma\mathfrak A = \mathfrak A$ is
  $\iota\mathfrak a\cdot\prod_{\mathfrak p \in S}\mathfrak P_\mathfrak p$ for an ideal $\mathfrak a \ne 0$ of $\mathcal O_F$ and a set $S \subseteq T$;
  **`eq_of_map_mul_prod_eq`**: $\mathfrak a$ and $S$ are unique.
* **Hilbert 90** in integral form (`exists_hilbert90`, `exists_conj_eq_mul`).
* **`card_strongAmb_mul_index`** (CM): the group $\mathrm{Cl}_E^{\mathrm{str}}$ of classes of ambiguous ideals ("strongly ambiguous classes")
  satisfies $\#\mathrm{Cl}_E^{\mathrm{str}}\cdot[\mu_E : \{u/\sigma u\}] = 2^t\,h_F$. The map $(S, d) \mapsto \prod_{\mathfrak p\in S}[\mathfrak P_\mathfrak p]\cdot\iota(d)$,
  $S \subseteq T$, $d \in \mathrm{Cl}_F$, is onto $\mathrm{Cl}_E^{\mathrm{str}}$ and each fibre is in bijection with $\mu_E/\{u/\sigma u : u \in \mathcal O_E^\times\}$
  (Hilbert 90: $\zeta = \sigma r/r$).

Elementary: unique factorization of ideals, the relative norm, Hilbert 90 for the quadratic extension; no class field theory.

Sources: Chevalley, *Sur la théorie du corps de classes dans les corps finis et les corps locaux* (1933) (ambiguous
class number formula) [unverified]; Hilbert, *Zahlbericht* (1897), §§ 71–75 [unverified]; Lemmermeyer, *The ambiguous class
number formula revisited*, J. Ramanujan Math. Soc. 28 (2013) [unverified].
-/

open NumberField Module IsDedekindDomain
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-! ### Conjugation and extension of ideals -/

theorem conjIdeal_mul (A B : Ideal (𝓞 E)) : conjIdeal F (A * B) = conjIdeal F A * conjIdeal F B :=
  Ideal.map_mul _ _ _

theorem map_conjO_eq (I : Ideal (𝓞 E)) :
    Ideal.map (conjO F E) I = Ideal.map (conjO F E : 𝓞 E →+* 𝓞 E) I := rfl

theorem conjIdeal_conjIdeal (A : Ideal (𝓞 E)) : conjIdeal F (conjIdeal F A) = A := by
  rw [conjIdeal, conjIdeal, map_conjO_eq, map_conjO_eq, Ideal.map_map]
  have : ((conjO F E : 𝓞 E →+* 𝓞 E).comp (conjO F E : 𝓞 E →+* 𝓞 E)) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, RingHom.coe_coe]
    exact conjO_conjO x
  rw [this, Ideal.map_id]

theorem conjIdeal_injective : Function.Injective (conjIdeal F (E := E)) := fun A B h => by
  rw [← conjIdeal_conjIdeal (F := F) A, h, conjIdeal_conjIdeal]

theorem conjIdeal_map (𝔞 : Ideal (𝓞 F)) :
    conjIdeal F (𝔞.map (algebraMap (𝓞 F) (𝓞 E))) = 𝔞.map (algebraMap (𝓞 F) (𝓞 E)) := by
  rw [conjIdeal, map_conjO_eq, Ideal.map_map]
  congr 1
  exact RingHom.ext fun x => conjO_algebraMap (E := E) x


theorem conjO_ne_zero {x : 𝓞 E} (hx : x ≠ 0) : conjO F E x ≠ 0 := fun h =>
  hx ((conjO F E).injective (by rw [h, map_zero]))

theorem finrank_O : finrank (𝓞 F) (𝓞 E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, Algebra.IsQuadraticExtension.finrank_eq_two]

/-- $N_{E/F}(\iota\mathfrak a) = \mathfrak a^2$. -/
theorem relNorm_map (𝔞 : Ideal (𝓞 F)) :
    Ideal.relNorm (𝓞 F) (𝔞.map (algebraMap (𝓞 F) (𝓞 E))) = 𝔞 ^ 2 := by
  rw [Ideal.relNorm_algebraMap, finrank_O]

/-- **Extension of ideals is injective** ($N(\iota\mathfrak a) = \mathfrak a^2$). -/
theorem map_injective : Function.Injective (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 F) → Ideal (𝓞 E)) :=
  fun 𝔞 𝔟 h => ideal_pow_left_injective two_ne_zero (by
    rw [← relNorm_map (E := E) 𝔞, ← relNorm_map (E := E) 𝔟, h])

theorem map_ne_bot {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) : 𝔞.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := by
  intro h0
  apply h
  have := relNorm_map (E := E) 𝔞
  rw [h0, Ideal.relNorm_bot] at this
  exact (pow_eq_zero_iff two_ne_zero).mp this.symm

theorem eq_top_of_relNorm_eq_top {J : Ideal (𝓞 E)} (h : Ideal.relNorm (𝓞 F) J = ⊤) : J = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, ← Ideal.absNorm_relNorm (𝓞 F), h, Ideal.absNorm_top]

/-! ### Primes over $\mathfrak p$ -/

theorem nonempty_primesOver (𝔭 : HeightOneSpectrum (𝓞 F)) : Nonempty (𝔭.asIdeal.primesOver (𝓞 E)) := by
  have := 𝔭.isMaximal
  obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) 𝔭.asIdeal
  exact ⟨⟨Q, hQm.isPrime, hQ⟩⟩

variable (E) in
/-- A chosen prime $\mathfrak P_\mathfrak p$ of $\mathcal O_E$ over $\mathfrak p$ (the only one when $\mathfrak p$ is ramified or inert). -/
def primeAbove (𝔭 : HeightOneSpectrum (𝓞 F)) : 𝔭.asIdeal.primesOver (𝓞 E) :=
  Classical.choice (nonempty_primesOver 𝔭)

theorem primesOver_ne_top {𝔭 : HeightOneSpectrum (𝓞 F)} (P : 𝔭.asIdeal.primesOver (𝓞 E)) : P.1 ≠ ⊤ :=
  P.2.1.ne_top

theorem map_le_primesOver {𝔭 : HeightOneSpectrum (𝓞 F)} (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    𝔭.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.1 := by
  have := P.2.2
  exact Ideal.map_le_of_le_comap (le_of_eq (Ideal.LiesOver.over))

theorem primesOver_dvd_map {𝔭 : HeightOneSpectrum (𝓞 F)} (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    P.1 ∣ 𝔭.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) :=
  Ideal.dvd_iff_le.mpr (map_le_primesOver P)

theorem relNorm_map_prime (𝔭 : HeightOneSpectrum (𝓞 F)) :
    Ideal.relNorm (𝓞 F) (𝔭.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) = 𝔭.asIdeal ^ 2 :=
  relNorm_map 𝔭.asIdeal

theorem pow_ne_zero_prime (𝔭 : HeightOneSpectrum (𝓞 F)) (n : ℕ) : 𝔭.asIdeal ^ n ≠ 0 :=
  pow_ne_zero _ (by rw [Ne, Ideal.zero_eq_bot]; exact 𝔭.ne_bot)

/-- **Inert:** $\iota\mathfrak p = \mathfrak P$. -/
theorem map_eq_of_inert {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 = -1) (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    𝔭.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.1 := by
  obtain ⟨h', -⟩ | ⟨-, P₀, hall, -, hf⟩ | ⟨h', -⟩ :=
    splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭
  · rw [h] at h'; norm_num at h'
  · obtain ⟨J, hJ⟩ := primesOver_dvd_map P
    have hN := congrArg (Ideal.relNorm (𝓞 F)) hJ
    rw [map_mul, relNorm_map_prime, relNorm_primesOver, hall P, hf] at hN
    have hJ1 : Ideal.relNorm (𝓞 F) J = ⊤ := by
      have := mul_left_cancel₀ (pow_ne_zero_prime 𝔭 2) (hN.symm.trans (mul_one _).symm)
      rw [this, Ideal.one_eq_top]
    rw [hJ, eq_top_of_relNorm_eq_top hJ1, ← Ideal.one_eq_top, mul_one]
  · rw [h] at h'; norm_num at h'

/-- **Ramified:** $\iota\mathfrak p = \mathfrak P^2$. -/
theorem map_eq_sq_of_ramified {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 = 0)
    (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    𝔭.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.1 ^ 2 := by
  obtain ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, P₀, hall, -, hf⟩ :=
    splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · have hNP : Ideal.relNorm (𝓞 F) P.1 = 𝔭.asIdeal := by
      rw [relNorm_primesOver, hall P, hf, pow_one]
    obtain ⟨J, hJ⟩ := primesOver_dvd_map P
    have hN := congrArg (Ideal.relNorm (𝓞 F)) hJ
    rw [map_mul, relNorm_map_prime, hNP, sq] at hN
    have hJN : Ideal.relNorm (𝓞 F) J = 𝔭.asIdeal :=
      (mul_left_cancel₀ (pow_ne_zero_prime 𝔭 1 |> fun h => by simpa using h) hN).symm
    obtain ⟨Q, hQ⟩ := exists_dvd_of_dvd_relNorm 𝔭 J (by rw [hJN])
    rw [hall Q, ← hall P] at hQ
    obtain ⟨J', hJ'⟩ := hQ
    have hN2 := congrArg (Ideal.relNorm (𝓞 F)) hJ'
    rw [map_mul, hJN, hNP] at hN2
    have hJ'1 : Ideal.relNorm (𝓞 F) J' = ⊤ := by
      have := mul_left_cancel₀ (pow_ne_zero_prime 𝔭 1 |> fun h => by simpa using h)
        (hN2.symm.trans (mul_one _).symm)
      rw [this, Ideal.one_eq_top]
    rw [hJ, hJ', eq_top_of_relNorm_eq_top hJ'1, ← Ideal.one_eq_top, mul_one, sq]

theorem conjIdeal_le {A B : Ideal (𝓞 E)} (h : A ≤ B) : conjIdeal F A ≤ conjIdeal F B := Ideal.map_mono h

def conjIdeal_primesOver {𝔭 : HeightOneSpectrum (𝓞 F)} (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    𝔭.asIdeal.primesOver (𝓞 E) := ⟨conjIdeal F P.1, conjIdeal_mem_primesOver 𝔭.asIdeal P⟩

/-- **Split:** $\sigma\mathfrak P \ne \mathfrak P$ and $\iota\mathfrak p = \mathfrak P\,\sigma\mathfrak P$. -/
theorem map_eq_mul_conj_of_split {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 = 1)
    (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    conjIdeal F P.1 ≠ P.1 ∧ 𝔭.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.1 * conjIdeal F P.1 := by
  obtain ⟨-, P₀, P₁, h01, hall, -, hf0, -, hf1⟩ | ⟨h', -⟩ | ⟨h', -⟩ :=
    splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭
  swap
  · rw [h] at h'; norm_num at h'
  swap
  · rw [h] at h'; norm_num at h'
  have hf : ∀ Q : 𝔭.asIdeal.primesOver (𝓞 E), Q.1.inertiaDeg (𝓞 F) = 1 := fun Q => by
    rcases hall Q with rfl | rfl <;> assumption
  -- the other prime
  obtain ⟨Q, hQP, hQall⟩ : ∃ Q : 𝔭.asIdeal.primesOver (𝓞 E), Q ≠ P ∧ ∀ R, R = P ∨ R = Q := by
    rcases hall P with rfl | rfl
    · exact ⟨P₁, h01.symm, fun R => hall R⟩
    · exact ⟨P₀, h01, fun R => (hall R).symm⟩
  have hPm := isMaximal_of_primesOver P
  have hQm := isMaximal_of_primesOver Q
  have hne : P.1 ≠ Q.1 := fun e => hQP (Subtype.ext e.symm)
  have hσne : conjIdeal F P.1 ≠ P.1 := by
    intro hσ
    have hσQ : conjIdeal F Q.1 = Q.1 := by
      rcases hQall (conjIdeal_primesOver Q) with e | e
      · exfalso
        have e' : conjIdeal F Q.1 = conjIdeal F P.1 := by rw [hσ]; exact congrArg Subtype.val e
        exact hne (conjIdeal_injective e').symm
      · exact congrArg Subtype.val e
    obtain ⟨x, hxP, hxQ⟩ : ∃ x ∈ P.1, x ∉ Q.1 := by
      by_contra hc
      push Not at hc
      exact hne (hPm.eq_of_le hQm.ne_top hc)
    have hN : algebraMap (𝓞 F) (𝓞 E) (Algebra.intNorm (𝓞 F) (𝓞 E) x) ∈ P.1 := by
      rw [algebraMap_intNorm_eq]; exact P.1.mul_mem_right _ hxP
    have hP𝔭 : Algebra.intNorm (𝓞 F) (𝓞 E) x ∈ 𝔭.asIdeal := by
      have := (P.2.2 : P.1.LiesOver 𝔭.asIdeal).over
      rw [this]; exact hN
    have hQ' : algebraMap (𝓞 F) (𝓞 E) (Algebra.intNorm (𝓞 F) (𝓞 E) x) ∈ Q.1 :=
      map_le_primesOver Q (Ideal.mem_map_of_mem _ hP𝔭)
    rw [algebraMap_intNorm_eq] at hQ'
    rcases hQm.isPrime.mem_or_mem hQ' with h1 | h1
    · exact hxQ h1
    · apply hxQ
      have : conjO F E (conjO F E x) ∈ conjIdeal F Q.1 := Ideal.mem_map_of_mem _ h1
      rwa [conjO_conjO, hσQ] at this
  refine ⟨hσne, ?_⟩
  have hσm : (conjIdeal F P.1).IsMaximal := isMaximal_of_primesOver (conjIdeal_primesOver P)
  have hcop : IsCoprime P.1 (conjIdeal F P.1) := Ideal.isCoprime_of_isMaximal hσne.symm
  obtain ⟨J, hJ⟩ := hcop.mul_dvd (primesOver_dvd_map P) (primesOver_dvd_map (conjIdeal_primesOver P))
  have hN := congrArg (Ideal.relNorm (𝓞 F)) hJ
  have hNP : Ideal.relNorm (𝓞 F) P.1 = 𝔭.asIdeal := by rw [relNorm_primesOver, hf P, pow_one]
  rw [map_mul, map_mul, relNorm_map_prime, relNorm_conjIdeal, hNP, ← sq] at hN
  have hJ1 : Ideal.relNorm (𝓞 F) J = ⊤ := by
    have := mul_left_cancel₀ (pow_ne_zero_prime 𝔭 2) (hN.symm.trans (mul_one _).symm)
    rw [this, Ideal.one_eq_top]
  rw [hJ, eq_top_of_relNorm_eq_top hJ1, ← Ideal.one_eq_top, mul_one]

/-- **At an unramified prime, $\iota\mathfrak p$ divides every ambiguous ideal divisible by a prime over $\mathfrak p$.** -/
theorem map_dvd_of_unramified {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 ≠ 0)
    (P : 𝔭.asIdeal.primesOver (𝓞 E)) {A : Ideal (𝓞 E)} (hA : conjIdeal F A = A) (hP : P.1 ∣ A) :
    𝔭.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ∣ A := by
  rcases relChar_mem (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭 with h1 | h1 | h1
  · obtain ⟨hσne, he⟩ := map_eq_mul_conj_of_split h1 P
    rw [he]
    have hσm : (conjIdeal F P.1).IsMaximal := isMaximal_of_primesOver (conjIdeal_primesOver P)
    have := isMaximal_of_primesOver P
    have hcop : IsCoprime P.1 (conjIdeal F P.1) := Ideal.isCoprime_of_isMaximal hσne.symm
    refine hcop.mul_dvd hP ?_
    rw [Ideal.dvd_iff_le] at hP ⊢
    rw [← hA]; exact conjIdeal_le hP
  · rw [map_eq_of_inert h1 P]; exact hP
  · exact absurd h1 h

/-- The prime $\mathfrak P$ over a ramified $\mathfrak p$ is the chosen one, and is $\sigma$-invariant. -/
theorem eq_primeAbove_of_ramified {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 = 0)
    (P : 𝔭.asIdeal.primesOver (𝓞 E)) : P = primeAbove E 𝔭 := by
  obtain ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, P₀, hall, -, -⟩ :=
    splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭
  · rw [h] at h'; norm_num at h'
  · rw [h] at h'; norm_num at h'
  · rw [hall P, hall (primeAbove E 𝔭)]

theorem conjIdeal_primeAbove {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 = 0) :
    conjIdeal F (primeAbove E 𝔭).1 = (primeAbove E 𝔭).1 :=
  congrArg Subtype.val (eq_primeAbove_of_ramified h (conjIdeal_primesOver (primeAbove E 𝔭)))

theorem sq_primeAbove {𝔭 : HeightOneSpectrum (𝓞 F)} (h : relChar E 𝔭 = 0) :
    (primeAbove E 𝔭).1 ^ 2 = 𝔭.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) :=
  (map_eq_sq_of_ramified h _).symm

/-! ### Ambiguous ideals -/

theorem ideal_map_prod {R S ι : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (s : Finset ι)
    (g : ι → Ideal R) : Ideal.map f (∏ i ∈ s, g i) = ∏ i ∈ s, Ideal.map f (g i) :=
  map_prod (Ideal.mapHom f) g s

variable (E) in
/-- $\prod_{\mathfrak p \in S}\mathfrak P_\mathfrak p$. -/
def ramProd (S : Finset (HeightOneSpectrum (𝓞 F))) : Ideal (𝓞 E) := ∏ 𝔭 ∈ S, (primeAbove E 𝔭).1

theorem ramProd_ne_bot (S : Finset (HeightOneSpectrum (𝓞 F))) : ramProd E S ≠ ⊥ := by
  rw [ramProd, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro 𝔭 _
  rw [Ne, Ideal.zero_eq_bot]
  exact primesOver_ne_bot 𝔭 _

theorem conjIdeal_ramProd {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ 𝔭 ∈ S, relChar E 𝔭 = 0) :
    conjIdeal F (ramProd E S) = ramProd E S := by
  rw [ramProd, conjIdeal, map_conjO_eq, ideal_map_prod]
  refine Finset.prod_congr rfl (fun 𝔭 h𝔭 => ?_)
  rw [← map_conjO_eq]
  exact conjIdeal_primeAbove (hS 𝔭 h𝔭)

/-- $(\prod_{\mathfrak p\in S}\mathfrak P_\mathfrak p)^2 = \iota\prod_{\mathfrak p \in S}\mathfrak p$. -/
theorem ramProd_sq {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ 𝔭 ∈ S, relChar E 𝔭 = 0) :
    ramProd E S ^ 2 = (∏ 𝔭 ∈ S, 𝔭.asIdeal).map (algebraMap (𝓞 F) (𝓞 E)) := by
  rw [ramProd, ← Finset.prod_pow, ideal_map_prod]
  exact Finset.prod_congr rfl (fun 𝔭 h𝔭 => sq_primeAbove (hS 𝔭 h𝔭))

/-- Peeling off an invariant factor: if $\mathfrak A = \mathfrak X\mathfrak A'$ with $\sigma\mathfrak X = \mathfrak X \ne 0, (1)$ and $\sigma\mathfrak A = \mathfrak A \ne 0$,
then $\sigma\mathfrak A' = \mathfrak A' \ne 0$ and $N\mathfrak A' < N\mathfrak A$. -/
theorem peel {A X A' : Ideal (𝓞 E)} (hA : A ≠ ⊥) (hσ : conjIdeal F A = A) (hX : conjIdeal F X = X)
    (hXt : X ≠ ⊤) (h : A = X * A') :
    A' ≠ ⊥ ∧ conjIdeal F A' = A' ∧ Ideal.absNorm A' < Ideal.absNorm A := by
  have hX0 : X ≠ ⊥ := fun h0 => hA (by rw [h, h0, Ideal.bot_mul])
  have hA'0 : A' ≠ ⊥ := fun h0 => hA (by rw [h, h0, Ideal.mul_bot])
  refine ⟨hA'0, ?_, ?_⟩
  · have e : X * conjIdeal F A' = X * A' := by
      calc X * conjIdeal F A' = conjIdeal F X * conjIdeal F A' := by rw [hX]
        _ = conjIdeal F A := by rw [← conjIdeal_mul, h]
        _ = X * A' := by rw [hσ, h]
    exact mul_left_cancel₀ (by rwa [Ne, Ideal.zero_eq_bot]) e
  · rw [h, map_mul]
    have h1 : Ideal.absNorm X ≠ 1 := fun e => hXt (Ideal.absNorm_eq_one_iff.mp e)
    have h0 : Ideal.absNorm X ≠ 0 := fun e => hX0 (Ideal.absNorm_eq_zero_iff.mp e)
    have h0' : Ideal.absNorm A' ≠ 0 := fun e => hA'0 (Ideal.absNorm_eq_zero_iff.mp e)
    have : 2 ≤ Ideal.absNorm X := by omega
    nlinarith [Nat.pos_of_ne_zero h0']

/-- **Ambiguous ideals** (existence): every nonzero ideal $\mathfrak A$ of $\mathcal O_E$ with $\sigma\mathfrak A = \mathfrak A$ is
$\iota\mathfrak a\cdot\prod_{\mathfrak p \in S}\mathfrak P_\mathfrak p$ with $\mathfrak a \ne 0$ an ideal of $\mathcal O_F$ and $S$ a set of ramified primes. -/
@[kb "hilbert1897" "Zahlbericht §§71–75 (ambiguous ideals) [unverified]"]
theorem exists_eq_map_mul_ramProd {A : Ideal (𝓞 E)} (hA : A ≠ ⊥) (hσ : conjIdeal F A = A) :
    ∃ (𝔞 : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))), 𝔞 ≠ ⊥ ∧ (∀ 𝔭 ∈ S, relChar E 𝔭 = 0) ∧
      A = 𝔞.map (algebraMap (𝓞 F) (𝓞 E)) * ramProd E S := by
  classical
  induction hn : Ideal.absNorm A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  by_cases htop : A = ⊤
  · exact ⟨⊤, ∅, top_ne_bot, by simp, by simp [ramProd, htop, Ideal.map_top]⟩
  obtain ⟨M, hMm, hAM⟩ := Ideal.exists_le_maximal A htop
  have hM0 : M ≠ ⊥ := fun h => hA (le_bot_iff.mp (h ▸ hAM))
  let w : HeightOneSpectrum (𝓞 E) := ⟨M, hMm.isPrime, hM0⟩
  have hlo : w.asIdeal.LiesOver (HN.under (F := F) w).asIdeal := ⟨rfl⟩
  obtain ⟨𝔭, h𝔭⟩ : ∃ 𝔭, 𝔭 = HN.under (F := F) w := ⟨_, rfl⟩
  let P : 𝔭.asIdeal.primesOver (𝓞 E) := ⟨M, hMm.isPrime, h𝔭 ▸ hlo⟩
  have hPA : P.1 ∣ A := Ideal.dvd_iff_le.mpr hAM
  by_cases hr : relChar E 𝔭 = 0
  · have hPe : P = primeAbove E 𝔭 := eq_primeAbove_of_ramified hr P
    obtain ⟨A', hA'⟩ := hPA
    obtain ⟨hA'0, hσ', hlt⟩ := peel hA hσ (by rw [hPe]; exact conjIdeal_primeAbove hr) (primesOver_ne_top P) hA'
    obtain ⟨𝔞', S', h𝔞', hS', he⟩ := ih _ (hn ▸ hlt) hA'0 hσ' rfl
    rw [hPe] at hA'
    by_cases h𝔭S : 𝔭 ∈ S'
    · refine ⟨𝔞' * 𝔭.asIdeal, S'.erase 𝔭, mul_ne_zero h𝔞' 𝔭.ne_bot,
        fun 𝔮 h𝔮 => hS' 𝔮 (Finset.mem_of_mem_erase h𝔮), ?_⟩
      rw [hA', he, ramProd, ramProd, ← Finset.mul_prod_erase S' _ h𝔭S, Ideal.map_mul, ← sq_primeAbove hr]
      ring
    · refine ⟨𝔞', insert 𝔭 S', h𝔞', fun 𝔮 h𝔮 => ?_, ?_⟩
      · rcases Finset.mem_insert.mp h𝔮 with rfl | h
        · exact hr
        · exact hS' 𝔮 h
      · rw [hA', he, ramProd, ramProd, Finset.prod_insert h𝔭S]
        ring
  · obtain ⟨A', hA'⟩ := map_dvd_of_unramified hr P hσ hPA
    have hXt : 𝔭.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊤ := fun e =>
      primesOver_ne_top P (top_le_iff.mp (e ▸ map_le_primesOver P))
    obtain ⟨hA'0, hσ', hlt⟩ := peel hA hσ (conjIdeal_map _) hXt hA'
    obtain ⟨𝔞', S', h𝔞', hS', he⟩ := ih _ (hn ▸ hlt) hA'0 hσ' rfl
    refine ⟨𝔭.asIdeal * 𝔞', S', mul_ne_zero 𝔭.ne_bot h𝔞', hS', ?_⟩
    rw [hA', he, Ideal.map_mul]
    ring

open Classical in
theorem count_normalizedFactors_prod (S : Finset (HeightOneSpectrum (𝓞 F))) (𝔮 : HeightOneSpectrum (𝓞 F)) :
    Multiset.count 𝔮.asIdeal (UniqueFactorizationMonoid.normalizedFactors (∏ 𝔭 ∈ S, 𝔭.asIdeal)) =
      if 𝔮 ∈ S then 1 else 0 := by
  classical
  have hinj : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 F) → Ideal (𝓞 F)) :=
    fun a b h => HeightOneSpectrum.ext h
  rw [Finset.prod_eq_multiset_prod, UniqueFactorizationMonoid.normalizedFactors_prod_of_prime, ]
  · rw [Multiset.count_map_eq_count' _ _ hinj]
    split_ifs with h
    · exact Multiset.count_eq_one_of_mem S.nodup h
    · exact Multiset.count_eq_zero.mpr h
  · intro p hp
    obtain ⟨𝔭, -, rfl⟩ := Multiset.mem_map.mp hp
    exact Ideal.prime_of_isPrime 𝔭.ne_bot 𝔭.isPrime

theorem prod_asIdeal_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) : (∏ 𝔭 ∈ S, 𝔭.asIdeal) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ => by rw [Ne, Ideal.zero_eq_bot]; exact 𝔭.ne_bot)

open Classical in
theorem count_sq_mul_prod {𝔞 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (𝔮 : HeightOneSpectrum (𝓞 F)) :
    Multiset.count 𝔮.asIdeal (UniqueFactorizationMonoid.normalizedFactors (𝔞 ^ 2 * ∏ 𝔭 ∈ S, 𝔭.asIdeal)) =
      2 * Multiset.count 𝔮.asIdeal (UniqueFactorizationMonoid.normalizedFactors 𝔞) + if 𝔮 ∈ S then 1 else 0 := by
  rw [UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero 2 (by rwa [Ne, Ideal.zero_eq_bot]))
    (prod_asIdeal_ne_zero S), Multiset.count_add, UniqueFactorizationMonoid.normalizedFactors_pow,
    Multiset.count_nsmul, count_normalizedFactors_prod]

/-- **Ambiguous ideals** (uniqueness): $\iota\mathfrak a\prod_{S}\mathfrak P_\mathfrak p = \iota\mathfrak b\prod_{S'}\mathfrak P_\mathfrak p$ ($S, S'$ ramified,
$\mathfrak a \ne 0$) forces $\mathfrak a = \mathfrak b$ and $S = S'$. (Square: $\iota(\mathfrak a^2\prod_S\mathfrak p) = \iota(\mathfrak b^2\prod_{S'}\mathfrak p)$; $\iota$ is
injective; compare the parity of $v_\mathfrak p$.) -/
theorem eq_of_map_mul_ramProd_eq {𝔞 𝔟 : Ideal (𝓞 F)} {S S' : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ 𝔭 ∈ S, relChar E 𝔭 = 0) (hS' : ∀ 𝔭 ∈ S', relChar E 𝔭 = 0) (h𝔞 : 𝔞 ≠ ⊥)
    (h : 𝔞.map (algebraMap (𝓞 F) (𝓞 E)) * ramProd E S = 𝔟.map (algebraMap (𝓞 F) (𝓞 E)) * ramProd E S') :
    𝔞 = 𝔟 ∧ S = S' := by
  classical
  have hsq := congrArg (· ^ 2) h
  simp only [mul_pow, ramProd_sq hS, ramProd_sq hS', ← Ideal.map_pow, ← Ideal.map_mul] at hsq
  have hN := map_injective (E := E) hsq
  have h𝔟 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [← Ideal.zero_eq_bot, zero_pow two_ne_zero, zero_mul] at hN
    exact mul_ne_zero (pow_ne_zero 2 (by rwa [Ne, Ideal.zero_eq_bot])) (prod_asIdeal_ne_zero S) hN
  have hSS : S = S' := by
    ext 𝔮
    have hc := congrArg (Multiset.count 𝔮.asIdeal ∘ UniqueFactorizationMonoid.normalizedFactors) hN
    simp only [Function.comp_apply, count_sq_mul_prod h𝔞, count_sq_mul_prod h𝔟] at hc
    split_ifs at hc with h1 h2 h2 <;> first | exact iff_of_true h1 h2 | exact iff_of_false h1 h2 | omega
  subst hSS
  refine ⟨ideal_pow_left_injective two_ne_zero (mul_right_cancel₀ (prod_asIdeal_ne_zero S) hN), rfl⟩

/-! ### Hilbert 90 -/

theorem algebraMap_O_E (m : 𝓞 F) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) m) = algebraMap F E (algebraMap (𝓞 F) F m) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, ← IsScalarTower.algebraMap_apply (𝓞 F) F E]

theorem nrm_conjO (x : 𝓞 E) : nrm (F := F) (conjO F E x) = nrm (F := F) x := by
  rw [nrm, nrm, algebraMap_conjO, norm_conj]

theorem intNorm_conjO (x : 𝓞 E) :
    Algebra.intNorm (𝓞 F) (𝓞 E) (conjO F E x) = Algebra.intNorm (𝓞 F) (𝓞 E) x := by
  apply FaithfulSMul.algebraMap_injective (𝓞 F) F
  rw [algebraMap_intNorm', algebraMap_intNorm', nrm, nrm, algebraMap_conjO, norm_conj]

/-- **Hilbert 90** (integral form): if $N x = N y$, $x \ne 0$, then $r\,\sigma(x) = y\,\sigma(r)$ for some $r \ne 0$ in $\mathcal O_E$
($r = x + y$, or $r = \theta x$ if $y = -x$). -/
@[kb "neukirch1999" "Ch. IV, Thm. 3.5 (Hilbert 90) [unverified]"]
theorem exists_hilbert90 {x y : 𝓞 E} (hx : x ≠ 0)
    (hN : Algebra.intNorm (𝓞 F) (𝓞 E) x = Algebra.intNorm (𝓞 F) (𝓞 E) y) :
    ∃ r : 𝓞 E, r ≠ 0 ∧ r * conjO F E x = y * conjO F E r := by
  have hxy : x * conjO F E x = y * conjO F E y := by
    rw [← algebraMap_intNorm_eq, ← algebraMap_intNorm_eq, hN]
  by_cases h0 : x + y = 0
  · have hy : y = -x := eq_neg_of_add_eq_zero_right h0
    have hθ : relGen F E ≠ 0 := fun h => relGen_ne_zero (F := F) (E := E) (by rw [h]; simp)
    refine ⟨relGen F E * x, mul_ne_zero hθ hx, ?_⟩
    rw [map_mul, conjO_relGen, hy]
    ring
  · refine ⟨x + y, h0, ?_⟩
    rw [map_add]
    linear_combination hxy

/-- **Hilbert 90 for a unit of norm one:** $N\zeta = 1 \Rightarrow \sigma r = \zeta r$ for some $r \ne 0$ in $\mathcal O_E$. -/
theorem exists_conj_eq_mul {ζ : 𝓞 E} (hζ : Algebra.intNorm (𝓞 F) (𝓞 E) ζ = 1) :
    ∃ r : 𝓞 E, r ≠ 0 ∧ conjO F E r = ζ * r := by
  obtain ⟨r, hr, h⟩ := exists_hilbert90 (F := F) (x := 1) (y := conjO F E ζ) one_ne_zero
    (by rw [intNorm_conjO, hζ, map_one])
  refine ⟨r, hr, ?_⟩
  rw [map_one, mul_one] at h
  have := congrArg (conjO F E) h
  rw [map_mul, conjO_conjO, conjO_conjO] at this
  exact this

/-- **Eigenvectors of $\sigma$ with the same eigenvalue are $F$-proportional:** $\sigma r = \zeta r$, $\sigma y = \zeta y$ ($r, y \ne 0$) give
$s\,y = m\,r$ with $m, s \in \mathcal O_F \setminus 0$. -/
theorem exists_proportional {ζ r y : 𝓞 E} (hr : r ≠ 0) (hy : y ≠ 0) (h1 : conjO F E r = ζ * r)
    (h2 : conjO F E y = ζ * y) :
    ∃ m s : 𝓞 F, m ≠ 0 ∧ s ≠ 0 ∧ algebraMap (𝓞 F) (𝓞 E) s * y = algebraMap (𝓞 F) (𝓞 E) m * r := by
  have hrE : algebraMap (𝓞 E) E r ≠ 0 := algebraMap_ne_zero hr
  have hyE : algebraMap (𝓞 E) E y ≠ 0 := algebraMap_ne_zero hy
  have hζ : algebraMap (𝓞 E) E ζ ≠ 0 := by
    intro h0
    have := congrArg (algebraMap (𝓞 E) E) h1
    rw [map_mul, h0, zero_mul, algebraMap_conjO] at this
    exact hrE ((conj F E).injective (by rw [this, map_zero]))
  set z := algebraMap (𝓞 E) E y / algebraMap (𝓞 E) E r
  have hz : conj F E z = z := by
    have e1 := congrArg (algebraMap (𝓞 E) E) h1
    have e2 := congrArg (algebraMap (𝓞 E) E) h2
    rw [algebraMap_conjO, map_mul] at e1 e2
    rw [map_div₀, e1, e2, mul_div_mul_left _ _ hζ]
  obtain ⟨a, ha⟩ := (conj_eq_self_iff z).mp hz
  obtain ⟨m, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsF : algebraMap (𝓞 F) F s ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hs0
  have key : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) s * y) =
      algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) m * r) := by
    rw [map_mul, map_mul, algebraMap_O_E, algebraMap_O_E]
    have : algebraMap (𝓞 E) E y = algebraMap F E (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F s) *
        algebraMap (𝓞 E) E r := by
      rw [ha, div_mul_cancel₀ _ hrE]
    rw [this, map_div₀]
    have : algebraMap F E (algebraMap (𝓞 F) F s) ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr hsF
    field_simp
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul, map_zero, map_mul] at key
    exact mul_ne_zero (by rw [algebraMap_O_E]; exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr hsF) hyE key
  exact ⟨m, s, hm0, hs0, FaithfulSMul.algebraMap_injective (𝓞 E) E key⟩

/-! ### Strongly ambiguous classes -/

variable {T : Finset (HeightOneSpectrum (𝓞 F))}

variable (T) in
/-- The parameter set $\{S \subseteq T\} \times \mathrm{Cl}_F$. -/
abbrev AmbDom := T.powerset × ClassGroup (𝓞 F)

theorem ramified_of_mem (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) (S : T.powerset) : ∀ 𝔭 ∈ S.1, relChar E 𝔭 = 0 :=
  fun 𝔭 h => (hT 𝔭).mp (Finset.mem_powerset.mp S.2 h)

variable (E) in
/-- The ambiguous ideal $\iota\mathfrak a_d\cdot\prod_{\mathfrak p\in S}\mathfrak P_\mathfrak p$ of $(S, d)$ ($\mathfrak a_d$ = `classRep F d`). -/
def ambIdeal (x : AmbDom T) : Ideal (𝓞 E) :=
  (classRep F x.2 : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) * ramProd E x.1.1

theorem ambIdeal_ne_bot (x : AmbDom T) : ambIdeal E x ≠ ⊥ := by
  rw [ambIdeal, ← Ideal.zero_eq_bot]
  refine mul_ne_zero ?_ ?_
  · rw [Ne, Ideal.zero_eq_bot]; exact map_ne_bot (classRep_ne_bot x.2)
  · rw [Ne, Ideal.zero_eq_bot]; exact ramProd_ne_bot _

theorem conjIdeal_ambIdeal (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) (x : AmbDom T) :
    conjIdeal F (ambIdeal E x) = ambIdeal E x := by
  rw [ambIdeal, conjIdeal_mul, conjIdeal_map, conjIdeal_ramProd (ramified_of_mem hT x.1)]

variable (E) in
/-- $(S, d) \mapsto [\iota\mathfrak a_d\prod_{S}\mathfrak P_\mathfrak p] \in \mathrm{Cl}_E$. -/
def ambClass (x : AmbDom T) : ClassGroup (𝓞 E) :=
  ClassGroup.mk0 ⟨ambIdeal E x, mem_nonZeroDivisors_of_ne_zero (ambIdeal_ne_bot x)⟩

variable (F) in
/-- **Strongly ambiguous classes:** classes of ideals $\mathfrak A$ with $\sigma\mathfrak A = \mathfrak A$. -/
def IsStrAmb (c : ClassGroup (𝓞 E)) : Prop :=
  ∃ A : (Ideal (𝓞 E))⁰, conjIdeal F (A : Ideal (𝓞 E)) = A ∧ ClassGroup.mk0 A = c

theorem isStrAmb_ambClass (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) (x : AmbDom T) : IsStrAmb F (ambClass E x) :=
  ⟨⟨ambIdeal E x, mem_nonZeroDivisors_of_ne_zero (ambIdeal_ne_bot x)⟩, conjIdeal_ambIdeal hT x, rfl⟩

theorem mk0_span_mul {R : Type*} [CommRing R] [IsDedekindDomain R] {a : R} (ha : a ≠ 0) (I : (Ideal R)⁰)
    (h : Ideal.span {a} * (I : Ideal R) ∈ (Ideal R)⁰) :
    ClassGroup.mk0 ⟨Ideal.span {a} * (I : Ideal R), h⟩ = ClassGroup.mk0 I :=
  ClassGroup.mk0_eq_mk0_iff.mpr ⟨1, a, one_ne_zero, ha, by rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, one_mul]⟩

theorem map_span_singleton (m : 𝓞 F) :
    (Ideal.span {m}).map (algebraMap (𝓞 F) (𝓞 E)) = Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} := by
  rw [Ideal.map_span, Set.image_singleton]

theorem algebraMap_O_ne_zero {m : 𝓞 F} (hm : m ≠ 0) : algebraMap (𝓞 F) (𝓞 E) m ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).mpr hm

/-- The decomposition $(S, [\mathfrak a])$ of an ambiguous ideal $\mathfrak A = \iota\mathfrak a\prod_S\mathfrak P_\mathfrak p$ (chosen; unique by
`eq_of_map_mul_ramProd_eq`). -/
def decOf (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) (A : Ideal (𝓞 E)) (hA : A ≠ ⊥) (hσ : conjIdeal F A = A) :
    AmbDom T :=
  ⟨⟨(exists_eq_map_mul_ramProd hA hσ).choose_spec.choose, Finset.mem_powerset.mpr (fun 𝔭 h =>
      (hT 𝔭).mpr ((exists_eq_map_mul_ramProd hA hσ).choose_spec.choose_spec.2.1 𝔭 h))⟩,
    ClassGroup.mk0 ⟨(exists_eq_map_mul_ramProd hA hσ).choose,
      mem_nonZeroDivisors_of_ne_zero (exists_eq_map_mul_ramProd hA hσ).choose_spec.choose_spec.1⟩⟩

theorem decOf_spec (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {A : Ideal (𝓞 E)} (hA : A ≠ ⊥)
    (hσ : conjIdeal F A = A) :
    ∃ 𝔞 : (Ideal (𝓞 F))⁰, (∀ 𝔭 ∈ (decOf hT A hA hσ).1.1, relChar E 𝔭 = 0) ∧
      (decOf hT A hA hσ).2 = ClassGroup.mk0 𝔞 ∧
      A = (𝔞 : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) * ramProd E (decOf hT A hA hσ).1.1 :=
  ⟨⟨_, mem_nonZeroDivisors_of_ne_zero (exists_eq_map_mul_ramProd hA hσ).choose_spec.choose_spec.1⟩,
    (exists_eq_map_mul_ramProd hA hσ).choose_spec.choose_spec.2.1, rfl,
    (exists_eq_map_mul_ramProd hA hσ).choose_spec.choose_spec.2.2⟩

/-- **The decomposition of an explicit ambiguous ideal.** -/
theorem decOf_eq (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {A : Ideal (𝓞 E)} (hA : A ≠ ⊥) (hσ : conjIdeal F A = A)
    (𝔞 : (Ideal (𝓞 F))⁰) (S : T.powerset)
    (he : A = (𝔞 : Ideal (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) * ramProd E S.1) :
    decOf hT A hA hσ = (S, ClassGroup.mk0 𝔞) := by
  obtain ⟨𝔞₀, hS₀, h2, he₀⟩ := decOf_spec hT hA hσ
  obtain ⟨h1, h3⟩ := eq_of_map_mul_ramProd_eq hS₀ (ramified_of_mem hT S) (nonZeroDivisors.coe_ne_zero 𝔞₀)
    (he₀.symm.trans he)
  refine Prod.ext (Subtype.ext h3) ?_
  rw [h2]
  congr 1
  exact Subtype.ext h1

/-- **When two ambiguous ideals have the same decomposition:** iff $m\mathfrak A = s\mathfrak A'$ with $m, s \in \mathcal O_F \setminus 0$. -/
theorem decOf_eq_iff (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {A A' : Ideal (𝓞 E)} (hA : A ≠ ⊥)
    (hσ : conjIdeal F A = A) (hA' : A' ≠ ⊥) (hσ' : conjIdeal F A' = A') :
    decOf hT A hA hσ = decOf hT A' hA' hσ' ↔
      ∃ m s : 𝓞 F, m ≠ 0 ∧ s ≠ 0 ∧ Ideal.span {algebraMap (𝓞 F) (𝓞 E) m} * A =
        Ideal.span {algebraMap (𝓞 F) (𝓞 E) s} * A' := by
  obtain ⟨𝔞, hS, h2, he⟩ := decOf_spec hT hA hσ
  obtain ⟨𝔞', hS', h2', he'⟩ := decOf_spec hT hA' hσ'
  constructor
  · intro h
    have hS1 : (decOf hT A hA hσ).1.1 = (decOf hT A' hA' hσ').1.1 := by rw [h]
    have hc : ClassGroup.mk0 𝔞 = ClassGroup.mk0 𝔞' := by rw [← h2, ← h2', h]
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hc
    refine ⟨x, y, hx, hy, ?_⟩
    rw [he, he', ← hS1, ← map_span_singleton, ← map_span_singleton, ← mul_assoc, ← mul_assoc,
      ← Ideal.map_mul, ← Ideal.map_mul, hxy]
  · rintro ⟨m, s, hm, hs, h⟩
    rw [he, he', ← map_span_singleton, ← map_span_singleton, ← mul_assoc, ← mul_assoc,
      ← Ideal.map_mul, ← Ideal.map_mul] at h
    have hne : Ideal.span {m} * (𝔞 : Ideal (𝓞 F)) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact mul_ne_zero (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hm)
        (by rw [Ne, Ideal.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero 𝔞)
    obtain ⟨h1, h3⟩ := eq_of_map_mul_ramProd_eq hS hS' hne h
    refine Prod.ext (Subtype.ext h3) ?_
    rw [h2, h2']
    exact ClassGroup.mk0_eq_mk0_iff.mpr ⟨m, s, hm, hs, h1⟩

/-- $\mathrm{ambClass}(\mathrm{dec}\,\mathfrak A) = [\mathfrak A]$. -/
theorem ambClass_decOf (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {A : Ideal (𝓞 E)} (hA : A ≠ ⊥)
    (hσ : conjIdeal F A = A) :
    ambClass E (decOf hT A hA hσ) = ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero hA⟩ := by
  obtain ⟨𝔞, -, h2, he⟩ := decOf_spec hT hA hσ
  have hc : ClassGroup.mk0 (classRep F (decOf hT A hA hσ).2) = ClassGroup.mk0 𝔞 := by rw [mk0_classRep, h2]
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hc
  refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨algebraMap (𝓞 F) (𝓞 E) x, algebraMap (𝓞 F) (𝓞 E) y,
    algebraMap_O_ne_zero hx, algebraMap_O_ne_zero hy, ?_⟩
  show Ideal.span {algebraMap (𝓞 F) (𝓞 E) x} * ambIdeal E (decOf hT A hA hσ) = Ideal.span {algebraMap (𝓞 F) (𝓞 E) y} * A
  conv_rhs => rw [he]
  rw [ambIdeal, ← map_span_singleton, ← map_span_singleton, ← mul_assoc, ← mul_assoc,
    ← Ideal.map_mul, ← Ideal.map_mul, hxy]

/-! ### Counting strongly ambiguous classes (CM) -/

section CM

variable [IsTotallyReal F] [IsTotallyComplex E]

open NumberField.Units

variable (F E) in
/-- $\sigma$ on $\mathcal O_E^\times$. -/
def conjUnits : (𝓞 E)ˣ →* (𝓞 E)ˣ := Units.map (conjO F E : 𝓞 E →+* 𝓞 E).toMonoidHom

theorem coe_conjUnits (u : (𝓞 E)ˣ) : ((conjUnits F E u : (𝓞 E)ˣ) : 𝓞 E) = conjO F E u := rfl

theorem nrm_unit_mul_inv (u : (𝓞 E)ˣ) : nrm (F := F) ((u : 𝓞 E)) * nrm (F := F) ((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = 1 := by
  rw [← nrm_mul, Units.mul_inv]; simp [nrm]

theorem mem_torsion_of_nrm {u : (𝓞 E)ˣ} (h : nrm (F := F) (u : 𝓞 E) = 1) : u ∈ torsion E :=
  (normOneUnits_eq_torsion (F := F) u).mp h

theorem nrm_torsion (ζ : torsion E) : nrm (F := F) (((ζ : (𝓞 E)ˣ) : 𝓞 E)) = 1 :=
  (normOneUnits_eq_torsion (F := F) (ζ : (𝓞 E)ˣ)).mpr ζ.2

theorem intNorm_torsion (ζ : torsion E) : Algebra.intNorm (𝓞 F) (𝓞 E) ((ζ : (𝓞 E)ˣ) : 𝓞 E) = 1 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 F) F
  rw [algebraMap_intNorm', nrm_torsion, map_one]

variable (F E) in
/-- **$u \mapsto u\,\sigma(u)^{-1}$**, $\mathcal O_E^\times \to \mu_E$ (its values have norm $1$). Its range is the group $\{u/\sigma u\}$. -/
def unitsMulConjInv : (𝓞 E)ˣ →* torsion E where
  toFun u := ⟨u * (conjUnits F E u)⁻¹, mem_torsion_of_nrm (F := F) (by
    rw [Units.val_mul, nrm_mul]
    have h1 := nrm_unit_mul_inv (F := F) (conjUnits F E u)
    rw [coe_conjUnits, nrm_conjO] at h1
    exact h1)⟩
  map_one' := by ext; simp
  map_mul' u v := by
    apply Subtype.ext
    show (u * v) * (conjUnits F E (u * v))⁻¹ = (u * (conjUnits F E u)⁻¹) * (v * (conjUnits F E v)⁻¹)
    rw [map_mul, mul_inv, mul_mul_mul_comm]

theorem coe_unitsMulConjInv (u : (𝓞 E)ˣ) :
    ((unitsMulConjInv F E u : torsion E) : (𝓞 E)ˣ) = u * (conjUnits F E u)⁻¹ := rfl

variable (F E) in
/-- The subgroup $\{u/\sigma u : u \in \mathcal O_E^\times\} \le \mu_E$. -/
abbrev conjQuotGroup : Subgroup (torsion E) := (unitsMulConjInv F E).range

/-- A chosen $r_\zeta \ne 0$ with $\sigma r_\zeta = \zeta r_\zeta$ (Hilbert 90). -/
def rOf (ζ : torsion E) : 𝓞 E :=
  (exists_conj_eq_mul (F := F) (intNorm_torsion (F := F) ζ)).choose

theorem rOf_ne_zero (ζ : torsion E) : rOf (F := F) ζ ≠ 0 :=
  (exists_conj_eq_mul (F := F) (intNorm_torsion (F := F) ζ)).choose_spec.1

theorem conjO_rOf (ζ : torsion E) : conjO F E (rOf (F := F) ζ) = ((ζ : (𝓞 E)ˣ) : 𝓞 E) * rOf (F := F) ζ :=
  (exists_conj_eq_mul (F := F) (intNorm_torsion (F := F) ζ)).choose_spec.2

theorem span_unit_mul (u : (𝓞 E)ˣ) (x : 𝓞 E) : Ideal.span {(u : 𝓞 E) * x} = Ideal.span {x} := by
  rw [mul_comm]; exact Ideal.span_singleton_mul_right_unit u.isUnit x

theorem conjIdeal_mul_span {D : Ideal (𝓞 E)} (hD : conjIdeal F D = D) {r : 𝓞 E} (u : (𝓞 E)ˣ)
    (hr : conjO F E r = (u : 𝓞 E) * r) : conjIdeal F (D * Ideal.span {r}) = D * Ideal.span {r} := by
  rw [conjIdeal_mul, hD, conjIdeal_span, hr, span_unit_mul]

theorem mul_span_ne_bot {D : Ideal (𝓞 E)} (hD : D ≠ ⊥) {r : 𝓞 E} (hr : r ≠ 0) : D * Ideal.span {r} ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact mul_ne_zero (by rwa [Ne, Ideal.zero_eq_bot]) (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])

/-- The fibre map $\mu_E \to \{S \subseteq T\}\times\mathrm{Cl}_F$: $\zeta \mapsto \mathrm{dec}(\mathfrak D_0\, r_\zeta)$. -/
def fibMap (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) (D₀ : Ideal (𝓞 E)) (hD₀ : D₀ ≠ ⊥) (hσ₀ : conjIdeal F D₀ = D₀)
    (ζ : torsion E) : AmbDom T :=
  decOf hT (D₀ * Ideal.span {rOf (F := F) ζ}) (mul_span_ne_bot hD₀ (rOf_ne_zero ζ))
    (conjIdeal_mul_span hσ₀ (ζ : (𝓞 E)ˣ) (conjO_rOf ζ))

/-- Any $r \ne 0$ with $\sigma r = \zeta r$ gives the same decomposition as $r_\zeta$. -/
theorem fibMap_eq_decOf (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {D₀ : Ideal (𝓞 E)} (hD₀ : D₀ ≠ ⊥)
    (hσ₀ : conjIdeal F D₀ = D₀) (ζ : torsion E) {r : 𝓞 E} (hr : r ≠ 0)
    (hσr : conjO F E r = ((ζ : (𝓞 E)ˣ) : 𝓞 E) * r) :
    fibMap hT D₀ hD₀ hσ₀ ζ = decOf hT (D₀ * Ideal.span {r}) (mul_span_ne_bot hD₀ hr)
      (conjIdeal_mul_span hσ₀ (ζ : (𝓞 E)ˣ) hσr) := by
  obtain ⟨m, s, hm, hs, h⟩ := exists_proportional (rOf_ne_zero (F := F) ζ) hr (conjO_rOf ζ) hσr
  refine (decOf_eq_iff hT _ _ _ _).mpr ⟨m, s, hm, hs, ?_⟩
  rw [mul_left_comm, Ideal.span_singleton_mul_span_singleton, ← h, mul_left_comm (Ideal.span {_}) D₀,
    Ideal.span_singleton_mul_span_singleton]

theorem decOf_congr (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {A A' : Ideal (𝓞 E)} (hA : A ≠ ⊥)
    (hσ : conjIdeal F A = A) (hA' : A' ≠ ⊥) (hσ' : conjIdeal F A' = A') (h : A = A') :
    decOf hT A hA hσ = decOf hT A' hA' hσ' := by
  subst h; rfl

theorem conjUnits_inv (v : (𝓞 E)ˣ) : conjUnits F E v⁻¹ = (conjUnits F E v)⁻¹ := map_inv _ _

/-- **The fibre map is constant exactly on the cosets of $\{u/\sigma u\}$.** -/
theorem fibMap_eq_iff (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) {D₀ : Ideal (𝓞 E)} (hD₀ : D₀ ≠ ⊥)
    (hσ₀ : conjIdeal F D₀ = D₀) (ζ ζ' : torsion E) :
    fibMap hT D₀ hD₀ hσ₀ ζ = fibMap hT D₀ hD₀ hσ₀ ζ' ↔ ζ⁻¹ * ζ' ∈ conjQuotGroup F E := by
  constructor
  · intro h
    obtain ⟨m, s, hm, hs, hms⟩ := (decOf_eq_iff hT _ _ _ _).mp h
    set r := rOf (F := F) ζ
    set r' := rOf (F := F) ζ'
    have hD : D₀ * Ideal.span {algebraMap (𝓞 F) (𝓞 E) m * r} = D₀ * Ideal.span {algebraMap (𝓞 F) (𝓞 E) s * r'} := by
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
        mul_left_comm, hms, mul_left_comm]
    have hspan := mul_left_cancel₀ (by rwa [Ne, Ideal.zero_eq_bot]) hD
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    -- apply σ
    have hσv := congrArg (conjO F E) hv
    rw [map_mul, map_mul, map_mul, conjO_algebraMap, conjO_algebraMap, conjO_rOf, conjO_rOf] at hσv
    have hmr : algebraMap (𝓞 F) (𝓞 E) m * r ≠ 0 := mul_ne_zero (algebraMap_O_ne_zero hm) (rOf_ne_zero ζ)
    have key : (algebraMap (𝓞 F) (𝓞 E) m * r) * (((ζ : (𝓞 E)ˣ) : 𝓞 E) * conjO F E (v : 𝓞 E)) =
        (algebraMap (𝓞 F) (𝓞 E) m * r) * (((ζ' : (𝓞 E)ˣ) : 𝓞 E) * (v : 𝓞 E)) := by
      calc _ = algebraMap (𝓞 F) (𝓞 E) m * (((ζ : (𝓞 E)ˣ) : 𝓞 E) * r) * conjO F E (v : 𝓞 E) := by ring
        _ = algebraMap (𝓞 F) (𝓞 E) s * (((ζ' : (𝓞 E)ˣ) : 𝓞 E) * r') := hσv
        _ = ((ζ' : (𝓞 E)ˣ) : 𝓞 E) * (algebraMap (𝓞 F) (𝓞 E) s * r') := by ring
        _ = _ := by rw [← hv]; ring
    have key' := mul_left_cancel₀ hmr key
    have hu : (ζ : (𝓞 E)ˣ) * conjUnits F E v = (ζ' : (𝓞 E)ˣ) * v := Units.ext key'
    refine ⟨v⁻¹, Subtype.ext ?_⟩
    rw [coe_unitsMulConjInv, conjUnits_inv, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have h2 : conjUnits F E v = (ζ : (𝓞 E)ˣ)⁻¹ * ((ζ' : (𝓞 E)ˣ) * v) := eq_inv_mul_of_mul_eq hu
    rw [h2, mul_comm v⁻¹, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  · rintro ⟨u, hu⟩
    have hu' : ((u : (𝓞 E)ˣ) * (conjUnits F E u)⁻¹) = (ζ : (𝓞 E)ˣ)⁻¹ * (ζ' : (𝓞 E)ˣ) := by
      rw [← coe_unitsMulConjInv, hu, Subgroup.coe_mul, Subgroup.coe_inv]
    have hz : (ζ' : (𝓞 E)ˣ) * conjUnits F E u = (ζ : (𝓞 E)ˣ) * u := by
      have : (ζ' : (𝓞 E)ˣ) = ζ * (u * (conjUnits F E u)⁻¹) := by rw [hu', mul_inv_cancel_left]
      rw [this, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    have hzO : ((ζ' : (𝓞 E)ˣ) : 𝓞 E) * conjO F E (u : 𝓞 E) = ((ζ : (𝓞 E)ˣ) : 𝓞 E) * u :=
      congrArg Units.val hz
    set r' := rOf (F := F) ζ'
    have hy0 : r' * (u : 𝓞 E) ≠ 0 := mul_ne_zero (rOf_ne_zero ζ') u.ne_zero
    have hσy : conjO F E (r' * (u : 𝓞 E)) = ((ζ : (𝓞 E)ˣ) : 𝓞 E) * (r' * (u : 𝓞 E)) := by
      rw [map_mul, conjO_rOf]
      linear_combination r' * hzO
    rw [fibMap_eq_decOf hT hD₀ hσ₀ ζ hy0 hσy]
    exact decOf_congr hT _ _ _ _ (by rw [mul_comm r', span_unit_mul])

theorem ambClass_fibMap (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) (D₀ : (Ideal (𝓞 E))⁰)
    (hσ₀ : conjIdeal F (D₀ : Ideal (𝓞 E)) = D₀) (ζ : torsion E) :
    ambClass E (fibMap hT (D₀ : Ideal (𝓞 E)) (nonZeroDivisors.coe_ne_zero D₀) hσ₀ ζ) = ClassGroup.mk0 D₀ := by
  rw [fibMap, ambClass_decOf]
  have := mk0_span_mul (rOf_ne_zero (F := F) ζ) D₀
    (by rw [mul_comm]; exact mem_nonZeroDivisors_of_ne_zero (mul_span_ne_bot (nonZeroDivisors.coe_ne_zero D₀)
      (rOf_ne_zero (F := F) ζ)))
  rw [← this]
  congr 2
  exact mul_comm _ _

/-- **The fibre map is onto the fibre** of `ambClass` over $[\mathfrak D_0]$. -/
theorem exists_fibMap_eq (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) (D₀ : (Ideal (𝓞 E))⁰)
    (hσ₀ : conjIdeal F (D₀ : Ideal (𝓞 E)) = D₀) (x : AmbDom T) (hx : ambClass E x = ClassGroup.mk0 D₀) :
    ∃ ζ : torsion E, fibMap hT (D₀ : Ideal (𝓞 E)) (nonZeroDivisors.coe_ne_zero D₀) hσ₀ ζ = x := by
  have hD0 : (D₀ : Ideal (𝓞 E)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero D₀
  obtain ⟨a, b, ha, hb, hab⟩ := ClassGroup.mk0_eq_mk0_iff.mp hx
  simp only at hab
  set r := b * conjO F E a
  have hr0 : r ≠ 0 := mul_ne_zero hb (conjO_ne_zero ha)
  set 𝔞 : Ideal (𝓞 F) := Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) a} * (classRep F x.2 : Ideal (𝓞 F))
  have hNa : Algebra.intNorm (𝓞 F) (𝓞 E) a ≠ 0 := by
    intro h0
    have := algebraMap_intNorm_eq (F := F) a
    rw [h0, map_zero] at this
    exact mul_ne_zero ha (conjO_ne_zero ha) this.symm
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mul_ne_zero (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
      (by rw [Ne, Ideal.zero_eq_bot]; exact classRep_ne_bot x.2)
  have he : (D₀ : Ideal (𝓞 E)) * Ideal.span {r} = 𝔞.map (algebraMap (𝓞 F) (𝓞 E)) * ramProd E x.1.1 := by
    rw [Ideal.map_mul, map_span_singleton, algebraMap_intNorm_eq, mul_assoc, ← ambIdeal,
      ← Ideal.span_singleton_mul_span_singleton, mul_comm a, ← Ideal.span_singleton_mul_span_singleton,
      mul_assoc, hab]
    ring
  have hσ : conjIdeal F ((D₀ : Ideal (𝓞 E)) * Ideal.span {r}) = (D₀ : Ideal (𝓞 E)) * Ideal.span {r} := by
    rw [he, conjIdeal_mul, conjIdeal_map, conjIdeal_ramProd (ramified_of_mem hT x.1)]
  have hspan : Ideal.span {r} = Ideal.span {conjO F E r} := by
    rw [conjIdeal_mul, hσ₀, conjIdeal_span] at hσ
    exact (mul_left_cancel₀ (by rwa [Ne, Ideal.zero_eq_bot]) hσ).symm
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hvN : nrm (F := F) (v : 𝓞 E) = 1 := by
    have := congrArg (nrm (F := F)) hv
    rw [nrm_mul, nrm_conjO] at this
    exact (mul_eq_left₀ (nrm_ne_zero hr0)).mp this
  set ζ : torsion E := ⟨v, mem_torsion_of_nrm hvN⟩
  have hσr : conjO F E r = ((ζ : (𝓞 E)ˣ) : 𝓞 E) * r := by rw [← hv, mul_comm]
  refine ⟨ζ, ?_⟩
  rw [fibMap_eq_decOf hT hD0 hσ₀ ζ hr0 hσr, decOf_eq hT _ hσ ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩ x.1 he]
  refine Prod.ext rfl ?_
  show ClassGroup.mk0 ⟨𝔞, _⟩ = x.2
  rw [mk0_span_mul hNa (classRep F x.2), mk0_classRep]

variable (F E) in
/-- The strongly ambiguous classes as a type. -/
abbrev StrAmb := {c : ClassGroup (𝓞 E) // IsStrAmb F c}

/-- **Each fibre of `ambClass` over a strongly ambiguous class has $[\mu_E : \{u/\sigma u\}]$ elements.** -/
theorem card_ambClass_fiber (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) (c : StrAmb F E) :
    Nat.card {x : AmbDom T // ambClass E x = c.1} = (conjQuotGroup F E).index := by
  obtain ⟨D₀, hσ₀, hc⟩ := c.2
  have hD0 : (D₀ : Ideal (𝓞 E)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero D₀
  rw [Subgroup.index, ← hc]
  let f : torsion E ⧸ conjQuotGroup F E → {x : AmbDom T // ambClass E x = ClassGroup.mk0 D₀} :=
    Quotient.lift (fun ζ => ⟨fibMap hT (D₀ : Ideal (𝓞 E)) hD0 hσ₀ ζ, ambClass_fibMap hT D₀ hσ₀ ζ⟩)
      (fun a b hab => Subtype.ext ((fibMap_eq_iff hT hD0 hσ₀ a b).mpr (QuotientGroup.leftRel_apply.mp hab)))
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    exact QuotientGroup.eq.mpr ((fibMap_eq_iff hT hD0 hσ₀ a b).mp (congrArg Subtype.val hab))
  · rintro ⟨x, hx⟩
    obtain ⟨ζ, hζ⟩ := exists_fibMap_eq hT D₀ hσ₀ x hx
    exact ⟨(ζ : torsion E ⧸ conjQuotGroup F E), Subtype.ext hζ⟩

/-- **The number of strongly ambiguous classes** (CM): $\#\mathrm{Cl}_E^{\mathrm{str}}\cdot[\mu_E : \{u/\sigma u\}] = 2^t\,h_F$, $t$ = number of
ramified primes. (Elementary: ambiguous ideals + Hilbert 90; cf. Chevalley's ambiguous class number formula.) -/
@[kb "chevalley1933" "ambiguous class number formula [unverified]; lemmermeyer2013 [unverified]"]
theorem card_strAmb_mul_index (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) :
    Nat.card (StrAmb F E) * (conjQuotGroup F E).index = 2 ^ T.card * classNumber F := by
  classical
  let g : AmbDom T → StrAmb F E := fun x => ⟨ambClass E x, isStrAmb_ambClass hT x⟩
  have e : AmbDom T ≃ Σ c : StrAmb F E, {x : AmbDom T // g x = c} := (Equiv.sigmaFiberEquiv g).symm
  have hfib : ∀ c : StrAmb F E, Nat.card {x : AmbDom T // g x = c} = (conjQuotGroup F E).index := fun c => by
    rw [← card_ambClass_fiber hT c]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [g, Subtype.ext_iff])
  have : Fintype (StrAmb F E) := Fintype.ofFinite _
  have hfin : ∀ c : StrAmb F E, Finite {x : AmbDom T // g x = c} := fun c => inferInstance
  have hdom : Nat.card (AmbDom T) = 2 ^ T.card * classNumber F := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := T.powerset), Fintype.card_coe, Finset.card_powerset,
      Nat.card_eq_fintype_card, classNumber]
  rw [← hdom, Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl (fun c _ => hfib c), Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end CM

end QuadFormsKB.Binary.Rel
