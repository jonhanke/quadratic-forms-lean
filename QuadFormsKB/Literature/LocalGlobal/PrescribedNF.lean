/-
# Elements with prescribed local Hilbert symbols over a number field

`PresNF.exists_prescribed_hilbert`: for $a_i \in F^\times$ ($i$ in a finite set) and signs $\varepsilon_{i,v}$ with finitely many
$-1$'s, an even number of $-1$'s for each $i$, and local solutions at every place, there is $x \in F^\times$ with
$(a_i, x)_v = \varepsilon_{i,v}$ for all $i, v$ (Serre III §2.2, Thm. 4, over a number field). This proves the input
`NFInputs.exists_prescribed_hilbert_nf` (`NumberFieldMain.lean`), hence the Serre-route bundle `NFInputs.hmInputs`.

**Route** (no class field theory, no $L$-functions beyond Dedekind's density argument already in the repo):

1. *Finite duality* (`SignPairing`, `exists_mul_mem_of_orth`): in a finite abelian group $G$ with a perfect symmetric
   $\pm1$-pairing, a subgroup $\Lambda$ with $\Lambda \perp \Lambda$ and $|\Lambda|^2 = |G|$, and any subgroup $Q$: if
   $t \perp \Lambda \cap Q^\perp$ then $t \in \Lambda Q$. (Double counting: $|Z|\,|Z^\perp| = |G|$, so $Z^{\perp\perp} = Z$;
   apply it to $Z = \Lambda Q$, whose orthogonal is $\Lambda \cap Q^\perp$.)
2. *The Lagrangian of $S$-units* (`SqDual`): for $S \supseteq$ dyadic places with the kernel condition, the image
   $\Lambda_S$ of the $S$-units in $G_S = \prod_{v \in S\cup\infty} F_v^\times/F_v^{\times2}$ is isotropic (Hilbert reciprocity) with
   $|\Lambda_S|^2 = |G_S|$.
3. *Primes with prescribed square classes* (`exists_prime_sq_nonsq`, induction over quadratic towers, from
   Dedekind's density argument `SqLG.not_almost_all_split`): if $u \notin \langle a_i\rangle F^{\times2}$, some prime outside a
   given finite set has every $a_i$ a square and $u$ a non-square.
4. *Assembly* (`exists_prescribed_hilbert`): $Q$ = the classes with trivial symbols against all $a_i$; the target $t$ is the
   class of the local solutions. Enlarging $S$ by primes from step 3 (at which all $a_i$ are squares, so nothing is
   prescribed there) kills the obstruction $\Lambda \cap Q^\perp$ modulo $\langle a_i \rangle$, on which $t$ is trivial by
   the parity condition. Step 1 then gives an $S$-unit $x$ with the prescribed symbols on $S \cup \infty$; outside, all
   symbols are symbols of units at non-dyadic places, hence $1$.

Locators are from memory and still `[unverified]`, except O'Meara 71:19, checked (see the docstring of
`exists_prescribed_hilbert`).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.SquareClassParam

open Finset NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.PresNF

/-! ### Finite duality for a perfect $\pm1$-pairing -/

section Duality

/-- **A perfect symmetric $\pm 1$-pairing** on a commutative group $G$: `B` takes values $\pm1$, is multiplicative in
the first variable (`mul`), symmetric (`symm`), and nondegenerate (`nd`: every $y \ne 1$ pairs to $-1$ with some $x$). -/
structure SignPairing (G : Type*) [CommGroup G] where
  /-- The pairing. -/
  B : G → G → ℤ
  /-- Values are $\pm 1$. -/
  pm : ∀ x y, B x y = 1 ∨ B x y = -1
  /-- Multiplicative in the first variable. -/
  mul : ∀ x x' y, B (x * x') y = B x y * B x' y
  /-- Symmetric. -/
  symm : ∀ x y, B x y = B y x
  /-- Nondegenerate. -/
  nd : ∀ y, y ≠ 1 → ∃ x, B x y = -1

variable {G : Type*} [CommGroup G] (P : SignPairing G)

namespace SignPairing

lemma one_left (y : G) : P.B 1 y = 1 := by
  have h := P.mul 1 1 y
  rw [mul_one] at h
  rcases P.pm 1 y with h' | h'
  · exact h'
  · rw [h'] at h; norm_num at h

lemma mul_right (x y y' : G) : P.B x (y * y') = P.B x y * P.B x y' := by
  rw [P.symm, P.mul, P.symm y, P.symm y']

lemma inv_right (x y : G) : P.B x y⁻¹ = P.B x y := by
  have h := P.mul_right x y y⁻¹
  rw [mul_inv_cancel, P.symm x 1, P.one_left] at h
  rcases P.pm x y with h1 | h1 <;> rcases P.pm x y⁻¹ with h2 | h2 <;> rw [h1, h2] at h ⊢ <;> norm_num at h

/-- **The orthogonal** $Z^\perp = \{y : B(x, y) = 1\ \forall x \in Z\}$ of a subgroup. -/
def orth (Z : Subgroup G) : Subgroup G where
  carrier := {y | ∀ x ∈ Z, P.B x y = 1}
  one_mem' := fun x _ => by rw [P.symm]; exact P.one_left x
  mul_mem' := fun {y y'} hy hy' x hx => by
    rw [P.mul_right, hy x hx, hy' x hx, one_mul]
  inv_mem' := fun {y} hy x hx => by rw [P.inv_right, hy x hx]

lemma mem_orth {Z : Subgroup G} {y : G} : y ∈ P.orth Z ↔ ∀ x ∈ Z, P.B x y = 1 := Iff.rfl

/-- $Z \subseteq Z^{\perp\perp}$. -/
lemma le_orth_orth (Z : Subgroup G) : Z ≤ P.orth (P.orth Z) := fun z hz y hy => by
  rw [P.symm]; exact hy z hz

/-- $(\Lambda \sqcup Q)^\perp = \Lambda^\perp \cap Q^\perp$. -/
lemma orth_sup (Λ Q : Subgroup G) : P.orth (Λ ⊔ Q) = P.orth Λ ⊓ P.orth Q := by
  ext y
  simp only [Subgroup.mem_inf, mem_orth]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Subgroup.mem_sup_left hx), fun x hx => h x (Subgroup.mem_sup_right hx)⟩
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨l, hl, q, hq, rfl⟩ := Subgroup.mem_sup.mp hx
    rw [P.mul, h1 l hl, h2 q hq, one_mul]

/-- **$|Z|\,|Z^\perp| = |G|$** for every subgroup $Z$ of a finite $G$ (double counting $\sum_{y}\sum_{x \in Z} B(x,y)$,
as in `SqDual.sum_pairing_eq`). -/
theorem card_mul_card_orth [Finite G] (Z : Subgroup G) :
    Nat.card Z * Nat.card (P.orth Z) = Nat.card G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set A := univ.filter (· ∈ Z)
  set O := univ.filter (· ∈ P.orth Z)
  have hsumy : ∀ y, ∑ x ∈ A, P.B x y = if y ∈ P.orth Z then (A.card : ℤ) else 0 := by
    intro y
    split_ifs with hy
    · rw [Finset.sum_congr rfl fun x hx => hy x (by simpa [A] using hx)]; simp
    · rw [mem_orth] at hy
      push Not at hy
      obtain ⟨x₀, hx₀, hne⟩ := hy
      exact SqDual.sum_char_subgroup Z (fun x => P.B x y) (fun x _ x' _ => P.mul x x' y) hx₀
        ((P.pm x₀ y).resolve_left hne)
  have hsumx : ∀ x, ∑ y, P.B x y = if x = 1 then (Fintype.card G : ℤ) else 0 := by
    intro x
    split_ifs with hx
    · subst hx; simp [P.one_left]
    · obtain ⟨y₀, hy₀⟩ := P.nd x hx
      have := SqDual.sum_char_subgroup (⊤ : Subgroup G) (fun y => P.B x y)
        (fun a _ b _ => P.mul_right x a b) (Subgroup.mem_top y₀) (by rw [P.symm]; exact hy₀)
      simpa using this
  have hdc : ∑ y, ∑ x ∈ A, P.B x y = (Fintype.card G : ℤ) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun x _ => hsumx x, Finset.sum_ite_eq' A 1]
    simp [A, Z.one_mem]
  have hperp : (O.card : ℤ) * A.card = Fintype.card G := by
    rw [← hdc, Finset.sum_congr rfl fun y _ => hsumy y, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
  have hA : Nat.card Z = A.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hO : Nat.card (P.orth Z) = O.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hA, hO, Nat.card_eq_fintype_card]
  have : ((A.card * O.card : ℕ) : ℤ) = (Fintype.card G : ℤ) := by push_cast; linarith
  exact_mod_cast this

/-- **$Z^{\perp\perp} = Z$** in a finite group. -/
theorem orth_orth [Finite G] (Z : Subgroup G) : P.orth (P.orth Z) = Z := by
  have h1 := P.card_mul_card_orth Z
  have h2 := P.card_mul_card_orth (P.orth Z)
  have hpos : 0 < Nat.card (P.orth Z) := Nat.card_pos
  have hcard : Nat.card (P.orth (P.orth Z)) = Nat.card Z := by
    have : Nat.card (P.orth (P.orth Z)) * Nat.card (P.orth Z) = Nat.card Z * Nat.card (P.orth Z) := by
      rw [mul_comm, h2, h1]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  exact (Subgroup.eq_of_le_of_card_ge (P.le_orth_orth Z) hcard.le).symm

/-- **A Lagrangian equals its orthogonal:** if $\Lambda \perp \Lambda$ and $|\Lambda|^2 = |G|$ then $\Lambda^\perp = \Lambda$. -/
theorem orth_eq_of_lagrangian [Finite G] (Λ : Subgroup G) (hiso : ∀ x ∈ Λ, ∀ y ∈ Λ, P.B x y = 1)
    (hcard : Nat.card Λ * Nat.card Λ = Nat.card G) : P.orth Λ = Λ := by
  have hle : Λ ≤ P.orth Λ := fun y hy x hx => hiso x hx y hy
  have h1 := P.card_mul_card_orth Λ
  have hpos : 0 < Nat.card Λ := Nat.card_pos
  have hc : Nat.card (P.orth Λ) = Nat.card Λ := by
    rw [← hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  exact (Subgroup.eq_of_le_of_card_ge hle hc.le).symm

/-- **Solving modulo a Lagrangian** (the finite linear algebra behind prescribed symbols). Let $\Lambda$ be a Lagrangian
($\Lambda \perp \Lambda$, $|\Lambda|^2 = |G|$) and $Q$ any subgroup of a finite $G$ with a perfect pairing. If $t$ is
orthogonal to every $y \in \Lambda$ that is orthogonal to $Q$, then $t\,q \in \Lambda$ for some $q \in Q$.

*Proof.* $(\Lambda Q)^\perp = \Lambda^\perp \cap Q^\perp = \Lambda \cap Q^\perp$, so $t \in (\Lambda Q)^{\perp\perp} = \Lambda Q$. -/
theorem exists_mul_mem_of_orth [Finite G] (Λ Q : Subgroup G) (hiso : ∀ x ∈ Λ, ∀ y ∈ Λ, P.B x y = 1)
    (hcard : Nat.card Λ * Nat.card Λ = Nat.card G) (t : G)
    (ht : ∀ y ∈ Λ, (∀ q ∈ Q, P.B q y = 1) → P.B y t = 1) : ∃ q ∈ Q, t * q ∈ Λ := by
  have hmem : t ∈ P.orth (P.orth (Λ ⊔ Q)) := by
    intro y hy
    rw [P.orth_sup, P.orth_eq_of_lagrangian Λ hiso hcard] at hy
    exact ht y hy.1 hy.2
  rw [P.orth_orth] at hmem
  obtain ⟨l, hl, q, hq, rfl⟩ := Subgroup.mem_sup.mp hmem
  exact ⟨q⁻¹, Q.inv_mem hq, by rwa [mul_inv_cancel_right]⟩

end SignPairing

end Duality


/-! ### Squares at a non-dyadic prime, modulo the prime -/

section SqMod

variable {K : Type} [Field K] [NumberField K]

/-- An element of $K$ that is integral at $\mathfrak t$ is congruent mod $\mathfrak t$ to an element of $\mathcal O_K$. -/
lemma exists_int_close (t : HeightOneSpectrum (𝓞 K)) (y : K) (hy : t.valuation K y ≤ 1) :
    ∃ c : 𝓞 K, t.valuation K (y - (c : K)) < 1 := by
  have hy' : y ∈ HeightOneSpectrum.valuationSubringAtPrime K t := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hy
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective t.asIdeal.primeCompl
    (⟨y, hy'⟩ : HeightOneSpectrum.valuationSubringAtPrime K t)
  have h2 := IsLocalization.mk'_spec (HeightOneSpectrum.valuationSubringAtPrime K t) a s
  simp only at h
  rw [h] at h2
  have hys : y * ((s : 𝓞 K) : K) = (a : K) := congrArg Subtype.val h2
  obtain ⟨c, i, hi, hci⟩ := Ideal.IsMaximal.exists_inv (t.isMaximal) s.2
  refine ⟨c * a, ?_⟩
  have hi' : t.valuation K (i : K) < 1 := (t.valuation_lt_one_iff_mem i).mpr hi
  have e : y - ((c * a : 𝓞 K) : K) = y * (i : K) := by
    have e1 : ((c : K) * ((s : 𝓞 K) : K) + i) = 1 := by exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) hci
    push_cast
    linear_combination (-y) * e1 + (c : K) * hys
  rw [e, map_mul]
  calc t.valuation K y * t.valuation K i ≤ 1 * t.valuation K i := by gcongr
    _ < 1 := by rw [one_mul]; exact hi'

lemma valuation_eq_of_sub_lt {t : HeightOneSpectrum (𝓞 K)} {x y : K} (hx : t.valuation K x = 1)
    (h : t.valuation K (x - y) < 1) : t.valuation K y = 1 := by
  have h' : t.valuation K (x - y) < t.valuation K x := by rw [hx]; exact h
  have := Valuation.map_sub_eq_of_lt_right (t.valuation K) h'
  rwa [show x - y - x = -y by ring, Valuation.map_neg, hx] at this

/-- **Hensel at a non-dyadic prime:** a $\mathfrak t$-unit congruent to a square $r^2$ mod $\mathfrak t$ is a square in
$K_{\mathfrak t}$. -/
lemma isSquare_of_close (t : HeightOneSpectrum (𝓞 K)) (h2 : (2 : 𝓞 K) ∉ t.asIdeal) (x : K)
    (hx : t.valuation K x = 1) (r : K) (hr : t.valuation K (x - r ^ 2) < 1) :
    IsSquare (algebraMap K (t.adicCompletion K) x) := by
  have hr2 : t.valuation K (r ^ 2) = 1 := valuation_eq_of_sub_lt hx hr
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr2
  have hval : t.valuation K (x / r ^ 2 - 1) < 1 := by
    have : x / r ^ 2 - 1 = (x - r ^ 2) / r ^ 2 := by field_simp
    rw [this, map_div₀, hr2, div_one]; exact hr
  obtain ⟨z, hz⟩ := NFLocal.isSquare_of_valuation_sub_one_lt_nf t h2 _ hval
  refine ⟨z * algebraMap K _ r, ?_⟩
  have : x = x / r ^ 2 * (r * r) := by field_simp
  rw [this, map_mul, hz, map_mul]; ring

/-- **Squares at a prime are squares mod the prime:** if a $\mathfrak t$-unit $x$ is a square in $K_{\mathfrak t}$, then
$x \equiv r^2 \pmod{\mathfrak t}$ for some $r \in \mathcal O_K$. -/
lemma exists_close_of_isSquare (t : HeightOneSpectrum (𝓞 K)) (x : K) (hx : t.valuation K x = 1)
    (hsq : IsSquare (algebraMap K (t.adicCompletion K) x)) :
    ∃ r : 𝓞 K, t.valuation K (x - (r : K) ^ 2) < 1 := by
  have hval : ∀ y : K, Valued.v (algebraMap K (t.adicCompletion K) y) = t.valuation K y := fun y =>
    HN.valued_algebraMap t y
  obtain ⟨z, hz⟩ := hsq
  have hvz : Valued.v z ≤ 1 := by
    have h1 : Valued.v z * Valued.v z = 1 := by rw [← map_mul, ← hz, hval, hx]
    by_contra hc
    have hc' : 1 < Valued.v z := lt_of_not_ge hc
    have : 1 < Valued.v z * Valued.v z := one_lt_mul hc'.le hc'
    rw [h1] at this; exact lt_irrefl _ this
  obtain ⟨y, hy⟩ : ∃ y : K, Valued.v (z - algebraMap K _ y) < 1 := by
    have hn : {w : t.adicCompletion K | Valued.v (w - z) < 1} ∈ nhds z := Valued.mem_nhds.mpr ⟨1, by simp⟩
    obtain ⟨_, h1, ⟨y, rfl⟩⟩ := mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap K t z) _ hn
    refine ⟨y, ?_⟩
    rw [← Valuation.map_neg, neg_sub]; exact h1
  set w := algebraMap K (t.adicCompletion K) y with hw
  have hvw : Valued.v w ≤ 1 := by
    have : w = z - (z - w) := by ring
    rw [this]; exact (Valuation.map_sub _ _ _).trans (max_le hvz hy.le)
  have hvy : t.valuation K y ≤ 1 := by rw [← hval]; exact hvw
  have hxy : t.valuation K (x - y ^ 2) < 1 := by
    rw [← hval, map_sub, map_pow, hz, ← hw]
    have : z * z - w ^ 2 = (z - w) * (z + w) := by ring
    rw [this, map_mul]
    have h3 : Valued.v (z + w) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le hvz hvw)
    calc Valued.v (z - w) * Valued.v (z + w) ≤ Valued.v (z - w) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hy
  obtain ⟨c, hc⟩ := exists_int_close t y hvy
  refine ⟨c, ?_⟩
  have hyc2 : t.valuation K (y + (c : K)) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le hvy (t.valuation_le_one _))
  have e : x - (c : K) ^ 2 = (x - y ^ 2) + (y - c) * (y + c) := by ring
  rw [e]
  apply Valuation.map_add_lt _ hxy
  rw [map_mul]
  calc t.valuation K (y - c) * t.valuation K (y + c) ≤ t.valuation K (y - c) * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact hc

end SqMod

/-! ### Transfer of squares along a quadratic extension -/

section Transfer

open HN

variable {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [Algebra.IsQuadraticExtension F L]

lemma valuation_lt_one_iff_under (P : HeightOneSpectrum (𝓞 L)) (y : F)
    (hy : (under (F := F) P).valuation F y ≤ 1) :
    P.valuation L (algebraMap F L y) < 1 ↔ (under (F := F) P).valuation F y < 1 := by
  rw [valuation_algebraMap]
  have he := ramificationIdx_ne_zero (F := F) P
  constructor
  · intro h
    by_contra hc
    have h1 : (under (F := F) P).valuation F y = 1 := le_antisymm hy (not_lt.mp hc)
    rw [h1, one_pow] at h; exact lt_irrefl _ h
  · intro h; exact pow_lt_one₀ zero_le h he

lemma valuation_eq_one_of_under (P : HeightOneSpectrum (𝓞 L)) (y : F)
    (hy : (under (F := F) P).valuation F y = 1) : P.valuation L (algebraMap F L y) = 1 := by
  rw [valuation_algebraMap, hy, one_pow]

lemma two_not_mem_of_under (P : HeightOneSpectrum (𝓞 L)) (h2 : (2 : 𝓞 F) ∉ (under (F := F) P).asIdeal) :
    (2 : 𝓞 L) ∉ P.asIdeal := by
  intro h; apply h2
  rw [under_asIdeal, Ideal.mem_comap, map_ofNat]; exact h

/-- **Squares go up:** a square in $F_{\mathfrak p}$ is a square in $L_{\mathfrak P}$ ($\mathfrak P \mid \mathfrak p$). -/
lemma isSquare_up (P : HeightOneSpectrum (𝓞 L)) (x : F)
    (h : IsSquare (algebraMap F ((under (F := F) P).adicCompletion F) x)) :
    IsSquare (algebraMap L (P.adicCompletion L) (algebraMap F L x)) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨compMap P z, ?_⟩
  rw [← compMap_algebraMap, hz, map_mul]

/-- **Squares come down when $f = 1$:** if $f(\mathfrak P \mid \mathfrak p) = 1$, $\mathfrak p$ is non-dyadic and $x \in F$
is a $\mathfrak p$-unit that is a square in $L_{\mathfrak P}$, then $x$ is a square in $F_{\mathfrak p}$. -/
lemma isSquare_down (P : HeightOneSpectrum (𝓞 L))
    (hf : (under (F := F) P).asIdeal.inertiaDeg' P.asIdeal = 1)
    (h2 : (2 : 𝓞 F) ∉ (under (F := F) P).asIdeal) (x : F)
    (hx : (under (F := F) P).valuation F x = 1)
    (h : IsSquare (algebraMap L (P.adicCompletion L) (algebraMap F L x))) :
    IsSquare (algebraMap F ((under (F := F) P).adicCompletion F) x) := by
  obtain ⟨r, hr⟩ := exists_close_of_isSquare P _ (valuation_eq_one_of_under P x hx) h
  obtain ⟨c, hc⟩ := exists_residue_of_f_eq_one (F := F) P hf r
  have hc' : P.valuation L ((r : L) - algebraMap F L (c : F)) < 1 := by
    have := (P.valuation_lt_one_iff_mem (K := L) _).mpr hc
    push_cast at this; exact this
  have hrc : P.valuation L ((r : L) + algebraMap F L (c : F)) ≤ 1 := by
    have h1 : (r : L) + algebraMap F L (c : F) = ((r + algebraMap (𝓞 F) (𝓞 L) c : 𝓞 L) : L) := by
      push_cast; rfl
    rw [h1]; exact P.valuation_le_one _
  have hlt : P.valuation L (algebraMap F L (x - (c : F) ^ 2)) < 1 := by
    have e : algebraMap F L (x - (c : F) ^ 2) =
        (algebraMap F L x - (r : L) ^ 2) + ((r : L) - algebraMap F L (c : F)) * ((r : L) + algebraMap F L (c : F)) := by
      rw [map_sub, map_pow]; ring
    rw [e]
    apply Valuation.map_add_lt _ hr
    rw [map_mul]
    calc _ ≤ P.valuation L ((r : L) - algebraMap F L (c : F)) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hc'
  have hle : (under (F := F) P).valuation F (x - (c : F) ^ 2) ≤ 1 := by
    have h1 : (under (F := F) P).valuation F ((c : F) ^ 2) ≤ 1 := by
      have := (under (F := F) P).valuation_le_one (K := F) (c ^ 2)
      simpa using this
    exact (Valuation.map_sub _ _ _).trans (max_le hx.le h1)
  exact isSquare_of_close _ h2 x hx (c : F) ((valuation_lt_one_iff_under P _ hle).mp hlt)

/-- **Every element of $\mathcal O_F$ is a square mod $\mathfrak P$ when $f(\mathfrak P \mid \mathfrak p) = 2$** ($\mathbb F_q \subseteq
\mathbb F_{q^2}$, $q$ odd; as in `HN.exists_good_prime`). -/
lemma exists_sq_mod_of_f_two (P : HeightOneSpectrum (𝓞 L))
    (hf : (under (F := F) P).asIdeal.inertiaDeg' P.asIdeal = 2)
    (h2t : (2 : 𝓞 F) ∉ (under (F := F) P).asIdeal) (x : 𝓞 F) :
    ∃ r : 𝓞 L, algebraMap (𝓞 F) (𝓞 L) x - r ^ 2 ∈ P.asIdeal := by
  set t := under (F := F) P with htdef
  have := t.isMaximal
  have := P.isMaximal
  let := Ideal.Quotient.field t.asIdeal
  let := Ideal.Quotient.field P.asIdeal
  have : Finite (𝓞 F ⧸ t.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ t.ne_bot
  have : Finite (𝓞 L ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  let := Fintype.ofFinite (𝓞 F ⧸ t.asIdeal)
  let := Fintype.ofFinite (𝓞 L ⧸ P.asIdeal)
  set q := Fintype.card (𝓞 F ⧸ t.asIdeal) with hqdef
  have hcardP : Fintype.card (𝓞 L ⧸ P.asIdeal) = q ^ 2 := by
    have hf' : t.asIdeal.inertiaDeg' P.asIdeal = P.asIdeal.inertiaDeg (𝓞 F) :=
      Ideal.inertiaDeg'_eq_inertiaDeg _ _
    have hN := Ideal.absNorm_pow_inertiaDeg t.asIdeal P.asIdeal
    rw [← hf', hf, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply] at hN
    rw [← Nat.card_eq_fintype_card, ← hN, hqdef, Nat.card_eq_fintype_card]
  have hqodd : Odd q := by
    have hchar : ringChar (𝓞 F ⧸ t.asIdeal) ≠ 2 := by
      intro h
      apply h2t
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
      have := ringChar.spec (𝓞 F ⧸ t.asIdeal) 2
      rw [h] at this
      exact_mod_cast this.mpr dvd_rfl
    have := mt FiniteField.even_card_iff_char_two.mpr hchar
    exact Nat.odd_iff.mpr (by omega)
  have hle' : t.asIdeal ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) := le_of_eq rfl
  set φ := Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 L)) hle'
  have hy : Ideal.Quotient.mk P.asIdeal (algebraMap (𝓞 F) (𝓞 L) x) = φ (Ideal.Quotient.mk t.asIdeal x) := by
    rw [Ideal.quotientMap_mk]
  have hyq : (Ideal.Quotient.mk P.asIdeal (algebraMap (𝓞 F) (𝓞 L) x)) ^ q =
      Ideal.Quotient.mk P.asIdeal (algebraMap (𝓞 F) (𝓞 L) x) := by
    rw [hy, ← map_pow, FiniteField.pow_card]
  obtain ⟨rb, hrb⟩ := HN.isSquare_of_pow_card_eq q hqodd hcardP _ hyq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective rb
  exact ⟨r, by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hrb, pow_two, sub_self]⟩

/-- **Every $\mathfrak p$-unit is a square in $L_{\mathfrak P}$ when $f(\mathfrak P \mid \mathfrak p) = 2$** ($\mathfrak p$ non-dyadic). -/
lemma isSquare_of_f_two (P : HeightOneSpectrum (𝓞 L))
    (hf : (under (F := F) P).asIdeal.inertiaDeg' P.asIdeal = 2)
    (h2t : (2 : 𝓞 F) ∉ (under (F := F) P).asIdeal) (u : F)
    (hu : (under (F := F) P).valuation F u = 1) :
    IsSquare (algebraMap L (P.adicCompletion L) (algebraMap F L u)) := by
  obtain ⟨c, hc⟩ := exists_int_close (under (F := F) P) u hu.le
  obtain ⟨r, hr⟩ := exists_sq_mod_of_f_two P hf h2t c
  have hr' : P.valuation L (algebraMap F L (c : F) - (r : L) ^ 2) < 1 := by
    have := (P.valuation_lt_one_iff_mem (K := L) _).mpr hr
    push_cast at this; exact this
  have huc : P.valuation L (algebraMap F L (u - (c : F))) < 1 := by
    rw [valuation_lt_one_iff_under P]
    · exact hc
    · exact (Valuation.map_sub _ _ _).trans (max_le hu.le ((under (F := F) P).valuation_le_one c))
  refine isSquare_of_close P (two_not_mem_of_under P h2t) _ (valuation_eq_one_of_under P u hu) r ?_
  have e : algebraMap F L u - (r : L) ^ 2 = algebraMap F L (u - (c : F)) + (algebraMap F L (c : F) - (r : L) ^ 2) := by
    rw [map_sub]; ring
  rw [e]
  exact Valuation.map_add_lt _ huc hr'

end Transfer

/-! ### Primes at which given elements are squares and another is not -/

section Primes

open HN

/-- **A non-square is a non-square at infinitely many primes** (Dedekind's density argument,
`SqLG.not_almost_all_split`): if $u \in F$ is not a square, then for every finite set $B$ of primes there is a prime
$\mathfrak p \notin B$ with $u$ not a square in $F_{\mathfrak p}$. -/
lemma exists_prime_nonsq {F : Type} [Field F] [NumberField F] (u : F) (hu : ¬ IsSquare u)
    (B : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ p ∉ B, ¬ IsSquare (algebraMap F (p.adicCompletion F) u) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) u
  have hy0 : (y : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  set b : 𝓞 F := x * y with hbdef
  have hb : (b : F) = algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y * (y : F) ^ 2 := by
    simp only [hbdef]
    push_cast
    change (x : F) * (y : F) = (x : F) / (y : F) * (y : F) ^ 2
    field_simp
  have hbd : ¬ IsSquare (b : F) := by
    rintro ⟨r, hr⟩
    apply hu
    refine ⟨r / y, ?_⟩
    have e : algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y
        = (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y * (y : F) ^ 2) / ((y : F) * (y : F)) := by
      field_simp
    rw [e, ← hb, hr]
    field_simp
  have hb0 : b ≠ 0 := by
    intro h0; apply hbd; rw [h0]; exact ⟨0, by simp⟩
  have hfin : {v : HeightOneSpectrum (𝓞 F) | 2 * b ∈ v.asIdeal}.Finite := by
    have h2 : (2 * b : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hb0
    have := Ideal.finite_factors (R := 𝓞 F) (I := Ideal.span {2 * b}) (by simpa using h2)
    convert this using 2 with v
    simp [Ideal.dvd_span_singleton]
  obtain ⟨L, _, _, _, s, hs, hspan⟩ := QuadFormsKB.Lam.exists_quadExt (b : F) hbd
  apply SqLG.not_almost_all_split (b : F) hbd s hs hspan (B ∪ hfin.toFinset)
  intro v hv
  have hvB : v ∉ B := fun h => hv (Finset.mem_union_left _ h)
  have hv' : 2 * b ∉ v.asIdeal := fun h => hv (Finset.mem_union_right _ (by simpa using h))
  apply SqLG.exists_two_primes_of_isSquare b hbd s hs hspan v hv'
  obtain ⟨t, ht⟩ := hcon v hvB
  refine ⟨t * algebraMap F (v.adicCompletion F) (y : F), ?_⟩
  rw [hb, map_mul, ht, map_pow]
  ring

/-- **Primes with prescribed squares** (a Chebotarev-type statement for $F(\sqrt{a_i}, \sqrt u)$, proved from Dedekind's
density argument by induction over quadratic towers). Let $a_i \in F^\times$ ($i \in s$) and $u \in F^\times$ with
$u\prod_{i \in t}a_i$ a non-square for every $t \subseteq s$ (i.e. $u \notin \langle a_i\rangle F^{\times2}$), and let $B$ be a finite set
of primes containing the dyadic primes and the primes where some $a_i$ or $u$ is not a unit. Then some prime
$\mathfrak p \notin B$ has every $a_i$ a square in $F_{\mathfrak p}$ and $u$ a non-square in $F_{\mathfrak p}$.

*Proof.* Induction on $s$, for all number fields at once. For $s = \emptyset$ this is `exists_prime_nonsq`. Adding $a_j$
(a non-square, else drop it): pass to $L = F(\sqrt{a_j})$, where $u \notin \langle a_i\rangle_{i \in s} L^{\times2}$
(`HN.not_isSquare_in_quadExt`), and take $\mathfrak P$ from the induction hypothesis over $L$, $\mathfrak p$ below it. If $a_j$ were
not a square at $\mathfrak p$, then $\mathfrak P$ would be the only prime above $\mathfrak p$, unramified, so $f = 2$, and every
$\mathfrak p$-unit, $u$ included, would be a square in $L_{\mathfrak P}$ (`isSquare_of_f_two`): contradiction. So $\mathfrak p$ splits,
$f(\mathfrak P \mid \mathfrak p) = 1$, and squares in $L_{\mathfrak P}$ of $\mathfrak p$-units come down to $F_{\mathfrak p}$ (`isSquare_down`), while a
square $u$ in $F_{\mathfrak p}$ would go up (`isSquare_up`). -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.2 (generalized to several square roots) [unverified]"]
theorem exists_prime_sq_nonsq {ι : Type} (s : Finset ι) :
    ∀ (F : Type) [Field F] [NumberField F] (a : ι → F) (u : F) (B : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → v ∈ B) →
      (∀ i ∈ s, a i ≠ 0 ∧ ∀ v ∉ B, v.valuation F (a i) = 1) →
      (∀ v ∉ B, v.valuation F u = 1) →
      (∀ t ⊆ s, ¬ IsSquare (u * ∏ i ∈ t, a i)) →
      ∃ p ∉ B, (∀ i ∈ s, IsSquare (algebraMap F (p.adicCompletion F) (a i))) ∧
        ¬ IsSquare (algebraMap F (p.adicCompletion F) u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro F _ _ a u B _ _ _ hsq
    obtain ⟨p, hpB, hp⟩ := exists_prime_nonsq u (by simpa using hsq ∅ (Finset.empty_subset _)) B
    exact ⟨p, hpB, by simp, hp⟩
  | insert j s hj ih =>
    intro F _ _ a u B h2B ha hu hsq
    have hsq' : ∀ t ⊆ s, ¬ IsSquare (u * ∏ i ∈ t, a i) := fun t ht =>
      hsq t (ht.trans (Finset.subset_insert j s))
    have ha' : ∀ i ∈ s, a i ≠ 0 ∧ ∀ v ∉ B, v.valuation F (a i) = 1 := fun i hi =>
      ha i (Finset.mem_insert_of_mem hi)
    obtain ⟨haj0, hajB⟩ := ha j (Finset.mem_insert_self j s)
    by_cases hjsq : IsSquare (a j)
    · obtain ⟨p, hpB, hps, hpu⟩ := ih F a u B h2B ha' hu hsq'
      refine ⟨p, hpB, fun i hi => ?_, hpu⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · obtain ⟨r, hr⟩ := hjsq; exact ⟨algebraMap F _ r, by rw [hr, map_mul]⟩
      · exact hps i hi
    · obtain ⟨L, _, _, _, s₀, hs₀, hspan⟩ := QuadFormsKB.Lam.exists_quadExt (a j) hjsq
      obtain ⟨hQ, σ, -, hσs⟩ := quadData (a j) hjsq s₀ hs₀ hspan
      have hnotB : ∀ P : HeightOneSpectrum (𝓞 L), P ∉ overS (L := L) B → under (F := F) P ∉ B :=
        fun P hP h => hP (mem_overS.mpr h)
      have h2L : ∀ P : HeightOneSpectrum (𝓞 L), (2 : 𝓞 L) ∈ P.asIdeal → P ∈ overS (L := L) B := by
        intro P hP
        rw [mem_overS]
        apply h2B
        rw [under_asIdeal, Ideal.mem_comap, map_ofNat]; exact hP
      have haL : ∀ i ∈ s, algebraMap F L (a i) ≠ 0 ∧
          ∀ P ∉ overS (L := L) B, P.valuation L (algebraMap F L (a i)) = 1 := fun i hi =>
        ⟨(map_ne_zero _).mpr (ha' i hi).1, fun P hP =>
          valuation_eq_one_of_under P (a i) ((ha' i hi).2 _ (hnotB P hP))⟩
      have huL : ∀ P ∉ overS (L := L) B, P.valuation L (algebraMap F L u) = 1 := fun P hP =>
        valuation_eq_one_of_under P u (hu _ (hnotB P hP))
      have hsqL : ∀ t ⊆ s, ¬ IsSquare (algebraMap F L u * ∏ i ∈ t, algebraMap F L (a i)) := by
        intro t ht
        rw [← map_prod, ← map_mul]
        refine not_isSquare_in_quadExt (a j) s₀ hs₀ hspan (li_of_sq (a j) hjsq s₀ hs₀) _ (hsq' t ht) ?_
        have hjt : j ∉ t := fun h => hj (ht h)
        have := hsq (insert j t) (Finset.insert_subset_insert j ht)
        rwa [Finset.prod_insert hjt, show u * (a j * ∏ i ∈ t, a i) = a j * (u * ∏ i ∈ t, a i) by ring] at this
      obtain ⟨P, hPB, hPs, hPu⟩ :=
        ih L (fun i => algebraMap F L (a i)) (algebraMap F L u) (overS (L := L) B) h2L haL huL hsqL
      have hpB : under (F := F) P ∉ B := hnotB P hPB
      have h2p : (2 : 𝓞 F) ∉ (under (F := F) P).asIdeal := fun h => hpB (h2B _ h)
      have hp2v : (under (F := F) P).valuation F 2 = 1 := by
        have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (under (F := F) P)).mpr h2p
        rwa [map_ofNat] at this
      -- `a j` is a square below `P`
      have hA : IsSquare (algebraMap F ((under (F := F) P).adicCompletion F) (a j)) := by
        by_contra hA
        have huniq := eq_of_not_isSquare (a j) haj0 s₀ hs₀ P hA
        have hef := ef_of_unique (F := F) P huniq
        have he : P.asIdeal.ramificationIdx (𝓞 F) = 1 :=
          ramificationIdx_eq_one σ s₀ (a j) hs₀ hσs P hp2v (hajB _ hpB)
        rw [ramificationIdx'_eq, he, one_mul] at hef
        exact hPu (isSquare_of_f_two P hef h2p u (hu _ hpB))
      -- so `P` has residue degree one
      obtain ⟨w, w', hww, hw, hw'⟩ := two_primes_of_isSquare σ s₀ (a j) hs₀ hσs hjsq _ hA
      have hf : (under (F := F) P).asIdeal.inertiaDeg' P.asIdeal = 1 := by
        by_cases hPw : P = w
        · subst hPw; exact (ef_of_two (F := F) P w' hww (by rw [hw, hw'])).2
        · exact (ef_of_two (F := F) P w hPw (by rw [hw])).2
      refine ⟨under (F := F) P, hpB, fun i hi => ?_, fun hsqu => hPu (isSquare_up P u hsqu)⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hA
      · exact isSquare_down P hf h2p (a i) ((ha' i hi).2 _ hpB) (hPs i hi)

end Primes

/-! ### Assembly -/

section Main

open HN SqDual

variable {F : Type} [Field F] [NumberField F]

/-- The product of local Hilbert pairings on $G_S$ as a `SignPairing` (`SqDual.BS`). -/
def pairingS (S : Finset (HeightOneSpectrum (𝓞 F))) : SignPairing (GS F S) :=
  ⟨BS S, BS_pm S, BS_mul S, BS_symm S, BS_nondeg S⟩

lemma hilbCl_one_right (K : Type*) [Field K] (x : SqCl K) : hilbCl K x 1 = 1 := by
  rw [hilbCl_symm]; exact hilbCl_one_left K x

lemma sqCl_inv (K : Type*) [Field K] (g : SqCl K) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact sqCl_sq K g)

lemma GS_inv (S : Finset (HeightOneSpectrum (𝓞 F))) (g : GS F S) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact GS_sq S g)

/-- A global square has trivial image in $G_S$. -/
lemma locMap_eq_one_of_isSquare (S : Finset (HeightOneSpectrum (𝓞 F))) (w : Fˣ) (h : IsSquare (w : F)) :
    locMap S w = 1 := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  have : w = Units.mk0 r hr0 ^ 2 := Units.ext (by simp [hr, sq])
  rw [this, map_pow, GS_sq]

lemma BS_prod (S : Finset (HeightOneSpectrum (𝓞 F))) {ι : Type*} (t : Finset ι) (x : ι → GS F S) (y : GS F S) :
    BS S (∏ i ∈ t, x i) y = ∏ i ∈ t, BS S (x i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact BS_one_left S y
  | insert j t hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, BS_mul, ih]

/-- **Parity over $S \cup \infty$:** if $e$ is $\pm1$-valued with an even number of $-1$'s, all at infinite places or at
places of $S$, then $\prod_{v \in S \cup \infty} e_v = 1$. -/
lemma prod_eps_eq_one (S : Finset (HeightOneSpectrum (𝓞 F))) (e : NFPlace F → ℤ) (he : ∀ v, e v = 1 ∨ e v = -1)
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), e (NFPlace.finite v) = -1 → v ∈ S)
    (heven : Even {v : NFPlace F | e v = -1}.ncard) :
    (∏ v : S, e (NFPlace.finite v.1)) * ∏ w : InfinitePlace F, e (NFPlace.infinite w) = 1 := by
  classical
  set hf : S → ℤ := fun v => e (NFPlace.finite v.1)
  set hi : InfinitePlace F → ℤ := fun w => e (NFPlace.infinite w)
  rw [prod_pm_eq_pow hf fun v => he _, prod_pm_eq_pow hi fun w => he _, ← pow_add]
  set A := Finset.univ.filter fun v : S => hf v = -1
  set B := Finset.univ.filter fun w : InfinitePlace F => hi w = -1
  have hE : {v : NFPlace F | e v = -1} =
      (fun v : S => NFPlace.finite v.1) '' (A : Set S) ∪ NFPlace.infinite '' (B : Set (InfinitePlace F)) := by
    ext v
    cases v with
    | infinite w => simp [B, hi]
    | finite v =>
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and,
        reduceCtorEq, and_false, exists_false, or_false, A, hf]
      constructor
      · intro h; exact ⟨⟨v, hS v h⟩, h, rfl⟩
      · rintro ⟨v', h, hv'⟩; cases hv'; exact h
  have hinj1 : Function.Injective fun v : S => (NFPlace.finite v.1 : NFPlace F) := fun x y h =>
    Subtype.ext (NFPlace.finite.inj h)
  have hinj2 : Function.Injective (NFPlace.infinite (F := F)) := fun x y h => by cases h; rfl
  have hdisj : Disjoint ((fun v : S => NFPlace.finite v.1) '' (A : Set S))
      (NFPlace.infinite '' (B : Set (InfinitePlace F))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, -, rfl⟩ ⟨w, -, h⟩
    cases h
  rw [hE, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ hinj1, Set.ncard_image_of_injective _ hinj2,
    Set.ncard_coe_finset, Set.ncard_coe_finset] at heven
  exact heven.neg_one_pow

/-- **Elements of $F$ with prescribed local Hilbert symbols** (Serre III §2.2, Thm. 4, over a number field $F$). Let
$a_i \in F^\times$ ($i \in \iota$, finite) and $\varepsilon_{i,v} \in \{\pm 1\}$ for the places $v$ of $F$, with (1) only finitely many
$-1$'s, (2) an even number of $-1$'s for each $i$, and (3) at each $v$ some $x_v \in F_v^\times$ with $(a_i, x_v)_v =
\varepsilon_{i,v}$ for all $i$. Then some $x \in F^\times$ has $(a_i, x)_v = \varepsilon_{i,v}$ for all $i$ and $v$.

*Proof* (no class field theory; see the module docstring). Take $S$ (finite places) containing the dyadic places, the
supports of the $a_i$ and of $\varepsilon$, and a set with the kernel condition (`SqDual.exists_sqKernelCond`). For every
$\lambda \in \Lambda_S$ whose lift $u_\lambda$ is not in $\langle a_i\rangle F^{\times 2}$, add a prime $\mathfrak p \notin S$ at which all $a_i$
are squares and $u_\lambda$ is not (`exists_prime_sq_nonsq`); call the enlarged set $S'$. In $G_{S'}$ let $t$ be the class of the
local solutions $(x_v)$ and $Q$ the classes with trivial symbols against every $a_i$. If $y \in \Lambda_{S'}$ is orthogonal to
$Q$, then $y$ is a local square at the added primes, hence (up to squares) an $S$-unit, hence in $\langle a_i\rangle F^{\times2}$ by the
choice of the added primes, and $\langle [a_i], t \rangle = \prod_v \varepsilon_{i,v} = 1$. So `exists_mul_mem_of_orth` gives
$q \in Q$ with $tq \in \Lambda_{S'}$, the class of an $S'$-unit $x$; it has the right symbols on $S' \cup \infty$, and outside
$S'$ all symbols are symbols of units at non-dyadic places, hence $1 = \varepsilon_{i,v}$.

*Locator.* O'Meara 71:19 (with Cor. 71:19a; printed p. 203, PDF p. 211; checked 2026-10-17) is the case of a single
$a$: given an even set $T$ of places at which $\beta$ is not a square, some $\alpha$ has $(\alpha, \beta)_v = -1$ exactly on $T$.
The several-$a_i$ statement is Serre's Thm. 4 (stated there over $\mathbb Q$). -/
@[kb "serre1973" "Ch. III §2.2, Thm. 4 (over a number field); omeara1963 §71D, 71:19 and 71:19a, p. 203 (one a)"]
theorem exists_prescribed_hilbert {ι : Type} [Fintype ι] (a : ι → F) (ha : ∀ i, a i ≠ 0)
    (ε : ι → NFPlace F → ℤ) (hε : ∀ i v, ε i v = 1 ∨ ε i v = -1)
    (h1 : {v : NFPlace F | ∃ i, ε i v = -1}.Finite)
    (h2 : ∀ i, Even {v : NFPlace F | ε i v = -1}.ncard)
    (h3 : ∀ v : NFPlace F, v.atPlace fun K _ _ =>
      ∃ x : K, x ≠ 0 ∧ ∀ i, hilbertSymbol K (algebraMap F K (a i)) x = ε i v) :
    ∃ x : F, x ≠ 0 ∧ ∀ i v, v.hilbert (a i) x = ε i v := by
  classical
  set aU : ι → Fˣ := fun i => Units.mk0 (a i) (ha i) with haU
  obtain ⟨S₀, hS₀⟩ := exists_genProp (F := F)
  obtain ⟨S₁, hS₀₁, hS₁⟩ := exists_sqKernelCond hS₀
  -- the set `S`
  obtain ⟨S, hS₁S, h2S, hεS, haS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), S₁ ⊆ S ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → v ∈ S) ∧
      (∀ i (v : HeightOneSpectrum (𝓞 F)), ε i (NFPlace.finite v) = -1 → v ∈ S) ∧
      (∀ i, ∀ v ∉ S, v.valuation F (a i) = 1) := by
    have h2fin : {p : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ p.asIdeal}.Finite := by
      refine (Ideal.finite_factors (I := Ideal.span {(2 : 𝓞 F)}) (by simp)).subset ?_
      intro p hp; rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]; exact hp
    have hεfin : {v : HeightOneSpectrum (𝓞 F) | ∃ i, ε i (NFPlace.finite v) = -1}.Finite :=
      h1.preimage (f := (NFPlace.finite : HeightOneSpectrum (𝓞 F) → NFPlace F))
        (fun x _ y _ h => NFPlace.finite.inj h)
    have hafin : ∀ i, {v : HeightOneSpectrum (𝓞 F) | ordL v (aU i) ≠ 0}.Finite := fun i =>
      finite_ordL_ne_zero (aU i)
    refine ⟨S₁ ∪ h2fin.toFinset ∪ hεfin.toFinset ∪ Finset.univ.biUnion (fun i => (hafin i).toFinset),
      fun v hv => by simp [hv], fun v hv => by simp [hv], fun i v hv => Finset.mem_union_left _ (Finset.mem_union_right _ (hεfin.mem_toFinset.mpr ⟨i, hv⟩)),
      fun i v hv => ?_⟩
    have : ordL v (aU i) = 0 := by
      by_contra h
      exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using h⟩))
    exact (ordL_eq_zero_iff v (aU i)).mp this
  have hS₀S : S₀ ⊆ S := hS₀₁.trans hS₁S
  have hkerS : SqKernelCond S := hS₁ S hS₁S
  -- the added primes `R`
  obtain ⟨R, hR, hRbad⟩ : ∃ R : Finset (HeightOneSpectrum (𝓞 F)),
      (∀ p ∈ R, p ∉ S ∧ ∀ i, IsSquare (algebraMap F (p.adicCompletion F) (a i))) ∧
      (∀ d : LamS S, (∀ t : Finset ι, ¬ IsSquare (((liftU d : Fˣ) : F) * ∏ i ∈ t, a i)) →
        ∃ p ∈ R, ¬ IsSquare (algebraMap F (p.adicCompletion F) ((liftU d : Fˣ) : F))) := by
    have hgood : ∀ d : {d : LamS S // ∀ t : Finset ι, ¬ IsSquare (((liftU d : Fˣ) : F) * ∏ i ∈ t, a i)},
        ∃ p : HeightOneSpectrum (𝓞 F), (p ∉ S ∧ ∀ i, IsSquare (algebraMap F (p.adicCompletion F) (a i))) ∧
          ¬ IsSquare (algebraMap F (p.adicCompletion F) ((liftU d.1 : Fˣ) : F)) := by
      rintro ⟨d, hd⟩
      obtain ⟨p, hp, hps, hpu⟩ := exists_prime_sq_nonsq Finset.univ F a ((liftU d : Fˣ) : F) S h2S
        (fun i _ => ⟨ha i, haS i⟩) (fun v hv => liftU_mem d v hv) (fun t _ => hd t)
      exact ⟨p, ⟨hp, fun i => hps i (Finset.mem_univ i)⟩, hpu⟩
    choose f hf using hgood
    refine ⟨Finset.univ.image f, fun p hp => ?_, fun d hd => ⟨f ⟨d, hd⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (hf ⟨d, hd⟩).2⟩⟩
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hf d).1
  set S' := S ∪ R with hS'def
  have hSS' : S ⊆ S' := Finset.subset_union_left
  have hkerS' : SqKernelCond S' := hS₁ S' (hS₁S.trans hSS')
  have h2S' : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S' := fun v hv => hSS' (h2S v hv)
  -- the local solutions
  have hxf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : (v.adicCompletion F)ˣ,
      ∀ i, hilbertSymbol _ (algebraMap F _ (a i)) (x : v.adicCompletion F) = ε i (NFPlace.finite v) := by
    intro v
    obtain ⟨x, hx0, hx⟩ := h3 (NFPlace.finite v)
    exact ⟨Units.mk0 x hx0, hx⟩
  have hxi : ∀ w : InfinitePlace F, ∃ x : w.Completionˣ,
      ∀ i, hilbertSymbol _ (algebraMap F _ (a i)) (x : w.Completion) = ε i (NFPlace.infinite w) := by
    intro w
    obtain ⟨x, hx0, hx⟩ := h3 (NFPlace.infinite w)
    exact ⟨Units.mk0 x hx0, hx⟩
  choose xf hxf using hxf
  choose xi hxi using hxi
  set ω : GS F S' := (fun v => QuotientGroup.mk (xf v.1), fun w => QuotientGroup.mk (xi w)) with hω
  -- the subgroup `Q` of classes with trivial symbols against all `a i`
  let Q : Subgroup (GS F S') :=
    { carrier := {g | (∀ i (v : S'), hilbCl _ ((locMap S' (aU i)).1 v) (g.1 v) = 1) ∧
        ∀ i (w : InfinitePlace F), hilbCl _ ((locMap S' (aU i)).2 w) (g.2 w) = 1}
      one_mem' := ⟨fun i v => hilbCl_one_right _ _, fun i w => hilbCl_one_right _ _⟩
      mul_mem' := fun {g h} hg hh => ⟨fun i v => by
          show hilbCl _ _ (g.1 v * h.1 v) = 1
          rw [hilbCl_symm, hilbCl_mul_fin, hilbCl_symm, hg.1 i v, hilbCl_symm, hh.1 i v, one_mul],
        fun i w => by
          show hilbCl _ _ (g.2 w * h.2 w) = 1
          rw [hilbCl_symm, hilbCl_mul_inf, hilbCl_symm, hg.2 i w, hilbCl_symm, hh.2 i w, one_mul]⟩
      inv_mem' := fun {g} hg => ⟨fun i v => by
          show hilbCl _ _ (g.1 v)⁻¹ = 1
          rw [sqCl_inv]; exact hg.1 i v,
        fun i w => by
          show hilbCl _ _ (g.2 w)⁻¹ = 1
          rw [sqCl_inv]; exact hg.2 i w⟩ }
  -- the pairing of `[a i]` with the target is `∏_v ε i v = 1`
  have hBa : ∀ i, BS S' (locMap S' (aU i)) ω = 1 := by
    intro i
    have e1 : ∀ v : S', hilbCl _ ((locMap S' (aU i)).1 v) (ω.1 v) = ε i (NFPlace.finite v.1) := fun v =>
      hxf v.1 i
    have e2 : ∀ w : InfinitePlace F, hilbCl _ ((locMap S' (aU i)).2 w) (ω.2 w) = ε i (NFPlace.infinite w) :=
      fun w => hxi w i
    unfold BS
    rw [Finset.prod_congr rfl fun v _ => e1 v, Finset.prod_congr rfl fun w _ => e2 w]
    exact prod_eps_eq_one S' (ε i) (hε i) (fun v hv => hSS' (hεS i v hv)) (h2 i)
  -- the obstruction vanishes
  have hobs : ∀ y ∈ LamS S', (∀ q ∈ Q, BS S' q y = 1) → BS S' y ω = 1 := by
    intro y hy hyQ
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hy
    -- (a) `u'` is a square at the added primes
    have hsqR : ∀ p ∈ R, IsSquare (algebraMap F (p.adicCompletion F) (u' : F)) := by
      intro p hpR
      have hpS' : p ∈ S' := Finset.mem_union_right _ hpR
      by_contra hns
      have hc : (locMap S' u').1 ⟨p, hpS'⟩ ≠ 1 := fun h =>
        hns ((mk_eq_one_iff_isSquare _ (Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom u')).mp h)
      obtain ⟨g, hg⟩ := hilbCl_nondeg_fin p _ hc
      set q : GS F S' := (Pi.mulSingle (M := fun v : S' => SqCl (v.1.adicCompletion F)) ⟨p, hpS'⟩ g, 1) with hq
      have hqQ : q ∈ Q := by
        refine ⟨fun i v => ?_, fun i w => hilbCl_one_right _ _⟩
        by_cases hv : v = ⟨p, hpS'⟩
        · subst hv
          have h1 : (locMap S' (aU i)).1 ⟨p, hpS'⟩ = 1 :=
            (mk_eq_one_iff_isSquare _ (Units.map (algebraMap F (p.adicCompletion F)).toMonoidHom (aU i))).mpr
              ((hR p hpR).2 i)
          rw [h1]; exact hilbCl_one_left _ _
        · show hilbCl _ _ (Pi.mulSingle (M := fun v : S' => SqCl (v.1.adicCompletion F)) ⟨p, hpS'⟩ g v) = 1
          rw [Pi.mulSingle_eq_of_ne hv]; exact hilbCl_one_right _ _
      have hBq : BS S' q (locMap S' u') = hilbCl _ g ((locMap S' u').1 ⟨p, hpS'⟩) := by
        unfold BS
        have e1 : ∏ w : InfinitePlace F, hilbCl _ (q.2 w) ((locMap S' u').2 w) = 1 :=
          Finset.prod_eq_one fun w _ => hilbCl_one_left _ _
        have e2 : ∏ v : S', hilbCl _ (q.1 v) ((locMap S' u').1 v) = hilbCl _ g ((locMap S' u').1 ⟨p, hpS'⟩) := by
          rw [Finset.prod_eq_single ⟨p, hpS'⟩ (fun v' _ hv' => by
            show hilbCl _ (Pi.mulSingle (M := fun v : S' => SqCl (v.1.adicCompletion F)) ⟨p, hpS'⟩ g v') _ = 1
            rw [Pi.mulSingle_eq_of_ne hv', hilbCl_one_left]) (by simp)]
          show hilbCl _ (Pi.mulSingle (M := fun v : S' => SqCl (v.1.adicCompletion F)) ⟨p, hpS'⟩ g ⟨p, hpS'⟩) _ = _
          rw [Pi.mulSingle_eq_same]
        rw [e1, e2, mul_one]
      have := hyQ q hqQ
      rw [hBq, hg] at this
      norm_num at this
    -- (b) up to a square, `u'` is an `S`-unit
    have heven : ∀ q ∉ S, Even (ordL q u') := by
      intro q hq
      by_cases hqR : q ∈ R
      · exact even_ordL_of_isSquare q u' (hsqR q hqR)
      · have hqS' : q ∉ S' := by rw [hS'def, Finset.mem_union]; tauto
        rw [ordL_sUnit hu' hqS']; exact ⟨0, rfl⟩
    obtain ⟨u'', hu'', z, hz⟩ := exists_sUnit_mul_sq hS₀ hS₀S u' heven
    -- (c) compare with the chosen lift `u₀` of its class
    set d : LamS S := ⟨locMap S u'', Subgroup.mem_map_of_mem _ hu''⟩ with hd
    set u₀ := liftU d with hu₀
    have hsq0 : IsSquare (((u'' * u₀⁻¹ : Fˣ)) : F) := by
      apply hkerS _ ((HN.SUnit S).mul_mem hu'' ((HN.SUnit S).inv_mem (liftU_mem d)))
      rw [map_mul, map_inv, locMap_liftU]; exact mul_inv_cancel _
    obtain ⟨r, hr⟩ := hsq0
    have hr0 : r ≠ 0 := by
      rintro rfl; simp at hr
    have hu₀eq : ((u₀ : Fˣ) : F) = (u' : F) / ((z : F) * r) ^ 2 := by
      have e1 : (u' : F) = (u'' : F) * (z : F) ^ 2 := by rw [hz]; simp
      have e2 : (u'' : F) = r * r * (u₀ : F) := by
        have : (u'' : F) * ((u₀ : Fˣ) : F)⁻¹ = r * r := by simpa using hr
        field_simp at this ⊢
        linear_combination this
      rw [e1, e2]; field_simp
    -- (d) `u₀` lies in `⟨a_i⟩ F^{×2}` by the choice of `R`
    obtain ⟨t, ht⟩ : ∃ t : Finset ι, IsSquare (((u₀ : Fˣ) : F) * ∏ i ∈ t, a i) := by
      by_contra hbad
      push Not at hbad
      obtain ⟨p, hpR, hpns⟩ := hRbad d hbad
      apply hpns
      obtain ⟨m, hm⟩ := hsqR p hpR
      refine ⟨m / algebraMap F (p.adicCompletion F) ((z : F) * r), ?_⟩
      have hz0 : algebraMap F (p.adicCompletion F) ((z : F) * r) ≠ 0 :=
        (map_ne_zero _).mpr (mul_ne_zero z.ne_zero hr0)
      rw [← hu₀, hu₀eq, map_div₀, map_pow, hm]
      field_simp
    -- (e) so `[u'] = ∏_{i ∈ t} [a_i]`, which pairs trivially with the target
    have hsq' : IsSquare (((u' * ∏ i ∈ t, aU i : Fˣ)) : F) := by
      obtain ⟨m, hm⟩ := ht
      refine ⟨(z : F) * r * m, ?_⟩
      have e : ((u' * ∏ i ∈ t, aU i : Fˣ) : F) = ((z : F) * r) ^ 2 * (((u₀ : Fˣ) : F) * ∏ i ∈ t, a i) := by
        rw [Units.val_mul, Units.coe_prod]
        simp only [haU, Units.val_mk0]
        rw [hu₀eq]
        field_simp
      rw [e, hm]; ring
    have hloc := locMap_eq_one_of_isSquare S' _ hsq'
    rw [map_mul, map_prod] at hloc
    have hy' : locMap S' u' = ∏ i ∈ t, locMap S' (aU i) := by
      rw [← GS_inv S' (∏ i ∈ t, locMap S' (aU i))]
      exact eq_inv_of_mul_eq_one_left hloc
    rw [hy', BS_prod, Finset.prod_eq_one fun i _ => hBa i]
  -- solve modulo the Lagrangian `Λ_{S'}`
  have hiso : ∀ x ∈ LamS S', ∀ y ∈ LamS S', BS S' x y = 1 := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact BS_locMap_sUnit S' h2S' hb hc
  have hcard : Nat.card (LamS S') * Nat.card (LamS S') = Nat.card (GS F S') := by
    rw [card_LamS S' hkerS', Nat.card_eq_fintype_card, card_GS S' h2S', ← pow_add, ← two_mul, pow_mul]
    norm_num
  obtain ⟨q, hqQ, hmem⟩ := (pairingS S').exists_mul_mem_of_orth (LamS S') Q hiso hcard ω hobs
  obtain ⟨x, hxS', hxloc⟩ := Subgroup.mem_map.mp hmem
  refine ⟨(x : F), x.ne_zero, fun i v => ?_⟩
  cases v with
  | infinite w =>
    have h := congrFun (congrArg Prod.snd hxloc) w
    have : (NFPlace.infinite w).hilbert (a i) (x : F) =
        hilbCl _ ((locMap S' (aU i)).2 w) ((locMap S' x).2 w) := rfl
    rw [this, h]
    show hilbCl _ _ (ω.2 w * q.2 w) = _
    rw [hilbCl_symm, hilbCl_mul_inf, hilbCl_symm, hilbCl_symm _ (q.2 w), hqQ.2 i w, mul_one]
    exact hxi w i
  | finite v =>
    by_cases hv : v ∈ S'
    · have h := congrFun (congrArg Prod.fst hxloc) ⟨v, hv⟩
      have : (NFPlace.finite v).hilbert (a i) (x : F) =
          hilbCl _ ((locMap S' (aU i)).1 ⟨v, hv⟩) ((locMap S' x).1 ⟨v, hv⟩) := rfl
      rw [this, h]
      show hilbCl _ _ (ω.1 ⟨v, hv⟩ * q.1 ⟨v, hv⟩) = _
      rw [hilbCl_symm, hilbCl_mul_fin, hilbCl_symm, hilbCl_symm _ (q.1 ⟨v, hv⟩), hqQ.1 i ⟨v, hv⟩, mul_one]
      exact hxf v i
    · have hvS : v ∉ S := fun h => hv (hSS' h)
      rw [hilbert_units_nondyadic v (fun h => hv (h2S' v h)) _ _ (haS i v hvS) (hxS' v hv)]
      exact ((hε i _).resolve_right fun h => hvS (hεS i v h)).symm

end Main

end QuadFormsKB.PresNF
