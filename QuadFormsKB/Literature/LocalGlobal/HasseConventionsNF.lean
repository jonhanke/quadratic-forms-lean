/-
# Hasse invariants in all conventions over a number field

The number-field version of `HasseConventions.lean`. Let $F$ be a number field and
$\langle a_0,\dots,a_{n-1}\rangle$ a nondegenerate diagonal form with $a_i \in F^\times$. At every place $v$ of $F$
(`NFPlace F`: an infinite place, real or complex, or a nonzero prime of $\mathcal{O}_F$), with the local Hilbert symbol
$(a,b)_v$ over the completion $F_v$ (`NFPlace.hilbert`), the five conventions are

* Serre's $\varepsilon_v$, Cassels' $c_v$, Lam's $s_v$: $\prod_{i<j}(a_i,a_j)_v$
  (`NFPlace.hasseSerre`, `hasseCassels`, `hasseLam`);
* O'Meara's Hasse symbol $S_v$ (§63B) and Hasse's original $\alpha_v$ as recorded by Shimura (§28.13):
  $\prod_{i\le j}(a_i,a_j)_v$ (`NFPlace.hasseOMeara`, `hasseShimura`).

O'Meara and Shimura work over number fields from the start; Serre and Cassels work over $\mathbb{Q}$, Lam over any
field (here: the completions $F_v$).

* **Dictionary** (Section "Conversions"): with $d = \prod a_i$ and $\delta = (-1)^{n(n-1)/2} d$,
  $S_v = \varepsilon_v\,(d,d)_v = \varepsilon_v\,(-1,d)_v = \varepsilon_v\,(-1,-1)_v\,(-1,-d)_v
  = \varepsilon_v\,(\delta,\delta)_v\,(-1,-1)_v^{n(n-1)/2}$ and $\varepsilon_v = S_v\,(d,d)_v$, exactly as over
  $\mathbb{Q}$ (`hasseOMeara_eq` etc.); the proofs use only bimultiplicativity, $(a,-a)_v = 1$ and
  symmetry, which hold at every place of $F$.
* **Product formulas** (Section "Product formulas"): each convention is $1$ at all but finitely many places and
  $\prod_v = 1$, from Hilbert reciprocity over $F$ (`hilbert_reciprocity_nf`, proved as
  `HN.hilbert_product_formula_nf`).
* **$F = \mathbb{Q}$** (Section "Specialization"): under the bijection `NFPlace.toRatPlace : NFPlace ℚ → RatPlace`
  each convention is the $\mathbb{Q}$ one (`NFPlace.hasseSerre_rat`, ...).
* **Isometry invariance**: the correction $(d,d)_v$ is an isometry invariant over $F_v$
  (`NFPlace.hilbert_diagDet_self_isometric`), so O'Meara's $S_v$ is invariant iff Serre's $\varepsilon_v$ is
  (`NFPlace.hasseOMeara_isometric_of_hasseSerre`). The invariance of $\varepsilon_v$ itself over $F_v$, at every place
  (dyadic and archimedean included), and hence of all five conventions, is proved in `HasseIsometryNF.lean`
  (`NFPlace.hasseSerre_isometric`, `NFPlace.hasseOMeara_isometric`, `NFPlace.hasseShimura_isometric`).

*Related work.* Tau Ceti (`TauCeti/NumberTheory/LocalField/QuadraticForm/Hasse.lean`,
`.../Global/{FiniteHasse,RealHasse,HasseSupport,ProductFormula}.lean`) defines one Hasse invariant (the $i<j$ product,
on isometry classes) over local fields and the Hasse product formula for a regular form over a number field. What this
file adds: all five literature conventions side by side over a number field, their exact dictionary, and the
specialization to the $\mathbb{Q}$ file.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Binary.RelGenusHilbert
import QuadFormsKB.Equiv.NumberFieldRat

open NumberField

namespace QuadFormsKB

open Finset PadicClass

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Basic properties of the local Hilbert symbol at a place of $F$ -/

namespace NFPlace

@[kb "omeara1963" "§63B, p. 166 (formulas of 57:10)"]
theorem hilbert_comm (v : NFPlace F) (a b : F) : v.hilbert a b = v.hilbert b a := by
  cases v <;> exact hilbertSymbol_comm _ _ _

@[kb "omeara1963" "§63B, p. 166 (bimultiplicativity)"]
theorem hilbert_mul_left (v : NFPlace F) {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    v.hilbert (a * b) c = v.hilbert a c * v.hilbert b c := by
  rw [hilbert_comm, hilbert_mul_right v hc ha hb, hilbert_comm v c, hilbert_comm v c]

@[kb "omeara1963" "§63B, p. 166 (formulas of 57:10)"]
theorem hilbert_self_neg (v : NFPlace F) (a : F) : v.hilbert a (-a) = 1 := by
  cases v <;> simp only [hilbert, map_neg] <;> exact hilbertSymbol_self_neg _ _

@[kb "omeara1963" "§63B, p. 166 (formulas of 57:10)"]
theorem hilbert_self (v : NFPlace F) {a : F} (ha : a ≠ 0) : v.hilbert a a = v.hilbert a (-1) := by
  have h := hilbert_self_neg v a
  rw [show -a = -1 * a by ring, hilbert_mul_right v ha (by norm_num) ha] at h
  rcases hilbert_eq_one_or v a (-1) with h1 | h1 <;> rw [h1] at h ⊢ <;> linarith

@[kb "omeara1963" "§63B, p. 166 (formulas of 57:10)"]
theorem hilbert_one_left (v : NFPlace F) (b : F) : v.hilbert 1 b = 1 := by
  cases v <;> simp only [hilbert, map_one] <;> rw [hilbertSymbol_comm] <;> exact hilbertSymbol_one_right _ _

theorem hilbert_prod_left (v : NFPlace F) {b : F} (hb : b ≠ 0) {ι : Type*} (s : Finset ι)
    (a : ι → F) (ha : ∀ i ∈ s, a i ≠ 0) :
    v.hilbert (∏ i ∈ s, a i) b = ∏ i ∈ s, v.hilbert (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [prod_empty]; exact hilbert_one_left v b
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj,
      hilbert_mul_left v (ha j (mem_insert_self _ _))
        (prod_ne_zero_iff.mpr fun i hi => ha i (mem_insert_of_mem hi)) hb,
      ih fun i hi => ha i (mem_insert_of_mem hi)]

/-! ### The conventions -/

/-- **Serre's Hasse invariant $\varepsilon_v$ at a place $v$ of the number field $F$** of
$\langle a_0,\dots,a_{n-1}\rangle$, $a_i \in F^\times$:
$$\varepsilon_v = \prod_{0 \le i < j < n} (a_i, a_j)_v,$$
the formula of *A Course in Arithmetic*, Ch. IV, §2.1, p. 35 (stated there over $\mathbb{Q}_p$ and $\mathbb{R}$),
taken over the completion $F_v$. For $F = \mathbb{Q}$ it is `RatPlace.hasseSerre` (`NFPlace.hasseSerre_rat`). -/
@[kb "serre1973" "Ch. IV, §2.1, p. 35"]
noncomputable def hasseSerre (v : NFPlace F) (a : Fin n → F) : ℤ :=
  ∏ i, ∏ j, if i < j then v.hilbert (a i) (a j) else 1

/-- **Cassels' Hasse–Minkowski invariant $c_v$** of $\langle a_0,\dots,a_{n-1}\rangle$, $a_i \in F^\times$, at a
place $v$ of the number field $F$ (*Rational Quadratic Forms*, Ch. 4, §1, p. 55, there over $\mathbb{Q}_p$):
$c_v = \prod_{0 \le i < j < n}(a_i,a_j)_v$, excluding the diagonal pairs (see `RatPlace.hasseCassels` for the check
against the book). Equal to Serre's $\varepsilon_v$ (`hasseCassels_eq_hasseSerre`). -/
@[kb "cassels1978" "Ch. 4, §1, p. 55 (over ℚ_p; the same formula over F_v)"]
noncomputable def hasseCassels (v : NFPlace F) (a : Fin n → F) : ℤ :=
  ∏ i, ∏ j, if i < j then v.hilbert (a i) (a j) else 1

/-- **O'Meara's Hasse symbol $S_v$** of $\langle a_0,\dots,a_{n-1}\rangle$, $a_i \in F^\times$, at a place $v$ of
the number field $F$ (*Introduction to Quadratic Forms*, §63B, p. 167, after 63:13a, where O'Meara works over a
number field $F$ and its completions $F_{\mathfrak p}$, including the infinite spots):
$$S_v = \prod_{0 \le i \le j < n} (a_i, a_j)_v,$$
including the diagonal pairs. Related to Serre's by $S_v = \varepsilon_v\,(d,d)_v$ (`hasseOMeara_eq`). -/
@[kb "omeara1963" "§63B, p. 167 (Hasse symbol S_p V); §58, p. 150 (Hasse algebra)"]
noncomputable def hasseOMeara (v : NFPlace F) (a : Fin n → F) : ℤ :=
  ∏ i, ∏ j, if i ≤ j then v.hilbert (a i) (a j) else 1

/-- **Lam's Hasse–Witt invariant $s$** of $\langle a_0,\dots,a_{n-1}\rangle$ over the completion $F_v$ of the
number field $F$ (*Introduction to Quadratic Forms over Fields*, V.3 [unverified locator and formula, as in
`RatPlace.hasseLam`]): $s_v = \prod_{0 \le i < j < n}(a_i,a_j)_v$. Equal to Serre's $\varepsilon_v$
(`hasseLam_eq_hasseSerre`). -/
@[kb "lam2005" "Ch. V, §3 [unverified]"]
noncomputable def hasseLam (v : NFPlace F) (a : Fin n → F) : ℤ :=
  ∏ i, ∏ j, if i < j then v.hilbert (a i) (a j) else 1

/-- **Hasse's original invariant $\alpha_v$, as recorded by Shimura** (*Arithmetic of Quadratic Forms*, §28.13,
p. 160, over a number field $F$): for $\varphi = \sum a_i x_i^2$, $a_i \in F^\times$,
$$\alpha_v(\varphi) = \prod_{0 \le i \le j < n} (a_i, a_j)_v.$$
Shimura notes that "some later authors" use $\alpha'_v = \prod_{i<j}$ instead (`hasseSerre`); see
`RatPlace.hasseShimura` for the full reading of §28.13. Equal to O'Meara's $S_v$
(`hasseShimura_eq_hasseOMeara`). -/
@[kb "shimura2010" "§28.13, p. 160"]
noncomputable def hasseShimura (v : NFPlace F) (a : Fin n → F) : ℤ :=
  ∏ i, ∏ j, if i ≤ j then v.hilbert (a i) (a j) else 1

/-- Lam's $s_v$ is Serre's $\varepsilon_v$. -/
theorem hasseLam_eq_hasseSerre (v : NFPlace F) (a : Fin n → F) : v.hasseLam a = v.hasseSerre a := rfl

/-- Cassels' $c_v$ is Serre's $\varepsilon_v$. -/
theorem hasseCassels_eq_hasseSerre (v : NFPlace F) (a : Fin n → F) :
    v.hasseCassels a = v.hasseSerre a := rfl

/-- Hasse's $\alpha_v$ (Shimura §28.13) is O'Meara's $S_v$. -/
theorem hasseShimura_eq_hasseOMeara (v : NFPlace F) (a : Fin n → F) :
    v.hasseShimura a = v.hasseOMeara a := rfl

/-! ### Conversions -/

theorem prod_hilbert_self (v : NFPlace F) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    ∏ i, v.hilbert (a i) (a i) = v.hilbert (diagDet a) (diagDet a) := by
  have hd : diagDet a ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  rw [hilbert_self v hd, diagDet, hilbert_prod_left v (by norm_num) univ a (fun i _ => ha i)]
  exact prod_congr rfl fun i _ => hilbert_self v (ha i)

/-- **O'Meara/Hasse from Serre over $F$:** $S_v = \varepsilon_v\,(d,d)_v$, $d = \prod_i a_i$. -/
@[kb "omeara1963" "§63B, p. 167 (Hasse symbol; derived identity)"]
theorem hasseOMeara_eq (v : NFPlace F) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    v.hasseOMeara a = v.hasseSerre a * v.hilbert (diagDet a) (diagDet a) := by
  unfold hasseOMeara hasseSerre
  rw [prod_ite_le_eq, prod_hilbert_self v a ha]

/-- $S_v = \varepsilon_v\,(-1,d)_v$ over $F$. -/
@[kb "omeara1963" "§63B, p. 167 (Hasse symbol; derived identity)"]
theorem hasseOMeara_eq_negOne (v : NFPlace F) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    v.hasseOMeara a = v.hasseSerre a * v.hilbert (-1) (diagDet a) := by
  have hd : diagDet a ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  rw [hasseOMeara_eq v a ha, hilbert_self v hd, hilbert_comm]

/-- **Serre from O'Meara over $F$:** $\varepsilon_v = S_v\,(d,d)_v$. -/
@[kb "omeara1963" "§63B, p. 167 (Hasse symbol; derived identity)"]
theorem hasseSerre_eq (v : NFPlace F) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    v.hasseSerre a = v.hasseOMeara a * v.hilbert (diagDet a) (diagDet a) := by
  rw [hasseOMeara_eq v a ha, mul_assoc]
  rcases hilbert_eq_one_or v (diagDet a) (diagDet a) with h | h <;> rw [h] <;> ring_nf

/-- $S_v = \varepsilon_v\,(-1,-1)_v\,(-1,-d)_v$ over $F$. -/
@[kb "omeara1963" "§63B, p. 167 (Hasse symbol; derived identity)"]
theorem hasseOMeara_eq_negOne_neg (v : NFPlace F) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    v.hasseOMeara a = v.hasseSerre a * (v.hilbert (-1) (-1) * v.hilbert (-1) (-diagDet a)) := by
  have hd : diagDet a ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  rw [hasseOMeara_eq_negOne v a ha, show -diagDet a = -1 * diagDet a by ring,
    hilbert_mul_right v (by norm_num) (by norm_num) hd, ← mul_assoc]
  rcases hilbert_eq_one_or v (-1) (-1) with h | h <;> rw [h] <;> ring_nf

/-- **In terms of Shimura's signed discriminant $\delta$ over $F$:**
$S_v = \varepsilon_v\,(\delta,\delta)_v\,(-1,-1)_v^{\,n(n-1)/2}$. -/
@[kb "shimura2010" "§22.6, p. 119 + §28.13, p. 160 (derived)"]
theorem hasseOMeara_eq_signedDisc (v : NFPlace F) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    v.hasseOMeara a = v.hasseSerre a * v.hilbert (diagSignedDisc a) (diagSignedDisc a) *
      (v.hilbert (-1) (-1)) ^ (n * (n - 1) / 2) := by
  have hd : diagDet a ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  have hδ : diagSignedDisc a ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hd
  have hδ' : diagSignedDisc a = (-1) ^ (n * (n - 1) / 2) * diagDet a := rfl
  rw [hasseOMeara_eq v a ha, hilbert_self v hδ, hilbert_self v hd, hδ']
  rcases Nat.even_or_odd (n * (n - 1) / 2) with hev | hodd
  · rw [hev.neg_one_pow, one_mul]
    rcases hilbert_eq_one_or v (-1) (-1) with h | h <;> simp [h, hev.neg_one_pow]
  · rw [hodd.neg_one_pow, hilbert_mul_left v (by norm_num) hd (by norm_num)]
    rcases hilbert_eq_one_or v (-1) (-1) with h | h <;> simp [h, hodd.neg_one_pow]

end NFPlace

/-! ### Product formulas over all places of $F$ -/

section Product

/-- A $\pm1$-valued function on a type with finitely many, and an even number of, $-1$'s has finite
multiplicative support and finite product $1$. Internal. -/
theorem finprod_eq_one_of_signs {P : Type*} (s : P → ℤ) (hpm : ∀ v, s v = 1 ∨ s v = -1)
    (hF : {v | s v = -1}.Finite) (hE : Even {v | s v = -1}.ncard) :
    Function.HasFiniteMulSupport s ∧ ∏ᶠ v, s v = 1 := by
  have hms : Function.mulSupport s = {v | s v = -1} := by
    ext v
    rcases hpm v with h | h <;> simp [Function.mem_mulSupport, h]
  refine ⟨by rw [Function.HasFiniteMulSupport, hms]; exact hF, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hF.toFinset) (by rw [hms]; simp)]
  rw [Finset.prod_congr rfl (fun v hv => (by simpa using hv : s v = -1))]
  rw [Finset.prod_const, neg_one_pow_eq_one_iff_even (by decide)]
  rwa [← Set.ncard_eq_toFinset_card _ hF]

/-- A finite product of functions with finite support and product $1$ has the same property. Internal. -/
theorem finprod_prod_eq_one {P ι : Type*} (S : Finset ι) (s : ι → P → ℤ)
    (h : ∀ k ∈ S, Function.HasFiniteMulSupport (s k) ∧ ∏ᶠ v, s k v = 1) :
    Function.HasFiniteMulSupport (fun v => ∏ k ∈ S, s k v) ∧ ∏ᶠ v, ∏ k ∈ S, s k v = 1 := by
  refine ⟨?_, ?_⟩
  · refine (S.finite_toSet.biUnion fun k hk => (h k hk).1).subset ?_
    simpa using mulSupport_prod S (fun (k : ι) (v : P) => s k v)
  · rw [finprod_prod_comm S (fun (v : P) (k : ι) => s k v) fun k hk => (h k hk).1]
    exact prod_eq_one fun k hk => (h k hk).2

theorem NFPlace.finprod_hilbert (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    Function.HasFiniteMulSupport (fun v : NFPlace F => v.hilbert x y) ∧
      ∏ᶠ v : NFPlace F, v.hilbert x y = 1 :=
  finprod_eq_one_of_signs _ (fun v => NFPlace.hilbert_eq_one_or v x y)
    (hilbert_reciprocity_nf x y hx hy).1 (hilbert_reciprocity_nf x y hx hy).2

theorem NFPlace.finprod_pairs (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)] (a : Fin n → F)
    (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport
        (fun v : NFPlace F => ∏ i, ∏ j, if P i j then v.hilbert (a i) (a j) else 1) ∧
      ∏ᶠ v : NFPlace F, (∏ i, ∏ j, if P i j then v.hilbert (a i) (a j) else 1) = 1 := by
  simp only [prod_pairs_eq P (fun i j => _)]
  exact finprod_prod_eq_one _ (fun (p : Fin n × Fin n) (v : NFPlace F) => v.hilbert (a p.1) (a p.2))
    fun p _ => NFPlace.finprod_hilbert _ _ (ha _) (ha _)

/-- **Product formula for Serre's $\varepsilon$ over a number field $F$:** for $a_i \in F^\times$,
$\varepsilon_v(\langle a\rangle) = 1$ at all but finitely many places $v$ of $F$ and
$\prod_v \varepsilon_v(\langle a\rangle) = 1$ (Hilbert reciprocity over $F$, `hilbert_reciprocity_nf`, for each pair). -/
@[kb "omeara1963" "§71D, 71:18, p. 201 (applied to each pair) + Serre Ch. IV, §2.1 (derived)"]
theorem NFPlace.hasseSerre_product_formula (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : NFPlace F => v.hasseSerre a) ∧
      ∏ᶠ v : NFPlace F, v.hasseSerre a = 1 :=
  NFPlace.finprod_pairs (fun i j => i < j) a ha

/-- **Product formula for Cassels' $c$ over a number field $F$.** -/
@[kb "cassels1978" "Ch. 6, Lemma 1.1, p. 76 (over ℚ; over F derived)"]
theorem NFPlace.hasseCassels_product_formula (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : NFPlace F => v.hasseCassels a) ∧
      ∏ᶠ v : NFPlace F, v.hasseCassels a = 1 :=
  NFPlace.finprod_pairs (fun i j => i < j) a ha

/-- **Product formula for O'Meara's Hasse symbol over a number field $F$:** $S_v = 1$ for almost all $v$ and
$\prod_v S_v = 1$ (O'Meara: Example 66:6, p. 189, for almost all $v$; the product is condition (3) of 72:1, p. 203, from Hilbert
reciprocity 71:18, p. 201). -/
@[kb "omeara1963" "§66, 66:6, p. 189 (S_p V = 1 almost everywhere); §72, 72:1 (3), p. 203 (∏ S_p V = 1)"]
theorem NFPlace.hasseOMeara_product_formula (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : NFPlace F => v.hasseOMeara a) ∧
      ∏ᶠ v : NFPlace F, v.hasseOMeara a = 1 :=
  NFPlace.finprod_pairs (fun i j => i ≤ j) a ha

/-- **Product formula for Lam's $s$ over a number field $F$.** -/
@[kb "lam2005" "Ch. V, §3 [unverified]"]
theorem NFPlace.hasseLam_product_formula (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : NFPlace F => v.hasseLam a) ∧
      ∏ᶠ v : NFPlace F, v.hasseLam a = 1 :=
  NFPlace.finprod_pairs (fun i j => i < j) a ha

/-- **Product formula for Hasse's $\alpha_v$ (Shimura §28.13) over a number field $F$.** -/
@[kb "shimura2010" "§28.13, p. 160"]
theorem NFPlace.hasseShimura_product_formula (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : NFPlace F => v.hasseShimura a) ∧
      ∏ᶠ v : NFPlace F, v.hasseShimura a = 1 :=
  NFPlace.finprod_pairs (fun i j => i ≤ j) a ha

end Product

/-! ### Specialization to $F = \mathbb{Q}$ -/

section Specialization

namespace NFPlace

/-- **Serre's $\varepsilon_v$ over $F = \mathbb{Q}$ is the $\mathbb{Q}$ version** at the corresponding `RatPlace`. -/
@[kb "serre1973" "Ch. IV, §2.1, p. 35"]
theorem hasseSerre_rat (v : NFPlace ℚ) (a : Fin n → ℚ) : v.hasseSerre a = v.toRatPlace.hasseSerre a := by
  simp only [hasseSerre, RatPlace.hasseSerre, toRatPlace_hilbert]

/-- Cassels' $c_v$ over $F = \mathbb{Q}$ is the $\mathbb{Q}$ version. -/
@[kb "cassels1978" "Ch. 4, §1, p. 55"]
theorem hasseCassels_rat (v : NFPlace ℚ) (a : Fin n → ℚ) :
    v.hasseCassels a = v.toRatPlace.hasseCassels a := hasseSerre_rat v a

/-- **O'Meara's $S_v$ over $F = \mathbb{Q}$ is the $\mathbb{Q}$ version.** -/
@[kb "omeara1963" "§63B, p. 167 (Hasse symbol)"]
theorem hasseOMeara_rat (v : NFPlace ℚ) (a : Fin n → ℚ) :
    v.hasseOMeara a = v.toRatPlace.hasseOMeara a := by
  simp only [hasseOMeara, RatPlace.hasseOMeara, toRatPlace_hilbert]

/-- Lam's $s_v$ over $F = \mathbb{Q}$ is the $\mathbb{Q}$ version. -/
@[kb "lam2005" "Ch. V, §3 [unverified]"]
theorem hasseLam_rat (v : NFPlace ℚ) (a : Fin n → ℚ) : v.hasseLam a = v.toRatPlace.hasseLam a :=
  hasseSerre_rat v a

/-- Hasse's $\alpha_v$ (Shimura §28.13) over $F = \mathbb{Q}$ is the $\mathbb{Q}$ version. -/
@[kb "shimura2010" "§28.13, p. 160"]
theorem hasseShimura_rat (v : NFPlace ℚ) (a : Fin n → ℚ) :
    v.hasseShimura a = v.toRatPlace.hasseShimura a := hasseOMeara_rat v a

/-- **The $\mathbb{Q}$ product formula is the $F = \mathbb{Q}$ case of the number-field one** (for O'Meara's $S$;
the others are the same argument): $\prod_{v \in \mathrm{NFPlace}\,\mathbb{Q}} S_v = \prod_{v \in \mathrm{RatPlace}} S_v$,
reindexing along the bijection `toRatPlace`. -/
theorem finprod_hasseOMeara_rat (a : Fin n → ℚ) :
    ∏ᶠ v : NFPlace ℚ, v.hasseOMeara a = ∏ᶠ v : RatPlace, v.hasseOMeara a := by
  rw [← finprod_comp_equiv (Equiv.ofBijective _ toRatPlace_bijective)]
  exact finprod_congr fun v => hasseOMeara_rat v a

end NFPlace

end Specialization

/-! ### Isometry invariance: what the dictionary gives -/

section Invariance

namespace NFPlace

omit [NumberField F] in
theorem isometricIn_cast {K : Type*} [Field K] [Algebra F K] (a b : Fin n → F) :
    (QuadForm.diag a).IsometricIn K (QuadForm.diag b) ↔
      (QuadForm.diag fun i => algebraMap F K (a i)).IsometricIn K
        (QuadForm.diag fun i => algebraMap F K (b i)) := by
  simp only [QuadForm.IsometricIn, QuadForm.evalIn_diag, Algebra.algebraMap_self, RingHom.id_apply]

theorem sameSq_gen {K : Type*} [Field K] [CharZero K] [Algebra F K] (a b : Fin n → F)
    (h : (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    ∃ t : K, t ≠ 0 ∧ algebraMap F K (diagDet b) = t ^ 2 * algebraMap F K (diagDet a) := by
  rw [isometricIn_cast] at h
  obtain ⟨t, ht, e⟩ := PadicClass.disc_of_isometric h
  exact ⟨t, ht, by simpa [diagDet] using e⟩

/-- **The correction $(d,d)_v$ is an isometry invariant over $F_v$:** if $\langle a\rangle \cong \langle b\rangle$
over the completion $F_v$, then $(d_a,d_a)_v = (d_b,d_b)_v$ (the square class of $d$ is an invariant). -/
theorem hilbert_diagDet_self_isometric (v : NFPlace F) (a b : Fin n → F)
    (h : v.atPlace fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    v.hilbert (diagDet a) (diagDet a) = v.hilbert (diagDet b) (diagDet b) := by
  cases v with
  | infinite w =>
    haveI : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    obtain ⟨t, ht, e⟩ := sameSq_gen (K := w.Completion) a b h
    simp only [hilbert]; rw [e, hs_sq_left _ _ _ ht, hs_sq_right _ _ _ ht]
  | finite v =>
    haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
    obtain ⟨t, ht, e⟩ := sameSq_gen (K := v.adicCompletion F) a b h
    simp only [hilbert]; rw [e, hs_sq_left _ _ _ ht, hs_sq_right _ _ _ ht]

/-- **O'Meara's $S_v$ is an isometry invariant over $F_v$ as soon as Serre's $\varepsilon_v$ is** (by
`hasseOMeara_eq` and `hilbert_diagDet_self_isometric`). The unconditional version is `NFPlace.hasseOMeara_isometric`
(`HasseIsometryNF.lean`). -/
@[kb "omeara1963" "§63B, p. 167 (Hasse symbol); §63C, 63:20, p. 170"]
theorem hasseOMeara_isometric_of_hasseSerre (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0)
    (h : v.atPlace fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b))
    (hε : v.hasseSerre a = v.hasseSerre b) :
    v.hasseOMeara a = v.hasseOMeara b := by
  rw [hasseOMeara_eq v a ha, hasseOMeara_eq v b hb, hε, hilbert_diagDet_self_isometric v a b h]

end NFPlace

end Invariance

end QuadFormsKB
