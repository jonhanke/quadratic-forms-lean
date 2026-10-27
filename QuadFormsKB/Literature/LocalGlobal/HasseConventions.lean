/-
# Hasse invariants in all conventions

For a nondegenerate diagonal form $\langle a_0,\dots,a_{n-1}\rangle$, $a_i \in \mathbb{Q}^\times$, at a place
$v$ of $\mathbb{Q}$ (so over $\mathbb{R}$ or $\mathbb{Q}_p$), the literature uses several invariants
built from the Hilbert symbols $(a_i,a_j)_v$. Each is defined here as its own declaration
(`RatPlace.hasseSerre`, `hasseCassels`, `hasseOMeara`, `hasseLam`, `hasseShimura`, `hasseConwaySloane`), then:

* the exact conversions (Section "Conversions"): with $d = \prod a_i$, $\delta = (-1)^{n(n-1)/2} d$,
  $S = \varepsilon\,(d,d) = \varepsilon\,(-1,d) = \varepsilon\,(\delta,\delta)\,(-1,-1)^{n(n-1)/2}
  = \varepsilon\,(-1,-1)\,(-1,-d)$, where $\varepsilon$ is the $\prod_{i<j}$ invariant (Serre, Cassels' $c$) and
  $S$ the $\prod_{i\le j}$ one (O'Meara, Hasse's $\alpha_v$ as in Shimura §28.13);
* isometry invariance of each, derived from the invariance of Serre's $\varepsilon$ over $\mathbb{Q}_p$
  (`hasseInvariant_isometric`), over $\mathbb{R}$ (Sylvester's law, Mathlib) and the invariance of the
  discriminant square class;
* the product formula over all places of $\mathbb{Q}$ in each convention.
-/
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity
import QuadFormsKB.Witt.Bridge
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace QuadFormsKB

open Finset QuadForm PadicClass

variable {n : ℕ}

/-! ### Basic properties of the Hilbert symbol at a place of $\mathbb{Q}$ -/

namespace RatPlace

theorem hilbert_pm (v : RatPlace) (a b : ℚ) : v.hilbert a b = 1 ∨ v.hilbert a b = -1 := by
  cases v <;> exact hs_pm _ _

theorem hilbert_comm (v : RatPlace) (a b : ℚ) : v.hilbert a b = v.hilbert b a := by
  cases v <;> exact hilbertSymbol_comm _ _ _

theorem hilbert_mul_right (v : RatPlace) (a b b' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    v.hilbert a (b * b') = v.hilbert a b * v.hilbert a b' := by
  rw [hilbert_comm, HilbertLocal.RatPlace.hilbert_mul_left v b b' a hb hb' ha,
    hilbert_comm v b, hilbert_comm v b']

theorem hilbert_self_neg (v : RatPlace) (a : ℚ) : v.hilbert a (-a) = 1 := by
  cases v <;> simp only [RatPlace.hilbert, Rat.cast_neg] <;> exact hilbertSymbol_self_neg _ _

theorem hilbert_self (v : RatPlace) (a : ℚ) (ha : a ≠ 0) : v.hilbert a a = v.hilbert a (-1) := by
  have h := hilbert_self_neg v a
  rw [show -a = -1 * a by ring, hilbert_mul_right v a (-1) a ha (by norm_num) ha] at h
  rcases hilbert_pm v a (-1) with h1 | h1 <;> rw [h1] at h ⊢ <;> linarith

theorem hilbert_sq_right (v : RatPlace) (a c : ℚ) (hc : c ≠ 0) : v.hilbert a (c ^ 2) = 1 := by
  cases v <;> simp only [RatPlace.hilbert, Rat.cast_pow] <;>
    exact hs_sq _ _ (by exact_mod_cast hc)

theorem hilbert_prod_left (v : RatPlace) (b : ℚ) (hb : b ≠ 0) {ι : Type*} (s : Finset ι)
    (a : ι → ℚ) (ha : ∀ i ∈ s, a i ≠ 0) :
    v.hilbert (∏ i ∈ s, a i) b = ∏ i ∈ s, v.hilbert (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    cases v <;> simp only [RatPlace.hilbert, Rat.cast_one] <;> exact hs_one_left _
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj,
      HilbertLocal.RatPlace.hilbert_mul_left v _ _ b (ha j (mem_insert_self _ _))
        (prod_ne_zero_iff.mpr fun i hi => ha i (mem_insert_of_mem hi)) hb,
      ih fun i hi => ha i (mem_insert_of_mem hi)]

end RatPlace

/-! ### The conventions -/

/-- **The determinant $d = \prod_i a_i$ of the diagonal form $\langle a_0,\dots,a_{n-1}\rangle$**
(coefficients in a commutative ring $R$; used for $R = \mathbb{Q}$ here and for a number field $F$ in
`HasseConventionsNF.lean`; for $a_i \in \mathbb{Q}^\times$ an element of $\mathbb{Q}^\times$, well defined modulo squares in each completion). Serre's
$d$ (IV.1.1, p. 27: $\det$ of the Gram matrix, "disc"; written $d(Q)$ in IV.2.1, p. 35), Cassels'
$d(f)$ (Ch. 4 §1, p. 55: the determinant, as an element of $k^\times/(k^\times)^2$), O'Meara's $dV$,
Lam's $d$ (the "determinant"; Lam's $d_\pm$ is `diagSignedDisc`). -/
def diagDet {R : Type*} [CommMonoid R] (a : Fin n → R) : R := ∏ i, a i

/-- **The signed discriminant $\delta = (-1)^{n(n-1)/2} \prod_i a_i$** of
$\langle a_0,\dots,a_{n-1}\rangle$ (0-based indices; $n(n-1)/2$ is the number of pairs $i < j$).
Shimura's discriminant coset $\delta_0(\varphi) = (-1)^{n(n-1)/2}\det(\Phi)\,F^{\times2}$
(*Arithmetic of Quadratic Forms*, §22.6, p. 119: "The factor $(-1)^{n(n-1)/2}$ may look
artificial"; the Gram matrix of $\varphi$ in an orthogonal basis is $\mathrm{diag}(a_i)$, so this is
exactly `diagSignedDisc`, up to squares); Lam's signed discriminant $d_\pm$ (V.2.? [unverified;
Lam's book is not available locally]). -/
def diagSignedDisc {R : Type*} [CommRing R] (a : Fin n → R) : R := (-1) ^ (n * (n - 1) / 2) * ∏ i, a i

namespace RatPlace

/-- **Serre's Hasse invariant $\varepsilon$ at the place $v$** of
$\langle a_0,\dots,a_{n-1}\rangle$, $a_i \in \mathbb{Q}^\times$ (*A Course in Arithmetic*, Ch. IV, §2.1,
p. 35, where it is written $\varepsilon(e) = \prod_{i<j}(a_i,a_j)$; Theorem 5, p. 35, is its independence
of the orthogonal basis):
$$\varepsilon_v = \prod_{0 \le i < j < n} (a_i, a_j)_v.$$
This is `hasseInvariant` over $\mathbb{R}$ or $\mathbb{Q}_p$ (`hasseSerre_infinite`,
`hasseSerre_finite`). The invariant of the form, independent of the diagonalization, is
`hasseSerre_isometric`. -/
@[kb "serre1973" "Ch. IV, §2.1, p. 35"]
noncomputable def hasseSerre (v : RatPlace) (a : Fin n → ℚ) : ℤ :=
  ∏ i, ∏ j, if i < j then v.hilbert (a i) (a j) else 1

/-- **Cassels' Hasse–Minkowski invariant $c_v$** of $\langle a_0,\dots,a_{n-1}\rangle$ (*Rational
Quadratic Forms*, Ch. 4, §1, p. 55):
$$c_v = \prod_{0 \le i < j < n} (a_i, a_j)_v,$$
**excluding** the diagonal pairs. This is Serre's $\varepsilon_v$ (`hasseCassels_eq_hasseSerre`, `rfl`).
*Clarification:* Cassels' product is sometimes recorded as $\prod_{i\le j}$; checked
against the book (p. 55 and Lemma 2.3(iii), p. 58: $c(f+g) = (d(f),d(g))\,c(f)c(g)$, which is
the $i<j$ product), it is $\prod_{i<j}$. Cassels' footnote there warns that "there are several
definitions of the Hasse–Minkowski invariant in the literature. Each differs from the other by a
factor depending on the number of variables and the determinant." The $i\le j$ product is
`hasseOMeara`. -/
@[kb "cassels1978" "Ch. 4, §1, p. 55"]
noncomputable def hasseCassels (v : RatPlace) (a : Fin n → ℚ) : ℤ :=
  ∏ i, ∏ j, if i < j then v.hilbert (a i) (a j) else 1

/-- **O'Meara's Hasse symbol $S_v$** of $\langle a_0,\dots,a_{n-1}\rangle$ (*Introduction to
Quadratic Forms*, §63B, p. 167, after 63:13a):
$$S_v = \prod_{0 \le i \le j < n} (a_i, a_j)_v,$$
**including** the diagonal pairs $i = j$. O'Meara first defines $S_{\mathfrak p}V = \prod_{i}
\big(\tfrac{\alpha_i, d_i}{\mathfrak p}\big)$ with $d_i = \alpha_1\cdots\alpha_i$ and then states
"from Remark 58:3 we get the formulas" $S_{\mathfrak p}V = \prod_{1\le i\le j\le n}(\alpha_i,\alpha_j)$,
$S_{\mathfrak p}(U\perp W) = S_{\mathfrak p}U\cdot(dU,dW)\cdot S_{\mathfrak p}W$ (the $\alpha_i$ are the
entries of an orthogonal splitting). The Hasse *algebra* it is built from is §58, p. 150. This is also
Hasse's original $\alpha_v$ (see `hasseShimura`). Related to Serre's by $S_v = \varepsilon_v\,(d,d)_v$
(`hasseOMeara_eq`). *Clarification:* this product is sometimes attributed to Cassels as well; Cassels'
$c$ is the $i<j$ product (`hasseCassels`). -/
@[kb "omeara1963" "§63B, p. 167 (Hasse symbol S_p V); §58, p. 150 (Hasse algebra)"]
noncomputable def hasseOMeara (v : RatPlace) (a : Fin n → ℚ) : ℤ :=
  ∏ i, ∏ j, if i ≤ j then v.hilbert (a i) (a j) else 1

/-- **Lam's Hasse–Witt invariant $s$** of $\langle a_0,\dots,a_{n-1}\rangle$ (*Introduction to
Quadratic Forms over Fields*, V.3 [unverified locator and formula; Lam's book is not available
locally]):
$$s_v = \prod_{0 \le i < j < n} (a_i, a_j)_v.$$
Same formula as Serre's $\varepsilon$ (`hasseLam_eq_hasseSerre`). Lam's *Witt invariant* $c$ (the
class of the Clifford algebra) differs from $s$ by a factor depending on $n \bmod 8$ and $d$; it
belongs to the Clifford-algebra work, not here. -/
@[kb "lam2005" "Ch. V, §3 [unverified]"]
noncomputable def hasseLam (v : RatPlace) (a : Fin n → ℚ) : ℤ :=
  ∏ i, ∏ j, if i < j then v.hilbert (a i) (a j) else 1

/-- **Hasse's original invariant $\alpha_v$, as recorded by Shimura** (*Arithmetic of Quadratic
Forms*, §28.13, p. 160): for $\varphi = \sum a_i x_i^2$,
$$\alpha_v(\varphi) = \prod_{0 \le i \le j < n} (a_i, a_j)_v.$$
*Clarification:* Shimura does **not** use a Hasse invariant in his own development; he classifies
forms by the dimension, the discriminant $\delta_0$ (`diagSignedDisc`, §22.6), the signatures
$s_v$ and the characteristic (Clifford) algebra $Q(\varphi)$ (Thm. 28.9). In §28.13 he describes
Hasse's $\alpha_v(\varphi) = \prod_{i\le j}(a_i,a_j)_v$ (this declaration) and says "Some later
authors chose $\alpha'_v(\varphi) = \prod_{i<j}(a_i,a_j)_v$ instead" (`hasseSerre`), remarking that both
equal $-1$ at $v=2$ for the hyperbolic form $x_1x_2+x_3x_4$ over $\mathbb{Q}$. (It is sometimes
recorded as $\prod_{i<j}$ for Shimura.) Same formula as `hasseOMeara`
(`hasseShimura_eq_hasseOMeara`). -/
@[kb "shimura2010" "§28.13, p. 160"]
noncomputable def hasseShimura (v : RatPlace) (a : Fin n → ℚ) : ℤ :=
  ∏ i, ∏ j, if i ≤ j then v.hilbert (a i) (a j) else 1

/-- **Conway–Sloane's Hasse–Minkowski invariant $(f)_p$** of $f = \langle a_0,\dots,a_{n-1}\rangle$
(*Sphere Packings, Lattices and Groups*, Ch. 15, §5.3, p. 373, eq. (17), following Cassels, p. 55):
$$(f)_p = (A_1, A_2, \dots, A_n)_p = \prod_{1 \le i < j \le n} (A_i, A_j)_p,$$
here 0-based ($A_{i+1}$ is `a i`), **excluding** the diagonal pairs. Conway–Sloane call the archimedean place the
"prime $-1$" (Ch. 15, §4.4, Note after Theorem 2, p. 370); it is `RatPlace.infinite` here. Same formula as Serre's $\varepsilon$
(`hasseConwaySloane_eq_hasseSerre`, `rfl`). The book avoids the Hilbert symbol in its own development (§5, p. 370); it states (§5.3) that
$(f)_p = \pm1$ according as the $p$-excess of $f$ is or is not $\equiv$ that of the "standard" form
$f_0 = \mathrm{diag}\{A_1\cdots A_n, 1, \dots, 1\}$ (mod 8), which is
`ConwaySloane.hasseConwaySloane_eq_one_iff`. -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373, eq. (17)"]
noncomputable def hasseConwaySloane (v : RatPlace) (a : Fin n → ℚ) : ℤ :=
  ∏ i, ∏ j, if i < j then v.hilbert (a i) (a j) else 1

/-- Conway–Sloane's $(f)_p$ is Serre's $\varepsilon$. -/
theorem hasseConwaySloane_eq_hasseSerre (v : RatPlace) (a : Fin n → ℚ) :
    v.hasseConwaySloane a = v.hasseSerre a := rfl

/-- Lam's $s$ is Serre's $\varepsilon$. -/
theorem hasseLam_eq_hasseSerre (v : RatPlace) (a : Fin n → ℚ) :
    v.hasseLam a = v.hasseSerre a := rfl

/-- Hasse's $\alpha_v$ (as recorded by Shimura, §28.13) is O'Meara's $S_v$. -/
theorem hasseShimura_eq_hasseOMeara (v : RatPlace) (a : Fin n → ℚ) :
    v.hasseShimura a = v.hasseOMeara a := rfl

/-- Cassels' $c$ is Serre's $\varepsilon$. -/
theorem hasseCassels_eq_hasseSerre (v : RatPlace) (a : Fin n → ℚ) :
    v.hasseCassels a = v.hasseSerre a := rfl

/-- `hasseSerre` is `hasseInvariant` over $\mathbb{R}$. -/
theorem hasseSerre_infinite (a : Fin n → ℚ) :
    RatPlace.infinite.hasseSerre a = hasseInvariant ℝ a := by
  simp [hasseSerre, hasseInvariant, RatPlace.hilbert]

/-- `hasseSerre` is `hasseInvariant` over $\mathbb{Q}_p$. -/
theorem hasseSerre_finite (p : Nat.Primes) (a : Fin n → ℚ) :
    haveI : Fact p.1.Prime := ⟨p.2⟩
    (RatPlace.finite p).hasseSerre a = hasseInvariant ℚ_[p.1] a := by
  haveI : Fact p.1.Prime := ⟨p.2⟩
  simp [hasseSerre, hasseInvariant, RatPlace.hilbert]

end RatPlace

/-! ### Conversions -/

section Conversions

open RatPlace

theorem prod_ite_le_eq (f : Fin n → Fin n → ℤ) :
    (∏ i, ∏ j, if i ≤ j then f i j else 1) =
      (∏ i, ∏ j, if i < j then f i j else 1) * ∏ i, f i i := by
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have : ∀ j, (if i ≤ j then f i j else 1) = (if i < j then f i j else 1) * (if i = j then f i j else 1) := by
    intro j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.le, h.ne]
    · simp [h]
    · simp [h.not_ge, h.not_gt, h.ne']
  simp only [this, prod_mul_distrib, prod_ite_eq, mem_univ, if_true]

theorem hilbert_mul_left_aux (v : RatPlace) {d : ℚ} (hd : d ≠ 0) :
    v.hilbert (-1 * d) (-1) = v.hilbert (-1) (-1) * v.hilbert d (-1) :=
  HilbertLocal.RatPlace.hilbert_mul_left v (-1) d (-1) (by norm_num) hd (by norm_num)

variable (v : RatPlace) (a : Fin n → ℚ)

theorem prod_hilbert_self (ha : ∀ i, a i ≠ 0) :
    ∏ i, v.hilbert (a i) (a i) = v.hilbert (diagDet a) (diagDet a) := by
  have hd : diagDet a ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  rw [hilbert_self v _ hd, diagDet, hilbert_prod_left v (-1) (by norm_num) univ a (fun i _ => ha i)]
  exact prod_congr rfl fun i _ => hilbert_self v _ (ha i)

/-- **O'Meara/Hasse from Serre:** $S_v = \varepsilon_v\,(d,d)_v$, where $d = \prod a_i$ (the
extra factor is $\prod_i (a_i,a_i)_v = (d,d)_v$, from $(a,a)_v = (a,-1)_v$ and bimultiplicativity). -/
@[kb "serre1973" "Ch. IV, §2.1 / Ch. III, §1.1 (derived)"]
theorem hasseOMeara_eq (ha : ∀ i, a i ≠ 0) :
    v.hasseOMeara a = v.hasseSerre a * v.hilbert (diagDet a) (diagDet a) := by
  unfold hasseOMeara hasseSerre
  rw [prod_ite_le_eq, prod_hilbert_self v a ha]

/-- $S_v = \varepsilon_v\,(-1, d)_v$. -/
@[kb "serre1973" "Ch. IV, §2.1 / Ch. III, §1.1 (derived)"]
theorem hasseOMeara_eq_negOne (ha : ∀ i, a i ≠ 0) :
    v.hasseOMeara a = v.hasseSerre a * v.hilbert (-1) (diagDet a) := by
  have hd : diagDet a ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  rw [hasseOMeara_eq v a ha, hilbert_self v _ hd, hilbert_comm]

/-- **Serre from O'Meara:** $\varepsilon_v = S_v\,(d,d)_v$ (the correction has order $2$). -/
@[kb "serre1973" "Ch. IV, §2.1 / Ch. III, §1.1 (derived)"]
theorem hasseSerre_eq (ha : ∀ i, a i ≠ 0) :
    v.hasseSerre a = v.hasseOMeara a * v.hilbert (diagDet a) (diagDet a) := by
  rw [hasseOMeara_eq v a ha, mul_assoc]
  rcases hilbert_pm v (diagDet a) (diagDet a) with h | h <;> rw [h] <;> ring_nf

/-- $S_v = \varepsilon_v\,(-1,-1)_v\,(-1,-d)_v$. -/
@[kb "serre1973" "Ch. IV, §2.1 / Ch. III, §1.1 (derived)"]
theorem hasseOMeara_eq_negOne_neg (ha : ∀ i, a i ≠ 0) :
    v.hasseOMeara a = v.hasseSerre a * (v.hilbert (-1) (-1) * v.hilbert (-1) (-diagDet a)) := by
  have hd : diagDet a ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  rw [hasseOMeara_eq_negOne v a ha, show -diagDet a = -1 * diagDet a by ring,
    hilbert_mul_right v (-1) (-1) _ (by norm_num) (by norm_num) hd, ← mul_assoc]
  rcases hilbert_pm v (-1) (-1) with h | h <;> rw [h] <;> ring_nf

/-- **In terms of the signed discriminant $\delta$:**
$S_v = \varepsilon_v\,(\delta,\delta)_v\,(-1,-1)_v^{\,n(n-1)/2}$. -/
@[kb "serre1973" "Ch. IV, §2.1 / Ch. III, §1.1 (derived)"]
theorem hasseOMeara_eq_signedDisc (ha : ∀ i, a i ≠ 0) :
    v.hasseOMeara a = v.hasseSerre a * v.hilbert (diagSignedDisc a) (diagSignedDisc a) *
      (v.hilbert (-1) (-1)) ^ (n * (n - 1) / 2) := by
  have hd : diagDet a ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  have hδ : diagSignedDisc a ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hd
  have hδ' : diagSignedDisc a = (-1) ^ (n * (n - 1) / 2) * diagDet a := rfl
  rw [hasseOMeara_eq v a ha, hilbert_self v _ hδ, hilbert_self v _ hd, hδ']
  rcases Nat.even_or_odd (n * (n - 1) / 2) with hev | hodd
  · rw [hev.neg_one_pow, one_mul]
    rcases hilbert_pm v (-1) (-1) with h | h <;> simp [h, hev.neg_one_pow]
  · rw [hodd.neg_one_pow, hilbert_mul_left_aux v hd]
    rcases hilbert_pm v (-1) (-1) with h | h <;> simp [h, hodd.neg_one_pow]

end Conversions

/-! ### Isometry invariance -/

section Invariance

open RatPlace

/-- $y' = t^2 y$ for some $t \ne 0$ in the completion at $v$ (same square class). Internal. -/
def SameSqAt (v : RatPlace) (y y' : ℚ) : Prop :=
  RatPlace.atPlace (fun K _ _ => ∃ t : K, t ≠ 0 ∧ (y' : K) = t ^ 2 * (y : K)) v

theorem isometricIn_cast {K : Type*} [Field K] [CharZero K] (a b : Fin n → ℚ) :
    (diag a).IsometricIn K (diag b) ↔
      (diag fun i => algebraMap ℚ K (a i)).IsometricIn K (diag fun i => algebraMap ℚ K (b i)) := by
  simp only [IsometricIn, evalIn_diag, Algebra.algebraMap_self, RingHom.id_apply]

theorem sameSq_gen {K : Type*} [Field K] [CharZero K] (a b : Fin n → ℚ)
    (h : (diag a).IsometricIn K (diag b)) :
    ∃ t : K, t ≠ 0 ∧ ((∏ i, b i : ℚ) : K) = t ^ 2 * ((∏ i, a i : ℚ) : K) := by
  rw [isometricIn_cast] at h
  obtain ⟨t, ht, e⟩ := disc_of_isometric h
  refine ⟨t, ht, ?_⟩
  simpa using e

theorem sameSq_of_isometric (v : RatPlace) (a b : Fin n → ℚ)
    (h : RatPlace.atPlace (fun K _ _ => (diag a).IsometricIn K (diag b)) v) :
    SameSqAt v (diagDet a) (diagDet b) := by
  cases v with
  | infinite => exact sameSq_gen (K := ℝ) a b h
  | finite p => haveI : Fact p.1.Prime := ⟨p.2⟩; exact sameSq_gen (K := ℚ_[p.1]) a b h

theorem SameSqAt.mul_left {v : RatPlace} {y y' : ℚ} (h : SameSqAt v y y') (c : ℚ) :
    SameSqAt v (c * y) (c * y') := by
  cases v <;> (obtain ⟨t, ht, e⟩ := h; exact ⟨t, ht, by push_cast; rw [e]; ring⟩)

theorem SameSqAt.hilbert_right {v : RatPlace} {y y' : ℚ} (h : SameSqAt v y y') (x : ℚ) :
    v.hilbert x y' = v.hilbert x y := by
  cases v <;> (obtain ⟨t, ht, e⟩ := h; simp only [RatPlace.hilbert]; rw [e]; exact hs_sq_right _ _ _ ht)

theorem SameSqAt.hilbert_self {v : RatPlace} {y y' : ℚ} (h : SameSqAt v y y') :
    v.hilbert y' y' = v.hilbert y y := by
  cases v <;> (obtain ⟨t, ht, e⟩ := h; simp only [RatPlace.hilbert]; rw [e, hs_sq_left _ _ _ ht,
    hs_sq_right _ _ _ ht])

/-- The count of pairs $i<j$ of negative entries. Internal. -/
def negPairs (a : Fin n → ℚ) : ℕ :=
  ∑ i, ∑ j, if i < j then (if a i < 0 then 1 else 0) * (if a j < 0 then 1 else 0) else 0

def negCount (a : Fin n → ℚ) : ℕ := ∑ i, if a i < 0 then 1 else 0

theorem two_negPairs_add (a : Fin n → ℚ) : 2 * negPairs a + negCount a = negCount a ^ 2 := by
  set e : Fin n → ℕ := fun i => if a i < 0 then 1 else 0 with he
  have h1 : negCount a = ∑ i, e i := rfl
  have h2 : negPairs a = ∑ i, ∑ j, if i < j then e i * e j else 0 := rfl
  have hB : (∑ i, ∑ j, if j < i then e i * e j else 0) = negPairs a := by
    rw [h2, sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  have hD : (∑ i, ∑ j, if i = j then e i * e j else 0) = negCount a := by
    rw [h1]
    refine sum_congr rfl fun i _ => ?_
    have : e i * e i = e i := by simp only [he]; split_ifs <;> simp
    simp [this]
  have hsq : negCount a ^ 2 = ∑ i, ∑ j, e i * e j := by
    rw [h1, sq, sum_mul_sum]
  have htri : (∑ i, ∑ j, e i * e j) =
      (∑ i, ∑ j, if i < j then e i * e j else 0) + (∑ i, ∑ j, if j < i then e i * e j else 0) +
        ∑ i, ∑ j, if i = j then e i * e j else 0 := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt, h.ne]
    · simp [h]
    · simp [h, h.not_gt, h.ne']
  rw [hsq, htri, hB, hD, ← h2]
  ring

theorem hilbert_infinite_eq (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    RatPlace.infinite.hilbert x y = if x < 0 ∧ y < 0 then -1 else 1 := by
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  have H := hilbertSymbol_real (x : ℝ) (y : ℝ) hx' hy'
  by_cases hc : x < 0 ∧ y < 0
  · rw [if_pos hc]
    exact H.mpr ⟨by exact_mod_cast hc.1, by exact_mod_cast hc.2⟩
  · rw [if_neg hc]
    rcases hs_pm (K := ℝ) (x : ℝ) (y : ℝ) with h | h
    · exact h
    · exfalso
      obtain ⟨h1, h2⟩ := H.mp h
      exact hc ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem hasseSerre_infinite_eq (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) :
    RatPlace.infinite.hasseSerre a = (-1) ^ negPairs a := by
  unfold hasseSerre negPairs
  have key : ∀ i j : Fin n, (if i < j then RatPlace.infinite.hilbert (a i) (a j) else 1) =
      (-1 : ℤ) ^ (if i < j then (if a i < 0 then 1 else 0) * (if a j < 0 then 1 else 0) else 0) := by
    intro i j
    by_cases hij : i < j
    · rw [if_pos hij, if_pos hij, hilbert_infinite_eq _ _ (ha i) (ha j)]
      by_cases h1 : a i < 0 <;> by_cases h2 : a j < 0 <;> simp [h1, h2]
    · simp [hij]
  calc _ = ∏ i, ∏ j, (-1 : ℤ) ^ (if i < j then (if a i < 0 then 1 else 0) * (if a j < 0 then 1 else 0) else 0) :=
        prod_congr rfl fun i _ => prod_congr rfl fun j _ => key i j
    _ = _ := by simp_rw [prod_pow_eq_pow_sum]

/-- Over $\mathbb{R}$: $\varepsilon_\infty$ depends only on the number $r$ of negative entries,
$\varepsilon_\infty = (-1)^{r(r-1)/2}$ (in the form $2 N + r = r^2$, $\varepsilon = (-1)^N$). -/
theorem hasseSerre_infinite_eq_of_negCount (a b : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : negCount a = negCount b) :
    RatPlace.infinite.hasseSerre a = RatPlace.infinite.hasseSerre b := by
  rw [hasseSerre_infinite_eq a ha, hasseSerre_infinite_eq b hb]
  have h1 := two_negPairs_add a
  have h2 := two_negPairs_add b
  rw [h] at h1
  have : negPairs a = negPairs b := by omega
  rw [this]

theorem negCount_eq_of_isometric (a b : Fin n → ℚ)
    (h : (diag a).IsometricIn ℝ (diag b)) : negCount a = negCount b := by
  have tq : ∀ c : Fin n → ℚ, (diag c).toQuadraticFormIn ℝ =
      QuadraticMap.weightedSumSquares ℝ (fun i => ((c i : ℚ) : ℝ)) := by
    intro c
    ext x
    rw [toQuadraticFormIn_apply, evalIn_diag, QuadraticMap.weightedSumSquares_apply]
    simp [sq]
  have cnt : ∀ c : Fin n → ℚ, negCount c =
      {i | ((c i : ℚ) : ℝ) < 0}.ncard := by
    intro c
    have : {i | ((c i : ℚ) : ℝ) < 0} = ↑(univ.filter fun i => c i < 0) := by
      ext i; simp
    rw [this, Set.ncard_coe_finset, Finset.card_filter]
    rfl
  have e := (isometricIn_iff_equivalent ℝ (diag a) (diag b)).mp h
  have sa := QuadraticForm.sigNeg_of_equiv_weightedSumSquares (𝕜 := ℝ)
    (Q := (diag a).toQuadraticFormIn ℝ) (w := fun i => ((a i : ℚ) : ℝ)) (by rw [tq]; exact QuadraticMap.Equivalent.refl _)
  have sb := QuadraticForm.sigNeg_of_equiv_weightedSumSquares (𝕜 := ℝ)
    (Q := (diag b).toQuadraticFormIn ℝ) (w := fun i => ((b i : ℚ) : ℝ)) (by rw [tq]; exact QuadraticMap.Equivalent.refl _)
  rw [← cnt] at sa sb
  rw [← sa, ← sb]
  exact e.sigNeg_eq.symm

/-- **Isometry invariance of Serre's $\varepsilon_v$** (the headline, at every place of $\mathbb{Q}$):
if the nondegenerate diagonal forms $\langle a_i \rangle$ and $\langle b_i \rangle$ ($a_i, b_i \in
\mathbb{Q}^\times$) are isometric over the completion $\mathbb{Q}_v$, then
$\prod_{i<j}(a_i,a_j)_v = \prod_{i<j}(b_i,b_j)_v$.
At $v = p$ this is `hasseInvariant_isometric` (Serre IV §2.1); at $v = \infty$ it follows from
Sylvester's law of inertia (Mathlib `QuadraticForm.sigNeg_of_equiv_weightedSumSquares`), since
$\varepsilon_\infty = (-1)^{r(r-1)/2}$ for $r$ negative entries. -/
@[kb "serre1973" "Ch. IV, §2.1"]
theorem RatPlace.hasseSerre_isometric (v : RatPlace) (a b : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0)
    (h : RatPlace.atPlace (fun K _ _ => (diag a).IsometricIn K (diag b)) v) :
    v.hasseSerre a = v.hasseSerre b := by
  cases v with
  | infinite =>
    exact hasseSerre_infinite_eq_of_negCount a b ha hb (negCount_eq_of_isometric a b h)
  | finite p =>
    haveI : Fact p.1.Prime := ⟨p.2⟩
    rw [RatPlace.hasseSerre_finite, RatPlace.hasseSerre_finite]
    exact hasseInvariant_isometric p.1 a b ha hb h

/-- **The correction $(d,d)_v$ is an isometry invariant** (the square class of $d$ is). -/
theorem RatPlace.hilbert_disc_self_isometric (v : RatPlace) (a b : Fin n → ℚ)
    (h : RatPlace.atPlace (fun K _ _ => (diag a).IsometricIn K (diag b)) v) :
    v.hilbert (diagDet a) (diagDet a) = v.hilbert (diagDet b) (diagDet b) :=
  ((sameSq_of_isometric v a b h).hilbert_self).symm

/-- **The correction $(\delta,\delta)_v$ is an isometry invariant.** -/
theorem RatPlace.hilbert_signedDisc_self_isometric (v : RatPlace) (a b : Fin n → ℚ)
    (h : RatPlace.atPlace (fun K _ _ => (diag a).IsometricIn K (diag b)) v) :
    v.hilbert (diagSignedDisc a) (diagSignedDisc a) =
      v.hilbert (diagSignedDisc b) (diagSignedDisc b) :=
  (((sameSq_of_isometric v a b h).mul_left ((-1) ^ (n * (n - 1) / 2))).hilbert_self).symm

/-- **Isometry invariance of Cassels' $c_v$** (`hasseSerre_isometric`, as $c = \varepsilon$). -/
@[kb "cassels1978" "Ch. 4, Lemma 2.2, p. 57, and Cor. 1, p. 58"]
theorem RatPlace.hasseCassels_isometric (v : RatPlace) (a b : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0)
    (h : RatPlace.atPlace (fun K _ _ => (diag a).IsometricIn K (diag b)) v) :
    v.hasseCassels a = v.hasseCassels b :=
  RatPlace.hasseSerre_isometric v a b ha hb h

/-- **Isometry invariance of O'Meara's $S_v$**, from `hasseSerre_isometric` and
`hasseOMeara_eq` ($S = \varepsilon\,(d,d)$). -/
@[kb "omeara1963" "§63B, p. 167 (S_p V independent of the splitting)"]
theorem RatPlace.hasseOMeara_isometric (v : RatPlace) (a b : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0)
    (h : RatPlace.atPlace (fun K _ _ => (diag a).IsometricIn K (diag b)) v) :
    v.hasseOMeara a = v.hasseOMeara b := by
  rw [hasseOMeara_eq v a ha, hasseOMeara_eq v b hb, RatPlace.hasseSerre_isometric v a b ha hb h,
    RatPlace.hilbert_disc_self_isometric v a b h]

/-- **Isometry invariance of Lam's $s_v$.** -/
@[kb "lam2005" "Ch. V, §3 [unverified]"]
theorem RatPlace.hasseLam_isometric (v : RatPlace) (a b : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0)
    (h : RatPlace.atPlace (fun K _ _ => (diag a).IsometricIn K (diag b)) v) :
    v.hasseLam a = v.hasseLam b :=
  RatPlace.hasseSerre_isometric v a b ha hb h

/-- **Isometry invariance of Hasse's $\alpha_v$ (Shimura §28.13).** -/
@[kb "shimura2010" "§28.13, p. 160"]
theorem RatPlace.hasseShimura_isometric (v : RatPlace) (a b : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0)
    (h : RatPlace.atPlace (fun K _ _ => (diag a).IsometricIn K (diag b)) v) :
    v.hasseShimura a = v.hasseShimura b :=
  RatPlace.hasseOMeara_isometric v a b ha hb h

/-- **Isometry invariance of Conway–Sloane's $(f)_p$** (`hasseSerre_isometric`, as $(f)_p = \varepsilon$). -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373, eq. (17)"]
theorem RatPlace.hasseConwaySloane_isometric (v : RatPlace) (a b : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0)
    (h : RatPlace.atPlace (fun K _ _ => (diag a).IsometricIn K (diag b)) v) :
    v.hasseConwaySloane a = v.hasseConwaySloane b :=
  RatPlace.hasseSerre_isometric v a b ha hb h

end Invariance

/-! ### Product formulas over all places of $\mathbb{Q}$ -/

section Product

open RatPlace

theorem finprod_hilbert (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Function.HasFiniteMulSupport (fun v : RatPlace => v.hilbert x y) ∧
      ∏ᶠ v : RatPlace, v.hilbert x y = 1 := by
  obtain ⟨hF, hE⟩ := hilbert_product_formula x y hx hy
  have hms : Function.mulSupport (fun v : RatPlace => v.hilbert x y) =
      {v | v.hilbert x y = -1} := by
    ext v
    rcases hilbert_pm v x y with h | h <;> simp [Function.mem_mulSupport, h]
  refine ⟨by rw [Function.HasFiniteMulSupport, hms]; exact hF, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hF.toFinset) (by rw [hms]; simp)]
  rw [Finset.prod_congr rfl (fun v hv => (by simpa using hv : v.hilbert x y = -1))]
  rw [Finset.prod_const, neg_one_pow_eq_one_iff_even (by decide)]
  rwa [← Set.ncard_eq_toFinset_card _ hF]

theorem finprod_prod_hilbert {ι : Type*} (S : Finset ι) (x y : ι → ℚ) (hx : ∀ k, x k ≠ 0)
    (hy : ∀ k, y k ≠ 0) :
    Function.HasFiniteMulSupport (fun v : RatPlace => ∏ k ∈ S, v.hilbert (x k) (y k)) ∧
      ∏ᶠ v : RatPlace, ∏ k ∈ S, v.hilbert (x k) (y k) = 1 := by
  have hf : ∀ k ∈ S, Function.HasFiniteMulSupport (fun v : RatPlace => v.hilbert (x k) (y k)) :=
    fun k _ => (finprod_hilbert _ _ (hx k) (hy k)).1
  refine ⟨?_, ?_⟩
  · refine (S.finite_toSet.biUnion fun k hk => hf k hk).subset ?_
    simpa using mulSupport_prod S (fun (k : ι) (v : RatPlace) => v.hilbert (x k) (y k))
  · rw [finprod_prod_comm S (fun (v : RatPlace) (k : ι) => v.hilbert (x k) (y k)) hf]
    exact prod_eq_one fun k _ => (finprod_hilbert _ _ (hx k) (hy k)).2

theorem prod_pairs_eq (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)]
    (f : Fin n → Fin n → ℤ) :
    (∏ i, ∏ j, if P i j then f i j else 1) =
      ∏ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n => P p.1 p.2), f p.1 p.2 := by
  rw [prod_filter, prod_product]

theorem finprod_pairs (P : Fin n → Fin n → Prop) [∀ i j, Decidable (P i j)] (a : Fin n → ℚ)
    (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport
        (fun v : RatPlace => ∏ i, ∏ j, if P i j then v.hilbert (a i) (a j) else 1) ∧
      ∏ᶠ v : RatPlace, (∏ i, ∏ j, if P i j then v.hilbert (a i) (a j) else 1) = 1 := by
  simp only [prod_pairs_eq P (fun i j => _)]
  exact finprod_prod_hilbert _ (fun p : Fin n × Fin n => a p.1) (fun p => a p.2)
    (fun p => ha _) (fun p => ha _)

/-- **Product formula for Serre's $\varepsilon$:** for $a_i \in \mathbb{Q}^\times$,
$\varepsilon_v = 1$ for all but finitely many $v$ and $\prod_v \varepsilon_v(\langle a\rangle) = 1$
(Hilbert reciprocity applied to each pair). -/
@[kb "serre1973" "Ch. III, §2.1 + Ch. IV, §2.1 (derived)"]
theorem hasseSerre_product_formula (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : RatPlace => v.hasseSerre a) ∧
      ∏ᶠ v : RatPlace, v.hasseSerre a = 1 :=
  finprod_pairs (fun i j => i < j) a ha

/-- **Product formula for Cassels' $c$.** -/
@[kb "cassels1978" "Ch. 6, Lemma 1.1, p. 76 (from Ch. 3, Lemma 3.4, p. 46); c defined in Ch. 4, §1, p. 55"]
theorem hasseCassels_product_formula (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : RatPlace => v.hasseCassels a) ∧
      ∏ᶠ v : RatPlace, v.hasseCassels a = 1 :=
  finprod_pairs (fun i j => i < j) a ha

/-- **Product formula for O'Meara's $S$.** -/
@[kb "omeara1963" "§66, 66:6, p. 189; §72, 72:1 (3), p. 203"]
theorem hasseOMeara_product_formula (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : RatPlace => v.hasseOMeara a) ∧
      ∏ᶠ v : RatPlace, v.hasseOMeara a = 1 :=
  finprod_pairs (fun i j => i ≤ j) a ha

/-- **Product formula for Lam's $s$.** -/
@[kb "lam2005" "Ch. V, §3 [unverified]"]
theorem hasseLam_product_formula (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : RatPlace => v.hasseLam a) ∧
      ∏ᶠ v : RatPlace, v.hasseLam a = 1 :=
  finprod_pairs (fun i j => i < j) a ha

/-- **Product formula for Hasse's $\alpha_v$ (Shimura §28.13).** -/
@[kb "shimura2010" "§28.13, p. 160"]
theorem hasseShimura_product_formula (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : RatPlace => v.hasseShimura a) ∧
      ∏ᶠ v : RatPlace, v.hasseShimura a = 1 :=
  finprod_pairs (fun i j => i ≤ j) a ha

/-- **Product formula for Conway–Sloane's $(f)_p$** over all $p$, including $p = -1$ (their name for $\infty$).
Conway–Sloane replace it by their sum formula (15)/oddity formula (16) (`ConwaySloane.sum_excess_eq_zero`,
`ConwaySloane.oddity_formula`). -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373, eq. (17); §5.1, p. 371"]
theorem hasseConwaySloane_product_formula (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) :
    Function.HasFiniteMulSupport (fun v : RatPlace => v.hasseConwaySloane a) ∧
      ∏ᶠ v : RatPlace, v.hasseConwaySloane a = 1 :=
  finprod_pairs (fun i j => i < j) a ha

end Product

end QuadFormsKB
