import QuadFormsKB.Literature.Cassels.Ch9Examples5
import QuadFormsKB.Literature.Hanke2011Structure.LocalGenera
import QuadFormsKB.Tamagawa.RatBridge
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree
import QuadFormsKB.Literature.Cassels.Ch8.Ex5
import QuadFormsKB.Literature.Cassels.Ch9Examples6
import QuadFormsKB.Literature.Cassels.Ch9Sec6Four
import QuadFormsKB.Literature.Cassels.Ch9Sec6Three
import QuadFormsKB.Literature.LocalGlobal.PrescribedSymbols

/-!
# Cassels, Chapter 9: the Hasse–Minkowski invariant $c_p$ of integral forms (Ex. 7 (i), Ex. 10, Lemma 6.4)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 9, Examples 7 (i) and 10 (pp. 163–164) and the proof of
Lemma 6.4 (pp. 150–151).

**Layer.** Integral forms `f : QuadForm ℤ n` (variables $x_0, \dots, x_{n-1}$, 0-based; Cassels' $x_1, \dots, x_n$ are shifted),
classically integral (`IsClassicallyIntegral`) with Cassels' matrix $(f_{ij}) = H/2$ (`Siegel.casselsMat`) and
Cassels' determinant $d(f) = \det(f_{ij}) = \det H/2^n$. The invariant is Cassels' $c_v(\langle a_0, \dots, a_{n-1}\rangle) =
\prod_{i<j}(a_i, a_j)_v$ (`RatPlace.hasseCassels`, Ch. 4, §1). For a classically integral $f$, "$c_p(f)$" means $c_p$ of any
diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ with $f \cong_{\mathbb Q} \langle a\rangle$
(`(f.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag a)`); it does not depend on the choice
(`RatPlace.hasseCassels_isometric`). All theorems take such an `a` (with nonzero entries) and the isometry as hypotheses.

**Proves.**
* The key lemma `hasseCassels_eq_one_of_not_dvd_hessian_det` / `hasseCassels_eq_one_of_not_dvd_d`: $c_p(f) = +1$ for an odd
  prime $p \nmid d(f)$ (equivalently $p \nmid \det H$). Proof: over $\mathbb Z_p$ the form is diagonalizable with unit entries
  (Hanke 2011, Lemma 4.7), units are squares times integers prime to $p$, and Hilbert symbols of units at odd $p$ are $+1$.
* Ch. 9, Ex. 10 (i)–(v), p. 163–164: (i) `ex10_i` ($c_p = 1$, $p \ne 2$, $d(f) = 1$); (ii) `ex10_ii` ($c_\infty = 1$ for positive
  definite $f$); (iii) `ex10_iii` ($c_2 = 1$ for positive definite $f$ with $d(f) = 1$, by the product formula); (iv) `ex10_iv`
  (an improperly primitive $\mathbb Z_2$-form $g_2$ with $d(g_2) = 1$ and $c_2(g_2) = 1$ exists iff $8 \mid n$; from Ch. 8, Ex. 4 (iv));
  (v) `ex10_v` (for $8 \mid n$ there is a global form $f$ with $d(f) = 1$, $\mathbb Z_2$-equivalent to $g_2$, $\mathbb Z_p$-equivalent to
  $x_0^2 + \dots + x_{n-1}^2$ for odd $p$ and $\mathbb R$-equivalent to it). *(v) is proved differently from Cassels (who uses Theorem 1.2):
  by $f = 2E_8^{\perp m}$ and the classification of unimodular forms.*
* Ex. 7 (i), p. 163, last sentence: `ex7_i_least_det`: the least $\lvert d(f)\rvert$ is $3$ (lower bound from the key lemma:
  $c_3(f) = -1$ forces $3 \mid d(f)$; attained by $x^2 + 3y^2 - z^2$, `Siegel.ex7_i`).
* Lemma 6.4, proof, pp. 150–151: the local invariants (6.36)–(6.39) of the binary forms $g$ of the set (i)–(iii)
  (`threeSqGenusSet a`): `lemma64_c_infinite`, `lemma64_c_odd_dvd`, `lemma64_c_unit`, `lemma64_c_two`, and the consequence
  `threeSqGenusSet_eq_empty_of_seven` (no such $g$ for $a \equiv 7 \pmod 8$).

**Not formalized.** The last step of Lemma 6.4 ("(6.36)–(6.39) determine $g$ up to $\mathbb Z_p$-equivalence for every $p$, so
the set (i)–(iii) is a single genus"), which uses Theorem 1.2 and the $\mathbb Z_p$-classification; `Siegel.threeSqClassCount`
already counts the classes of the set (i)–(iii) directly.

**Reconstructed.** The displays (6.37) and (6.39) are garbled in the machine-read text; (6.37) $c_p(g) = (-1/p)$ for odd $p \mid a$
is reconstructed from the argument, and (6.39) $c_2(g) = \prod_{p \mid a,\ p \ne 2}(-1/p)$ from the product formula; both are proved
here. Condition $(*)$ of Ex. 7 is reconstructed in `Ex7Star` (see `Siegel.ex7_i`).
-/

open Matrix

namespace QuadFormsKB.Cassels.HasseInv

open QuadFormsKB QuadFormsKB.Siegel

variable {n : ℕ}

/-- Helper: the Hessian determinant of the base change $f \otimes R$ of an integral form $f$ along $\mathbb Z \to R$ is
the image of $\det H(f)$ (for any commutative ring $R$). -/
theorem hessian_det_map (R : Type*) [CommRing R] (f : QuadForm ℤ n) :
    ((f.map (Int.castRingHom R)).hessian).det = ((f.hessian.det : ℤ) : R) := by
  have h : (f.map (Int.castRingHom R)).hessian = f.hessian.map (Int.castRingHom R) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map, Matrix.map_apply]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simp

/-- Helper: an integer is divisible by $p$ in $\mathbb Z_p$ iff it is divisible by $p$ in $\mathbb Z$. -/
theorem padic_dvd_intCast_iff (p : ℕ) [Fact p.Prime] (m : ℤ) :
    (p : ℤ_[p]) ∣ (m : ℤ_[p]) ↔ (p : ℤ) ∣ m := by
  have := PadicInt.pow_p_dvd_int_iff (p := p) 1 m
  simpa using this

/-- Helper: the values over $K$ of the rationalization of an integral form agree with the values of its
$\mathbb Z_p$-base change evaluated over $K$. -/
theorem evalIn_rat_eq_padic (p : ℕ) [Fact p.Prime] (f : QuadForm ℤ n) (z : Fin n → ℚ_[p]) :
    (f.map (Int.castRingHom ℚ)).evalIn ℚ_[p] z =
      ((f.map (Int.castRingHom ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p])).eval z := by
  simp [QuadForm.evalIn, QuadForm.map, Matrix.map_apply]


/-- Helper: a unit of $\mathbb Z_p$ ($p$ odd) is, in $\mathbb Q_p$, a nonzero square times a natural number
prime to $p$ (the representative of its residue class in $\{0,\dots,p-1\}$). -/
theorem exists_nat_sq_class (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {u : ℤ_[p]} (hu : IsUnit u) :
    ∃ b : ℕ, ¬ p ∣ b ∧ ∃ s : ℚ_[p], s ≠ 0 ∧ ((u : ℤ_[p]) : ℚ_[p]) = (b : ℚ_[p]) * s ^ 2 := by
  have hu0 : PadicInt.toZMod u ≠ 0 := (hu.map PadicInt.toZMod).ne_zero
  set b : ℕ := (PadicInt.toZMod u).val with hb
  have hbz : ((b : ℕ) : ZMod p) = PadicInt.toZMod u := ZMod.natCast_zmod_val _
  have hpb : ¬ p ∣ b := by
    intro h
    exact hu0 (by rw [← hbz]; exact (ZMod.natCast_eq_zero_iff b p).2 h)
  have hpb' : ¬ (p : ℤ_[p]) ∣ ((b : ℤ) : ℤ_[p]) := by
    rw [padic_dvd_intCast_iff]; exact_mod_cast hpb
  have hw : IsUnit ((b : ℤ) : ℤ_[p]) :=
    LocalDensity.DVR.dvr_isUnit_of_not_dvd (PadicInt.irreducible_p) hpb'
  obtain ⟨wu, hwu⟩ := hw
  set v : ℤ_[p]ˣ := hu.unit * wu⁻¹ with hvdef
  have hv : (v : ℤ_[p]) * ((b : ℤ) : ℤ_[p]) = u := by
    rw [← hwu, hvdef, Units.val_mul]
    simp
  have htw : PadicInt.toZMod (((b : ℤ) : ℤ_[p])) = PadicInt.toZMod u := by
    simp [hbz]
  have hv1 : PadicInt.toZMod (v : ℤ_[p]) = 1 := by
    have h1 := congrArg PadicInt.toZMod hv
    rw [map_mul, htw] at h1
    exact mul_right_cancel₀ hu0 (by rw [h1, one_mul])
  have hsq : IsSquare (((v : ℤ_[p]) : ℚ_[p])) :=
    (HilbertLocal.isSquare_unit_iff (p := p) hp2 v).2 (by rw [hv1]; exact ⟨1, by simp⟩)
  obtain ⟨s, hs⟩ := hsq
  have hv0 : (((v : ℤ_[p]) : ℚ_[p])) ≠ 0 := by
    intro h
    exact v.ne_zero (PadicInt.coe_eq_zero.mp h)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hv0 (by rw [hs]; simp)
  refine ⟨b, hpb, s, hs0, ?_⟩
  have h2 := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hv
  simp only [PadicInt.coe_mul] at h2
  rw [← h2, hs]
  push_cast
  ring

/-- Helper: over $\mathbb Q_p$ ($p$ odd), an integral form whose Hessian determinant is prime to $p$ is isometric to
a diagonal form $\langle b_0,\dots,b_{n-1}\rangle$ whose entries are positive integers prime to $p$. -/
theorem exists_diag_nat_isometric (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (f : QuadForm ℤ n)
    (hdet : ¬ (p : ℤ) ∣ f.hessian.det) :
    ∃ b : Fin n → ℕ, (∀ i, ¬ p ∣ b i) ∧
      (f.map (Int.castRingHom ℚ)).IsometricIn ℚ_[p] (QuadForm.diag fun i => ((b i : ℕ) : ℚ)) := by
  classical
  let _ : Fintype (IsLocalRing.ResidueField ℤ_[p]) := Fintype.ofFinite _
  set Q := f.map (Int.castRingHom ℤ_[p]) with hQdef
  have hQ : ¬ (p : ℤ_[p]) ∣ Q.hessian.det := by
    rw [hessian_det_map, padic_dvd_intCast_iff]; exact hdet
  obtain ⟨u, hu, hiso, -⟩ := Hanke2011Structure.lemma_4_7_diag (π := (p : ℤ_[p]))
    PadicInt.irreducible_p (Siegel.Kneser.not_p_dvd_two hp2) ℚ_[p] Q hQ
  -- natural-number representatives of the unit entries
  have hcls := fun i => exists_nat_sq_class p hp2 (hu i)
  choose b hb s hs0 hs using hcls
  refine ⟨b, hb, ?_⟩
  -- the isometry over `ℚ_[p]`
  obtain ⟨g, hg⟩ := Tamagawa.RatBridge.isometricGL_map_hom (algebraMap ℤ_[p] ℚ_[p]) hiso
  have hdm : ((QuadForm.diag u).map (algebraMap ℤ_[p] ℚ_[p])) =
      QuadForm.diag fun i => ((u i : ℤ_[p]) : ℚ_[p]) := by
    ext i j
    simp [QuadForm.map, QuadForm.diag, Matrix.diagonal_apply]
    split_ifs <;> simp
  refine ⟨g.val * Matrix.diagonal fun i => (s i)⁻¹, ?_, fun x => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    exact (Matrix.isUnit_iff_isUnit_det _ |>.mp g.isUnit).mul
      (isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (hs0 i)))
  · rw [evalIn_rat_eq_padic, ← Matrix.mulVec_mulVec, hg, hdm, Siegel.Kneser.eval_diag,
      QuadForm.evalIn_diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec_diagonal, Algebra.algebraMap_eq_smul_one]
    rw [hs i]
    rw [Rat.smul_one_eq_cast]
    push_cast
    have := hs0 i
    field_simp

/-- Helper: the natural-number cast of an integer prime to $p$ is a $p$-adic unit, so its Hilbert symbol with another
such number at an odd prime is $+1$ (the product defining $c_p$ is empty of $-1$'s). -/
theorem hasseCassels_nat_unit (p : Nat.Primes) (hp2 : p.1 ≠ 2) (b : Fin n → ℕ) (hb : ∀ i, ¬ p.1 ∣ b i) :
    (RatPlace.finite p).hasseCassels (fun i => ((b i : ℕ) : ℚ)) = 1 := by
  have : Fact p.1.Prime := ⟨p.2⟩
  have hb0 : ∀ i, ((b i : ℕ) : ℚ) ≠ 0 := fun i h => by
    have : b i = 0 := by exact_mod_cast h
    exact hb i (this ▸ dvd_zero _)
  have hv : ∀ i, padicValRat p.1 ((b i : ℕ) : ℚ) = 0 := fun i => by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (hb i)]; rfl
  unfold RatPlace.hasseCassels
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs
  · exact HilbertLocal.hilbert_eq_one_of_padicValRat hp2 _ _ (hb0 i) (hb0 j) (hv i) (hv j)
  · rfl

/-- **Key lemma: $c_p(f) = +1$ at an odd prime not dividing $\det H$** (Cassels, Ch. 9, Ex. 10 (i), p. 163, and its use in
Ex. 7).

Let $f$ be an integral quadratic form in $n$ variables (`f : QuadForm ℤ n`) with Hessian matrix $H$ (so
$H = C + C^{\mathsf T}$ for the coefficient matrix $C$; for classically integral $f$ this is $2(f_{ij})$), let $p$ be an
odd prime with $p \nmid \det H$, and let $\langle a_0,\dots,a_{n-1}\rangle$ (`a`, all entries nonzero rationals) be a
diagonal form that is $\mathbb Q$-equivalent to $f$ (`hiso`). Then Cassels' invariant
$c_p = \prod_{i<j}(a_i,a_j)_p$ of the diagonal form is $+1$.

*Proof.* Over $\mathbb Z_p$ the form is equivalent to a diagonal form with unit entries $u_i$ (Hanke 2011, Lemma 4.7;
`Hanke2011Structure.lemma_4_7_diag`); each $u_i$ is a $p$-adic square times a natural number $b_i$ prime to $p$; the
invariant is unchanged under $\mathbb Q_p$-equivalence (`RatPlace.hasseCassels_isometric`), and
$(b_i,b_j)_p = 1$ for $p$-adic units at odd $p$. -/
@[kb "cassels1978" "Ch. 9, Ex. 10 (i), p. 163 (c_p(f) = 1 for p ≠ 2 and integral f with d(f) = 1; generalization: p ∤ 2d(f), stated with det H)"]
theorem hasseCassels_eq_one_of_not_dvd_hessian_det (p : Nat.Primes) (hp2 : p.1 ≠ 2) (f : QuadForm ℤ n)
    (hdet : ¬ (p.1 : ℤ) ∣ f.hessian.det) (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hiso : (f.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag a)) :
    (RatPlace.finite p).hasseCassels a = 1 := by
  have : Fact p.1.Prime := ⟨p.2⟩
  obtain ⟨b, hb, hbiso⟩ := exists_diag_nat_isometric p.1 hp2 f hdet
  have hb0 : ∀ i, ((b i : ℕ) : ℚ) ≠ 0 := fun i h => by
    have : b i = 0 := by exact_mod_cast h
    exact hb i (this ▸ dvd_zero _)
  have hrat := HM3.isometricIn_of_rat ℚ_[p.1] hiso
  have hab : (QuadForm.diag a).IsometricIn ℚ_[p.1] (QuadForm.diag fun i => ((b i : ℕ) : ℚ)) :=
    QuadForm.isometricIn_trans _ (QuadForm.isometricIn_symm _ hrat) hbiso
  rw [RatPlace.hasseCassels_isometric (RatPlace.finite p) a _ ha hb0 hab]
  exact hasseCassels_nat_unit p hp2 b hb

/-- Helper: for a classically integral form, $\det H = 2^n\,d(f)$ where $d(f) = \det(f_{ij})$ is Cassels' determinant
(`casselsMat`, the matrix $H/2$) and $n$ is the number of variables. -/
theorem hessian_det_eq_of_ci (f : QuadForm ℤ n) (hf : IsClassicallyIntegral f) :
    f.hessian.det = 2 ^ n * (casselsMat f).det := by
  rw [hessian_eq_two_smul_casselsMat hf, Matrix.det_smul]
  simp

/-- Helper: an odd prime $p$ not dividing Cassels' determinant $d(f)$ of a classically integral form does not divide
$\det H$ either (as $\det H = 2^n d(f)$). -/
theorem not_dvd_hessian_det_of_not_dvd_d (p : Nat.Primes) (hp2 : p.1 ≠ 2) (f : QuadForm ℤ n)
    (hf : IsClassicallyIntegral f) (hd : ¬ (p.1 : ℤ) ∣ (casselsMat f).det) :
    ¬ (p.1 : ℤ) ∣ f.hessian.det := by
  intro h
  rw [hessian_det_eq_of_ci f hf] at h
  have hpp : Prime (p.1 : ℤ) := Nat.prime_iff_prime_int.mp p.2
  rcases hpp.dvd_or_dvd h with h2 | h2
  · have h3 : (p.1 : ℤ) ∣ 2 := hpp.dvd_of_dvd_pow h2
    have h4 : p.1 ∣ 2 := by exact_mod_cast h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).1 h4)
  · exact hd h2

/-- **Key lemma in Cassels' normalization: $c_p(f) = +1$ at every odd prime $p \nmid d(f)$** (Ch. 9, Ex. 10 (i), p. 163,
generalized from $d(f) = 1$; the same fact is used in Ex. 7).

Let $f$ be a classically integral form in $n$ variables (`f`, `hf`) with Cassels' determinant
$d(f) = \det(f_{ij}) = \det H/2^n$ (`casselsMat`), let $p$ be an odd prime with $p \nmid d(f)$ (`hd`), and let
$\langle a_0,\dots,a_{n-1}\rangle$ (`a`, nonzero entries `ha`) be a diagonal form $\mathbb Q$-equivalent to $f$ (`hiso`);
$c_p(f)$ means $c_p$ of this diagonal form (it does not depend on the choice, `RatPlace.hasseCassels_isometric`). Then
$c_p(f) = +1$. -/
@[kb "cassels1978" "Ch. 9, Ex. 10 (i), p. 163 (c_p(f) = 1 for p ≠ 2 and integral f with d(f) = 1; generalization: p ∤ 2d(f))"]
theorem hasseCassels_eq_one_of_not_dvd_d (p : Nat.Primes) (hp2 : p.1 ≠ 2) (f : QuadForm ℤ n)
    (hf : IsClassicallyIntegral f) (hd : ¬ (p.1 : ℤ) ∣ (casselsMat f).det) (a : Fin n → ℚ)
    (ha : ∀ i, a i ≠ 0) (hiso : (f.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag a)) :
    (RatPlace.finite p).hasseCassels a = 1 :=
  hasseCassels_eq_one_of_not_dvd_hessian_det p hp2 f (not_dvd_hessian_det_of_not_dvd_d p hp2 f hf hd) a ha hiso

/-- **Cassels, Ch. 9, Ex. 10 (i)** (p. 163): *$c_p(f) = 1$ for $p \ne 2$ and all integral forms $f$ with $d(f) = 1$.*
Here $f$ is classically integral with Cassels' determinant $d(f) = \det(f_{ij}) = 1$ (`hd`), $p$ is an odd prime, and
$\langle a_0,\dots,a_{n-1}\rangle$ is a diagonal form $\mathbb Q$-equivalent to $f$ (`a`, `ha`, `hiso`); then
$c_p = +1$. -/
@[kb "cassels1978" "Ch. 9, Ex. 10 (i), p. 163"]
theorem ex10_i (p : Nat.Primes) (hp2 : p.1 ≠ 2) (f : QuadForm ℤ n) (hf : IsClassicallyIntegral f)
    (hd : (casselsMat f).det = 1) (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hiso : (f.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag a)) :
    (RatPlace.finite p).hasseCassels a = 1 :=
  hasseCassels_eq_one_of_not_dvd_d p hp2 f hf (by rw [hd]; exact_mod_cast p.2.not_dvd_one) a ha hiso

/-- Helper: the value of the diagonal form $\langle a_0,\dots,a_{n-1}\rangle$ over $\mathbb R$ at the $i$-th standard
basis vector is $a_i$. -/
theorem evalIn_diag_single (a : Fin n → ℚ) (i : Fin n) :
    (QuadForm.diag a).evalIn ℝ (Pi.single i 1) = (a i : ℝ) := by
  rw [QuadForm.evalIn_diag, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- Helper: a form that is $\mathbb R$-equivalent to a diagonal form $\langle a\rangle$ and positive definite has all
diagonal entries $a_i > 0$ (the value at the image of the $i$-th basis vector). -/
theorem pos_of_posDef_isometric (f : QuadForm ℤ n) (hp : IntQF.PosDef f) (a : Fin n → ℚ)
    (hiso : (f.map (Int.castRingHom ℚ)).IsometricIn ℝ (QuadForm.diag a)) (i : Fin n) : 0 < a i := by
  obtain ⟨P, hP, hx⟩ := hiso
  have hne : P *ᵥ (Pi.single i 1 : Fin n → ℝ) ≠ 0 := fun h => by
    have h1 := congrArg (fun z => P⁻¹ *ᵥ z) h
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h1
    have := congrFun h1 i
    simp at this
  have h1 := hp.evalIn_real_pos _ hne
  have h2 := hx (Pi.single i 1)
  rw [evalIn_diag_single] at h2
  have h3 : (f.map (Int.castRingHom ℚ)).evalIn ℝ (P *ᵥ (Pi.single i 1 : Fin n → ℝ)) =
      f.evalIn ℝ (P *ᵥ (Pi.single i 1 : Fin n → ℝ)) := by
    simp [QuadForm.evalIn, QuadForm.map, Matrix.map_apply]
  rw [h3] at h2
  have : (0 : ℝ) < (a i : ℝ) := h2 ▸ h1
  exact_mod_cast this

/-- **Cassels, Ch. 9, Ex. 10 (ii)** (p. 163): *$c_\infty(f) = 1$ for all positive definite forms $f$.* Let $f$ be a
positive definite integral form (`hp`; `IntQF.PosDef`) and $\langle a_0,\dots,a_{n-1}\rangle$ (`a`, `ha`) a diagonal form
that is $\mathbb R$-equivalent to $f$ (`hiso`; implied by $\mathbb Q$-equivalence). Then all $a_i > 0$ and
$c_\infty = \prod_{i<j}(a_i,a_j)_\infty = +1$. -/
@[kb "cassels1978" "Ch. 9, Ex. 10 (ii), p. 163"]
theorem ex10_ii (f : QuadForm ℤ n) (hp : IntQF.PosDef f) (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hiso : (f.map (Int.castRingHom ℚ)).IsometricIn ℝ (QuadForm.diag a)) :
    RatPlace.infinite.hasseCassels a = 1 := by
  have hpos := pos_of_posDef_isometric f hp a hiso
  unfold RatPlace.hasseCassels
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs
  · have hr : ∀ i, ((a i : ℚ) : ℝ) ≠ 0 := fun i => by exact_mod_cast ha i
    simp only [RatPlace.hilbert]
    rw [HasseIsoNF.hilbertSymbol_real_eq _ _ (hr i) (hr j)]
    have : ¬ ((a i : ℝ) < 0 ∧ (a j : ℝ) < 0) := fun h => by
      have := hpos i
      have : (0 : ℝ) < (a i : ℝ) := by exact_mod_cast this
      linarith [h.1]
    simp only [this, ↓reduceIte]
  · rfl

/-- **Cassels, Ch. 9, Ex. 10 (iii)** (p. 163–164): *hence $c_2(f) = 1$ for all positive definite integral forms $f$ with
$d(f) = 1$.* Here $f$ is classically integral and positive definite with Cassels' determinant $d(f) = 1$, and
$\langle a_0,\dots,a_{n-1}\rangle$ (`a`, `ha`) is a diagonal form $\mathbb Q$-equivalent to $f$ (`hiso`). By (i) and (ii)
all local invariants $c_v$ with $v \ne 2$ equal $+1$, so $c_2 = +1$ by the product formula
`hasseCassels_product_formula`. -/
@[kb "cassels1978" "Ch. 9, Ex. 10 (iii), p. 164"]
theorem ex10_iii (f : QuadForm ℤ n) (hf : IsClassicallyIntegral f) (hp : IntQF.PosDef f)
    (hd : (casselsMat f).det = 1) (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0)
    (hiso : (f.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag a)) :
    (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseCassels a = 1 := by
  classical
  have hinf : RatPlace.infinite.hasseCassels a = 1 :=
    ex10_ii f hp a ha (HM3.isometricIn_of_rat ℝ hiso)
  obtain ⟨-, hprod⟩ := hasseCassels_product_formula a ha
  have hsupp : Function.mulSupport (fun v : RatPlace => v.hasseCassels a) ⊆
      ({RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩} : Finset RatPlace) := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases v with _ | p
    · exact Or.inl rfl
    · by_cases hp2 : p.1 = 2
      · exact Or.inr (by congr 1; exact Subtype.ext hp2)
      · exact absurd (ex10_i p hp2 f hf hd a ha hiso) hv
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, Finset.prod_insert (by simp),
    Finset.prod_singleton, hinf, one_mul] at hprod
  exact hprod

/-! ### Example 10 (iv): the dyadic condition $8 \mid n$ -/

/-- Helper: for a symmetric matrix over $\mathbb Z_2$ with even diagonal, $\vec x^{\mathsf T}F\vec x$ is even for every
$\vec x$ (the off-diagonal terms pair up). -/
theorem two_dvd_quad_of_even_diag (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F)
    (hd : ∀ i, (2 : ℤ_[2]) ∣ F i i) (x : Fin n → ℤ_[2]) : (2 : ℤ_[2]) ∣ x ⬝ᵥ (F *ᵥ x) := by
  classical
  set h : Fin n → Fin n → ℤ_[2] := fun i j => x i * F i j * x j with hh
  have hsymm : ∀ i j, h i j = h j i := by
    intro i j
    have : F j i = F i j := by simpa using congrFun (congrFun hF i) j
    simp only [hh, this]; ring
  have hS : x ⬝ᵥ (F *ᵥ x) = ∑ i, ∑ j, h i j := by
    simp only [dotProduct, Matrix.mulVec, hh, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsplit : ∀ i, ∑ j, h i j =
      h i i + ∑ j, (if i < j then h i j else 0) + ∑ j, (if j < i then h i j else 0) := by
    intro i
    have : ∀ j, h i j = (if j = i then h i i else 0) + (if i < j then h i j else 0) +
        (if j < i then h i j else 0) := by
      intro j
      rcases lt_trichotomy i j with hij | rfl | hij
      · simp [hij, hij.ne', not_lt.mpr hij.le]
      · simp
      · simp [hij, hij.ne, not_lt.mpr hij.le]
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp
  have hcomm : ∑ i, ∑ j, (if j < i then h i j else 0) = ∑ i, ∑ j, (if i < j then h i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i < j
    · simp [hij, hsymm i j]
    · simp [hij]
  rw [hS, Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_add_distrib, hcomm]
  rw [show ∀ A T : ℤ_[2], A + T + T = A + 2 * T from fun A T => by ring]
  refine dvd_add (Finset.dvd_sum fun i _ => ?_) (dvd_mul_right 2 _)
  simp only [hh]
  exact ((hd i).mul_left _).mul_right _

/-- Helper: divisibility by $8$ of an integer in $\mathbb Z_2$ is divisibility by $8$ in $\mathbb Z$. -/
theorem eight_dvd_int (k : ℤ) : (8 : ℤ_[2]) ∣ (k : ℤ_[2]) ↔ (8 : ℤ) ∣ k := by
  have := PadicInt.pow_p_dvd_int_iff (p := 2) 3 k
  norm_num at this
  exact this

/-- Helper: for a symmetric Gram matrix $F$ over $\mathbb Z_2$ with $\det F = 1$ and even diagonal, every diagonalization
$\langle a\rangle$ of $F$ over $\mathbb Q_2$ has $c_2 = (-1)^s$ with $8 \mid n + 4s$ in $\mathbb Z_2$ (Ch. 8, Ex. 4 (iv) with the
characteristic vector $0$, and invariance of $c_2$ under $\mathbb Q_2$-equivalence). -/
theorem dyadic_hasse_of_even_diag (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (hdet : F.det = 1)
    (hd : ∀ i, (2 : ℤ_[2]) ∣ F i i) (a : Fin n → ℚ_[2]) (ha : Ex5.QDiag (F.map PadicInt.Coe.ringHom) a) :
    ∃ s : ℕ, (8 : ℤ_[2]) ∣ ((n : ℤ_[2]) + 4 * s) ∧ PadicClass.hasseVec a = (-1) ^ s := by
  have hchar : ∀ x, (2 : ℤ_[2]) ∣ x ⬝ᵥ (F *ᵥ x) - x ⬝ᵥ (F *ᵥ (0 : Fin n → ℤ_[2])) := by
    intro x; simpa using two_dvd_quad_of_even_diag F hF hd x
  obtain ⟨a', ha', s, hs, hh'⟩ := Ex5.ex4_iv.exists_diag n F hF (by rw [hdet]; exact isUnit_one) 0 hchar
  refine ⟨s, ?_, ?_⟩
  · have h2 : (8 : ℤ_[2]) ∣ -((n : ℤ_[2]) + 4 * s) := by
      convert hs using 1
      simp [hdet]; ring
    exact (dvd_neg).1 h2
  · rw [← hh']
    exact ((Ex5.qequiv_iff_invariants ha ha').1 (Ex5.QEquiv.refl _)).2

/-- Helper: the Gram matrix $(E_8^{\perp m})$-Hessian, viewed over $\mathbb Z_2$, is symmetric with determinant $1$ and even
diagonal (the matrix of the improperly primitive form $2E_8^{\perp m}$ in Cassels' normalization). -/
theorem e8_gram_props (m : ℕ) :
    ((Siegel.e8Sum m).hessian.map (Int.castRingHom ℤ_[2]))ᵀ = (Siegel.e8Sum m).hessian.map (Int.castRingHom ℤ_[2]) ∧
    ((Siegel.e8Sum m).hessian.map (Int.castRingHom ℤ_[2])).det = 1 ∧
    ∀ i, (2 : ℤ_[2]) ∣ ((Siegel.e8Sum m).hessian.map (Int.castRingHom ℤ_[2])) i i := by
  refine ⟨?_, ?_, fun i => ?_⟩
  · ext i j
    simp [QuadForm.hessian, add_comm]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Siegel.e8Sum_det]
    simp
  · refine ⟨((Siegel.e8Sum m).coeff i i : ℤ_[2]), ?_⟩
    simp [QuadForm.hessian]
    ring

/-- Helper: every classically integral $\mathbb Z_2$-form with unit determinant has a diagonalization over $\mathbb Q_2$
(Ch. 8, Ex. 4 (iv), `Ex5.ex4_iv`, applied with a characteristic vector from Ex. 4 (i)). -/
theorem exists_qdiag (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (hdet : F.det = 1) :
    ∃ a : Fin n → ℚ_[2], Ex5.QDiag (F.map PadicInt.Coe.ringHom) a := by
  have hu : IsUnit F.det := by rw [hdet]; exact isUnit_one
  obtain ⟨b, hb⟩ := ex4_exists_char F hF hu
  obtain ⟨a, ha, -⟩ := Ex5.ex4_iv.exists_diag n F hF hu b hb
  exact ⟨a, ha⟩

/-- **Cassels, Ch. 9, Ex. 10 (iv)** (p. 164): *a necessary and sufficient condition for the existence of an improperly
primitive integral $\mathbb Z_2$-form $g_2$ with $c_2(g_2) = 1$ and $d(g_2) = 1$ is that $8 \mid n$* (Cassels' reference:
Ch. 8, Ex. 4).

Here $g_2$ is given by its symmetric Gram matrix `F` over $\mathbb Z_2$ ($g_2(\vec x) = \vec x^{\mathsf T}F\vec x$, Cassels'
classically integral normalization), *improperly primitive* means that every diagonal entry $F_{ii}$ is even (for unit
determinant, primitivity is automatic), and $d(g_2) = \det F = 1$. The invariant $c_2(g_2)$ is
`PadicClass.hasseVec` $= \prod_{i<j}(a_i,a_j)_2$ of any diagonal form $\langle a_0,\dots,a_{n-1}\rangle$ that is
$\mathbb Q_2$-equivalent to $g_2$ (`Ex5.QDiag`); it does not depend on the diagonal form
(`Ex5.qequiv_iff_invariants`), and the statement uses "some diagonalization with invariant $+1$".
The proof applies Ch. 8, Ex. 4 (iv) (`Ex5.ex4_iv`) with the characteristic vector $\vec b = 0$ (available as all $F_{ii}$
are even), which gives $c_2 = (-1)^s$ with $4s \equiv -n \pmod 8$; so $c_2 = 1$ iff $s$ is even iff $8 \mid n$.
For the converse $F$ is the Gram matrix of $E_8^{\perp m}$ ($\det = 1$, even diagonal). The case $n = 0$ is included
(the empty form). -/
@[kb "cassels1978" "Ch. 9, Ex. 10 (iv), p. 164"]
theorem ex10_iv (n : ℕ) :
    (∃ F : Matrix (Fin n) (Fin n) ℤ_[2], Fᵀ = F ∧ F.det = 1 ∧ (∀ i, (2 : ℤ_[2]) ∣ F i i) ∧
      ∃ a : Fin n → ℚ_[2], Ex5.QDiag (F.map PadicInt.Coe.ringHom) a ∧ PadicClass.hasseVec a = 1) ↔
    8 ∣ n := by
  constructor
  · rintro ⟨F, hF, hdet, hd, a, ha, hh⟩
    obtain ⟨s, hs8, hhs⟩ := dyadic_hasse_of_even_diag F hF hdet hd a ha
    rw [hh] at hhs
    have hs : Even s := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      rw [hodd.neg_one_pow] at hhs
      omega
    obtain ⟨t, rfl⟩ := hs
    have h8 : (8 : ℤ_[2]) ∣ ((n + 4 * (t + t) : ℤ) : ℤ_[2]) := by
      rw [show ((n + 4 * (t + t) : ℤ) : ℤ_[2]) = (n : ℤ_[2]) + 4 * ((t + t : ℕ) : ℤ_[2]) by push_cast; ring]
      exact hs8
    rw [eight_dvd_int] at h8
    omega
  · intro h
    obtain ⟨m, rfl⟩ := h
    obtain ⟨hF, hdet, hd⟩ := e8_gram_props m
    set F : Matrix (Fin (8 * m)) (Fin (8 * m)) ℤ_[2] :=
      (Siegel.e8Sum m).hessian.map (Int.castRingHom ℤ_[2]) with hFdef
    obtain ⟨a, ha⟩ := exists_qdiag F hF hdet
    refine ⟨F, hF, hdet, hd, a, ha, ?_⟩
    obtain ⟨s, hs8, hhs⟩ := dyadic_hasse_of_even_diag F hF hdet hd a ha
    rw [hhs]
    have h8 : (8 : ℤ_[2]) ∣ (((8 * m : ℕ) + 4 * s : ℤ) : ℤ_[2]) := by
      rw [show (((8 * m : ℕ) + 4 * s : ℤ) : ℤ_[2]) = ((8 * m : ℕ) : ℤ_[2]) + 4 * (s : ℤ_[2]) by push_cast; ring]
      exact hs8
    rw [eight_dvd_int] at h8
    have : Even s := by
      rw [Nat.even_iff]; omega
    exact this.neg_one_pow

/-! ### Example 10 (v): the global form -/

/-- Helper: the Hessian of the base change of an integral form along $\mathbb Z \to R$ is the base change of the Hessian. -/
theorem hessian_map_int (R : Type*) [CommRing R] (f : QuadForm ℤ n) :
    (f.map (Int.castRingHom R)).hessian = f.hessian.map (Int.castRingHom R) := by
  ext i j; simp [QuadForm.hessian, QuadForm.map, Matrix.map_apply]

/-- Helper: $\mathrm{GL}_n(R)$-equivalence of the base changes of two classically integral forms (over a domain $R$ of
characteristic $0$) is equivalence of Cassels' matrices: $T^{\mathsf T}(f_{ij})T = (g_{ij})$. -/
theorem exists_gram_equiv_of_isometricGL {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (f g : QuadForm ℤ n) (hf : IsClassicallyIntegral f) (hg : IsClassicallyIntegral g)
    (h : IsometricGL (f.map (Int.castRingHom R)) (g.map (Int.castRingHom R))) :
    ∃ T : GL (Fin n) R, (T.val)ᵀ * (casselsMat f).map (Int.castRingHom R) * T.val =
      (casselsMat g).map (Int.castRingHom R) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  have hH := Lattices.Nbr.hessian_eq_of_eval' (Q := f.map (Int.castRingHom R)) (Q' := g.map (Int.castRingHom R))
    (U := T.val) (fun x => (hT x).symm)
  have e : ∀ C : Matrix (Fin n) (Fin n) ℤ, ((2 : ℤ) • C).map (Int.castRingHom R) =
      (2 : R) • C.map (Int.castRingHom R) := by
    intro C; ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat]
  rw [hessian_map_int, hessian_map_int, hessian_eq_two_smul_casselsMat hf, hessian_eq_two_smul_casselsMat hg,
    e, e, Matrix.mul_smul, Matrix.smul_mul] at hH
  exact (smul_right_injective _ (two_ne_zero : (2 : R) ≠ 0) hH).symm

/-- Helper: a block list all of whose blocks are $2xy$ (`hyp 0`) has dimension twice its length. -/
theorem dyDim_of_all_hyp (D : List DyBlock) (h : ∀ b ∈ D, b = DyBlock.hyp 0) : dyDim D = 2 * D.length := by
  induction D with
  | nil => rfl
  | cons b D ih =>
    have hb := h b (List.mem_cons_self ..)
    subst hb
    have := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp [dyDim, DyBlock.dim, this]
    ring

/-- Helper: two lists of blocks $2xy$ with the same dimension are equal. -/
theorem list_eq_of_all_hyp (D D' : List DyBlock) (h : ∀ b ∈ D, b = DyBlock.hyp 0)
    (h' : ∀ b ∈ D', b = DyBlock.hyp 0) (hd : dyDim D = dyDim D') : D = D' := by
  have l1 := dyDim_of_all_hyp D h
  have l2 := dyDim_of_all_hyp D' h'
  have hl : D.length = D'.length := by omega
  rw [List.eq_replicate_iff.2 ⟨rfl, h⟩, List.eq_replicate_iff.2 ⟨rfl, h'⟩, hl]

/-- Helper: a symmetric matrix over $\mathbb Z_2$ with determinant $1$, even diagonal and $n \ge 1$ rows has a unit entry. -/
theorem exists_unit_entry (hn : 0 < n) (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hdet : F.det = 1) :
    ∃ i j, IsUnit (F i j) := by
  by_contra hcon
  push Not at hcon
  have h0 : F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) = 0 := by
    ext i j
    have h := hcon i j
    have : F i j ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h
    simpa using this
  have hd := congrArg (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) hdet
  rw [map_one, RingHom.map_det] at hd
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [RingHom.mapMatrix_apply, h0, Matrix.det_zero] at hd
  exact zero_ne_one hd

/-- Helper: a symmetric matrix over $\mathbb Z_2$ with determinant $1$, even diagonal and $n \ge 1$ rows is
$\mathbb Z_2$-equivalent (as a form over $\mathbb Q_2$, `ZpEquiv`) to the orthogonal sum of $n/2$ copies of $2xy$:
Ch. 8, Ex. 3 (ii) (`ex3_square`) applied to the improperly primitive form with unit square determinant. -/
theorem exists_hyp_equiv (hn : 0 < n) (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (hdet : F.det = 1)
    (hd : ∀ i, (2 : ℤ_[2]) ∣ F i i) :
    ∃ D : List DyBlock, (∀ b ∈ D, b = DyBlock.hyp 0) ∧ ∃ h : dyDim D = n,
      ZpEquiv (F.map PadicInt.Coe.ringHom) ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) := by
  have h2 : ¬ IsUnit (2 : ℤ_[2]) := by
    intro hu
    have := PadicInt.isUnit_iff.1 hu
    have h' : ‖(2 : ℤ_[2])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd 2).2 (by exact_mod_cast dvd_refl _)
    linarith
  have hprim : IsPrimitiveForm (F.map PadicInt.Coe.ringHom) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [Matrix.map_apply]
      have := PadicInt.norm_le_one (F i j)
      simpa [PadicInt.norm_coe] using this
    · obtain ⟨i, j, hij⟩ := exists_unit_entry hn F hdet
      exact ⟨i, j, by simpa [Matrix.map_apply, PadicInt.norm_coe] using PadicInt.isUnit_iff.1 hij⟩
  have himp : IsImproperlyPrimitive (F.map PadicInt.Coe.ringHom) := by
    refine ⟨hprim, ?_⟩
    rintro ⟨-, j, hj⟩
    have hu : IsUnit (F j j) := PadicInt.isUnit_iff.2 (by simpa [Matrix.map_apply, PadicInt.norm_coe] using hj)
    exact h2 (isUnit_of_dvd_unit (hd j) hu)
  have hdetn : ‖(F.map PadicInt.Coe.ringHom).det‖ = 1 := by
    have : (F.map PadicInt.Coe.ringHom).det = ((F.det : ℤ_[2]) : ℚ_[2]) := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [this, hdet]; simp
  have hsq : IsSquare (F.map PadicInt.Coe.ringHom).det := by
    have : (F.map PadicInt.Coe.ringHom).det = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]; simp
    rw [this]; exact ⟨1, by simp⟩
  have hFt : (F.map PadicInt.Coe.ringHom)ᵀ = F.map PadicInt.Coe.ringHom := by
    rw [← Matrix.transpose_map, hF]
  exact (ex3_square hFt himp hdetn hsq).2

/-- Helper: the sum of squares $x_0^2 + \dots + x_{n-1}^2$ (`QuadForm.diag 1`) is classically integral, positive definite, and
has Cassels' matrix the identity. -/
theorem sumSq_props (n : ℕ) :
    IsClassicallyIntegral (QuadForm.diag (1 : Fin n → ℤ)) ∧ casselsMat (QuadForm.diag (1 : Fin n → ℤ)) = 1 ∧
      IntQF.PosDef (QuadForm.diag (1 : Fin n → ℤ)) := by
  have hhess : (QuadForm.diag (1 : Fin n → ℤ)).hessian = (2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [QuadForm.hessian, QuadForm.diag]
    · simp [QuadForm.hessian, QuadForm.diag, hij]
  have hci : IsClassicallyIntegral (QuadForm.diag (1 : Fin n → ℤ)) :=
    ci_of_two_dvd_hessian fun i j => by rw [hhess]; exact ⟨(1 : Matrix (Fin n) (Fin n) ℤ) i j, by simp⟩
  refine ⟨hci, ?_, ?_⟩
  · ext i j
    simp only [casselsMat, hhess, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  · intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h; push Not at h; exact hx (funext h)
    rw [Kneser.eval_diag]
    exact Finset.sum_pos' (fun j _ => by simp; positivity) ⟨i, Finset.mem_univ _, by simp; positivity⟩

/-- Helper: an odd prime does not divide a power of $2$. -/
theorem not_dvd_two_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) : ¬ (p : ℤ) ∣ 2 ^ k := by
  intro h
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h3 : (p : ℤ) ∣ 2 := hpp.dvd_of_dvd_pow h
  have h4 : p ∣ 2 := by exact_mod_cast h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)

/-- **Cassels, Ch. 9, Ex. 10 (v)** (p. 164): *if $8 \mid n$, there is a global form $f$ with $d(f) = 1$ which is
$\mathbb Z_2$-equivalent to $g_2$ and $\mathbb Z_p$-equivalent to $x_0^2 + \dots + x_{n-1}^2$ for every $p \ne 2$,
including $p = \infty$.* Cassels obtains $f$ from Theorem 1.2.

Here $g_2$ is given by a symmetric Gram matrix `F` over $\mathbb Z_2$ with $\det F = 1$ and even diagonal (an improperly
primitive $\mathbb Z_2$-form with $d(g_2) = 1$, as in (iv); the hypothesis $c_2(g_2) = 1$ of (iv) is not needed in this proof and
follows from $8 \mid n$ by `ex10_iv`), and $n \ge 1$ (Cassels' $n$ is a number of variables $\ge 1$). The conclusion is
about a classically integral `f : QuadForm ℤ n` with Cassels' matrix $C = (f_{ij})$ (`casselsMat`): $d(f) = \det C = 1$;
$T^{\mathsf T}CT = F$ for some $T \in \mathrm{GL}_n(\mathbb Z_2)$; $T^{\mathsf T}CT = 1$ for some $T \in \mathrm{GL}_n(\mathbb Z_p)$,
$p$ odd; and $T^{\mathsf T}CT = 1$ for some $T \in \mathrm{GL}_n(\mathbb R)$ (identity matrix $=$ the form $x_0^2 + \dots + x_{n-1}^2$).

*Proof (not via Theorem 1.2).* Take $f = 2E_8^{\perp m}$, $n = 8m$ (`Siegel.e8Sum`): classically integral, positive definite,
$\det C = 1$. At $p = 2$ both $C$ and $F$ are improperly primitive with square unit determinant, hence both are
$\mathbb Z_2$-equivalent to a sum of $n/2$ forms $2xy$ (Ch. 8, Ex. 3 (ii), `ex3_square`); for odd $p$ a unimodular form is
determined by its determinant (`Siegel.Kneser.isometricGL_of_unimodular`); over $\mathbb R$ positive definite forms are
equivalent (`Siegel.isometricGL_real_of_posDef`). -/
@[kb "cassels1978" "Ch. 9, Ex. 10 (v), p. 164"]
theorem ex10_v (m : ℕ) (hn : 0 < 8 * m) (F : Matrix (Fin (8 * m)) (Fin (8 * m)) ℤ_[2]) (hF : Fᵀ = F)
    (hdet : F.det = 1) (hd : ∀ i, (2 : ℤ_[2]) ∣ F i i) :
    ∃ f : QuadForm ℤ (8 * m), IsClassicallyIntegral f ∧ (casselsMat f).det = 1 ∧
      (∃ T : GL (Fin (8 * m)) ℤ_[2],
        (T.val)ᵀ * (casselsMat f).map (Int.castRingHom ℤ_[2]) * T.val = F) ∧
      (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ T : GL (Fin (8 * m)) ℤ_[p],
        (T.val)ᵀ * (casselsMat f).map (Int.castRingHom ℤ_[p]) * T.val = 1) ∧
      (∃ T : GL (Fin (8 * m)) ℝ, (T.val)ᵀ * (casselsMat f).map (Int.castRingHom ℝ) * T.val = 1) := by
  classical
  set Q := Siegel.e8Sum m with hQdef
  set f : QuadForm ℤ (8 * m) := (2 : ℤ) • Q with hfdef
  have hev : ∀ i j, (2 : ℤ) ∣ f.hessian i j := fun i j => by
    rw [hfdef, hessian_two_smul]; exact ⟨Q.hessian i j, by simp⟩
  have hci : IsClassicallyIntegral f := ci_of_two_dvd_hessian hev
  have hcm : casselsMat f = Q.hessian := by
    ext i j; simp [casselsMat, hfdef, hessian_two_smul]
  have hdetf : (casselsMat f).det = 1 := by rw [hcm]; exact Siegel.e8Sum_det m
  have hpos : IntQF.PosDef f := fun x hx => by
    rw [hfdef, eval_two_smul]; have := Siegel.e8Sum_posDef m x hx; linarith
  obtain ⟨hci1, hcm1, hpos1⟩ := sumSq_props (8 * m)
  have hhess_f : f.hessian.det = 2 ^ (8 * m) := by
    rw [hessian_det_eq_of_ci f hci, hdetf, mul_one]
  have hhess_1 : (QuadForm.diag (1 : Fin (8 * m) → ℤ)).hessian.det = 2 ^ (8 * m) := by
    rw [hessian_det_eq_of_ci _ hci1, hcm1, Matrix.det_one, mul_one]
  refine ⟨f, hci, hdetf, ?_, ?_, ?_⟩
  · -- the prime 2
    obtain ⟨hF1, hdet1, hd1⟩ := e8_gram_props m
    obtain ⟨D₁, hD₁, h₁, e₁⟩ := exists_hyp_equiv hn _ hF1 hdet1 hd1
    obtain ⟨D₂, hD₂, h₂, e₂⟩ := exists_hyp_equiv hn F hF hdet hd
    obtain rfl : D₁ = D₂ := list_eq_of_all_hyp D₁ D₂ hD₁ hD₂ (h₁.trans h₂.symm)
    obtain ⟨T, hT⟩ := e₁.trans e₂.symm
    refine ⟨T, ?_⟩
    apply Matrix.map_injective (f := (PadicInt.Coe.ringHom : ℤ_[2] → ℚ_[2])) (fun a b h => Subtype.ext h)
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hcm]
    exact hT
  · -- odd primes
    intro p hp hp2
    have hiso : IsometricGL (f.map (Int.castRingHom ℤ_[p]))
        ((QuadForm.diag (1 : Fin (8 * m) → ℤ)).map (Int.castRingHom ℤ_[p])) := by
      refine Kneser.isometricGL_of_unimodular hp2 _ _ ?_ ?_
      · rw [hessian_det_map, hhess_f, padic_dvd_intCast_iff]
        exact not_dvd_two_pow p hp.out hp2 _
      · rw [hessian_det_map, hessian_det_map, hhess_f, hhess_1]
    obtain ⟨T, hT⟩ := exists_gram_equiv_of_isometricGL f _ hci hci1 hiso
    rw [hcm1, Matrix.map_one _ (map_zero _) (map_one _)] at hT
    exact ⟨T, hT⟩
  · -- the real place
    have hiso := isometricGL_real_of_posDef hci hci1 hpos hpos1
    obtain ⟨T, hT⟩ := exists_gram_equiv_of_isometricGL f _ hci hci1 hiso
    rw [hcm1, Matrix.map_one _ (map_zero _) (map_one _)] at hT
    exact ⟨T, hT⟩

/-! ### Example 7 (i): the least determinant -/

/-- **Condition $(*)$ of Ex. 7** (p. 163) on a diagonal rational form $\langle a_0, a_1, a_2\rangle$: $c_2 = c_3 = -1$ and
$c_p = +1$ for every prime $p \ne 2, 3$. (The condition on $c_\infty$ is not part of $(*)$; it is determined by the real
equivalence class.) -/
def Ex7Star (a : Fin 3 → ℚ) : Prop :=
  (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseCassels a = -1 ∧
    (RatPlace.finite ⟨3, Nat.prime_three⟩).hasseCassels a = -1 ∧
    ∀ p : Nat.Primes, p.1 ≠ 2 → p.1 ≠ 3 → (RatPlace.finite p).hasseCassels a = 1

/-- **Admissible forms for Ex. 7 (i)**: a ternary integral form $f$ (`f : QuadForm ℤ 3`) that is classically integral,
$\mathbb R$-equivalent to $x_0^2 + x_1^2 - x_2^2$, and satisfies $(*)$ (`Ex7Star`) for some (equivalently, by the
isometry invariance of $c_p$, every) nondegenerate diagonal form $\langle a_0, a_1, a_2\rangle$ that is
$\mathbb Q$-equivalent to $f$. -/
def Ex7Admissible (f : QuadForm ℤ 3) : Prop :=
  IsClassicallyIntegral f ∧
  IsometricGL (f.map (Int.castRingHom ℝ)) ((QuadForm.diag ![1, 1, -1] : QuadForm ℤ 3).map (Int.castRingHom ℝ)) ∧
  ∃ a : Fin 3 → ℚ, (∀ i, a i ≠ 0) ∧ (f.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag a) ∧ Ex7Star a

/-- Helper: the determinant of the Hessian of $x_0^2 + x_1^2 - x_2^2$ is $-8$. -/
theorem hessian_det_signature_form :
    (QuadForm.diag ![1, 1, -1] : QuadForm ℤ 3).hessian.det = -8 := by
  rw [Matrix.det_fin_three]
  simp [QuadForm.hessian, QuadForm.diag]

/-- Helper: an admissible form has negative Cassels determinant (the signature of $x_0^2 + x_1^2 - x_2^2$ has one negative
sign) and its Cassels determinant is divisible by $3$. -/
theorem ex7_admissible_det (f : QuadForm ℤ 3) (h : Ex7Admissible f) :
    (casselsMat f).det < 0 ∧ (3 : ℤ) ∣ (casselsMat f).det := by
  obtain ⟨hf, ⟨g, hg⟩, a, ha, hiso, h2, h3, hp⟩ := h
  refine ⟨?_, ?_⟩
  · have hH := Lattices.Nbr.hessian_eq_of_eval' (Q := f.map (Int.castRingHom ℝ))
      (Q' := (QuadForm.diag ![1, 1, -1] : QuadForm ℤ 3).map (Int.castRingHom ℝ)) (U := g.val)
      (fun x => (hg x).symm)
    have hdet := congrArg Matrix.det hH
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hessian_det_map ℝ f,
      hessian_det_map ℝ (QuadForm.diag ![1, 1, -1] : QuadForm ℤ 3), hessian_det_signature_form] at hdet
    have hg2 : 0 < g.val.det ^ 2 := by
      have : g.val.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit |>.ne_zero
      positivity
    have hneg : ((f.hessian.det : ℤ) : ℝ) < 0 := by
      by_contra hnn
      rw [not_lt] at hnn
      have hdet' : (-8 : ℝ) = g.val.det * ((f.hessian.det : ℤ) : ℝ) * g.val.det := by exact_mod_cast hdet
      nlinarith [mul_nonneg hnn hg2.le]
    have hneg' : f.hessian.det < 0 := by exact_mod_cast hneg
    rw [hessian_det_eq_of_ci f hf] at hneg'
    by_contra hnn
    rw [not_lt] at hnn
    have : (0 : ℤ) ≤ 2 ^ 3 * (casselsMat f).det := by positivity
    omega
  · by_contra hnd
    have := hasseCassels_eq_one_of_not_dvd_d ⟨3, Nat.prime_three⟩ (by norm_num) f hf
      (by simpa using hnd) a ha hiso
    rw [h3] at this
    omega

/-- **Cassels, Ch. 9, Ex. 7 (i), p. 163, last sentence: "How small can the determinant of $f$ be made?"** *Answer:
$|d(f)| = 3$.* The set of values $|d(f)|$, where $d(f) = \det(f_{ij})$ (`casselsMat`) and $f$ ranges over the classically
integral ternary forms that are $\mathbb R$-equivalent to $x^2 + y^2 - z^2$ and satisfy $(*)$ (`Ex7Admissible`), has least
element $3$. *Lower bound:* by the key lemma (`hasseCassels_eq_one_of_not_dvd_d`) $c_3(f) = -1$ forces $3 \mid d(f)$,
and $d(f) < 0$ by the signature, so $|d(f)| \ge 3$. *Attained* by the library's example $x^2 + 3y^2 - z^2$
(`Siegel.ex7_i`, `Siegel.ex7_det`), with $d = -3$. -/
@[kb "cassels1978" "Ch. 9, Ex. 7 (i), p. 163 (the least |d(f)| is 3)"]
theorem ex7_i_least_det :
    IsLeast {m : ℤ | ∃ f : QuadForm ℤ 3, Ex7Admissible f ∧ m = |(casselsMat f).det|} 3 := by
  refine ⟨?_, ?_⟩
  · refine ⟨QuadForm.diag ![1, 3, -1], ?_, ?_⟩
    · obtain ⟨hci, hreal, h2, h3, hp⟩ := Siegel.ex7_i
      refine ⟨hci, hreal, Siegel.ex7Diag, ?_, ?_, h2, h3, hp⟩
      · intro i; fin_cases i <;> simp [Siegel.ex7Diag]
      · have : ((QuadForm.diag ![1, 3, -1] : QuadForm ℤ 3).map (Int.castRingHom ℚ)) =
            QuadForm.diag Siegel.ex7Diag := by
          ext i j
          simp [QuadForm.map, QuadForm.diag, Matrix.diagonal_apply, Siegel.ex7Diag]
          split_ifs <;> fin_cases i <;> simp
        rw [this]
        exact QuadForm.isometricIn_refl ℚ _
    · rw [Siegel.ex7_det]; rfl
  · rintro m ⟨f, hf, rfl⟩
    obtain ⟨hneg, hdvd⟩ := ex7_admissible_det f hf
    obtain ⟨k, hk⟩ := hdvd
    rw [abs_of_neg hneg]
    omega

/-! ### Lemma 6.4, (6.36)–(6.39): the Hasse–Minkowski symbols of a binary form -/

/-- Helper: the value of a classically integral binary form over $\mathbb Q$ in terms of Cassels' matrix
$G = (g_{ij})$: $g(x_0,x_1) = g_{00}x_0^2 + 2g_{01}x_0x_1 + g_{11}x_1^2$. -/
theorem evalIn_binary (g : QuadForm ℤ 2) (hg : IsClassicallyIntegral g) (x : Fin 2 → ℚ) :
    g.evalIn ℚ x = (casselsMat g 0 0 : ℚ) * x 0 ^ 2 + 2 * (casselsMat g 0 1 : ℚ) * x 0 * x 1 +
      (casselsMat g 1 1 : ℚ) * x 1 ^ 2 := by
  have h := Kneser.two_mul_evalIn (K := ℚ) g x
  rw [hessian_eq_two_smul_casselsMat hg] at h
  have h10 : casselsMat g 1 0 = casselsMat g 0 1 := (casselsMat_isSymm g).apply 0 1
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    h10] at h
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_mul, Int.cast_ofNat] at h
  linarith

/-- Helper: for a classically integral form, Cassels' diagonal entry $g_{ii}$ is the value of $g$ at the $i$-th standard
basis vector. -/
theorem casselsMat_diag_eq_eval (g : QuadForm ℤ n) (hg : IsClassicallyIntegral g) (i : Fin n) :
    casselsMat g i i = g.eval (Pi.single i 1) := by
  have h := LocalDensity.two_mul_eval_eq_hessian g (Pi.single i 1)
  rw [hessian_eq_two_smul_casselsMat hg] at h
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
  have h2 : (Pi.single i (1 : ℤ) : Fin n → ℤ) ⬝ᵥ (casselsMat g *ᵥ Pi.single i 1) = casselsMat g i i := by
    simp
  rw [h2] at h
  linarith

/-- Helper: a classically integral binary form of Cassels' determinant $a$ with $g_{ii} \ne 0$ is $\mathbb Q$-equivalent to the
diagonal form $\langle g_{ii}, a/g_{ii}\rangle$ (completing the square; $i \in \{0, 1\}$ indexes the variable that is split
off). -/
theorem binary_isometric_diag (g : QuadForm ℤ 2) (hg : IsClassicallyIntegral g) {a : ℤ}
    (hdet : (casselsMat g).det = a) (i : Fin 2) (hi : casselsMat g i i ≠ 0) :
    (g.map (Int.castRingHom ℚ)).IsometricIn ℚ
      (QuadForm.diag ![(casselsMat g i i : ℚ), (a : ℚ) / (casselsMat g i i : ℚ)]) := by
  have h10 : casselsMat g 1 0 = casselsMat g 0 1 := (casselsMat_isSymm g).apply 0 1
  have hd : (a : ℚ) = (casselsMat g 0 0 : ℚ) * casselsMat g 1 1 - (casselsMat g 0 1 : ℚ) ^ 2 := by
    rw [← hdet, Matrix.det_fin_two, h10]; push_cast; ring
  have hev : ∀ x : Fin 2 → ℚ, (g.map (Int.castRingHom ℚ)).evalIn ℚ x = g.evalIn ℚ x := fun x => by
    simp [QuadForm.evalIn, QuadForm.map, Matrix.map_apply]
  fin_cases i
  · simp only [Fin.zero_eta] at hi ⊢
    have hq : (casselsMat g 0 0 : ℚ) ≠ 0 := by exact_mod_cast hi
    refine ⟨!![1, -(casselsMat g 0 1 : ℚ) / casselsMat g 0 0; 0, 1], ?_, fun x => ?_⟩
    · simp
    · rw [hev, evalIn_binary g hg, QuadForm.evalIn_diag]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mulVec, dotProduct,
        Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Algebra.algebraMap_eq_smul_one]
      simp only [Rat.smul_one_eq_cast, Rat.cast_id]
      field_simp
      rw [hd]; ring
  · simp only [Fin.mk_one] at hi ⊢
    have hq : (casselsMat g 1 1 : ℚ) ≠ 0 := by exact_mod_cast hi
    refine ⟨!![0, 1; 1, -(casselsMat g 0 1 : ℚ) / casselsMat g 1 1], ?_, fun x => ?_⟩
    · simp
    · rw [hev, evalIn_binary g hg, QuadForm.evalIn_diag]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mulVec, dotProduct,
        Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Algebra.algebraMap_eq_smul_one]
      simp only [Rat.smul_one_eq_cast, Rat.cast_id]
      field_simp
      rw [hd]; ring

/-- Helper: $(m, a/m)_v = (m, -a)_v$ for nonzero rationals $m, a$ (since $a/m = (am)(1/m)^2$ and $(m,m)_v = (m,-1)_v$). -/
theorem hilbert_div_eq (v : RatPlace) {m a : ℚ} (hm : m ≠ 0) (ha : a ≠ 0) :
    v.hilbert m (a / m) = v.hilbert m (-a) := by
  have h1 : a / m = (a * m) * (1 / m) ^ 2 := by field_simp
  have h2 : (1 / m) ^ 2 ≠ 0 := pow_ne_zero 2 (one_div_ne_zero hm)
  rw [h1, RatPlace.hilbert_mul_right v m (a * m) _ hm (mul_ne_zero ha hm) h2, RatPlace.hilbert_sq_right v m _
    (one_div_ne_zero hm), mul_one, RatPlace.hilbert_mul_right v m a m hm ha hm, RatPlace.hilbert_self v m hm,
    ← RatPlace.hilbert_mul_right v m a (-1) hm ha (by norm_num), mul_neg_one]

/-- Helper: **the Hasse–Minkowski symbol of a binary form from one diagonal Gram entry.** Let $g$ be a classically integral
binary form with Cassels' determinant $d(g) = a \ne 0$ and $g_{ii} \ne 0$, and let $\langle d_0, d_1\rangle$ (`d`, nonzero
entries) be a diagonal form that is $\mathbb Q$-equivalent to $g$. Then $c_v(g) = (g_{ii}, -a)_v$ at every place $v$. -/
theorem hasseCassels_binary (v : RatPlace) (g : QuadForm ℤ 2) (hg : IsClassicallyIntegral g) {a : ℤ} (ha : a ≠ 0)
    (hdet : (casselsMat g).det = a) (i : Fin 2) (hi : casselsMat g i i ≠ 0) (d : Fin 2 → ℚ) (hd : ∀ j, d j ≠ 0)
    (hiso : (g.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag d)) :
    v.hasseCassels d = v.hilbert (casselsMat g i i : ℚ) (-(a : ℚ)) := by
  have hm : (casselsMat g i i : ℚ) ≠ 0 := by exact_mod_cast hi
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have h1 := binary_isometric_diag g hg hdet i hi
  have he : ∀ j, (![(casselsMat g i i : ℚ), (a : ℚ) / (casselsMat g i i : ℚ)] : Fin 2 → ℚ) j ≠ 0 := by
    intro j; fin_cases j
    · simpa using hm
    · simpa using div_ne_zero ha' hm
  have hcomp : ∀ (K : Type) [Field K] [CharZero K], (QuadForm.diag d).IsometricIn K
      (QuadForm.diag ![(casselsMat g i i : ℚ), (a : ℚ) / (casselsMat g i i : ℚ)]) := fun K _ _ =>
    QuadForm.isometricIn_trans K (QuadForm.isometricIn_symm K (HM3.isometricIn_of_rat K hiso))
      (HM3.isometricIn_of_rat K h1)
  have hat : RatPlace.atPlace (fun K _ _ => (QuadForm.diag d).IsometricIn K
      (QuadForm.diag ![(casselsMat g i i : ℚ), (a : ℚ) / (casselsMat g i i : ℚ)])) v := by
    cases v with
    | infinite => exact hcomp ℝ
    | finite p => have : Fact p.1.Prime := ⟨p.2⟩; exact hcomp ℚ_[p.1]
  rw [RatPlace.hasseCassels_isometric v d _ hd he hat]
  simp only [RatPlace.hasseCassels, Fin.prod_univ_two, Fin.lt_def]
  simp
  exact hilbert_div_eq v hm ha'

/-- **Cassels, Ch. 9, §6, (6.36)** (p. 151): *definiteness implies $c_\infty(g) = +1$.* For a form $g$ of Cassels' set (i)–(iii)
(`threeSqGenusSet a`; in particular $g$ is positive definite) and a diagonal form $\langle d_0, d_1\rangle$ (`d`, nonzero
entries) that is $\mathbb Q$-equivalent to $g$: $c_\infty(\langle d_0, d_1\rangle) = +1$ (`ex10_ii`). -/
@[kb "cassels1978" "Ch. 9, §6, (6.36), p. 151"]
theorem lemma64_c_infinite {a : ℕ} (g : QuadForm ℤ 2) (hg : g ∈ threeSqGenusSet a) (d : Fin 2 → ℚ)
    (hd : ∀ j, d j ≠ 0) (hiso : (g.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag d)) :
    RatPlace.infinite.hasseCassels d = 1 :=
  ex10_ii g hg.2.1 d hd (HM3.isometricIn_of_rat ℝ hiso)

/-- **Cassels, Ch. 9, §6, (6.38)** (p. 151): *for $p \nmid 2a$ one has automatically $c_p(g) = +1$ for any form of determinant
$a$.* For a classically integral binary form $g$ with Cassels' determinant $a$ (`hdet`), an odd prime $p \nmid a$ and a diagonal
form $\langle d_0, d_1\rangle$ that is $\mathbb Q$-equivalent to $g$: $c_p = +1$ (the key lemma
`hasseCassels_eq_one_of_not_dvd_d`). -/
@[kb "cassels1978" "Ch. 9, §6, (6.38), p. 151"]
theorem lemma64_c_unit (p : Nat.Primes) (hp2 : p.1 ≠ 2) {n a : ℕ} (g : QuadForm ℤ n) (hg : IsClassicallyIntegral g)
    (hdet : (casselsMat g).det = a) (hpa : ¬ p.1 ∣ a) (d : Fin n → ℚ) (hd : ∀ j, d j ≠ 0)
    (hiso : (g.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag d)) :
    (RatPlace.finite p).hasseCassels d = 1 :=
  hasseCassels_eq_one_of_not_dvd_d p hp2 g hg (by rw [hdet]; exact_mod_cast hpa) d hd hiso

/-- Helper: for a squarefree $a$, an odd prime $p \mid a$ and a form $g$ of Cassels' set (i)–(iii), some coordinate $i$ has
$p \nmid v_i$, where $a \mid v_iv_j + g_{ij}$ (otherwise $p$ divides all $g_{ij}$ and $p^2 \mid \det(g_{ij}) = a$). -/
theorem exists_coord_not_dvd {a : ℕ} (hsf : Squarefree a) {p : ℕ} (hp : p.Prime) (hpa : p ∣ a) (g : QuadForm ℤ 2)
    (hdet : (casselsMat g).det = a) (v : Fin 2 → ℤ) (hv : ∀ i j, (a : ℤ) ∣ v i * v j + casselsMat g i j) :
    ∃ i, ¬ (p : ℤ) ∣ v i := by
  by_contra hno
  push Not at hno
  have hpa' : (p : ℤ) ∣ (a : ℤ) := by exact_mod_cast hpa
  have hG : ∀ i j, (p : ℤ) ∣ casselsMat g i j := fun i j => by
    have h1 : (p : ℤ) ∣ v i * v j + casselsMat g i j := hpa'.trans (hv i j)
    have h2 : (p : ℤ) ∣ v i * v j := (hno i).mul_right _
    simpa using dvd_sub h1 h2
  have h10 : casselsMat g 1 0 = casselsMat g 0 1 := (casselsMat_isSymm g).apply 0 1
  have hpp : (p : ℤ) * p ∣ (a : ℤ) := by
    rw [← hdet, Matrix.det_fin_two, h10]
    exact dvd_sub (mul_dvd_mul (hG 0 0) (hG 1 1)) (mul_dvd_mul (hG 0 1) (hG 0 1))
  have hpp' : p * p ∣ a := by exact_mod_cast hpp
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p hpp'))

/-- **Cassels, Ch. 9, §6, (6.37)** (p. 151): *for an odd prime $p \mid a$, $c_p(g) = \left(\frac{-1}{p}\right)$.* Let $a$ be
squarefree and $g$ a form of Cassels' set (i)–(iii) (`threeSqGenusSet a`: classically integral, positive definite,
$d(g) = a$, and $a \mid v_iv_j + g_{ij}$ for some integers $v_0, v_1$); then $g$ represents $-1$ modulo $p$ and over
$\mathbb Z_p$, so that $g \cong \langle -1, -a\rangle$ over $\mathbb Q_p$ and $c_p = (-1,-a)_p = \left(\frac{-1}{p}\right)$. For
any diagonal form $\langle d_0, d_1\rangle$ ($\mathbb Q$-equivalent to $g$): $c_p(\langle d_0,d_1\rangle) =$ `legendreSym p (-1)`.

*Reconstruction note.* The printed (6.37) is garbled in the machine-read text; the value $\left(\frac{-1}{p}\right)$ is
reconstructed from the argument ("(iii)$'_p$ is equivalent to $g$ representing $-1$") and confirmed by the proof here, which
computes $c_p(g) = (g_{ii}, -a)_p$ for a coordinate with $p \nmid v_i$, where $g_{ii} \equiv -v_i^2 \pmod p$, by the explicit
formula for the Hilbert symbol at an odd prime. -/
@[kb "cassels1978" "Ch. 9, §6, (6.37), p. 151"]
theorem lemma64_c_odd_dvd (p : Nat.Primes) (hp2 : p.1 ≠ 2) {a : ℕ} (hsf : Squarefree a) (hpa : p.1 ∣ a)
    (g : QuadForm ℤ 2) (hg : g ∈ threeSqGenusSet a) (d : Fin 2 → ℚ) (hd : ∀ j, d j ≠ 0)
    (hiso : (g.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag d)) :
    haveI : Fact p.1.Prime := ⟨p.2⟩
    (RatPlace.finite p).hasseCassels d = legendreSym p.1 (-1) := by
  have : Fact p.1.Prime := ⟨p.2⟩
  obtain ⟨hci, hpos, hdet, v, hv⟩ := hg
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast hsf.ne_zero
  obtain ⟨i, hi⟩ := exists_coord_not_dvd hsf p.2 hpa g hdet v hv
  set m : ℤ := casselsMat g i i with hmdef
  have hpa' : (p.1 : ℤ) ∣ (a : ℤ) := by exact_mod_cast hpa
  have hmv : (p.1 : ℤ) ∣ v i * v i + m := hpa'.trans (hv i i)
  have hpm : ¬ (p.1 : ℤ) ∣ m := by
    intro h
    have h1 : (p.1 : ℤ) ∣ v i * v i := by simpa using dvd_sub hmv h
    rcases (Nat.prime_iff_prime_int.mp p.2).dvd_or_dvd h1 with h2 | h2 <;> exact hi h2
  have hm0 : m ≠ 0 := fun h => hpm (h ▸ dvd_zero _)
  rw [hasseCassels_binary (RatPlace.finite p) g hci ha0 hdet i hm0 d hd hiso, ← hmdef]
  -- the Hilbert symbol at `p`
  obtain ⟨b, hb⟩ := hpa
  have hbp : ¬ p.1 ∣ b := fun hpb => by
    obtain ⟨c, hc⟩ := hpb
    exact p.2.one_lt.ne' (Nat.isUnit_iff.mp (hsf p.1 ⟨c, by rw [hb, hc]; ring⟩))
  have hbp' : ¬ (p.1 : ℤ) ∣ (-(b : ℤ)) := by
    rw [dvd_neg]; exact_mod_cast hbp
  have hsym := ConwaySloane.hilbert_odd_int p.1 hp2 0 1 m (-(b : ℤ)) (m : ℚ) (-(((a : ℤ)) : ℚ)) hpm hbp' (by simp)
    (by rw [hb]; push_cast; ring)
  have hsym' : (RatPlace.finite p).hilbert (m : ℚ) (-(((a : ℤ)) : ℚ)) = legendreSym p.1 m := by
    have h := hsym
    simp only [zero_mul, pow_zero, one_mul, mul_one, pow_one] at h
    exact h
  rw [hsym']
  -- `m ≡ -v_i²` modulo `p`
  have hz : ((v i * v i + m : ℤ) : ZMod p.1) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hmv
  have hmz : (m : ZMod p.1) = -((v i : ZMod p.1) ^ 2) := by
    push_cast at hz; linear_combination hz
  have hvz : (v i : ZMod p.1) ≠ 0 := fun h => hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
  unfold legendreSym
  rw [hmz, show (((-1 : ℤ) : ℤ) : ZMod p.1) = -1 by simp, neg_eq_neg_one_mul, map_mul,
    quadraticChar_sq_one' hvz, mul_one]

/-- **Cassels, Ch. 9, §6, (6.39)** (p. 151): *by the product formula, $c_2(g) = \prod_{p \mid a,\ p \ne 2}\left(\frac{-1}{p}\right)$.*
For a squarefree $a$, a form $g$ of Cassels' set (i)–(iii) and a diagonal form $\langle d_0, d_1\rangle$ that is
$\mathbb Q$-equivalent to $g$:
$c_2 = \prod_{p \mid a,\ p \ne 2} \left(\frac{-1}{p}\right)$ (written with the Jacobi symbol `jacobiSym (-1) p`, which for a
prime $p$ is the Legendre symbol). The proof is the product formula `hasseCassels_product_formula` with $c_\infty = 1$ (6.36),
$c_p = \left(\frac{-1}{p}\right)$ for odd $p \mid a$ (6.37) and $c_p = 1$ for $p \nmid 2a$ (6.38). -/
@[kb "cassels1978" "Ch. 9, §6, (6.39), p. 151"]
theorem lemma64_c_two {a : ℕ} (hsf : Squarefree a) (g : QuadForm ℤ 2) (hg : g ∈ threeSqGenusSet a)
    (d : Fin 2 → ℚ) (hd : ∀ j, d j ≠ 0) (hiso : (g.map (Int.castRingHom ℚ)).IsometricIn ℚ (QuadForm.diag d)) :
    (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseCassels d = ∏ p ∈ a.primeFactors.erase 2, jacobiSym (-1) p := by
  classical
  set T : Finset ℕ := a.primeFactors.erase 2 with hT
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  set f : {p // p ∈ T} → RatPlace := fun q => RatPlace.finite ⟨q.1, hTp q.1 q.2⟩ with hf
  have hfinj : Function.Injective f := by
    intro q q' h
    have h' := RatPlace.finite.inj h
    exact Subtype.ext (congrArg (fun x : Nat.Primes => (x : ℕ)) h')
  set S : Finset RatPlace := insert RatPlace.infinite (insert (RatPlace.finite ⟨2, Nat.prime_two⟩) (T.attach.image f))
    with hS
  have hodd : ∀ q : {p // p ∈ T}, (RatPlace.finite ⟨q.1, hTp q.1 q.2⟩).hasseCassels d = jacobiSym (-1) q.1 := by
    intro q
    have hq : q.1 ∈ a.primeFactors.erase 2 := q.2
    rw [Finset.mem_erase] at hq
    have : Fact q.1.Prime := ⟨hTp q.1 q.2⟩
    have h := lemma64_c_odd_dvd ⟨q.1, hTp q.1 q.2⟩ hq.1 hsf (Nat.dvd_of_mem_primeFactors hq.2) g hg d hd hiso
    rw [h]
    exact jacobiSym.legendreSym.to_jacobiSym q.1 (-1)
  have hsupp : Function.mulSupport (fun v : RatPlace => v.hasseCassels d) ⊆ (S : Set RatPlace) := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    simp only [hS, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image]
    rcases v with _ | p
    · exact Or.inl rfl
    · by_cases hp2 : p.1 = 2
      · exact Or.inr (Or.inl (by congr 1; exact Subtype.ext hp2))
      · by_cases hpa : p.1 ∣ a
        · refine Or.inr (Or.inr ⟨⟨p.1, ?_⟩, Finset.mem_attach _ _, rfl⟩)
          rw [hT, Finset.mem_erase]
          exact ⟨hp2, Nat.mem_primeFactors.mpr ⟨p.2, hpa, hsf.ne_zero⟩⟩
        · exact absurd (lemma64_c_unit p hp2 g hg.1 hg.2.2.1 hpa d hd hiso) hv
  obtain ⟨-, hprod⟩ := hasseCassels_product_formula d hd
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp] at hprod
  have h2 : RatPlace.finite ⟨2, Nat.prime_two⟩ ∉ T.attach.image f := by
    simp only [Finset.mem_image, hf]
    rintro ⟨q, -, hq⟩
    have h' : q.1 = 2 := congrArg (fun x : Nat.Primes => (x : ℕ)) (RatPlace.finite.inj hq)
    have hq2 : q.1 ∈ a.primeFactors.erase 2 := q.2
    rw [Finset.mem_erase] at hq2
    exact hq2.1 h'
  rw [hS, Finset.prod_insert (by simp), Finset.prod_insert h2, Finset.prod_image fun x _ y _ h => hfinj h,
    lemma64_c_infinite g hg d hd hiso, one_mul] at hprod
  have hP : ∏ q ∈ T.attach, (f q).hasseCassels d = ∏ p ∈ T, jacobiSym (-1) p := by
    rw [← Finset.prod_attach T (fun p => jacobiSym (-1) p)]
    exact Finset.prod_congr rfl fun q _ => hodd q
  rw [hP] at hprod
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]

/-- Helper: the Jacobi symbol is multiplicative in the denominator over a finite product of nonzero naturals. -/
theorem jacobiSym_prod_finset (c : ℤ) (s : Finset ℕ) (hs : ∀ p ∈ s, p ≠ 0) :
    jacobiSym c (∏ p ∈ s, p) = ∏ p ∈ s, jacobiSym c p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jacobiSym.one_right]
  | insert q s hq ih =>
    have hq0 : q ≠ 0 := hs q (Finset.mem_insert_self _ _)
    have hs' : ∀ p ∈ s, p ≠ 0 := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hP : (∏ p ∈ s, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs'
    have : NeZero q := ⟨hq0⟩
    have : NeZero (∏ p ∈ s, p) := ⟨hP⟩
    rw [Finset.prod_insert hq, Finset.prod_insert hq, jacobiSym.mul_right, ih hs']

/-- **Cassels, Ch. 9, §6, proof of Lemma 6.4, p. 151: $a \equiv 7 \pmod 8$ is impossible.** *"When $a \equiv 7 \pmod 8$, so
$-a \in (\mathbb Q_2^{\times})^2$, then $c_2(g) = +1$ for any form of determinant $a$, but the right-hand side of (6.39) is
$(+1)(-1) = -1$: a contradiction."* Formally: for a squarefree $a \equiv 7 \pmod 8$ the set (i)–(iii) of Cassels
(`threeSqGenusSet a`) is empty. (For $a \equiv 7 \pmod 8$, $c_2(g) = (g_{00}, -a)_2 = 1$ since $-a \equiv 1 \pmod 8$ is a square
in $\mathbb Q_2$, whereas (6.39) gives $c_2 = \left(\frac{-1}{a}\right) = (-1)^{(a-1)/2} = -1$.) -/
@[kb "cassels1978" "Ch. 9, §6, proof of Lemma 6.4, p. 151 (a ≡ 7 mod 8 is impossible)"]
theorem threeSqGenusSet_eq_empty_of_seven {a : ℕ} (hsf : Squarefree a) (h7 : a % 8 = 7) :
    threeSqGenusSet a = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hg
  have hg' := hg
  obtain ⟨hci, hpos, hdet, v, hv⟩ := hg'
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast hsf.ne_zero
  have hG00 : casselsMat g 0 0 ≠ 0 := by
    rw [casselsMat_diag_eq_eval g hci 0]
    refine (hpos (Pi.single 0 1) fun h => ?_).ne'
    have := congrFun h 0
    simp at this
  have hm : (casselsMat g 0 0 : ℚ) ≠ 0 := by exact_mod_cast hG00
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast hsf.ne_zero
  have h1 := binary_isometric_diag g hci hdet 0 hG00
  have he : ∀ j, (![(casselsMat g 0 0 : ℚ), ((a : ℤ) : ℚ) / (casselsMat g 0 0 : ℚ)] : Fin 2 → ℚ) j ≠ 0 := by
    intro j; fin_cases j
    · simpa using hm
    · simpa using div_ne_zero (Int.cast_ne_zero.mpr ha0) hm
  -- `c_2 = 1`
  have hc2 : (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseCassels
      ![(casselsMat g 0 0 : ℚ), ((a : ℤ) : ℚ) / (casselsMat g 0 0 : ℚ)] = 1 := by
    rw [hasseCassels_binary (RatPlace.finite ⟨2, Nat.prime_two⟩) g hci ha0 hdet 0 hG00 _ he h1]
    have hodd : ¬ (2 : ℤ) ∣ -((a : ℕ) : ℤ) := by omega
    have hsq : IsSquare (((-(a : ℤ) : ℤ) : ℚ_[2]) / ((1 : ℤ) : ℚ_[2])) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := Prescribed.isSquare_div_of_modEq 2 (-(a : ℤ)) 1 hodd (by omega) (by
        simp only [ite_true]; unfold Int.ModEq; omega)
      simpa using this
    have hsq' : IsSquare (((-(a : ℚ)) : ℚ) : ℚ_[2]) := by
      simpa using hsq
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    show hilbertSymbol ℚ_[2] ((casselsMat g 0 0 : ℚ) : ℚ_[2]) ((-(((a : ℤ)) : ℚ) : ℚ) : ℚ_[2]) = 1
    exact PadicClass.hs_of_isSquare _ _ (by simpa using ha') (by simpa using hsq')
  -- `c_2 = -1`
  have hc2' := lemma64_c_two hsf g hg _ he h1
  have hodda : ¬ 2 ∣ a := by omega
  have hera : a.primeFactors.erase 2 = a.primeFactors :=
    Finset.erase_eq_of_notMem fun h2 => hodda (Nat.dvd_of_mem_primeFactors h2)
  rw [hera] at hc2'
  have hJ : ∏ p ∈ a.primeFactors, jacobiSym (-1) p = jacobiSym (-1) a := by
    rw [← jacobiSym_prod_finset (-1) _ fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero,
      Nat.prod_primeFactors_of_squarefree hsf]
  rw [hJ, jacobiSym.at_neg_one (by rw [Nat.odd_iff]; omega), ZMod.χ₄_nat_three_mod_four (by omega)] at hc2'
  rw [hc2] at hc2'
  omega

end QuadFormsKB.Cassels.HasseInv
