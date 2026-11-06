/-
# Tsen–Lang for quadratic forms over $\mathbb{F}_q(t)$

**Theorem** (`RatFuncPlace.isotropic_of_five_le`). Let $k$ be a finite field (any characteristic) and
$Q$ a quadratic form in $n \ge 5$ variables over $k(t)$, with no nondegeneracy hypothesis. Then $Q$ is
isotropic over $k(t)$. This is O'Meara 66:2 for $F = \mathbb{F}_q(t)$ (every form in $\ge 5$ variables is
isotropic).

*Proof* (the Chevalley–Warning / Tsen–Lang argument, not O'Meara's, which derives 66:2 from 66:1 and
local facts). Clear denominators so that $Q = \sum_{0 \le i \le j < n} p_{ij}\, x_i x_j$ with
$p_{ij} \in k[t]$ of degree $\le r$. Look for $x_i = \sum_{l=0}^{s} y_{i,l}\, t^l$ with $s = 2r + 3$
and unknowns $y_{i,l} \in k$ ($n(s+1)$ of them). The coefficients of $t^m$, $0 \le m \le r + 2s$, of
$Q(x)$ are $r + 2s + 1$ polynomials of degree $\le 2$ in the $y_{i,l}$, and
$2(r + 2s + 1) < 5(s+1) \le n(s+1)$. By Chevalley–Warning
(`char_dvd_card_solutions_of_sum_lt`) the number of common zeros is divisible by $\operatorname{char} k$;
$y = 0$ is one, so there is a nonzero one. Then $Q(x) \in k[t]$ has degree $\le r + 2s$ and all those
coefficients vanish, so $Q(x) = 0$ with $x \ne 0$.

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Defs.QuadForm

open Polynomial

namespace QuadFormsKB.RatFuncPlace

namespace Tsen

variable {k : Type} [Field k] [Fintype k]

/-- All coefficients of the polynomial `Q : A[X]` have total degree `≤ d`. -/
def CoeffDeg {σ : Type} (d : ℕ) (Q : (MvPolynomial σ k)[X]) : Prop :=
  ∀ m, (Q.coeff m).totalDegree ≤ d

variable {σ : Type}

lemma CoeffDeg.zero {d : ℕ} : CoeffDeg (σ := σ) (k := k) d 0 := fun m => by simp

lemma CoeffDeg.sum {ι : Type} (s : Finset ι) {d : ℕ} {F : ι → (MvPolynomial σ k)[X]}
    (h : ∀ i ∈ s, CoeffDeg d (F i)) : CoeffDeg d (∑ i ∈ s, F i) := fun m => by
  rw [finsetSum_coeff]
  exact (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun i hi => h i hi m)

lemma CoeffDeg.mul {d₁ d₂ : ℕ} {Q₁ Q₂ : (MvPolynomial σ k)[X]} (h₁ : CoeffDeg d₁ Q₁)
    (h₂ : CoeffDeg d₂ Q₂) : CoeffDeg (d₁ + d₂) (Q₁ * Q₂) := fun m => by
  rw [coeff_mul]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun ab _ => ?_)
  exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (h₁ _) (h₂ _))

lemma CoeffDeg.mono {d d' : ℕ} {Q : (MvPolynomial σ k)[X]} (h : CoeffDeg d Q) (hd : d ≤ d') :
    CoeffDeg d' Q := fun m => (h m).trans hd

/-- The generic polynomial `∑_{l ≤ s} X_{i,l} t^l`. -/
noncomputable def genPoly (s : ℕ) {n : ℕ} (i : Fin n) :
    (MvPolynomial (Fin n × Fin (s + 1)) k)[X] :=
  ∑ l : Fin (s + 1), monomial (l : ℕ) (MvPolynomial.X (i, l))

lemma coeffDeg_genPoly (s : ℕ) {n : ℕ} (i : Fin n) :
    CoeffDeg 1 (genPoly (k := k) s i) := fun m => by
  unfold genPoly
  rw [finsetSum_coeff]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  rw [coeff_monomial]
  split_ifs
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

lemma coeffDeg_C_map {n : ℕ} (s : ℕ) (p : k[X]) :
    CoeffDeg (σ := Fin n × Fin (s + 1)) 0 (p.map (MvPolynomial.C : k →+* _)) := fun m => by
  rw [coeff_map]; simp

/-- The generic form `∑_{i ≤ j} p_ij P_i P_j` over `A[X]`. -/
noncomputable def Gform {n : ℕ} (s : ℕ) (p : Fin n → Fin n → k[X]) :
    (MvPolynomial (Fin n × Fin (s + 1)) k)[X] :=
  ∑ i, ∑ j, if i ≤ j then
    (p i j).map (MvPolynomial.C : k →+* _) * genPoly s i * genPoly s j else 0

/-- The polynomial `∑_l y_{i,l} t^l`. -/
noncomputable def xs {n : ℕ} (s : ℕ) (y : Fin n × Fin (s + 1) → k) (i : Fin n) : k[X] :=
  ∑ l : Fin (s + 1), monomial (l : ℕ) (y (i, l))

lemma map_genPoly {n : ℕ} (s : ℕ) (y : Fin n × Fin (s + 1) → k) (i : Fin n) :
    (genPoly s i).map (MvPolynomial.eval y) = xs s y i := by
  simp [genPoly, xs, Polynomial.map_sum]

lemma map_C_map' {n : ℕ} (s : ℕ) (y : Fin n × Fin (s + 1) → k) (p : k[X]) :
    (p.map (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (s + 1)) k)).map
      (MvPolynomial.eval y) = p := by
  rw [Polynomial.map_map]
  have : (MvPolynomial.eval y).comp (MvPolynomial.C : k →+* _) = RingHom.id k := by
    ext a; simp
  rw [this, Polynomial.map_id]

lemma map_Gform {n : ℕ} (s : ℕ) (p : Fin n → Fin n → k[X]) (y : Fin n × Fin (s + 1) → k) :
    (Gform s p).map (MvPolynomial.eval y) =
      ∑ i, ∑ j, if i ≤ j then p i j * xs s y i * xs s y j else 0 := by
  unfold Gform
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [Polynomial.map_mul, Polynomial.map_mul, map_C_map', map_genPoly, map_genPoly]
  · simp

lemma natDegree_xs {n : ℕ} (s : ℕ) (y : Fin n × Fin (s + 1) → k) (i : Fin n) :
    (xs s y i).natDegree ≤ s := by
  unfold xs
  refine natDegree_sum_le_of_forall_le _ _ fun l _ => ?_
  exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp l.2)

lemma coeff_xs {n : ℕ} (s : ℕ) (y : Fin n × Fin (s + 1) → k) (i : Fin n) (l : Fin (s + 1)) :
    (xs s y i).coeff l = y (i, l) := by
  unfold xs
  rw [finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ l := fun h => hb (Fin.ext h)
    simp [this]
  · simp

/-- If a predicate holds at `0` and the number of its solutions is divisible by some `q > 1`,
it holds at some nonzero point. -/
lemma exists_ne_zero_of_dvd_card {α : Type} [Fintype α] [Zero α] (P : α → Prop)
    {_ : DecidablePred P} {q : ℕ} (hq : 1 < q) (h0 : P 0) (h : q ∣ Fintype.card {x // P x}) :
    ∃ x, x ≠ 0 ∧ P x := by
  by_contra hc
  push_neg at hc
  have hle : Fintype.card {x // P x} ≤ 1 := by
    refine Fintype.card_le_one_iff.mpr fun a b => Subtype.ext ?_
    have ha : a.1 = 0 := by
      by_contra h; exact hc _ h a.2
    have hb : b.1 = 0 := by
      by_contra h; exact hc _ h b.2
    rw [ha, hb]
  have hpos : 0 < Fintype.card {x // P x} := Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have := Nat.le_of_dvd hpos h
  omega

/-- The polynomial identity: a form over `k[t]` in `n ≥ 5` variables has a nontrivial zero. -/
lemma main_poly {n : ℕ} (hn : 5 ≤ n) (p : Fin n → Fin n → k[X]) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧ ∑ i, ∑ j, (if i ≤ j then p i j * x i * x j else 0) = 0 := by
  classical
  set r : ℕ := Finset.univ.sup (fun ij : Fin n × Fin n => (p ij.1 ij.2).natDegree) with hr
  have hpr : ∀ i j, (p i j).natDegree ≤ r := fun i j =>
    Finset.le_sup (f := fun ij : Fin n × Fin n => (p ij.1 ij.2).natDegree) (Finset.mem_univ (i, j))
  set s : ℕ := 2 * r + 3 with hs
  have hG : CoeffDeg 2 (Gform s p) := by
    refine CoeffDeg.sum _ fun i _ => CoeffDeg.sum _ fun j _ => ?_
    split_ifs
    · have := ((coeffDeg_C_map (n := n) s (p i j)).mul (coeffDeg_genPoly (k := k) s i)).mul
        (coeffDeg_genPoly (k := k) s j)
      exact this.mono (by norm_num)
    · exact CoeffDeg.zero
  let f : ℕ → MvPolynomial (Fin n × Fin (s + 1)) k := fun m => (Gform s p).coeff m
  have hcard : ∑ m ∈ Finset.range (r + 2 * s + 1), (f m).totalDegree
      < Fintype.card (Fin n × Fin (s + 1)) := by
    calc ∑ m ∈ Finset.range (r + 2 * s + 1), (f m).totalDegree
        ≤ ∑ m ∈ Finset.range (r + 2 * s + 1), 2 := Finset.sum_le_sum fun m _ => hG m
      _ = 2 * (r + 2 * s + 1) := by simp [mul_comm]
      _ < n * (s + 1) := by
        have : 5 * (s + 1) ≤ n * (s + 1) := Nat.mul_le_mul_right _ hn
        omega
      _ = _ := by simp
  obtain ⟨q, hq⟩ := CharP.exists k
  have hdvd := char_dvd_card_solutions_of_sum_lt q hcard
  have hprime : q.Prime := CharP.char_is_prime k q
  -- key: eval y (f m) = coefficient m of the evaluated form
  have hcoef : ∀ (y : Fin n × Fin (s + 1) → k) m,
      MvPolynomial.eval y (f m) =
        (∑ i, ∑ j, if i ≤ j then p i j * xs s y i * xs s y j else 0).coeff m := by
    intro y m
    rw [← map_Gform, coeff_map]
  have hz0 : ∀ m ∈ Finset.range (r + 2 * s + 1),
      MvPolynomial.eval (0 : Fin n × Fin (s + 1) → k) (f m) = 0 := by
    intro m _
    rw [hcoef]
    have : ∀ i, xs s (0 : Fin n × Fin (s + 1) → k) i = 0 := fun i => by simp [xs]
    simp [this]
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_of_dvd_card _ hprime.one_lt hz0 hdvd
  refine ⟨xs s y, ?_, ?_⟩
  · intro h
    apply hy0
    funext ⟨i, l⟩
    have := coeff_xs s y i l
    rw [h] at this
    simpa using this.symm
  · rw [← map_Gform]
    ext m
    rw [coeff_map, coeff_zero]
    by_cases hm : m < r + 2 * s + 1
    · exact hy m (Finset.mem_range.mpr hm)
    · have hdeg : (∑ i, ∑ j, if i ≤ j then p i j * xs s y i * xs s y j else (0 : k[X])).natDegree
          ≤ r + 2 * s := by
        refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
        refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
        split_ifs
        · refine (natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans
            (add_le_add (hpr i j) (natDegree_xs s y i))) (natDegree_xs s y j))).trans (by omega)
        · simp
      rw [← map_Gform] at hdeg
      have := coeff_eq_zero_of_natDegree_lt (p := (Gform s p).map (MvPolynomial.eval y))
        (n := m) (by omega)
      rw [coeff_map] at this
      exact this

end Tsen

open Tsen in
/-- **Tsen–Lang / O'Meara 66:2 for $F = \mathbb{F}_q(t)$.** Over the rational function field $k(t)$
of a finite field $k$ (any characteristic), every quadratic form in $n \ge 5$ variables is isotropic;
no nondegeneracy hypothesis is needed. The proof is the Chevalley–Warning argument (see the module
docstring), not O'Meara's. *Update:* for $F = \mathbb{F}_q(t)$, 66:2 needs no local theory.
Indices are 0-based. -/
@[kb "omeara1963" "§66, 66:2, p. 188 (F = F_q(t)); proof: Chevalley–Warning (Tsen–Lang), not O'Meara's"]
theorem isotropic_of_five_le {k : Type} [Field k] [Fintype k] {n : ℕ} (hn : 5 ≤ n)
    (Q : QuadForm (RatFunc k) n) : Q.IsotropicIn (RatFunc k) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors k[X])
    (Finset.univ : Finset (Fin n × Fin n)) (fun ij => Q.coeff ij.1 ij.2)
  have hb' : ∀ i j, ∃ a : k[X], algebraMap k[X] (RatFunc k) a = (b : k[X]) • Q.coeff i j :=
    fun i j => hb (i, j) (Finset.mem_univ _)
  choose p hp using hb'
  obtain ⟨x, hx0, hx⟩ := main_poly hn p
  refine ⟨fun i => algebraMap k[X] (RatFunc k) (x i), ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    exact (map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mp
      (by simpa using congrFun h i)
  · have hbne : algebraMap k[X] (RatFunc k) (b : k[X]) ≠ 0 := by
      intro h
      exact nonZeroDivisors.coe_ne_zero b
        ((map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mp h)
    have key : algebraMap k[X] (RatFunc k) (b : k[X]) * Q.evalIn (RatFunc k)
        (fun i => algebraMap k[X] (RatFunc k) (x i)) = 0 := by
      have h2 := congrArg (algebraMap k[X] (RatFunc k)) hx
      rw [map_zero, map_sum] at h2
      rw [← h2, QuadForm.evalIn, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · have e : algebraMap k[X] (RatFunc k) (p i j) = algebraMap k[X] (RatFunc k) (b : k[X]) *
            Q.coeff i j := by
          rw [hp i j, Algebra.smul_def]
        rw [map_mul, map_mul, e, Algebra.algebraMap_self, RingHom.id_apply]
        ring
      · simp
    exact (mul_eq_zero.mp key).resolve_left hbne

end QuadFormsKB.RatFuncPlace
