/-
# Dirichlet $L$-functions of $\mathbb{F}_q[t]$ are polynomials

For a finite field $k = \mathbb{F}_q$, a monic $m \in k[t]$ and a multiplicative character $\chi$ of $k[t]/(m)$ (a
Dirichlet character modulo $m$), the $L$-function is
$$L(u, \chi) = \sum_{f \text{ monic}} \chi(f)\, u^{\deg f} = \sum_{n \ge 0} \Big(\sum_{\substack{f \text{ monic} \\ \deg f = n}}
  \chi(f)\Big) u^n \qquad (u = q^{-s}).$$
**Theorem** (Rosen, Prop. 4.3; `charSum_eq_zero`, `lSeries_eq_lPoly`): if $\chi$ is nontrivial, the inner sums vanish
for $n \ge \deg m$, so $L(u, \chi)$ is a polynomial in $u$ of degree at most $\deg m - 1$. *Proof:* for
$n \ge \deg m$ the monic polynomials $t^n + g$, $\deg g < n$, cover every residue class modulo $m$ equally often
($g \mapsto g \bmod m$ is an onto additive map), and $\sum_{r \bmod m} \chi(r) = 0$.

This is the first step of Kornblum's proof of Dirichlet's theorem for $\mathbb{F}_q[t]$ (Rosen, Ch. 4); the remaining
analytic step ($L(q^{-1}, \chi) \ne 0$ and the density argument) is not formalized.
The monic polynomials of degree $n$ are parametrized by their lower coefficients (`monicOf`, `exists_monicOf`).

Indices are 0-based: $c : \mathrm{Fin}\, n \to k$ gives $t^n + c_0 + c_1 t + \dots + c_{n-1} t^{n-1}$.
-/
import Mathlib
import QuadFormsKB.Citation

open Polynomial Finset

namespace QuadFormsKB.RatFuncDirichlet

variable {k : Type} [Field k]

/-- The monic polynomial $t^n + \sum_{i < n} c_i t^i$ with lower coefficients $c$. -/
noncomputable def monicOf (n : ℕ) (c : Fin n → k) : k[X] := X ^ n + ∑ i, C (c i) * X ^ (i : ℕ)

lemma natDegree_sum_lt (n : ℕ) (c : Fin n → k) (_hn : 0 < n) :
    (∑ i, C (c i) * X ^ (i : ℕ) : k[X]).degree < n :=
  degree_sum_fin_lt c

lemma monicOf_monic (n : ℕ) (c : Fin n → k) : (monicOf n c).Monic := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [monicOf]
  · exact monic_X_pow_add (natDegree_sum_lt n c hn)

lemma natDegree_monicOf (n : ℕ) (c : Fin n → k) : (monicOf n c).natDegree = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [monicOf]
  · unfold monicOf
    rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]; exact natDegree_sum_lt n c hn

/-- **Every monic polynomial of degree $n$ is `monicOf n c`** for its lower coefficients $c_i = f_i$. -/
lemma exists_monicOf {f : k[X]} (hf : f.Monic) : f = monicOf f.natDegree fun i => f.coeff i := by
  unfold monicOf
  conv_lhs => rw [hf.as_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]

variable [Fintype k] {R : Type*} [CommRing R] [IsDomain R]

/-- **The character sum over monic polynomials of degree $n$:** $\sum_{f \text{ monic}, \deg f = n} \chi(f \bmod m)$,
for a multiplicative character $\chi$ of $k[t]/(m)$ (parametrized by `monicOf`). -/
@[kb "rosen2002" "Ch. 4, p. 35 (Dirichlet L-series, sums over monic polynomials of degree n) [unverified]"]
noncomputable def charSum (m : k[X]) [Fintype (k[X] ⧸ Ideal.span {m})]
    (χ : MulChar (k[X] ⧸ Ideal.span {m}) R) (n : ℕ) : R :=
  ∑ c : Fin n → k, χ (Ideal.Quotient.mk _ (monicOf n c))

/-- **The character sums vanish in high degree** (Rosen, Prop. 4.3): for $m$ monic, $\chi$ a nontrivial character
of $k[t]/(m)$ and $n \ge \deg m$, $\sum_{f \text{ monic}, \deg f = n} \chi(f) = 0$. -/
@[kb "rosen2002" "Ch. 4, Prop. 4.3 [unverified]"]
theorem charSum_eq_zero {m : k[X]} (hm : m.Monic) [Fintype (k[X] ⧸ Ideal.span {m})]
    (χ : MulChar (k[X] ⧸ Ideal.span {m}) R) (hχ : χ ≠ 1) {n : ℕ} (hn : m.natDegree ≤ n) :
    charSum m χ n = 0 := by
  classical
  set Q := k[X] ⧸ Ideal.span {m}
  set mk : k[X] →+* Q := Ideal.Quotient.mk _
  have hm1 : m ≠ 1 := by
    rintro rfl
    apply hχ
    have : Subsingleton (k[X] ⧸ Ideal.span {(1 : k[X])}) :=
      Ideal.Quotient.subsingleton_iff.mpr Ideal.span_singleton_one
    ext a
    rw [Subsingleton.elim a 1, Units.val_one, map_one, map_one]
  -- the additive map `c ↦ ∑ cᵢ tⁱ mod m`
  let φ : (Fin n → k) →+ Q :=
    { toFun := fun c => mk (∑ i, C (c i) * X ^ (i : ℕ))
      map_zero' := by simp
      map_add' := fun c d => by simp [add_mul, Finset.sum_add_distrib] }
  have hφ : Function.Surjective φ := by
    intro r
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨fun i => (p %ₘ m).coeff i, ?_⟩
    have hdeg : (p %ₘ m).natDegree < n :=
      (natDegree_modByMonic_lt p hm hm1).trans_le hn
    change mk (∑ i : Fin n, C ((p %ₘ m).coeff i) * X ^ (i : ℕ)) = mk p
    rw [Fin.sum_univ_eq_sum_range (fun i => C ((p %ₘ m).coeff i) * X ^ i), ← as_sum_range_C_mul_X_pow' _ hdeg]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    have := modByMonic_add_div p m
    exact ⟨-(p /ₘ m), by linear_combination this⟩
  have key : charSum m χ n = ∑ c : Fin n → k, χ (mk (X ^ n) + φ c) := by
    unfold charSum monicOf
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [φ, mk, map_add]
  refine key.trans ?_
  rw [Finset.sum_comp (fun b => χ (mk (X ^ n) + b)) (fun c => φ c)]
  have himage : (Finset.univ : Finset (Fin n → k)).image (fun c => φ c) = Finset.univ :=
    Finset.eq_univ_of_forall fun b => by
      obtain ⟨c, rfl⟩ := hφ b
      exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
  rw [himage]
  have hfib : ∀ b : Q, #{c | φ c = b} = #{c | φ c = 0} := fun b =>
    AddMonoidHom.card_fiber_eq_of_mem_range φ (hφ b) (hφ 0)
  simp only [hfib]
  rw [← Finset.smul_sum]
  have htrans : ∑ b : Q, χ (mk (X ^ n) + b) = ∑ b : Q, χ b :=
    Equiv.sum_comp (Equiv.addLeft (mk (X ^ n))) (fun b => χ b)
  rw [htrans, MulChar.sum_eq_zero_of_ne_one hχ, smul_zero]

/-- **The polynomial $L(u, \chi) = \sum_{n < \deg m} \big(\sum_{\deg f = n} \chi(f)\big) u^n$.** -/
noncomputable def lPoly (m : k[X]) [Fintype (k[X] ⧸ Ideal.span {m})]
    (χ : MulChar (k[X] ⧸ Ideal.span {m}) R) : R[X] :=
  ∑ n ∈ Finset.range m.natDegree, Polynomial.C (charSum m χ n) * Polynomial.X ^ n

/-- **Dirichlet $L$-functions of $\mathbb{F}_q[t]$ are polynomials** (Rosen, Prop. 4.3): for $m$ monic and $\chi$ a
nontrivial character modulo $m$, the formal power series $L(u, \chi) = \sum_n \big(\sum_{\deg f = n} \chi(f)\big) u^n$
equals the polynomial `lPoly m χ`, of degree at most $\deg m - 1$. -/
@[kb "rosen2002" "Ch. 4, Prop. 4.3 [unverified]"]
theorem lSeries_eq_lPoly {m : k[X]} (hm : m.Monic) [Fintype (k[X] ⧸ Ideal.span {m})]
    (χ : MulChar (k[X] ⧸ Ideal.span {m}) R) (hχ : χ ≠ 1) :
    PowerSeries.mk (charSum m χ) = (lPoly m χ : PowerSeries R) := by
  ext n
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, lPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range m.natDegree) n]
  split_ifs with h
  · rfl
  · exact charSum_eq_zero hm χ hχ (by simpa using h)

end QuadFormsKB.RatFuncDirichlet
