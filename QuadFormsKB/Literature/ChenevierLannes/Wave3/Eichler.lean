/-
# Chenevier–Lannes, §5.5: the Eichler commutation relation in genus $1$ for even unimodular lattices

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.3, p. 7 (the Eichler commutation relations), §5.1,
Proposition 5.1.1, p. 124, and §5.5, Theorem 5.5.1, p. 142 (proved there for genus $g = 1$). Printed page numbers.

**Layer.** Earlier files (`Neighbors.lean`): the $p$-neighbours `Siegel.Kneser.neighbors Q p` of an even unimodular $L$
(given by its integral form $Q$, $q_L = Q$), the neighbour numbers `nbNum`; the representation numbers
$r_L(m) = |\{x \in L : q_L(x) = m\}|$ (`Siegel.repNum`, `Siegel.Kneser.latRep` for a lattice in $\mathbb{Q}^n$), the
$m$-th $q$-coefficient of the theta series $\vartheta(L) = \sum_{x \in L} q^{q_L(x)}$.

The Hecke operator $T(p^2)$ on $M_k(\mathrm{SL}_2(\mathbb{Z}))$ acts on $q$-coefficients by
$$a_m(T(p^2)g) = \sum_{d \mid (p^2, m)} d^{k-1}\, a_{mp^2/d^2}(g)
  = a_{p^2m}(g) + [p \mid m]\,p^{k-1}a_m(g) + p^{2k-2}a_{m/p^2}(g)$$
(Serre, *Cours d'arithmétique*, VII.5.3, quoted on p. 142; $a_{m/p^2} = 0$ unless $p^2 \mid m$); `heckeTpSqCoeff`
is this formula on a coefficient sequence.

**Proves** ($p$ an odd prime; unconditional):
- `eichler_genus_one` (Theorem 5.5.1 with $P = 1$, $d = 0$): for $L$ even unimodular of dimension $n \ge 4$,
  $$\sum_{L' \sim_p L} \vartheta(L') = \frac{p^{n-2} - p}{p - 1}\,\vartheta(L) + T(p^2)\,\vartheta(L),$$
  coefficient by coefficient, with $k = n/2$ and $\frac{p^{n-2} - p}{p-1} = p + p^2 + \cdots + p^{n-3}$ (from the
  library's single-lattice relation `Siegel.Kneser.sum_latRep_neighbors_even`);
- `eichler_genus_one_classes`: the same relation on the class set, $\vartheta(T_px) = \bigl(\tfrac{p^{n-2}-p}{p-1} +
  T(p^2)\bigr)\vartheta(x)$ for $x \in X_n$, i.e. $\sum_y N_p(x, y)\,r_y(m)$ in place of the sum over neighbours.

*Not covered:* harmonic coefficients $P \ne 1$ (Theorem 5.5.1 in general), $p = 2$, and genus $g \ge 2$
(Proposition 5.1.1).
-/
import QuadFormsKB.Literature.ChenevierLannes.Neighbors
import QuadFormsKB.Siegel.EichlerCommutation

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-- **The Hecke operator $T(p^2)$ of weight $k$ on $q$-coefficients** (Serre, VII.5.3; Chenevier–Lannes, p. 142): for a
coefficient sequence $a : \mathbb{Z} \to \mathbb{Z}$ (with $a_m$ for $m < 0$ unused),
$$T(p^2)(a)_m = a_{p^2m} + [p \mid m]\,p^{k-1}a_m + [p^2 \mid m]\,p^{2k-2}a_{m/p^2}.$$ -/
@[kb "chenevierlannes2019" "§5.5, p. 142 (T(p^2) on q-coefficients)"]
def heckeTpSqCoeff (k p : ℕ) (a : ℤ → ℤ) (m : ℤ) : ℤ :=
  a ((p : ℤ) ^ 2 * m) + (if (p : ℤ) ∣ m then (p : ℤ) ^ (k - 1) * a m else 0) +
    (if (p : ℤ) ^ 2 ∣ m then (p : ℤ) ^ (2 * k - 2) * a (m / (p : ℤ) ^ 2) else 0)

/-- **Theorem 5.5.1, genus $1$, $P = 1$** (Chenevier–Lannes, p. 142; $p$ odd): for an even unimodular lattice $L$ of
dimension $n \ge 4$ and every $m \in \mathbb{Z}$,
$$\sum_{L' \sim_p L} r_{L'}(m) = (p + p^2 + \cdots + p^{n-3})\,r_L(m) + T(p^2)(r_L)_m, \qquad k = n/2,$$
the sum over the $p$-neighbours $L'$ of $L$ in $\mathbb{Q} \otimes L$. Unconditional. -/
@[kb "chenevierlannes2019" "Thm. 5.5.1, p. 142 (g = 1, P = 1, odd p)"]
theorem eichler_genus_one {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (hn : 4 ≤ n) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (m : ℤ) :
    (∑ L ∈ neighbors Q p, (latRep Q L m : ℤ)) =
      (∑ i ∈ Finset.Ico 1 (n - 2), (p : ℤ) ^ i) * repNum Q m +
        heckeTpSqCoeff (n / 2) p (fun t => (repNum Q t : ℤ)) m := by
  classical
  have hp := (Fact.out : p.Prime)
  have hdet := not_dvd_det hQ p
  obtain ⟨j, hj⟩ := eight_dvd_of_isEvenUnimodular hQ
  have heven : Even n := ⟨4 * j, by omega⟩
  have h := sum_latRep_neighbors_even hQ.posDef hp2 hdet heven (by omega) m
  have h0 := card_qv_zero (Q := Q) (p := p) hp2 hdet heven (by omega)
  rw [discSign_eq_one hQ, one_mul] at h0
  rw [h0] at h
  have hp0 : ((p : ℤ) - 1) ≠ 0 := by have := hp.one_lt; omega
  have hS : (∑ i ∈ Finset.Ico 1 (n - 2), (p : ℤ) ^ i) * ((p : ℤ) - 1) = (p : ℤ) ^ (n - 2) - p := by
    have := geom_sum_Ico_mul (p : ℤ) (m := 1) (n := n - 2) (by omega)
    simpa using this
  have hpow : (p : ℤ) ^ (n - 1) = p * (p : ℤ) ^ (n - 2) := by
    rw [← pow_succ']; congr 1; omega
  have h2k : 2 * (n / 2) - 2 = n - 2 := by omega
  have hD : (repNumDiv Q p m : ℤ) = if (p : ℤ) ^ 2 ∣ m then (repNum Q (m / (p : ℤ) ^ 2) : ℤ) else 0 := by
    unfold repNumDiv; split_ifs <;> simp
  unfold heckeTpSqCoeff
  rw [h2k]
  apply mul_left_cancel₀ hp0
  rw [h]
  by_cases hm : (p : ℤ) ∣ m
  · have hT3 : (if (p : ℤ) ^ 2 ∣ m then (p : ℤ) ^ (n - 2) * (repNum Q (m / (p : ℤ) ^ 2) : ℤ) else 0) =
        (p : ℤ) ^ (n - 2) * (repNumDiv Q p m : ℤ) := by
      rw [hD]; split_ifs <;> simp
    simp only [if_pos hm]
    rw [hT3]
    linear_combination (repNum Q m : ℤ) * hpow - (repNum Q m : ℤ) * hS
  · have hm2 : ¬ (p : ℤ) ^ 2 ∣ m := fun h2 => hm (Dvd.dvd.trans (dvd_pow_self _ two_ne_zero) h2)
    have hD0 : (repNumDiv Q p m : ℤ) = 0 := by rw [hD, if_neg hm2]
    simp only [if_neg hm, if_neg hm2, hD0]
    linear_combination (-(repNum Q m : ℤ)) * hS

/-- **Theorem 5.5.1 on the class set** (Chenevier–Lannes, p. 142 with §3.2, p. 55; $p$ odd): for $x \in X_n$
($n \ge 4$) and every $m$,
$$\sum_{y \in X_n} N_p(x, y)\,r_y(m) = (p + \cdots + p^{n-3})\,r_x(m) + T(p^2)(r_x)_m,$$
i.e. $\vartheta(T_p x) = \bigl(\tfrac{p^{n-2} - p}{p - 1} + T(p^2)\bigr)\vartheta(x)$ on $q$-coefficients. Here $r_x$
is `QClass.repNum x`. Unconditional. -/
@[kb "chenevierlannes2019" "Thm. 5.5.1, p. 142, on X_n (g = 1, P = 1, odd p)"]
theorem eichler_genus_one_classes (hn : 4 ≤ n) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x : QClass n}
    (hx : x ∈ classSet n) (m : ℤ) :
    (∑ y ∈ (classSet_finite n).toFinset, (nbNum p x y : ℤ) * (y.repNum m : ℤ)) =
      (∑ i ∈ Finset.Ico 1 (n - 2), (p : ℤ) ^ i) * x.repNum m +
        heckeTpSqCoeff (n / 2) p (fun t => (x.repNum t : ℤ)) m := by
  classical
  have hQ := out_isEvenUnimodular hx
  have hT : ∀ c, c ∈ (classSet_finite n).toFinset ↔ c ∈ genusClasses (Quotient.out (s := intSetoid n) x) := by
    intro c; rw [Set.Finite.mem_toFinset, classSet_eq_genusClasses hQ]
  have hx' : ∀ t, x.repNum t = repNum (Quotient.out (s := intSetoid n) x) t := by
    intro t
    conv_lhs => rw [← (Quotient.out_eq x : classOf (Quotient.out (s := intSetoid n) x) = x)]
    rfl
  have h1 := sum_latRep_eq_sum_classes (p := p) hp2 (not_dvd_det hQ p) _ hT m
  have h2 : (∑ L ∈ neighbors (Quotient.out (s := intSetoid n) x) p, (latRep (Quotient.out (s := intSetoid n) x) L m : ℤ)) =
      ∑ y ∈ (classSet_finite n).toFinset, (nbNum p x y : ℤ) * (y.repNum m : ℤ) := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [h1]
    rfl
  rw [← h2, eichler_genus_one hQ hn hp2 m]
  simp only [hx']

end QuadFormsKB.ChenevierLannes
