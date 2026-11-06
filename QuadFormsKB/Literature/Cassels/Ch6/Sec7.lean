/-
# Cassels, Chapter 6, §7 and Theorem 1.3: rational forms with prescribed local forms

**Setting.** The places of $\mathbb Q$ are `RatPlace` ($\infty$ and the primes $p$), with completions
$\mathbb Q_\infty = \mathbb R$ and $\mathbb Q_p$; `v.atPlace P` is the property $P$ over $\mathbb Q_v$. A regular local
form at $v$ is given as a diagonal form $\langle\alpha_v\rangle = \langle\alpha_{v,0}, \dots, \alpha_{v,n-1}\rangle$ with
$\alpha_{v,i} \in \mathbb Q^\times$, viewed over $\mathbb Q_v$. This loses no generality: every regular form over
$\mathbb Q_v$ is $\mathbb Q_v$-equivalent to a diagonal one, and each diagonal coefficient is a rational number times a
square of $\mathbb Q_v^\times$ (`Prescribed.exists_rat_sq_class`; over $\mathbb R$, $\pm1$ times a square). Cassels'
invariants of $\langle\alpha_v\rangle$ are the determinant $d = \prod_i\alpha_{v,i}$, compared in
$\mathbb Q_v^\times/(\mathbb Q_v^\times)^2$ (`SameSquareClass`), and $c_v = \prod_{i<j}(\alpha_{v,i}, \alpha_{v,j})_v$
(`RatPlace.hasseCassels`). Indices are $0, \dots, n-1$ (Cassels: $1, \dots, n$).

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6)
* Theorem 1.3 (existence of a rational form with prescribed local forms): `exists_form_of_local`;
* its proof in §7 (6.p4), in the steps `exists_split_rat` (splitting off a represented value with rational
  coefficients), `reduce_step` (the forms $g_v$ with $f_v \cong \langle t\rangle \perp g_v$ satisfy the hypotheses
  again), `exists_rep_two` (the case $n = 2$) and `exists_rep_three_le` (the choice of $t$ for $n \ge 3$).

**Proof notes.** Induction on $n$, as in Cassels §7. For $n \ge 2$ one finds $t \in \mathbb Q^\times$ represented by
every $f_v$; then $f_v \cong \langle t\rangle \perp g_v$ with $d(g_v) = d_0/t$ and $c_v(g_v) = c_v(f_v)(t, d_0/t)_v$, so
the $g_v$ satisfy the hypotheses by the product formula, and $f = \langle t\rangle \perp g$ for the form $g$ given by
induction. For $n = 2$, $\langle\alpha_{v,0}, \alpha_{v,1}\rangle$ represents $t$ iff $(t, -d_0)_v = c_v(f_v)$, and such a
$t$ exists by the theorem on rationals with prescribed Hilbert symbols (`Prescribed.exists_rat_prescribed_hilbert`,
O'Meara 71:19; Cassels uses the Corollary to Dirichlet's Theorem 5.1 directly). For $n \ge 3$, Cassels' set $P$ (the
primes $2$, those dividing $d_0$ and those with $c_p(f_p) = -1$) and $\infty$: $t$ is chosen in the square class of a
value of $f_p$ for $p \in P$ and with the sign of a value of $f_\infty$ (`Prescribed.exists_rat_approx_sq_classes`); for
$p \notin P$ the form $f_p$ is isotropic, hence represents $t$. The base case is $n = 1$ (Cassels starts at $n = 2$).
-/
import QuadFormsKB.Literature.Cassels.Ch6.Sec7Steps
import QuadFormsKB.Literature.Cassels.Ch6.Sec7Rep

namespace QuadFormsKB.Cassels.Ch6

open QuadForm

variable {m n : ℕ}

/-- **Cassels, Ch. 6, Theorem 1.3**: *let $n \ge 2$ and $d_0 \in \mathbb Q^\times$ be given, and for every $p$
(including $p = \infty$) let $f_p$ be a regular form over $\mathbb Q_p$ in $n$ variables with (i)
$d(f_p) = d_0$ in $\mathbb Q_p^\times/(\mathbb Q_p^\times)^2$ and (ii) $c_p(f_p) = 1$ for almost all $p$ and
$\prod_p c_p(f_p) = 1$; then there is a rational form $f$ with $d(f) = d_0$ in $\mathbb Q^\times/(\mathbb Q^\times)^2$
which is equivalent over $\mathbb Q_p$ to $f_p$ for every $p$.*

Here $f_v = \langle\alpha_v\rangle$ with $\alpha_{v,i} \in \mathbb Q^\times$ (no loss of generality, see the module
docstring), condition (ii) is "the set of $v$ with $c_v(f_v) = -1$ is finite and has an even number of elements", and
the form $f = \langle a_0, \dots, a_{n-1}\rangle$ found is diagonal. Stated for $n \ge 1$ (Cassels: $n \ge 2$; for
$n = 1$ the statement is immediate). -/
@[kb "cassels1978" "Ch. 6, Thm. 1.3, p. 77"]
theorem exists_form_of_local (hn : 1 ≤ n) (d₀ : ℚ) (hd₀ : d₀ ≠ 0) (α : RatPlace → Fin n → ℚ)
    (hα : ∀ v i, α v i ≠ 0)
    (hdet : ∀ v : RatPlace, v.atPlace fun K _ _ => SameSquareClass K (∏ i, α v i) d₀)
    (hfin : {v : RatPlace | v.hasseCassels (α v) = -1}.Finite)
    (heven : Even {v : RatPlace | v.hasseCassels (α v) = -1}.ncard) :
    ∃ a : Fin n → ℚ, (∀ i, a i ≠ 0) ∧ SameSquareClass ℚ (∏ i, a i) d₀ ∧
      ∀ v : RatPlace, v.atPlace fun K _ _ => (diag a).IsometricIn K (diag (α v)) := by
  induction n generalizing d₀ with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact exists_form_one d₀ hd₀ α hdet
    obtain ⟨t, ht, hrep⟩ : ∃ t : ℚ, t ≠ 0 ∧
        ∀ v : RatPlace, v.atPlace fun K _ _ => (diag (α v)).RepresentsIn K t := by
      rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | h2
      · exact exists_rep_two d₀ hd₀ α hα hdet hfin heven
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
        exact exists_rep_three_le d₀ hd₀ α hα hdet hfin
    obtain ⟨β, hβ, hβdet, hβfin, hβeven, hiso⟩ := reduce_step d₀ hd₀ α hα hdet hfin heven ht hrep
    obtain ⟨b, hb, hbdet, hbiso⟩ := ih hm (d₀ / t) (div_ne_zero hd₀ ht) β hβ hβdet hβfin hβeven
    refine ⟨Fin.cons t b, fun i => Fin.cases ht hb i, ?_, fun v => ?_⟩
    · obtain ⟨s, hs, e⟩ := hbdet
      refine ⟨s, hs, ?_⟩
      simp only [Algebra.algebraMap_self, RingHom.id_apply] at e ⊢
      rw [Fin.prod_cons, e]
      field_simp
    · have key : ∀ (K : Type) [Field K] [CharZero K], (diag b).IsometricIn K (diag (β v)) →
          (diag (α v)).IsometricIn K (diag (Fin.cons t (β v))) →
          (diag (Fin.cons t b)).IsometricIn K (diag (α v)) := fun K _ _ h1 h2 =>
        isometricIn_trans K (isometricIn_diag_cons_of K t h1) (isometricIn_symm K h2)
      have h1 := hbiso v
      have h2 := hiso v
      cases v with
      | infinite => exact key ℝ h1 h2
      | finite p =>
        have : Fact p.1.Prime := ⟨p.2⟩
        exact key ℚ_[p.1] h1 h2

end QuadFormsKB.Cassels.Ch6
