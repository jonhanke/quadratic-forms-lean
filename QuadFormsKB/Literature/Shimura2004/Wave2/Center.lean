/-
# Shimura 2004, Theorem 2.8: the centers 𝔠 and 𝔠⁺

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I: Theorem 2.8 and
Lemma 2.7 (iv) (printed p. 19). Page numbers are printed pages.

**Setting and dictionary.** As in `QuadFormsKB/Literature/Shimura2004/Wave2/CliffordLemmas.lean`: $F$ a field of
characteristic $\ne 2$, `Q : QuadraticForm F V` nondegenerate, $A(V)$ = `CliffordAlgebra Q`, $A^+(V)$ =
`evenOdd Q 0` (= `CliffordAlgebra.even Q` as a submodule), $z = h_1\cdots h_n$ = `orthProd Q (List.ofFn h)` for an
orthogonal basis $h_0, \dots, h_{n-1}$ of $V$ (Shimura's $h_1, \dots, h_n$, shifted to 0-based indexing).
The hypothesis `hanis : ∀ i, Q (h i) ≠ 0` follows from the nondegeneracy of `Q` together with orthogonality and
spanning; it is kept as an explicit hypothesis for convenience.

**Proves** (all unconditional; standard axioms only)
* Theorem 2.8 (ii) / Lemma 2.7 (iv), $n$ odd: the center of $A(V)$ is $F + Fz$ (`theorem_2_8_ii_center`).
* Theorem 2.8 (i) / Lemma 2.7 (iv), $n$ even and $> 0$: the center of $A^+(V)$ is $F + Fz$
  (`theorem_2_8_i_center`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave2.CliffordLemmas
import QuadFormsKB.Literature.OMeara.Sec54
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

local notation "A" => CliffordAlgebra Q

/-! ### Auxiliary facts -/

/-- An element of $A^+(V)$ (`evenOdd Q 0`) lies in the even subalgebra. -/
theorem mem_even_of_mem_evenOdd_zero {a : A} (ha : a ∈ evenOdd Q 0) : a ∈ CliffordAlgebra.even Q := by
  rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]; exact ha

/-- The product of the vectors of a list of length $m$ lies in $A^{m \bmod 2}$. -/
theorem orthProd_mem_evenOdd (l : List V) : orthProd Q l ∈ evenOdd Q (l.length : ZMod 2) := by
  induction l with
  | nil => simpa [orthProd] using one_mem_evenOdd_zero (Q := Q)
  | cons a t ih =>
    rw [orthProd_cons, List.length_cons, Nat.cast_succ, add_comm (t.length : ZMod 2) 1]
    exact mul_mem_evenOdd (ι_mem_evenOdd_one Q a) ih

/-- If $z^2 = c \ne 0$ is a scalar and $dz = k$ is a scalar, then $d = (k/c)z$. -/
theorem eq_smul_of_mul_eq_algebraMap {z d : A} {c k : F} (hz : z * z = algebraMap F A c) (hc : c ≠ 0)
    (hd : d * z = algebraMap F A k) : d = (k / c) • z := by
  have h1 : c • d = k • z := by
    calc c • d = algebraMap F A c * d := Algebra.smul_def _ _
      _ = d * algebraMap F A c := Algebra.commutes c d
      _ = (d * z) * z := by rw [← hz, mul_assoc]
      _ = k • z := by rw [hd, Algebra.smul_def]
  calc d = c⁻¹ • (c • d) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = (k / c) • z := by rw [h1, smul_smul, div_eq_inv_mul]

/-- Nondegenerate case of Corollary 2.9 (O'Meara 54:4): an element of $A^+(V)$ commuting with all vectors is a
scalar. -/
theorem scalar_of_evenOdd_zero_commute (hQ : (QuadraticMap.associated Q).Nondegenerate) {a : A}
    (ha : a ∈ evenOdd Q 0) (hc : ∀ x : V, a * ι Q x = ι Q x * a) : ∃ c : F, a = algebraMap F A c :=
  mem_range_algebraMap_of_mem_even_of_commute Q hQ (mem_even_of_mem_evenOdd_zero ha) hc

/-- Conjugation by an anisotropic vector $x$: $\beta \mapsto x\beta x^{-1} = \varphi[x]^{-1}\,x\beta x$. -/
def conjV (Q : QuadraticForm F V) (x : V) (β : CliffordAlgebra Q) : CliffordAlgebra Q :=
  (Q x)⁻¹ • (ι Q x * β * ι Q x)

theorem conjV_mul {x : V} (hx : Q x ≠ 0) (β γ : A) : conjV Q x (β * γ) = conjV Q x β * conjV Q x γ := by
  have key : ι Q x * β * ι Q x * (ι Q x * γ * ι Q x) = Q x • (ι Q x * (β * γ) * ι Q x) := by
    have e : ι Q x * β * ι Q x * (ι Q x * γ * ι Q x) = ι Q x * β * (ι Q x * ι Q x) * γ * ι Q x := by
      simp only [mul_assoc]
    rw [e, ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc]
  unfold conjV
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, key, smul_smul]
  congr 1
  field_simp

theorem conjV_conjV {x : V} (hx : Q x ≠ 0) (β : A) : conjV Q x (conjV Q x β) = β := by
  have key : ι Q x * (ι Q x * β * ι Q x) * ι Q x = Q x • Q x • β := by
    have e : ι Q x * (ι Q x * β * ι Q x) * ι Q x = (ι Q x * ι Q x) * β * (ι Q x * ι Q x) := by
      simp only [mul_assoc]
    rw [e, ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, smul_smul]
  unfold conjV
  rw [mul_smul_comm, smul_mul_assoc, key, smul_smul, smul_smul, smul_smul]
  convert one_smul F β using 2
  field_simp

theorem conjV_mem_evenOdd_zero (x : V) {β : A} (hβ : β ∈ evenOdd Q 0) : conjV Q x β ∈ evenOdd Q 0 := by
  have h := mul_mem_evenOdd (mul_mem_evenOdd (ι_mem_evenOdd_one Q x) hβ) (ι_mem_evenOdd_one Q x)
  rw [show (1 + 0 + 1 : ZMod 2) = 0 from by decide] at h
  exact Submodule.smul_mem _ _ h

theorem conjV_commute {x : V} (hx : Q x ≠ 0) {β : A} (hc : ∀ g ∈ evenOdd Q 0, β * g = g * β) :
    ∀ g ∈ evenOdd Q 0, conjV Q x β * g = g * conjV Q x β := by
  intro g hg
  have hg' : conjV Q x g ∈ evenOdd Q 0 := conjV_mem_evenOdd_zero x hg
  have e : g = conjV Q x (conjV Q x g) := (conjV_conjV hx g).symm
  calc conjV Q x β * g = conjV Q x β * conjV Q x (conjV Q x g) := by rw [← e]
    _ = conjV Q x (β * conjV Q x g) := (conjV_mul hx _ _).symm
    _ = conjV Q x (conjV Q x g * β) := by rw [hc _ hg']
    _ = conjV Q x (conjV Q x g) * conjV Q x β := conjV_mul hx _ _
    _ = g * conjV Q x β := by rw [← e]

/-- (L1) If $\beta \in A^+$ commutes with $A^+$ then $\beta\,y = y\,(x\beta x^{-1})$ for every $y \in V$. -/
theorem mul_ι_eq_ι_mul_conjV {x : V} (hx : Q x ≠ 0) {β : A} (hc : ∀ g ∈ evenOdd Q 0, β * g = g * β)
    (y : V) : β * ι Q y = ι Q y * conjV Q x β := by
  have h1 := hc (ι Q y * ι Q x) (ι_mul_ι_mem_evenOdd_zero Q y x)
  have h2 : β * ι Q y * (ι Q x * ι Q x) = ι Q y * (ι Q x * β * ι Q x) := by
    calc β * ι Q y * (ι Q x * ι Q x) = β * (ι Q y * ι Q x) * ι Q x := by simp only [mul_assoc]
      _ = (ι Q y * ι Q x) * β * ι Q x := by rw [h1]
      _ = ι Q y * (ι Q x * β * ι Q x) := by simp only [mul_assoc]
  have h3 : ι Q y * (ι Q x * β * ι Q x) = Q x • (ι Q y * conjV Q x β) := by
    simp only [conjV, mul_smul_comm, smul_smul, mul_inv_cancel₀ hx, one_smul]
  have h4 : β * ι Q y * (ι Q x * ι Q x) = Q x • (β * ι Q y) := by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  exact smul_right_injective A hx (by simp only [← h4, h2, h3])

section Center

variable {n : ℕ} (h : Fin n → V)

/-- $z^2$ is a nonzero scalar when all $\varphi[h_i] \ne 0$. -/
theorem orthProd_sq_ne_zero (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hanis : ∀ i, Q (h i) ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ orthProd Q (List.ofFn h) * orthProd Q (List.ofFn h) = algebraMap F A c := by
  refine ⟨_, ?_, orthProd_sq h horth⟩
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Finset.prod_ne_zero_iff.2 fun i _ => hanis i)

/-- **Theorem 2.8 (ii)** (Shimura 2004, p. 19): for $n$ odd the center $\mathfrak{c}$ of $A(V)$ is $F + Fz$,
$z = h_1\cdots h_n$ for an orthogonal basis $h_1, \dots, h_n$ (here $h_0, \dots, h_{n-1}$).
The hypothesis `hanis` follows from the nondegeneracy of `Q`, orthogonality and `hspan`. This also gives the
odd case of Lemma 2.7 (iv). -/
@[kb "shimura2004" "Thm. 2.8 (ii), p. 19 (n odd: the center of A(V) is F + Fz)"]
theorem theorem_2_8_ii_center (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : Submodule.span F (Set.range h) = ⊤) (hanis : ∀ i, Q (h i) ≠ 0) (hn : Odd n) (a : A) :
    (∀ g, a * g = g * a) ↔ ∃ c d : F, a = algebraMap F A c + d • orthProd Q (List.ofFn h) := by
  have hz1 : orthProd Q (List.ofFn h) ∈ evenOdd Q 1 := by
    have := orthProd_mem_evenOdd (Q := Q) (List.ofFn h)
    rwa [List.length_ofFn, (ZMod.natCast_eq_one_iff_odd).2 hn] at this
  constructor
  · intro hc
    obtain ⟨c, hc0, hcz⟩ := orthProd_sq_ne_zero h horth hanis
    have hmem : a ∈ evenOdd Q 0 ⊔ evenOdd Q 1 := by
      rw [(evenOdd_isCompl Q).sup_eq_top]; trivial
    obtain ⟨a0, ha0, a1, ha1, rfl⟩ := Submodule.mem_sup.1 hmem
    have hdisj := (evenOdd_isCompl Q).disjoint
    rw [Submodule.disjoint_def] at hdisj
    have hv : ∀ x : V, a0 * ι Q x = ι Q x * a0 := by
      intro x
      have hx := hc (ι Q x)
      have m1 : a0 * ι Q x - ι Q x * a0 ∈ evenOdd Q 1 := by
        refine Submodule.sub_mem _ ?_ ?_
        · simpa using mul_mem_evenOdd ha0 (ι_mem_evenOdd_one Q x)
        · simpa using mul_mem_evenOdd (ι_mem_evenOdd_one Q x) ha0
      have m0 : a0 * ι Q x - ι Q x * a0 ∈ evenOdd Q 0 := by
        have e : a0 * ι Q x - ι Q x * a0 = ι Q x * a1 - a1 * ι Q x := by
          rw [add_mul, mul_add] at hx
          rw [sub_eq_sub_iff_add_eq_add]; exact hx.trans (add_comm _ _)
        rw [e]
        refine Submodule.sub_mem _ ?_ ?_
        · have := mul_mem_evenOdd (ι_mem_evenOdd_one Q x) ha1
          rwa [show (1 + 1 : ZMod 2) = 0 from by decide] at this
        · have := mul_mem_evenOdd ha1 (ι_mem_evenOdd_one Q x)
          rwa [show (1 + 1 : ZMod 2) = 0 from by decide] at this
      exact sub_eq_zero.1 (hdisj _ m0 m1)
    have hv1 : ∀ x : V, a1 * ι Q x = ι Q x * a1 := by
      intro x
      have hx := hc (ι Q x)
      have := hv x
      rw [add_mul, mul_add, this] at hx
      exact add_left_cancel hx
    obtain ⟨c0, hc0'⟩ := scalar_of_evenOdd_zero_commute hQ ha0 hv
    have hz := orthProd_mem_center_of_odd h horth hspan hn
    have hzv : ∀ x : V, orthProd Q (List.ofFn h) * ι Q x = ι Q x * orthProd Q (List.ofFn h) := fun x => hz _
    have hm : a1 * orthProd Q (List.ofFn h) ∈ evenOdd Q 0 := by
      have := mul_mem_evenOdd ha1 hz1
      rwa [show (1 + 1 : ZMod 2) = 0 from by decide] at this
    obtain ⟨k, hk⟩ := scalar_of_evenOdd_zero_commute hQ hm (fun x => by
      rw [mul_assoc, hzv, ← mul_assoc, hv1, mul_assoc])
    have := eq_smul_of_mul_eq_algebraMap hcz hc0 hk
    exact ⟨c0, k / c, by rw [hc0', this]⟩
  · rintro ⟨c, d, rfl⟩ g
    have hz := orthProd_mem_center_of_odd h horth hspan hn g
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hz, Algebra.commutes]

/-- **Theorem 2.8 (i)** (Shimura 2004, p. 19): for $n$ even and $> 0$ the center $\mathfrak{c}^+$ of $A^+(V)$ is
$F + Fz$, $z = h_1\cdots h_n$ for an orthogonal basis $h_1, \dots, h_n$ (here $h_0, \dots, h_{n-1}$). Here $A^+(V)$ is
`evenOdd Q 0`. The hypothesis `hanis` follows from the nondegeneracy of `Q`, orthogonality and `hspan`. -/
@[kb "shimura2004" "Thm. 2.8 (i), p. 19 (n even > 0: the center of A⁺(V) is F + Fz)"]
theorem theorem_2_8_i_center (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : Submodule.span F (Set.range h) = ⊤) (hanis : ∀ i, Q (h i) ≠ 0) (hn : Even n) (hpos : 0 < n)
    (a : A) (ha : a ∈ evenOdd Q 0) :
    (∀ g ∈ evenOdd Q 0, a * g = g * a) ↔ ∃ c d : F, a = algebraMap F A c + d • orthProd Q (List.ofFn h) := by
  have hz0 : orthProd Q (List.ofFn h) ∈ evenOdd Q 0 := by
    have := orthProd_mem_evenOdd (Q := Q) (List.ofFn h)
    rwa [List.length_ofFn, (ZMod.natCast_eq_zero_iff_even).2 hn] at this
  have hodd : Odd (n - 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k - 1, by omega⟩
  have hanti : ∀ y : V, orthProd Q (List.ofFn h) * ι Q y = -(ι Q y * orthProd Q (List.ofFn h)) := by
    intro y
    rw [vec_mul_orthProd h horth hspan y, hodd.neg_one_pow, neg_smul, one_smul, neg_neg]
  have hanti' : ∀ (y : V) (w : A), orthProd Q (List.ofFn h) * (ι Q y * w) =
      -(ι Q y * (orthProd Q (List.ofFn h) * w)) := by
    intro y w
    rw [← mul_assoc, hanti, neg_mul, mul_assoc]
  constructor
  · intro hcomm
    obtain ⟨c, hc0, hcz⟩ := orthProd_sq_ne_zero h horth hanis
    set x := h ⟨0, hpos⟩ with hxdef
    have hx : Q x ≠ 0 := hanis _
    set b := conjV Q x a with hb
    have hbe : b ∈ evenOdd Q 0 := conjV_mem_evenOdd_zero x ha
    have hbc := conjV_commute hx hcomm
    have hv1 : ∀ y : V, a * ι Q y = ι Q y * b := mul_ι_eq_ι_mul_conjV hx hcomm
    have hv2 : ∀ y : V, b * ι Q y = ι Q y * a := by
      intro y
      rw [mul_ι_eq_ι_mul_conjV hx hbc y, conjV_conjV hx]
    obtain ⟨c0, hc0'⟩ := scalar_of_evenOdd_zero_commute hQ (Submodule.add_mem _ ha hbe) (fun y => by
      rw [add_mul, mul_add, hv1, hv2]; abel)
    have hd : ∀ y : V, (a - b) * ι Q y = -(ι Q y * (a - b)) := by
      intro y
      rw [sub_mul, mul_sub, hv1, hv2]; abel
    have hdz : (a - b) * orthProd Q (List.ofFn h) ∈ evenOdd Q 0 := by
      simpa using mul_mem_evenOdd (Submodule.sub_mem _ ha hbe) hz0
    obtain ⟨k, hk⟩ := scalar_of_evenOdd_zero_commute hQ hdz (fun y => by
      rw [mul_assoc, hanti, mul_neg, ← mul_assoc, hd, neg_mul, neg_neg, mul_assoc])
    have hdeq := eq_smul_of_mul_eq_algebraMap hcz hc0 hk
    have h2 : a = (⅟2 : F) • (algebraMap F A c0 + (k / c) • orthProd Q (List.ofFn h)) := by
      rw [← hc0', ← hdeq,
        show a + b + (a - b) = (2 : F) • a by rw [two_smul]; abel, smul_smul, invOf_mul_self, one_smul]
    refine ⟨⅟2 * c0, ⅟2 * (k / c), ?_⟩
    rw [h2, smul_add, smul_smul, map_mul, Algebra.smul_def]
  · rintro ⟨c, d, rfl⟩ g hg
    have hzg : orthProd Q (List.ofFn h) * g = g * orthProd Q (List.ofFn h) := by
      induction g, hg using CliffordAlgebra.even_induction with
      | algebraMap r => exact (Algebra.commutes r _).symm
      | add x y hx hy ihx ihy => rw [mul_add, add_mul, ihx, ihy]
      | ι_mul_ι_mul m₁ m₂ x hx ih =>
        simp only [mul_assoc, hanti', neg_neg, mul_neg]
        rw [ih]
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hzg, Algebra.commutes]

end Center

end QuadFormsKB.Shimura2004
