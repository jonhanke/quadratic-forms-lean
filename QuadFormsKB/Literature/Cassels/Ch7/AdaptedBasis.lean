/-
# Cassels, Chapter 7, §3: a basis adapted to independent vectors

**Setting.** Cassels, *Rational Quadratic Forms*, Chapter 7, §3. Here $I$ is $\mathbb Z$ or $\mathbb Z_p$; in Lean the
ring is any principal ideal domain $R$ (a generalization), and a lattice is a free $R$-module $\Lambda$ with a basis
indexed by `Fin n`. Indices run over $0, \dots, n-1$ (Cassels: $1, \dots, n$); $n$ is the dimension.

**Proves**
* Lemma 3.4: if $\vec b_0, \dots, \vec b_{m-1}$ are linearly independent elements of a lattice $\Lambda$ of rank $n$,
  then $\Lambda$ has a basis $\vec e_0, \dots, \vec e_{n-1}$ such that $\vec b_j = \sum_{i \le j} c_{ij}\vec e_i$ with
  $c_{jj} \ne 0$ for each $j < m$ (`exists_basis_triangular`). Checked against the printed page (pp. 105–106) on 2026-10-27: a
  generalization (Cassels: $I$ a principal ideal domain, $\Lambda$ a lattice; here any principal ideal domain and any module with a basis).

**Proof notes.** Induction on the rank $n$ (in coordinates $R^n$, then transported to $\Lambda$). For the first
vector, Mathlib's Smith normal form of the rank one submodule $R\vec b_0$ gives a basis $g$ of $\Lambda$ with
$\vec b_0 = c\,g_0$, $c \ne 0$ (`exists_basis_smul_zero`). The remaining vectors are projected along $g_0$
onto $R^{n-1}$ (the coordinates $1, \dots, n-1$ with respect to $g$); the projections stay linearly independent; the
induction hypothesis gives an adapted basis of $R^{n-1}$, which is glued to $g_0$ (`exists_basis_cons`).
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

open Module Submodule

/-- If $v \ne 0$ lies in a free module $M$ with a basis of $n+1$ elements over a principal ideal domain, then $M$
has a basis $g_0, \dots, g_n$ with $v = c\,g_0$ for some scalar $c \ne 0$ (a nonzero vector is a nonzero multiple of a
primitive vector which extends to a basis). Proof: Smith normal form of the submodule spanned by $v$. -/
theorem exists_basis_smul_zero {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (B : Basis (Fin (n+1)) R M) {v : M} (hv : v ≠ 0) :
    ∃ (g : Basis (Fin (n+1)) R M) (c : R), c ≠ 0 ∧ v = c • g 0 := by
  obtain ⟨k, snf⟩ := Submodule.smithNormalForm B (R ∙ v)
  have hk : k = 1 := by
    have : Module.Free R M := Module.Free.of_basis B
    have h1 := Module.finrank_eq_card_basis snf.bN
    have h2 := finrank_span_eq_card (R := R) (b := fun _ : Unit => v)
      (linearIndependent_unique_iff.2 hv)
    rw [Set.range_const] at h2
    rw [h2] at h1
    simpa using h1.symm
  subst hk
  have hvN : v ∈ (R ∙ v) := mem_span_singleton_self v
  have hrepr : (⟨v, hvN⟩ : R ∙ v) = (snf.bN.repr ⟨v, hvN⟩ 0) • snf.bN 0 := by
    conv_lhs => rw [← snf.bN.sum_repr ⟨v, hvN⟩]
    simp
  set t := snf.bN.repr ⟨v, hvN⟩ 0
  have hvt : v = (t * snf.a 0) • snf.bM (snf.f 0) := by
    have := congrArg Subtype.val hrepr
    simp only [Submodule.coe_smul_of_tower, snf.snf] at this
    rw [smul_smul] at this; exact this
  have hta : t * snf.a 0 ≠ 0 := fun h => hv (by rw [hvt, h, zero_smul])
  refine ⟨snf.bM.reindex (Equiv.swap (snf.f 0) 0), t * snf.a 0, hta, ?_⟩
  simpa using hvt

/-- Gluing: given a basis $g_0, \dots, g_n$ of $M$ and a basis $e'$ of $R^n$, there is a basis $e$ of $M$ whose
coordinate $0$ is that of $g$ and whose coordinates $1, \dots, n$ are the coordinates of $e'$ applied to the vector
$(g\text{-coordinates } 1, \dots, n)$. -/
theorem exists_basis_cons {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (g : Basis (Fin (n+1)) R M) (e' : Basis (Fin n) R (Fin n → R)) :
    ∃ e : Basis (Fin (n+1)) R M, (∀ x, e.repr x 0 = g.repr x 0) ∧
      ∀ x i, e.repr x i.succ = e'.repr (fun k => g.repr x k.succ) i := by
  let Φ : M ≃ₗ[R] R × (Fin n → R) :=
    g.equivFun.trans (Fin.consLinearEquiv R (fun _ : Fin (n+1) => R)).symm
  have hΦ : ∀ x, Φ x = (g.repr x 0, fun k => g.repr x k.succ) := by
    intro x; rfl
  let P : Basis (PUnit.{1} ⊕ Fin n) R (R × (Fin n → R)) := (Basis.singleton PUnit.{1} R).prod e'
  let eqv : Fin (n+1) ≃ PUnit.{1} ⊕ Fin n :=
    (finSuccEquiv n).trans ((Equiv.optionEquivSumPUnit _).trans (Equiv.sumComm _ _))
  have h0 : eqv 0 = Sum.inl PUnit.unit.{1} := rfl
  have hs : ∀ i, eqv i.succ = Sum.inr i := fun i => by simp [eqv]
  refine ⟨(P.map Φ.symm).reindex eqv.symm, ?_, ?_⟩
  · intro x
    simp [h0, hΦ, P]
  · intro x i
    simp [hs, hΦ, P]

/-- Coordinate version of Lemma 3.4 (induction on the rank). -/
theorem exists_basis_triangular_pi {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    ∀ (n m : ℕ) (hmn : m ≤ n) (b : Fin m → (Fin n → R)), LinearIndependent R b →
      ∃ e : Basis (Fin n) R (Fin n → R), ∀ j : Fin m,
        e.repr (b j) (Fin.castLE hmn j) ≠ 0 ∧ ∀ i : Fin n, (j : ℕ) < i → e.repr (b j) i = 0 := by
  intro n
  induction n with
  | zero =>
    intro m hmn b _
    have : m = 0 := Nat.le_zero.1 hmn
    subst this
    exact ⟨Pi.basisFun R (Fin 0), fun j => j.elim0⟩
  | succ n ih =>
    intro m hmn b hb
    cases m with
    | zero => exact ⟨Pi.basisFun R (Fin (n+1)), fun j => j.elim0⟩
    | succ m =>
      have hmn' : m ≤ n := Nat.le_of_succ_le_succ hmn
      obtain ⟨g, c, hc, hbc⟩ := exists_basis_smul_zero (Pi.basisFun R (Fin (n+1)))
        (hb.ne_zero 0)
      let π : (Fin (n+1) → R) →ₗ[R] (Fin n → R) := LinearMap.pi fun k => g.coord k.succ
      have hπ : ∀ x k, π x k = g.repr x k.succ := fun x k => rfl
      have hπ0 : π (b 0) = 0 := by
        ext k
        rw [hπ, hbc]
        simp
      have hind : LinearIndependent R (fun j : Fin m => π (b j.succ)) := by
        rw [Fintype.linearIndependent_iff] at hb ⊢
        intro a ha
        set y : Fin (n+1) → R := ∑ j, a j • b j.succ with hy
        have hπy : π y = 0 := by
          rw [hy, map_sum]
          simpa using ha
        have hyg : y = (g.repr y 0) • g 0 := by
          apply g.ext_elem
          intro i
          refine Fin.cases ?_ (fun k => ?_) i
          · simp
          · have : g.repr y k.succ = 0 := by rw [← hπ, hπy]; rfl
            simp [this]
        have hsum : ∑ i, (Fin.cons (-(g.repr y 0)) (fun j => c * a j) : Fin (m+1) → R) i • b i = 0 := by
          have hcy : c • y = (g.repr y 0) • b 0 := by
            rw [hbc, smul_smul, mul_comm, mul_smul, ← hyg]
          have hs2 : ∑ j, (c * a j) • b j.succ = c • y := by
            rw [hy, Finset.smul_sum]
            simp [mul_smul]
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hs2, hcy, neg_smul]
          exact neg_add_cancel _
        intro j
        have := hb _ hsum j.succ
        simpa [hc] using this
      obtain ⟨e', he'⟩ := ih m hmn' _ hind
      obtain ⟨e, he0, hes⟩ := exists_basis_cons g e'
      refine ⟨e, fun j => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) j
      · have hc0 : Fin.castLE hmn (0 : Fin (m+1)) = 0 := rfl
        refine ⟨?_, fun i hi => ?_⟩
        · rw [hc0, he0, hbc]
          simpa using hc
        · induction i using Fin.cases with
          | zero => simp at hi
          | succ i =>
            rw [hes]
            have : (fun k : Fin n => g.repr (b 0) k.succ) = 0 := by
              funext k; rw [← hπ, hπ0]
            rw [this]; simp
      · have hcs : Fin.castLE hmn j.succ = (Fin.castLE hmn' j).succ := by
          ext; simp
        refine ⟨?_, fun i hi => ?_⟩
        · rw [hcs, hes]
          exact (he' j).1
        · induction i using Fin.cases with
          | zero => simp at hi
          | succ i =>
            rw [hes]
            exact (he' j).2 i (by simpa using hi)

/-- **Cassels, Ch. 7, Lemma 3.4**: *let $\Lambda$ be a lattice of rank $n$ and let
$\vec b_0, \dots, \vec b_{m-1} \in \Lambda$ be linearly independent (so $m \le n$); then $\Lambda$ has a basis
$\vec e_0, \dots, \vec e_{n-1}$ such that $\vec b_j = \sum_{i \le j} c_{ij}\vec e_i$ with $c_{jj} \ne 0$ for
$j = 0, \dots, m-1$.* Generalization: $R$ is any principal ideal domain (Cassels: $\mathbb Z$ or $\mathbb Z_p$), and
$\Lambda$ is any $R$-module with a basis `B` of $n$ elements. The coefficients $c_{ij}$ are the coordinates
`e.repr (b j) i`; the statement says that $c_{jj} \ne 0$ (the coordinate of $\vec b_j$ at the index $j$, which is
`Fin.castLE hmn j` as an element of `Fin n`) and that $c_{ij} = 0$ for $i > j$. Indices are 0-based. Checked against the printed page
(pp. 105–106) on 2026-10-27: a generalization of the printed lemma (see above); the conclusion is the same. -/
@[kb "cassels1978" "Ch. 7, Lemma 3.4, p. 105"]
theorem exists_basis_triangular {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] {n m : ℕ} (B : Basis (Fin n) R M) (hmn : m ≤ n)
    (b : Fin m → M) (hb : LinearIndependent R b) :
    ∃ e : Basis (Fin n) R M, ∀ j : Fin m,
      e.repr (b j) (Fin.castLE hmn j) ≠ 0 ∧ ∀ i : Fin n, (j : ℕ) < i → e.repr (b j) i = 0 := by
  have hb' : LinearIndependent R (fun j => B.equivFun (b j)) :=
    hb.map' B.equivFun.toLinearMap (LinearMap.ker_eq_bot.2 B.equivFun.injective)
  obtain ⟨e', he'⟩ := exists_basis_triangular_pi n m hmn _ hb'
  refine ⟨e'.map B.equivFun.symm, fun j => ?_⟩
  simpa using he' j

end QuadFormsKB.Cassels
