/-
# Cassels, Chapter 6, Example 7: finite groups of proper rational automorphs

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 6, *Examples*, Ex. 7, p. 101.

**Statement (`ex7`).** A finite group $G$ of proper rational automorphs of a regular rational quadratic form $f$ in $n$
variables has order dividing $g(n) = \prod_q q^{\gamma_q(n)}$ (`gCassels`, `gamma`). Here $f$ is a `RatQF n`
(`QuadForm ℚ n`), regular means `Nondegenerate`, and $G$ is a finite `Subgroup (GL (Fin n) ℚ)` of matrices $T$ with
$f(T\vec x) = f(\vec x)$ for all $\vec x \in \mathbb Q^n$ and $\det T = 1$. Indices are $0$-based ($\vec x = (x_0,
\dots, x_{n-1})$).

**Proof.** Unconditional, following Cassels' hint (apply the hint of Ch. 3, Ex. 16 to Ch. 2, Ex. 13), except that Ch. 3,
Ex. 16 itself is not used (it is not formalized); its Dirichlet step is redone here with Mathlib's Dirichlet theorem
`Nat.forall_exists_prime_gt_and_eq_mod`:
* `integral_model_gl`: a finite subgroup of $\mathrm{GL}_n(\mathbb Q)$ stabilizes a lattice (the span of its orbit of the
  standard basis), so it is conjugate to a group of integer matrices preserving an integral symmetric matrix $S$;
* `card_dvd_card_orthPlus`: for an odd prime $p \nmid \det S$ reduction modulo $p$ is injective on $G$ (Ch. 3, Ex. 14 (i),
  `ex14_i`) and lands in $O^{+}(\bar S)$ over $\mathbb F_p$;
* `divData`: its order, by Ch. 2, Ex. 13 (vi) (`ex13_vi_odd`, `ex13_vi_even`), divides $p^{m^2}\prod_{i=1}^{m}(p^{2i}-1)$
  ($n = 2m$ or $2m+1$; for even $n$ even after multiplying by $2$);
* `val_card_le`: choosing $p$ by Dirichlet's theorem ($p \equiv 3 \pmod 8$ for $q = 2$; a primitive root modulo $q^2$
  for odd $q$), the $q$-adic valuation of that product is at most $\gamma_q(n)$ (lifting the exponent).

**The formula (read from the page image).** The formulas for $\gamma_q(n)$ are garbled in the machine-read text of
p. 101; the page image gives $\gamma(2) = n - 1 + [n/2] + [n/2^2] + \cdots$ and
$\gamma(q) = [n/(q-1)] + [n/q(q-1)] + [n/q^2(q-1)] + \cdots$ ($q > 2$), which are the formulas proved here. For $q = 2$
this is the exponent of $2$ in $2^n n!$ (the Minkowski bound) minus $1$ for the determinant condition; it improves the
direct use of Ch. 3, Ex. 16 (whose $2$-exponent is $n + 2\lfloor n/2\rfloor + \lfloor n/4\rfloor + \cdots$). The bound is
sharp for $q = 2$ (signed permutation matrices of determinant $1$ preserving $\sum x_i^2$).
-/
import QuadFormsKB.Literature.Cassels.Ch2.Ex13Counts
import QuadFormsKB.Literature.Cassels.Ch3.Exercises
import QuadFormsKB.Equiv.RationalGram

set_option linter.unusedSectionVars false

open Matrix Module

namespace QuadFormsKB.Cassels.Ch6Ex7

section Lattice

variable {n : ℕ}

/-- Helper: the space $\mathbb Q^n$ of column vectors (`Fin n → ℚ`), $n$ the number of variables. -/
abbrev Vec (n : ℕ) := Fin n → ℚ

/-- Helper: a $\mathbb Z$-basis `b` of a lattice `L` $\subseteq \mathbb Q^n$ containing the standard basis vectors (`hL`) is also a $\mathbb Q$-basis of $\mathbb Q^n$ with the same vectors. -/
lemma qbasis_of_lattice {ι : Type*} [Fintype ι] (L : Submodule ℤ (Vec n)) (b : Basis ι ℤ L)
    (hL : ∀ i, (Pi.single i 1 : Vec n) ∈ L) :
    ∃ bq : Basis ι ℚ (Vec n), ∀ j, bq j = (b j : Vec n) := by
  have hli : LinearIndependent ℤ (fun j => (b j : Vec n)) :=
    b.linearIndependent.map' L.subtype (by simp)
  have hliQ : LinearIndependent ℚ (fun j => (b j : Vec n)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hspan : ⊤ ≤ Submodule.span ℚ (Set.range fun j => (b j : Vec n)) := by
    rw [← (Pi.basisFun ℚ (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi := hL i
    have hsum := b.sum_repr ⟨_, hi⟩
    have := congrArg Subtype.val hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [Pi.basisFun_apply]
    rw [← this]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact ⟨Basis.mk hliQ hspan, fun j => by simp⟩

/-- Helper: the $\mathbb Z$-span of the images $g e_i$ of the standard basis vectors under all elements $g$ of the subgroup `G` of $\mathrm{GL}(\mathbb Q^n)$. -/
def stabLattice (G : Subgroup (Vec n ≃ₗ[ℚ] Vec n)) : Submodule ℤ (Vec n) :=
  Submodule.span ℤ {v | ∃ g ∈ G, ∃ i, v = g (Pi.single i 1)}

/-- Helper: the standard basis vector $e_i$ (`i`) lies in `stabLattice G`. -/
lemma stabLattice_mem_single (G : Subgroup (Vec n ≃ₗ[ℚ] Vec n)) (i : Fin n) :
    (Pi.single i 1 : Vec n) ∈ stabLattice G :=
  Submodule.subset_span ⟨1, G.one_mem, i, by simp⟩

/-- Helper: `stabLattice G` is stable under every `g` $\in$ `G` (`hg`): $g v \in$ `stabLattice G` for $v$ in it (`hv`). -/
lemma stabLattice_map (G : Subgroup (Vec n ≃ₗ[ℚ] Vec n)) (g : Vec n ≃ₗ[ℚ] Vec n) (hg : g ∈ G)
    (v : Vec n) (hv : v ∈ stabLattice G) : g v ∈ stabLattice G := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hh, i, rfl⟩ := hx
    exact Submodule.subset_span ⟨g * h, G.mul_mem hg hh, i, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ _ hx

/-- Helper: for a finite group `G`, `stabLattice G` is finitely generated. -/
lemma stabLattice_fg (G : Subgroup (Vec n ≃ₗ[ℚ] Vec n)) [Finite G] : (stabLattice G).FG := by
  apply Submodule.fg_span
  refine (Set.finite_range (fun p : G × Fin n =>
    (p.1 : Vec n ≃ₗ[ℚ] Vec n) (Pi.single p.2 1))).subset ?_
  rintro _ ⟨g, hg, i, rfl⟩
  exact ⟨(⟨g, hg⟩, i), rfl⟩

/-- Helper: **integral model.** Let `B` be a symmetric nondegenerate bilinear form on $\mathbb Q^n$ and `G` a finite group of linear automorphisms preserving `B` (`hG`). In a $\mathbb Z$-basis of the `G`-stable lattice `stabLattice G`, `G` acts by integer matrices `ρ g` (an injective homomorphism), and $B$ has a (scaled) integral symmetric Gram matrix `S` with $\det S \ne 0$, $\rho(g)^{\mathsf T} S \rho(g) = S$, and $\det\rho(g)$ equal to the determinant of `g`. -/
theorem integral_model (B : LinearMap.BilinForm ℚ (Vec n)) (hsymm : ∀ x y, B x y = B y x)
    (hB : B.Nondegenerate) (G : Subgroup (Vec n ≃ₗ[ℚ] Vec n)) [Finite G]
    (hG : ∀ g ∈ G, ∀ x y, B (g x) (g y) = B x y) :
    ∃ (ρ : G →* Matrix (Fin n) (Fin n) ℤ) (S : Matrix (Fin n) (Fin n) ℤ),
      Function.Injective ρ ∧ Sᵀ = S ∧ S.det ≠ 0 ∧ (∀ g, (ρ g)ᵀ * S * ρ g = S) ∧
      (∀ g : G, (((ρ g).det : ℤ) : ℚ) =
        LinearMap.det ((g : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n)) := by
  set L := stabLattice G with hLdef
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr (stabLattice_fg G)
  let b0 := Module.Free.chooseBasis ℤ L
  obtain ⟨bq0, hbq0⟩ := qbasis_of_lattice L b0 (stabLattice_mem_single G)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = n := by
    have := Module.finrank_eq_card_basis bq0
    simpa using this.symm
  let e := Fintype.equivFinOfCardEq hcard
  let b : Basis (Fin n) ℤ L := b0.reindex e
  obtain ⟨bq, hbq⟩ := qbasis_of_lattice L b (stabLattice_mem_single G)
  let act : G →* (L →ₗ[ℤ] L) :=
    { toFun := fun g => ((g.1 : Vec n ≃ₗ[ℚ] Vec n).toLinearMap.restrictScalars ℤ).restrict
        (fun v hv => stabLattice_map G g.1 g.2 v hv)
      map_one' := LinearMap.ext fun v => Subtype.ext rfl
      map_mul' := fun g h => LinearMap.ext fun v => Subtype.ext rfl }
  let ρ : G →* Matrix (Fin n) (Fin n) ℤ :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom.comp act
  have hact : ∀ g v, ((act g v : L) : Vec n) = (g : Vec n ≃ₗ[ℚ] Vec n) (v : Vec n) :=
    fun g v => rfl
  have hρ : ∀ (g : G) k j, ρ g k j = b.repr (act g (b j)) k := fun g k j => by
    simp only [ρ, MonoidHom.comp_apply]
    exact LinearMap.toMatrix_apply b b (act g) k j
  have hrel : ∀ (g : G) j, (g : Vec n ≃ₗ[ℚ] Vec n) (bq j) =
      ∑ k, ((ρ g k j : ℤ) : ℚ) • bq k := by
    intro g j
    have h1 := congrArg Subtype.val (b.sum_repr (act g (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, hact] at h1
    rw [hbq j, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hbq k, hρ g k j]
    exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
  have hmat : ∀ g : G, LinearMap.toMatrix bq bq ((g : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n) =
      (ρ g).map (Int.cast : ℤ → ℚ) := by
    intro g
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [LinearEquiv.coe_coe]
    rw [hrel g j, Basis.repr_sum_self]
    rfl
  have hN : ∃ N : ℕ, 0 < N ∧ ∀ i j, ∃ z : ℤ, (z : ℚ) = N * B (bq i) (bq j) := by
    refine ⟨∏ p : Fin n × Fin n, (B (bq p.1) (bq p.2)).den,
      Finset.prod_pos fun p _ => Rat.den_pos _, ?_⟩
    intro i j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
      (fun p : Fin n × Fin n => (B (bq p.1) (bq p.2)).den) (Finset.mem_univ (i, j))
    refine ⟨c * (B (bq i) (bq j)).num, ?_⟩
    rw [hc]
    have := Rat.mul_den_eq_num (B (bq i) (bq j))
    push_cast
    rw [← this]
    ring
  obtain ⟨N, hNpos, hNz⟩ := hN
  choose z hz using hNz
  let S : Matrix (Fin n) (Fin n) ℤ := Matrix.of z
  have hSmap : S.map (Int.cast : ℤ → ℚ) = (N : ℚ) • LinearMap.BilinForm.toMatrix bq B := by
    ext i j
    simp [S, hz]
  have hGramdet : (LinearMap.BilinForm.toMatrix bq B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bq).mp hB
  refine ⟨ρ, S, ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ∀ i, ((g : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n) (bq i) =
        (LinearMap.id : Vec n →ₗ[ℚ] Vec n) (bq i) := by
      intro i
      have := hrel g i
      rw [hg] at this
      simpa [Matrix.one_apply] using this
    have h2 : ((g : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n) =
        (LinearMap.id : Vec n →ₗ[ℚ] Vec n) := bq.ext h1
    exact Subtype.ext (LinearEquiv.ext fun x => LinearMap.congr_fun h2 x)
  · ext i j
    have h1 := hsymm (bq i) (bq j)
    have h2 : ((S i j : ℤ) : ℚ) = ((S j i : ℤ) : ℚ) := by
      simp only [S, Matrix.of_apply, hz, h1]
    rw [Matrix.transpose_apply]
    exact_mod_cast h2.symm
  · intro h0
    have h1 : ((S.det : ℤ) : ℚ) = 0 := by exact_mod_cast h0
    have h2 : ((S.det : ℤ) : ℚ) = (S.map (Int.cast : ℤ → ℚ)).det :=
      (RingHom.map_det (Int.castRingHom ℚ) S)
    rw [h2, hSmap, Matrix.det_smul, Fintype.card_fin] at h1
    exact (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hNpos.ne')) hGramdet) h1
  · intro g
    have hBg : B.comp ((g : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n)
        ((g : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n) = B :=
      LinearMap.ext fun x => LinearMap.ext fun y => hG g.1 g.2 x y
    have hc := LinearMap.BilinForm.toMatrix_comp bq bq B
      ((g : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n) ((g : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n)
    rw [hBg, hmat g] at hc
    have e1 : ((ρ g)ᵀ * S * ρ g).map (Int.cast : ℤ → ℚ) =
        ((ρ g).map (Int.cast : ℤ → ℚ))ᵀ * S.map (Int.cast : ℤ → ℚ) * (ρ g).map (Int.cast : ℤ → ℚ) := by
      change ((ρ g)ᵀ * S * ρ g).map (Int.castRingHom ℚ) =
        ((ρ g).map (Int.castRingHom ℚ))ᵀ * S.map (Int.castRingHom ℚ) * (ρ g).map (Int.castRingHom ℚ)
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    have key : ((ρ g)ᵀ * S * ρ g).map (Int.cast : ℤ → ℚ) = S.map (Int.cast : ℤ → ℚ) := by
      rw [e1, hSmap, Matrix.mul_smul, Matrix.smul_mul, ← hc]
    exact Matrix.map_injective (Int.cast_injective (α := ℚ)) key
  · intro g
    rw [← LinearMap.det_toMatrix bq, hmat g]
    exact RingHom.map_det (Int.castRingHom ℚ) (ρ g)

/-- Helper: $\mathrm{GL}_n(\mathbb Q)$ (invertible matrices over `ℚ`, `n` variables) as the group of linear automorphisms of $\mathbb Q^n$. -/
def eGL (n : ℕ) : GL (Fin n) ℚ ≃* (Vec n ≃ₗ[ℚ] Vec n) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

/-- Helper: `eGL n T` acts on a vector `x` by the matrix product $T x$. -/
lemma eGL_apply {n : ℕ} (T : GL (Fin n) ℚ) (x : Vec n) : eGL n T x = (T : Matrix (Fin n) (Fin n) ℚ) *ᵥ x := rfl

/-- Helper: **integral model for a finite subgroup of $\mathrm{GL}_n(\mathbb Q)$.** If `G` is a finite subgroup of $\mathrm{GL}_n(\mathbb Q)$ with $T^{\mathsf T} A T = A$ for all $T \in G$ (`hG`; `A` a symmetric matrix with nonzero determinant) and $\det T = 1$ (`hdetG`), then `G` embeds as a group of integer matrices of determinant $1$ preserving an integral symmetric matrix `S` of nonzero determinant (`ρ` the embedding). -/
theorem integral_model_gl (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (G : Subgroup (GL (Fin n) ℚ)) [Finite G]
    (hG : ∀ T ∈ G, (T : Matrix (Fin n) (Fin n) ℚ)ᵀ * A * (T : Matrix (Fin n) (Fin n) ℚ) = A)
    (hdetG : ∀ T ∈ G, (T : Matrix (Fin n) (Fin n) ℚ).det = 1) :
    ∃ (ρ : G →* Matrix (Fin n) (Fin n) ℤ) (S : Matrix (Fin n) (Fin n) ℤ),
      Function.Injective ρ ∧ Sᵀ = S ∧ S.det ≠ 0 ∧ (∀ g, (ρ g)ᵀ * S * ρ g = S) ∧
      (∀ g, (ρ g).det = 1) := by
  let B : LinearMap.BilinForm ℚ (Vec n) := Matrix.toLinearMap₂' ℚ A
  have hBapp : ∀ x y, B x y = x ⬝ᵥ (A *ᵥ y) := fun x y => by
    simp [B, Matrix.toLinearMap₂'_apply']
  have hsymm : ∀ x y, B x y = B y x := by
    intro x y
    rw [hBapp, hBapp, dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]
  have hB : B.Nondegenerate := (LinearMap.nondegenerate_toLinearMap₂'_iff_det_ne_zero (M := A)).mpr hdet
  let H : Subgroup (Vec n ≃ₗ[ℚ] Vec n) := G.map (eGL n).toMonoidHom
  have : Finite H := by
    have : Finite G := inferInstance
    exact Finite.of_surjective (fun g : G => (⟨eGL n g.1, g.1, g.2, rfl⟩ : H)) (by
      rintro ⟨_, g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩)
  have hGH : ∀ g ∈ H, ∀ x y, B (g x) (g y) = B x y := by
    rintro _ ⟨T, hT, rfl⟩ x y
    simp only [MulEquiv.coe_toMonoidHom, eGL_apply]
    rw [hBapp, hBapp]
    have key : (T.val *ᵥ x) ⬝ᵥ (A *ᵥ (T.val *ᵥ y)) = x ⬝ᵥ ((T.valᵀ * A * T.val) *ᵥ y) := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec x T.valᵀ, Matrix.vecMul_transpose]
    rw [key, hG T hT]
  obtain ⟨ρH, S, hinj, hS, hSd, hSρ, hdetρ⟩ := integral_model B hsymm hB H hGH
  let iso : G ≃* H := (eGL n).subgroupMap G
  refine ⟨ρH.comp iso.toMonoidHom, S, hinj.comp iso.injective, hS, hSd, fun g => hSρ _, fun g => ?_⟩
  have h1 := hdetρ (iso g)
  have h2 : LinearMap.det (((iso g : H) : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n) =
      (g.1 : Matrix (Fin n) (Fin n) ℚ).det := by
    have : (((iso g : H) : Vec n ≃ₗ[ℚ] Vec n) : Vec n →ₗ[ℚ] Vec n) =
        Matrix.toLin' (g.1 : Matrix (Fin n) (Fin n) ℚ) := LinearMap.ext fun x => by
      rw [Matrix.toLin'_apply]; rfl
    rw [this, LinearMap.det_toLin']
  rw [h2, hdetG g.1 g.2] at h1
  exact_mod_cast h1

end Lattice


section Reduction

open QuadFormsKB.OMeara

variable {n : ℕ}

/-- Helper: reduction modulo the prime `p` of integer $n \times n$ matrices, as a ring homomorphism. -/
def red (p : ℕ) : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) (ZMod p) :=
  (Int.castRingHom (ZMod p)).mapMatrix

/-- Helper: **kernel of reduction (via Ch. 3, Ex. 14 (i)).** For an odd prime `p` (`hp2`), an integer matrix `A` $\ne I$ (`hA`) with $A \equiv I \pmod p$ (`h1`) has $A^k \ne I$ for all $k \ge 1$ (`hk`). -/
lemma pow_ne_one_of_red (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A ≠ 1) (h1 : red p A = 1) (k : ℕ) (hk : 1 ≤ k) : A ^ k ≠ 1 := by
  intro hk1
  let φ : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℤ_[p] :=
    (Int.castRingHom ℤ_[p]).mapMatrix
  have hne : φ A ≠ 1 := by
    intro h
    apply hA
    have h' : φ A = φ 1 := h.trans (map_one φ).symm
    exact Matrix.map_injective (Int.cast_injective (α := ℤ_[p])) h'
  have hdiv : ∀ i j, ((p : ℕ) : ℤ_[p]) ∣ (φ A - 1) i j := by
    intro i j
    have h2 : ((A i j : ℤ) : ZMod p) = (1 : Matrix (Fin n) (Fin n) (ZMod p)) i j :=
      congrFun (congrFun h1 i) j
    have h3 : (((A - 1) i j : ℤ) : ZMod p) = 0 := by
      simp only [Matrix.sub_apply]
      push_cast
      rw [sub_eq_zero]
      by_cases hij : i = j
      · subst hij
        simpa using h2
      · simpa [Matrix.one_apply, hij] using h2
    obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h3
    refine ⟨(c : ℤ_[p]), ?_⟩
    have : (φ A - 1) i j = (((A - 1) i j : ℤ) : ℤ_[p]) := by
      simp only [φ, RingHom.mapMatrix_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
    rw [this, hc]
    push_cast
    rfl
  apply QuadFormsKB.Cassels.Ch3Ex.ex14_i hp2 hdiv hne k hk
  rw [← map_pow, hk1, map_one]

/-- Helper: if `ρ` embeds a finite group `G` in integer matrices (`hρ`) and `p` is odd (`hp2`), then an element `g` whose image is $\equiv I \pmod p$ (`hg`) is the identity. -/
lemma eq_one_of_red_eq_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (ρ : G →* Matrix (Fin n) (Fin n) ℤ) (hρ : Function.Injective ρ) (g : G)
    (hg : red p (ρ g) = 1) : g = 1 := by
  by_contra hne
  have hA : ρ g ≠ 1 := fun h => hne (hρ (by rw [h, map_one]))
  exact pow_ne_one_of_red p hp2 (ρ g) hA hg (orderOf g) (orderOf_pos g)
    (by rw [← map_pow, pow_orderOf_eq_one, map_one])

section Form

variable (p : ℕ) [Fact p.Prime]

/-- Helper: the quadratic form $x \mapsto x^{\mathsf T}\bar S x$ over $\mathbb F_p$ (`ZMod p`) given by the reduction modulo `p` of the integer matrix `S`. -/
def redForm (S : Matrix (Fin n) (Fin n) ℤ) : QuadraticForm (ZMod p) (Fin n → ZMod p) :=
  Matrix.toQuadraticForm' (red p S)

/-- Helper: the value of `redForm p S` at `x` is $x^{\mathsf T}\bar S x$. -/
lemma redForm_apply (S : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod p) :
    redForm p S x = x ⬝ᵥ (red p S) *ᵥ x := by
  rw [redForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

/-- Helper: reduction modulo `p` commutes with transposition of `S`. -/
lemma red_transpose (S : Matrix (Fin n) (Fin n) ℤ) : red p Sᵀ = (red p S)ᵀ := by
  ext i j; rfl

variable [Invertible (2 : ZMod p)]

/-- Helper: for symmetric `S` (`hS`) and odd `p`, the associated bilinear form of `redForm p S` is $(x, y) \mapsto x^{\mathsf T}\bar S y$. -/
lemma redForm_associated (S : Matrix (Fin n) (Fin n) ℤ) (hS : Sᵀ = S) (x y : Fin n → ZMod p) :
    QuadraticMap.associated (R := ZMod p) (redForm p S) x y = x ⬝ᵥ (red p S) *ᵥ y := by
  have hS' : (red p S)ᵀ = red p S := by
    rw [← red_transpose, hS]
  rw [QuadraticMap.associated_apply]
  simp only [redForm_apply, dotProduct_add, add_dotProduct, Matrix.mulVec_add]
  have h1 : y ⬝ᵥ (red p S) *ᵥ x = x ⬝ᵥ (red p S) *ᵥ y := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hS', dotProduct_comm]
  rw [h1]
  have : x ⬝ᵥ (red p S) *ᵥ x + x ⬝ᵥ (red p S) *ᵥ y + (x ⬝ᵥ (red p S) *ᵥ y + y ⬝ᵥ (red p S) *ᵥ y) -
      x ⬝ᵥ (red p S) *ᵥ x - y ⬝ᵥ (red p S) *ᵥ y = 2 * (x ⬝ᵥ (red p S) *ᵥ y) := by
    ring
  rw [this]
  change ⅟(2 : ZMod p) * (2 * _) = _
  rw [← mul_assoc, invOf_mul_self, one_mul]

/-- Helper: the associated bilinear form of `redForm p S` is `Matrix.toLinearMap₂'` of $\bar S$ (symmetric `S`, `hS`). -/
lemma redForm_associated_eq (S : Matrix (Fin n) (Fin n) ℤ) (hS : Sᵀ = S) :
    QuadraticMap.associated (R := ZMod p) (redForm p S) =
      Matrix.toLinearMap₂' (ZMod p) (red p S) := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [redForm_associated p S hS, Matrix.toLinearMap₂'_apply']

/-- Helper: if `S` is symmetric (`hS`) and `p` does not divide $\det S$ (`hp`), then `redForm p S` is regular (nondegenerate associated bilinear form) over $\mathbb F_p$. -/
lemma redForm_nondegenerate (S : Matrix (Fin n) (Fin n) ℤ) (hS : Sᵀ = S) (hp : ¬ (p : ℤ) ∣ S.det) :
    (QuadraticMap.associated (R := ZMod p) (redForm p S)).Nondegenerate := by
  rw [redForm_associated_eq p S hS, LinearMap.nondegenerate_toLinearMap₂'_iff_det_ne_zero]
  intro h0
  apply hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have : (red p S).det = ((S.det : ℤ) : ZMod p) := by
    exact (RingHom.map_det (Int.castRingHom (ZMod p)) S).symm
  rw [← this]; exact h0

/-- Helper: if `S` is symmetric (`hS`) and `p` does not divide $\det S$ (`hp`), the determinant `discr'` of `redForm p S` is nonzero. -/
lemma redForm_discr_ne_zero (S : Matrix (Fin n) (Fin n) ℤ) (hS : Sᵀ = S) (hp : ¬ (p : ℤ) ∣ S.det) :
    (redForm p S).discr' ≠ 0 := by
  have h : (redForm p S).discr' = (red p S).det := by
    rw [QuadraticForm.discr', QuadraticForm.toMatrix', redForm_associated_eq p S hS]
    congr 1
    exact (LinearMap.toMatrix₂' (ZMod p)).apply_symm_apply _
  rw [h]
  intro h0
  apply hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have : (red p S).det = ((S.det : ℤ) : ZMod p) := by
    exact (RingHom.map_det (Int.castRingHom (ZMod p)) S).symm
  rw [← this]; exact h0

/-- Helper: the group of invertible $n \times n$ matrices over $\mathbb F_p$ as the group of linear automorphisms of $\mathbb F_p^n$. -/
def glEquiv : (Matrix (Fin n) (Fin n) (ZMod p))ˣ ≃* ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

/-- Helper: **reduction step.** Let `S` be a symmetric integer matrix (`hS`) with $p \nmid \det S$ (`hp`), `p` an odd prime (`hp2`), and `ρ` an injective homomorphism (`hρ`) of a finite group `G` into integer matrices of determinant $1$ (`hdet`) preserving `S` (`hAS`). Then $|G|$ divides the order of the group $O^{+}$ of proper automorphs of the regular form $\bar S$ over $\mathbb F_p$ (`orthPlus (redForm p S)`). -/
theorem card_dvd_card_orthPlus (S : Matrix (Fin n) (Fin n) ℤ) (hS : Sᵀ = S)
    (hp : ¬ (p : ℤ) ∣ S.det) (hp2 : p ≠ 2) {G : Type*} [Group G] [Finite G]
    (ρ : G →* Matrix (Fin n) (Fin n) ℤ) (hρ : Function.Injective ρ)
    (hAS : ∀ g, (ρ g)ᵀ * S * ρ g = S) (hdet : ∀ g, (ρ g).det = 1) :
    Nat.card G ∣ Nat.card (orthPlus (redForm p S)) := by
  let φ : G →* (Matrix (Fin n) (Fin n) (ZMod p))ˣ :=
    MonoidHom.toHomUnits ((red p).toMonoidHom.comp ρ)
  let ψ : G →* ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) := (glEquiv p).toMonoidHom.comp φ
  have hφ : ∀ g, ((φ g : (Matrix (Fin n) (Fin n) (ZMod p))ˣ) : Matrix (Fin n) (Fin n) (ZMod p)) =
      red p (ρ g) := fun g => rfl
  have hψ : ∀ g x, ψ g x = red p (ρ g) *ᵥ x := fun g x => rfl
  have hmem : ∀ g, ψ g ∈ orthPlus (redForm p S) := by
    intro g
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · intro x
      rw [hψ, redForm_apply, redForm_apply]
      have hMS : (red p (ρ g))ᵀ * red p S * red p (ρ g) = red p S := by
        rw [← red_transpose, ← map_mul, ← map_mul, hAS]
      conv_rhs => rw [← hMS]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      conv_rhs => rw [dotProduct_mulVec, Matrix.vecMul_transpose]
    · rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [LinearEquiv.coe_det]
      have h1 : ((ψ g : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) :
          (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p)) = Matrix.toLin' (red p (ρ g)) :=
        LinearMap.ext fun x => by rw [Matrix.toLin'_apply]; exact hψ g x
      rw [h1, LinearMap.det_toLin']
      have h2 : (red p (ρ g)).det = (((ρ g).det : ℤ) : ZMod p) :=
        (RingHom.map_det (Int.castRingHom (ZMod p)) (ρ g)).symm
      rw [h2, hdet g]
      simp
  let ψ' : G →* orthPlus (redForm p S) := ψ.codRestrict _ hmem
  have hinj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : ψ g = 1 := congrArg Subtype.val hg
    have h2 : φ g = 1 := (glEquiv p).injective (by rw [map_one]; exact h1)
    have h3 : red p (ρ g) = 1 := by
      rw [← hφ g, h2]; rfl
    exact eq_one_of_red_eq_one p hp2 ρ hρ g h3
  exact Subgroup.card_dvd_of_injective ψ' hinj

end Form

end Reduction


section NT
open Finset


section Odd

variable (q p : ℕ) [hq : Fact q.Prime]

/-- Helper: for an odd prime `q`, a prime-to-`q` base `p` with $p^{q-1} \not\equiv 1 \pmod{q^2}$ (`c2`) and $q \mid p^j - 1 \Rightarrow (q-1) \mid j$ (`c1`), the $q$-adic valuation of $p^{2i} - 1$ is $1 + v_q(i/h)$ if $h = (q-1)/2$ divides `i`, and $0$ otherwise. -/
lemma val_odd (hq2 : q ≠ 2) (hpq : ¬ q ∣ p)
    (c2 : ¬ q ^ 2 ∣ p ^ (q - 1) - 1) (hp1 : 1 < p)
    (c1 : ∀ j, q ∣ p ^ j - 1 → (q - 1) ∣ j)
    (i : ℕ) (hi : 0 < i) :
    padicValNat q (p ^ (2 * i) - 1) =
      if (q - 1) / 2 ∣ i then 1 + padicValNat q (i / ((q - 1) / 2)) else 0 := by
  have hqodd : Odd q := hq.out.odd_of_ne_two hq2
  have hq3 : 3 ≤ q := by
    have := hq.out.two_le
    rcases Nat.lt_or_ge q 3 with h | h
    · omega
    · exact h
  obtain ⟨h, hh⟩ : ∃ h, q - 1 = 2 * h := by
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k, by omega⟩
  have hhpos : 0 < h := by omega
  have hdiv2 : (q - 1) / 2 = h := by omega
  rw [hdiv2]
  split_ifs with hdiv
  · obtain ⟨s, hs⟩ := hdiv
    have hspos : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · rw [h0] at hs; omega
      · exact h0
    have hfermat : q ∣ p ^ (q - 1) - 1 := by
      have hp0 : (p : ZMod q) ≠ 0 := by
        rwa [Ne, ZMod.natCast_eq_zero_iff]
      have h1 := ZMod.pow_card_sub_one_eq_one hp0
      have h2 : ((p ^ (q - 1) : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
        push_cast; exact h1
      have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h3.symm
    have hx1 : 1 < p ^ (q - 1) := Nat.one_lt_pow (by omega) hp1
    have hxq : ¬ q ∣ p ^ (q - 1) := by
      intro hd
      exact hpq (hq.out.dvd_of_dvd_pow hd)
    have hv1 : padicValNat q (p ^ (q - 1) - 1) = 1 := by
      have hne : p ^ (q - 1) - 1 ≠ 0 := by omega
      have hge : 1 ≤ padicValNat q (p ^ (q - 1) - 1) :=
        (padicValNat_dvd_iff_le hne).mp (by simpa using hfermat)
      have hlt : ¬ 2 ≤ padicValNat q (p ^ (q - 1) - 1) := fun h2 =>
        c2 ((padicValNat_dvd_iff_le hne).mpr h2)
      omega
    have := padicValNat.pow_sub_pow (p := q) (x := p ^ (q - 1)) (y := 1) hqodd hx1
      (by simpa using hfermat) hxq (n := s) hspos.ne'
    rw [one_pow] at this
    have e : p ^ (2 * i) = (p ^ (q - 1)) ^ s := by
      have h2 : 2 * i = (q - 1) * s := by rw [hs, hh]; ring
      rw [← pow_mul, h2]
    rw [e, this, hv1]
    congr 2
    rw [hs, Nat.mul_div_cancel_left _ hhpos]
  · apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have := c1 _ hd
    rw [hh] at this
    exact hdiv (by
      have := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by simpa using this : 2 * h ∣ 2 * i)
      exact this)

end Odd

/-- Helper: $P_p(m) = \prod_{i=1}^{m}(p^{2i} - 1)$ (natural-number product, `m` factors). -/
def P (p m : ℕ) : ℕ := ∏ i ∈ range m, (p ^ (2 * (i + 1)) - 1)

/-- Helper: $P_p(m+1) = P_p(m)\,(p^{2(m+1)} - 1)$. -/
lemma P_succ (p m : ℕ) : P p (m + 1) = P p m * (p ^ (2 * (m + 1)) - 1) :=
  Finset.prod_range_succ _ _

/-- Helper: $p^k - 1 \ne 0$ for $p > 1$ and $k > 0$. -/
lemma pow_sub_one_ne_zero {p : ℕ} (hp : 1 < p) (k : ℕ) (hk : 0 < k) : p ^ k - 1 ≠ 0 := by
  have := Nat.one_lt_pow hk.ne' hp
  omega

/-- Helper: $P_p(m) \ne 0$ for $p > 1$. -/
lemma P_ne_zero {p : ℕ} (hp : 1 < p) (m : ℕ) : P p m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_sub_one_ne_zero hp _ (by omega)

section Odd2

variable (q p : ℕ) [hq : Fact q.Prime]

/-- Helper: for odd `q` and `p` with the properties `c1`, `c2` of `val_odd`, $v_q(P_p(m)) = \lfloor m/h\rfloor + v_q(\lfloor m/h\rfloor!)$, $h = (q-1)/2$. -/
lemma val_P_odd (hq2 : q ≠ 2) (hpq : ¬ q ∣ p)
    (c2 : ¬ q ^ 2 ∣ p ^ (q - 1) - 1) (hp1 : 1 < p)
    (c1 : ∀ j, q ∣ p ^ j - 1 → (q - 1) ∣ j) (m : ℕ) :
    padicValNat q (P p m) =
      m / ((q - 1) / 2) + padicValNat q ((m / ((q - 1) / 2)).factorial) := by
  induction m with
  | zero => simp [P]
  | succ m ih =>
    haveI := hq
    rw [P_succ, padicValNat.mul (P_ne_zero hp1 m) (pow_sub_one_ne_zero hp1 _ (by omega)), ih,
      val_odd q p hq2 hpq c2 hp1 c1 (m + 1) (Nat.succ_pos m)]
    have hsucc : (m + 1) / ((q - 1) / 2) =
        m / ((q - 1) / 2) + if (q - 1) / 2 ∣ m + 1 then 1 else 0 := Nat.succ_div
    rw [hsucc]
    split_ifs with hd
    · rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
      simp only [Nat.succ_eq_add_one]
      ring
    · simp

end Odd2

/-- Helper: for $p \equiv 3 \pmod 8$, $v_2(p^{2i} - 1) = 3 + v_2(i)$ for $i > 0$. -/
lemma val_two (p : ℕ) (hp8 : p % 8 = 3) (i : ℕ) (hi : 0 < i) :
    padicValNat 2 (p ^ (2 * i) - 1) = 3 + padicValNat 2 i := by
  obtain ⟨k, hk⟩ : ∃ k, p = 8 * k + 3 := ⟨p / 8, by omega⟩
  have h := padicValNat.pow_two_sub_one (x := p) (n := 2 * i) (by omega) (by omega) (by omega)
    (even_two_mul i)
  have h1 : padicValNat 2 (p + 1) = 2 := by
    have : p + 1 = 2 ^ 2 * (2 * k + 1) := by rw [hk]; ring
    rw [this, padicValNat.mul (by norm_num) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by omega)]
  have h2 : padicValNat 2 (p - 1) = 1 := by
    have : p - 1 = 2 * (4 * k + 1) := by omega
    rw [this, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by omega)]
  have h3 : padicValNat 2 (2 * i) = 1 + padicValNat 2 i := by
    rw [padicValNat.mul (by norm_num) hi.ne', padicValNat.self (by norm_num)]
  rw [h1, h2, h3] at h
  omega

/-- Helper: for $p \equiv 3 \pmod 8$, $v_2(P_p(m)) = 3m + v_2(m!)$. -/
lemma val_P_two (p : ℕ) (hp8 : p % 8 = 3) (m : ℕ) :
    padicValNat 2 (P p m) = 3 * m + padicValNat 2 m.factorial := by
  induction m with
  | zero => simp [P]
  | succ m ih =>
    have hp1 : 1 < p := by omega
    rw [P_succ, padicValNat.mul (P_ne_zero hp1 m) (pow_sub_one_ne_zero hp1 _ (by omega)), ih,
      val_two p hp8 (m + 1) (Nat.succ_pos m), Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
    ring

/-- **The exponent $\gamma_q(n)$** of the prime `q` in Cassels' bound $g(n)$ for the order of a finite group of proper rational automorphs of a regular form in `n` variables: $\gamma_q(n) = \sum_{k \ge 0} \lfloor n/(q^{k}(q-1))\rfloor$ for odd `q`, and $\gamma_2(n) = (n - 1) + \sum_{k \ge 1}\lfloor n/2^{k}\rfloor$ (for $n \ge 1$). The displayed formulas, garbled in the machine-read text of Ch. 6, Ex. 7 (p. 101), were read from the page image; the odd case agrees with Ch. 3, Ex. 16; for $q = 2$ the formula is the one obtained by the book's method (reduction modulo a prime $p \equiv 3 \pmod 8$, Ch. 2, Ex. 13 (vi)) and equals the exponent $n + \sum_{k\ge1}\lfloor n/2^k\rfloor$ of $2$ in $2^n n!$ (Minkowski) minus $1$. -/
def gamma (q n : ℕ) : ℕ :=
  if q = 2 then n - 1 + ∑ k ∈ range (n + 1), n / 2 ^ (k + 1)
  else ∑ k ∈ range (n + 1), n / (q ^ k * (q - 1))

/-- Helper: if $a \mid b$ and $b \ne 0$ then $v_q(a) \le v_q(b)$ for a prime `q`. -/
lemma val_le_of_dvd (q : ℕ) [Fact q.Prime] {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat q a ≤ padicValNat q b :=
  (padicValNat_dvd_iff_le hb).mp ((pow_padicValNat_dvd).trans h)

/-- Helper: Legendre's formula $v_q(M!) = \sum_{k=1}^{n}\lfloor M/q^k\rfloor$ for any bound $n \ge M$ (`hM`). -/
lemma legendre_sum (q : ℕ) [hq : Fact q.Prime] (n M : ℕ) (hM : M ≤ n) :
    padicValNat q M.factorial = ∑ k ∈ range n, M / q ^ (k + 1) := by
  have hlog : Nat.log q M < n + 1 :=
    lt_of_le_of_lt (Nat.log_le_self q M) (Nat.lt_succ_of_le hM)
  rw [padicValNat_factorial hlog, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm]

/-- Helper: for odd `q`, $\gamma_q(n) = \lfloor n/(q-1)\rfloor + v_q(\lfloor n/(q-1)\rfloor!)$. -/
lemma gamma_odd (q n : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) :
    gamma q n = n / (q - 1) + padicValNat q ((n / (q - 1)).factorial) := by
  have hq1 : 0 < q - 1 := by have := hq.out.two_le; omega
  have hM : n / (q - 1) ≤ n := Nat.div_le_self _ _
  rw [legendre_sum q n _ hM, gamma, if_neg hq2, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, pow_succ]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.div_div_eq_div_mul]
  congr 1
  ring

/-- Helper: $\gamma_2(n) = (n - 1) + \lfloor n/2\rfloor + v_2(\lfloor n/2\rfloor!)$. -/
lemma gamma_two (n : ℕ) :
    gamma 2 n = n - 1 + (n / 2 + padicValNat 2 ((n / 2).factorial)) := by
  have hM : n / 2 ≤ n := Nat.div_le_self _ _
  rw [legendre_sum 2 n _ hM, gamma, if_pos rfl]
  congr 1
  have h2 : ∀ k, n / 2 ^ (k + 1) = n / 2 / 2 ^ k := fun k => by
    rw [Nat.div_div_eq_div_mul, pow_succ']
  simp only [h2]
  rw [Finset.sum_range_succ']
  simp [add_comm]

/-- Helper: **divisibility datum.** For a candidate group order `card` (the order of $O^{+}$ over $\mathbb F_p$) in `n` variables: for odd $n = 2m+1$, `card` divides $p^{m^2}P_p(m)$; for even $n = 2m > 0$, $2\cdot$`card` divides it; for $n = 0$, `card` $= 1$. -/
def DivData (n card p : ℕ) : Prop :=
  (n % 2 = 1 → card ∣ p ^ ((n / 2) * (n / 2)) * P p (n / 2)) ∧
  (n % 2 = 0 → 0 < n → 2 * card ∣ p ^ ((n / 2) * (n / 2)) * P p (n / 2)) ∧
  (n = 0 → card = 1)

/-- Helper: for an odd prime `q` and `p` with the properties `c1`, `c2` of `val_odd`, the divisibility datum gives $v_q(\text{card}) \le \gamma_q(n)$. -/
lemma bound_odd (q p n card : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) (hpq : ¬ q ∣ p)
    (c2 : ¬ q ^ 2 ∣ p ^ (q - 1) - 1) (hp1 : 1 < p)
    (c1 : ∀ j, q ∣ p ^ j - 1 → (q - 1) ∣ j) (hD : DivData n card p) :
    padicValNat q card ≤ gamma q n := by
  obtain ⟨hD1, hD2, hD3⟩ := hD
  have hXne : p ^ ((n / 2) * (n / 2)) * P p (n / 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by omega)) (P_ne_zero hp1 _)
  have hcX : card ∣ p ^ ((n / 2) * (n / 2)) * P p (n / 2) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [hD3 rfl, P]
    · rcases Nat.mod_two_eq_zero_or_one n with he | ho
      · exact (Dvd.intro_left 2 rfl).trans (hD2 he hpos)
      · exact hD1 ho
  have h1 := val_le_of_dvd q hXne hcX
  rw [padicValNat.mul (pow_ne_zero _ (by omega)) (P_ne_zero hp1 _),
    padicValNat.eq_zero_of_not_dvd (fun h => hpq (hq.out.dvd_of_dvd_pow h)), zero_add,
    val_P_odd q p hq2 hpq c2 hp1 c1] at h1
  rw [gamma_odd q n hq2]
  have hh : q - 1 = 2 * ((q - 1) / 2) := by
    have := hq.out.odd_of_ne_two hq2
    obtain ⟨k, hk⟩ := this
    omega
  have : n / 2 / ((q - 1) / 2) = n / (q - 1) := by
    rw [Nat.div_div_eq_div_mul, ← hh]
  rw [this] at h1
  exact h1

/-- Helper: for $p \equiv 3 \pmod 8$, the divisibility datum gives $v_2(\text{card}) \le \gamma_2(n)$. -/
lemma bound_two (p n card : ℕ) (hp8 : p % 8 = 3) (hD : DivData n card p) :
    padicValNat 2 card ≤ gamma 2 n := by
  obtain ⟨hD1, hD2, hD3⟩ := hD
  have hp1 : 1 < p := by omega
  have hXne : p ^ ((n / 2) * (n / 2)) * P p (n / 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by omega)) (P_ne_zero hp1 _)
  have hp2 : ¬ 2 ∣ p := by omega
  have hX : padicValNat 2 (p ^ ((n / 2) * (n / 2)) * P p (n / 2)) =
      3 * (n / 2) + padicValNat 2 ((n / 2).factorial) := by
    rw [padicValNat.mul (pow_ne_zero _ (by omega)) (P_ne_zero hp1 _),
      padicValNat.eq_zero_of_not_dvd (fun h => hp2 (Nat.prime_two.dvd_of_dvd_pow h)), zero_add,
      val_P_two p hp8]
  rw [gamma_two]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [hD3 rfl]
  · rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have h2dvd := hD2 he hpos
      have hc0 : card ≠ 0 := fun h => hXne (by rw [h] at h2dvd; simpa using h2dvd)
      have h1 := val_le_of_dvd 2 hXne h2dvd
      rw [hX, padicValNat.mul (by norm_num) hc0, padicValNat.self (by norm_num)] at h1
      omega
    · have h1 := val_le_of_dvd 2 hXne (hD1 ho)
      rw [hX] at h1
      omega

/-- Helper (Dirichlet's theorem on primes in progressions): there are primes $p \equiv 3 \pmod 8$ larger than any bound `N`. -/
lemma exists_prime_two (N : ℕ) : ∃ p, N < p ∧ p.Prime ∧ p % 8 = 3 := by
  have hu : IsUnit (3 : ZMod 8) := by decide
  obtain ⟨p, hpN, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu N
  refine ⟨p, hpN, hp, ?_⟩
  have h1 : ((p : ℕ) : ZMod 8) = ((3 : ℕ) : ZMod 8) := by simpa using hmod
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
  simpa using this

/-- Helper (Dirichlet's theorem): for an odd prime `q` there are primes $p > N$ whose residue modulo $q^2$ generates the unit group (a primitive root modulo $q^2$), in the form: $q \nmid p$, $q \mid p^j - 1 \Rightarrow (q-1) \mid j$, and $q^2 \nmid p^{q-1} - 1$. -/
lemma exists_prime_odd (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) (N : ℕ) (hN : q ≤ N) :
    ∃ p, N < p ∧ p.Prime ∧ ¬ q ∣ p ∧ (∀ j, q ∣ p ^ j - 1 → (q - 1) ∣ j) ∧
      ¬ q ^ 2 ∣ p ^ (q - 1) - 1 := by
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  haveI : IsCyclic (ZMod (q ^ 2))ˣ := ZMod.isCyclic_units_of_prime_pow q hq.out hq2 2
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (q ^ 2))ˣ)
  have hord : orderOf g = q * (q - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime_pow hq.out (by norm_num)]
    simp
  obtain ⟨p, hpN, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod g.isUnit N
  have hpq : ¬ q ∣ p := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hq.out hp).mp hd
    omega
  have hfwd : ∀ j, q ^ 2 ∣ p ^ j - 1 → q * (q - 1) ∣ j := by
    intro j hj
    have h1 : 1 ≡ p ^ j [MOD q ^ 2] := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mpr hj
    have h2 : ((1 : ℕ) : ZMod (q ^ 2)) = ((p ^ j : ℕ) : ZMod (q ^ 2)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    have h3 : g ^ j = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← hmod]
      simpa using h2.symm
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h3
  refine ⟨p, hpN, hp, hpq, ?_, ?_⟩
  · intro j hj
    have hz : ((q : ℕ) : ℤ) ∣ ((p : ℤ) ^ j) - 1 := by
      have h1 := (Int.natCast_dvd_natCast).mpr hj
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos)] at h1
      simpa using h1
    have h2 := dvd_sub_pow_of_dvd_sub hz 1
    have h3 : q ^ 2 ∣ p ^ (j * q) - 1 := by
      have h4 : ((q ^ 2 : ℕ) : ℤ) ∣ ((p ^ (j * q) - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos)]
        simpa [pow_mul] using h2
      exact_mod_cast h4
    have h5 := hfwd _ h3
    have h6 : q * (q - 1) ∣ q * j := by rwa [mul_comm j q] at h5
    exact Nat.dvd_of_mul_dvd_mul_left hq.out.pos h6
  · intro h
    have h1 := hfwd _ h
    have h2 := Nat.le_of_dvd (by have := hq.out.two_le; omega) h1
    have h3 := hq.out.two_le
    have h4 : 2 * (q - 1) ≤ q * (q - 1) := Nat.mul_le_mul_right _ h3
    omega


end NT

section Count

open QuadFormsKB.OMeara

/-- Helper: $P_p(m)$ as an integer equals $\prod_{i=1}^{m}(p^{2i} - 1)$ over `Finset.Ico 1 (m + 1)`. -/
lemma castP (p m : ℕ) (hp : 1 ≤ p) :
    ((P p m : ℕ) : ℤ) = ∏ i ∈ Finset.Ico 1 (m + 1), ((p : ℤ) ^ (2 * i) - 1) := by
  induction m with
  | zero => simp [P]
  | succ m ih =>
    rw [P_succ, Nat.cast_mul, ih, Finset.prod_Ico_succ_top (show 1 ≤ m + 1 by omega), Nat.cast_sub
      (Nat.one_le_pow _ _ (by omega))]
    push_cast
    ring

/-- Helper: **counting step (Ch. 2, Ex. 13 (vi)).** For an odd prime `p` and a symmetric integer matrix `S` in `n` variables with $p \nmid \det S$, the order of $O^{+}(\bar S)$ over $\mathbb F_p$ satisfies the divisibility datum `DivData`. -/
lemma divData (p : ℕ) [hp : Fact p.Prime] [Invertible (2 : ZMod p)] (hp2 : p ≠ 2) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℤ) (hS : Sᵀ = S) (hpd : ¬ (p : ℤ) ∣ S.det) :
    DivData n (Nat.card (orthPlus (redForm p S))) p := by
  have hnd := redForm_nondegenerate p S hS hpd
  have hdisc := redForm_discr_ne_zero p S hS hpd
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  refine ⟨?_, ?_, ?_⟩
  · intro hodd
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have h := QuadFormsKB.Cassels.Ch2Ex.ex13_vi_odd p m (redForm p S) hnd
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h2]
    have h3 : ((Nat.card (orthPlus (redForm p S)) : ℕ) : ℤ) = ((p ^ (m * m) * P p m : ℕ) : ℤ) := by
      rw [h, Nat.cast_mul, castP p m hp1]
      push_cast
      rfl
    have h4 : Nat.card (orthPlus (redForm p S)) = p ^ (m * m) * P p m := by exact_mod_cast h3
    rw [h4]
  · intro heven hpos
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hm : 0 < m := by omega
    have h := QuadFormsKB.Cassels.Ch2Ex.ex13_vi_even p m hm (redForm p S) hnd
    have h2 : 2 * m / 2 = m := by omega
    rw [h2]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    set χ : ℤ := quadraticChar (ZMod p) ((-1) ^ (m' + 1) * (redForm p S).discr') with hχ
    have hχ2 : χ ^ 2 = 1 := by
      apply quadraticChar_sq_one
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdisc
    have hχ1 : χ = 1 ∨ χ = -1 := by
      have : χ * χ = 1 := by rw [← sq]; exact hχ2
      exact mul_self_eq_one_iff.mp this
    have hodd : Odd (p : ℤ) := by
      have := hp.out.odd_of_ne_two hp2
      exact_mod_cast this
    have hoddχ : Odd χ := by
      rcases hχ1 with h1 | h1 <;> rw [h1] <;> decide
    obtain ⟨t, ht⟩ : (2 : ℤ) ∣ (p : ℤ) ^ (m' + 1) + χ :=
      even_iff_two_dvd.mp (Odd.add_odd (hodd.pow) hoddχ)
    have hP : ((P p (m' + 1) : ℕ) : ℤ) =
        (∏ i ∈ Finset.Ico 1 (m' + 1), ((p : ℤ) ^ (2 * i) - 1)) * ((p : ℤ) ^ (2 * (m' + 1)) - 1) := by
      rw [castP p _ hp1, Finset.prod_Ico_succ_top (by omega)]
    have hX : ((p ^ ((m' + 1) * (m' + 1)) * P p (m' + 1) : ℕ) : ℤ) =
        ((2 * Nat.card (orthPlus (redForm p S)) : ℕ) : ℤ) * ((p : ℤ) ^ (m' + 1) * t) := by
      rw [Nat.cast_mul, hP]
      push_cast
      rw [h]
      have e1 : (p : ℤ) ^ ((m' + 1) * (m' + 1)) =
          (p : ℤ) ^ ((m' + 1) * (m' + 1 - 1)) * (p : ℤ) ^ (m' + 1) := by
        rw [← pow_add]; congr 1
      have e2 : (p : ℤ) ^ (2 * (m' + 1)) = ((p : ℤ) ^ (m' + 1)) ^ 2 := by
        rw [← pow_mul, mul_comm]
      have e3 : ((p : ℤ) ^ (m' + 1)) ^ 2 - 1 =
          ((p : ℤ) ^ (m' + 1) - χ) * ((p : ℤ) ^ (m' + 1) + χ) := by
        have : ((p : ℤ) ^ (m' + 1) - χ) * ((p : ℤ) ^ (m' + 1) + χ) =
            ((p : ℤ) ^ (m' + 1)) ^ 2 - χ ^ 2 := by ring
        rw [this, hχ2]
      rw [e1, e2, e3, ht]
      ring
    exact Int.natCast_dvd_natCast.mp (Dvd.intro _ hX.symm)
  · intro h0
    subst h0
    have : Subsingleton (Fin 0 → ZMod p) := inferInstance
    have : Subsingleton (orthPlus (redForm p S)) :=
      ⟨fun a b => Subtype.ext (LinearEquiv.ext fun x => Subsingleton.elim _ _)⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

end Count


section Final

open QuadFormsKB QuadFormsKB.OMeara

/-- Helper: a symmetric rational matrix `M` with $x^{\mathsf T}Mx = 0$ for all `x` is zero (polarization). -/
lemma mat_eq_zero_of_forall {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ)
    (hM : M.IsSymm) (h : ∀ x, x ⬝ᵥ (M *ᵥ x) = 0) : M = 0 := by
  ext i j
  have hii := h (Pi.single i 1)
  have hjj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  have hs : M j i = M i j := by
    have := congrFun (congrFun hM i) j
    simpa using this
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single_one,
    dotProduct_single, single_dotProduct] at hii hjj hij
  simp only [Matrix.zero_apply]
  simp [hs] at hij hii hjj
  linarith

/-- Helper: if $f(Tx) = f(x)$ for all $x \in \mathbb Q^n$ then $T^{\mathsf T}AT = A$ for the Gram matrix $A$ of $f$. -/
lemma gram_conj {n : ℕ} (f : RatQF n) (T : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ x : Fin n → ℚ, f.eval (T *ᵥ x) = f.eval x) :
    Tᵀ * f.gram * T = f.gram := by
  have hev : ∀ x : Fin n → ℚ, f.eval x = x ⬝ᵥ (f.gram *ᵥ x) := fun x => by
    have := RatQF.evalIn_eq_gram ℚ f x
    simpa using this
  have hsymm : (Tᵀ * f.gram * T - f.gram).IsSymm := by
    have h1 := RatQF.gram_isSymm f
    unfold Matrix.IsSymm at *
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, h1,
      Matrix.mul_assoc]
  have key : ∀ x, x ⬝ᵥ ((Tᵀ * f.gram * T) *ᵥ x) = f.eval (T *ᵥ x) := by
    intro x
    rw [hev, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec x Tᵀ, Matrix.vecMul_transpose]
  have := mat_eq_zero_of_forall _ hsymm (fun x => by
    rw [Matrix.sub_mulVec, dotProduct_sub, key, h x, hev x, sub_self])
  exact sub_eq_zero.mp this


/-- Helper: a prime `p` larger than $|\det S|$ does not divide $\det S \ne 0$. -/
lemma not_dvd_det {n p : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (hSd : S.det ≠ 0)
    (hp : S.det.natAbs < p) : ¬ (p : ℤ) ∣ S.det := by
  intro h
  have h1 : p ∣ S.det.natAbs := Int.natCast_dvd.mp h
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hSd) h1
  omega

/-- Helper: $2 \ne 0$ in $\mathbb F_p$ for a prime $p \ne 2$. -/
lemma two_ne_zero_zmod (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have := (ZMod.natCast_eq_zero_iff 2 p).mp h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

/-- Helper: the divisibility datum forces `card` $\ne 0$. -/
lemma card_ne_zero_of_divData {n card p : ℕ} (hp : 1 < p) (hD : DivData n card p) : card ≠ 0 := by
  obtain ⟨hD1, hD2, hD3⟩ := hD
  have hXne : p ^ ((n / 2) * (n / 2)) * P p (n / 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by omega)) (P_ne_zero hp _)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [hD3 rfl]
  · rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · intro h0
      have := hD2 he hpos
      rw [h0] at this
      simp at this
      exact hXne (by simpa using this)
    · intro h0
      have := hD1 ho
      rw [h0] at this
      exact hXne (zero_dvd_iff.mp this)

/-- Helper: **local bound.** For a finite group `G` embedded by `ρ` in integer matrices of determinant $1$ preserving a symmetric integral matrix `S` of nonzero determinant, and every prime `q`, $v_q(|G|) \le \gamma_q(n)$. (Choose a prime `p` by Dirichlet's theorem: $p \equiv 3 \pmod 8$ for $q = 2$, a primitive root modulo $q^2$ otherwise, and $p$ larger than $|\det S|$; reduce modulo `p`.) -/
theorem val_card_le {n : ℕ} (S : Matrix (Fin n) (Fin n) ℤ) (hS : Sᵀ = S) (hSd : S.det ≠ 0)
    {G : Type*} [Group G] [Finite G] (ρ : G →* Matrix (Fin n) (Fin n) ℤ)
    (hρ : Function.Injective ρ) (hAS : ∀ g, (ρ g)ᵀ * S * ρ g = S) (hdet : ∀ g, (ρ g).det = 1)
    (q : ℕ) [hq : Fact q.Prime] : padicValNat q (Nat.card G) ≤ gamma q n := by
  have hcardG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  by_cases hq2 : q = 2
  · subst hq2
    obtain ⟨p, hpN, hp, hp8⟩ := exists_prime_two (S.det.natAbs)
    have hpf : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by omega
    have : Invertible (2 : ZMod p) := invertibleOfNonzero (two_ne_zero_zmod p hp2)
    have hpd := not_dvd_det S hSd hpN
    have hdvd := card_dvd_card_orthPlus p S hS hpd hp2 ρ hρ hAS hdet
    have hD := divData p hp2 S hS hpd
    have hc0 := card_ne_zero_of_divData hp.one_lt hD
    exact (val_le_of_dvd 2 hc0 hdvd).trans (bound_two p n _ hp8 hD)
  · obtain ⟨p, hpN, hp, hpq, c1, c2⟩ :=
      exists_prime_odd q hq2 (S.det.natAbs + q) (by omega)
    have hpf : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by have := hq.out.two_le; omega
    have : Invertible (2 : ZMod p) := invertibleOfNonzero (two_ne_zero_zmod p hp2)
    have hpd := not_dvd_det (p := p) S hSd (by omega)
    have hdvd := card_dvd_card_orthPlus p S hS hpd hp2 ρ hρ hAS hdet
    have hD := divData p hp2 S hS hpd
    have hc0 := card_ne_zero_of_divData hp.one_lt hD
    exact (val_le_of_dvd q hc0 hdvd).trans (bound_odd q p n _ hq2 hpq c2 hp.one_lt c1 hD)


/-- **Cassels' bound** $g(n) = \prod_{q} q^{\gamma_q(n)}$ (product over the primes $q \le n + 1$; for larger primes $\gamma_q(n) = 0$), see `gamma`. -/
def gCassels (n : ℕ) : ℕ := ∏ q ∈ (Finset.range (n + 2)).filter Nat.Prime, q ^ gamma q n

/-- Helper: $\gamma_q(n) = 0$ for a prime $q > n + 1$. -/
lemma gamma_eq_zero {q n : ℕ} (hq : q.Prime) (h : n + 1 < q) : gamma q n = 0 := by
  unfold gamma
  split_ifs with h2
  · subst h2
    have : n = 0 := by omega
    subst this
    simp
  · apply Finset.sum_eq_zero
    intro k _
    apply Nat.div_eq_of_lt
    have hq1 : n < q - 1 := by omega
    exact lt_of_lt_of_le hq1 (Nat.le_mul_of_pos_left _ (pow_pos hq.pos _))

/-- Helper: a nonzero natural number `N` with $v_q(N) \le \gamma_q(n)$ for all primes `q` divides $g(n)$. -/
lemma dvd_gCassels (n N : ℕ) (hN : N ≠ 0) (h : ∀ q, q.Prime → padicValNat q N ≤ gamma q n) :
    N ∣ gCassels n := by
  have hg : gCassels n ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ (Finset.mem_filter.mp hq).2.ne_zero
  rw [← Nat.factorization_prime_le_iff_dvd hN hg]
  intro q hq
  have hfac : (gCassels n).factorization q = gamma q n := by
    unfold gCassels
    rw [Nat.factorization_prod (fun x hx => pow_ne_zero _ (Finset.mem_filter.mp hx).2.ne_zero),
      Finsupp.finset_sum_apply]
    by_cases hqm : q ∈ (Finset.range (n + 2)).filter Nat.Prime
    · rw [Finset.sum_eq_single q]
      · rw [hq.factorization_pow]; simp
      · intro b hb hbq
        rw [(Finset.mem_filter.mp hb).2.factorization_pow]
        simp [Finsupp.single_apply, hbq]
      · intro hn; exact absurd hqm hn
    · rw [Finset.sum_eq_zero]
      · symm
        refine gamma_eq_zero hq ?_
        by_contra hcon
        exact hqm (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩)
      · intro b hb
        rw [(Finset.mem_filter.mp hb).2.factorization_pow]
        have : b ≠ q := fun hbq => hqm (hbq ▸ hb)
        simp [Finsupp.single_apply, this]
  rw [hfac, Nat.factorization_def N hq]
  exact h q hq

/-- **Cassels, Ch. 6, Ex. 7 (p. 101).** Let `G` be a finite group of proper rational automorphs of a regular rational
quadratic form `f` in `n` variables: `G` is a finite subgroup of $\mathrm{GL}_n(\mathbb Q)$ whose elements `T` satisfy
$f(T\vec x) = f(\vec x)$ for all $\vec x \in \mathbb Q^n$ (`hG`, first component) and $\det T = 1$ (second component);
`hf` says that `f` is regular (nondegenerate). Then the order of `G` divides $g(n) = \prod_q q^{\gamma_q(n)}$
(`gCassels n`, exponents `gamma`). *Proof (Cassels' hint):* `G` stabilizes a lattice, hence is conjugate to a group of
integer matrices preserving an integral Gram matrix (`integral_model_gl`); for every prime `q` choose by Dirichlet's
theorem a prime `p` (large, $p \equiv 3 \pmod 8$ if $q = 2$, a primitive root modulo $q^2$ if `q` is odd); reduction
modulo `p` embeds `G` in $O^{+}$ of the reduced form (kernel trivial by Ch. 3, Ex. 14 (i)), whose order is given by Ch. 2,
Ex. 13 (vi), and the $q$-adic valuation of that order is at most $\gamma_q(n)$. -/
@[kb "cassels1978" "Ch. 6, Ex. 7, p. 101"]
theorem ex7 {n : ℕ} (f : RatQF n) (hf : f.Nondegenerate) (G : Subgroup (GL (Fin n) ℚ)) [Finite G]
    (hG : ∀ T ∈ G, (∀ x : Fin n → ℚ, f.eval (T.val *ᵥ x) = f.eval x) ∧ T.val.det = 1) :
    Nat.card G ∣ gCassels n := by
  obtain ⟨ρ, S, hinj, hS, hSd, hSρ, hdetρ⟩ :=
    integral_model_gl f.gram (RatQF.gram_isSymm f) ((RatQF.nondegenerate_iff_det_gram f).mp hf) G
      (fun T hT => gram_conj f T.val (hG T hT).1) (fun T hT => (hG T hT).2)
  refine dvd_gCassels n _ Nat.card_pos.ne' (fun q hq => ?_)
  have : Fact q.Prime := ⟨hq⟩
  exact val_card_le S hS hSd ρ hinj hSρ hdetρ q

end Final

end QuadFormsKB.Cassels.Ch6Ex7
