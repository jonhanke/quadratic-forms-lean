/-
# Cassels, Chapter 10, Lemma 4.1 (p. 183): $\operatorname{Spin}(\Lambda) \to \Theta(\Lambda)$ is onto

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §4, Lemma 4.1, pp. 183-184. Let $I = \mathbb Z_p$
with $p \ne 2$ prime, $n > 1$, and suppose that (4.5) holds ($\phi(\Lambda) \subseteq I$) and that the determinant $d$ of the
form induced on the lattice $\Lambda$ is a $p$-adic unit. Then the homomorphism $\operatorname{Spin}(\Lambda) \to
O(\Lambda)$, $u \mapsto T_u$ (4.10) (Theorem 3.3 restricted to $\operatorname{Spin}(\Lambda)$) maps onto
$\Theta(\Lambda) = \Theta(V) \cap O(\Lambda)$; moreover the spinor norms of $O^+(\Lambda)$ are exactly
$U_p(\mathbb Q_p^\times)^2$ (4.11).

**What is formalized.** The onto part, `exists_spinConj_eq_of_mem_orthPrime`: every $\sigma \in \Theta(V)$ with
$\sigma\Lambda = \Lambda$ is $T_v$ (`spinConj v`) for some $v$ in `intSpin Q Λ`. The second assertion (4.11) is not
re-proved here: over any number field it is already in the library as `Lattices.mem_localSpinorNormGroup_iff_of_unimodular`.

**Setting (a choice, no loss of generality).** Every lattice has a basis, so the lattice is taken to be
$\Lambda = \mathbb Z_p^n$ (`zpLat p n`) in $V = \mathbb Q_p^n$, with the quadratic form $Q(\vec x) = \vec x^{t}F\vec x$
of a symmetric matrix $F$ (`qfForm F`). Condition (4.5) and the unit determinant are the hypotheses `hint`
($\lVert f_{ij}\rVert_p \le 1$ for all entries) and `hdet` ($\lVert\det F\rVert_p = 1$); `hn` is $n > 1$. The group
$\Theta(V)$ is O'Meara's $O'(V)$ (`OMeara.orthPrime`), and $O(\Lambda)$ is `OMeara.orthLat Q Λ`
(rotations preserving the form and mapping $\Lambda$ onto itself), so $\Theta(\Lambda)$ is the conjunction of the
two hypotheses on $\sigma$.

**Proof** (as in Cassels). By Ch. 8, Lemma 3.3, Corollary 2 (`intAut_eq_prod_tau_unit`) an integral automorph is a product
$\tau(b_1)\cdots\tau(b_r)$ with $\vec b_j \in \Lambda$ and $\phi(\vec b_j)$ a unit. As $\sigma$ is a rotation, $r$ is
even. Then $\sigma = T_w$ with $w = \vec b_1\cdots\vec b_r \in C_0(\Lambda)$ and $ww' = \phi(\vec b_1)\cdots\phi(\vec b_r)$,
a unit of $\mathbb Z_p$. As $\sigma \in \Theta$, the spinor norm of $\sigma$ is trivial, so $ww' = t^2$ with $t \in
\mathbb Q_p^\times$, hence a unit of $\mathbb Z_p$; then $v = t^{-1}w$ lies in $C(\Lambda)$, in $\operatorname{Spin}(V)$ and
$T_v = \sigma$.

*Deviation from the printed text.* None in substance; Cassels' $\mathbb Z_p$-lattice $\Lambda$ is replaced by $\mathbb Z_p^n$
(see above), and the hypothesis $n > 1$ (used by Cassels only for (4.11), and by the library's `Nontrivial` hypothesis
in Theorem 3.3) is kept as printed.
-/
import QuadFormsKB.Literature.Cassels.Ch10.IntegralClifford
import QuadFormsKB.Literature.Cassels.Ch10.SpinGroup
import QuadFormsKB.Literature.Cassels.Ch8.Automorphs

open Module CliffordAlgebra Matrix

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

section Lemma41

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- Helper: the product of symmetries `symProd` of the quadratic form of $F$ is the product of Cassels' maps
`tauFun F b` (as linear endomorphisms). -/
theorem symProd_toLinearMap_eq_prod_tauFun {F : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : Fᵀ = F)
    (l : List (Fin n → ℚ_[p])) (hl : ∀ y ∈ l, qfForm F y ≠ 0) :
    (symProd (Q := qfForm F) l hl).toLinearMap = (l.map (tauFun F)).prod := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [symProd_cons, List.map_cons, List.prod_cons, ← ih (fun z hz => hl z (List.mem_cons_of_mem y hz))]
    refine LinearMap.ext fun x => ?_
    simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply, Module.End.mul_apply]
    exact symmetry_eq_tauFun hF _ _

/-- Helper: a product of vectors of the lattice, as an element of the Clifford group, lies in $C(\Lambda)$. -/
theorem vecProd_mem_intClifford {I k V : Type*} [CommRing I] [Field k] [Invertible (2 : k)] [Algebra I k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [Module I V] [IsScalarTower I k V] {Q : QuadraticForm k V} {Λ : Submodule I V}
    (l : List V) (hl : ∀ y ∈ l, Q y ≠ 0) (hΛ : ∀ y ∈ l, y ∈ Λ) :
    (((vecProd l hl : cliffordGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ intClifford Q Λ := by
  induction l with
  | nil =>
    simp only [vecProd, List.attach_nil, List.map_nil, List.prod_nil]
    exact (intClifford Q Λ).one_mem
  | cons y l ih =>
    rw [coe_vecProd_cons]
    exact mul_mem (ι_mem_intClifford (hΛ y (List.mem_cons_self ..)))
      (ih _ fun z hz => hΛ z (List.mem_cons_of_mem y hz))

/-- Helper: the product of a list of $p$-adic numbers of norm $1$ has norm $1$. -/
theorem norm_list_prod_eq_one (l : List ℚ_[p]) (h : ∀ a ∈ l, ‖a‖ = 1) : ‖l.prod‖ = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, norm_mul, h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem a hb),
      mul_one]

/-- Helper: an even element $u$ of the Clifford group (a unit of $M_0(V)$) with $uu' = 1$ lies in the spin group. -/
theorem mem_spinGroup_of_M0 {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] {Q : QuadraticForm k V}
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (u : M0 Q)
    (hu : ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      reverse ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1) :
    ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ spinGroup Q := by
  rw [mem_spinGroup_iff hQ]
  refine ⟨u.2.1, hu, fun x => ?_⟩
  obtain ⟨y, hy⟩ := u.2.2 x
  have hinv : (↑((u : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) =
      reverse ((u : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
    eq_of_mul_eq_one_of_mul_eq_one (u : (CliffordAlgebra Q)ˣ).mul_inv
      (mul_eq_one_comm_of_finiteDimensional k hu)
  exact ⟨y, by rw [hy, hinv]⟩

/-- **Cassels, Ch. 10, Lemma 4.1** (pp. 183-184), the onto part: the homomorphism
$\operatorname{Spin}(\Lambda) \to \Theta(\Lambda)$, $v \mapsto T_v$ (4.10) is onto.

Arguments: `hp2` is $p \ne 2$; `hn` is $n > 1$; `F` is the symmetric matrix (`hF`) of the form
$Q(\vec x) = \vec x^{t}F\vec x$ on $V = \mathbb Q_p^n$ (`qfForm F`); `hint` is (4.5) for $\Lambda = \mathbb Z_p^n$ (all
entries of $F$ are $p$-adic integers); `hdet` says that the determinant $d = \det F$ of the form induced on $\Lambda$ is a
$p$-adic unit; `σ` is an element of $\Theta(V)$ (`hσΘ`, O'Meara's $O'(V)$) that maps $\Lambda = \mathbb Z_p^n$ onto itself
(`hσΛ`), i.e. an element of $\Theta(\Lambda) = \Theta(V) \cap O(\Lambda)$. Conclusion: there is $v$ in
$\operatorname{Spin}(\Lambda)$ (`intSpin (qfForm F) (zpLat p n)`) with $T_v = \sigma$ (`spinConj v`). -/
@[kb "cassels1978" "Ch. 10, Lemma 4.1, p. 183 ((4.10) is onto)"]
theorem exists_spinConj_eq_of_mem_orthPrime (hp2 : p ≠ 2) (hn : 1 < n) (F : Matrix (Fin n) (Fin n) ℚ_[p])
    (hF : Fᵀ = F) (hint : ∀ i j, ‖F i j‖ ≤ 1) (hdet : ‖F.det‖ = 1)
    {σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p])}
    (hσΘ : σ ∈ OMeara.orthPrime (qfForm F)) (hσΛ : σ ∈ OMeara.orthLat (qfForm F) (zpLat p n)) :
    ∃ v ∈ intSpin (I := ℤ_[p]) (Q := qfForm F) (zpLat p n), spinConj v = σ := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hdet0 : F.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  have hright : ∀ y : Fin n → ℚ_[p], (∀ x, OMeara.bil (qfForm F) x y = 0) → y = 0 := by
    intro y hy
    refine Matrix.eq_zero_of_mulVec_eq_zero hdet0 (funext fun i => ?_)
    have := hy (Pi.single i 1)
    rw [bil_qfForm hF, single_dotProduct, one_mul] at this
    simpa using this
  have hQ : (QuadraticMap.associated (qfForm F)).Nondegenerate :=
    ⟨fun x hx => hright x fun z => (OMeara.bil_comm (qfForm F) z x).trans (hx z), hright⟩
  obtain ⟨l, hl, hσl⟩ :=
    intAut_eq_prod_tau_unit hp2 F hF hint hdet ((isIntAut_iff_mem_orthLat F σ).2 hσΛ)
  have hl0 : ∀ y ∈ l, qfForm F y ≠ 0 := by
    intro y hy
    rw [qfForm_apply]
    exact (hl y hy).2.2.choose
  have hσ : σ = symProd (Q := qfForm F) l hl0 :=
    LinearEquiv.toLinearMap_injective (by rw [symProd_toLinearMap_eq_prod_tauFun hF l hl0]; exact hσl)
  have hev : Even l.length := even_length_of_det l hl0 (by rw [← hσ]; exact hσΘ.1.2)
  -- the element w = b_1 ⋯ b_r
  set W : cliffordGroup (qfForm F) := vecProd l hl0 with hW
  have hWeven : ((W : (CliffordAlgebra (qfForm F))ˣ) : CliffordAlgebra (qfForm F)) ∈ evenOdd (qfForm F) 0 :=
    vecProd_mem_even hl0 hev
  have hWM : (W : (CliffordAlgebra (qfForm F))ˣ) ∈ M0 (qfForm F) := ⟨hWeven, W.2⟩
  have hWT : conjHom W = σ := by
    rw [hW, conjHom_vecProd, negE_pow_even hev, one_mul, hσ]
  -- ww' = c is a unit
  set c : ℚ_[p] := (l.map (qfForm F)).prod with hc
  have hWc : ((W : (CliffordAlgebra (qfForm F))ˣ) : CliffordAlgebra (qfForm F)) *
      reverse ((W : (CliffordAlgebra (qfForm F))ˣ) : CliffordAlgebra (qfForm F)) =
      algebraMap ℚ_[p] _ c := vecProd_mul_reverse l hl0
  have hcnorm : ‖c‖ = 1 := by
    refine norm_list_prod_eq_one _ fun a ha => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    rw [qfForm_apply]
    exact (hl b hb).2.1
  -- c is a square (the spinor norm of σ is trivial)
  have hsn : OMeara.HasSpinorNorm (qfForm F) σ c := by
    rw [← hWT]
    exact hasSpinorNorm_conjM0 hQ ⟨_, hWM⟩ hWc
  obtain ⟨s, hs0, hcs⟩ := OMeara.HasSpinorNorm.eq_mul_sq (qfForm F) hQ hsn hσΘ.2
  rw [one_mul] at hcs
  have hsnorm : ‖s‖ = 1 := by
    have h2 : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, ← hcs, hcnorm]
    have h3 : 0 ≤ ‖s‖ := norm_nonneg _
    nlinarith
  -- v = s⁻¹ w
  let t : ℤ_[p] := ⟨s⁻¹, by change ‖s⁻¹‖ ≤ 1; rw [norm_inv, hsnorm]; simp⟩
  have ht : algebraMap ℤ_[p] ℚ_[p] t = s⁻¹ := rfl
  have hWmem : ((W : (CliffordAlgebra (qfForm F))ˣ) : CliffordAlgebra (qfForm F)) ∈
      intClifford (qfForm F) (zpLat p n) :=
    vecProd_mem_intClifford l hl0 fun y hy => mem_zpLat.2 (hl y hy).1
  let U : M0 (qfForm F) := ⟨_, (M0 (qfForm F)).mul_mem (scalar_mem_M0 (Units.mk0 s⁻¹ (inv_ne_zero hs0))) hWM⟩
  have hUval : ((U : (CliffordAlgebra (qfForm F))ˣ) : CliffordAlgebra (qfForm F)) =
      algebraMap ℚ_[p] _ s⁻¹ * ((W : (CliffordAlgebra (qfForm F))ˣ) : CliffordAlgebra (qfForm F)) := rfl
  have hUrev : ((U : (CliffordAlgebra (qfForm F))ˣ) : CliffordAlgebra (qfForm F)) *
      reverse ((U : (CliffordAlgebra (qfForm F))ˣ) : CliffordAlgebra (qfForm F)) = 1 := by
    rw [hUval, reverse.map_mul, reverse.commutes, ← Algebra.commutes s⁻¹ (reverse _), mul_assoc,
      ← mul_assoc _ (algebraMap ℚ_[p] _ s⁻¹), ← Algebra.commutes s⁻¹, mul_assoc, hWc, ← mul_assoc,
      ← map_mul, ← map_mul, hcs, ← map_one (algebraMap ℚ_[p] (CliffordAlgebra (qfForm F)))]
    congr 1
    field_simp
  have hmem := mem_spinGroup_of_M0 hQ U hUrev
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · -- v ∈ C(Λ)
    change ((U : (CliffordAlgebra (qfForm F))ˣ) : CliffordAlgebra (qfForm F)) ∈
      intClifford (qfForm F) (zpLat p n)
    rw [hUval, ← ht, ← IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p]]
    exact mul_mem ((intClifford (qfForm F) (zpLat p n)).algebraMap_mem t) hWmem
  · rw [spinConj_eq]
    have hUeq : (⟨spinGroup.toUnits (⟨_, hmem⟩ : spinGroup (qfForm F)), spinGroup_mem_M0 _⟩ : M0 (qfForm F)) = U :=
      Subtype.ext (Units.ext rfl)
    refine Eq.trans (congrArg conjM0 hUeq) ?_
    change conjM0 (⟨_, scalar_mem_M0 (Units.mk0 s⁻¹ (inv_ne_zero hs0))⟩ * ⟨_, hWM⟩) = σ
    rw [map_mul, (conjM0_eq_one_iff hQ ⟨_, scalar_mem_M0 (Units.mk0 s⁻¹ (inv_ne_zero hs0))⟩).2 ⟨_, rfl⟩,
      one_mul]
    exact hWT

end Lemma41

end QuadFormsKB.Cassels