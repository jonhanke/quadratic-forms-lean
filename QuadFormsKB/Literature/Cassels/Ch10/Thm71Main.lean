/-
# Cassels, Chapter 10, Theorem 7.1 for $n \ge 5$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §7, Theorem 7.1 (p. 186) and its proof for
$n \ge 4$ (pp. 189–190).

**Proves** `spinStrongApproximation_five`: the field of `SpinStrongApproximation` for $\dim V \ge 5$. Proof (Cassels' second
stage, which suffices when every $V_p$ is isotropic): let $T$ be the finite set of primes where $\mathcal U_p \ne \operatorname{Spin}(\Lambda_p)$,
together with $2$ and the primes dividing the determinant of the integral model $f$ of $Q$ on a basis of $\Lambda$. For $p \in T$
choose $u^{(p)} \in \mathcal U_p$; $V_p$ is isotropic ($n \ge 5$), so by Lemma 3.4 and Theorem 3.2 $u^{(p)}$ is a product of commutators
$w_j^{(p)}$, padded to a common number $s$ of factors with trivial commutators; by Lemma 7.2 each family $(w_j^{(p)})_p$ has the
approximation property, hence so does their product (`SpinApprox.list_prod`), which is the family $u^{(p)}$.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Five
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski

open CliffordAlgebra TensorProduct Module Matrix Topology Filter

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Thm71Five

open QuadFormsKB.Cassels Thm71Ternary Thm71Spin Thm71Coords Thm71Approx

section Main

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] {Q : QuadraticForm ℚ V}

/-- Helper: $Q_K$ is regular when $Q$ is (via the Gram matrix of a basis). -/
theorem nondegenerate_baseChange {n : ℕ} (e : Basis (Fin n) ℚ V) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (K : Type*) [Field K] [Algebra ℚ K] [Invertible (2 : K)] :
    (QuadraticMap.associated (Q.baseChange K)).Nondegenerate := by
  refine (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Algebra.TensorProduct.basis K e)).2 ?_
  have e1 : LinearMap.BilinForm.toMatrix (Algebra.TensorProduct.basis K e) (QuadraticMap.associated (Q.baseChange K)) =
      (gram Q e).map (algebraMap ℚ K) := by
    rw [← gram_baseChange]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply]
    rfl
  rw [e1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (det_gram_ne_zero hQ e)

/-- Helper: Cassels' commutator of $a$ with itself is $1$. -/
theorem vprod_vcommList_self {k W : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup W] [Module k W]
    {Q : QuadraticForm k W} {a : W} (ha : Q a ≠ 0) : vprod Q (vcommList Q a a) = 1 := by
  rw [← commutatorElement_vecUnit ha ha, commutatorElement_self, Units.val_one]

/-- Helper: padding a product with trivial factors. -/
theorem prod_range_getD {M α : Type*} [Monoid M] (g : α → M) (d : α) (hd : g d = 1) :
    ∀ (L : List α) (s : ℕ), L.length ≤ s → ((List.range s).map fun j => g (L.getD j d)).prod = (L.map g).prod
  | [], s, _ => by simp [hd]
  | x :: L, 0, h => by simp at h
  | x :: L, s + 1, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    simp only [List.getD_cons_zero, List.map_cons, List.prod_cons]
    congr 1
    have := prod_range_getD g d hd L s (by simpa using h)
    rw [← this]
    congr 1

/-- **Cassels, Ch. 10, Theorem 7.1 for $n \ge 5$** (Strong Approximation Theorem for the Spin Group, p. 186; proof pp. 189–190):
the field of `SpinStrongApproximation` for $\dim V \ge 5$ (`hn`). -/
@[kb "cassels1978" "Ch. 10, Thm. 7.1, p. 186; proof for n ≥ 4 (second stage), pp. 189–190"]
theorem spinStrongApproximation_five (Q : QuadraticForm ℚ V) (hn : 5 ≤ Module.finrank ℚ V)
    (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hind : ∃ x : ℝ ⊗[ℚ] V, x ≠ 0 ∧ Q.baseChange ℝ x = 0)
    (Λ : Submodule ℤ V) (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set V) = ⊤)
    (U : ∀ (p : ℕ) [Fact p.Prime], Set (spinGroup (Q.baseChange ℚ_[p])))
    (hne : ∀ (p : ℕ) [Fact p.Prime], (U p).Nonempty)
    (hopen : ∀ (p : ℕ) [Fact p.Prime],
      @IsOpen _ (@instTopologicalSpaceSubtype _ _ (cliffordTopology (Q.baseChange ℚ_[p]))) (U p))
    (hcof : {p : ℕ | ∃ hp : p.Prime, haveI : Fact p.Prime := ⟨hp⟩;
      U p ≠ (intSpin (Q := Q.baseChange ℚ_[p]) (baseChangeLat ℚ_[p] ℤ_[p] Λ) : Set _)}.Finite) :
    ∃ u : spinGroup Q, ∀ (p : ℕ) [Fact p.Prime], spinBaseChange ℚ_[p] Q u ∈ U p := by
  classical
  obtain ⟨n, hn'⟩ : ∃ n, Module.finrank ℚ V = n := ⟨_, rfl⟩
  rw [hn'] at hn
  -- a basis of $\Lambda$
  obtain ⟨b₀, hb₀li, hΛ⟩ := exists_basis_of_fg_span (I := ℤ) (k := ℚ) Λ hfg hspan
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set e₀ : Fin n → V := fun i => b₀ (Fin.cast hn'.symm i) with he₀
  have he₀li : LinearIndependent ℚ e₀ := hb₀li.comp _ (Fin.cast_injective _)
  set e : Basis (Fin n) ℚ V := basisOfLinearIndependentOfCardEqFinrank he₀li (by simp [hn']) with hedef
  have heV : ⇑e = e₀ := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have he : ∀ i, e i ∈ Λ := fun i => by
    rw [heV, hΛ]; exact Submodule.subset_span ⟨_, rfl⟩
  -- the integral model
  set G := gram Q e with hG
  obtain ⟨D, hD, hDz⟩ := exists_common_den (fun ij : Fin n × Fin n => G ij.1 ij.2)
  choose N₀ hN₀ using hDz
  set N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => N₀ (i, j) with hN
  have hND : N.map (Int.cast : ℤ → ℚ) = (D : ℚ) • G := by
    ext i j; simp [hN, hN₀]
  have hNs : Nᵀ = N := by
    ext i j
    have h1 := congrFun (congrFun hND i) j
    have h2 := congrFun (congrFun hND j) i
    have hGs : G j i = G i j := by
      exact congrFun (congrFun (gram_transpose Q e) i) j
    simp only [map_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
    have : (N j i : ℚ) = N i j := by rw [h1, h2, hGs]
    exact_mod_cast this
  set f := LocalDensity.ofMatrixZ N with hf
  have hfdet : f.hessian.det ≠ 0 := det_hessian_ne_zero e hQ hNs hD hND
  -- $f$ is indefinite
  have hfind : ∃ x y : Fin n → ℝ, f.evalIn ℝ x < 0 ∧ 0 < f.evalIn ℝ y := by
    obtain ⟨x, hx0, hx⟩ := hind
    set bR := Algebra.TensorProduct.basis ℝ e
    have hGR : gram (Q.baseChange ℝ) bR = G.map (algebraMap ℚ ℝ) := by
      have : (bR : Fin n → ℝ ⊗[ℚ] V) = fun l => (1 : ℝ) ⊗ₜ[ℚ] e l := by
        funext l; exact Algebra.TensorProduct.basis_apply e l
      rw [this, gram_baseChange]
    have hsym : (G.map (algebraMap ℚ ℝ))ᵀ = G.map (algebraMap ℚ ℝ) := by
      rw [← Matrix.transpose_map, gram_transpose]
    have hdet : (G.map (algebraMap ℚ ℝ)).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero _).2 (det_gram_ne_zero hQ e)
    have hw : bR.equivFun x ≠ 0 := fun h => hx0 (bR.equivFun.injective (by rw [h, map_zero]))
    have hiso : bR.equivFun x ⬝ᵥ G.map (algebraMap ℚ ℝ) *ᵥ bR.equivFun x = 0 := by
      rw [← hGR, ← eq_dotProduct_gram]; exact hx
    obtain ⟨y₁, y₂, h₁, h₂⟩ := exists_pos_neg_of_isotropic hsym hdet hw hiso
    have hNR : N.map (Int.cast : ℤ → ℝ) = (D : ℝ) • G.map (algebraMap ℚ ℝ) := by
      ext i j
      have := congrFun (congrFun hND i) j
      simp only [map_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [← Rat.cast_intCast, this, Rat.cast_mul, Rat.cast_natCast, eq_ratCast]
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    refine ⟨y₁, y₂, ?_, ?_⟩
    · rw [evalIn_ofMatrixZ N hNs, hNR, smul_mulVec, dotProduct_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg hDR h₁
    · rw [evalIn_ofMatrixZ N hNs, hNR, smul_mulVec, dotProduct_smul, smul_eq_mul]
      exact mul_pos hDR h₂
  -- the finite set $T$
  set T : Finset Nat.Primes :=
    (hcof.toFinset ∪ {2} ∪ (f.hessian.det.natAbs).primeFactors).subtype Nat.Prime with hT
  have hT2 : ∀ p : Nat.Primes, p ∉ T → (p : ℕ) ≠ 2 := fun p hp h => hp (Finset.mem_subtype.2 (by simp [h]))
  have hTd : ∀ p : Nat.Primes, p ∉ T → ¬ ((p : ℕ) : ℤ) ∣ f.hessian.det := by
    intro p hp h
    refine hp (Finset.mem_subtype.2 (Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨p.2, ?_,
      Int.natAbs_ne_zero.2 hfdet⟩)))
    exact Int.natCast_dvd.1 h
  have hTU : ∀ p : Nat.Primes, p ∉ T →
      U p = (intSpin (Q := Q.baseChange ℚ_[(p : ℕ)]) (baseChangeLat ℚ_[(p : ℕ)] ℤ_[(p : ℕ)] Λ) : Set _) := by
    intro p hp
    by_contra hne'
    exact hp (Finset.mem_subtype.2 (Finset.mem_union_left _ (Finset.mem_union_left _
      (hcof.mem_toFinset.2 ⟨p.2, hne'⟩))))
  -- local commutator decompositions
  have hloc : ∀ p : Nat.Primes, ∃ (L : List ((ℚ_[(p : ℕ)] ⊗[ℚ] V) × (ℚ_[(p : ℕ)] ⊗[ℚ] V)))
      (a₀ : ℚ_[(p : ℕ)] ⊗[ℚ] V), p ∈ T → (∀ ab ∈ L, Q.baseChange ℚ_[(p : ℕ)] ab.1 ≠ 0 ∧
        Q.baseChange ℚ_[(p : ℕ)] ab.2 ≠ 0) ∧ Q.baseChange ℚ_[(p : ℕ)] a₀ ≠ 0 ∧
        ∃ w ∈ U p, (w : CliffordAlgebra _) =
          (L.map fun ab => vprod (Q.baseChange ℚ_[(p : ℕ)]) (vcommList (Q.baseChange ℚ_[(p : ℕ)]) ab.1 ab.2)).prod := by
    intro p
    by_cases hp : p ∈ T
    · have hQp := nondegenerate_baseChange e hQ ℚ_[(p : ℕ)]
      have hfin : Module.finrank ℚ_[(p : ℕ)] (ℚ_[(p : ℕ)] ⊗[ℚ] V) = n := by
        rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℚ_[(p : ℕ)] e), Fintype.card_fin]
      have : Nontrivial (ℚ_[(p : ℕ)] ⊗[ℚ] V) := Module.nontrivial_of_finrank_pos (R := ℚ_[(p : ℕ)]) (by rw [hfin]; omega)
      -- isotropy of $V_p$
      have hiso : ∃ x : ℚ_[(p : ℕ)] ⊗[ℚ] V, x ≠ 0 ∧ Q.baseChange ℚ_[(p : ℕ)] x = 0 := by
        have hnd : (f.map (Int.castRingHom ℚ)).Nondegenerate :=
          Lattices.nondegenerate_map_of_det_ne_zero f hfdet
        obtain ⟨x, hx0, hx⟩ := isotropic_padic_of_five_le (p : ℕ) (f.map (Int.castRingHom ℚ)) hn hnd
        refine ⟨vecP e p x, fun h => hx0 ?_, ?_⟩
        · rw [vecP_eq] at h
          exact (Algebra.TensorProduct.basis ℚ_[(p : ℕ)] e).equivFun.symm.injective (by rw [h, map_zero])
        · have h1 : f.evalIn ℚ_[(p : ℕ)] x = 0 := by
            rw [← hx]; simp [QuadForm.evalIn, QuadForm.map]
          rw [f_vecP hNs hND] at h1
          have hD' : (D : ℚ_[(p : ℕ)]) ≠ 0 := by exact_mod_cast hD.ne'
          exact (mul_eq_zero.1 h1).resolve_left hD'
      obtain ⟨u₀, hu₀⟩ := hne p
      obtain ⟨L, hL, hLu⟩ := exists_list_vcomm hQp (by omega) hiso u₀
      obtain ⟨a₀, ha₀⟩ := exists_anisotropic hQp
      exact ⟨L, a₀, fun _ => ⟨hL, ha₀, u₀, hu₀, hLu⟩⟩
    · exact ⟨[], 0, fun h => absurd h hp⟩
  choose L a₀ hL using hloc
  set s : ℕ := T.sup fun p => (L p).length with hs
  -- the families of commutators
  set bP := fun p : Nat.Primes => Algebra.TensorProduct.basis ℚ_[(p : ℕ)] e
  set fam : List (∀ p : Nat.Primes, CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) :=
    (List.range s).map fun j p =>
      vprod (Q.baseChange ℚ_[(p : ℕ)]) (vcommList (Q.baseChange ℚ_[(p : ℕ)]) ((L p).getD j (a₀ p, a₀ p)).1 ((L p).getD j (a₀ p, a₀ p)).2)
    with hfam
  have hvec : ∀ (p : Nat.Primes) (x : ℚ_[(p : ℕ)] ⊗[ℚ] V), vecP e p ((bP p).equivFun x) = x := by
    intro p x; rw [vecP_eq, LinearEquiv.symm_apply_apply]
  have happrox : SpinApprox Q Λ T fun p => (fam.map fun t => t p).prod := by
    refine SpinApprox.list_prod fam fun t ht => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
    have h72 := lemma72 e hQ (by omega) he hNs hD hND hfind T hT2 hTd
      (fun p => (bP p).equivFun ((L p).getD j (a₀ p, a₀ p)).1)
      (fun p => (bP p).equivFun ((L p).getD j (a₀ p, a₀ p)).2)
      (fun p hp => by
        rw [hvec]
        obtain ⟨hLp, ha₀p, -⟩ := hL p hp
        rw [List.getD_eq_getElem?_getD]
        cases h : (L p)[j]? with
        | none => simpa using ha₀p
        | some ab => simpa using (hLp ab (List.mem_of_getElem? h)).1)
      (fun p hp => by
        rw [hvec]
        obtain ⟨hLp, ha₀p, -⟩ := hL p hp
        rw [List.getD_eq_getElem?_getD]
        cases h : (L p)[j]? with
        | none => simpa using ha₀p
        | some ab => simpa using (hLp ab (List.mem_of_getElem? h)).2)
    simpa only [hvec] using h72
  refine happrox.exists_mem U hopen (fun p hp => ?_) hTU
  obtain ⟨-, ha₀p, w, hw, hwL⟩ := hL p hp
  refine ⟨w, hw, ?_⟩
  rw [hwL, hfam, List.map_map]
  have := prod_range_getD (fun ab : (ℚ_[(p : ℕ)] ⊗[ℚ] V) × (ℚ_[(p : ℕ)] ⊗[ℚ] V) =>
      vprod (Q.baseChange ℚ_[(p : ℕ)]) (vcommList (Q.baseChange ℚ_[(p : ℕ)]) ab.1 ab.2)) (a₀ p, a₀ p)
    (vprod_vcommList_self ha₀p) (L p) s (Finset.le_sup (f := fun p => (L p).length) hp)
  rw [← this]
  rfl

end Main

end QuadFormsKB.Cassels.Thm71Five
