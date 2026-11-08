/-
# Cassels, Chapter 10, Theorem 7.1 for $n \ge 4$: the assembly

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §7, Theorem 7.1 (p. 186), proof for $n \ge 4$
(pp. 189–190).

**Proves** `spinStrongApproximation_four_le`: the field of `SpinStrongApproximation` for $\dim V \ge 4$. Cassels' proof: choose
$u^{(p)} \in \mathcal U_p$ on the finite set $T$ (bad primes, $2$, primes dividing the determinant); write
$u^{(p)} = a_1^{(p)}\cdots a_r^{(p)}$ with a common even $r$ (`exists_vprod_of_mem_spinGroup`, `exists_vprod_length`); the first stage
(`firstStage`) gives $u = a_1\cdots a_r \in \operatorname{Spin}(V)$ close to $u^{(p)}$ on $T$; $u \in \operatorname{Spin}(\Lambda_p)$ outside $T$ and
the finite set $P_2$ of primes dividing a denominator of a coordinate of an $a_j$; at $p \in P_2$ the space $V_p$ is isotropic, and
the second stage (`spinApprox_of_isotropic`) gives $v$ close to $1$ on $T$, with $uv \in \operatorname{Spin}(\Lambda_p)$ on $P_2$ and
$v \in \operatorname{Spin}(\Lambda_p)$ elsewhere. Then $uv$ lies in every $\mathcal U_p$.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71FourMain

open CliffordAlgebra TensorProduct Module Matrix Topology Filter

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Thm71Five

open QuadFormsKB.Cassels Thm71Ternary Thm71Spin Thm71Coords Thm71Approx

/-- Helper (file-local): the vector space topology on $C(V_p)$. -/
noncomputable local instance cliffTop3 {V : Type} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : TopologicalSpace (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  cliffordTopology (Q.baseChange ℚ_[p])

local instance cliffModTop3 {V : Type} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : IsModuleTopology ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) := ⟨rfl⟩

local instance cliffFin3 {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : Module.Finite ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  finiteDimensional_clifford (Q.baseChange ℚ_[p])

local instance cliffTopRing3 {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Q : QuadraticForm ℚ V) (p : ℕ) [Fact p.Prime] : IsTopologicalRing (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  IsModuleTopology.isTopologicalRing ℚ_[p] _

section Final

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

theorem ofFn_getD {α : Type*} (l : List α) (d : α) (k : ℕ) (h : l.length = k) :
    List.ofFn (fun i : Fin k => l.getD i d) = l := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ h2]

set_option maxHeartbeats 1600000 in
/-- **Cassels, Ch. 10, Theorem 7.1 for $n \ge 4$** (Strong Approximation Theorem for the Spin Group, p. 186; proof
pp. 189–190): the field of `SpinStrongApproximation` for $\dim V \ge 4$ (`hn`). Proof: Cassels' two stages (module docstring). -/
@[kb "cassels1978" "Ch. 10, Thm. 7.1, p. 186; proof for n ≥ 4, pp. 189–190"]
theorem spinStrongApproximation_four_le (Q : QuadraticForm ℚ V) (hn : 4 ≤ Module.finrank ℚ V)
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
  have hTne : T.Nonempty := ⟨⟨2, Nat.prime_two⟩, Finset.mem_subtype.2 (by simp)⟩
  set bP := fun p : Nat.Primes => Algebra.TensorProduct.basis ℚ_[(p : ℕ)] e
  have hvec : ∀ (p : Nat.Primes) (x : ℚ_[(p : ℕ)] ⊗[ℚ] V), vecP e p ((bP p).equivFun x) = x := by
    intro p x; rw [vecP_eq, LinearEquiv.symm_apply_apply]
  -- the open sets of the $\mathcal U_p$
  have hOU : ∀ p : Nat.Primes, ∃ O : Set (CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])),
      IsOpen O ∧ Subtype.val ⁻¹' O = U p := fun p => isOpen_induced_iff.1 (hopen p)
  choose O hO hOU using hOU
  have hntV : ∀ p : Nat.Primes, Nontrivial (ℚ_[(p : ℕ)] ⊗[ℚ] V) := by
    intro p
    have hfin : Module.finrank ℚ_[(p : ℕ)] (ℚ_[(p : ℕ)] ⊗[ℚ] V) = n := by
      rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℚ_[(p : ℕ)] e), Fintype.card_fin]
    exact Module.nontrivial_of_finrank_pos (R := ℚ_[(p : ℕ)]) (by rw [hfin]; omega)
  -- local data on $T$: $u^{(p)} = a_1^{(p)}\cdots a_r^{(p)}$ and neighbourhoods $W_p W'_p \subseteq \mathcal O_p$
  have hloc : ∀ p : Nat.Primes, ∃ (w : spinGroup (Q.baseChange ℚ_[(p : ℕ)])) (l : List (ℚ_[(p : ℕ)] ⊗[ℚ] V))
      (W W' : Set (CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)]))), p ∈ T →
      w ∈ U p ∧ 2 ≤ l.length ∧ Even l.length ∧ (∀ a ∈ l, Q.baseChange ℚ_[(p : ℕ)] a ≠ 0) ∧
      (w : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) = vprod (Q.baseChange ℚ_[(p : ℕ)]) l ∧ (l.map (Q.baseChange ℚ_[(p : ℕ)])).prod = 1 ∧
      IsOpen W ∧ IsOpen W' ∧ (w : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) ∈ W ∧ (1 : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) ∈ W' ∧
      ∀ x ∈ W, ∀ y ∈ W', x * y ∈ O p := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨w, hw⟩ := hne p
      have hQp := nondegenerate_baseChange e hQ ℚ_[(p : ℕ)]
      have := hntV p
      obtain ⟨l, hl2, hlev, hla, hlw, hlQ⟩ := exists_vprod_of_mem_spinGroup hQp w
      have hwO : (w : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) * 1 ∈ O p := by
        rw [mul_one]; have : w ∈ Subtype.val ⁻¹' O p := by rw [hOU]; exact hw
        exact this
      have hpre : IsOpen ((fun z : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)]) × _ => z.1 * z.2) ⁻¹' O p) :=
        (hO p).preimage continuous_mul
      obtain ⟨W, W', hW, hW', hwW, h1W', hsub⟩ := isOpen_prod_iff.1 hpre _ _ hwO
      exact ⟨w, l, W, W', fun _ => ⟨hw, hl2, hlev, hla, hlw, hlQ, hW, hW', hwW, h1W',
        fun x hx y hy => hsub (Set.mk_mem_prod hx hy)⟩⟩
    · exact ⟨1, [], ∅, ∅, fun h => absurd h hp⟩
  choose w l W W' hloc using hloc
  -- padding to the common even length $R = s + 1$
  set R : ℕ := 2 * T.sup fun p => (l p).length with hR
  obtain ⟨p₀, hp₀⟩ := hTne
  have hR2 : 2 ≤ R := by
    have h1 := (hloc p₀ hp₀).2.1
    have h2 : (l p₀).length ≤ T.sup fun p => (l p).length := Finset.le_sup (f := fun p => (l p).length) hp₀
    omega
  have hpad : ∀ p : Nat.Primes, ∃ l' : List (ℚ_[(p : ℕ)] ⊗[ℚ] V), p ∈ T → l'.length = R ∧
      (∀ a ∈ l', Q.baseChange ℚ_[(p : ℕ)] a ≠ 0) ∧ (w p : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) = vprod (Q.baseChange ℚ_[(p : ℕ)]) l' ∧
      (l'.map (Q.baseChange ℚ_[(p : ℕ)])).prod = 1 := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨-, hl2, hlev, hla, hlw, hlQ, -⟩ := hloc p hp
      have hQp := nondegenerate_baseChange e hQ ℚ_[(p : ℕ)]
      have := hntV p
      have hle : (l p).length ≤ R := by
        have : (l p).length ≤ T.sup fun p => (l p).length := Finset.le_sup (f := fun p => (l p).length) hp
        omega
      obtain ⟨l', h1, h2, h3, h4⟩ := exists_vprod_length hQp (w p) (l p) hl2 hlev hla hlw hlQ R hle
        ⟨T.sup fun p => (l p).length, by omega⟩
      exact ⟨l', fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨[], fun h => absurd h hp⟩
  choose l' hl' using hpad
  obtain ⟨s, hs⟩ : ∃ s, R = s + 1 := ⟨R - 1, by omega⟩
  set a : ∀ p : Nat.Primes, Fin (s + 1) → Fin n → ℚ_[(p : ℕ)] :=
    fun p i => (bP p).equivFun ((l' p).getD i 0) with ha
  have hofFn : ∀ p ∈ T, List.ofFn (fun i : Fin (s + 1) => vecP e p (a p i)) = l' p := by
    intro p hp
    simp only [ha, hvec]
    exact ofFn_getD _ _ _ (by rw [(hl' p hp).1, hs])
  obtain ⟨y, hyQ, hyW⟩ := firstStage e hQ hn hNs hD hND hfind T ⟨p₀, hp₀⟩ hT2 hTd s a
    (fun p hp i => by
      obtain ⟨hlen, hla, -⟩ := hl' p hp
      simp only [ha, hvec]
      rw [List.getD_eq_getElem _ _ (by rw [hlen, hs]; exact i.2)]
      exact hla _ (List.getElem_mem _))
    (fun p hp => by
      rw [← List.prod_ofFn]
      have : (List.ofFn fun i => Q.baseChange ℚ_[(p : ℕ)] (vecP e p (a p i))) =
          (l' p).map (Q.baseChange ℚ_[(p : ℕ)]) := by
        rw [← hofFn p hp, List.map_ofFn]; rfl
      rw [this]
      exact (hl' p hp).2.2.2)
    W (fun p hp => ⟨(hloc p hp).2.2.2.2.2.2.1, by
      rw [vprodP, hofFn p hp, ← (hl' p hp).2.2.1]; exact (hloc p hp).2.2.2.2.2.2.2.2.1⟩)
  -- the global element $u = a_1 \cdots a_r$
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℚ) (by rw [hn']; omega)
  have hu : vprod Q (List.ofFn fun i => vecG e (y i)) ∈ spinGroup Q := by
    refine vprod_mem_spinGroup hQ ?_ ?_
    · rw [List.length_ofFn, ← hs]; exact ⟨T.sup fun p => (l p).length, by omega⟩
    · rw [List.map_ofFn, List.prod_ofFn]; exact hyQ
  set u : spinGroup Q := ⟨_, hu⟩ with hudef
  have himg : ∀ p : Nat.Primes, (spinBaseChange ℚ_[(p : ℕ)] Q u : CliffordAlgebra _) =
      vprodP (Q := Q) e p (fun i j => (y i j : ℚ_[(p : ℕ)])) := by
    intro p
    rw [coe_spinBaseChange, ofBaseChangeAux_vprod, List.map_ofFn, vprodP]
    congr 2
    funext i
    exact one_tmul_vecG e p (y i)
  -- the finite set $P_2$ of primes outside $T$ where $u$ need not be integral
  set Bad : ℕ := ∏ i, ∏ j, (y i j).den with hBad
  have hBad0 : Bad ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => (y i j).den_nz
  set P₂ : Finset Nat.Primes := (Bad.primeFactors.subtype Nat.Prime).filter fun p => p ∉ T with hP₂
  set T' : Finset Nat.Primes := T ∪ P₂ with hT'
  have hint : ∀ p : Nat.Primes, p ∉ T' → (spinBaseChange ℚ_[(p : ℕ)] Q u : CliffordAlgebra _) ∈
      intClifford (Q.baseChange ℚ_[(p : ℕ)]) (baseChangeLat ℚ_[(p : ℕ)] ℤ_[(p : ℕ)] Λ) := by
    intro p hp
    have hpT : p ∉ T := fun h => hp (Finset.mem_union_left _ h)
    have hpB : ¬ (p : ℕ) ∣ Bad := fun h => hp (Finset.mem_union_right _ (Finset.mem_filter.2
      ⟨Finset.mem_subtype.2 (Nat.mem_primeFactors.2 ⟨p.2, h, hBad0⟩), hpT⟩))
    rw [himg, vprodP, vprod]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
    refine ι_mem_intClifford (vecP_mem e he p fun j => norm_rat_le_one _ fun h => hpB ?_)
    exact h.trans ((Finset.dvd_prod_of_mem (fun j => (y i j).den) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (y i j).den) (Finset.mem_univ i)))
  -- the second stage
  set t : ∀ p : Nat.Primes, spinGroup (Q.baseChange ℚ_[(p : ℕ)]) :=
    fun p => if p ∈ T then 1 else (spinBaseChange ℚ_[(p : ℕ)] Q u)⁻¹ with ht
  have hT2' : ∀ p : Nat.Primes, p ∉ T' → (p : ℕ) ≠ 2 :=
    fun p hp => hT2 p fun h => hp (Finset.mem_union_left _ h)
  have hTd' : ∀ p : Nat.Primes, p ∉ T' → ¬ ((p : ℕ) : ℤ) ∣ f.hessian.det :=
    fun p hp => hTd p fun h => hp (Finset.mem_union_left _ h)
  have hiso : ∀ p ∈ T', (t p : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) = 1 ∨
      ∃ x : ℚ_[(p : ℕ)] ⊗[ℚ] V, x ≠ 0 ∧ Q.baseChange ℚ_[(p : ℕ)] x = 0 := by
    intro p _
    by_cases hp : p ∈ T
    · left; simp [ht, hp]
    · right
      obtain ⟨x, hx0, hx⟩ := exists_isotropic_good f (by omega) p (hT2 p hp) (hTd p hp)
      refine ⟨vecP e p x, fun h => hx0 ?_, ?_⟩
      · rw [vecP_eq] at h
        exact (Algebra.TensorProduct.basis ℚ_[(p : ℕ)] e).equivFun.symm.injective (by rw [h, map_zero])
      · rw [f_vecP hNs hND] at hx
        have hDp : (D : ℚ_[(p : ℕ)]) ≠ 0 := by exact_mod_cast hD.ne'
        exact (mul_eq_zero.1 hx).resolve_left hDp
  have hSA := spinApprox_of_isotropic e hQ hn he hNs hD hND hfind T' hT2' hTd' t hiso
  set O' : ∀ p : Nat.Primes, Set (CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) := fun p =>
    if p ∈ T then W' p else {x | (spinBaseChange ℚ_[(p : ℕ)] Q u : CliffordAlgebra _) * x ∈
      intClifford (Q.baseChange ℚ_[(p : ℕ)]) (baseChangeLat ℚ_[(p : ℕ)] ℤ_[(p : ℕ)] Λ)} with hO'
  obtain ⟨v, hv₁, hv₂⟩ := hSA O' fun p _ => by
    by_cases hp : p ∈ T
    · simp only [hO', ht, hp, ite_true]
      exact ⟨(hloc p hp).2.2.2.2.2.2.2.1, (hloc p hp).2.2.2.2.2.2.2.2.2.1⟩
    · simp only [hO', ht, hp, ite_false]
      refine ⟨(isOpen_and_isClosed_intClifford (Q := Q.baseChange ℚ_[(p : ℕ)])
        (span_baseChangeLat e he p)).1.preimage (continuous_const.mul continuous_id), ?_⟩
      show (spinBaseChange ℚ_[(p : ℕ)] Q u : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) *
        (((spinBaseChange ℚ_[(p : ℕ)] Q u)⁻¹ : spinGroup (Q.baseChange ℚ_[(p : ℕ)])) :
          CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) ∈
        intClifford (Q.baseChange ℚ_[(p : ℕ)]) (baseChangeLat ℚ_[(p : ℕ)] ℤ_[(p : ℕ)] Λ)
      rw [← Submonoid.coe_mul, mul_inv_cancel]
      exact one_mem _
  refine ⟨u * v, fun p hp => ?_⟩
  set pp : Nat.Primes := ⟨p, hp.out⟩
  change spinBaseChange ℚ_[(pp : ℕ)] Q (u * v) ∈ U pp
  by_cases hT : pp ∈ T
  · rw [← hOU pp]
    show (spinBaseChange ℚ_[(pp : ℕ)] Q (u * v) : CliffordAlgebra (Q.baseChange ℚ_[(pp : ℕ)])) ∈ O pp
    rw [map_mul, Submonoid.coe_mul]
    refine (hloc pp hT).2.2.2.2.2.2.2.2.2.2 _ ?_ _ ?_
    · rw [himg]; exact hyW pp hT
    · have := hv₁ pp (Finset.mem_union_left _ hT)
      simpa [hO', hT] using this
  · rw [hTU pp hT]
    show (spinBaseChange ℚ_[(pp : ℕ)] Q (u * v) : CliffordAlgebra (Q.baseChange ℚ_[(pp : ℕ)])) ∈
      intClifford (Q.baseChange ℚ_[(pp : ℕ)]) (baseChangeLat ℚ_[(pp : ℕ)] ℤ_[(pp : ℕ)] Λ)
    rw [map_mul, Submonoid.coe_mul]
    by_cases hP : pp ∈ T'
    · have := hv₁ pp hP
      simpa [hO', hT] using this
    · exact mul_mem (hint pp hP) (hv₂ pp hP)

end Final

end QuadFormsKB.Cassels.Thm71Five
