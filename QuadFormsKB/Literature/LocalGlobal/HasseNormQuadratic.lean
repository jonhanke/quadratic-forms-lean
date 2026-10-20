/-
# Quadratic extensions $F(\sqrt a)$: Galois structure and local norms

Two facts about $L = F(\sqrt a)$ used by our proof of the Hasse norm theorem for quadratic extensions
(`HasseNorm/Main.lean`); split out of the Yamaguchi-based `HasseNormBridge.lean` (now archived in
`archive/yamaguchi/`), which also used them.

For $a \in F^\times$ not a square, $L = F(\sqrt a)$ is cyclic of degree 2, and for any field $M \supseteq F$,
$b$ is a norm from $M \otimes_F L$ iff $(a, b)_M = 1$: in the basis $1, s$ ($s^2 = a$) the norm of
$x_0 + x_1 s$ is $x_0^2 - a x_1^2$, and $(a,b)_M = 1$ iff $b = x_0^2 - a x_1^2$ has a solution
(`hilbertSymbol_eq_one_iff_conic`, with $z^2 = a x^2 + b y^2$ rearranged).
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNF

open NumberField

namespace QuadFormsKB.HasseNorm

variable {F : Type} [Field F] [NumberField F]

/-- **$F(\sqrt a)$ is a cyclic Galois extension** (degree 2): for $a \in F$ not a square and $L = F + Fs$
with $s^2 = a$, $L/F$ is finite-dimensional and Galois, and its Galois group is cyclic (of order 2). -/
@[kb "lam2005" "Ch. VI §3 [unverified]"]
theorem quadExt_cyclic {L : Type} [Field L] [NumberField L] [Algebra F L] (a : F) (hd : ¬ IsSquare a)
    (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s) :
    ∃ _ : FiniteDimensional F L, IsGalois F L ∧ IsCyclic (L ≃ₐ[F] L) := by
  classical
  have htop : Submodule.span F ((({1, s} : Finset L)) : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    have h1 : (algebraMap F L b₀) = b₀ • (1 : L) := by rw [Algebra.smul_def, mul_one]
    have h2 : (algebraMap F L b₁) * s = b₁ • s := by rw [Algebra.smul_def]
    rw [h1, h2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hfin : FiniteDimensional F L := ⟨⟨{1, s}, htop⟩⟩
  have hle : Module.finrank F L ≤ 2 := by
    rw [← finrank_top, ← htop]
    exact (finrank_span_finset_le_card ({1, s} : Finset L)).trans (Finset.card_le_two)
  have hne : Module.finrank F L ≠ 1 := by
    intro h1
    have := Subalgebra.bot_eq_top_of_finrank_eq_one h1
    have hs' : s ∈ (⊥ : Subalgebra F L) := this ▸ Algebra.mem_top
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hs'
    apply hd
    refine ⟨c, ?_⟩
    apply (algebraMap F L).injective
    rw [map_mul, hc, ← hs, sq]
  have hpos : 0 < Module.finrank F L := Module.finrank_pos
  have h2 : Module.finrank F L = 2 := by omega
  have : Algebra.IsQuadraticExtension F L := ⟨h2⟩
  have := Algebra.IsQuadraticExtension.normal F L
  have hG : IsGalois F L := IsGalois.mk
  refine ⟨hfin, hG, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCyclic_of_prime_card (p := 2) (by rw [IsGalois.card_aut_eq_finrank, h2])

/-- **Norms from $M \otimes_F F(\sqrt a)$ and the Hilbert symbol** (the key computation): for any field
$M$ that is an $F$-algebra of characteristic $0$, and $b \in F^\times$: $b$ (in $M$) is the norm of a unit
of $M \otimes_F L$ iff $(a, b)_M = 1$.

*Proof.* $M \otimes_F L$ has $M$-basis $1 \otimes 1, 1 \otimes s$ (from `hspan` and $[L:F] = 2$); multiplication
by $y = x_0 + x_1 s$ has matrix $\begin{pmatrix} x_0 & a x_1 \\ x_1 & x_0 \end{pmatrix}$, so
`Algebra.norm M y` $= x_0^2 - a x_1^2$; $y$ is a unit iff its norm is nonzero. Conclude with the conic
criterion `hilbertSymbol_eq_one_iff_conic` and $(a, b) = (b, a)$. -/
@[kb "serre1973" "Ch. III §1.1, Prop. 1 [unverified]"]
theorem norm_tensor_iff_hilbert {L : Type} [Field L] [NumberField L] [Algebra F L] (a : F)
    (hd : ¬ IsSquare a) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (M : Type) [Field M] [CharZero M] [Algebra F M] (b : F) (hb : b ≠ 0) :
    (∃ y : (TensorProduct F M L)ˣ, Algebra.norm M (y : TensorProduct F M L) = algebraMap F M b) ↔
      hilbertSymbol M (algebraMap F M a) (algebraMap F M b) = 1 := by
  classical
  have hinj := (algebraMap F L).injective
  have hli : LinearIndependent F ![(1:L), s] := by
    rw [LinearIndependent.pair_iff]
    intro c₀ c₁ h
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
    by_cases h1 : c₁ = 0
    · subst h1; simp at h; exact ⟨h, rfl⟩
    · exfalso; apply hd
      refine ⟨-c₀ / c₁, ?_⟩
      apply hinj
      have h1' : algebraMap F L c₁ ≠ 0 := by simpa using h1
      have hs' : s = algebraMap F L (-c₀ / c₁) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      rw [← hs, hs', map_mul, sq]
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1:L), s]) := by
    intro y _
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![b₀, b₁], ?_⟩
    simp [Fin.sum_univ_two, Algebra.smul_def]
  let bL := Module.Basis.mk hli hsp
  let bT := Algebra.TensorProduct.basis M bL
  set t : TensorProduct F M L := (1 : M) ⊗ₜ[F] s with ht
  set α := algebraMap F M a with hα
  have ht2 : t * t = algebraMap M _ α := by
    rw [ht, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← sq, hs, hα, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := L) a, Algebra.algebraMap_eq_smul_one (A := M) a, ← TensorProduct.smul_tmul]
    simp
  have hb0 : bT 0 = 1 := by simp [bT, bL, Algebra.TensorProduct.one_def]
  have hb1 : bT 1 = t := by simp [bT, bL, ht]
  have hrepr : ∀ c₀ c₁ : M, ∀ i, bT.repr (algebraMap M _ c₀ + algebraMap M _ c₁ * t) i = ![c₀, c₁] i := by
    intro c₀ c₁ i
    have : algebraMap M _ c₀ + algebraMap M _ c₁ * t = c₀ • bT 0 + c₁ • bT 1 := by
      rw [hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [this]
    fin_cases i <;> simp
  have hnorm : ∀ x₀ x₁ : M, Algebra.norm M (algebraMap M _ x₀ + algebraMap M _ x₁ * t) = x₀ ^ 2 - α * x₁ ^ 2 := by
    intro x₀ x₁
    rw [Algebra.norm_eq_matrix_det bT, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one]
    have : (algebraMap M _ x₀ + algebraMap M _ x₁ * t) * t = algebraMap M _ (α * x₁) + algebraMap M _ x₀ * t := by
      rw [map_mul]; linear_combination (algebraMap M _ x₁) * ht2
    rw [this, hrepr, hrepr, hrepr, hrepr]
    simp; ring
  have hspanT : ∀ y : TensorProduct F M L, ∃ x₀ x₁ : M, y = algebraMap M _ x₀ + algebraMap M _ x₁ * t := by
    intro y
    refine ⟨bT.repr y 0, bT.repr y 1, ?_⟩
    conv_lhs => rw [← bT.sum_repr y]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
  set β := algebraMap F M b with hβ
  have hβ0 : β ≠ 0 := by simpa [hβ] using hb
  have ha0 : a ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
  have hα0 : α ≠ 0 := by simpa [hα] using ha0
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x₀, x₁, hyx⟩ := hspanT y
    rw [hyx, hnorm] at hy
    unfold hilbertSymbol
    exact if_pos ⟨x₁, 1, x₀, fun h => by simp [Prod.ext_iff] at h, by linear_combination hy⟩
  · intro h
    unfold hilbertSymbol at h
    split_ifs at h with hex
    all_goals try norm_num at h
    obtain ⟨x, y, z, hne, hz⟩ := hex
    have hx : ∃ x₀ x₁ : M, x₀ ^ 2 - α * x₁ ^ 2 = β := by
      by_cases hy : y = 0
      · subst hy
        have hx0 : x ≠ 0 := by
          rintro rfl
          simp at hz
          exact hne (by simp [hz])
        have hz0 : z ≠ 0 := by
          rintro rfl
          simp at hz
          rcases hz with h | h
          · exact hα0 h
          · exact hx0 h
        have hz' : α * x ^ 2 = z ^ 2 := by linear_combination -hz
        have h1 : α * (x / z) ^ 2 = 1 := by
          field_simp
          linear_combination hz'
        refine ⟨(1 + β) / 2, (β - 1) / 2 * (x / z), ?_⟩
        linear_combination (-((β - 1) / 2) ^ 2) * h1
      · refine ⟨z / y, x / y, ?_⟩
        field_simp
        linear_combination hz
    obtain ⟨x₀, x₁, hx⟩ := hx
    let e : TensorProduct F M L := algebraMap M _ x₀ + algebraMap M _ x₁ * t
    let e' : TensorProduct F M L := algebraMap M _ β⁻¹ * (algebraMap M _ x₀ - algebraMap M _ x₁ * t)
    have key : algebraMap M (TensorProduct F M L) x₀ ^ 2 - algebraMap M (TensorProduct F M L) x₁ ^ 2 * algebraMap M _ α = algebraMap M _ β := by
      rw [← hx]; simp only [map_sub, map_mul, map_pow]; ring
    have hinvβ : algebraMap M (TensorProduct F M L) β⁻¹ * algebraMap M _ β = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hβ0, map_one]
    have hee : e * e' = 1 := by
      simp only [e, e']
      linear_combination (-(algebraMap M (TensorProduct F M L) β⁻¹ * algebraMap M _ x₁ ^ 2)) * ht2 + algebraMap M (TensorProduct F M L) β⁻¹ * key + hinvβ
    exact ⟨Units.mkOfMulEqOne e e' hee, by simp only [Units.val_mkOfMulEqOne, e, hnorm, hx]⟩

end QuadFormsKB.HasseNorm
