/-
# Optimal embeddings and embedding numbers (Voight, Chapter 30)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Definition 30.3.2 (p. 546),
30.3.10-30.3.12 (pp. 546-547), Theorem 30.4.7 (p. 548), Proposition 30.5.3 (p. 552), Proposition 30.6.12 and
Lemma 30.6.16 (pp. 556-557), (30.7.2) and Theorem 30.7.3 (p. 559).

**Setting (general part).** $R$ is a commutative ring with fraction field $F$ (any field $F$ with an $R$-algebra
structure is allowed in the definitions), $B$ an $F$-algebra, $\mathcal O \subseteq B$ an $R$-subalgebra (in the book a
quaternion $R$-order), $S$ a commutative $R$-algebra (in the book a quadratic $R$-order in a separable quadratic
$F$-algebra $K$, with $K = FS$). An $R$-algebra embedding $\varphi : S \to \mathcal O$ extends to $K = FS$, with image
$\varphi(K) = F\varphi(S)$, the $F$-span of $\varphi(S)$; this is how $\varphi(K)$ is written below, so that $K$ does not
have to be named.

**Contents.**
* `IsOptimalEmbedding F O φ` (Definition 30.3.2): $\varphi$ is injective, $\varphi(S) \subseteq \mathcal O$ and
  $\varphi(K) \cap \mathcal O = \varphi(S)$.
* `OptEmb F S O` $= \operatorname{Emb}_R(S, \mathcal O)$ (30.3.3), `embSetoid` (conjugation by a subgroup
  $\Gamma \le \mathcal O^\times$, 30.3.10) and `embNum F S O Γ` $= m(S, \mathcal O; \Gamma)$ (30.3.11-30.3.12), the number of
  $\Gamma$-conjugacy classes of optimal embeddings.
* `companionEmb` and `embNum_matOrder` (**Proposition 30.5.3 (a)**, proved): for $R$ a discrete valuation ring and
  $S = R[\gamma]$ free with basis $1, \gamma$, $m(S, \mathrm M_2(R); \mathrm{GL}_2(R)) = 1$.
* `LocalEmbNumEichler R K π` (**Proposition 30.6.12**, stated): the local embedding numbers of the standard Eichler order
  $\mathcal O_0(\pi^e)$, $e \ge 1$, in terms of the roots of $f_\gamma$ modulo $\pi^e$ and $\pi^{e+1}$.
* `LocalEmbNumEichlerOne R K π` (**Lemma 30.6.16**, stated): for $e = 1$ and $S$ integrally closed,
  $m(S, \mathcal O_0(\pi); \mathcal O_0(\pi)^\times) = 1 + (K \mid \mathfrak p)$.
* `rightOrder`, `TraceFormulaEmb F` (**Theorem 30.4.7 with (30.7.2), i.e. Theorem 30.7.3**, stated): for a quaternion
  order $\mathcal O$ over a number field and a quadratic order $S$ embedding in $B$,
  $\sum_{[J] \in \operatorname{Cls}\mathcal O} m(S, \mathcal O_R(J); \mathcal O_R(J)^\times) = h(S)\prod_{\mathfrak p} m(S_{\mathfrak p}, \mathcal O_{\mathfrak p};
  \mathcal O_{\mathfrak p}^\times)$.

**Conventions.** Matrix entries are indexed $0, 1$. Ideal classes are classes of nonzero integral left ideals $J$ of
$\mathcal O$ under $J \sim J\beta$ (`QuatOrder.idealSetoid`, as in `Voight/MassFormula.lean`); Voight uses right ideals
$I$ and their left orders $\mathcal O_L(I)$, and the standard involution exchanges the two conventions, so the left order
of a right ideal becomes the right order $\mathcal O_R(J) = \{x \in B : Jx \subseteq J\}$ of a left ideal here.
-/
import QuadFormsKB.Literature.Voight.Wave3.EichlerLocal
import QuadFormsKB.Literature.Voight.MassFormula

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave4

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3

/-! ### Optimal embeddings and embedding numbers -/

section General

variable (R F : Type*) {B : Type*} (S : Type*) [CommRing R] [Field F] [Algebra R F] [Ring B] [Algebra F B]
  [Algebra R B] [IsScalarTower R F B] [CommRing S] [Algebra R S]

/-- **Optimal embedding** (Voight 2021, Definition 30.3.2): an $R$-algebra embedding $\varphi : S \to \mathcal O$ is optimal
if $\varphi(K) \cap \mathcal O = \varphi(S)$, where $\varphi(K) = F\varphi(S)$ is the $F$-span of the image ($K = FS$). Here
$\varphi$ is an $R$-algebra map $S \to B$; the three fields say that $\varphi$ is injective (an embedding), that
$\varphi(S) \subseteq \mathcal O$, and that every element of $\mathcal O$ in the $F$-span of $\varphi(S)$ lies in $\varphi(S)$. -/
@[kb "voight2021" "Definition 30.3.2, p. 546"]
structure IsOptimalEmbedding (O : Subalgebra R B) (φ : S →ₐ[R] B) : Prop where
  /-- $\varphi$ is injective. -/
  injective : Function.Injective φ
  /-- $\varphi(S) \subseteq \mathcal O$. -/
  mem : ∀ s, φ s ∈ O
  /-- $\varphi(K) \cap \mathcal O \subseteq \varphi(S)$. -/
  optimal : ∀ x ∈ O, x ∈ Submodule.span F (Set.range φ) → x ∈ Set.range φ

/-- **The set of optimal embeddings** $\operatorname{Emb}_R(S, \mathcal O)$ (Voight 2021, (30.3.3)). -/
@[kb "voight2021" "(30.3.3), p. 546"]
def OptEmb (O : Subalgebra R B) : Type _ := {φ : S →ₐ[R] B // IsOptimalEmbedding R F S O φ}

variable {R S}

/-- $\Gamma$-conjugacy of embeddings (Voight 2021, 30.3.10): $\psi = \gamma^{-1}\varphi\gamma$ for some $\gamma \in \Gamma$. -/
def ConjBy {O : Subalgebra R B} (Γ : Subgroup Oˣ) (φ ψ : S →ₐ[R] B) : Prop :=
  ∃ γ ∈ Γ, ∀ s, ψ s = ((↑(γ⁻¹ : Oˣ) : O) : B) * φ s * ((↑(γ : Oˣ) : O) : B)

/-- **$\Gamma$-conjugacy classes of optimal embeddings** (Voight 2021, 30.3.10-30.3.11), for a subgroup
$\Gamma \le \mathcal O^\times$ acting by $\varphi \mapsto \gamma^{-1}\varphi\gamma$. -/
def embSetoid (O : Subalgebra R B) (Γ : Subgroup Oˣ) : Setoid (OptEmb R F S O) where
  r φ ψ := ConjBy Γ φ.1 ψ.1
  iseqv := by
    refine ⟨fun φ => ⟨1, Γ.one_mem, fun s => by simp⟩, ?_, ?_⟩
    · rintro φ ψ ⟨γ, hγ, h⟩
      refine ⟨γ⁻¹, Γ.inv_mem hγ, fun s => ?_⟩
      rw [h s, inv_inv]
      simp only [← mul_assoc, ← Subalgebra.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Subalgebra.coe_one, one_mul]
      rw [mul_assoc, ← Subalgebra.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subalgebra.coe_one,
        mul_one]
    · rintro φ ψ χ ⟨γ, hγ, h⟩ ⟨δ, hδ, h'⟩
      refine ⟨γ * δ, Γ.mul_mem hγ hδ, fun s => ?_⟩
      rw [h' s, h s, _root_.mul_inv_rev]
      simp only [Units.val_mul, Subalgebra.coe_mul, mul_assoc]

variable (S)

/-- **The embedding number** $m(S, \mathcal O; \Gamma) = \#\operatorname{Emb}(S, \mathcal O; \Gamma)$ (Voight 2021, (30.3.11),
(30.3.12)): the number of $\Gamma$-conjugacy classes of optimal embeddings $S \to \mathcal O$ (`Nat.card`, so $0$ if
infinite; it is finite by Corollary 30.5.5). -/
@[kb "voight2021" "(30.3.12), p. 547"]
def embNum (O : Subalgebra R B) (Γ : Subgroup Oˣ) : ℕ := Nat.card (Quotient (embSetoid F (S := S) O Γ))

end General

/-! ### Proposition 30.5.3 (a): the maximal order $\mathrm M_2(R)$ -/

section Matrix

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  {S : Type*} [CommRing S] [Algebra R S]

/-- The entrywise map $\mathrm M_2(R) \to \mathrm M_2(F)$ induced by $R \to F$, as an $R$-algebra homomorphism; its range
is `matOrder R F`. -/
def matMap (R F : Type*) [CommRing R] [Field F] [Algebra R F] :
    Matrix (Fin 2) (Fin 2) R →ₐ[R] Matrix (Fin 2) (Fin 2) F :=
  AlgHom.mapMatrix (Algebra.ofId R F)

theorem matMap_apply (X : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    matMap R F X i j = algebraMap R F (X i j) := rfl

theorem matMap_injective : Function.Injective (matMap R F) := by
  intro X Y h
  ext i j
  exact IsFractionRing.injective R F (by simpa [matMap_apply] using congrFun (congrFun h i) j)

/-- The companion matrix $\begin{pmatrix} 0 & p \\ 1 & t\end{pmatrix}$ of $x^2 = tx + p$ (with $p = -n_\gamma$,
$t = t_\gamma$ in the notation of Voight (30.5.4)). -/
def compMat (p t : R) : Matrix (Fin 2) (Fin 2) R := !![0, p; 1, t]

theorem compMat_mul_self (p t : R) : compMat p t * compMat p t = t • compMat p t + p • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

/-- The coordinates of $\gamma^2$ in the basis $1, \gamma$ (with $\gamma = b_1$). -/
theorem basis_sq (b : Module.Basis (Fin 2) R S) :
    b 1 * b 1 = b.repr (b 1 * b 1) 0 • b 0 + b.repr (b 1 * b 1) 1 • b 1 := by
  have := b.sum_repr (b 1 * b 1)
  rw [Fin.sum_univ_two] at this
  exact this.symm

/-- An $R$-algebra map out of $S$ is determined by the images of the basis:
$\psi(s) = s_0\psi(b_0) + s_1\psi(b_1)$. -/
theorem alg_apply {B : Type*} [Ring B] [Algebra R B] (b : Module.Basis (Fin 2) R S) (ψ : S →ₐ[R] B) (s : S) :
    ψ s = b.repr s 0 • ψ (b 0) + b.repr s 1 • ψ (b 1) := by
  have := congrArg ψ (b.sum_repr s)
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul] at this
  exact this.symm

/-- $F\psi(S) = F + F\psi(\gamma)$ for $S$ with basis $1, \gamma$. -/
theorem span_range_eq {B : Type*} [Ring B] [Algebra R B] [Algebra F B] [IsScalarTower R F B]
    (b : Module.Basis (Fin 2) R S) (hb : b 0 = 1) (ψ : S →ₐ[R] B) :
    Submodule.span F (Set.range ψ) = Submodule.span F {1, ψ (b 1)} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    rw [alg_apply b ψ s, hb, map_one ψ, ← algebraMap_smul F (b.repr s 0) (1 : B),
      ← algebraMap_smul F (b.repr s 1) (ψ (b 1))]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · refine Submodule.span_le.2 ?_
    rintro _ (rfl | rfl)
    · exact Submodule.subset_span ⟨1, map_one ψ⟩
    · exact Submodule.subset_span ⟨_, rfl⟩

/-- The $R$-linear map $S \to \mathrm M_2(F)$ with $1 \mapsto 1$, $\gamma \mapsto C$ (companion matrix). -/
def companionLin (F : Type*) [Field F] [Algebra R F] (b : Module.Basis (Fin 2) R S) (p t : R) :
    S →ₗ[R] Matrix (Fin 2) (Fin 2) F :=
  b.constr R (![1, matMap R F (compMat p t)] : Fin 2 → Matrix (Fin 2) (Fin 2) F)

omit [IsFractionRing R F] in
theorem companionLin_b0(b : Module.Basis (Fin 2) R S) (p t : R) :
    companionLin F b p t (b 0) = 1 := by
  simp [companionLin, Module.Basis.constr_basis]

omit [IsFractionRing R F] in
theorem companionLin_b1(b : Module.Basis (Fin 2) R S) (p t : R) :
    companionLin F b p t (b 1) = matMap R F (compMat p t) := by
  simp [companionLin, Module.Basis.constr_basis]

omit [IsFractionRing R F] in
theorem companionLin_mul(b : Module.Basis (Fin 2) R S) (hb : b 0 = 1) (p t : R)
    (h : b 1 * b 1 = p • b 0 + t • b 1) (x y : S) :
    companionLin F b p t (x * y) = companionLin F b p t x * companionLin F b p t y := by
  have key : (LinearMap.mul R S).compr₂ (companionLin F b p t) =
      (LinearMap.mul R (Matrix (Fin 2) (Fin 2) F)).compl₁₂ (companionLin F b p t) (companionLin F b p t) := by
    refine b.ext fun i => b.ext fun j => ?_
    have h1 : companionLin F b p t 1 = 1 := by rw [← hb, companionLin_b0]
    fin_cases i <;> fin_cases j
    · simp [hb, h1, companionLin_b0]
    · simp [hb, h1, companionLin_b0, companionLin_b1]
    · simp [hb, h1, companionLin_b0, companionLin_b1]
    · simp only [Fin.mk_one, Fin.zero_eta, LinearMap.compr₂_apply, LinearMap.mul_apply',
        LinearMap.compl₁₂_apply, h, map_add, map_smul, companionLin_b0, companionLin_b1,
        ← map_mul, compMat_mul_self, map_one]
      rw [add_comm]
  exact LinearMap.congr_fun₂ key x y

/-- **The companion embedding** (the regular representation (30.5.4) of Voight 2021): for $S$ with $R$-basis
$1, \gamma$ and $\gamma^2 = p + t\gamma$, the $R$-algebra map $S \to \mathrm M_2(F)$ with
$\gamma \mapsto \begin{pmatrix} 0 & p \\ 1 & t\end{pmatrix}$. -/
def companionEmb (F : Type*) [Field F] [Algebra R F] (b : Module.Basis (Fin 2) R S) (hb : b 0 = 1) (p t : R)
    (h : b 1 * b 1 = p • b 0 + t • b 1) : S →ₐ[R] Matrix (Fin 2) (Fin 2) F :=
  AlgHom.ofLinearMap (companionLin F b p t) (by rw [← hb, companionLin_b0])
    (companionLin_mul b hb p t h)

theorem companionEmb_b0 (b : Module.Basis (Fin 2) R S) (hb : b 0 = 1) (p t : R)
    (h : b 1 * b 1 = p • b 0 + t • b 1) : companionEmb F b hb p t h (b 0) = 1 := by
  rw [hb, map_one]

theorem companionEmb_b1 (b : Module.Basis (Fin 2) R S) (hb : b 0 = 1) (p t : R)
    (h : b 1 * b 1 = p • b 0 + t • b 1) :
    companionEmb F b hb p t h (b 1) = matMap R F (compMat p t) :=
  companionLin_b1 b p t

theorem companionEmb_apply (b : Module.Basis (Fin 2) R S) (hb : b 0 = 1) (p t : R)
    (h : b 1 * b 1 = p • b 0 + t • b 1) (s : S) :
    companionEmb F b hb p t h s = matMap R F (b.repr s 0 • 1 + b.repr s 1 • compMat p t) := by
  rw [alg_apply b _ s, companionEmb_b0, companionEmb_b1, map_add, map_smul, map_smul, map_one (matMap R F)]

/-- The companion embedding is an optimal embedding of $S$ into $\mathrm M_2(R)$. -/
theorem companionEmb_isOptimal (b : Module.Basis (Fin 2) R S) (hb : b 0 = 1) (p t : R)
    (h : b 1 * b 1 = p • b 0 + t • b 1) :
    IsOptimalEmbedding R F S (matOrder R F) (companionEmb F b hb p t h) where
  injective := by
    intro s s' hh
    rw [companionEmb_apply, companionEmb_apply] at hh
    have hh := matMap_injective hh
    have h00 := congrFun (congrFun hh 0) 0
    have h10 := congrFun (congrFun hh 1) 0
    simp [compMat] at h00 h10
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    fin_cases i
    · exact h00
    · exact h10
  mem s := by
    rw [companionEmb_apply]
    exact ⟨_, rfl⟩
  optimal := by
    intro x hx hxs
    rw [span_range_eq b hb, companionEmb_b1, Submodule.mem_span_pair] at hxs
    obtain ⟨u, v, rfl⟩ := hxs
    obtain ⟨X, hX⟩ := hx
    have hX : matMap R F X = u • 1 + v • matMap R F (compMat p t) := hX
    have h10 := congrFun (congrFun hX 1) 0
    have h00 := congrFun (congrFun hX 0) 0
    simp [matMap_apply, compMat] at h10 h00
    refine ⟨X 0 0 • b 0 + X 1 0 • b 1, ?_⟩
    rw [map_add, map_smul, map_smul, companionEmb_b0, companionEmb_b1, ← h10, ← h00,
      algebraMap_smul, algebraMap_smul]

/-- Pure matrix algebra: if $M^2 = tM + p$ and $q(x) = M_{10}x_0^2 + (M_{11} - M_{00})x_0x_1 - M_{01}x_1^2 =
\det(x \mid Mx)$ is a unit, then $M$ is $\mathrm{GL}_2(R)$-conjugate to the companion matrix. -/
theorem conj_companion_aux {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (p t : R)
    (hM : M * M = t • M + p • 1) (x1 x2 : R)
    (hu : IsUnit (M 1 0 * x1 ^ 2 + (M 1 1 - M 0 0) * x1 * x2 - M 0 1 * x2 ^ 2)) :
    ∃ A A' : Matrix (Fin 2) (Fin 2) R, A * A' = 1 ∧ A' * A = 1 ∧ A' * M * A = compMat p t := by
  have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = t * M 0 0 + p := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 0) 0
  have e01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 = t * M 0 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 0) 1
  have e10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = t * M 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 1) 0
  have e11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = t * M 1 1 + p := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 1) 1
  set α : Matrix (Fin 2) (Fin 2) R :=
    !![x1, M 0 0 * x1 + M 0 1 * x2; x2, M 1 0 * x1 + M 1 1 * x2] with hα
  have hdet : α.det = M 1 0 * x1 ^ 2 + (M 1 1 - M 0 0) * x1 * x2 - M 0 1 * x2 ^ 2 := by
    simp [hα, Matrix.det_fin_two]; ring
  have hMα : M * α = α * compMat p t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hα, compMat, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination x1 * e00 + x2 * e01
    · linear_combination x1 * e10 + x2 * e11
  obtain ⟨u, hu'⟩ := hu
  rw [← hdet] at hu'
  have h1 : α * ((↑u⁻¹ : R) • α.adjugate) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, ← hu', smul_smul, Units.inv_mul, one_smul]
  have h2 : ((↑u⁻¹ : R) • α.adjugate) * α = 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, ← hu', smul_smul, Units.inv_mul, one_smul]
  refine ⟨α, (↑u⁻¹ : R) • α.adjugate, h1, h2, ?_⟩
  rw [mul_assoc, hMα, ← mul_assoc, h2, one_mul]

/-- **Every optimal embedding into $\mathrm M_2(R)$ is $\mathrm{GL}_2(R)$-conjugate to the companion embedding**
($R$ a discrete valuation ring). -/
theorem exists_conj_companion [IsDiscreteValuationRing R] (b : Module.Basis (Fin 2) R S) (hb : b 0 = 1) (p t : R)
    (h : b 1 * b 1 = p • b 0 + t • b 1) (ψ : S →ₐ[R] Matrix (Fin 2) (Fin 2) F)
    (hψ : IsOptimalEmbedding R F S (matOrder R F) ψ) :
    ∃ A A' : Matrix (Fin 2) (Fin 2) R, A * A' = 1 ∧ A' * A = 1 ∧
      ∀ s, companionEmb F b hb p t h s = matMap R F A' * ψ s * matMap R F A := by
  obtain ⟨M0, hM0⟩ := hψ.mem (b 1)
  have hM0 : matMap R F M0 = ψ (b 1) := hM0
  have h2 : ψ (b 1) * ψ (b 1) = p • (1 : Matrix (Fin 2) (Fin 2) F) + t • ψ (b 1) := by
    rw [← map_mul, h, map_add, map_smul, map_smul, hb, map_one]
  have hsq : M0 * M0 = t • M0 + p • 1 := by
    apply matMap_injective (R := R) (F := F)
    rw [map_mul, map_add, map_smul, map_smul, map_one, hM0, h2, add_comm]
  -- one of the three entries is a unit
  have hunit : IsUnit (M0 1 0) ∨ IsUnit (M0 0 1) ∨ IsUnit (M0 1 1 - M0 0 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hc, hb', he⟩ := hcon
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ
    have hdvd : ∀ x : R, ¬ IsUnit x → π ∣ x := fun x hx => by
      have : x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).2 hx
      rwa [hmax, Ideal.mem_span_singleton] at this
    obtain ⟨c', hc'⟩ := hdvd _ hc
    obtain ⟨b'', hb''⟩ := hdvd _ hb'
    obtain ⟨e'', he''⟩ := hdvd _ he
    have hMZ : M0 = M0 0 0 • 1 + π • !![0, b''; c', e''] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
      · exact hb''
      · exact hc'
      · linear_combination he''
    have hMz : ψ (b 1) = M0 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) + π • matMap R F !![0, b''; c', e''] := by
      have := congrArg (matMap R F) hMZ
      rw [map_add, map_smul, map_smul, map_one (matMap R F)] at this
      rw [← hM0]
      exact this
    have hπ0 : algebraMap R F π ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
    have hzspan : matMap R F !![0, b''; c', e''] ∈ Submodule.span F (Set.range ψ) := by
      have : matMap R F !![0, b''; c', e''] =
          (algebraMap R F π)⁻¹ • (ψ (b 1) - algebraMap R F (M0 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)) := by
        rw [hMz, algebraMap_smul, add_sub_cancel_left, ← algebraMap_smul F π, inv_smul_smul₀ hπ0]
      rw [this, span_range_eq b hb]
      refine Submodule.smul_mem _ _ (sub_mem (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    obtain ⟨s, hs⟩ := hψ.optimal _ ⟨_, rfl⟩ hzspan
    have hs : ψ s = matMap R F !![0, b''; c', e''] := hs
    have e : ψ s = b.repr s 0 • (1 : Matrix (Fin 2) (Fin 2) F) + b.repr s 1 • ψ (b 1) := by
      rw [alg_apply b ψ s, hb, map_one ψ]
    rw [← hs, e] at hMz
    have h3 : ψ (b 1) = ψ ((M0 0 0 + π * b.repr s 0) • b 0 + (π * b.repr s 1) • b 1) := by
      rw [map_add, map_smul, map_smul, hb, map_one ψ]
      conv_lhs => rw [hMz]
      simp only [smul_add, add_smul, smul_smul]
      abel
    have h4 := congrArg (fun v => b.repr v 1) (hψ.injective h3)
    simp at h4
    exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨_, h4.symm⟩)
  -- choose x
  have hq : ∃ x1 x2 : R, IsUnit (M0 1 0 * x1 ^ 2 + (M0 1 1 - M0 0 0) * x1 * x2 - M0 0 1 * x2 ^ 2) := by
    by_cases hc : IsUnit (M0 1 0)
    · exact ⟨1, 0, by simpa using hc⟩
    by_cases hb' : IsUnit (M0 0 1)
    · exact ⟨0, 1, by simpa using hb'.neg⟩
    have he : IsUnit (M0 1 1 - M0 0 0) := hunit.resolve_left hc |>.resolve_left hb'
    refine ⟨1, 1, ?_⟩
    by_contra hcon
    have : M0 1 1 - M0 0 0 ∈ nonunits R := by
      have h1 : M0 1 0 * 1 ^ 2 + (M0 1 1 - M0 0 0) * 1 * 1 - M0 0 1 * 1 ^ 2 ∈ nonunits R := hcon
      have h2 : (M0 1 1 - M0 0 0) = (M0 1 0 * 1 ^ 2 + (M0 1 1 - M0 0 0) * 1 * 1 - M0 0 1 * 1 ^ 2)
          + (-M0 1 0) + M0 0 1 := by ring
      rw [h2]
      exact IsLocalRing.nonunits_add (IsLocalRing.nonunits_add h1 (by simpa using hc))
        (by simpa using hb')
    exact this he
  obtain ⟨x1, x2, hu⟩ := hq
  obtain ⟨A, A', hAA', hA'A, hconj⟩ := conj_companion_aux M0 p t hsq x1 x2 hu
  refine ⟨A, A', hAA', hA'A, fun s => ?_⟩
  have key : (companionEmb F b hb p t h).toLinearMap =
      (LinearMap.mulLeft R (matMap R F A')).comp
        ((LinearMap.mulRight R (matMap R F A)).comp ψ.toLinearMap) := by
    refine b.ext fun i => ?_
    fin_cases i
    · simp [hb, ← map_mul, hA'A]
    · simp only [Fin.mk_one, Fin.zero_eta, AlgHom.toLinearMap_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply, companionEmb_b1, ← hM0, ← map_mul]
      rw [← mul_assoc, hconj]
  have := LinearMap.congr_fun key s
  simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply] at this
  rw [this, mul_assoc]

/-- **$m(S, \mathrm M_2(R); \mathrm{GL}_2(R)) = 1$** (Voight 2021, Proposition 30.5.3 (a)): over a discrete valuation ring
$R$ with fraction field $F$, for $S = R[\gamma]$ free with $R$-basis $1, \gamma$ (30.5.1), all optimal embeddings
$S \to \mathrm M_2(R)$ are $\mathrm{GL}_2(R)$-conjugate, and there is one (the regular representation (30.5.4),
$\gamma \mapsto \begin{pmatrix} 0 & -n_\gamma \\ 1 & t_\gamma\end{pmatrix}$). Here $\mathrm M_2(R)$ is `matOrder R F` and
$\mathrm{GL}_2(R)$ its unit group. The book assumes $K = FS$ separable and $R$ complete; the proof uses neither. -/
@[kb "voight2021" "Proposition 30.5.3, p. 552"]
theorem embNum_matOrder [IsDiscreteValuationRing R] (b : Module.Basis (Fin 2) R S) (hb : b 0 = 1) :
    embNum F S (matOrder R F) ⊤ = 1 := by
  obtain ⟨p, t, h⟩ : ∃ p t : R, b 1 * b 1 = p • b 0 + t • b 1 := ⟨_, _, basis_sq b⟩
  have hφ₀ := companionEmb_isOptimal (F := F) b hb p t h
  have key : ∀ ψ : OptEmb R F S (matOrder R F),
      (Quotient.mk (embSetoid F (S := S) (matOrder R F) ⊤) ψ) =
        Quotient.mk (embSetoid F (S := S) (matOrder R F) ⊤) ⟨companionEmb F b hb p t h, hφ₀⟩ := by
    intro ψ
    obtain ⟨A, A', hAA', hA'A, hconj⟩ := exists_conj_companion b hb p t h ψ.1 ψ.2
    refine Quotient.sound ?_
    let g : (matOrder R F)ˣ :=
      ⟨⟨matMap R F A, ⟨A, rfl⟩⟩, ⟨matMap R F A', ⟨A', rfl⟩⟩,
        Subtype.ext (by simp [← map_mul, hAA']), Subtype.ext (by simp [← map_mul, hA'A])⟩
    exact ⟨g, Subgroup.mem_top _, fun s => hconj s⟩
  unfold embNum
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y => Quotient.inductionOn₂ x y fun ψ χ => (key ψ).trans (key χ).symm⟩,
    ⟨Quotient.mk _ ⟨companionEmb F b hb p t h, hφ₀⟩⟩⟩

end Matrix

/-! ### Local embedding numbers of Eichler orders (stated) -/

section Eichler

variable {R : Type*} [CommRing R]

/-- $M(s) = \{x \in R/\pi^s : x^2 - tx + n \equiv 0\}$ (Voight 2021, (30.6.13)): the roots of $f_\gamma = x^2 - tx + n$
modulo $\pi^s$. -/
def rootsMod (π t n : R) (s : ℕ) : Set (R ⧸ Ideal.span {π ^ s}) :=
  {x | x ^ 2 - Ideal.Quotient.mk _ t * x + Ideal.Quotient.mk _ n = 0}

/-- The reduction map $R/\pi^{s+1} \to R/\pi^s$. -/
def redSucc (π : R) (s : ℕ) : R ⧸ Ideal.span {π ^ (s + 1)} →+* R ⧸ Ideal.span {π ^ s} :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow π (Nat.le_succ s)))

open scoped Classical in
/-- **The local embedding numbers of an Eichler order** (Voight 2021, Proposition 30.6.12), as a named proposition about
a complete discrete valuation ring $R$ with finite residue field, fraction field $F$ and uniformizer $\pi$ (the setting of
sections 30.5 and 30.6): let $S = R[\gamma]$ be free with $R$-basis $1, \gamma$ and $\gamma^2 = t\gamma - n$
($f_\gamma(x) = x^2 - tx + n$, discriminant $d_\gamma = t^2 - 4n \ne 0$, i.e. $K = FS$ separable), and let $e \ge 1$. With
$M(s) = \{x \in R/\pi^s : f_\gamma(x) \equiv 0\}$ (`rootsMod`),
$$m(S, \mathcal O_0(\pi^e); \mathcal O_0(\pi^e)^\times) = \begin{cases} \#M(e), & d_\gamma \in R^\times,\\
\#M(e) + \#\operatorname{img}(M(e+1) \to R/\pi^e), & \text{otherwise.}\end{cases}$$
Stated, not proved. -/
@[kb "voight2021" "Proposition 30.6.12, p. 556"]
def LocalEmbNumEichler (R F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] (π : R) : Prop :=
  Irreducible π → IsAdicComplete (IsLocalRing.maximalIdeal R) R → Finite (IsLocalRing.ResidueField R) →
  ∀ (S : Type) [CommRing S] [Algebra R S] (b : Module.Basis (Fin 2) R S) (t n : R), b 0 = 1 →
    b 1 * b 1 = algebraMap R S t * b 1 - algebraMap R S n → t ^ 2 - 4 * n ≠ 0 →
    ∀ e : ℕ, 1 ≤ e →
      embNum F S (stdEichlerOrder R F π e) ⊤ =
        if IsUnit (t ^ 2 - 4 * n) then Nat.card (rootsMod π t n e)
        else Nat.card (rootsMod π t n e) + Nat.card (redSucc π e '' rootsMod π t n (e + 1))

/-- **The splitting symbol** $(K \mid \mathfrak p)$ (Voight 2021, 30.5.2) of a quadratic $R$-order $S$ over a local ring $R$,
written as $\#\operatorname{Hom}_R(S, k) - 1$ with $k$ the residue field. For $S$ integrally closed this is $1$, $0$ or $-1$
according as $K = FS$ is split ($S/\mathfrak pS \cong k \times k$, two maps to $k$), a ramified field extension
($S/\mathfrak pS \cong k[\varepsilon]/(\varepsilon^2)$, one map) or an unramified field extension ($S/\mathfrak pS$ the quadratic
extension of $k$, no map), which is the book's definition. -/
@[kb "voight2021" "30.5.2, p. 552"]
def splitSymbol (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S] : ℤ :=
  (Nat.card (S →ₐ[R] IsLocalRing.ResidueField R) : ℤ) - 1

/-- **Embedding numbers of a local Eichler order of level $\mathfrak p$** (Voight 2021, Lemma 30.6.16), as a named
proposition: in the setting of `LocalEmbNumEichler`, if $S$ is integrally closed (a maximal $R$-order in $K$), then
$m(S, \mathcal O_0(\pi); \mathcal O_0(\pi)^\times) = 1 + (K \mid \mathfrak p)$ (`splitSymbol`). Stated, not proved. -/
@[kb "voight2021" "Lemma 30.6.16, p. 557"]
def LocalEmbNumEichlerOne (R F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] (π : R) : Prop :=
  Irreducible π → IsAdicComplete (IsLocalRing.maximalIdeal R) R → Finite (IsLocalRing.ResidueField R) →
  ∀ (S : Type) [CommRing S] [Algebra R S] (b : Module.Basis (Fin 2) R S) (t n : R), b 0 = 1 →
    b 1 * b 1 = algebraMap R S t * b 1 - algebraMap R S n → t ^ 2 - 4 * n ≠ 0 → IsIntegrallyClosed S →
      (embNum F S (stdEichlerOrder R F π 1) ⊤ : ℤ) = 1 + splitSymbol R S

end Eichler

/-! ### The trace formula (stated) -/

section Global

open NumberField IsDedekindDomain QuadFormsKB.Quat

variable {F : Type} [Field F] [NumberField F]

/-- **The right order** $\mathcal O_R(J) = \{x \in B : Jx \subseteq J\}$ of a left ideal $J$ of $\mathcal O$ (Voight 2021,
Definition 10.2.8); it plays the role of the left order $\mathcal O_L(I)$ of the book's right ideals $I$ (standard involution). -/
@[kb "voight2021" "Definition 10.2.8, p. 157"]
def rightOrder {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (J : Ideal O) : Subalgebra (𝓞 F) (QuatF F a b) where
  carrier := {x | ∀ y ∈ idealSet J, y * x ∈ idealSet J}
  mul_mem' {x x'} hx hx' y hy := by rw [← mul_assoc]; exact hx' _ (hx y hy)
  add_mem' {x x'} hx hx' y hy := by
    obtain ⟨h1, h1'⟩ := hx y hy
    obtain ⟨h2, h2'⟩ := hx' y hy
    rw [mul_add]
    exact ⟨O.add_mem h1 h2, J.add_mem h1' h2'⟩
  algebraMap_mem' r y hy := rTrans_algebraMap_subset J r ⟨y, hy, rfl⟩

/-- **The trace formula** (Voight 2021, Theorem 30.4.7 together with (30.7.2), i.e. Theorem 30.7.3), as a named
proposition about the number field $F$: let $B = (a,b)_F$, $\mathcal O \subseteq B$ an order and $S$ a quadratic $\mathbb Z_F$-order
that is a domain (so $K = FS$ is a quadratic field; the book also allows $K \cong F \times F$) such that $K$ embeds in $B$.
Then
$$\sum_{[J] \in \operatorname{Cls}\mathcal O} m(S, \mathcal O_R(J); \mathcal O_R(J)^\times)
= h(S)\prod_{\mathfrak p} m(S_{\mathfrak p}, \mathcal O_{\mathfrak p}; \mathcal O_{\mathfrak p}^\times),$$
with $\operatorname{Cls}\mathcal O$ = `ClsO O`, $h(S) = \#\operatorname{Pic}S$ (Mathlib's `ClassGroup S`), and
$S_{\mathfrak p} = \mathfrak o_{\mathfrak p} \otimes S$, $\mathcal O_{\mathfrak p}$ = `localOrder` the completions. The product is a
`finprod`: all but finitely many factors are $1$ (Proposition 30.5.3 (a), `embNum_matOrder`), and the product of the
others is the product over $\mathfrak p \mid \operatorname{discrd}\mathcal O$ of Theorem 30.7.3. Stated, not proved (it needs
the adelic bijection (30.4.6) and Skolem–Noether). -/
@[kb "voight2021" "Theorem 30.4.7, p. 548; Theorem 30.7.3, p. 559"]
def TraceFormulaEmb (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O →
  ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S] [Module.Finite (𝓞 F) S], Module.finrank (𝓞 F) S = 2 →
    (∃ φ : S →ₐ[𝓞 F] QuatF F a b, Function.Injective φ) →
    ∑ᶠ c : ClsO O, embNum F S (rightOrder c.1.out) ⊤ =
      Nat.card (ClassGroup S) * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        embNum (v.adicCompletion F) (TensorProduct (𝓞 F) (v.adicCompletionIntegers F) S)
          (localOrder (v := v) a b O) ⊤

end Global

end QuadFormsKB.Voight.Wave4
