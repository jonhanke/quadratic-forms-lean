/-
# Gorenstein, Bass and basic orders; local Eichler orders are all three (Voight, chapter 24)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Definition 15.6.15 (p. 236),
24.1.1 and (24.1.2) (p. 393), Definition 24.2.1, 24.2.2, Proposition 24.2.3 (p. 395), Theorem 24.2.10 (p. 396),
24.2.14 (p. 397), Proposition 24.2.15 (p. 397), Definition 24.5.1, 24.5.2, Propositions 24.5.4, 24.5.8 (pp. 406–407),
Definition 24.5.6 (p. 407).

**Setting.** $R$ a domain with fraction field $F$ (Lean: `K`), $B$ an $F$-algebra with a reduced trace
$\operatorname{trd} \colon B \to F$ (an $F$-linear map `t`; for $B = \mathrm M_2(F)$ it is the matrix trace `trM`),
$\mathcal O \subseteq B$ an $R$-order (`QuatOrder.IsOrder`). Matrix entries are indexed $0, 1$.

**Definitions.**
* `codiff t O` (**Definition 15.6.15**): the codifferent
  $\operatorname{codiff}(\mathcal O) = \mathcal O^\sharp = \{\alpha \in B : \operatorname{trd}(\alpha\mathcal O) \subseteq R\}$.
* `IsGorenstein t O` (**Definition 24.2.1**, local form): $\operatorname{codiff}(\mathcal O) = \mathcal O\alpha$ for some
  $\alpha \in B^\times$. The book calls $\mathcal O$ Gorenstein when $\operatorname{codiff}(\mathcal O)$ is invertible;
  over a local ring $R$ (where the book works from 24.2.2 on, the property being local) an invertible lattice with left
  order $\mathcal O$ is principal (Main Theorem 16.6.1), and $\mathcal O_L(\operatorname{codiff}\mathcal O) = \mathcal O$
  (Lemma 15.6.16), so this is the book's condition for local $R$. Over a non-local ring the definition is a
  restriction (principal rather than locally principal) and is used here only over local rings.
* `IsBass t O` (**Definition 24.5.1**): every $R$-order $\mathcal O' \supseteq \mathcal O$ of $B$ is Gorenstein.
* `IsMaxCommSubalg L`, `IsBasic O` (**Definition 24.5.6**): $\mathcal O$ contains a maximal $R$-order of a maximal
  commutative $F$-subalgebra $L \subseteq B$.

**Proved** (no inputs).
* `codiff_map`, `IsGorenstein.map`: the codifferent and the Gorenstein property are transported by trace-preserving
  isomorphisms (in particular by conjugation in $\mathrm M_2(F)$, `trM_conj`).
* `codiff_matOrder`, `isGorenstein_matOrder`: $\operatorname{codiff}\mathrm M_2(R) = \mathrm M_2(R)$, so $\mathrm M_2(R)$ is
  Gorenstein.
* `codiff_stdEichlerOrder`, `isGorenstein_stdEichlerOrder` (**24.2.14** for the standard orders):
  $\operatorname{codiff}\mathcal O_0(\pi^e) = \mathcal O_0(\pi^e)\begin{pmatrix} 0 & \pi^{-e} \\ 1 & 0\end{pmatrix}
  = \begin{pmatrix} R & \pi^{-e}R \\ R & R\end{pmatrix}$, so $\mathcal O_0(\pi^e)$ is Gorenstein.
* `IsEichler.isGorenstein` (**24.2.14**, local case): over a discrete valuation ring every Eichler order of
  $\mathrm M_2(F)$ is Gorenstein.
* `IsEichler.isBass` (**24.5.2**, local case): every Eichler order of $\mathrm M_2(F)$ is Bass.
-/
import QuadFormsKB.Literature.Voight.Wave5.EichlerSymbol
import QuadFormsKB.Literature.Voight.EvenClifford

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave7

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 IsLocalization

/-! ### Definitions -/

section General

variable {R K A A' : Type*} [CommRing R] [Field K] [Algebra R K]
  [Ring A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Ring A'] [Algebra K A'] [Algebra R A'] [IsScalarTower R K A']

theorem isInteger_add' {x y : K} (hx : IsInteger R x) (hy : IsInteger R y) : IsInteger R (x + y) :=
  (algebraMap R K).rangeS.add_mem hx hy

theorem isInteger_mul' {x y : K} (hx : IsInteger R x) (hy : IsInteger R y) : IsInteger R (x * y) :=
  (algebraMap R K).rangeS.mul_mem hx hy

theorem isInteger_algebraMap' (r : R) : IsInteger R (algebraMap R K r) := ⟨r, rfl⟩

/-- **The codifferent** (Voight 2021, Definition 15.6.15) of an $R$-subalgebra $\mathcal O$ of $B$ with respect to the
reduced trace $t = \operatorname{trd}$: $\operatorname{codiff}(\mathcal O) = \{\alpha \in B : t(\alpha x) \in R \text{ for all }
x \in \mathcal O\}$, an $R$-submodule of $B$. -/
@[kb "voight2021" "Definition 15.6.15, p. 236; 24.2, p. 394"]
def codiff (t : A →ₗ[K] K) (O : Subalgebra R A) : Submodule R A where
  carrier := {α | ∀ x ∈ O, IsInteger R (t (α * x))}
  add_mem' {α β} hα hβ x hx := by
    rw [add_mul, map_add]; exact isInteger_add' (hα x hx) (hβ x hx)
  zero_mem' x _ := by rw [zero_mul, map_zero]; exact ⟨0, map_zero _⟩
  smul_mem' r α hα x hx := by
    rw [smul_mul_assoc, ← algebraMap_smul K r (α * x), map_smul, smul_eq_mul]
    exact isInteger_mul' (isInteger_algebraMap' r) (hα x hx)

theorem mem_codiff {t : A →ₗ[K] K} {O : Subalgebra R A} {α : A} :
    α ∈ codiff t O ↔ ∀ x ∈ O, IsInteger R (t (α * x)) := Iff.rfl

/-- **Gorenstein order** (Voight 2021, Definition 24.2.1, in the local form of 24.2.2): $\operatorname{codiff}(\mathcal O)$
is principal as a left $\mathcal O$-lattice, $\operatorname{codiff}(\mathcal O) = \mathcal O\alpha$ with $\alpha \in B^\times$. For
a local ring $R$ this is the book's condition that $\operatorname{codiff}(\mathcal O)$ be invertible (Main Theorem 16.6.1:
invertible lattices are locally principal; Lemma 15.6.16: $\mathcal O_L(\operatorname{codiff}\mathcal O) = \mathcal O$). -/
@[kb "voight2021" "Definition 24.2.1, p. 395; 24.2.2, p. 395"]
def IsGorenstein (t : A →ₗ[K] K) (O : Subalgebra R A) : Prop :=
  ∃ α : Aˣ, (codiff t O : Set A) = (· * (α : A)) '' (O : Set A)

/-- **Bass order** (Voight 2021, Definition 24.5.1): every $R$-order $\mathcal O' \supseteq \mathcal O$ of $B$ (including
$\mathcal O$ itself) is Gorenstein. -/
@[kb "voight2021" "Definition 24.5.1, p. 406"]
def IsBass (t : A →ₗ[K] K) (O : Subalgebra R A) : Prop :=
  ∀ O' : Subalgebra R A, IsOrder R K O' → O ≤ O' → IsGorenstein t O'

/-- **Maximal commutative subalgebra** (as in Voight 2021, Definition 24.5.6): an $F$-subalgebra $L \subseteq B$ that is
commutative and not properly contained in a commutative $F$-subalgebra of $B$. -/
@[kb "voight2021" "Definition 24.5.6, p. 407"]
def IsMaxCommSubalg (L : Subalgebra K A) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, x * y = y * x) ∧
    ∀ L' : Subalgebra K A, (∀ x ∈ L', ∀ y ∈ L', x * y = y * x) → L ≤ L' → L' = L

/-- **Basic order** (Voight 2021, Definition 24.5.6): $\mathcal O$ contains a maximal $R$-order $S$ (`IsMaximalOrder`, an
$R$-subalgebra of $L$) of a maximal commutative $F$-subalgebra $L \subseteq B$. -/
@[kb "voight2021" "Definition 24.5.6, p. 407"]
def IsBasic (O : Subalgebra R A) : Prop :=
  ∃ L : Subalgebra K A, IsMaxCommSubalg L ∧
    ∃ S : Subalgebra R L, IsMaximalOrder R K S ∧ ∀ x ∈ S, (x : A) ∈ O

/-! ### Transport along trace-preserving isomorphisms -/

variable {t : A →ₗ[K] K} {t' : A' →ₗ[K] K}

/-- A trace-preserving isomorphism $\varphi$ maps the codifferent of $\mathcal O$ onto that of $\varphi(\mathcal O)$. -/
theorem codiff_map (φ : A ≃ₐ[K] A') (hφ : ∀ x, t' (φ x) = t x) (O : Subalgebra R A) :
    (codiff t' (O.map ((φ : A →ₐ[K] A').restrictScalars R)) : Set A') = φ '' (codiff t O : Set A) := by
  ext β
  simp only [SetLike.mem_coe, mem_codiff, Set.mem_image, Subalgebra.mem_map, AlgHom.coe_restrictScalars',
    AlgHom.coe_coe, forall_exists_index, and_imp]
  constructor
  · intro h
    refine ⟨φ.symm β, fun x hx => ?_, φ.apply_symm_apply β⟩
    have := h (φ x) x hx rfl
    rwa [← φ.apply_symm_apply β, ← map_mul, hφ] at this
  · rintro ⟨α, hα, rfl⟩ _ x hx rfl
    have h1 := hα x hx
    rw [← hφ, map_mul] at h1
    simpa using h1

/-- **The Gorenstein property is an isomorphism invariant**: if $\varphi \colon B \to B'$ preserves the reduced trace and
$\mathcal O$ is Gorenstein, so is $\varphi(\mathcal O)$. -/
theorem IsGorenstein.map {O : Subalgebra R A} (hO : IsGorenstein t O) (φ : A ≃ₐ[K] A')
    (hφ : ∀ x, t' (φ x) = t x) : IsGorenstein t' (O.map ((φ : A →ₐ[K] A').restrictScalars R)) := by
  obtain ⟨α, hα⟩ := hO
  refine ⟨Units.map (φ : A →* A') α, ?_⟩
  rw [codiff_map φ hφ, hα, Set.image_image]
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Subalgebra.mem_map, AlgHom.coe_restrictScalars', AlgHom.coe_coe,
    Units.coe_map, MonoidHom.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, ⟨x, hx, rfl⟩, (map_mul φ x α).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, map_mul φ x α⟩

/-- Maximal commutative subalgebras are transported by isomorphisms. -/
theorem IsMaxCommSubalg.map {L : Subalgebra K A} (hL : IsMaxCommSubalg L) (φ : A ≃ₐ[K] A') :
    IsMaxCommSubalg (L.map (φ : A →ₐ[K] A')) := by
  obtain ⟨hcomm, hmax⟩ := hL
  refine ⟨?_, fun L' hL' hle => le_antisymm (fun z hz => ?_) hle⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · have hsub : L'.map (φ.symm : A' →ₐ[K] A) = L := by
      refine hmax _ ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        change φ.symm x * φ.symm y = φ.symm y * φ.symm x
        rw [← map_mul, ← map_mul, hL' x hx y hy]
      · intro x hx
        exact ⟨φ x, hle ⟨x, hx, rfl⟩, φ.symm_apply_apply x⟩
    have h1 : φ.symm z ∈ L'.map (φ.symm : A' →ₐ[K] A) := ⟨z, hz, rfl⟩
    rw [hsub] at h1
    exact ⟨φ.symm z, h1, φ.apply_symm_apply z⟩

/-- **Being basic is an isomorphism invariant**: if $\varphi \colon B \to B'$ is an isomorphism of $F$-algebras and
$\mathcal O$ is basic, so is $\varphi(\mathcal O)$. -/
theorem IsBasic.map {O : Subalgebra R A} (hO : IsBasic (K := K) O) (φ : A ≃ₐ[K] A') :
    IsBasic (K := K) (O.map ((φ : A →ₐ[K] A').restrictScalars R)) := by
  obtain ⟨L, hL, S, hS, hSO⟩ := hO
  let e : L ≃ₐ[K] L.map (φ : A →ₐ[K] A') := φ.subalgebraMap L
  refine ⟨L.map (φ : A →ₐ[K] A'), hL.map φ, S.map ((e : L →ₐ[K] L.map (φ : A →ₐ[K] A')).restrictScalars R),
    hS.map e, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hSO x hx, rfl⟩

end General

/-! ### Orders in $\mathrm M_2(F)$ -/

section Matrix

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The reduced trace of $\mathrm M_2(F)$: the matrix trace. -/
abbrev trM (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K →ₗ[K] K := Matrix.traceLinearMap (Fin 2) K K

theorem trM_apply (x : Matrix (Fin 2) (Fin 2) K) : trM K x = x 0 0 + x 1 1 := by
  simp [Matrix.trace_fin_two]

/-- Conjugation preserves the trace. -/
theorem trM_conj {P Q : Matrix (Fin 2) (Fin 2) K} (hPQ : P * Q = 1) (hQP : Q * P = 1) (x : Matrix (Fin 2) (Fin 2) K) :
    trM K (conjAlgEquiv P Q hPQ hQP x) = trM K x := by
  change Matrix.trace (P * x * Q) = Matrix.trace x
  rw [Matrix.trace_mul_comm, ← mul_assoc, hQP, one_mul]

/-- The trace of $\alpha E_{ji}$ is the entry $\alpha_{ij}$. -/
theorem trM_mul_single (α : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) (c : K) :
    trM K (α * Matrix.single j i c) = α i j * c := by
  rw [trM_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

/-- **The codifferent of $\mathrm M_2(R)$ is $\mathrm M_2(R)$.** -/
theorem codiff_matOrder : (codiff (trM K) (matOrder R K) : Set (Matrix (Fin 2) (Fin 2) K)) = matOrder R K := by
  ext α
  simp only [SetLike.mem_coe, mem_codiff]
  constructor
  · intro h
    rw [mem_matOrder]
    intro i j
    have := h _ (single_mem_matOrder j i)
    rwa [trM_mul_single, mul_one] at this
  · intro hα x hx
    have hm := (matOrder R K).mul_mem hα hx
    rw [mem_matOrder] at hm
    rw [trM_apply]
    exact isInteger_add' (hm 0 0) (hm 1 1)

/-- **$\mathrm M_2(R)$ is Gorenstein** ($\operatorname{codiff}\mathrm M_2(R) = \mathrm M_2(R) \cdot 1$). -/
@[kb "voight2021" "24.1.1, p. 393; Definition 24.2.1, p. 395"]
theorem isGorenstein_matOrder : IsGorenstein (trM K) (matOrder R K) :=
  ⟨1, by rw [codiff_matOrder]; simp⟩

/-- $w = \begin{pmatrix} 0 & \pi^{-e} \\ 1 & 0 \end{pmatrix}$, the generator of $\operatorname{codiff}\mathcal O_0(\pi^e)$. -/
abbrev codiffGen (π : R) (e : ℕ) : Matrix (Fin 2) (Fin 2) K := !![0, (algebraMap R K π ^ e)⁻¹; 1, 0]

/-- $w^{-1} = \begin{pmatrix} 0 & 1 \\ \pi^e & 0 \end{pmatrix}$. -/
abbrev codiffGenInv (π : R) (e : ℕ) : Matrix (Fin 2) (Fin 2) K := !![0, 1; algebraMap R K π ^ e, 0]

theorem codiffGen_mul_inv {π : R} (hπ : π ≠ 0) (e : ℕ) :
    codiffGen (K := K) π e * codiffGenInv π e = 1 := by
  have hp : (algebraMap R K π ^ e) ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ)
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp]

theorem codiffGen_inv_mul {π : R} (hπ : π ≠ 0) (e : ℕ) :
    codiffGenInv (K := K) π e * codiffGen π e = 1 := by
  have hp : (algebraMap R K π ^ e) ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ)
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hp]

theorem mul_codiffGenInv (π : R) (e : ℕ) (α : Matrix (Fin 2) (Fin 2) K) :
    α * codiffGenInv π e = !![α 0 1 * algebraMap R K π ^ e, α 0 0; α 1 1 * algebraMap R K π ^ e, α 1 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_codiffGen (π : R) (e : ℕ) (α : Matrix (Fin 2) (Fin 2) K) :
    α * codiffGen π e =
      !![α 0 1, α 0 0 * (algebraMap R K π ^ e)⁻¹; α 1 1, α 1 0 * (algebraMap R K π ^ e)⁻¹] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem trM_mul_apply (M x : Matrix (Fin 2) (Fin 2) K) :
    trM K (M * x) = M 0 0 * x 0 0 + M 0 1 * x 1 0 + (M 1 0 * x 0 1 + M 1 1 * x 1 1) := by
  rw [trM_apply]; simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- A matrix unit $cE_{ij}$ with $c \in R$ and $(i, j) \neq (1, 0)$ lies in $\mathcal O_0(\pi^e)$. -/
theorem single_mem_stdEichlerOrder {π : R} {e : ℕ} (i j : Fin 2) (h : ¬ (i = 1 ∧ j = 0)) (r : R) :
    Matrix.single i j (algebraMap R K r) ∈ stdEichlerOrder R K π e := by
  refine ⟨fun k l => ?_, 0, ?_⟩
  · by_cases hkl : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := hkl; exact ⟨r, by simp⟩
    · exact ⟨0, by rw [Matrix.single_apply, if_neg hkl, map_zero]⟩
  · rw [Matrix.single_apply, if_neg (fun h' => h ⟨h'.1, h'.2⟩)]; simp

/-- $\pi^e r E_{10} \in \mathcal O_0(\pi^e)$. -/
theorem single_one_zero_mem_stdEichlerOrder (π : R) (e : ℕ) (r : R) :
    Matrix.single 1 0 (algebraMap R K (π ^ e * r)) ∈ stdEichlerOrder R K π e := by
  refine ⟨fun k l => ?_, r, by simp [map_mul, map_pow]⟩
  by_cases hkl : (1 : Fin 2) = k ∧ (0 : Fin 2) = l
  · obtain ⟨rfl, rfl⟩ := hkl; exact ⟨π ^ e * r, by simp⟩
  · exact ⟨0, by rw [Matrix.single_apply, if_neg hkl, map_zero]⟩

/-- **The codifferent of the standard Eichler order** (Voight 2021, 24.2.14):
$\operatorname{codiff}\mathcal O_0(\pi^e) = \mathcal O_0(\pi^e)\,w$ with $w = \begin{pmatrix} 0 & \pi^{-e} \\ 1 & 0\end{pmatrix}$;
both sides are $\begin{pmatrix} R & \pi^{-e}R \\ R & R\end{pmatrix}$. -/
theorem codiff_stdEichlerOrder {π : R} (hπ : π ≠ 0) (e : ℕ) :
    (codiff (trM K) (stdEichlerOrder R K π e) : Set (Matrix (Fin 2) (Fin 2) K)) =
      (· * codiffGen π e) '' (stdEichlerOrder R K π e : Set (Matrix (Fin 2) (Fin 2) K)) := by
  have hp : (algebraMap R K π ^ e) ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ)
  ext α
  simp only [SetLike.mem_coe, mem_codiff, Set.mem_image]
  constructor
  · intro h
    -- the entries of α, tested against E₀₀, E₀₁, π^e E₁₀, E₁₁
    have t00 := h _ (single_mem_stdEichlerOrder (π := π) (e := e) 0 0 (by decide) 1)
    have t10 := h _ (single_mem_stdEichlerOrder (π := π) (e := e) 0 1 (by decide) 1)
    have t11 := h _ (single_mem_stdEichlerOrder (π := π) (e := e) 1 1 (by decide) 1)
    have t01 := h _ (single_one_zero_mem_stdEichlerOrder (K := K) π e 1)
    rw [map_one, trM_mul_single, mul_one] at t00 t10 t11
    rw [trM_mul_single, mul_one, map_pow] at t01
    obtain ⟨r00, h00⟩ := t00
    obtain ⟨r10, h10⟩ := t10
    obtain ⟨r11, h11⟩ := t11
    obtain ⟨r01, h01⟩ := t01
    refine ⟨α * codiffGenInv π e, ⟨fun i j => ?_, r11, ?_⟩, ?_⟩
    · rw [mul_codiffGenInv]
      fin_cases i <;> fin_cases j
      · exact ⟨r01, by simpa using h01⟩
      · exact ⟨r00, by simpa using h00⟩
      · exact ⟨r11 * π ^ e, by simp [← h11]⟩
      · exact ⟨r10, by simpa using h10⟩
    · rw [mul_codiffGenInv]; simp [← h11, mul_comm]
    · rw [mul_assoc, codiffGen_inv_mul hπ, mul_one]
  · rintro ⟨y, ⟨hyi, r, hr⟩, rfl⟩ x ⟨hxi, s, hs⟩
    obtain ⟨y00, h00⟩ := hyi 0 0
    obtain ⟨y01, h01⟩ := hyi 0 1
    obtain ⟨y11, h11⟩ := hyi 1 1
    obtain ⟨x00, g00⟩ := hxi 0 0
    obtain ⟨x01, g01⟩ := hxi 0 1
    obtain ⟨x11, g11⟩ := hxi 1 1
    refine ⟨y01 * x00 + y00 * s + (y11 * x01 + r * x11), ?_⟩
    rw [mul_codiffGen, trM_mul_apply]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [hr, hs, ← h00, ← h01, ← h11, ← g00, ← g01, ← g11]
    simp only [map_add, map_mul, map_pow]
    field_simp

/-- **The standard Eichler order is Gorenstein** (Voight 2021, 24.2.14): $\mathcal O_0(\pi^e)$ is a Gorenstein
$R$-order of $\mathrm M_2(F)$ for every $e \ge 0$. -/
@[kb "voight2021" "24.2.14, p. 397"]
theorem isGorenstein_stdEichlerOrder {π : R} (hπ : π ≠ 0) (e : ℕ) :
    IsGorenstein (trM K) (stdEichlerOrder R K π e) :=
  ⟨⟨codiffGen π e, codiffGenInv π e, codiffGen_mul_inv hπ e, codiffGen_inv_mul hπ e⟩,
    codiff_stdEichlerOrder hπ e⟩

variable [IsDiscreteValuationRing R]

/-- **Eichler orders are Gorenstein** (Voight 2021, 24.2.14 and (24.1.2), local case): over a discrete valuation ring
$R$ with uniformizer $\pi$, every Eichler $R$-order of $\mathrm M_2(F)$ is Gorenstein. -/
@[kb "voight2021" "24.2.14, p. 397; (24.1.2), p. 393"]
theorem IsEichler.isGorenstein {π : R} (hπ : Irreducible π) {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)}
    (hO : IsEichler R K O) : IsGorenstein (trM K) O := by
  obtain ⟨e, P, Q, hPQ, hQP, rfl⟩ := localEichlerStructure hπ O hO
  exact (isGorenstein_stdEichlerOrder hπ.ne_zero e).map (conjAlgEquiv P Q hPQ hQP) (trM_conj hPQ hQP)

/-- **Eichler orders are Bass** (Voight 2021, 24.5.2 and (24.1.2), local case): over a discrete valuation ring, every
order of $\mathrm M_2(F)$ containing an Eichler order is Eichler (Corollary 23.4.10, `IsEichler.of_le`), hence
Gorenstein; so every Eichler order is Bass. -/
@[kb "voight2021" "24.5.2, p. 406; (24.1.2), p. 393"]
theorem IsEichler.isBass {π : R} (hπ : Irreducible π) {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)}
    (hO : IsEichler R K O) : IsBass (trM K) O :=
  fun _ hO' hle => IsEichler.isGorenstein hπ (Wave4.IsEichler.of_le hπ hO hO' hle)

/-! #### Basic: the diagonal order $R \times R \subseteq F \times F$ -/

/-- The diagonal subalgebra $F \times F \subseteq \mathrm M_2(F)$. -/
abbrev diagSub (K : Type*) [Field K] : Subalgebra K (Matrix (Fin 2) (Fin 2) K) :=
  (Matrix.diagonalAlgHom K : (Fin 2 → K) →ₐ[K] Matrix (Fin 2) (Fin 2) K).range

theorem mem_diagSub {x : Matrix (Fin 2) (Fin 2) K} : x ∈ diagSub K ↔ x = Matrix.diagonal (fun i => x i i) := by
  constructor
  · rintro ⟨d, rfl⟩
    change Matrix.diagonal d = Matrix.diagonal (fun i => Matrix.diagonal d i i)
    simp
  · intro h
    exact ⟨fun i => x i i, h.symm⟩

/-- The coordinate $x \mapsto x_{ii}$ on $F \times F$, an algebra homomorphism. -/
def diagProj (i : Fin 2) : diagSub K →ₐ[R] K where
  toFun x := (x : Matrix (Fin 2) (Fin 2) K) i i
  map_one' := by simp
  map_mul' x y := by
    simp only [Subalgebra.coe_mul]
    rw [mem_diagSub.1 x.2, mem_diagSub.1 y.2, Matrix.diagonal_mul_diagonal]
    simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' r := by
    simp only [Subalgebra.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply R K (Matrix (Fin 2) (Fin 2) K), Matrix.algebraMap_matrix_apply]
    simp

/-- The diagonal order $R \times R$ of $F \times F$: diagonal matrices with entries in $R$. -/
def diagOrder (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    Subalgebra R (diagSub K) where
  carrier := {x | ∀ i, IsInteger R ((x : Matrix (Fin 2) (Fin 2) K) i i)}
  mul_mem' {x y} hx hy i := by
    change IsInteger R (diagProj (R := R) i (x * y))
    rw [map_mul]
    exact isInteger_mul' (hx i) (hy i)
  add_mem' {x y} hx hy i := by
    simpa using isInteger_add' (hx i) (hy i)
  algebraMap_mem' r i := ⟨r, (diagProj (R := R) i).commutes r |>.symm⟩

theorem diagonal_mem_diagSub (d : Fin 2 → K) : Matrix.diagonal d ∈ diagSub K := ⟨d, rfl⟩

/-- $R \times R$ is a maximal $R$-order of $F \times F$. -/
theorem isMaximalOrder_diagOrder : IsMaximalOrder R K (diagOrder R K) := by
  -- the R-linear parametrization d ↦ diag(d)
  let f : (Fin 2 → R) →ₗ[R] diagSub K :=
    { toFun := fun d => ⟨Matrix.diagonal (fun i => algebraMap R K (d i)), diagonal_mem_diagSub _⟩
      map_add' := fun d d' => by ext i j; simp [Matrix.diagonal_add]
      map_smul' := fun r d => by
        apply Subtype.ext
        change Matrix.diagonal (fun i => algebraMap R K ((r • d) i)) =
          r • Matrix.diagonal (fun i => algebraMap R K (d i))
        ext i j
        by_cases h : i = j
        · subst h; simp [Algebra.smul_def]
        · simp [Matrix.diagonal_apply_ne _ h] }
  have hrange : Subalgebra.toSubmodule (diagOrder R K) = Submodule.map f ⊤ := by
    ext x
    simp only [Subalgebra.mem_toSubmodule, Submodule.map_top, LinearMap.mem_range]
    constructor
    · intro hx
      choose d hd using hx
      refine ⟨d, Subtype.ext ?_⟩
      change Matrix.diagonal (fun i => algebraMap R K (d i)) = (x : Matrix (Fin 2) (Fin 2) K)
      rw [mem_diagSub.1 x.2]
      simp only [hd]
    · rintro ⟨d, rfl⟩ i
      exact ⟨d i, by simp [f]⟩
  have hord : IsOrder R K (diagOrder R K) := by
    refine ⟨?_, ?_⟩
    · rw [hrange]; exact Submodule.FG.map _ Module.Finite.fg_top
    · rw [eq_top_iff]
      rintro x -
      have hx := mem_diagSub.1 x.2
      have : x = (x : Matrix (Fin 2) (Fin 2) K) 0 0 • f (Pi.single 0 1) +
          (x : Matrix (Fin 2) (Fin 2) K) 1 1 • f (Pi.single 1 1) := by
        apply Subtype.ext
        rw [hx]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [f, Matrix.diagonal_apply, Pi.single_apply]
      rw [this]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
        (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      · intro i; exact ⟨(Pi.single 0 (1 : R) : Fin 2 → R) i, by simp [f]⟩
      · intro i; exact ⟨(Pi.single 1 (1 : R) : Fin 2 → R) i, by simp [f]⟩
  refine ⟨hord, fun S' hS' hle => le_antisymm (fun x hx i => ?_) hle⟩
  have hint : IsIntegral R (diagProj (R := R) i x) := (hS'.isIntegral hx).map (diagProj i)
  exact IsIntegrallyClosed.isIntegral_iff.1 hint

/-- $F \times F$ (the diagonal) is a maximal commutative subalgebra of $\mathrm M_2(F)$. -/
theorem isMaxCommSubalg_diagSub : IsMaxCommSubalg (diagSub K) := by
  refine ⟨?_, fun L' hL' hle => le_antisymm (fun y hy => ?_) hle⟩
  · intro x hx y hy
    rw [mem_diagSub.1 hx, mem_diagSub.1 hy, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]
  · have hE := hL' y hy _ (hle (diagonal_mem_diagSub ![1, 0]))
    have h01 := congrFun (congrFun hE 0) 1
    have h10 := congrFun (congrFun hE 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] at h01 h10
    rw [mem_diagSub]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, h01, h10]

/-- **The standard Eichler order is basic** (Voight 2021, Definition 24.5.6; 24.5.2 and Proposition 24.5.8): it contains
the diagonal order $R \times R$, a maximal $R$-order of the maximal commutative subalgebra $F \times F$. -/
@[kb "voight2021" "Definition 24.5.6, p. 407; Proposition 24.5.8, p. 407"]
theorem isBasic_stdEichlerOrder (π : R) (e : ℕ) : IsBasic (K := K) (stdEichlerOrder R K π e) := by
  refine ⟨diagSub K, isMaxCommSubalg_diagSub, diagOrder R K, isMaximalOrder_diagOrder, fun x hx => ?_⟩
  have hd := mem_diagSub.1 x.2
  refine ⟨fun i j => ?_, 0, ?_⟩
  · by_cases h : i = j
    · subst h; exact hx i
    · rw [hd, Matrix.diagonal_apply_ne _ h]; exact ⟨0, map_zero _⟩
  · rw [hd, Matrix.diagonal_apply_ne _ (by decide)]; simp

/-- **Eichler orders are basic** (Voight 2021, Definition 24.5.6, with 24.5.2 and Proposition 24.5.8, local case): over a
discrete valuation ring, every Eichler order of $\mathrm M_2(F)$ contains a maximal $R$-order of a maximal commutative
subalgebra (a conjugate of $R \times R$). -/
@[kb "voight2021" "Definition 24.5.6, p. 407; Proposition 24.5.8, p. 407"]
theorem IsEichler.isBasic {π : R} (hπ : Irreducible π) {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)}
    (hO : IsEichler R K O) : IsBasic (K := K) O := by
  obtain ⟨e, P, Q, hPQ, hQP, rfl⟩ := localEichlerStructure hπ O hO
  exact (isBasic_stdEichlerOrder π e).map (conjAlgEquiv P Q hPQ hQP)

end Matrix

/-! ### Statements over a complete discrete valuation ring (named propositions) -/

section Statements

open Quaternion

/-- **The reduced trace of $B = \mathbb H[F, c_1, c_2, c_3]$** (Mathlib's presentation $i^2 = c_1 + c_2 i$, $j^2 = c_3$):
$\operatorname{trd}(x) = x + \bar x = 2x_0 + c_2x_1$ (Mathlib's `QuaternionAlgebra.self_add_star'`), as an $F$-linear map. For
$\mathbb H[F, a, b] = (a, b)_F$ this is $2x_0$ (`QuatOrder.trd`). -/
def trdH (K : Type*) [Field K] (c₁ c₂ c₃ : K) : ℍ[K,c₁,c₂,c₃] →ₗ[K] K :=
  (2 : K) • QuaternionAlgebra.reₗ c₁ c₂ c₃ + c₂ • QuaternionAlgebra.imIₗ c₁ c₂ c₃

theorem trdH_apply {K : Type*} [Field K] {c₁ c₂ c₃ : K} (x : ℍ[K,c₁,c₂,c₃]) :
    trdH K c₁ c₂ c₃ x = 2 * x.re + c₂ * x.imI := rfl

/-- **Primitive ternary quadratic form** (Voight 2021, Definition 9.7.14, for forms with values in $L = R$): the values
$Q(x)$, $x \in R^3$, generate the unit ideal of $R$. -/
@[kb "voight2021" "Theorem 24.2.10, p. 396"]
def IsPrimitiveTernary {R : Type*} [CommRing R] (Q : QuadForm R 3) : Prop :=
  Ideal.span (Set.range Q.eval) = ⊤

variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Gorenstein orders are those of primitive ternary forms** (Voight 2021, Theorem 24.2.10), as a named proposition
about a complete discrete valuation ring $R$ with fraction field $F$ (the book's "R local", 23.2.1; the statement is
local, as in its proof): let $B = \mathbb H[F, c_1, c_2, c_3]$ be a quaternion algebra ($c_2^2 + 4c_1 \neq 0$, $c_3 \neq 0$),
$\mathcal O \subseteq B$ an $R$-order and $Q$ a ternary quadratic form over $R$ with $\mathcal O \cong \operatorname{Clf}^0(Q)$
(for instance the form $\operatorname{nrd}^\sharp$ of Main Theorem 22.4.1, which is determined up to similarity). Then
$\mathcal O$ is Gorenstein iff $Q$ is primitive. Stated, not proved: the book's proof identifies the odd Clifford
bimodule with $\operatorname{Hom}_R(\mathcal O, R)$ (Proposition 24.2.6). -/
@[kb "voight2021" "Theorem 24.2.10, p. 396"]
def GorensteinIffPrimitive : Prop :=
  ∀ c₁ c₂ c₃ : K, c₂ ^ 2 + 4 * c₁ ≠ 0 → c₃ ≠ 0 → ∀ O : Subalgebra R ℍ[K,c₁,c₂,c₃], IsOrder R K O →
    ∀ Q : QuadForm R 3, Nonempty (O ≃ₐ[R] Voight.Clf0 Q) →
      (IsGorenstein (trdH K c₁ c₂ c₃) O ↔ IsPrimitiveTernary Q)

/-- **Gorenstein saturation and conductor** (Voight 2021, Proposition 24.2.15 and Definition 24.2.17), as a named
proposition about a complete discrete valuation ring $R$: for every $R$-order $\mathcal O$ of a quaternion algebra
$B = \mathbb H[F, c_1, c_2, c_3]$ there is a unique pair of an ideal $\mathfrak f = \mathfrak f(\mathcal O) \subseteq R$ (the
Gorenstein conductor) and a Gorenstein $R$-order $\operatorname{Gor}(\mathcal O)$ (the Gorenstein saturation) with
$\mathcal O = R + \mathfrak f\operatorname{Gor}(\mathcal O)$ (equality of $R$-submodules of $B$). Stated, not proved. -/
@[kb "voight2021" "Proposition 24.2.15, p. 397; Definition 24.2.17, p. 398"]
def GorensteinSaturation : Prop :=
  ∀ c₁ c₂ c₃ : K, c₂ ^ 2 + 4 * c₁ ≠ 0 → c₃ ≠ 0 → ∀ O : Subalgebra R ℍ[K,c₁,c₂,c₃], IsOrder R K O →
    ∃! p : Ideal R × Subalgebra R ℍ[K,c₁,c₂,c₃], IsOrder R K p.2 ∧ IsGorenstein (trdH K c₁ c₂ c₃) p.2 ∧
      Subalgebra.toSubmodule O = Submodule.span R {1} ⊔ p.1 • Subalgebra.toSubmodule p.2

/-- **Residually inert orders are Bass** (Voight 2021, Proposition 24.5.4), as a named proposition about a complete
discrete valuation ring $R$: an $R$-order $\mathcal O$ of a quaternion algebra $B = \mathbb H[F, c_1, c_2, c_3]$ with Eichler
symbol $(\mathcal O \mid \mathfrak p) = -1$ (`Wave6.HasEichlerSymbol`) is Bass. Stated, not proved (the book's proof uses the
base change of Proposition 24.2.23 to an unramified quadratic extension). -/
@[kb "voight2021" "Proposition 24.5.4, p. 406"]
def ResiduallyInertIsBass : Prop :=
  ∀ c₁ c₂ c₃ : K, c₂ ^ 2 + 4 * c₁ ≠ 0 → c₃ ≠ 0 → ∀ O : Subalgebra R ℍ[K,c₁,c₂,c₃], IsOrder R K O →
    Wave6.HasEichlerSymbol R O .negOne → IsBass (trdH K c₁ c₂ c₃) O

/-- **Basic equals Bass, locally** (Voight 2021, Proposition 24.5.8; Chari–Smertnig–Voight 2019, Theorem 1.1), as a
named proposition about a complete discrete valuation ring $R$: an $R$-order of a quaternion algebra
$B = \mathbb H[F, c_1, c_2, c_3]$ is basic iff it is Bass. Stated, not proved. -/
@[kb "voight2021" "Proposition 24.5.8, p. 407"]
def BasicIffBass : Prop :=
  ∀ c₁ c₂ c₃ : K, c₂ ^ 2 + 4 * c₁ ≠ 0 → c₃ ≠ 0 → ∀ O : Subalgebra R ℍ[K,c₁,c₂,c₃], IsOrder R K O →
    (IsBasic (K := K) O ↔ IsBass (trdH K c₁ c₂ c₃) O)

end Statements

end QuadFormsKB.Voight.Wave7
