/-
# The radical idealizer of a local Eichler order (Voight, Definition 24.4.1, 24.4.5)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Definition 24.4.1 (p. 403), 24.4.2,
24.4.5 (pp. 403–404).

**Setting.** $R$ a discrete valuation ring with fraction field $F$ (Lean: `K`) and uniformizer $\pi$, $B = \mathrm M_2(F)$,
$\mathcal O_0(\pi^e) = \begin{pmatrix} R & R \\ \pi^eR & R \end{pmatrix}$ (`Wave3.stdEichlerOrder`). Matrix entries are
indexed $0, 1$. $\operatorname{rad}\mathcal O$ is the Jacobson radical (Mathlib's `Ring.jacobson`).

**Contents.**
* `radSet O`: $\operatorname{rad}\mathcal O$ as a subset of $B$.
* `radIdealizer O` (**Definition 24.4.1**): the radical idealizer
  $\mathcal O^\natural = \mathcal O_L(\operatorname{rad}\mathcal O) \cap \mathcal O_R(\operatorname{rad}\mathcal O)$.
* `radIdealizer_stdEichlerOrder` (**24.4.5**, proved): for $e \ge 2$,
  $\mathcal O_0(\pi^e)^\natural = \begin{pmatrix} R & \pi^{-1}R \\ \pi^{e-1}R & R\end{pmatrix}
  = P\,\mathcal O_0(\pi^{e-2})\,P^{-1}$ with $P = \operatorname{diag}(1, \pi)$; in particular
  (`isEichler_radIdealizer_stdEichlerOrder`) it is an Eichler order of level $\pi^{e-2}$.
-/
import QuadFormsKB.Literature.Voight.Wave5.EichlerSymbol

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave7

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 QuadFormsKB.Voight.Wave5
  QuadFormsKB.Voight.Wave6 IsLocalization

section General

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- **The radical of $\mathcal O$ as a subset of $B$**: the elements $x \in \mathcal O$ lying in the Jacobson radical
$\operatorname{rad}\mathcal O$. -/
def radSet (O : Subalgebra R A) : Set A := {x | ∃ h : x ∈ O, (⟨x, h⟩ : O) ∈ Ring.jacobson O}

theorem add_mem_radSet {O : Subalgebra R A} {x y : A} (hx : x ∈ radSet O) (hy : y ∈ radSet O) :
    x + y ∈ radSet O := by
  obtain ⟨hx, hJx⟩ := hx; obtain ⟨hy, hJy⟩ := hy
  exact ⟨O.add_mem hx hy, (Ring.jacobson O).add_mem hJx hJy⟩

theorem smul_mem_radSet {O : Subalgebra R A} (r : R) {x : A} (hx : x ∈ radSet O) : r • x ∈ radSet O := by
  obtain ⟨hx, hJx⟩ := hx
  refine ⟨O.smul_mem hx r, ?_⟩
  have : (⟨r • x, O.smul_mem hx r⟩ : O) = algebraMap R O r * ⟨x, hx⟩ := by
    apply Subtype.ext; simp [Algebra.smul_def]
  rw [this]
  exact (Ring.jacobson O).mul_mem_left _ hJx

/-- **The radical idealizer** (Voight 2021, Definition 24.4.1):
$\mathcal O^\natural = \mathcal O_L(\operatorname{rad}\mathcal O) \cap \mathcal O_R(\operatorname{rad}\mathcal O)
= \{x \in B : x\operatorname{rad}\mathcal O \subseteq \operatorname{rad}\mathcal O \text{ and }
\operatorname{rad}\mathcal O\,x \subseteq \operatorname{rad}\mathcal O\}$. -/
@[kb "voight2021" "Definition 24.4.1, p. 403"]
def radIdealizer (O : Subalgebra R A) : Subalgebra R A where
  carrier := {x | (∀ j ∈ radSet O, x * j ∈ radSet O) ∧ (∀ j ∈ radSet O, j * x ∈ radSet O)}
  mul_mem' {x y} hx hy := by
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [mul_assoc]; exact hx.1 _ (hy.1 j hj)
    · rw [← mul_assoc]; exact hy.2 _ (hx.2 j hj)
  add_mem' {x y} hx hy := by
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [add_mul]; exact add_mem_radSet (hx.1 j hj) (hy.1 j hj)
    · rw [mul_add]; exact add_mem_radSet (hx.2 j hj) (hy.2 j hj)
  algebraMap_mem' r := by
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [← Algebra.smul_def]; exact smul_mem_radSet r hj
    · rw [← Algebra.commutes, ← Algebra.smul_def]; exact smul_mem_radSet r hj

end General

/-! ### The radical idealizer of $\mathcal O_0(\pi^e)$ -/

section Std

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **The radical of $\mathcal O_0(\pi^e)$**, $e \ge 1$ (Voight 2021, (23.4.17)), entrywise:
$\operatorname{rad}\mathcal O_0(\pi^e) = \begin{pmatrix} \pi R & R \\ \pi^eR & \pi R\end{pmatrix}$. -/
theorem mem_radSet_stdEichlerOrder {π : R} (hπ : Irreducible π) {e : ℕ} (he : 1 ≤ e)
    {j : Matrix (Fin 2) (Fin 2) K} :
    j ∈ radSet (stdEichlerOrder R K π e) ↔ ∃ j₁ j₂ j₃ j₄ : R,
      j = !![algebraMap R K (π * j₁), algebraMap R K j₂; algebraMap R K (π ^ e * j₃), algebraMap R K (π * j₄)] := by
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  have hπm : π ∈ IsLocalRing.maximalIdeal R := by rw [hmax]; exact Ideal.mem_span_singleton_self π
  constructor
  · rintro ⟨hj, hJ⟩
    rw [jacobson_stdEichlerOrder hπm he, RingHom.mem_ker, eichlerRes_eq_zero_iff, hmax,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton] at hJ
    obtain ⟨⟨j₁, h₁⟩, ⟨j₄, h₄⟩⟩ := hJ
    have h₁' : j 0 0 = algebraMap R K (π * j₁) := by rw [← h₁, algebraMap_intMat]
    have h₄' : j 1 1 = algebraMap R K (π * j₄) := by rw [← h₄, algebraMap_intMat]
    obtain ⟨hint, j₃, h₃⟩ := hj
    obtain ⟨j₂, h₂⟩ := hint 0 1
    refine ⟨j₁, j₂, j₃, j₄, ?_⟩
    ext i k; fin_cases i <;> fin_cases k <;> simp [h₁', h₄', h₃, ← h₂]
  · rintro ⟨j₁, j₂, j₃, j₄, rfl⟩
    have hmem : !![algebraMap R K (π * j₁), algebraMap R K j₂; algebraMap R K (π ^ e * j₃),
        algebraMap R K (π * j₄)] ∈ stdEichlerOrder R K π e := by
      refine ⟨fun i k => ?_, j₃, by simp⟩
      fin_cases i <;> fin_cases k
      · exact ⟨π * j₁, by simp⟩
      · exact ⟨j₂, by simp⟩
      · exact ⟨π ^ e * j₃, by simp⟩
      · exact ⟨π * j₄, by simp⟩
    refine ⟨hmem, ?_⟩
    rw [jacobson_stdEichlerOrder hπm he, RingHom.mem_ker, eichlerRes_eq_zero_iff, hmax,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    refine ⟨⟨j₁, ?_⟩, ⟨j₄, ?_⟩⟩ <;> apply IsFractionRing.injective R K <;> rw [algebraMap_intMat] <;> simp

/-- Conjugation by $P^{-1} = \operatorname{diag}(1, \pi^{-1})$: $P^{-1}xP = \begin{pmatrix} x_{00} & \pi x_{01} \\
\pi^{-1}x_{10} & x_{11}\end{pmatrix}$. -/
theorem diagQ_mul_mul_diagP {π : R} (hπ : π ≠ 0) (x : Matrix (Fin 2) (Fin 2) K) :
    diagQ π 1 * x * diagP π 1 =
      !![x 0 0, x 0 1 * algebraMap R K π; (algebraMap R K π)⁻¹ * x 1 0, x 1 1] := by
  have hp : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ
  ext i k; fin_cases i <;> fin_cases k <;> simp [diagQ, diagP, Matrix.mul_apply, Fin.sum_univ_two, mul_comm] <;>
    field_simp

/-- The conjugate $P\,\mathcal O_0(\pi^k)P^{-1}$, $P = \operatorname{diag}(1, \pi)$, is
$\begin{pmatrix} R & \pi^{-1}R \\ \pi^{k+1}R & R\end{pmatrix}$. -/
theorem mem_map_conj_diag {π : R} (hπ : π ≠ 0) (k : ℕ) {x : Matrix (Fin 2) (Fin 2) K} :
    x ∈ (stdEichlerOrder R K π k).map ((conjAlgEquiv (diagP (K := K) π 1) (diagQ π 1) (diagP_mul_diagQ hπ 1)
        (diagQ_mul_diagP hπ 1) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R) ↔
      ∃ a b c d : R, x = !![algebraMap R K a, algebraMap R K b * (algebraMap R K π)⁻¹;
        algebraMap R K (π ^ (k + 1) * c), algebraMap R K d] := by
  have hp : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ
  rw [mem_map_conj, diagQ_mul_mul_diagP hπ, mem_stdEichlerOrder]
  constructor
  · rintro ⟨hint, c, hc⟩
    obtain ⟨a, ha⟩ := hint 0 0
    obtain ⟨b, hb⟩ := hint 0 1
    obtain ⟨d, hd⟩ := hint 1 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at ha hb hd hc
    have h01 : x 0 1 = algebraMap R K b * (algebraMap R K π)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hp, hb]
    have h10 : x 1 0 = algebraMap R K (π ^ (k + 1) * c) := by
      have : x 1 0 = algebraMap R K π * ((algebraMap R K π)⁻¹ * x 1 0) := by field_simp
      rw [this, hc]; simp only [map_mul, map_pow]; ring
    refine ⟨a, b, c, d, ?_⟩
    rw [Matrix.eta_fin_two x, ← ha, ← hd, h01, h10]
  · rintro ⟨a, b, c, d, rfl⟩
    refine ⟨fun i k => ?_, c, ?_⟩
    · fin_cases i <;> fin_cases k
      · exact ⟨a, by simp⟩
      · exact ⟨b, by simp [hp]⟩
      · exact ⟨π ^ k * c, by simp; field_simp; ring⟩
      · exact ⟨d, by simp⟩
    · simp; field_simp; ring

/-- **The radical idealizer of the standard Eichler order** (Voight 2021, 24.4.5): for $e = k + 2 \ge 2$,
$\mathcal O_0(\pi^{k+2})^\natural = \begin{pmatrix} R & \pi^{-1}R \\ \pi^{k+1}R & R\end{pmatrix} = P\,\mathcal O_0(\pi^k)P^{-1}$ with
$P = \operatorname{diag}(1, \pi)$: an Eichler order of level $\pi^k = \pi^{e-2}$, obtained (on the Bruhat–Tits tree) by
removing the two end vertices of the path of length $e$. -/
@[kb "voight2021" "24.4.5, p. 403"]
theorem radIdealizer_stdEichlerOrder {π : R} (hπ : Irreducible π) (k : ℕ) :
    radIdealizer (stdEichlerOrder R K π (k + 2)) =
      (stdEichlerOrder R K π k).map ((conjAlgEquiv (diagP (K := K) π 1) (diagQ π 1) (diagP_mul_diagQ hπ.ne_zero 1)
        (diagQ_mul_diagP hπ.ne_zero 1) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R) := by
  have hp : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  have he : 1 ≤ k + 2 := by omega
  ext x
  rw [mem_map_conj_diag hπ.ne_zero]
  constructor
  · rintro ⟨hL, -⟩
    -- test elements E₀₁, πE₀₀, πE₁₁ of the radical
    obtain ⟨n₁, n₂, n₃, n₄, hn⟩ := (mem_radSet_stdEichlerOrder hπ he).1
      (hL _ ((mem_radSet_stdEichlerOrder (K := K) hπ he).2 ⟨0, 1, 0, 0, rfl⟩))
    obtain ⟨m₁, m₂, m₃, m₄, hm⟩ := (mem_radSet_stdEichlerOrder hπ he).1
      (hL _ ((mem_radSet_stdEichlerOrder (K := K) hπ he).2 ⟨1, 0, 0, 0, rfl⟩))
    obtain ⟨l₁, l₂, l₃, l₄, hl⟩ := (mem_radSet_stdEichlerOrder hπ he).1
      (hL _ ((mem_radSet_stdEichlerOrder (K := K) hπ he).2 ⟨0, 0, 0, 1, rfl⟩))
    have e00 : x 0 0 = algebraMap R K n₂ := by
      have := congrFun (congrFun hn 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have e10 : x 1 0 * algebraMap R K π = algebraMap R K π ^ (k + 2) * algebraMap R K m₃ := by
      have := congrFun (congrFun hm 1) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have f01 : x 0 1 * algebraMap R K π = algebraMap R K l₂ := by
      have := congrFun (congrFun hl 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have f11 : x 1 1 * algebraMap R K π = algebraMap R K π * algebraMap R K l₄ := by
      have := congrFun (congrFun hl 1) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h01 : x 0 1 = algebraMap R K l₂ * (algebraMap R K π)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hp, f01]
    have h10 : x 1 0 = algebraMap R K (π ^ (k + 1) * m₃) := by
      apply mul_right_cancel₀ hp
      rw [e10]; simp only [map_mul, map_pow]; ring
    have h11 : x 1 1 = algebraMap R K l₄ := by
      apply mul_right_cancel₀ hp
      rw [f11]; ring
    refine ⟨n₂, l₂, m₃, l₄, ?_⟩
    rw [Matrix.eta_fin_two x, e00, h01, h10, h11]
  · rintro ⟨a, b, c, d, rfl⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩ <;>
      obtain ⟨j₁, j₂, j₃, j₄, rfl⟩ := (mem_radSet_stdEichlerOrder hπ he).1 hj <;>
      rw [mem_radSet_stdEichlerOrder hπ he]
    · refine ⟨a * j₁ + b * π ^ k * j₃, a * j₂ + b * j₄, c * j₁ + d * j₃, π ^ k * c * j₂ + d * j₄, ?_⟩
      ext i l; fin_cases i <;> fin_cases l <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    · refine ⟨j₁ * a + j₂ * π ^ k * c, j₁ * b + j₂ * d, j₃ * a + j₄ * c, π ^ k * j₃ * b + j₄ * d, ?_⟩
      ext i l; fin_cases i <;> fin_cases l <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- **The radical idealizer of a standard Eichler order of level $\pi^{k+2}$ is an Eichler order** (Voight 2021, 24.4.5;
it has level $\pi^k$ by `radIdealizer_stdEichlerOrder`). -/
@[kb "voight2021" "24.4.5, p. 403"]
theorem isEichler_radIdealizer_stdEichlerOrder {π : R} (hπ : Irreducible π) (k : ℕ) :
    IsEichler R K (radIdealizer (stdEichlerOrder R K π (k + 2))) := by
  rw [radIdealizer_stdEichlerOrder hπ k]
  exact IsEichler.map_conj (isEichler_stdEichlerOrder hπ.ne_zero k) _ _

end Std

end QuadFormsKB.Voight.Wave7
