/-
# The standard local Eichler order (Voight, Definition 23.4.1, Proposition 23.4.3, Lemma 23.5.15)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Definition 23.4.1 (p. 391),
Proposition 23.4.3 (p. 392), Lemma 23.5.15 (p. 399).

**Model.** $R$ an integrally closed domain with fraction field $K$ (in the application a complete discrete valuation
ring), $\pi \in R$ nonzero, $e \ge 0$. The **standard Eichler order of level $\pi^e$** is
$$\mathcal O_0(\pi^e) = \begin{pmatrix} R & R \\ \pi^e R & R\end{pmatrix} \subseteq \mathrm M_2(K)$$
(`stdEichlerOrder R K π e`; entries indexed $0, 1$, so the lower left entry is $x_{10}$).

**Contents.**
* `IsEichler R K O` (Definition 23.4.1 for any $K$-algebra): $\mathcal O = \mathcal O_1 \cap \mathcal O_2$ with $\mathcal O_1, \mathcal O_2$ maximal
  orders.
* `stdEichlerOrder_eq_inf` (Lemma 23.5.15): $\mathcal O_0(\pi^e) = \mathrm M_2(R) \cap P\,\mathrm M_2(R)\,P^{-1}$ with
  $P = \operatorname{diag}(1, \pi^e)$, the endomorphism rings of the lattices $R x_1 \oplus R x_2$ and
  $R x_1 \oplus \pi^e R x_2$.
* `isEichler_stdEichlerOrder` (Proposition 23.4.3, (c) $\Rightarrow$ (a)): $\mathcal O_0(\pi^e)$ is an Eichler order.
* `LocalEichlerStructure R K` (Proposition 23.4.3, (a) $\Rightarrow$ (c)): every Eichler order of $\mathrm M_2(K)$ is
  conjugate to some $\mathcal O_0(\pi^e)$ ($R$ a discrete valuation ring with uniformizer $\pi$). Stated, not proved.
-/
import QuadFormsKB.Tamagawa.MatOrder

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave3

open QuadFormsKB.QuatOrder IsLocalization

/-- **Eichler order** (Voight 2021, Definition 23.4.1): an $R$-order $\mathcal O$ of the $K$-algebra $A$ is an Eichler order
if $\mathcal O = \mathcal O_1 \cap \mathcal O_2$ for two (not necessarily distinct) maximal $R$-orders $\mathcal O_1, \mathcal O_2$. -/
@[kb "voight2021" "Definition 23.4.1, p. 391"]
def IsEichler (R K : Type*) {A : Type*} [CommRing R] [Field K] [Algebra R K] [Ring A] [Algebra K A] [Algebra R A]
    [IsScalarTower R K A] (O : Subalgebra R A) : Prop :=
  ∃ O₁ O₂ : Subalgebra R A, IsMaximalOrder R K O₁ ∧ IsMaximalOrder R K O₂ ∧ O = O₁ ⊓ O₂

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The standard Eichler order of level $\pi^e$** (Voight 2021, Proposition 23.4.3 (c) and 23.4.12):
$\mathcal O_0(\pi^e) = \{x \in \mathrm M_2(R) : x_{10} \in \pi^eR\}$. -/
@[kb "voight2021" "Proposition 23.4.3, p. 392"]
def stdEichlerOrder (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (e : ℕ) : Subalgebra R (Matrix (Fin 2) (Fin 2) K) where
  carrier := {x | (∀ i j, IsInteger R (x i j)) ∧ ∃ r : R, x 1 0 = algebraMap R K (π ^ e * r)}
  mul_mem' {x y} hx hy := by
    obtain ⟨hxi, r, hr⟩ := hx
    obtain ⟨hyi, s, hs⟩ := hy
    refine ⟨fun i j => ?_, ?_⟩
    · obtain ⟨p0, hp0⟩ := hxi i 0; obtain ⟨p1, hp1⟩ := hxi i 1
      obtain ⟨q0, hq0⟩ := hyi 0 j; obtain ⟨q1, hq1⟩ := hyi 1 j
      exact ⟨p0 * q0 + p1 * q1, by
        rw [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_mul, hp0, hp1, hq0, hq1]⟩
    · obtain ⟨q0, hq0⟩ := hyi 0 0; obtain ⟨p1, hp1⟩ := hxi 1 1
      refine ⟨r * q0 + p1 * s, ?_⟩
      rw [Matrix.mul_apply, Fin.sum_univ_two, hr, hs, ← hq0, ← hp1]
      simp only [map_mul, map_add, map_pow]; ring
  one_mem' := ⟨fun i j => by
      by_cases h : i = j
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Matrix.one_apply_ne h]⟩, 0, by simp⟩
  add_mem' {x y} hx hy := by
    obtain ⟨hxi, r, hr⟩ := hx
    obtain ⟨hyi, s, hs⟩ := hy
    refine ⟨fun i j => ?_, r + s, ?_⟩
    · obtain ⟨p, hp⟩ := hxi i j; obtain ⟨q, hq⟩ := hyi i j
      exact ⟨p + q, by rw [Matrix.add_apply, map_add, hp, hq]⟩
    · rw [Matrix.add_apply, hr, hs, mul_add, map_add]
  zero_mem' := ⟨fun i j => ⟨0, by simp⟩, 0, by simp⟩
  algebraMap_mem' c := ⟨fun i j => by
      by_cases h : i = j
      · subst h; exact ⟨c, by simp [Matrix.algebraMap_matrix_apply]⟩
      · exact ⟨0, by simp [Matrix.algebraMap_matrix_apply, h]⟩, 0, by simp [Matrix.algebraMap_matrix_apply]⟩

theorem mem_stdEichlerOrder {π : R} {e : ℕ} {x : Matrix (Fin 2) (Fin 2) K} :
    x ∈ stdEichlerOrder R K π e ↔ (∀ i j, IsInteger R (x i j)) ∧ ∃ r : R, x 1 0 = algebraMap R K (π ^ e * r) :=
  Iff.rfl

/-- $P = \operatorname{diag}(1, \pi^e)$. -/
abbrev diagP (π : R) (e : ℕ) : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![1, algebraMap R K π ^ e]
/-- $P^{-1} = \operatorname{diag}(1, \pi^{-e})$. -/
abbrev diagQ (π : R) (e : ℕ) : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![1, (algebraMap R K π ^ e)⁻¹]

theorem diagP_mul_diagQ {π : R} (hπ : π ≠ 0) (e : ℕ) : diagP (K := K) π e * diagQ π e = 1 := by
  have h : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ
  rw [diagP, diagQ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; fin_cases i <;> simp [h]

theorem diagQ_mul_diagP {π : R} (hπ : π ≠ 0) (e : ℕ) : diagQ (K := K) π e * diagP π e = 1 := by
  have h : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ
  rw [diagP, diagQ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; fin_cases i <;> simp [h]

/-- The conjugate maximal order $P\,\mathrm M_2(R)\,P^{-1}$, $P = \operatorname{diag}(1,\pi^e)$. -/
abbrev conjMatOrder {π : R} (hπ : π ≠ 0) (e : ℕ) : Subalgebra R (Matrix (Fin 2) (Fin 2) K) :=
  (matOrder R K).map (((conjAlgEquiv (diagP (K := K) π e) (diagQ (K := K) π e) (diagP_mul_diagQ (K := K) hπ e)
    (diagQ_mul_diagP (K := K) hπ e)) :
    Matrix (Fin 2) (Fin 2) K →ₐ[K] _).restrictScalars R)

theorem mem_conjMatOrder {π : R} (hπ : π ≠ 0) (e : ℕ) (x : Matrix (Fin 2) (Fin 2) K) :
    x ∈ conjMatOrder hπ e ↔ diagQ π e * x * diagP π e ∈ matOrder R K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change diagQ π e * (diagP π e * y * diagQ π e) * diagP π e ∈ _
    simp only [← mul_assoc, diagQ_mul_diagP hπ, one_mul]
    rw [mul_assoc, diagQ_mul_diagP hπ, mul_one]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    change diagP π e * (diagQ π e * x * diagP π e) * diagQ π e = x
    simp only [← mul_assoc, diagP_mul_diagQ hπ, one_mul]
    rw [mul_assoc, diagP_mul_diagQ hπ, mul_one]

/-- **The standard Eichler order is an intersection of two maximal orders** (Voight 2021, Lemma 23.5.15):
$\mathcal O_0(\pi^e) = \mathrm M_2(R) \cap P\,\mathrm M_2(R)\,P^{-1}$, $P = \operatorname{diag}(1, \pi^e)$. -/
@[kb "voight2021" "Lemma 23.5.15, p. 399"]
theorem stdEichlerOrder_eq_inf {π : R} (hπ : π ≠ 0) (e : ℕ) :
    stdEichlerOrder R K π e = matOrder R K ⊓ conjMatOrder hπ e := by
  have h : algebraMap R K π ^ e ≠ 0 := pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ)
  ext x
  change _ ↔ x ∈ matOrder R K ∧ x ∈ conjMatOrder hπ e
  rw [mem_conjMatOrder, mem_matOrder, mem_matOrder, mem_stdEichlerOrder]
  have hc : ∀ i j, (diagQ π e * x * diagP π e : Matrix (Fin 2) (Fin 2) K) i j = ![1, (algebraMap R K π ^ e)⁻¹] i * x i j *
      ![1, algebraMap R K π ^ e] j := fun i j => by
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  constructor
  · rintro ⟨hx, r, hr⟩
    refine ⟨hx, fun i j => ?_⟩
    rw [hc]
    fin_cases i <;> fin_cases j
    · simpa using hx 0 0
    · obtain ⟨p, hp⟩ := hx 0 1
      exact ⟨p * π ^ e, by simp [← hp, map_pow]⟩
    · refine ⟨r, ?_⟩
      change algebraMap R K r = (algebraMap R K π ^ e)⁻¹ * x 1 0 * 1
      rw [hr, map_mul, map_pow]; field_simp
    · obtain ⟨p, hp⟩ := hx 1 1
      refine ⟨p, ?_⟩
      change algebraMap R K p = (algebraMap R K π ^ e)⁻¹ * x 1 1 * algebraMap R K π ^ e
      rw [hp]; field_simp
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    obtain ⟨r, hr⟩ := hy 1 0
    rw [hc] at hr
    refine ⟨r, ?_⟩
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, mul_one] at hr
    rw [map_mul, map_pow, hr]; field_simp

variable [IsIntegrallyClosed R]

/-- **The standard Eichler order of level $\pi^e$ is an Eichler order** (Voight 2021, Proposition 23.4.3,
(c) $\Rightarrow$ (a)), $R$ integrally closed, $\pi \ne 0$. -/
@[kb "voight2021" "Proposition 23.4.3, p. 392; Lemma 23.5.15, p. 399"]
theorem isEichler_stdEichlerOrder {π : R} (hπ : π ≠ 0) (e : ℕ) : IsEichler R K (stdEichlerOrder R K π e) :=
  ⟨_, _, isMaximalOrder_matOrder,
    (isMaximalOrder_matOrder (R := R) (K := K)).map (conjAlgEquiv (diagP π e) (diagQ π e)
      (diagP_mul_diagQ hπ e) (diagQ_mul_diagP hπ e)), stdEichlerOrder_eq_inf (K := K) hπ e⟩

/-- **Local structure of Eichler orders** (Voight 2021, Proposition 23.4.3, (a) $\Rightarrow$ (c)), as a named
proposition about a discrete valuation ring $R$ with uniformizer $\pi$: every Eichler $R$-order of $\mathrm M_2(K)$ is
conjugate, by some $P \in \mathrm{GL}_2(K)$, to the standard Eichler order $\mathcal O_0(\pi^e)$ of some level $\pi^e$.
Stated, not proved (it needs the adapted bases of Lemma 23.5.1 / the Bruhat–Tits tree). -/
@[kb "voight2021" "Proposition 23.4.3, p. 392"]
def LocalEichlerStructure (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) : Prop :=
  ∀ O : Subalgebra R (Matrix (Fin 2) (Fin 2) K), IsEichler R K O →
    ∃ (e : ℕ) (P Q : Matrix (Fin 2) (Fin 2) K) (hPQ : P * Q = 1) (hQP : Q * P = 1),
      O = (stdEichlerOrder R K π e).map (((conjAlgEquiv P Q hPQ hQP) : _ →ₐ[K] _).restrictScalars R)

end QuadFormsKB.Voight.Wave3
