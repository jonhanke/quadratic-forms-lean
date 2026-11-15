/-
# The residue ring of a local Eichler order (Voight, 23.4.15-23.4.17)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): 23.4.15 and (23.4.17), p. 385.

**Setting.** $R$ a discrete valuation ring with fraction field $F$ (Lean: `K`), uniformizer $\pi$, residue field
$k = R/\mathfrak p$; $e \ge 1$ and $\mathcal O = \mathcal O_0(\pi^e) = \begin{pmatrix} R & R \\ \pi^eR & R\end{pmatrix}$
(`stdEichlerOrder`). Entries are indexed $0, 1$.

**Contents** (proved).
* `eichlerRes`: the ring homomorphism $\mathcal O \to k \times k$, $x \mapsto (x_{00} \bmod \mathfrak p, x_{11} \bmod \mathfrak p)$.
* `eichlerRes_surjective` and `eichlerRes_eq_zero_iff` (**(23.4.17)**): it is surjective with kernel
  $J = \begin{pmatrix} \mathfrak p & R \\ \mathfrak p^e & \mathfrak p\end{pmatrix}$, i.e. $\mathcal O/J \cong k \times k$.
  (The book then identifies $J$ with the Jacobson radical $\operatorname{rad}\mathcal O$; that identification is not
  formalized here.)
-/
import QuadFormsKB.Literature.Voight.Wave4.EichlerIndex
import QuadFormsKB.Literature.Voight.Wave4.EichlerStructure

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave5

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4 IsLocalization

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The integral matrix $A \in \mathrm M_2(R)$ of an element $x \in \mathcal O_0(\pi^e) \subseteq \mathrm M_2(R)$. -/
def intMat {π : R} {e : ℕ} (x : stdEichlerOrder R K π e) : Matrix (Fin 2) (Fin 2) R :=
  (toMatOrder R K).symm ⟨x, stdEichlerOrder_le_matOrder π e x.2⟩

theorem intMat_map {π : R} {e : ℕ} (x : stdEichlerOrder R K π e) :
    (intMat x).map (algebraMap R K) = (x : Matrix (Fin 2) (Fin 2) K) := by
  have := congrArg Subtype.val
    ((toMatOrder R K).apply_symm_apply ⟨(x : Matrix (Fin 2) (Fin 2) K), stdEichlerOrder_le_matOrder π e x.2⟩)
  rw [toMatOrder_val] at this
  exact this

theorem algebraMap_intMat {π : R} {e : ℕ} (x : stdEichlerOrder R K π e) (i j : Fin 2) :
    algebraMap R K (intMat x i j) = (x : Matrix (Fin 2) (Fin 2) K) i j := by
  rw [← intMat_map x]; rfl

theorem intMat_mul {π : R} {e : ℕ} (x y : stdEichlerOrder R K π e) : intMat (x * y) = intMat x * intMat y :=
  map_mul (toMatOrder R K).symm
    ⟨(x : Matrix (Fin 2) (Fin 2) K), stdEichlerOrder_le_matOrder π e x.2⟩
    ⟨(y : Matrix (Fin 2) (Fin 2) K), stdEichlerOrder_le_matOrder π e y.2⟩

theorem intMat_add {π : R} {e : ℕ} (x y : stdEichlerOrder R K π e) : intMat (x + y) = intMat x + intMat y :=
  map_add (toMatOrder R K).symm
    ⟨(x : Matrix (Fin 2) (Fin 2) K), stdEichlerOrder_le_matOrder π e x.2⟩
    ⟨(y : Matrix (Fin 2) (Fin 2) K), stdEichlerOrder_le_matOrder π e y.2⟩

theorem intMat_one {π : R} {e : ℕ} : intMat (1 : stdEichlerOrder R K π e) = 1 :=
  map_one (toMatOrder R K).symm

theorem intMat_zero {π : R} {e : ℕ} : intMat (0 : stdEichlerOrder R K π e) = 0 :=
  map_zero (toMatOrder R K).symm

/-- The lower left entry of an element of $\mathcal O_0(\pi^e)$ is divisible by $\pi^e$. -/
theorem pow_dvd_intMat_one_zero {π : R} {e : ℕ} (x : stdEichlerOrder R K π e) : π ^ e ∣ intMat x 1 0 := by
  obtain ⟨-, r, hr⟩ := x.2
  refine ⟨r, IsFractionRing.injective R K ?_⟩
  rw [algebraMap_intMat, hr]

variable [IsLocalRing R]

/-- **The residue map** $\mathcal O_0(\pi^e) \to k \times k$, $x \mapsto (x_{00} \bmod \mathfrak p, x_{11} \bmod \mathfrak p)$
(Voight 2021, (23.4.17)), a ring homomorphism for $e \ge 1$ and $\pi$ in the maximal ideal. -/
@[kb "voight2021" "23.4.15, (23.4.17), p. 385"]
def eichlerRes {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) {e : ℕ} (he : 1 ≤ e) :
    stdEichlerOrder R K π e →+* IsLocalRing.ResidueField R × IsLocalRing.ResidueField R where
  toFun x := (IsLocalRing.residue R (intMat x 0 0), IsLocalRing.residue R (intMat x 1 1))
  map_one' := by simp [intMat_one]
  map_zero' := by simp [intMat_zero]
  map_add' x y := by simp [intMat_add]
  map_mul' x y := by
    have hm : ∀ z : stdEichlerOrder R K π e, IsLocalRing.residue R (intMat z 1 0) = 0 := fun z => by
      rw [IsLocalRing.residue_eq_zero_iff]
      obtain ⟨c, hc⟩ := pow_dvd_intMat_one_zero z
      rw [hc]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
      rw [pow_add, pow_one, mul_assoc]
      exact Ideal.mul_mem_right _ _ hπ
    simp only [intMat_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, hm, mul_zero, zero_mul, add_zero,
      zero_add, Prod.mk_mul_mk]

theorem eichlerRes_apply {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) {e : ℕ} (he : 1 ≤ e)
    (x : stdEichlerOrder R K π e) :
    eichlerRes hπ he x = (IsLocalRing.residue R (intMat x 0 0), IsLocalRing.residue R (intMat x 1 1)) := rfl

/-- **(23.4.17)** (Voight 2021): the residue map $\mathcal O_0(\pi^e) \to k \times k$ is surjective. -/
@[kb "voight2021" "(23.4.17), p. 385"]
theorem eichlerRes_surjective {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) {e : ℕ} (he : 1 ≤ e) :
    Function.Surjective (eichlerRes (K := K) hπ he) := by
  rintro ⟨a, b⟩
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective b
  have hmem : diagK (K := K) r s ∈ stdEichlerOrder R K π e := by
    rw [mem_stdEichlerOrder]
    refine ⟨fun i j => ⟨!![r, 0; 0, s] i j, rfl⟩, 0, ?_⟩
    simp
  refine ⟨⟨_, hmem⟩, ?_⟩
  have h : ∀ i j, intMat (⟨_, hmem⟩ : stdEichlerOrder R K π e) i j = !![r, 0; 0, s] i j := fun i j =>
    IsFractionRing.injective R K (by rw [algebraMap_intMat]; rfl)
  rw [eichlerRes_apply, h, h]
  simp

/-- **The kernel of the residue map** (Voight 2021, 23.4.15 and (23.4.17)): $x \in \mathcal O_0(\pi^e)$ maps to $0$ iff
$x_{00}, x_{11} \in \mathfrak p$, i.e. $x \in J = \begin{pmatrix} \mathfrak p & R \\ \mathfrak p^e & \mathfrak p\end{pmatrix}$; so
$\mathcal O/J \cong k \times k$. -/
@[kb "voight2021" "23.4.15, (23.4.17), p. 385"]
theorem eichlerRes_eq_zero_iff {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) {e : ℕ} (he : 1 ≤ e)
    (x : stdEichlerOrder R K π e) :
    eichlerRes hπ he x = 0 ↔
      intMat x 0 0 ∈ IsLocalRing.maximalIdeal R ∧ intMat x 1 1 ∈ IsLocalRing.maximalIdeal R := by
  rw [eichlerRes_apply, Prod.mk_eq_zero, IsLocalRing.residue_eq_zero_iff, IsLocalRing.residue_eq_zero_iff]

end QuadFormsKB.Voight.Wave5
