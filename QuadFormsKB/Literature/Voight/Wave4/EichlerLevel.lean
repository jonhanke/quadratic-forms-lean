/-
# The level of a local Eichler order is well defined (Voight, 23.4.12)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`), 23.4.12 (p. 384) and
Definition 23.4.11 (p. 384): an Eichler order $\mathcal O \simeq \mathcal O_0(\mathfrak p^e)$ of $\mathrm M_2(F)$ over a discrete
valuation ring $R$ has reduced discriminant $\operatorname{discrd}\mathcal O = \mathfrak p^e$, so its level $\mathfrak p^e$ is
determined by $\mathcal O$.

**Setting.** As in `EichlerStructure.lean`: $R$ a discrete valuation ring with fraction field $F$ (written `K`),
uniformizer $\pi$, $\mathcal O_0(\pi^e)$ is `Wave3.stdEichlerOrder R K π e`, and conjugation $x \mapsto PxP^{-1}$ is
`QuatOrder.conjAlgEquiv P Q` with $Q = P^{-1}$.

**Contents.**
* `eq_of_conj_stdEichlerOrder`: if $P\,\mathcal O_0(\pi^e)P^{-1} = \mathcal O_0(\pi^f)$ then $e = f$. Proof: conjugation
  preserves the reduced trace, so the conjugated standard basis of $\mathcal O_0(\pi^e)$ is a basis of $\mathcal O_0(\pi^f)$
  with trace Gram determinant $-\pi^{2e}$; by `det_gram_basis` this is a unit times $-\pi^{2f}$.
* `existsUnique_level`: every Eichler order of $\mathrm M_2(F)$ is conjugate to $\mathcal O_0(\pi^e)$ for exactly one
  $e \ge 0$ (its level is $\mathfrak p^e$).

All proved; no inputs.
-/
import QuadFormsKB.Literature.Voight.Wave4.EichlerStructure
import QuadFormsKB.Literature.Voight.Wave4.EichlerDiscriminant

set_option linter.unusedSectionVars false

open Matrix

noncomputable section

namespace QuadFormsKB.Voight.Wave4

open QuadFormsKB.QuatOrder QuadFormsKB.Voight.Wave3

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Conjugation preserves the trace of products: $\operatorname{tr}(PxQ \cdot PyQ) = \operatorname{tr}(xy)$ when $QP = 1$. -/
theorem trace_conj_mul_conj {P Q x y : Matrix (Fin 2) (Fin 2) K} (hQP : Q * P = 1) :
    Matrix.trace (P * x * Q * (P * y * Q)) = Matrix.trace (x * y) := by
  have : P * x * Q * (P * y * Q) = P * (x * y * Q) := by
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, hQP, Matrix.mul_one]

variable [IsDiscreteValuationRing R]

/-- **The level of $\mathcal O_0(\pi^e)$ is an invariant** (Voight 2021, 23.4.12 with Definition 23.4.11): over a discrete
valuation ring with uniformizer $\pi$, if a conjugate $P\,\mathcal O_0(\pi^e)P^{-1}$ ($P \in \mathrm{GL}_2(F)$, $Q = P^{-1}$)
equals $\mathcal O_0(\pi^f)$, then $e = f$. -/
@[kb "voight2021" "23.4.12, p. 384"]
theorem eq_of_conj_stdEichlerOrder {π : R} (hπ : Irreducible π) {e f : ℕ} {P Q : Matrix (Fin 2) (Fin 2) K}
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h : (stdEichlerOrder R K π e).map
        (((conjAlgEquiv P Q hPQ hQP) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R) =
      stdEichlerOrder R K π f) : e = f := by
  set φ : Matrix (Fin 2) (Fin 2) K →ₐ[R] Matrix (Fin 2) (Fin 2) K :=
    ((conjAlgEquiv P Q hPQ hQP) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R with hφ
  have hinj : Function.Injective φ.toLinearMap := (conjAlgEquiv P Q hPQ hQP).injective
  have hsub : (Subalgebra.toSubmodule (stdEichlerOrder R K π e)).map φ.toLinearMap =
      Subalgebra.toSubmodule (stdEichlerOrder R K π f) := by
    rw [← Subalgebra.map_toSubmodule, h]
  set L := (Submodule.equivMapOfInjective φ.toLinearMap hinj (Subalgebra.toSubmodule (stdEichlerOrder R K π e))).trans
    (LinearEquiv.ofEq _ _ hsub)
  set f' := (stdEichlerBasisR (K := K) hπ.ne_zero e).map L
  have hf' : ∀ p, (f' p : Matrix (Fin 2) (Fin 2) K) = P * stdEichlerBasis π e p * Q := by
    intro p
    simp only [f', L, Module.Basis.map_apply, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      Submodule.coe_equivMapOfInjective_apply, stdEichlerBasisR_apply]
    rfl
  obtain ⟨u, hu⟩ := det_gram_basis (e := f) hπ.ne_zero f'
  simp only [hf', trace_conj_mul_conj hQP] at hu
  rw [det_gram_stdEichlerBasis] at hu
  have hR : algebraMap R K (π ^ (2 * e)) = algebraMap R K ((u : R) * π ^ (2 * f)) := by
    simp only [map_mul, map_pow, pow_mul']
    linear_combination -hu
  have hR' := IsFractionRing.injective R K hR
  have : ((1 : Rˣ) : R) * π ^ (2 * e) = (u : R) * π ^ (2 * f) := by rw [Units.val_one, one_mul, hR']
  have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hπ hπ 1 u _ _ this
  omega

/-- **Every local Eichler order has a unique level** (Voight 2021, Proposition 23.4.3 and 23.4.12): over a discrete
valuation ring with uniformizer $\pi$, an Eichler order $\mathcal O \subseteq \mathrm M_2(F)$ is conjugate to
$\mathcal O_0(\pi^e)$ for exactly one $e \ge 0$. -/
@[kb "voight2021" "23.4.12, p. 384"]
theorem existsUnique_level {π : R} (hπ : Irreducible π) {O : Subalgebra R (Matrix (Fin 2) (Fin 2) K)}
    (hO : IsEichler R K O) :
    ∃! e : ℕ, ∃ (P Q : Matrix (Fin 2) (Fin 2) K) (hPQ : P * Q = 1) (hQP : Q * P = 1),
      O = (stdEichlerOrder R K π e).map
        (((conjAlgEquiv P Q hPQ hQP) : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) K).restrictScalars R) := by
  obtain ⟨e, P, Q, hPQ, hQP, hOe⟩ := localEichlerStructure hπ O hO
  refine ⟨e, ⟨P, Q, hPQ, hQP, hOe⟩, ?_⟩
  rintro f ⟨P', Q', hPQ', hQP', hOf⟩
  -- conjugate by `Q' P` (inverse `Q P'`): it carries `O_0(π^e)` to `O_0(π^f)`.
  have h1 : (Q' * P) * (Q * P') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul, hQP']
  have h2 : (Q * P') * (Q' * P) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P' Q', hPQ', Matrix.one_mul, hQP]
  refine (eq_of_conj_stdEichlerOrder hπ h1 h2 ?_).symm
  ext x
  rw [mem_map_conj]
  have hx : x ∈ stdEichlerOrder R K π f ↔ P' * x * Q' ∈ O := by
    rw [hOf, mem_map_conj]
    rw [show Q' * (P' * x * Q') * P' = x by
      simp only [← Matrix.mul_assoc, hQP', Matrix.one_mul]; rw [Matrix.mul_assoc, hQP', Matrix.mul_one]]
  rw [hx, hOe, mem_map_conj]
  constructor <;> intro hm <;> convert hm using 1 <;> simp only [Matrix.mul_assoc]
