/-
# The Schrödinger operators on tensor products $V^{r+1} = V \otimes V^r$ (for $\Phi E^{(r+1)} = E^{(r)}$)

**Layer:** local harmonic analysis over a field $K$, for any `LocalData K` (no model axioms beyond $\sigma$-finiteness of the measure
in the one statement that integrates).

**Setting.** $V = K^{2m}$ with $Q(x) = \sum_i a_ix_i^2$ and $V^{g} = M_{2m\times g}(K)$ (`PtG`). A point $X \in V^{r+1}$ splits into its
column $0$, `headG X` $\in V^1$, and its columns $1, \dots, r$, `tailG X` $\in V^r$ (renumbered $0, \dots, r-1$). For
$\varphi : V^1 \to \mathbb C$ and $\Phi : V^r \to \mathbb C$ the tensor product is
$(\varphi\otimes\Phi)(X) = \varphi(\mathrm{head}\,X)\,\Phi(\mathrm{tail}\,X)$ (`tensG`).

**Results.** The operators of the Schrödinger model (`opNg`, `opMg`, `opWg`) of the generators of $\mathrm{Sp}_{2r+2}$ that come from
$\mathrm{Sp}_{2r}\times\mathrm{Sp}_2$ act column by column on tensor products:
* `tensG_mem`: $\varphi\otimes\Phi \in S(V^{r+1})$ for $\varphi \in S(V^1)$ and $\Phi \in S(V^r)$;
* `det_extC`: $\det(\mathrm{extC}\,c\,X) = c\det X$;
* `QX_extC_trace`: $\operatorname{tr}(\mathrm{extC}\,b\,B\cdot Q[X]) = b\,Q[x_0]_{00} + \operatorname{tr}(B\,Q[\mathrm{tail}\,X])$;
* `opNg_extC`: $\omega(n(\mathrm{extC}\,b\,B))(\varphi\otimes\Phi) = \omega(n(b))\varphi\otimes\omega(n(B))\Phi$;
* `opMg_extGL`: $\omega(m(\mathrm{extC}\,1\,A))(\varphi\otimes\Phi) = \varphi\otimes\omega(m(A))\Phi$;
* `opWg_tensG`: $\omega(w)(\varphi\otimes\Phi) = \omega(w)\varphi\otimes\omega(w)\Phi$ (Fubini, via the measure-preserving
  equivalence `splitEquiv` $V^{r+1} \cong V^1\times V^r$), assuming `D.IsOps` (only for $\sigma$-finiteness of $\mu$).

Source: Kudla, *Notes on the local theta correspondence* (1996), §I.1, Prop. 1.3 (Schrödinger model) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.PhiEmbed
import QuadFormsKB.Weil.Genus.Model

open Matrix MeasureTheory

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open QuadFormsKB.WeilRep QuadFormsKB.WeilRep.Genus QuadFormsKB.WeilRep.LocalData

variable {K : Type*} [Field K] [MeasurableSpace K] {m r : ℕ} {D : LocalData K} {a : Fin (2 * m) → Kˣ}

/-- Column 0 of $X$, as a point of $V^1$. -/
def headG (X : PtG m (r + 1) K) : PtG m 1 K := fun i _ => X i 0

/-- Columns $1, \dots, r$ of $X$ (renumbered $0, \dots, r-1$), as a point of $V^r$. -/
def tailG (X : PtG m (r + 1) K) : PtG m r K := fun i j => X i j.succ

/-- The tensor product $(\varphi\otimes\Phi)(X) = \varphi(\mathrm{head}\,X)\,\Phi(\mathrm{tail}\,X)$. -/
def tensG (φ : PtG m 1 K → ℂ) (Φ : PtG m r K → ℂ) : PtG m (r + 1) K → ℂ :=
  fun X => φ (headG X) * Φ (tailG X)

lemma tensG_add_left (φ φ' : PtG m 1 K → ℂ) (Φ : PtG m r K → ℂ) :
    tensG φ Φ + tensG φ' Φ = tensG (φ + φ') Φ := by
  ext X; simp [tensG, add_mul]

lemma tensG_smul_left (c : ℂ) (φ : PtG m 1 K → ℂ) (Φ : PtG m r K → ℂ) :
    c • tensG φ Φ = tensG (c • φ) Φ := by
  ext X; simp [tensG, mul_assoc]

lemma tensG_add_right (φ : PtG m 1 K → ℂ) (Φ Φ' : PtG m r K → ℂ) :
    tensG φ Φ + tensG φ Φ' = tensG φ (Φ + Φ') := by
  ext X; simp [tensG, mul_add]

lemma tensG_smul_right (c : ℂ) (φ : PtG m 1 K → ℂ) (Φ : PtG m r K → ℂ) :
    c • tensG φ Φ = tensG φ (c • Φ) := by
  ext X; simp [tensG]; ring

lemma tensG_zero_left (Φ : PtG m r K → ℂ) : tensG (0 : PtG m 1 K → ℂ) Φ = 0 := by
  ext X; simp [tensG]

lemma tensG_zero_right (φ : PtG m 1 K → ℂ) : tensG φ (0 : PtG m r K → ℂ) = 0 := by
  ext X; simp [tensG]

/-- Pure tensors: $\mathrm{ptG}(f)\otimes\mathrm{ptG}(f') = \mathrm{ptG}(f \sqcup f')$, with $f$ in the column $0$. -/
lemma tensG_ptG (f : Fin (2 * m) → Fin 1 → K → ℂ) (f' : Fin (2 * m) → Fin r → K → ℂ) :
    tensG (ptG f) (ptG f') = ptG (fun i j => Fin.cases (f i 0) (f' i) j) := by
  ext X
  simp [tensG, ptG, headG, tailG, Fin.prod_univ_succ, Finset.prod_mul_distrib]

/-- **$S(V^1)\otimes S(V^r) \subseteq S(V^{r+1})$.** -/
lemma tensG_mem {φ : PtG m 1 K → ℂ} {Φ : PtG m r K → ℂ} (hφ : φ ∈ Sg D m 1) (hΦ : Φ ∈ Sg D m r) :
    tensG φ Φ ∈ Sg D m (r + 1) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    induction hΦ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f', hf', rfl⟩ := hy
      rw [tensG_ptG]
      refine ptG_mem_Sg fun i j => ?_
      induction j using Fin.cases with
      | zero => simpa using hf i 0
      | succ j => simpa using hf' i j
    | zero => rw [tensG_zero_right]; exact zero_mem _
    | add y z _ _ hy hz => rw [← tensG_add_right]; exact add_mem hy hz
    | smul c y _ hy => rw [← tensG_smul_right]; exact Submodule.smul_mem _ _ hy
  | zero => rw [tensG_zero_left]; exact zero_mem _
  | add x y _ _ hx hy => rw [← tensG_add_left]; exact add_mem hx hy
  | smul c x _ hx => rw [← tensG_smul_left]; exact Submodule.smul_mem _ _ hx

/-- **$\det(\mathrm{extC}\,c\,X) = c\det X$.** -/
lemma det_extC (c : K) (X : Matrix (Fin r) (Fin r) K) : (extC c X).det = c * X.det := by
  have h : (extC c X).submatrix Fin.succ (Fin.succ : Fin r → Fin (r + 1)) = X := by
    ext i j; rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove_zero, h]

lemma QX_apply {g : ℕ} (X : PtG m g K) (j k : Fin g) : QX a X j k = ∑ l, (a l : K) * X l j * X l k := by
  rw [QX, mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_diagonal, transpose_apply]; ring

/-- **The trace splits:** $\operatorname{tr}(\mathrm{extC}\,b\,B\cdot Q[X]) = b\,Q[\mathrm{head}\,X]_{00} + \operatorname{tr}(B\,Q[\mathrm{tail}\,X])$. -/
lemma QX_extC_trace (b : K) (B : Matrix (Fin r) (Fin r) K) (X : PtG m (r + 1) K) :
    trace (extC b B * QX a X) = b * (QX a (headG X)) 0 0 + trace (B * QX a (tailG X)) := by
  simp only [trace, diag_apply, mul_apply, Fin.sum_univ_succ, extC_zero_zero, extC_zero_succ,
    extC_succ_zero, extC_succ_succ, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  simp only [QX_apply, headG, tailG]

/-- **$\omega(n(\mathrm{extC}\,b\,B))$ on tensor products:** acts by $\omega(n(b))$ on the first factor and $\omega(n(B))$ on the second. -/
lemma opNg_extC (b : K) (B : Matrix (Fin r) (Fin r) K) (φ : PtG m 1 K → ℂ) (Φ : PtG m r K → ℂ) :
    opNg D a (extC b B) (tensG φ Φ) =
      tensG (opNg D a (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => b) φ) (opNg D a B Φ) := by
  ext X
  have h1 : ∀ M : Matrix (Fin 1) (Fin 1) K, trace (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => b) * M) = b * M 0 0 := by
    intro M; simp [trace, mul_apply]
  simp only [opNg, tensG, h1, QX_extC_trace, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

lemma coe_extGL (A : GL (Fin r) K) : ((extGL A : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) =
    extC 1 (A : Matrix (Fin r) (Fin r) K) := rfl

/-- **$\omega(m(\mathrm{extC}\,1\,A))$ on tensor products:** acts only on the second factor, by $\omega(m(A))$. -/
lemma opMg_extGL (A : GL (Fin r) K) (φ : PtG m 1 K → ℂ) (Φ : PtG m r K → ℂ) :
    opMg D a (extGL A) (tensG φ Φ) = tensG φ (opMg D a A Φ) := by
  ext X
  have hdet : ((extGL A : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K).det =
      (A : Matrix (Fin r) (Fin r) K).det := by
    rw [coe_extGL, det_extC, one_mul]
  have hhead : headG (X * ((extGL A : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K)) = headG X := by
    ext i j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [headG, mul_apply, Fin.sum_univ_succ, coe_extGL]
  have htail : tailG (X * ((extGL A : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K)) =
      tailG X * (A : Matrix (Fin r) (Fin r) K) := by
    ext i j
    simp [tailG, mul_apply, Fin.sum_univ_succ, coe_extGL]
  simp only [opMg, tensG, hdet, hhead, htail]
  ring

/-- **The splitting $V^{r+1} \cong V^1 \times V^r$** $X \mapsto (\mathrm{head}\,X, \mathrm{tail}\,X)$ as a measurable equivalence. -/
def splitEquiv : PtG m (r + 1) K ≃ᵐ PtG m 1 K × PtG m r K :=
  (MeasurableEquiv.piCongrRight fun _ : Fin (2 * m) =>
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => K) 0).trans
    ((MeasurableEquiv.arrowProdEquivProdArrow K (Fin r → K) (Fin (2 * m))).trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piCongrRight fun _ : Fin (2 * m) => (MeasurableEquiv.funUnique (Fin 1) K).symm)
        (MeasurableEquiv.refl _)))

lemma splitEquiv_apply (X : PtG m (r + 1) K) : splitEquiv X = (headG X, tailG X) := rfl

/-- $\mu^{\otimes(2m\times g)}$ is $\sigma$-finite when $\mu$ is. -/
lemma sigmaFinite_muG (hD : D.IsOps) (g : ℕ) : SigmaFinite (muG D m g) := by
  have hσ := hD.sigmaFinite
  unfold muG
  have : ∀ _ : Fin (2 * m), SigmaFinite (Measure.pi fun _ : Fin g => D.μ) := fun _ => inferInstance
  exact Measure.pi.sigmaFinite _

/-- **`splitEquiv` is measure preserving** from $\mu^{\otimes(2m\times(r+1))}$ to the product of the two measures. -/
lemma splitEquiv_mp (hD : D.IsOps) :
    MeasurePreserving (splitEquiv (K := K) (m := m) (r := r)) (muG D m (r + 1))
      ((muG D m 1).prod (muG D m r)) := by
  have hσ := hD.sigmaFinite
  have hσg1 := sigmaFinite_muG (m := m) hD 1
  have hσgr := sigmaFinite_muG (m := m) hD r
  have hσr : ∀ _ : Fin (2 * m), SigmaFinite (Measure.pi fun _ : Fin r => D.μ) := fun _ => inferInstance
  have hσ1 : ∀ _ : Fin (2 * m), SigmaFinite (Measure.pi fun _ : Fin 1 => D.μ) := fun _ => inferInstance
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : Fin (2 * m) =>
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => K) 0)
      (muG D m (r + 1)) (Measure.pi fun _ : Fin (2 * m) => D.μ.prod (Measure.pi fun _ : Fin r => D.μ)) :=
    measurePreserving_pi _ _ (fun _ => measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => D.μ) 0)
  have h2 := measurePreserving_arrowProdEquivProdArrow K (Fin r → K) (Fin (2 * m))
    (fun _ => D.μ) (fun _ => Measure.pi fun _ : Fin r => D.μ)
  have h3 : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : Fin (2 * m) => (MeasurableEquiv.funUnique (Fin 1) K).symm)
      (Measure.pi fun _ : Fin (2 * m) => D.μ) (muG D m 1) :=
    measurePreserving_pi (hν := hσ1) _ _
      (fun _ => (measurePreserving_funUnique D.μ (Fin 1)).symm (MeasurableEquiv.funUnique (Fin 1) K))
  have h4 := h3.prod (MeasurePreserving.id (muG D m r))
  exact h4.comp (h2.comp h1)

/-- **$\omega(w)$ on tensor products** (Fubini): $\omega(w)(\varphi\otimes\Phi) = \omega(w)\varphi\otimes\omega(w)\Phi$. -/
lemma opWg_tensG (hD : D.IsOps) (φ : PtG m 1 K → ℂ) (Φ : PtG m r K → ℂ) :
    opWg D a (tensG φ Φ) = tensG (opWg D a φ) (opWg D a Φ) := by
  have hσ1 := sigmaFinite_muG (m := m) hD 1
  have hσr := sigmaFinite_muG (m := m) hD r
  ext Y
  have hB : ∀ X : PtG m (r + 1) K,
      BX a X Y = BX a (headG X) (headG Y) + BX a (tailG X) (tailG Y) := by
    intro X
    simp [BX, headG, tailG, Fin.sum_univ_succ, Finset.sum_add_distrib]
  have hint : ∫ X, tensG φ Φ X * (D.ψ (BX a X Y) : ℂ) ∂muG D m (r + 1) =
      (∫ X, φ X * (D.ψ (BX a X (headG Y)) : ℂ) ∂muG D m 1) *
        ∫ X, Φ X * (D.ψ (BX a X (tailG Y)) : ℂ) ∂muG D m r := by
    have h := (splitEquiv_mp hD).integral_comp'
      (fun p : PtG m 1 K × PtG m r K =>
        (φ p.1 * (D.ψ (BX a p.1 (headG Y)) : ℂ)) * (Φ p.2 * (D.ψ (BX a p.2 (tailG Y)) : ℂ)))
    rw [integral_prod_mul (fun x : PtG m 1 K => φ x * (D.ψ (BX a x (headG Y)) : ℂ))
      (fun x : PtG m r K => Φ x * (D.ψ (BX a x (tailG Y)) : ℂ))] at h
    rw [← h]
    congr 1
    funext X
    simp only [splitEquiv_apply, tensG, hB, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp only [opWg]
  rw [hint]
  simp only [tensG, opWg]
  ring

end QuadFormsKB.SiegelWeil.Forms
