import QuadFormsKB.HilbertModular.ThetaCusp

/-!
# Theta series over a totally real field V: the $\Gamma_0(\mathfrak N)$ law with a Gauss-sum multiplier

Let $Q$ be a form over $\mathcal{O}_F$ in $n$ variables, $H$ its Hessian (`QuadForm.hessian`, $Q(x) = \frac12x^{\mathsf T}Hx$),
$A = \frac12H$ the Gram matrix (`gramF`), totally positive definite (`IsTotPosGram`), and
$Q^\#(y) = \frac14y^{\mathsf T}A^{-1}y = \frac12y^{\mathsf T}H^{-1}y$ the dual form on $(\mathfrak d^{-1})^n$.

* **Level** (`IsThetaLevelF Q 𝔑`): $\nu\,Q^\#(y) \in \mathfrak d^{-1}$ for all $\nu \in \mathfrak N$ and $y \in (\mathfrak d^{-1})^n$, i.e.
  $\mathfrak N\,Q^\#(L^\#) \subseteq \mathfrak d^{-1}$ for $L = \mathcal{O}_F^n$. For $F = \mathbb{Q}$ this is `QuadFormsKB.IsThetaLevel`
  ($N\,Q^*$ integral). Over $F$ it is the condition that makes the dual lattice, with the form $\mathfrak N Q^\#$, integral for
  the trace form; e.g. for $Q = x_0^2 + \dots + x_3^2$ the level is $4\mathfrak d$.
* **Gauss sums** (`gaussSumF Q a c μ`): for $a, c \in \mathcal{O}_F$ and $\mu \in (\mathfrak d^{-1})^n$,
  $$G(a, \mu, c) = \sum_{r\in(\mathcal{O}_F/c)^n}e\Big(\operatorname{Tr}\frac{aQ(r) + \mu\cdot r}{c}\Big).$$
* `exists_eq_hessF_of_gaussSumF_ne_zero`: for $c \in \mathfrak N$, $G(a, \mu, c) \ne 0 \Rightarrow \mu \in H\mathcal{O}_F^n$;
  `gaussSumF_hessF`: $G(a, Hu, c) = e(-\operatorname{Tr}\frac{dQ(u)}{c})\,G(a, 0, c)$ if $ad - bc = 1$ (completing the square).
* **`thetaQ_slash_gamma0`**: for $n = 2k$, $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$, $c \ne 0$:
  $\theta_Q\,|_k\,\gamma = M_Q(a, c)\,\theta_Q$ with
  $$M_Q(a, c) = \frac{1}{\sqrt{N(\det A)}\,d_F^{k}}\prod_v\Big(\frac{-i}{2\varphi_v(c)}\Big)^k\,G(a, 0, c)\qquad(\texttt{thetaMultF}).$$
  `thetaQ_slash_gamma0_c0`: for $c = 0$, $\theta_Q\,|_k\,\gamma = N(d)^{-k}\theta_Q$ ($d$ a unit, $N(d) = \pm1$).

*Proof* (as over $\mathbb{Q}$, `QuadFormsKB.Siegel.thetaGram_gamma0`): $\gamma z = \frac ac - \frac{1}{c^2u}$ with $u = z + \frac dc$; expand at the
cusp (`tsum_latSet_cusp`, representatives `qlift` of $\mathcal{O}_F/c$); only $\mu = Hu'$ survive, and for those the Gauss sum
completes the square. Sources: Iwaniec, *Topics in Classical Automorphic Forms*, §10.4 [unverified] (over $\mathbb{Q}$);
Shimura, *On modular forms of half integral weight*, Ann. of Math. 97 (1973), §2 [unverified] (theta over $F$).
-/

open Matrix NumberField NumberField.InfinitePlace Complex UpperHalfPlane
open scoped Real nonZeroDivisors MatrixGroups ModularForm

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-! ### Integrality helpers -/

lemma algebraMap_mem_one (r : 𝓞 F) : algebraMap (𝓞 F) F r ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) :=
  (FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩

lemma mem_invDifferent_of_mem_one {x : F} (h : x ∈ (1 : FractionalIdeal (𝓞 F)⁰ F)) :
    x ∈ invDifferent F :=
  FractionalIdeal.one_le_dual_one ℤ ℚ (L := F) (B := 𝓞 F) h

lemma algebraMap_mem_invDifferent (r : 𝓞 F) : algebraMap (𝓞 F) F r ∈ invDifferent F :=
  mem_invDifferent_of_mem_one (algebraMap_mem_one r)

lemma algebraMap_mul_mem_invDifferent (r : 𝓞 F) {y : F} (hy : y ∈ invDifferent F) :
    algebraMap (𝓞 F) F r * y ∈ invDifferent F := by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem _ r hy

lemma trace_int_of_mem_invDifferent {y : F} (hy : y ∈ invDifferent F) :
    ∃ m : ℤ, Algebra.trace ℚ F y = m := by
  obtain ⟨m, hm⟩ := trace_mem_int_of_mem_invDifferent hy 1
  exact ⟨m, by simpa using hm⟩

/-- $e(\operatorname{Tr}y) = 1$ for $y \in \mathfrak d^{-1}$. -/
lemma cexp_trace_eq_one {y : F} (hy : y ∈ invDifferent F) :
    cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F y : ℚ) : ℂ)) = 1 := by
  obtain ⟨m, hm⟩ := trace_int_of_mem_invDifferent hy
  rw [hm, show 2 * (Real.pi : ℂ) * Complex.I * ((m : ℚ) : ℂ) = m * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

/-- $e(\operatorname{Tr}(x + y)) = e(\operatorname{Tr}x)$ for $y \in \mathfrak d^{-1}$. -/
lemma cexp_trace_add_of_mem {x y : F} (hy : y ∈ invDifferent F) :
    cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (x + y) : ℚ) : ℂ)) =
      cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  rw [map_add, Rat.cast_add, mul_add, Complex.exp_add, cexp_trace_eq_one hy, mul_one]

/-- If $t\,\mathfrak d^{-1} \subseteq \mathfrak d^{-1}$ then $t \in \mathcal{O}_F$ ($\mathcal{O}_F = $ the trace dual of $\mathfrak d^{-1}$). -/
lemma mem_one_of_mul_mem_invDifferent {t : F} (h : ∀ δ ∈ invDifferent F, t * δ ∈ invDifferent F) :
    t ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  have hdd : FractionalIdeal.dual ℤ ℚ (invDifferent F) = (1 : FractionalIdeal (𝓞 F)⁰ F) :=
    FractionalIdeal.dual_dual ℤ ℚ (L := F) (B := 𝓞 F) 1
  rw [← hdd, FractionalIdeal.mem_dual invDifferent_ne_zero]
  intro δ hδ
  obtain ⟨m, hm⟩ := trace_int_of_mem_invDifferent (h δ hδ)
  exact ⟨m, by simp [Algebra.traceForm_apply, hm]⟩

/-! ### Vectors over $\mathcal{O}_F$ and the Hessian over $F$ -/

/-- An integral vector as a vector over $F$. -/
abbrev vecO (x : Fin n → 𝓞 F) : Fin n → F := fun i => algebraMap (𝓞 F) F (x i)

/-- The Hessian over $F$: $H = 2A$. -/
def hessF (Q : QuadForm (𝓞 F) n) : Matrix (Fin n) (Fin n) F := Q.hessian.map (algebraMap (𝓞 F) F)

lemma gramF_eq (Q : QuadForm (𝓞 F) n) : gramF Q = (1 / 2 : F) • hessF Q := rfl

lemma hessF_transpose (Q : QuadForm (𝓞 F) n) : (hessF Q)ᵀ = hessF Q := by
  rw [hessF, ← transpose_map, QuadForm.hessian, transpose_add, transpose_transpose, add_comm]

lemma vecO_add (x y : Fin n → 𝓞 F) : vecO (x + y) = vecO x + vecO y := by
  funext i; simp only [vecO, Pi.add_apply, map_add]

lemma vecO_smul (c : 𝓞 F) (x : Fin n → 𝓞 F) : vecO (c • x) = algebraMap (𝓞 F) F c • vecO x := by
  funext i; simp only [vecO, Pi.smul_apply, smul_eq_mul, map_mul]

lemma dotProduct_vecO (x y : Fin n → 𝓞 F) :
    vecO x ⬝ᵥ vecO y = algebraMap (𝓞 F) F (x ⬝ᵥ y) := by
  simp [dotProduct, map_sum]

lemma hessF_mulVec_vecO (Q : QuadForm (𝓞 F) n) (u : Fin n → 𝓞 F) :
    hessF Q *ᵥ vecO u = vecO (Q.hessian *ᵥ u) := by
  funext i; simp [hessF, vecO, mulVec, dotProduct, map_sum]

lemma qv_vecO (Q : QuadForm (𝓞 F) n) (x : Fin n → 𝓞 F) :
    qv (gramF Q) (vecO x) = algebraMap (𝓞 F) F (Q.eval x) :=
  (algebraMap_eval_eq_qv Q x).symm

/-- $Q(x + y) = Q(x) + x^{\mathsf T}Hy + Q(y)$. -/
lemma qv_gramF_add (Q : QuadForm (𝓞 F) n) (x y : Fin n → F) :
    qv (gramF Q) (x + y) = qv (gramF Q) x + x ⬝ᵥ hessF Q *ᵥ y + qv (gramF Q) y := by
  have hyx : y ⬝ᵥ hessF Q *ᵥ x = x ⬝ᵥ hessF Q *ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hessF_transpose, dotProduct_comm]
  simp only [qv, gramF_eq, smul_mulVec, dotProduct_smul, mulVec_add, dotProduct_add,
    add_dotProduct, smul_eq_mul, hyx]
  ring

lemma gramF_det_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) : (gramF Q).det ≠ 0 := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
  intro h
  have := (hQ v).det_pos
  rw [show ((gramF Q).map (realEmb F v)).det = realEmb F v (gramF Q).det from
    (RingHom.map_det _ _).symm, h, map_zero] at this
  exact lt_irrefl _ this

lemma hessF_det_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) : (hessF Q).det ≠ 0 := by
  have h := gramF_det_ne_zero hQ
  rw [gramF_eq, det_smul] at h
  exact right_ne_zero_of_mul h

/-! ### The dual form -/

/-- The dual form $Q^\#(y) = \frac14y^{\mathsf T}A^{-1}y$. -/
abbrev qDual (Q : QuadForm (𝓞 F) n) (y : Fin n → F) : F := qv ((1 / 4 : F) • (gramF Q)⁻¹) y

lemma gramF_inv {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) :
    (gramF Q)⁻¹ = (2 : F) • (hessF Q)⁻¹ := by
  have hu : IsUnit (hessF Q).det := isUnit_iff_ne_zero.mpr (hessF_det_ne_zero hQ)
  rw [gramF_eq]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, nonsing_inv_mul _ hu, smul_smul]
  norm_num

lemma hessF_inv_transpose (Q : QuadForm (𝓞 F) n) : ((hessF Q)⁻¹)ᵀ = (hessF Q)⁻¹ := by
  rw [transpose_nonsing_inv, hessF_transpose]

lemma qDual_eq {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (y : Fin n → F) :
    qDual Q y = (1 / 2 : F) * (y ⬝ᵥ (hessF Q)⁻¹ *ᵥ y) := by
  simp only [qDual, qv, gramF_inv hQ, smul_smul, smul_mulVec, dotProduct_smul, smul_eq_mul]
  norm_num

/-- Polarization of $Q^\#$: $Q^\#(y + y') - Q^\#(y) - Q^\#(y') = y'^{\mathsf T}H^{-1}y$. -/
lemma qDual_add {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (y y' : Fin n → F) :
    qDual Q (y + y') - qDual Q y - qDual Q y' = y' ⬝ᵥ (hessF Q)⁻¹ *ᵥ y := by
  have hs : y ⬝ᵥ (hessF Q)⁻¹ *ᵥ y' = y' ⬝ᵥ (hessF Q)⁻¹ *ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hessF_inv_transpose, dotProduct_comm]
  simp only [qDual_eq hQ, mulVec_add, dotProduct_add, add_dotProduct, hs]
  ring

/-- $Q(H^{-1}y) = Q^\#(y)$. -/
lemma qv_hessF_inv (Q : QuadForm (𝓞 F) n) (hQ : IsTotPosGram (gramF Q)) (y : Fin n → F) :
    qv (gramF Q) ((hessF Q)⁻¹ *ᵥ y) = qDual Q y := by
  have hu : IsUnit (hessF Q).det := isUnit_iff_ne_zero.mpr (hessF_det_ne_zero hQ)
  rw [qDual_eq hQ, qv, gramF_eq, smul_mulVec, dotProduct_smul, mulVec_mulVec,
    mul_nonsing_inv _ hu, one_mulVec, dotProduct_mulVec, ← mulVec_transpose,
    hessF_inv_transpose, dotProduct_comm, smul_eq_mul]

/-! ### The level -/

/-- **The level of a form over $\mathcal{O}_F$** (theta-series level): an ideal $\mathfrak N$ with $\nu\,Q^\#(y) \in \mathfrak d^{-1}$ for all
$\nu \in \mathfrak N$ and $y \in (\mathfrak d^{-1})^n$, $Q^\#(y) = \frac14y^{\mathsf T}A^{-1}y$, $\mathfrak d^{-1}$ = `invDifferent F`. For $F = \mathbb{Q}$
this is `QuadFormsKB.IsThetaLevel` ($N\,Q^*$ integral on $\mathbb{Z}^n$).

Parameters: `Q` (a form over $\mathcal{O}_F$), `𝔑` (an ideal of $\mathcal{O}_F$). -/
@[kb "shimura1973" "§2, level of a theta series [unverified]"]
def IsThetaLevelF (Q : QuadForm (𝓞 F) n) (𝔑 : Ideal (𝓞 F)) : Prop :=
  ∀ ν ∈ 𝔑, ∀ y : Fin n → F, (∀ i, y i ∈ invDifferent F) →
    algebraMap (𝓞 F) F ν * qDual Q y ∈ invDifferent F

/-- At a level: $c H^{-1}y \in \mathcal{O}_F^n$ for $c \in \mathfrak N$, $y \in (\mathfrak d^{-1})^n$. -/
lemma exists_vecO_of_level {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {𝔑 : Ideal (𝓞 F)}
    (hlev : IsThetaLevelF Q 𝔑)
    {c : 𝓞 F} (hc : c ∈ 𝔑) {y : Fin n → F} (hy : ∀ i, y i ∈ invDifferent F) :
    ∃ s : Fin n → 𝓞 F, vecO s = algebraMap (𝓞 F) F c • ((hessF Q)⁻¹ *ᵥ y) := by
  have h : ∀ i, (algebraMap (𝓞 F) F c • ((hessF Q)⁻¹ *ᵥ y)) i ∈
      (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    intro i
    refine mem_one_of_mul_mem_invDifferent fun δ hδ => ?_
    classical
    set y' : Fin n → F := Pi.single i δ
    have hy' : ∀ j, y' j ∈ invDifferent F := fun j => by
      by_cases hj : j = i
      · subst hj; simpa [y'] using hδ
      · simp only [y', Pi.single_apply, hj, ite_false]; exact Submodule.zero_mem _
    have hyy : ∀ j, (y + y') j ∈ invDifferent F := fun j => Submodule.add_mem _ (hy j) (hy' j)
    have h1 := hlev c hc _ hyy
    have h2 := hlev c hc _ hy
    have h3 := hlev c hc _ hy'
    have hsub := Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) h3
    rw [← mul_sub, ← mul_sub, qDual_add hQ] at hsub
    have : y' ⬝ᵥ (hessF Q)⁻¹ *ᵥ y = δ * ((hessF Q)⁻¹ *ᵥ y) i := by
      simp [y', dotProduct, Pi.single_apply]
    rw [this] at hsub
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show algebraMap (𝓞 F) F c * ((hessF Q)⁻¹ *ᵥ y) i * δ =
      algebraMap (𝓞 F) F c * (δ * ((hessF Q)⁻¹ *ᵥ y) i) by ring]
    exact hsub
  choose s hs using fun i => (FractionalIdeal.mem_one_iff _).mp (h i)
  exact ⟨s, funext hs⟩

/-! ### Quadratic Gauss sums over $\mathcal{O}_F/c$ -/

/-- A lift $\mathcal{O}_F/c \to \mathcal{O}_F$ (any section of the quotient map). -/
def qlift {c : 𝓞 F} (r : 𝓞 F ⧸ Ideal.span {c}) : 𝓞 F := (Ideal.Quotient.mk_surjective r).choose

@[simp] lemma mk_qlift {c : 𝓞 F} (r : 𝓞 F ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (qlift r) = r :=
  (Ideal.Quotient.mk_surjective r).choose_spec

lemma finite_quot_span {c : 𝓞 F} (hc : c ≠ 0) : Finite (𝓞 F ⧸ Ideal.span {c}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hc)

/-- Two elements with the same class modulo $c$ differ by a multiple of $c$. -/
lemma exists_eq_add_mul_of_mk_eq {c x y : 𝓞 F}
    (h : Ideal.Quotient.mk (Ideal.span {c}) x = Ideal.Quotient.mk (Ideal.span {c}) y) :
    ∃ t, x = y + c * t := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by linear_combination -ht⟩

/-- The summand $e\big(\operatorname{Tr}\frac{aQ(x) + \mu\cdot x}{c}\big)$ of the Gauss sum, $x \in \mathcal{O}_F^n$. -/
def gsTermF (Q : QuadForm (𝓞 F) n) (a c : 𝓞 F) (μ : Fin n → F) (x : Fin n → 𝓞 F) : ℂ :=
  cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
    ((algebraMap (𝓞 F) F a * qv (gramF Q) (vecO x) + μ ⬝ᵥ vecO x) / algebraMap (𝓞 F) F c) : ℚ) : ℂ))

/-- **The $n$-ary quadratic Gauss sum over $\mathcal{O}_F/c$ with a linear term**:
$$G(a, \mu, c) = \sum_{r\in(\mathcal{O}_F/c)^n}e\Big(\operatorname{Tr}_{F/\mathbb{Q}}\frac{aQ(r) + \mu\cdot r}{c}\Big),$$
$a, c \in \mathcal{O}_F$, $\mu \in F^n$ (in use $\mu \in (\mathfrak d^{-1})^n$, which makes the summand well defined modulo $c$,
`gsTermF_add_mul`); a finite sum (`finsum`) for $c \ne 0$. For $F = \mathbb{Q}$ it is `QuadFormsKB.Siegel.gaussSum`. -/
@[kb "iwaniec1997" "§10.4, Gauss sums [unverified]"]
def gaussSumF (Q : QuadForm (𝓞 F) n) (a c : 𝓞 F) (μ : Fin n → F) : ℂ :=
  ∑ᶠ r : Fin n → 𝓞 F ⧸ Ideal.span {c}, gsTermF Q a c μ fun i => qlift (r i)

lemma gaussSumF_eq_sum (Q : QuadForm (𝓞 F) n) (a : 𝓞 F) {c : 𝓞 F} (μ : Fin n → F)
    [Fintype (𝓞 F ⧸ Ideal.span {c})] :
    gaussSumF Q a c μ = ∑ r : Fin n → 𝓞 F ⧸ Ideal.span {c}, gsTermF Q a c μ fun i => qlift (r i) :=
  finsum_eq_sum_of_fintype _

/-- Periodicity: for $\mu \in (\mathfrak d^{-1})^n$, the summand depends only on $x \bmod c$. -/
lemma gsTermF_add_mul (Q : QuadForm (𝓞 F) n) (a : 𝓞 F) {c : 𝓞 F} (hc : c ≠ 0) {μ : Fin n → F}
    (hμ : ∀ i, μ i ∈ invDifferent F) (x z : Fin n → 𝓞 F) :
    gsTermF Q a c μ (x + c • z) = gsTermF Q a c μ x := by
  have hc' : algebraMap (𝓞 F) F c ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective (𝓞 F) F).ne hc
  have key : (algebraMap (𝓞 F) F a * qv (gramF Q) (vecO (x + c • z)) + μ ⬝ᵥ vecO (x + c • z)) /
      algebraMap (𝓞 F) F c = (algebraMap (𝓞 F) F a * qv (gramF Q) (vecO x) + μ ⬝ᵥ vecO x) /
        algebraMap (𝓞 F) F c +
      (algebraMap (𝓞 F) F (a * (x ⬝ᵥ Q.hessian *ᵥ z + c * Q.eval z)) + μ ⬝ᵥ vecO z) := by
    rw [vecO_add, vecO_smul, qv_gramF_add, qv_smul_vec, dotProduct_add, dotProduct_smul,
      mulVec_smul, dotProduct_smul, hessF_mulVec_vecO, dotProduct_vecO, qv_vecO, smul_eq_mul,
      smul_eq_mul]
    simp only [map_mul, map_add, qv_vecO]
    field_simp
    ring
  rw [gsTermF, gsTermF, key]
  refine cexp_trace_add_of_mem (Submodule.add_mem _ (algebraMap_mem_invDifferent _) ?_)
  exact Submodule.sum_mem _ fun i _ => by
    rw [mul_comm]; exact algebraMap_mul_mem_invDifferent _ (hμ i)

lemma gsTermF_congr (Q : QuadForm (𝓞 F) n) (a : 𝓞 F) {c : 𝓞 F} (hc : c ≠ 0) {μ : Fin n → F}
    (hμ : ∀ i, μ i ∈ invDifferent F) {x y : Fin n → 𝓞 F}
    (h : ∀ i, Ideal.Quotient.mk (Ideal.span {c}) (x i) = Ideal.Quotient.mk (Ideal.span {c}) (y i)) :
    gsTermF Q a c μ x = gsTermF Q a c μ y := by
  choose t ht using fun i => exists_eq_add_mul_of_mk_eq (h i)
  have : x = y + c • t := funext fun i => by simp [ht i]
  rw [this, gsTermF_add_mul Q a hc hμ]

/-- Shifting the summation variable by $s \in \mathcal{O}_F^n$ does not change the Gauss sum. -/
lemma gaussSumF_shift (Q : QuadForm (𝓞 F) n) (a : 𝓞 F) {c : 𝓞 F} (hc : c ≠ 0) {μ : Fin n → F}
    (hμ : ∀ i, μ i ∈ invDifferent F) (s : Fin n → 𝓞 F) :
    ∑ᶠ r : Fin n → 𝓞 F ⧸ Ideal.span {c}, gsTermF Q a c μ ((fun i => qlift (r i)) + s) =
      gaussSumF Q a c μ := by
  have := finite_quot_span hc
  haveI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {c})
  rw [gaussSumF_eq_sum, finsum_eq_sum_of_fintype]
  set sbar : Fin n → 𝓞 F ⧸ Ideal.span {c} := fun i => Ideal.Quotient.mk _ (s i)
  refine Fintype.sum_equiv (Equiv.addRight sbar) _ _ fun r => ?_
  refine gsTermF_congr Q a hc hμ fun i => ?_
  simp [sbar]

/-! ### Vanishing under a level, and completing the square -/

/-- **Only $\mu \in H\mathcal{O}_F^n$ contribute.** If $\mathfrak N$ is a level of $Q$, $c \in \mathfrak N$, $c \ne 0$,
$\mu \in (\mathfrak d^{-1})^n$ and $G(a, \mu, c) \ne 0$, then $\mu = Hu$ for some $u \in \mathcal{O}_F^n$. -/
theorem exists_eq_hessF_of_gaussSumF_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (a : 𝓞 F) {c : 𝓞 F} (hc0 : c ≠ 0) (hc : c ∈ 𝔑)
    {μ : Fin n → F} (hμ : ∀ i, μ i ∈ invDifferent F) (hG : gaussSumF Q a c μ ≠ 0) :
    ∃ u : Fin n → 𝓞 F, μ = hessF Q *ᵥ vecO u := by
  have hc' : algebraMap (𝓞 F) F c ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective (𝓞 F) F).ne hc0
  have hu : IsUnit (hessF Q).det := isUnit_iff_ne_zero.mpr (hessF_det_ne_zero hQ)
  -- for every `y ∈ (𝔡⁻¹)ⁿ`, `Tr(μ ⬝ H⁻¹ y) ∈ ℤ`
  have hint : ∀ y : Fin n → F, (∀ i, y i ∈ invDifferent F) →
      cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (μ ⬝ᵥ (hessF Q)⁻¹ *ᵥ y) : ℚ) : ℂ)) = 1 := by
    intro y hy
    obtain ⟨s, hs⟩ := exists_vecO_of_level hQ hlev hc hy
    have hterm : ∀ x : Fin n → 𝓞 F, gsTermF Q a c μ (x + s) = gsTermF Q a c μ x *
        cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (μ ⬝ᵥ (hessF Q)⁻¹ *ᵥ y) : ℚ) : ℂ)) := by
      intro x
      have hHs : hessF Q *ᵥ vecO s = algebraMap (𝓞 F) F c • y := by
        rw [hs, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
      have hqs : qv (gramF Q) (vecO s) = algebraMap (𝓞 F) F c ^ 2 * qDual Q y := by
        rw [hs, qv_smul_vec, qv_hessF_inv Q hQ]
      have key : (algebraMap (𝓞 F) F a * qv (gramF Q) (vecO (x + s)) + μ ⬝ᵥ vecO (x + s)) /
          algebraMap (𝓞 F) F c =
          ((algebraMap (𝓞 F) F a * qv (gramF Q) (vecO x) + μ ⬝ᵥ vecO x) / algebraMap (𝓞 F) F c +
            μ ⬝ᵥ (hessF Q)⁻¹ *ᵥ y) +
          (algebraMap (𝓞 F) F a * (vecO x ⬝ᵥ y) +
            algebraMap (𝓞 F) F a * (algebraMap (𝓞 F) F c * qDual Q y)) := by
        rw [vecO_add, qv_gramF_add, hHs, hqs, dotProduct_add, hs, dotProduct_smul, dotProduct_smul,
          smul_eq_mul, smul_eq_mul]
        field_simp
        ring
      rw [gsTermF, gsTermF, key, cexp_trace_add_of_mem, map_add, Rat.cast_add, mul_add,
        Complex.exp_add]
      refine Submodule.add_mem _ (algebraMap_mul_mem_invDifferent _ ?_)
        (algebraMap_mul_mem_invDifferent _ (hlev c hc y hy))
      exact Submodule.sum_mem _ fun i _ => algebraMap_mul_mem_invDifferent _ (hy i)
    have h := gaussSumF_shift Q a hc0 hμ s
    simp_rw [hterm] at h
    have := finite_quot_span hc0
    letI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {c})
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_mul, ← gaussSumF_eq_sum] at h
    exact (mul_eq_left₀ hG).mp h
  -- hence `H⁻¹ μ` is integral
  have hw : ∀ i, ((hessF Q)⁻¹ *ᵥ μ) i ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    intro i
    have hdd : FractionalIdeal.dual ℤ ℚ (invDifferent F) = (1 : FractionalIdeal (𝓞 F)⁰ F) :=
      FractionalIdeal.dual_dual ℤ ℚ (L := F) (B := 𝓞 F) 1
    rw [← hdd, FractionalIdeal.mem_dual invDifferent_ne_zero]
    intro δ hδ
    classical
    have hy : ∀ j, (Pi.single i δ : Fin n → F) j ∈ invDifferent F := fun j => by
      by_cases hj : j = i
      · subst hj; simpa using hδ
      · simp only [Pi.single_apply, hj, ite_false]; exact Submodule.zero_mem _
    have h1 := hint _ hy
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    refine ⟨m, ?_⟩
    have hdot : μ ⬝ᵥ (hessF Q)⁻¹ *ᵥ Pi.single i δ = ((hessF Q)⁻¹ *ᵥ μ) i * δ := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hessF_inv_transpose, dotProduct_comm]
      simp [dotProduct, Pi.single_apply, mul_comm]
    rw [hdot] at hm
    have h2 : ((Algebra.trace ℚ F (((hessF Q)⁻¹ *ᵥ μ) i * δ) : ℚ) : ℂ) = m := by
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ hpi
      rw [hm]; ring
    simp only [Algebra.traceForm_apply, eq_intCast]
    exact_mod_cast h2.symm
  choose u hu' using fun i => (FractionalIdeal.mem_one_iff _).mp (hw i)
  refine ⟨u, ?_⟩
  have : vecO u = (hessF Q)⁻¹ *ᵥ μ := funext hu'
  rw [this, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]

/-- **Completing the square.** For $ad - bc = 1$ and $u \in \mathcal{O}_F^n$:
$G(a, Hu, c) = e\big(-\operatorname{Tr}\frac{dQ(u)}{c}\big)\,G(a, 0, c)$. -/
theorem gaussSumF_hessF (Q : QuadForm (𝓞 F) n) {a b c d : 𝓞 F} (hc0 : c ≠ 0)
    (hdet : a * d - b * c = 1) (u : Fin n → 𝓞 F) :
    gaussSumF Q a c (hessF Q *ᵥ vecO u) =
      cexp (-(2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
        (algebraMap (𝓞 F) F d * qv (gramF Q) (vecO u) / algebraMap (𝓞 F) F c) : ℚ) : ℂ))) *
      gaussSumF Q a c 0 := by
  have hc' : algebraMap (𝓞 F) F c ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective (𝓞 F) F).ne hc0
  have hdet' : algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F d -
      algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F c = 1 := by
    have := congrArg (algebraMap (𝓞 F) F) hdet
    simpa using this
  have hzero : ∀ i, (0 : Fin n → F) i ∈ invDifferent F := fun _ => Submodule.zero_mem _
  have hterm : ∀ x : Fin n → 𝓞 F, gsTermF Q a c (hessF Q *ᵥ vecO u) x =
      cexp (-(2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
        (algebraMap (𝓞 F) F d * qv (gramF Q) (vecO u) / algebraMap (𝓞 F) F c) : ℚ) : ℂ))) *
      gsTermF Q a c 0 (x + d • u) := by
    intro x
    have hsym : (hessF Q *ᵥ vecO u) ⬝ᵥ vecO x = vecO x ⬝ᵥ hessF Q *ᵥ vecO u := by
      rw [dotProduct_comm]
    set B := vecO x ⬝ᵥ hessF Q *ᵥ vecO u with hB
    set q := qv (gramF Q) (vecO u) with hq
    have hBint : B = algebraMap (𝓞 F) F (x ⬝ᵥ Q.hessian *ᵥ u) := by
      rw [hB, hessF_mulVec_vecO, dotProduct_vecO]
    have hqint : q = algebraMap (𝓞 F) F (Q.eval u) := by rw [hq, qv_vecO]
    have key : (algebraMap (𝓞 F) F a * qv (gramF Q) (vecO x) + (hessF Q *ᵥ vecO u) ⬝ᵥ vecO x) /
        algebraMap (𝓞 F) F c =
        (-(algebraMap (𝓞 F) F d * q / algebraMap (𝓞 F) F c) +
          (algebraMap (𝓞 F) F a * qv (gramF Q) (vecO (x + d • u)) + (0 : Fin n → F) ⬝ᵥ
            vecO (x + d • u)) / algebraMap (𝓞 F) F c) +
        -(algebraMap (𝓞 F) F b * B + algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F d * q) := by
      rw [hsym, vecO_add, vecO_smul, qv_gramF_add, qv_smul_vec, mulVec_smul, dotProduct_smul,
        smul_eq_mul, zero_dotProduct, add_zero, ← hB, ← hq]
      have ha : algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F d =
          1 + algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F c := by linear_combination hdet'
      field_simp
      linear_combination (-(algebraMap (𝓞 F) F d * q) - B) * ha
    rw [gsTermF, gsTermF, key, cexp_trace_add_of_mem, map_add, Rat.cast_add, mul_add,
      Complex.exp_add, map_neg, Rat.cast_neg, mul_neg]
    refine Submodule.neg_mem _ (Submodule.add_mem _ ?_ ?_)
    · rw [hBint]; exact algebraMap_mul_mem_invDifferent _ (algebraMap_mem_invDifferent _)
    · rw [hqint, ← map_mul, ← map_mul]; exact algebraMap_mem_invDifferent _
  rw [gaussSumF]
  simp_rw [hterm]
  rw [← gaussSumF_shift Q a hc0 hzero (d • u)]
  have := finite_quot_span hc0
  haveI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {c})
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]

/-! ### The lattice $\mathcal{O}_F^n$ and its representatives modulo $c$ -/

/-- The trivial ideal vector $(1, \dots, 1)$. -/
abbrev oneIdeals : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ := fun _ => 1

lemma mem_latSet_one {x : Fin n → F} :
    x ∈ latSet (oneIdeals (F := F)) ↔ ∀ i, x i ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  simp [latSet]

lemma mem_dualSet_one {x : Fin n → F} :
    x ∈ dualSet (oneIdeals (F := F)) ↔ ∀ i, x i ∈ invDifferent F := by
  simp [dualSet, invDifferent]

/-- $\mathcal{O}_F^n \simeq L = \mathcal{O}_F^n \subset F^n$. -/
def latSetOneEquiv : (Fin n → 𝓞 F) ≃ latSet (oneIdeals (F := F) (n := n)) where
  toFun x := ⟨vecO x, mem_latSet_one.mpr fun i => algebraMap_mem_one _⟩
  invFun y := fun i => ((FractionalIdeal.mem_one_iff _).mp (mem_latSet_one.mp y.2 i)).choose
  left_inv x := by
    funext i
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    exact ((FractionalIdeal.mem_one_iff _).mp
      (mem_latSet_one.mp (⟨vecO x, mem_latSet_one.mpr fun i => algebraMap_mem_one _⟩ :
        latSet (oneIdeals (F := F) (n := n))).2 i)).choose_spec
  right_inv y := by
    apply Subtype.ext
    funext i
    exact ((FractionalIdeal.mem_one_iff _).mp (mem_latSet_one.mp y.2 i)).choose_spec

@[simp] lemma latSetOneEquiv_coe (x : Fin n → 𝓞 F) :
    ((latSetOneEquiv x : latSet (oneIdeals (F := F) (n := n))) : Fin n → F) = vecO x := rfl

/-- The quotient in division with remainder: $x = \tilde{\bar x} + c\,q(x)$ (`qdiv_spec`). -/
def qdiv (c : 𝓞 F) (x : 𝓞 F) : 𝓞 F :=
  (exists_eq_add_mul_of_mk_eq (mk_qlift (Ideal.Quotient.mk (Ideal.span {c}) x)).symm).choose

lemma qdiv_spec (c : 𝓞 F) (x : 𝓞 F) :
    x = qlift (Ideal.Quotient.mk (Ideal.span {c}) x) + c * qdiv c x :=
  (exists_eq_add_mul_of_mk_eq (mk_qlift (Ideal.Quotient.mk (Ideal.span {c}) x)).symm).choose_spec

/-- Division with remainder modulo $c$: $\mathcal{O}_F/c \times \mathcal{O}_F \simeq \mathcal{O}_F$, $(r, y) \mapsto \tilde r + cy$. -/
def divModEquiv {c : 𝓞 F} (hc : c ≠ 0) : (𝓞 F ⧸ Ideal.span {c}) × 𝓞 F ≃ 𝓞 F where
  toFun p := qlift p.1 + c * p.2
  invFun x := (Ideal.Quotient.mk _ x, qdiv c x)
  left_inv p := by
    obtain ⟨r, y⟩ := p
    have hmk : Ideal.Quotient.mk (Ideal.span {c}) (qlift r + c * y) = r := by
      rw [map_add, mk_qlift, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self c), zero_mul, add_zero]
    simp only [Prod.mk.injEq]
    refine ⟨hmk, ?_⟩
    have h := qdiv_spec c (qlift r + c * y)
    rw [hmk] at h
    exact (mul_left_cancel₀ hc (add_left_cancel h)).symm
  right_inv x := (qdiv_spec c x).symm

/-- The decomposition $(\mathcal{O}_F/c)^n \times L \simeq L$, $(r, y) \mapsto \tilde r + cy$. -/
def cuspSplitEquiv {c : 𝓞 F} (hc : c ≠ 0) :
    (Fin n → 𝓞 F ⧸ Ideal.span {c}) × latSet (oneIdeals (F := F) (n := n)) ≃
      latSet (oneIdeals (F := F) (n := n)) :=
  ((Equiv.refl _).prodCongr latSetOneEquiv.symm).trans
    ((Equiv.arrowProdEquivProdArrow _ _ _).symm.trans
      ((Equiv.piCongrRight fun _ => divModEquiv hc).trans latSetOneEquiv))

lemma cuspSplitEquiv_coe {c : 𝓞 F} (hc : c ≠ 0)
    (p : (Fin n → 𝓞 F ⧸ Ideal.span {c}) × latSet (oneIdeals (F := F) (n := n))) :
    ((cuspSplitEquiv hc p : latSet _) : Fin n → F) =
      vecO (fun i => qlift (p.1 i)) + algebraMap (𝓞 F) F c • (p.2 : Fin n → F) := by
  obtain ⟨r, y⟩ := p
  have hy : (y : Fin n → F) = vecO (latSetOneEquiv.symm y) := by
    rw [← latSetOneEquiv_coe, Equiv.apply_symm_apply]
  rw [hy]
  funext i
  simp only [cuspSplitEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id, latSetOneEquiv_coe, Equiv.piCongrRight_apply, divModEquiv, Equiv.coe_fn_mk,
    Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, vecO, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Pi.map_apply]
  rw [map_add, map_mul]

/-! ### The $\Gamma_0(\mathfrak N)$ law -/

/-- **The theta multiplier** for even rank $n = 2k$, $a, c \in \mathcal{O}_F$:
$$M_Q(a, c) = \frac{1}{\prod_v\sqrt{\det\varphi_v(A)}\,\sqrt{d_F}^{\,n}}\prod_v\Big(\frac{-i}{2\varphi_v(c)}\Big)^k\,G(a, 0, c),\qquad
  G(a, 0, c) = \sum_{r\in(\mathcal{O}_F/c)^n}e\Big(\operatorname{Tr}\frac{aQ(r)}{c}\Big)$$
($\prod_v\sqrt{\det\varphi_v(A)} = \sqrt{N(\det A)}$). For $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$, $c \ne 0$:
$\theta_Q\,|_k\,\gamma = M_Q(a, c)\,\theta_Q$ (`thetaQ_slash_gamma0`). For $F = \mathbb{Q}$ it is `QuadFormsKB.Siegel.thetaMult`. -/
@[kb "iwaniec1997" "§10.4, the theta multiplier [unverified]"]
def thetaMultF (Q : QuadForm (𝓞 F) n) (k : ℕ) (a c : 𝓞 F) : ℂ :=
  (((∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ *
      (Real.sqrt (NumberField.discr F : ℝ) ^ n)⁻¹ : ℝ) : ℂ) *
    (∏ v, (-Complex.I / (2 * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ))) ^ k) *
      gaussSumF Q a c 0

/-- $\mathrm{SL}_2(\mathcal{O}_F)$ acting on $\mathbb{H}^d$: $(\gamma z)_v = \frac{\varphi_v(a)z_v + \varphi_v(b)}{\varphi_v(c)z_v + \varphi_v(d)}$. -/
lemma coe_slHom_toF_smul (γ : SL(2, 𝓞 F)) (z : InfinitePlace F → ℍ) (v : InfinitePlace F) :
    (((slHom (realEmb F) (toF F γ) • z) v : ℍ) : ℂ) =
      ((realEmb F v (algebraMap (𝓞 F) F (γ 0 0)) : ℂ) * (z v : ℂ) +
          realEmb F v (algebraMap (𝓞 F) F (γ 0 1))) /
        ((realEmb F v (algebraMap (𝓞 F) F (γ 1 0)) : ℂ) * (z v : ℂ) +
          realEmb F v (algebraMap (𝓞 F) F (γ 1 1))) := by
  rw [Pi.smul_apply', glPos_smul_eq, UpperHalfPlane.coe_smul_of_det_pos (det_glPos_pos _)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, toF]

lemma denom_slHom_toF (γ : SL(2, 𝓞 F)) (z : InfinitePlace F → ℍ) (v : InfinitePlace F) :
    UpperHalfPlane.denom ((slHom (realEmb F) (toF F γ) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) =
      (realEmb F v (algebraMap (𝓞 F) F (γ 1 0)) : ℂ) * (z v : ℂ) +
        realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) := by
  simp [UpperHalfPlane.denom, toF]

lemma sl2O_det (γ : SL(2, 𝓞 F)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2; rwa [det_fin_two] at this

lemma realEmb_algebraMap_ne_zero {c : 𝓞 F} (hc : c ≠ 0) (v : InfinitePlace F) :
    (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) ≠ 0 := by
  rw [ofReal_ne_zero, map_ne_zero_iff _ (realEmb F v).injective]
  simpa using (FaithfulSMul.algebraMap_injective (𝓞 F) F).ne hc

/-- $Q^\#(Hx) = Q(x)$. -/
lemma qDual_hessF_mulVec {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (x : Fin n → F) :
    qDual Q (hessF Q *ᵥ x) = qv (gramF Q) x := by
  have hu : IsUnit (hessF Q).det := isUnit_iff_ne_zero.mpr (hessF_det_ne_zero hQ)
  rw [← qv_hessF_inv Q hQ, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

/-- The surviving terms: $e(\sum_v\varphi_v(Q^\#(Hx))(z_v + \frac{d_v}{c_v}))\,e(-\operatorname{Tr}\frac{dQ(x)}{c}) = e(\sum_v\varphi_v(Q(x))z_v)$. -/
lemma thetaTerm_hessF_shift {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (x : Fin n → F)
    (d c : F) (z : InfinitePlace F → ℂ) :
    thetaTerm ((1 / 4 : F) • (gramF Q)⁻¹) (hessF Q *ᵥ x)
        (fun v => z v + (realEmb F v d : ℂ) / (realEmb F v c : ℂ)) *
      cexp (-(2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (d * qv (gramF Q) x / c) : ℚ) : ℂ))) =
      thetaTerm (gramF Q) x z := by
  have h1 : qv ((1 / 4 : F) • (gramF Q)⁻¹) (hessF Q *ᵥ x) = qv (gramF Q) x := qDual_hessF_mulVec hQ x
  rw [thetaTerm, thetaTerm, h1, ← Complex.exp_add]
  congr 1
  have htr := sum_realEmb (d * qv (gramF Q) x / c)
  have htr' : ((Algebra.trace ℚ F (d * qv (gramF Q) x / c) : ℚ) : ℂ) =
      ∑ v, ((realEmb F v (d * qv (gramF Q) x / c) : ℝ) : ℂ) := by
    rw [← ofReal_ratCast, ← htr]; push_cast; rfl
  rw [htr']
  simp only [map_mul, map_div₀, mul_add, Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  ring_nf
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  conv_rhs => rw [← add_zero (∑ x_1, _)]
  congr 1
  exact Finset.sum_eq_zero fun v _ => by ring

lemma cusp_identity (a b c d z : ℂ) (hc : c ≠ 0) (hden : c * z + d ≠ 0) (hdet : a * d - b * c = 1) :
    (a * z + b) / (c * z + d) = a / c - (c ^ 2 * (z + d / c))⁻¹ := by
  have h1 : c ^ 2 * (z + d / c) = c * (c * z + d) := by field_simp
  rw [h1, eq_sub_iff_add_eq, ← one_div, div_add_div _ _ hden (mul_ne_zero hc hden),
    div_eq_div_iff (mul_ne_zero hden (mul_ne_zero hc hden)) hc]
  linear_combination (-(c * (c * z + d))) * hdet

/-- $\gamma z = \frac ac - \frac{1}{c^2u}$ with $u = z + \frac dc$, place by place (`cuspPt`). -/
lemma slHom_toF_smul_eq_cuspPt (γ : SL(2, 𝓞 F)) (hc : γ 1 0 ≠ 0) (z : InfinitePlace F → ℍ) :
    (fun v => ((slHom (realEmb F) (toF F γ) • z) v : ℂ)) =
      cuspPt (algebraMap (𝓞 F) F (γ 0 0)) (algebraMap (𝓞 F) F (γ 1 0)) fun v =>
        (z v : ℂ) + (realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) : ℂ) /
          (realEmb F v (algebraMap (𝓞 F) F (γ 1 0)) : ℂ) := by
  funext v
  have hcv := realEmb_algebraMap_ne_zero hc v
  have hdetv : (realEmb F v (algebraMap (𝓞 F) F (γ 0 0)) : ℂ) *
      realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) - realEmb F v (algebraMap (𝓞 F) F (γ 0 1)) *
        realEmb F v (algebraMap (𝓞 F) F (γ 1 0)) = 1 := by
    have := congrArg (fun t : 𝓞 F => (realEmb F v (algebraMap (𝓞 F) F t) : ℂ)) (sl2O_det γ)
    simpa using this
  have hden : (realEmb F v (algebraMap (𝓞 F) F (γ 1 0)) : ℂ) * (z v : ℂ) +
      realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) ≠ 0 := by
    rw [← denom_slHom_toF]; exact UpperHalfPlane.denom_ne_zero _ _
  have hden' : (z v : ℂ) * (realEmb F v (algebraMap (𝓞 F) F (γ 1 0)) : ℂ) +
      realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) ≠ 0 := by rw [mul_comm]; exact hden
  rw [coe_slHom_toF_smul, cuspPt, map_div₀, ofReal_div]
  exact cusp_identity _ _ _ _ _ hcv hden hdetv

/-- **$\theta_Q$ at the cusp $a/c$** ($a, c \in \mathcal{O}_F$, $c \ne 0$, $\operatorname{Im}u_v > 0$):
$$\theta_Q\Big(\frac ac - \frac{1}{c^2u}\Big) = C(u)\sum_{\mu\in(\mathfrak d^{-1})^n}e\Big(\sum_v\varphi_v(Q^\#(\mu))u_v\Big)\,G(a, \mu, c),$$
$C(u) = (\prod_v\sqrt{\det\varphi_v(A)})^{-1}\Delta(\mathcal{O}_F)^{-n}\prod_v(-iu_v/2)^{n/2}$ (`tsum_latSet_cusp` for $L = \mathcal{O}_F^n$). -/
theorem thetaLat_one_cuspPt {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (a : 𝓞 F)
    {c : 𝓞 F} (hc : c ≠ 0) {u : InfinitePlace F → ℂ} (hu : ∀ v, 0 < (u v).im) :
    thetaLat (gramF Q) oneIdeals (cuspPt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F c) u) =
      (((∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ *
          (∏ i : Fin n, embDet (oneIdeals (F := F) i))⁻¹ : ℝ) : ℂ) *
        (∏ v, (-Complex.I * u v / 2) ^ ((n : ℂ) / 2)) *
          ∑' μ : dualSet (oneIdeals (F := F) (n := n)),
            thetaTerm ((1 / 4 : F) • (gramF Q)⁻¹) μ u * gaussSumF Q a c μ := by
  have hcF : algebraMap (𝓞 F) F c ≠ 0 := fun h => hc (FaithfulSMul.algebraMap_injective (𝓞 F) F (by
    rw [map_zero]; exact h))
  have : Finite (𝓞 F ⧸ Ideal.span {c}) := finite_quot_span hc
  letI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {c})
  have hint : ∀ (r : Fin n → 𝓞 F ⧸ Ideal.span {c}) (y : latSet (oneIdeals (F := F) (n := n))),
      ∃ m : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F c *
        (qv (gramF Q) (vecO (fun i => qlift (r i)) + algebraMap (𝓞 F) F c • (y : Fin n → F)) -
          qv (gramF Q) (vecO (fun i => qlift (r i))))) = m := by
    intro r y
    obtain ⟨y', rfl⟩ := latSetOneEquiv.surjective y
    rw [latSetOneEquiv_coe]
    refine trace_int_of_mem_invDifferent ?_
    have : algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F c *
        (qv (gramF Q) (vecO (fun i => qlift (r i)) + algebraMap (𝓞 F) F c • vecO y') -
          qv (gramF Q) (vecO (fun i => qlift (r i)))) =
        algebraMap (𝓞 F) F (a * ((fun i => qlift (r i)) ⬝ᵥ Q.hessian *ᵥ y' + c * Q.eval y')) := by
      rw [qv_gramF_add, qv_smul_vec, mulVec_smul, dotProduct_smul, smul_eq_mul,
        hessF_mulVec_vecO, dotProduct_vecO]
      simp only [map_mul, map_add, qv_vecO]
      field_simp
      ring
    rw [this]; exact algebraMap_mem_invDifferent _
  have hexp := tsum_latSet_cusp hQ oneIdeals (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F c) hcF
    (fun r : Fin n → 𝓞 F ⧸ Ideal.span {c} => vecO (fun i => qlift (r i)))
    (cuspSplitEquiv hc) (cuspSplitEquiv_coe hc) hint hu
  rw [thetaLat_eq_tsum_latSet, hexp]
  -- the Gauss sums
  have hG : ∀ μ : dualSet (oneIdeals (F := F) (n := n)),
      ∑ r : Fin n → 𝓞 F ⧸ Ideal.span {c}, cexp (2 * Real.pi * Complex.I *
        ((Algebra.trace ℚ F (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F c *
            qv (gramF Q) (vecO (fun i => qlift (r i))) +
          ∑ i, (μ : Fin n → F) i * ((algebraMap (𝓞 F) F c)⁻¹ * vecO (fun i => qlift (r i)) i)) : ℚ) :
            ℂ)) =
      gaussSumF Q a c μ := by
    intro μ
    rw [gaussSumF_eq_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [gsTermF]
    congr 4
    simp only [dotProduct]
    rw [add_div, Finset.sum_div]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hG]

/-- **$\theta_Q$ at the cusp $a/c$ for a column of $\Gamma_0(\mathfrak N)$.** For $a, b, c, d \in \mathcal{O}_F$ with $ad - bc = 1$,
$c \in \mathfrak N$, $c \ne 0$, and $u = z + \frac dc$:
$\theta_Q(\frac ac - \frac{1}{c^2u}) = M_Q(a, c)\prod_v(c_vz_v + d_v)^k\,\theta_Q(z)$. -/
theorem thetaLat_cuspPt_gamma0 {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {a b c d : 𝓞 F}
    (hc : c ≠ 0) (hcN : c ∈ 𝔑) (hdet : a * d - b * c = 1) (z : InfinitePlace F → ℍ) :
    thetaLat (gramF Q) oneIdeals (cuspPt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F c) fun v =>
        (z v : ℂ) + (realEmb F v (algebraMap (𝓞 F) F d) : ℂ) /
          (realEmb F v (algebraMap (𝓞 F) F c) : ℂ)) =
      thetaMultF Q k a c *
        (∏ v, ((realEmb F v (algebraMap (𝓞 F) F c)) * (z v : ℂ) +
          realEmb F v (algebraMap (𝓞 F) F d)) ^ k) * thetaQ Q z := by
  have hcv : ∀ v, (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) ≠ 0 := realEmb_algebraMap_ne_zero hc
  have hu : ∀ v, 0 < ((z v : ℂ) + (realEmb F v (algebraMap (𝓞 F) F d) : ℂ) /
      (realEmb F v (algebraMap (𝓞 F) F c) : ℂ)).im := by
    intro v
    simp only [add_im, div_ofReal_im, ofReal_im, zero_div, add_zero]
    exact (z v).im_pos
  rw [thetaLat_one_cuspPt hQ a hc hu]
  -- only `μ = H w` survive
  have hmem : ∀ w : Fin n → 𝓞 F, hessF Q *ᵥ vecO w ∈ dualSet (oneIdeals (F := F) (n := n)) :=
    fun w => mem_dualSet_one.mpr fun i => by
      rw [hessF_mulVec_vecO]; exact algebraMap_mem_invDifferent _
  set g : (Fin n → 𝓞 F) → dualSet (oneIdeals (F := F) (n := n)) := fun w =>
    ⟨hessF Q *ᵥ vecO w, hmem w⟩ with hg
  have hginj : Function.Injective g := by
    intro w w' h
    have h1 := congrArg Subtype.val h
    simp only [hg] at h1
    have hu' : IsUnit (hessF Q).det := isUnit_iff_ne_zero.mpr (hessF_det_ne_zero hQ)
    have h2 := congrArg (fun t => (hessF Q)⁻¹ *ᵥ t) h1
    simp only [mulVec_mulVec, nonsing_inv_mul _ hu', one_mulVec] at h2
    funext i
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F (congrFun h2 i)
  have hsupp : Function.support (fun μ : dualSet (oneIdeals (F := F) (n := n)) =>
      thetaTerm ((1 / 4 : F) • (gramF Q)⁻¹) μ (fun v => (z v : ℂ) +
        (realEmb F v (algebraMap (𝓞 F) F d) : ℂ) / (realEmb F v (algebraMap (𝓞 F) F c) : ℂ)) *
          gaussSumF Q a c μ) ⊆ Set.range g := by
    intro μ hμ
    have hG0 : gaussSumF Q a c μ ≠ 0 := fun h0 => hμ (by simp [h0])
    obtain ⟨w, hw⟩ := exists_eq_hessF_of_gaussSumF_ne_zero hQ hlev a hc hcN
      (mem_dualSet_one.mp μ.2) hG0
    exact ⟨w, Subtype.ext hw.symm⟩
  rw [← hginj.tsum_eq hsupp]
  have hterm : ∀ w : Fin n → 𝓞 F,
      thetaTerm ((1 / 4 : F) • (gramF Q)⁻¹) (g w : Fin n → F) (fun v => (z v : ℂ) +
        (realEmb F v (algebraMap (𝓞 F) F d) : ℂ) / (realEmb F v (algebraMap (𝓞 F) F c) : ℂ)) *
          gaussSumF Q a c (g w) =
        gaussSumF Q a c 0 * thetaTerm (gramF Q) (vecO w) fun v => (z v : ℂ) := by
    intro w
    simp only [hg]
    rw [gaussSumF_hessF Q hc hdet w, ← thetaTerm_hessF_shift hQ (vecO w) (algebraMap (𝓞 F) F d)
      (algebraMap (𝓞 F) F c)]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hθ : ∑' w : Fin n → 𝓞 F, thetaTerm (gramF Q) (vecO w) (fun v => (z v : ℂ)) =
      thetaQ Q z := by
    rw [thetaQ_eq_thetaLatH, thetaLatH, thetaLat_eq_tsum_latSet, ← latSetOneEquiv.tsum_eq]
    rfl
  rw [hθ, thetaMultF]
  -- the constants
  have hnk : ((n : ℂ) / 2) = ((k : ℕ) : ℂ) := by rw [hn]; push_cast; ring
  simp only [hnk, cpow_natCast, embDet_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hprod : ∏ v, (-Complex.I * ((z v : ℂ) + (realEmb F v (algebraMap (𝓞 F) F d) : ℂ) /
        (realEmb F v (algebraMap (𝓞 F) F c) : ℂ)) / 2) ^ k =
      (∏ v, (-Complex.I / (2 * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ))) ^ k) *
        ∏ v, ((realEmb F v (algebraMap (𝓞 F) F c) : ℂ) * (z v : ℂ) +
          realEmb F v (algebraMap (𝓞 F) F d)) ^ k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← mul_pow]
    congr 1
    have := hcv v
    field_simp
  rw [hprod]
  push_cast
  ring

/-- **The $\Gamma_0(\mathfrak N)$ transformation of $\theta_Q$, pointwise.** For $Q$ totally positive definite of rank
$n = 2k$, $\mathfrak N$ a level (`IsThetaLevelF`), $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$ with $c \ne 0$
(0-based: $a = \gamma_{00}$, $c = \gamma_{10}$, $d = \gamma_{11}$) and $z \in \mathbb{H}^d$:
$$\theta_Q(\gamma z) = M_Q(a, c)\prod_v(\varphi_v(c)z_v + \varphi_v(d))^k\,\theta_Q(z).$$ -/
theorem thetaQ_gamma0_apply {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {γ : SL(2, 𝓞 F)}
    (hγ : γ ∈ Gamma0R 𝔑) (hc : γ 1 0 ≠ 0) (z : InfinitePlace F → ℍ) :
    thetaQ Q (slHom (realEmb F) (toF F γ) • z) =
      thetaMultF Q k (γ 0 0) (γ 1 0) *
        (∏ v, ((realEmb F v (algebraMap (𝓞 F) F (γ 1 0)) : ℂ) * (z v : ℂ) +
          realEmb F v (algebraMap (𝓞 F) F (γ 1 1))) ^ k) * thetaQ Q z := by
  calc thetaQ Q (slHom (realEmb F) (toF F γ) • z) =
      thetaLat (gramF Q) oneIdeals (fun v => ((slHom (realEmb F) (toF F γ) • z) v : ℂ)) := by
        rw [thetaQ_eq_thetaLatH]; rfl
    _ = _ := by
      rw [slHom_toF_smul_eq_cuspPt γ hc z, thetaLat_cuspPt_gamma0 hQ hn hlev hc hγ (sl2O_det γ) z]

/-- **The $\Gamma_0(\mathfrak N)$ law with a Gauss-sum multiplier.** For $Q$ totally positive definite of rank $n = 2k$ over
$\mathcal{O}_F$, $\mathfrak N$ a level (`IsThetaLevelF`) and $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(\mathfrak N)$ with $c \ne 0$:
$$\theta_Q\,|_k\,\gamma = M_Q(a, c)\,\theta_Q,\qquad
  M_Q(a, c) = \frac{1}{\sqrt{N(\det A)}\,d_F^{k}}\prod_v\Big(\frac{-i}{2\varphi_v(c)}\Big)^k\sum_{r\in(\mathcal{O}_F/c)^n}
  e\Big(\operatorname{Tr}\frac{aQ(r)}{c}\Big)$$
(`thetaMultF`). For $F = \mathbb{Q}$ this is `QuadFormsKB.Siegel.theta_gamma0`. -/
@[kb "shimura1973" "§2, theta transformation over F [unverified]"]
theorem thetaQ_slash_gamma0 {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {γ : SL(2, 𝓞 F)}
    (hγ : γ ∈ Gamma0R 𝔑) (hc : γ 1 0 ≠ 0) :
    thetaQ Q ∣[(k : ℤ)] slHom (realEmb F) (toF F γ) = thetaMultF Q k (γ 0 0) (γ 1 0) • thetaQ Q := by
  funext z
  rw [slash_apply, thetaQ_gamma0_apply hQ hn hlev hγ hc z, Pi.smul_apply, smul_eq_mul]
  have h : ∀ v, (((((slHom (realEmb F) (toF F γ) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^
      ((k : ℤ) - 1) : ℝ)) : ℂ) * UpperHalfPlane.denom ((slHom (realEmb F) (toF F γ) v : GL(2, ℝ)⁺) :
        GL (Fin 2) ℝ) (z v) ^ (-(k : ℤ)) =
      (((realEmb F v (algebraMap (𝓞 F) F (γ 1 0)) : ℂ) * (z v : ℂ) +
          realEmb F v (algebraMap (𝓞 F) F (γ 1 1))) ^ k)⁻¹ := by
    intro v
    rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul, denom_slHom_toF, _root_.zpow_neg, zpow_natCast]
  simp_rw [h]
  rw [Finset.prod_inv_distrib]
  have hne : ∏ v, (((realEmb F v (algebraMap (𝓞 F) F (γ 1 0)) : ℂ) * (z v : ℂ) +
      realEmb F v (algebraMap (𝓞 F) F (γ 1 1))) ^ k) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ ?_
    rw [← denom_slHom_toF]; exact UpperHalfPlane.denom_ne_zero _ _
  field_simp

/-! ### The case $c = 0$ -/

lemma thetaQ_eq_tsum (Q : QuadForm (𝓞 F) n) (w : InfinitePlace F → ℂ)
    (z : InfinitePlace F → ℍ) (hw : ∀ v, (z v : ℂ) = w v) :
    thetaQ Q z = ∑' x : Fin n → 𝓞 F, thetaTerm (gramF Q) (vecO x) w := by
  rw [thetaQ_eq_thetaLatH, thetaLatH, thetaLat_eq_tsum_latSet, ← latSetOneEquiv.tsum_eq]
  have : (fun v => (z v : ℂ)) = w := funext hw
  rw [this]; rfl

/-- **The case $c = 0$**: for $\gamma = \begin{pmatrix}a&b\\0&d\end{pmatrix} \in \mathrm{SL}_2(\mathcal{O}_F)$ ($a = d^{-1}$ a unit),
$\theta_Q\,|_k\,\gamma = \big(\prod_v\varphi_v(d)\big)^{-k}\theta_Q$, i.e. the multiplier is $N(d)^{-k} = \pm1$. -/
@[kb "shimura1973" "§2, theta transformation over F [unverified]"]
theorem thetaQ_slash_gamma0_c0 (Q : QuadForm (𝓞 F) n) (k : ℤ) {γ : SL(2, 𝓞 F)} (hc : γ 1 0 = 0) :
    thetaQ Q ∣[k] slHom (realEmb F) (toF F γ) =
      ((∏ v, (realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) : ℂ)) ^ k)⁻¹ • thetaQ Q := by
  have hdet := sl2O_det γ
  rw [hc, mul_zero, sub_zero] at hdet
  set u : (𝓞 F)ˣ := ⟨γ 0 0, γ 1 1, hdet, by rw [mul_comm]; exact hdet⟩
  have hdetF : algebraMap (𝓞 F) F (γ 0 0) * algebraMap (𝓞 F) F (γ 1 1) = 1 := by
    rw [← map_mul, hdet, map_one]
  funext z
  rw [slash_apply, Pi.smul_apply, smul_eq_mul]
  have hden : ∀ v, UpperHalfPlane.denom ((slHom (realEmb F) (toF F γ) v : GL(2, ℝ)⁺) :
      GL (Fin 2) ℝ) (z v) = (realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) : ℂ) := by
    intro v; rw [denom_slHom_toF, hc]; simp
  have hfac : ∏ v, (((((slHom (realEmb F) (toF F γ) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^
      (k - 1) : ℝ)) : ℂ) * UpperHalfPlane.denom ((slHom (realEmb F) (toF F γ) v : GL(2, ℝ)⁺) :
        GL (Fin 2) ℝ) (z v) ^ (-k) =
      ((∏ v, (realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) : ℂ)) ^ k)⁻¹ := by
    rw [← Finset.prod_zpow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul, hden, _root_.zpow_neg]
  rw [hfac, mul_comm]
  congr 1
  -- `θ(γ z) = θ(z)`: substitute `x ↦ a x`
  rw [thetaQ_eq_tsum Q _ z (fun v => rfl), thetaQ_eq_tsum Q _ _ (fun v => rfl)]
  conv_rhs => rw [← (MulAction.toPerm u : Equiv.Perm (Fin n → 𝓞 F)).tsum_eq]
  refine tsum_congr fun x => ?_
  have hx : vecO ((MulAction.toPerm u : Equiv.Perm (Fin n → 𝓞 F)) x) =
      algebraMap (𝓞 F) F (γ 0 0) • vecO x := by
    funext i
    show algebraMap (𝓞 F) F ((u : 𝓞 F) * x i) = _
    rw [map_mul]; rfl
  rw [hx, thetaTerm, thetaTerm, qv_smul_vec]
  have htr : ∃ m : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F (γ 0 0) *
      algebraMap (𝓞 F) F (γ 0 1) * qv (gramF Q) (vecO x)) = m := by
    refine trace_int_of_mem_invDifferent ?_
    rw [qv_vecO, ← map_mul, ← map_mul]; exact algebraMap_mem_invDifferent _
  obtain ⟨m, hm⟩ := htr
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m, ?_⟩
  have hsum := sum_realEmb (algebraMap (𝓞 F) F (γ 0 0) * algebraMap (𝓞 F) F (γ 0 1) *
    qv (gramF Q) (vecO x))
  rw [hm] at hsum
  have hsumC : ∑ v, ((realEmb F v (algebraMap (𝓞 F) F (γ 0 0)) : ℂ) *
      (realEmb F v (algebraMap (𝓞 F) F (γ 0 1)) : ℂ) * (realEmb F v (qv (gramF Q) (vecO x)) : ℂ)) =
        m := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hsum
    simp only [map_mul, ofReal_sum, ofReal_mul] at this
    rw [this]; push_cast; rfl
  have hpt : ∀ v, (((slHom (realEmb F) (toF F γ) • z) v : ℍ) : ℂ) =
      (realEmb F v (algebraMap (𝓞 F) F (γ 0 0)) : ℂ) ^ 2 * (z v : ℂ) +
        (realEmb F v (algebraMap (𝓞 F) F (γ 0 0)) : ℂ) * realEmb F v (algebraMap (𝓞 F) F (γ 0 1)) := by
    intro v
    rw [coe_slHom_toF_smul, hc]
    have hv : (realEmb F v (algebraMap (𝓞 F) F (γ 0 0)) : ℂ) *
        realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) = 1 := by
      have := congrArg (fun t : F => (realEmb F v t : ℂ)) hdetF
      simpa using this
    have hd0 : (realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) : ℂ) ≠ 0 := right_ne_zero_of_mul_eq_one hv
    simp only [map_zero, ofReal_zero, zero_mul, zero_add]
    rw [div_eq_iff hd0]
    linear_combination (-((realEmb F v (algebraMap (𝓞 F) F (γ 0 0)) : ℂ) * (z v : ℂ) +
      realEmb F v (algebraMap (𝓞 F) F (γ 0 1)))) * hv
  simp_rw [hpt]
  simp only [map_mul, map_pow]
  push_cast
  rw [← hsumC, mul_comm _ (2 * (Real.pi : ℂ) * Complex.I), ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun v _ => by ring

/-! ### The multiplier as a character of $\Gamma_0(\mathfrak N)$ -/

/-- The base point $(i, \dots, i) \in \mathbb{H}^d$. -/
def ptI : InfinitePlace F → ℍ := fun _ => UpperHalfPlane.I

/-- $\theta_Q(i, \dots, i) = \sum_xe^{-2\pi\operatorname{Tr}Q(x)}$ has real part $\ge 1$; in particular $\theta_Q \ne 0$. -/
theorem one_le_re_thetaQ_ptI {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) :
    1 ≤ (thetaQ Q (ptI (F := F))).re := by
  have hs := (summable_norm_thetaQTerm hQ (ptI (F := F))).of_norm
  rw [thetaQ, Complex.re_tsum hs]
  have hterm : ∀ x : Fin n → 𝓞 F, (thetaQTerm Q ptI x).re =
      Real.exp (-(2 * Real.pi) * ∑ v, realEmb F v (algebraMap (𝓞 F) F (Q.eval x))) := by
    intro x
    have : thetaQTerm Q ptI x = ((Real.exp (-(2 * Real.pi) *
        ∑ v, realEmb F v (algebraMap (𝓞 F) F (Q.eval x))) : ℝ) : ℂ) := by
      rw [thetaQTerm, ofReal_exp]
      congr 1
      simp only [ptI, UpperHalfPlane.coe_I, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun v _ => ?_
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this, ofReal_re]
  rw [tsum_congr hterm]
  have hs' : Summable fun x : Fin n → 𝓞 F =>
      Real.exp (-(2 * Real.pi) * ∑ v, realEmb F v (algebraMap (𝓞 F) F (Q.eval x))) := by
    refine (Complex.reCLM.summable hs).congr fun x => ?_
    simp only [Complex.reCLM_apply]
    exact hterm x
  have h0 := hs'.le_tsum 0 (fun x _ => (Real.exp_pos _).le)
  have hq0 : Q.eval (0 : Fin n → 𝓞 F) = 0 := by simp [QuadForm.eval, QuadForm.evalIn]
  simp only [hq0, map_zero, Finset.sum_const_zero, mul_zero, Real.exp_zero] at h0
  exact h0

theorem thetaQ_ptI_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) :
    thetaQ Q (ptI (F := F)) ≠ 0 := by
  intro h
  have := one_le_re_thetaQ_ptI hQ
  rw [h, zero_re] at this
  linarith

/-- **The theta multiplier on $\Gamma_0(\mathfrak N)$**: $m_Q(\gamma) = M_Q(a, c)$ (`thetaMultF`) if $c \ne 0$, and
$N(d)^{-k}$ if $c = 0$. Then $\theta_Q\,|_k\,\gamma = m_Q(\gamma)\,\theta_Q$ on $\Gamma_0(\mathfrak N)$ (`thetaQ_slash_eq_thetaMultG`). -/
@[kb "iwaniec1997" "§10.4, the theta multiplier [unverified]"]
noncomputable def thetaMultG (Q : QuadForm (𝓞 F) n) (k : ℕ) (γ : SL(2, 𝓞 F)) : ℂ :=
  haveI := Classical.propDecidable
  if γ 1 0 = 0 then ((∏ v, (realEmb F v (algebraMap (𝓞 F) F (γ 1 1)) : ℂ)) ^ (k : ℤ))⁻¹
  else thetaMultF Q k (γ 0 0) (γ 1 0)

/-- **$\theta_Q\,|_k\,\gamma = m_Q(\gamma)\,\theta_Q$ for every $\gamma \in \Gamma_0(\mathfrak N)$** ($n = 2k$, $\mathfrak N$ a level). -/
theorem thetaQ_slash_eq_thetaMultG {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {γ : SL(2, 𝓞 F)}
    (hγ : γ ∈ Gamma0R 𝔑) :
    thetaQ Q ∣[(k : ℤ)] slHom (realEmb F) (toF F γ) = thetaMultG Q k γ • thetaQ Q := by
  by_cases hc : γ 1 0 = 0
  · rw [thetaQ_slash_gamma0_c0 Q k hc]; simp [thetaMultG, hc]
  · rw [thetaQ_slash_gamma0 hQ hn hlev hγ hc]; simp [thetaMultG, hc]

/-- **The multiplier is a character of $\Gamma_0(\mathfrak N)$**: $m_Q(\gamma\delta) = m_Q(\gamma)m_Q(\delta)$
(because $|_k$ is an action and $\theta_Q \ne 0$). -/
theorem thetaMultG_mul {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {γ δ : SL(2, 𝓞 F)}
    (hγ : γ ∈ Gamma0R 𝔑) (hδ : δ ∈ Gamma0R 𝔑) :
    thetaMultG Q k (γ * δ) = thetaMultG Q k γ * thetaMultG Q k δ := by
  have h1 := thetaQ_slash_eq_thetaMultG hQ hn hlev (Subgroup.mul_mem _ hγ hδ)
  rw [map_mul, map_mul, SlashAction.slash_mul, thetaQ_slash_eq_thetaMultG hQ hn hlev hγ,
    smul_slash, thetaQ_slash_eq_thetaMultG hQ hn hlev hδ, smul_smul] at h1
  have h2 := congrFun h1 ptI
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_right_cancel₀ (thetaQ_ptI_ne_zero hQ) h2).symm

/-- $m_Q(T(b)\gamma) = m_Q(\gamma)$: the multiplier depends on $a$ only modulo $c$. -/
theorem thetaMultG_transl_mul {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {γ : SL(2, 𝓞 F)}
    (hγ : γ ∈ Gamma0R 𝔑) (b : 𝓞 F) :
    thetaMultG Q k (⟨!![1, b; 0, 1], by simp [det_fin_two_of]⟩ * γ) = thetaMultG Q k γ := by
  set T : SL(2, 𝓞 F) := ⟨!![1, b; 0, 1], by simp [det_fin_two_of]⟩
  have hT : T ∈ Gamma0R 𝔑 := by
    show T 1 0 ∈ 𝔑
    simp [T]
  rw [thetaMultG_mul hQ hn hlev hT hγ]
  have : thetaMultG Q k T = 1 := by
    have h1 := thetaQ_slash_eq_thetaMultG hQ hn hlev hT
    have hTF : toF F T = transl (algebraMap (𝓞 F) F b) := by
      ext i j
      change algebraMap (𝓞 F) F ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓞 F)) i j) =
        (!![1, algebraMap (𝓞 F) F b; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hTF, thetaQ_slash_transl_int] at h1
    have h2 := congrFun h1 ptI
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_eq_right₀ (thetaQ_ptI_ne_zero hQ)).mp h2.symm
  rw [this, one_mul]

end

end QuadFormsKB.HilbertModular
