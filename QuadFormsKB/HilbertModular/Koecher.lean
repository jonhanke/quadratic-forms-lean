/-
# Hilbert modular forms V: the Koecher principle over a totally real field

Let $F$ be totally real of degree $d \ge 2$, $\Gamma \le \mathrm{SL}_2(F)$, and $f : \mathbb{H}^d \to \mathbb{C}$ holomorphic with
$f\,|_k\,\gamma = f$ for $\gamma \in \Gamma$. Suppose $\Gamma$ contains

* the translations $T(\beta) = \begin{pmatrix}1&\beta\\0&1\end{pmatrix}$ (`transl`) for $\beta$ in a fractional ideal $I$
  (the period lattice), and
* the diagonal matrices $\mathrm{diag}(u^m, u^{-m})$ (`diagU`) for all units $u \in \mathcal{O}_F^\times$ and some fixed $m \ge 1$

(true for every $\Gamma$ commensurable with $\mathrm{SL}_2(\mathcal{O}_F)$; for $\Gamma_0(\mathfrak N)$ with $I = \mathcal{O}_F$, $m = 1$:
`transl_mem_Gamma0`, `diagU_mem_Gamma0`). Write $c_\nu(y)$ for the Fourier coefficients of $f$ with respect to the lattice $I$
(`coeff`, in the $\mathbb{Z}$-basis `koecherBasis I` of $I$ embedded in $\mathbb{R}^d$), for $\nu$ in the trace dual $I^\vee$.

**Koecher principle** (`koecher`): if $\nu \ne 0$ is not totally positive then $c_\nu \equiv 0$. So the Fourier expansion of $f$
is supported on $\{0\} \cup (I^\vee)_{\gg 0}$ **without any hypothesis at the cusps**; for $d \ge 2$ the cusp condition in
`modularFormSpace` is automatic at the level of Fourier coefficients. (`koecher_HMF_Gamma0`: the case $\Gamma_0(\mathfrak N)$,
$I = \mathcal{O}_F$, $I^\vee = \mathfrak d^{-1}$.)

*Proof.* Choose a place $w$ with $\nu_w < 0$ and (Dirichlet; `NumberField.Units.dirichletUnitTheorem.exists_unit`) a unit
$u_0$ with $|u_0|_v < 1$ for all $v \ne w$; then $|u_0|_w > 1$ because $\prod_v|u_0|_v = |N(u_0)| = 1$ and $d \ge 2$. With
$u = u_0^m$, invariance under $\mathrm{diag}(u, u^{-1})$ gives $|f(u^2z)| = |f(z)|$ (`norm_slash_diagU`), and
`koecher_coeff_eq_zero` applies with $\varepsilon = (u_v^2)_v$.

*Not done here* (only planned): Fourier inversion ($f = \sum_\nu a_\nu e(\operatorname{Tr}\nu z)$,
absolutely and locally uniformly), hence the boundedness form of Koecher's principle (boundedness of $f\,|_k\,\gamma$ at
$i\infty$ for every $\gamma$); this needs convergence of $\sum_{\nu \gg 0}|a_\nu|e^{-2\pi\operatorname{Tr}(\nu y)}$.
-/
import QuadFormsKB.HilbertModular.Forms
import QuadFormsKB.HilbertModular.QExpansion
import QuadFormsKB.Analysis.MinkowskiPoisson

open Matrix NumberField NumberField.InfinitePlace NumberField.mixedEmbedding UpperHalfPlane Complex
open scoped MatrixGroups Real nonZeroDivisors ModularForm

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Real embeddings and the trace -/

lemma abs_realEmb (v : InfinitePlace F) (x : F) : |realEmb F v x| = v x := by
  rw [← Real.norm_eq_abs]; exact norm_embedding_of_isReal _ x

/-- The vector $(\varphi_v(x))_v \in \mathbb{R}^d$ of real embeddings of $x \in F$. -/
noncomputable def realVec (x : F) : InfinitePlace F → ℝ := fun v => realEmb F v x

lemma realVec_add (x x' : F) : realVec (x + x') = realVec x + realVec x' := by
  funext v; simp [realVec]

lemma realVec_sum {J : Type*} (s : Finset J) (x : J → F) :
    realVec (∑ j ∈ s, x j) = ∑ j ∈ s, realVec (x j) := by
  funext v; simp [realVec]

lemma realVec_intCast_mul (n : ℤ) (x : F) : realVec ((n : F) * x) = (n : ℝ) • realVec x := by
  funext v; simp [realVec]

instance isEmpty_complexPlaces : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => (not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩

/-- **$\sum_v\varphi_v(x) = \operatorname{Tr}_{F/\mathbb{Q}}(x)$** for totally real $F$. -/
lemma sum_realEmb (x : F) : ∑ v, realEmb F v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  classical
  rw [← QuadFormsKB.Analysis.traceInf_mixedEmbedding, QuadFormsKB.Analysis.traceInf]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mixedEmbedding_apply_isReal]
  exact (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v)
    (fun w : {w : InfinitePlace F // IsReal w} => embedding_of_isReal w.2 x)
    (fun v => realEmb F v x) fun _ => rfl).symm

lemma pair_realVec (a c : F) :
    pair (realVec a) (realVec c) = ((Algebra.trace ℚ F (a * c) : ℚ) : ℝ) := by
  rw [← sum_realEmb, pair]
  simp [realVec]

/-- For a unit, $\prod_v|u|_v = 1$. -/
lemma prod_place_unit (u : (𝓞 F)ˣ) : ∏ v : InfinitePlace F, v (u : F) = 1 := by
  have h := prod_eq_abs_norm (u : F)
  have hm : ∀ v : InfinitePlace F, v.mult = 1 := fun v => by
    simp [mult, IsTotallyReal.isReal v]
  simp only [hm, pow_one] at h
  rw [h, NumberField.Units.norm]; simp

/-! ### The real-coordinate lattice basis of a fractional ideal -/

/-- $F \otimes \mathbb{R} = \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ is $\mathbb{R}^d$ for totally real $F$. -/
noncomputable def mixedEquiv : mixedSpace F ≃ₗ[ℝ] (InfinitePlace F → ℝ) where
  toFun y v := y.1 ⟨v, IsTotallyReal.isReal v⟩
  invFun x := (fun w => x w.1, fun w => isEmptyElim w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    ext w
    · rfl
    · exact isEmptyElim w
  right_inv _ := rfl

/-- **The lattice basis of a fractional ideal $I$ in $\mathbb{R}^d$**: the real embeddings of a $\mathbb{Z}$-basis of $I$
(`QuadFormsKB.Analysis.bq`), an $\mathbb{R}$-basis of $\mathbb{R}^d$ (Minkowski). -/
noncomputable def koecherBasis (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Module.Basis (Fin (Module.finrank ℚ F)) ℝ (InfinitePlace F → ℝ) :=
  (QuadFormsKB.Analysis.bR I).map mixedEquiv

lemma koecherBasis_apply (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (j : Fin (Module.finrank ℚ F)) :
    koecherBasis I j = realVec (QuadFormsKB.Analysis.bq I j) := by
  rw [koecherBasis, Module.Basis.map_apply, QuadFormsKB.Analysis.bR_apply]
  funext v
  simp [mixedEquiv, realVec, realEmb]

lemma koecherBasis_symm (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (m : Fin (Module.finrank ℚ F) → ℤ) :
    (koecherBasis I).equivFun.symm (fun j => (m j : ℝ)) =
      realVec (QuadFormsKB.Analysis.latElt I m) := by
  rw [Module.Basis.equivFun_symm_apply, QuadFormsKB.Analysis.latElt, realVec_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [koecherBasis_apply, realVec_intCast_mul]

lemma latElt_mem (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (m : Fin (Module.finrank ℚ F) → ℤ) :
    QuadFormsKB.Analysis.latElt I m ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [← QuadFormsKB.Analysis.latEquiv_coe]
  exact (QuadFormsKB.Analysis.latEquiv I m).2

lemma bq_mem (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (j : Fin (Module.finrank ℚ F)) :
    QuadFormsKB.Analysis.bq I j ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := by
  classical
  have := latElt_mem I (Pi.single j 1)
  have h : QuadFormsKB.Analysis.latElt I (Pi.single j 1) = QuadFormsKB.Analysis.bq I j := by
    rw [QuadFormsKB.Analysis.latElt, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Pi.single_apply, hij]
    · simp
  rwa [h] at this

/-! ### Translations and diagonal matrices -/

/-- **The translation** $T(\beta) = \begin{pmatrix}1&\beta\\0&1\end{pmatrix} \in \mathrm{SL}_2(F)$. -/
def transl (β : F) : SL(2, F) := ⟨!![1, β; 0, 1], by simp [det_fin_two_of]⟩

/-- **The diagonal matrix** $\mathrm{diag}(u, u^{-1}) \in \mathrm{SL}_2(F)$ for $u \in F^\times$. -/
def diagU (u : Fˣ) : SL(2, F) := ⟨!![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)], by simp [det_fin_two_of]⟩

@[simp] lemma transl_00 (β : F) : transl β 0 0 = 1 := rfl
@[simp] lemma transl_01 (β : F) : transl β 0 1 = β := rfl
@[simp] lemma transl_10 (β : F) : transl β 1 0 = 0 := rfl
@[simp] lemma transl_11 (β : F) : transl β 1 1 = 1 := rfl
@[simp] lemma diagU_00 (u : Fˣ) : diagU u 0 0 = u := rfl
@[simp] lemma diagU_01 (u : Fˣ) : diagU u 0 1 = 0 := rfl
@[simp] lemma diagU_10 (u : Fˣ) : diagU u 1 0 = 0 := rfl
@[simp] lemma diagU_11 (u : Fˣ) : diagU u 1 1 = ((u⁻¹ : Fˣ) : F) := rfl

/-- A unit of $\mathcal{O}_F$ as a unit of $F$. -/
noncomputable def unitF (u : (𝓞 F)ˣ) : Fˣ := Units.map (algebraMap (𝓞 F) F).toMonoidHom u

@[simp] lemma coe_unitF (u : (𝓞 F)ˣ) : ((unitF u : Fˣ) : F) = (u : F) := rfl

lemma ptXY_coe {x y : InfinitePlace F → ℝ} (hy : ∀ v, 0 < y v) (v : InfinitePlace F) :
    ((ptXY x y v : ℍ) : ℂ) = (x v : ℂ) + (y v : ℂ) * Complex.I := ptXY_im hy v

/-- $f\,|_k\,T(\beta)$ at $x + iy$ is $f(x + \varphi(\beta) + iy)$. -/
lemma slash_transl_ptXY (k : ℤ) (f : (InfinitePlace F → ℍ) → ℂ) (β : F)
    {x y : InfinitePlace F → ℝ} (hy : ∀ v, 0 < y v) :
    (f ∣[k] slHom (realEmb F) (transl β)) (ptXY x y) = f (ptXY (x + realVec β) y) := by
  rw [slash_apply]
  have hprod : ∏ v, (((((slHom (realEmb F) (transl β) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^
      (k - 1) : ℝ)) : ℂ) * denom ((slHom (realEmb F) (transl β) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ)
        (ptXY x y v) ^ (-k) = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul]
    simp [denom]
  rw [hprod, mul_one]
  congr 1
  funext v
  apply UpperHalfPlane.ext
  rw [Pi.smul_apply', glPos_smul_eq, coe_smul_of_det_pos (det_glPos_pos _), ptXY_coe hy,
    ptXY_coe hy]
  simp [num, denom, realVec]
  ring

/-- $|f\,|_k\,\mathrm{diag}(u, u^{-1})|$ at $x + iy$ is $|f(u^2x + iu^2y)|$ for a unit $u$ of $\mathcal{O}_F$. -/
lemma norm_slash_diagU (k : ℤ) (f : (InfinitePlace F → ℍ) → ℂ) (u : (𝓞 F)ˣ)
    {x y : InfinitePlace F → ℝ} (hy : ∀ v, 0 < y v) :
    ‖(f ∣[k] slHom (realEmb F) (diagU (unitF u))) (ptXY x y)‖ =
      ‖f (ptXY ((fun v => realEmb F v (u : F) ^ 2) * x) ((fun v => realEmb F v (u : F) ^ 2) * y))‖ := by
  rw [slash_apply, norm_mul]
  have hu : ∀ v, realEmb F v (u : F) ≠ 0 := fun v => by
    simp only [ne_eq, map_eq_zero]; exact (unitF u).ne_zero
  have hprod : ‖∏ v, (((((slHom (realEmb F) (diagU (unitF u)) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^
      (k - 1) : ℝ)) : ℂ) * denom ((slHom (realEmb F) (diagU (unitF u)) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ)
        (ptXY x y v) ^ (-k)‖ = 1 := by
    rw [norm_prod]
    have : ∀ v, ‖(((((slHom (realEmb F) (diagU (unitF u)) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^
        (k - 1) : ℝ)) : ℂ) * denom ((slHom (realEmb F) (diagU (unitF u)) v : GL(2, ℝ)⁺) :
          GL (Fin 2) ℝ) (ptXY x y v) ^ (-k)‖ = (v (u : F)) ^ k := by
      intro v
      rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul, norm_zpow]
      have hd : denom ((slHom (realEmb F) (diagU (unitF u)) v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ)
          (ptXY x y v) = ((realEmb F v (u : F))⁻¹ : ℝ) := by
        simp [denom]
      rw [hd, Complex.norm_real, norm_inv, Real.norm_eq_abs, abs_realEmb, _root_.zpow_neg, _root_.inv_zpow,
        inv_inv]
    rw [Finset.prod_congr rfl fun v _ => this v, Finset.prod_zpow, prod_place_unit, _root_.one_zpow]
  rw [hprod, mul_one]
  congr 2
  funext v
  apply UpperHalfPlane.ext
  rw [Pi.smul_apply', glPos_smul_eq, coe_smul_of_det_pos (det_glPos_pos _), ptXY_coe hy]
  rw [ptXY_coe (fun v => by
    simp only [Pi.mul_apply]; have := hu v; have := hy v; positivity)]
  simp [num, denom]
  field_simp

/-! ### The Koecher principle -/

/-- Invariance under the translations $T(\beta)$, $\beta \in I$, makes $f$ periodic for the lattice `koecherBasis I`. -/
lemma isLatticePeriodic_of_transl {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ} {Γ : Subgroup SL(2, F)}
    (hinv : ∀ γ ∈ Γ, f ∣[k] slHom (realEmb F) γ = f) (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hT : ∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), transl β ∈ Γ) :
    IsLatticePeriodic f (koecherBasis I) := by
  intro m x y hy
  rw [koecherBasis_symm, ← slash_transl_ptXY k f _ hy, hinv _ (hT _ (latElt_mem I m))]

/-- $\nu \in I^\vee$ (trace dual) gives a dual vector for `koecherBasis I`. -/
lemma isDual_of_trace (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {ν : F}
    (hν : ∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), ∃ n : ℤ, Algebra.trace ℚ F (ν * β) = n) :
    IsDual (koecherBasis I) (realVec ν) := by
  intro j
  obtain ⟨n, hn⟩ := hν _ (bq_mem I j)
  exact ⟨n, by rw [koecherBasis_apply, pair_realVec, hn]; simp⟩

/-- A nonzero element that is not totally positive is negative at some real place. -/
lemma exists_neg_of_not_totallyPositive {ν : F} (h0 : ν ≠ 0)
    (hpos : ¬ ∀ v : InfinitePlace F, 0 < realEmb F v ν) : ∃ w, realEmb F w ν < 0 := by
  push_neg at hpos
  obtain ⟨w, hw⟩ := hpos
  refine ⟨w, lt_of_le_of_ne hw ?_⟩
  intro h
  exact h0 ((realEmb F w).injective (by rw [h, map_zero]))

/-- **The Koecher principle for Hilbert modular forms** ($d = [F:\mathbb{Q}] \ge 2$, coefficient form). Let $f$ be holomorphic
on $\mathbb{H}^d$ with $f\,|_k\,\gamma = f$ for $\gamma \in \Gamma$, where $\Gamma \ni T(\beta)$ for $\beta \in I$ ($I$ a fractional ideal) and
$\Gamma \ni \mathrm{diag}(u^m, u^{-m})$ for all units $u$ ($m \ge 1$). If $\nu \in I^\vee$ and $\varphi_w(\nu) < 0$ for some place $w$,
then the Fourier coefficient $c_\nu(y)$ of $f$ (lattice $I$) vanishes for every $y > 0$. No condition at the cusps is
assumed.

Parameters: `hd` ($d \ge 2$), `hinv` (invariance), `hf` (holomorphy), `I`, `hT` (translations), `m`, `hm`, `hU`
(units), `ν`, `hν` ($\nu \in I^\vee$), `hw` ($\nu_w < 0$), `y`, `hy` ($y > 0$). -/
@[kb "freitag1990" "Ch. I, §4, Koecher principle [unverified]"]
theorem koecher (hd : 2 ≤ Fintype.card (InfinitePlace F)) {Γ : Subgroup SL(2, F)} {k : ℤ}
    {f : (InfinitePlace F → ℍ) → ℂ} (hinv : ∀ γ ∈ Γ, f ∣[k] slHom (realEmb F) γ = f)
    (hf : IsHolomorphic f) (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hT : ∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), transl β ∈ Γ) {m : ℕ} (hm : 0 < m)
    (hU : ∀ u : (𝓞 F)ˣ, diagU (unitF u ^ m) ∈ Γ) {ν : F}
    (hν : ∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), ∃ n : ℤ, Algebra.trace ℚ F (ν * β) = n)
    {w : InfinitePlace F} (hw : realEmb F w ν < 0) {y : InfinitePlace F → ℝ}
    (hy : ∀ v, 0 < y v) : coeff f (koecherBasis I) (realVec ν) y = 0 := by
  classical
  obtain ⟨u₀, hu₀⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit (K := F) w
  set u : (𝓞 F)ˣ := u₀ ^ m with hudef
  have hpos : ∀ v : InfinitePlace F, 0 < v (u : F) := fun v => NumberField.Units.pos_at_place u v
  have hlog : ∀ v ≠ w, Real.log (v (u : F)) < 0 := by
    intro v hv
    have : (u : F) = (u₀ : F) ^ m := by simp [hudef]
    rw [this, map_pow, Real.log_pow]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hm) (hu₀ v hv)
  have hlt : ∀ v ≠ w, v (u : F) < 1 := fun v hv =>
    (Real.log_neg_iff (hpos v)).mp (hlog v hv)
  have hgt : 1 < w (u : F) := by
    have hsum := NumberField.Units.sum_mult_mul_log u
    have hm1 : ∀ v : InfinitePlace F, (v.mult : ℝ) = 1 := fun v => by
      simp [mult, IsTotallyReal.isReal v]
    simp only [hm1, one_mul] at hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w)] at hsum
    have hne : (Finset.univ.erase w).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]
      omega
    have hneg : ∑ v ∈ Finset.univ.erase w, Real.log (v (u : F)) < 0 := by
      have := Finset.sum_lt_sum_of_nonempty hne (g := fun _ => (0 : ℝ))
        (fun v hv => hlog v (Finset.ne_of_mem_erase hv))
      simpa using this
    exact (Real.log_pos_iff (hpos w).le).mp (by linarith)
  set ε : InfinitePlace F → ℝ := fun v => realEmb F v (u : F) ^ 2 with hεdef
  have hε_eq : ∀ v, ε v = v (u : F) ^ 2 := fun v => by
    show realEmb F v (u : F) ^ 2 = _
    rw [← sq_abs, abs_realEmb]
  have hε : ∀ v, 0 < ε v := fun v => by rw [hε_eq]; exact pow_pos (hpos v) 2
  have hεw : 1 < ε w := by rw [hε_eq]; nlinarith
  have hεv : ∀ v ≠ w, ε v < 1 := fun v hv => by
    rw [hε_eq]; have := hlt v hv; have := hpos v; nlinarith
  have hfε : ∀ x y, (∀ v, 0 < y v) → ‖f (ptXY (ε * x) (ε * y))‖ = ‖f (ptXY x y)‖ := by
    intro x y hy
    have h := norm_slash_diagU k f u (x := x) hy
    have hmem : diagU (unitF u) ∈ Γ := by
      have : unitF u = unitF u₀ ^ m := by simp [hudef, unitF, map_pow]
      rw [this]; exact hU u₀
    rw [hinv _ hmem] at h
    exact h.symm
  exact koecher_coeff_eq_zero hf (isLatticePeriodic_of_transl hinv I hT) (isDual_of_trace I hν)
    hε hfε hw hεw hεv hy

/-! ### $\Gamma_0(\mathfrak N)$ -/

lemma transl_mem_Gamma0 (𝔑 : Ideal (𝓞 F)) {β : F}
    (hβ : β ∈ (1 : FractionalIdeal (𝓞 F)⁰ F)) : transl β ∈ Gamma0 𝔑 := by
  obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hβ
  refine ⟨⟨!![1, r; 0, 1], by simp [det_fin_two_of]⟩, (mem_Gamma0R 𝔑).mpr ?_, ?_⟩
  · change (0 : 𝓞 F) ∈ 𝔑; exact 𝔑.zero_mem
  · ext i j
    change algebraMap (𝓞 F) F (!![1, r; 0, 1] i j) = transl (algebraMap (𝓞 F) F r) i j
    fin_cases i <;> fin_cases j <;> simp

lemma diagU_mem_Gamma0 (𝔑 : Ideal (𝓞 F)) (u : (𝓞 F)ˣ) : diagU (unitF u) ∈ Gamma0 𝔑 := by
  refine ⟨⟨!![(u : 𝓞 F), 0; 0, ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F)], by simp [det_fin_two_of]⟩,
    (mem_Gamma0R 𝔑).mpr ?_, ?_⟩
  · change (0 : 𝓞 F) ∈ 𝔑; exact 𝔑.zero_mem
  · ext i j
    change algebraMap (𝓞 F) F (!![(u : 𝓞 F), 0; 0, ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F)] i j) = diagU (unitF u) i j
    fin_cases i <;> fin_cases j <;> simp [unitF]

/-- **Koecher for $M_k(\Gamma_0(\mathfrak N))$** ($d \ge 2$): for $f$ holomorphic and $\Gamma_0(\mathfrak N)$-invariant (no cusp
condition), the Fourier coefficients for the lattice $\mathcal{O}_F$ vanish at every $\nu \in \mathfrak d^{-1}$ that is nonzero and not
totally positive. -/
theorem koecher_Gamma0 (hd : 2 ≤ Fintype.card (InfinitePlace F)) (𝔑 : Ideal (𝓞 F)) {k : ℤ}
    {f : (InfinitePlace F → ℍ) → ℂ}
    (hinv : ∀ γ ∈ Gamma0 𝔑, f ∣[k] slHom (realEmb F) γ = f) (hf : IsHolomorphic f) {ν : F}
    (hν : ∀ β ∈ (1 : FractionalIdeal (𝓞 F)⁰ F), ∃ n : ℤ, Algebra.trace ℚ F (ν * β) = n)
    (h0 : ν ≠ 0) (hnpos : ¬ ∀ v : InfinitePlace F, 0 < realEmb F v ν)
    {y : InfinitePlace F → ℝ} (hy : ∀ v, 0 < y v) :
    coeff f (koecherBasis 1) (realVec ν) y = 0 := by
  obtain ⟨w, hw⟩ := exists_neg_of_not_totallyPositive h0 hnpos
  exact koecher hd hinv hf 1 (fun β hβ => transl_mem_Gamma0 𝔑 hβ) one_pos
    (fun u => by rw [pow_one]; exact diagU_mem_Gamma0 𝔑 u) (by simpa using hν) hw hy

end QuadFormsKB.HilbertModular
