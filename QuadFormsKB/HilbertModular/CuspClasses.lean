/-
# Hilbert modular forms: cusps, their ideal classes, and the constant terms of $E$ and $\theta$ at every cusp

**Cusps.** A cusp of $\mathrm{SL}_2(F)$ is a point $(\alpha : \gamma) \in \mathbb{P}^1(F)$; it is $A\infty$ for
$A = \begin{pmatrix}\alpha&*\\\gamma&*\end{pmatrix} \in \mathrm{SL}_2(F)$, and `cuspMat α γ` is an explicit such $A$
($\begin{pmatrix}\alpha&0\\\gamma&\alpha^{-1}\end{pmatrix}$ if $\alpha \ne 0$, $\begin{pmatrix}0&-\gamma^{-1}\\\gamma&0\end{pmatrix}$ otherwise). So the cusp
conditions of $M_k(\Gamma)$ (a condition for every $A \in \mathrm{SL}_2(F)$) cover every cusp, and the constant term "at
$\alpha/\gamma$" is the limit of $f\,|_k\,\mathrm{cuspMat}\ \alpha\ \gamma$.

**Cusps and ideal classes.** `cuspIdeal α γ` $= \alpha\mathcal{O}_F + \gamma\mathcal{O}_F$. It is unchanged by
$\mathrm{SL}_2(\mathcal{O}_F)$ (`cuspIdeal_SL2O`) and multiplied by $(t)$ under $(\alpha, \gamma) \mapsto (t\alpha, t\gamma)$
(`cuspIdeal_smul`), so its class `cuspClass` $\in \mathrm{Cl}(F)$ is an invariant of the $\mathrm{SL}_2(\mathcal{O}_F)$-orbit of the cusp
(`cuspClass_SL2O`, `cuspClass_smul`). The orbit of $\infty$ has trivial class (`cuspClass_SL2O_infty`): a cusp whose ideal
is not principal is not $\mathrm{SL}_2(\mathcal{O}_F)$-equivalent to $\infty$ (`not_SL2O_infty_of_cuspClass_ne_one`). (The classical
statement that `cuspClass` is a bijection $\mathrm{SL}_2(\mathcal{O}_F)\backslash\mathbb{P}^1(F) \simeq \mathrm{Cl}(F)$ is not needed here and
is not formalized.)

**Constant terms of Eisenstein series at a cusp** (`eisConst_eq_tsum_orbitF`, `eisConst_slashWeight`): for a
unit-equivariant weight,
$$\mathrm{c}_\infty(W_A) = \sum_{t \in U\backslash F}W(-t\gamma, t\alpha)\,N(t)^{-k},\qquad A = \begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix};$$
for $W_\chi$ (level $\mathfrak N$) the sum runs over $t$ in $\mathfrak b_A = \{t : t\alpha \in \mathcal{O}_F,\ t\gamma \in \mathfrak N\}$
(`chiWeight_rowMul_zero`), and for $\mathfrak N = (1)$, $\mathfrak b_A = (\alpha, \gamma)^{-1}$ (`mem_inv_cuspIdeal_iff`): **the constant
term at the cusp $\alpha/\gamma$ is a partial zeta (or $L$-) value of the ideal class of $(\alpha, \gamma)^{-1}$.** This is the
cusps $\leftrightarrow$ ideal classes correspondence as it enters constant terms.

**Constant terms of theta series at a cusp** (`tendsto_thetaQ_slash`): for $Q$ totally positive definite of rank
$n = 2k$ and $A \in \mathrm{SL}_2(F)$ with $\gamma = A_{10} \ne 0$, choose $D \in \mathcal{O}_F\setminus0$ with $a = D\alpha$, $c = D\gamma \in \mathcal{O}_F$
(any common denominator). Then
$$(\theta_Q\,|_k\,A)(z) \longrightarrow K_Q\prod_v\Big(\frac{-i}{2\sigma_v(c)\sigma_v(D)}\Big)^k\,G(a, 0, c),\qquad
  G(a, 0, c) = \sum_{r \in (\mathcal{O}_F/c)^n}e\Big(\operatorname{Tr}\frac{aQ(r)}{c}\Big),$$
$K_Q = (\prod_v\sqrt{\det\sigma_v(A_Q)})^{-1}\Delta(\mathcal{O}_F)^{-n}$ (the constant of `thetaLat_one_cuspPt`); for $\gamma = 0$ the limit is
$N(\alpha)^k$ (`tendsto_thetaQ_slash_of_c_eq_zero`). *Proof:* $Az = \frac ac - \frac{1}{c^2u}$ with $u = (z + \delta/\gamma)/D^2$, the
cusp expansion `thetaLat_one_cuspPt`, and dominated convergence for the dual theta series along
$\min_v\operatorname{Im}u_v \to \infty$ (`tendsto_tsum_thetaTerm_filter`). This is the input needed for the Hecke argument at cusps not equivalent to
$\infty$ under $\mathrm{SL}_2(\mathcal{O}_F)$.

Sources: Shimura (Duke 1978), §2 (cusps) [unverified]; Freitag (1990), Ch. I §2 (cusps and ideal classes) [unverified];
Garrett (1990), Ch. 1 [unverified].
-/
import QuadFormsKB.HilbertModular.EisensteinChar
import QuadFormsKB.HilbertModular.ThetaCharF

open Complex Matrix NumberField UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Matrices moving $\infty$ to a cusp -/

open Classical in
/-- **A matrix moving $\infty$ to the cusp $(\alpha : \gamma)$**: first column $(\alpha, \gamma)$, determinant $1$. For $\alpha \ne 0$ it is
$\begin{pmatrix}\alpha&0\\\gamma&\alpha^{-1}\end{pmatrix}$; for $\alpha = 0 \ne \gamma$ it is $\begin{pmatrix}0&-\gamma^{-1}\\\gamma&0\end{pmatrix}$ (and $1$ for the
non-cusp $(0, 0)$, a junk value). -/
noncomputable def cuspMat (α γ : F) : SL(2, F) :=
  if hα : α = 0 then
    if hγ : γ = 0 then 1 else ⟨!![0, -γ⁻¹; γ, 0], by simp [det_fin_two_of, hγ]⟩
  else ⟨!![α, 0; γ, α⁻¹], by simp [det_fin_two_of, hα]⟩

/-- The first column of `cuspMat α γ` is $(\alpha, \gamma)$, i.e. `cuspMat α γ` maps $\infty$ to $\alpha/\gamma$. -/
theorem cuspMat_col {α γ : F} (h : α ≠ 0 ∨ γ ≠ 0) :
    cuspMat α γ 0 0 = α ∧ cuspMat α γ 1 0 = γ := by
  unfold cuspMat
  by_cases hα : α = 0
  · have hγ : γ ≠ 0 := h.resolve_left (not_not.mpr hα)
    simp only [hα, hγ, ↓reduceDIte]
    simp
  · simp only [hα, ↓reduceDIte]
    simp

/-! ### The ideal of a cusp -/

/-- **The ideal of the cusp $(\alpha : \gamma)$**: $\alpha\mathcal{O}_F + \gamma\mathcal{O}_F$ (a fractional ideal). -/
@[kb "freitag1990" "Ch. I §2, the ideal class of a cusp [unverified]"]
noncomputable def cuspIdeal (α γ : F) : FractionalIdeal (𝓞 F)⁰ F :=
  FractionalIdeal.spanSingleton (𝓞 F)⁰ α + FractionalIdeal.spanSingleton (𝓞 F)⁰ γ

lemma mem_cuspIdeal_iff {α γ x : F} :
    x ∈ cuspIdeal α γ ↔ ∃ r s : 𝓞 F, x = r • α + s • γ := by
  rw [cuspIdeal, FractionalIdeal.mem_add]
  simp only [FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨_, ⟨r, rfl⟩, _, ⟨s, rfl⟩, rfl⟩; exact ⟨r, s, rfl⟩
  · rintro ⟨r, s, rfl⟩; exact ⟨_, ⟨r, rfl⟩, _, ⟨s, rfl⟩, rfl⟩

lemma cuspIdeal_ne_zero {α γ : F} (h : α ≠ 0 ∨ γ ≠ 0) : cuspIdeal α γ ≠ 0 := by
  intro h0
  rcases h with h | h
  · have : α ∈ cuspIdeal α γ := mem_cuspIdeal_iff.mpr ⟨1, 0, by simp⟩
    rw [h0, FractionalIdeal.mem_zero_iff] at this; exact h this
  · have : γ ∈ cuspIdeal α γ := mem_cuspIdeal_iff.mpr ⟨0, 1, by simp⟩
    rw [h0, FractionalIdeal.mem_zero_iff] at this; exact h this

/-- **$\mathrm{SL}_2(\mathcal{O}_F)$-invariance**: for $g \in \mathrm{SL}_2(\mathcal{O}_F)$ the cusp $g(\alpha : \gamma) = (a\alpha + b\gamma : c\alpha + d\gamma)$ has the
same ideal. -/
lemma cuspIdeal_le_of (r00 r01 r10 r11 : 𝓞 F) (α γ : F) :
    cuspIdeal (r00 • α + r01 • γ) (r10 • α + r11 • γ) ≤ cuspIdeal α γ := by
  intro x hx
  obtain ⟨r, s, rfl⟩ := mem_cuspIdeal_iff.mp hx
  refine mem_cuspIdeal_iff.mpr ⟨r * r00 + s * r10, r * r01 + s * r11, ?_⟩
  simp only [Algebra.smul_def, map_add, map_mul]; ring

theorem cuspIdeal_SL2O (g : SL(2, 𝓞 F)) (α γ : F) :
    cuspIdeal (toF F g 0 0 * α + toF F g 0 1 * γ) (toF F g 1 0 * α + toF F g 1 1 * γ) =
      cuspIdeal α γ := by
  have hdet : algebraMap (𝓞 F) F (g 0 0) * algebraMap (𝓞 F) F (g 1 1) -
      algebraMap (𝓞 F) F (g 0 1) * algebraMap (𝓞 F) F (g 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, sl2O_det, map_one]
  refine le_antisymm ?_ ?_
  · have := cuspIdeal_le_of (g 0 0) (g 0 1) (g 1 0) (g 1 1) α γ
    simpa only [Algebra.smul_def, toF_apply] using this
  · set α' := toF F g 0 0 * α + toF F g 0 1 * γ
    set γ' := toF F g 1 0 * α + toF F g 1 1 * γ
    have h1 : α = g 1 1 • α' + (-g 0 1) • γ' := by
      simp only [α', γ', Algebra.smul_def, toF_apply, map_neg]; linear_combination (-α) * hdet
    have h2 : γ = (-g 1 0) • α' + g 0 0 • γ' := by
      simp only [α', γ', Algebra.smul_def, toF_apply, map_neg]; linear_combination (-γ) * hdet
    calc cuspIdeal α γ = cuspIdeal (g 1 1 • α' + (-g 0 1) • γ') ((-g 1 0) • α' + g 0 0 • γ') := by
          rw [← h1, ← h2]
      _ ≤ cuspIdeal α' γ' := cuspIdeal_le_of _ _ _ _ α' γ'

/-- **Scaling**: $(t\alpha, t\gamma)$ has ideal $(t)\cdot(\alpha, \gamma)$. -/
theorem cuspIdeal_smul (t α γ : F) :
    cuspIdeal (t * α) (t * γ) = FractionalIdeal.spanSingleton (𝓞 F)⁰ t * cuspIdeal α γ := by
  rw [cuspIdeal, cuspIdeal, mul_add, FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton]

/-- **The ideal class of a cusp** (the class of $\alpha\mathcal{O}_F + \gamma\mathcal{O}_F$; junk value $1$ at $(0, 0)$). -/
@[kb "freitag1990" "Ch. I §2, cusps ↔ ideal classes [unverified]"]
noncomputable def cuspClass (α γ : F) : ClassGroup (𝓞 F) := by
  classical exact
    if h : α ≠ 0 ∨ γ ≠ 0 then ClassGroup.mk F (Units.mk0 (cuspIdeal α γ) (cuspIdeal_ne_zero h)) else 1

lemma cuspClass_eq {α γ : F} (h : α ≠ 0 ∨ γ ≠ 0) :
    cuspClass α γ = ClassGroup.mk F (Units.mk0 (cuspIdeal α γ) (cuspIdeal_ne_zero h)) := by
  rw [cuspClass]; simp only [h]; rfl

/-- **The class is an invariant of the $\mathrm{SL}_2(\mathcal{O}_F)$-orbit.** -/
theorem cuspClass_SL2O (g : SL(2, 𝓞 F)) {α γ : F} (h : α ≠ 0 ∨ γ ≠ 0)
    (h' : toF F g 0 0 * α + toF F g 0 1 * γ ≠ 0 ∨ toF F g 1 0 * α + toF F g 1 1 * γ ≠ 0) :
    cuspClass (toF F g 0 0 * α + toF F g 0 1 * γ) (toF F g 1 0 * α + toF F g 1 1 * γ) =
      cuspClass α γ := by
  rw [cuspClass_eq h, cuspClass_eq h']
  congr 1
  exact Units.ext (cuspIdeal_SL2O g α γ)

/-- **The class does not change under scaling** $(\alpha, \gamma) \mapsto (t\alpha, t\gamma)$, $t \ne 0$. -/
theorem cuspClass_smul {t : F} (ht : t ≠ 0) {α γ : F} (h : α ≠ 0 ∨ γ ≠ 0) :
    cuspClass (t * α) (t * γ) = cuspClass α γ := by
  have h' : t * α ≠ 0 ∨ t * γ ≠ 0 := h.imp (mul_ne_zero ht) (mul_ne_zero ht)
  rw [cuspClass_eq h, cuspClass_eq h']
  have hS : FractionalIdeal.spanSingleton (𝓞 F)⁰ t ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ht
  have : Units.mk0 (cuspIdeal (t * α) (t * γ)) (cuspIdeal_ne_zero h') =
      Units.mk0 _ hS * Units.mk0 (cuspIdeal α γ) (cuspIdeal_ne_zero h) :=
    Units.ext (by simp [cuspIdeal_smul])
  rw [this, map_mul]
  have h1 : ClassGroup.mk F (Units.mk0 _ hS) = 1 := by
    rw [ClassGroup.mk_eq_one_iff]
    exact ⟨⟨t, by rw [Units.val_mk0, FractionalIdeal.coe_spanSingleton]⟩⟩
  rw [h1, one_mul]

/-- **The cusps $\mathrm{SL}_2(\mathcal{O}_F)\infty$ have trivial class**: for $g \in \mathrm{SL}_2(\mathcal{O}_F)$, $(g_{00}, g_{10})$ generates $\mathcal{O}_F$. -/
theorem cuspClass_SL2O_infty (g : SL(2, 𝓞 F)) : cuspClass (toF F g 0 0) (toF F g 1 0) = 1 := by
  have h10 : (1 : F) ≠ 0 ∨ (0 : F) ≠ 0 := Or.inl one_ne_zero
  have := cuspClass_SL2O g h10
  simp only [mul_one, mul_zero, add_zero] at this
  have hne : toF F g 0 0 ≠ 0 ∨ toF F g 1 0 ≠ 0 := by
    by_contra hc
    push Not at hc
    have hd := sl2O_det g
    have h0 : g 0 0 = 0 := algebraMap_O_injective (by rw [← toF_apply, hc.1, map_zero])
    have h1 : g 1 0 = 0 := algebraMap_O_injective (by rw [← toF_apply, hc.2, map_zero])
    rw [h0, h1] at hd; simp at hd
  rw [this hne, cuspClass_eq h10]
  rw [ClassGroup.mk_eq_one_iff]
  refine ⟨⟨1, ?_⟩⟩
  rw [Units.val_mk0, cuspIdeal, FractionalIdeal.spanSingleton_zero, add_zero,
    FractionalIdeal.coe_spanSingleton]

/-- **A cusp with non-principal ideal is not $\mathrm{SL}_2(\mathcal{O}_F)$-equivalent to $\infty$**: there is no
$g \in \mathrm{SL}_2(\mathcal{O}_F)$ and $t \ne 0$ with $(\alpha, \gamma) = t\,(g_{00}, g_{10})$. -/
theorem not_SL2O_infty_of_cuspClass_ne_one {α γ : F} (hcl : cuspClass α γ ≠ 1) :
    ¬ ∃ g : SL(2, 𝓞 F), ∃ t : F, t ≠ 0 ∧ α = t * toF F g 0 0 ∧ γ = t * toF F g 1 0 := by
  rintro ⟨g, t, ht, rfl, rfl⟩
  apply hcl
  have hne : toF F g 0 0 ≠ 0 ∨ toF F g 1 0 ≠ 0 := by
    by_contra hc
    push Not at hc
    have hd := sl2O_det g
    have h0 : g 0 0 = 0 := algebraMap_O_injective (by rw [← toF_apply, hc.1, map_zero])
    have h1 : g 1 0 = 0 := algebraMap_O_injective (by rw [← toF_apply, hc.2, map_zero])
    rw [h0, h1] at hd; simp at hd
  rw [cuspClass_smul ht hne, cuspClass_SL2O_infty]

/-- **The inverse of the cusp ideal**: $t \in (\alpha, \gamma)^{-1} \iff t\alpha, t\gamma \in \mathcal{O}_F$. -/
theorem mem_inv_cuspIdeal_iff {α γ : F} (h : α ≠ 0 ∨ γ ≠ 0) {t : F} :
    t ∈ (cuspIdeal α γ)⁻¹ ↔ t * α ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) ∧
      t * γ ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [FractionalIdeal.mem_inv_iff (cuspIdeal_ne_zero h)]
  constructor
  · intro H
    exact ⟨H α (mem_cuspIdeal_iff.mpr ⟨1, 0, by simp⟩), H γ (mem_cuspIdeal_iff.mpr ⟨0, 1, by simp⟩)⟩
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨r, s, rfl⟩ := mem_cuspIdeal_iff.mp hy
    have : t * (r • α + s • γ) = r • (t * α) + s • (t * γ) := by
      simp only [Algebra.smul_def]; ring
    rw [this]
    rw [← FractionalIdeal.mem_coe] at h1 h2 ⊢
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

/-! ### Constant terms of Eisenstein series as sums over $U\backslash F$ -/

variable (F) in
/-- **The orbits of $U = \mathcal{O}_F^\times$ on $F$.** -/
abbrev UOrbitF := MulAction.orbitRel.Quotient (𝓞 F)ˣ F

/-- $Ut \mapsto U(0, t)$. -/
noncomputable def zeroRowOrbit : UOrbitF F → UOrbit F :=
  Quotient.map (fun t => ((0 : F), t)) fun a b h => by
    obtain ⟨ε, hε⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    exact orbitRel_iff.mpr ⟨ε, by ext <;> simp [smul_fst, smul_snd, ← hε, unit_smul_eq]⟩

lemma zeroRowOrbit_mk (t : F) : zeroRowOrbit (Quotient.mk _ t : UOrbitF F) = Quotient.mk _ ((0 : F), t) :=
  rfl

lemma zeroRowOrbit_injective : Function.Injective (zeroRowOrbit (F := F)) := by
  intro o o' h
  induction o using Quotient.inductionOn
  induction o' using Quotient.inductionOn
  rename_i a b
  rw [zeroRowOrbit_mk, zeroRowOrbit_mk] at h
  obtain ⟨ε, hε⟩ := orbitRel_iff.mp (Quotient.exact h)
  refine Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨ε, ?_⟩))
  have := (Prod.ext_iff.mp hε).2
  simpa [smul_snd, unit_smul_eq] using this

lemma eisDen_of_fst_eq_zero {x : F × F} (hx : x.1 = 0) (Z : InfinitePlace F → ℂ) :
    eisDen x Z = ∏ v, (realEmb F v x.2 : ℂ) := by
  simp [eisDen, hx]

/-- **The constant term at $\infty$ as a sum over $U\backslash F$**:
$\mathrm{c}_\infty(W) = \sum_{t \in U\backslash F}W(0, t)\,N(t)^{-k}$ for a unit-equivariant weight. -/
theorem eisConst_eq_tsum_orbitF {W : F × F → ℂ} {k : ℤ} (hW : IsUnitEquivariant W k) :
    eisConst W k = ∑' t : UOrbitF F, W ((0 : F), t.out) * (∏ v, (realEmb F v t.out : ℂ)) ^ (-k) := by
  classical
  rw [eisConst]
  set f : UOrbit F → ℂ := fun o => if o.out.1 = 0 then
    W o.out * (∏ v, (realEmb F v o.out.2 : ℂ)) ^ (-k) else 0 with hf
  have hsupp : Function.support f ⊆ Set.range zeroRowOrbit := by
    intro o ho
    have h1 : o.out.1 = 0 := by
      by_contra h; exact ho (by simp only [hf, h, ↓reduceIte])
    refine ⟨Quotient.mk _ o.out.2, ?_⟩
    rw [zeroRowOrbit_mk]
    conv_rhs => rw [← Quotient.out_eq o]
    congr 1
    exact Prod.ext h1.symm rfl
  rw [← zeroRowOrbit_injective.tsum_eq hsupp]
  refine tsum_congr fun t => ?_
  have hout : ((zeroRowOrbit t).out).1 = 0 := by
    obtain ⟨ε, hε⟩ := exists_smul_out ((0 : F), t.out)
    rw [← Quotient.out_eq t, zeroRowOrbit_mk, ← hε]
    simp [smul_fst]
  simp only [hf, hout, ↓reduceIte]
  have e1 : W (zeroRowOrbit t).out * (∏ v, (realEmb F v (zeroRowOrbit t).out.2 : ℂ)) ^ (-k) =
      eisTerm W k (zeroRowOrbit t).out 0 := by
    rw [eisTerm, eisDen_of_fst_eq_zero hout]
  have e2 : W ((0 : F), t.out) * (∏ v, (realEmb F v t.out : ℂ)) ^ (-k) =
      eisTerm W k ((0 : F), t.out) 0 := by
    rw [eisTerm, eisDen_of_fst_eq_zero rfl]
  rw [e1, e2]
  conv_lhs => rw [← Quotient.out_eq t, zeroRowOrbit_mk]
  exact eisTerm_out hW _ _

/-- **The constant term at the cusp $A\infty$ as a sum over $U\backslash F$**: for $A = \begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}$,
$$\mathrm{c}_\infty(W_A) = \sum_{t \in U\backslash F}W(-t\gamma, t\alpha)\,N(t)^{-k},$$
since $(0, t)A^{-1} = (-t\gamma, t\alpha)$. -/
@[kb "freitag1990" "Ch. I §5, constant term at the cusp A∞ [unverified]"]
theorem eisConst_slashWeight {W : F × F → ℂ} {k : ℤ} (hW : IsUnitEquivariant W k) (A : SL(2, F)) :
    eisConst (slashWeight W A) k =
      ∑' t : UOrbitF F, W (-(t.out * A 1 0), t.out * A 0 0) * (∏ v, (realEmb F v t.out : ℂ)) ^ (-k) := by
  rw [eisConst_eq_tsum_orbitF (hW.slashWeight A)]
  refine tsum_congr fun t => ?_
  obtain ⟨i0, -, i2, i3⟩ := sl2_inv_apply A
  simp only [slashWeight, rowMul, i2, i3, zero_mul, zero_add, mul_neg]

/-- **The lattice of the cusp for $W_\chi$**: $W_\chi(-t\gamma, t\alpha) \ne 0$ only if $t\gamma \in \mathfrak N$ and $t\alpha \in \mathcal{O}_F$,
i.e. $t \in \mathfrak b_A = \gamma^{-1}\mathfrak N \cap \alpha^{-1}\mathcal{O}_F$; then the value is $\chi(t\alpha)^{-1}$. For $\mathfrak N = (1)$,
$\mathfrak b_A = (\alpha, \gamma)^{-1}$ (`mem_inv_cuspIdeal_iff`). -/
theorem chiWeight_rowMul_zero {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ} {t α γ : F}
    (h : chiWeight 𝔑 χ (-(t * γ), t * α) ≠ 0) :
    (∃ c ∈ 𝔑, algebraMap (𝓞 F) F c = t * γ) ∧ ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = t * α ∧
      chiWeight 𝔑 χ (-(t * γ), t * α) = (χ (Ideal.Quotient.mk 𝔑 d))⁻¹ := by
  by_cases hl : InLevel 𝔑 (-(t * γ), t * α)
  · obtain ⟨p, hp, hpx⟩ := hl
    have h1 := (Prod.ext_iff.mp hpx).1
    have h2 := (Prod.ext_iff.mp hpx).2
    refine ⟨⟨-p.1, 𝔑.neg_mem hp, by simp only [map_neg] at h1 ⊢; rw [h1]; ring⟩, p.2, h2, ?_⟩
    rw [← hpx, chiWeight_coe hp]
  · exact absurd (chiWeight_of_not hl) h

/-! ### Theta series: the constant term at every cusp -/

variable {n : ℕ}

/-- **Dominated convergence for theta-type series along any filter** on which $\operatorname{Im}w_v \to \infty$ for every $v$:
$\sum_{x\in S}e(\sum_v\sigma_v(Q(x))w_v)\,g(x) \to g(0)$, for $Q$ totally positive definite and $g$ bounded. (Generalizes
`tendsto_tsum_thetaTerm`, which is the ray $w_v = it$.) -/
theorem tendsto_tsum_thetaTerm_filter {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    {S : Set (Fin n → F)} (h0 : (0 : Fin n → F) ∈ S)
    (hsum : Summable fun x : S => ‖thetaTerm A x (fun _ => Complex.I)‖) (g : S → ℂ) {B : ℝ}
    (hg : ∀ x, ‖g x‖ ≤ B) {α : Type*} {l : Filter α} (w : α → InfinitePlace F → ℂ)
    (hw : ∀ v, Tendsto (fun a => (w a v).im) l atTop) :
    Tendsto (fun a => ∑' x : S, thetaTerm A x (w a) * g x) l (𝓝 (g ⟨0, h0⟩)) := by
  classical
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hev : ∀ᶠ a in l, ∀ v, 1 ≤ (w a v).im :=
    eventually_all.mpr fun v => (hw v).eventually (eventually_ge_atTop 1)
  have hlim : ∀ x : S, Tendsto (fun a => thetaTerm A x (w a) * g x) l
      (𝓝 (if x = ⟨0, h0⟩ then g ⟨0, h0⟩ else 0)) := by
    intro x
    by_cases hx : x = ⟨0, h0⟩
    · subst hx
      simp only [↓reduceIte]
      have : ∀ a, thetaTerm A ((⟨0, h0⟩ : S) : Fin n → F) (w a) = 1 := by
        intro a; simp [thetaTerm, qv]
      simp_rw [this, one_mul]
      exact tendsto_const_nhds
    · simp only [hx, ↓reduceIte]
      have hx' : (x : Fin n → F) ≠ 0 := fun h => hx (Subtype.ext h)
      rw [show (0 : ℂ) = 0 * g x by ring]
      refine Tendsto.mul_const _ ?_
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hq0 : 0 < realEmb F v₀ (qv A x) := realEmb_qv_pos hA hx' v₀
      have hT : Tendsto (fun a => Real.exp (-(2 * Real.pi * realEmb F v₀ (qv A x)) * (w a v₀).im)) l
          (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          ((hw v₀).const_mul_atTop_of_neg (by nlinarith [Real.pi_pos]))
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hT
      filter_upwards [hev] with a ha
      rw [norm_thetaTerm, Real.exp_le_exp]
      have hle : realEmb F v₀ (qv A x) * (w a v₀).im ≤ ∑ v, realEmb F v (qv A x) * (w a v).im :=
        Finset.single_le_sum (f := fun v => realEmb F v (qv A x) * (w a v).im)
          (fun v _ => mul_nonneg (qv_nonneg hA v x) (zero_le_one.trans (ha v))) (Finset.mem_univ v₀)
      nlinarith [Real.pi_pos]
  have hbound : ∀ᶠ a in l, ∀ x : S,
      ‖thetaTerm A x (w a) * g x‖ ≤ ‖thetaTerm A x (fun _ => Complex.I)‖ * B := by
    filter_upwards [hev] with a ha x
    rw [norm_mul]
    exact mul_le_mul (norm_thetaTerm_le hA _ fun v => by simpa using ha v) (hg x) (norm_nonneg _)
      (norm_nonneg _)
  have h := tendsto_tsum_of_dominated_convergence (hsum.mul_right B) hlim hbound
  rwa [tsum_ite_eq] at h

lemma zero_mem_latSet_one : (0 : Fin n → F) ∈ latSet (oneIdeals (F := F) (n := n)) :=
  fun i => by simp

lemma tendsto_im_atImInftyPi (v : InfinitePlace F) :
    Tendsto (fun z : InfinitePlace F → ℍ => (z v).im) atImInftyPi atTop :=
  tendsto_comap.mono_left (iInf_le _ v)

/-- **$\theta_Q \to 1$ at $\infty$** (the constant term $r_Q(0) = 1$), along $\min_v\operatorname{Im}z_v \to \infty$. -/
theorem tendsto_thetaQ_atImInfty {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) :
    Tendsto (thetaQ Q) atImInftyPi (𝓝 1) := by
  have h := tendsto_tsum_thetaTerm_filter hQ zero_mem_latSet_one
    (summable_norm_thetaTerm_latSet hQ oneIdeals (z := fun _ => Complex.I) fun _ => by simp)
    (fun _ => (1 : ℂ)) (B := 1) (fun _ => by simp) (l := atImInftyPi)
    (fun z v => ((z v : ℍ) : ℂ)) fun v => by simpa using tendsto_im_atImInftyPi v
  simp only [mul_one] at h
  refine h.congr fun z => ?_
  rw [thetaQ_eq_thetaLatH, thetaLatH, thetaLat_eq_tsum_latSet]

/-- **The constant term of $\theta_Q$ at a cusp $A\infty$ with $A_{10} = 0$**: $\theta_Q\,|_k\,A \to N(A_{00})^k$. -/
theorem tendsto_thetaQ_slash_of_c_eq_zero {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (k : ℤ) (A : SL(2, F)) (hc : A 1 0 = 0) :
    Tendsto (thetaQ Q ∣[k] slHom (realEmb F) A) atImInftyPi
      (𝓝 ((∏ v, (realEmb F v (A 0 0) : ℂ)) ^ k)) := by
  have hdet := sl2_det A
  rw [hc, mul_zero, sub_zero] at hdet
  have hd : ∀ v, realEmb F v (A 1 1) ≠ 0 := fun v h => by
    have := congrArg (realEmb F v) hdet; rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  have hfac : ∀ z : InfinitePlace F → ℍ, ∏ v, ((((slHom (realEmb F) A v : GL(2, ℝ)⁺) :
      GL (Fin 2) ℝ).det.val ^ (k - 1) : ℝ) : ℂ) *
      denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ (-k) =
      (∏ v, (realEmb F v (A 0 0) : ℂ)) ^ k := by
    intro z
    have hprod : (∏ v, (realEmb F v (A 0 0) : ℂ)) * ∏ v, (realEmb F v (A 1 1) : ℂ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [← ofReal_mul, ← map_mul, hdet, map_one, ofReal_one]
    have : ∀ v, ((((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^ (k - 1) : ℝ) : ℂ) *
        denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ (-k) =
        ((realEmb F v (A 1 1) : ℂ)) ^ (-k) := by
      intro v
      rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul]
      simp [denom, hc]
    simp_rw [this]
    rw [Finset.prod_zpow, _root_.zpow_neg, ← _root_.inv_zpow, ← eq_inv_of_mul_eq_one_left hprod]
  have him : ∀ v, Tendsto (fun z : InfinitePlace F → ℍ =>
      ((slHom (realEmb F) A • z) v : ℍ).im) atImInftyPi atTop := by
    intro v
    have heq : ∀ z : InfinitePlace F → ℍ, ((slHom (realEmb F) A • z) v : ℍ).im =
        (z v).im / (realEmb F v (A 1 1)) ^ 2 := by
      intro z
      rw [Pi.smul_apply', glPos_smul_eq, UpperHalfPlane.im_smul_eq_div_normSq,
        GeneralLinearGroup.val_det_apply]
      have hdet1 := slHom_det (realEmb F) A v
      rw [GeneralLinearGroup.val_det_apply] at hdet1
      rw [hdet1, abs_one, one_mul]
      congr 1
      simp [denom, hc, Complex.normSq_ofReal, sq]
    simp_rw [heq]
    exact (tendsto_im_atImInftyPi v).atTop_div_const (pow_pos (lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (hd v)))) 1 |>.trans_eq (pow_one _))
  have hθ : Tendsto (fun z => thetaQ Q (slHom (realEmb F) A • z)) atImInftyPi (𝓝 1) := by
    refine (tendsto_thetaQ_atImInfty hQ).comp ?_
    exact tendsto_iInf.mpr fun v => tendsto_comap_iff.mpr (him v)
  have := hθ.mul_const ((∏ v, (realEmb F v (A 0 0) : ℂ)) ^ k)
  rw [one_mul] at this
  refine this.congr fun z => ?_
  rw [slash_apply, hfac]

lemma zero_mem_dualSet_one : (0 : Fin n → F) ∈ dualSet (oneIdeals (F := F) (n := n)) :=
  fun i => by
    have := (Submodule.zero_mem _ : (0 : F) ∈
      ((FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) :
        Submodule (𝓞 F) F))
    exact this

lemma norm_gaussSumF_le (Q : QuadForm (𝓞 F) n) (a : 𝓞 F) {c : 𝓞 F} (hc : c ≠ 0) (μ : Fin n → F) :
    ‖gaussSumF Q a c μ‖ ≤ Nat.card (Fin n → 𝓞 F ⧸ Ideal.span {c}) := by
  have : Finite (𝓞 F ⧸ Ideal.span {c}) := finite_quot_span hc
  let _ := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {c})
  rw [gaussSumF_eq_sum, Nat.card_eq_fintype_card]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  rw [Finset.card_univ.symm, Finset.cast_card]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [gsTermF, show (2 : ℂ) * Real.pi * Complex.I * (((Algebra.trace ℚ F _ : ℚ) : ℂ)) =
      ((2 * Real.pi * ((Algebra.trace ℚ F ((algebraMap (𝓞 F) F a * qv (gramF Q)
        (vecO fun i => qlift (r i)) + μ ⬝ᵥ vecO fun i => qlift (r i)) / algebraMap (𝓞 F) F c) : ℚ) : ℝ) : ℝ) : ℂ) *
        Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The constant of the theta series at a cusp**:
$K_Q\prod_v\big(\frac{-i}{2\sigma_v(c)\sigma_v(D)}\big)^k$ with $K_Q = (\prod_v\sqrt{\det\sigma_v(A_Q)})^{-1}\prod_i\Delta(\mathcal{O}_F)^{-1}$
(`embDet` of $\mathcal{O}_F$ is $\sqrt{d_F}$). Parameters: $k$ (half the rank), $D$ (the common denominator), $c = D\gamma$. -/
noncomputable def thetaCuspConst (Q : QuadForm (𝓞 F) n) (k : ℕ) (D c : 𝓞 F) : ℂ :=
  (((∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ *
      (∏ i : Fin n, embDet (oneIdeals (F := F) i))⁻¹ : ℝ) : ℂ) *
    ∏ v, (-Complex.I / (2 * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) *
      (realEmb F v (algebraMap (𝓞 F) F D) : ℂ))) ^ k

/-- **The constant term of $\theta_Q$ at every cusp $A\infty$, $A_{10} \ne 0$** (rank $n = 2k$): for any $D \in \mathcal{O}_F \setminus 0$
with $a = DA_{00}$, $c = DA_{10}$ in $\mathcal{O}_F$,
$$(\theta_Q\,|_k\,A)(z) \longrightarrow K_Q\prod_v\Big(\frac{-i}{2\sigma_v(c)\sigma_v(D)}\Big)^k\,G(a, 0, c)
  \qquad(\min_v\operatorname{Im}z_v \to \infty),$$
$G(a, 0, c) = \sum_{r\in(\mathcal{O}_F/c)^n}e(\operatorname{Tr}\frac{aQ(r)}{c})$ (`gaussSumF`). For $A \in \mathrm{SL}_2(\mathcal{O}_F)$ take $D = 1$:
the constant is the theta multiplier `thetaMultF Q k a c`. -/
@[kb "iwaniec1997" "§10.4, constant term of θ at a cusp [unverified]"]
theorem tendsto_thetaQ_slash {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) (A : SL(2, F)) (hA : A 1 0 ≠ 0) {D a c : 𝓞 F} (hD : D ≠ 0)
    (ha : algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F D * A 0 0)
    (hcD : algebraMap (𝓞 F) F c = algebraMap (𝓞 F) F D * A 1 0) :
    Tendsto (thetaQ Q ∣[(k : ℤ)] slHom (realEmb F) A) atImInftyPi
      (𝓝 (thetaCuspConst Q k D c * gaussSumF Q a c 0)) := by
  have hDF : algebraMap (𝓞 F) F D ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ algebraMap_O_injective]
  have hcF : algebraMap (𝓞 F) F c ≠ 0 := by rw [hcD]; exact mul_ne_zero hDF hA
  have hc : c ≠ 0 := fun h => hcF (by rw [h, map_zero])
  set σ : InfinitePlace F → F → ℂ := fun v x => (realEmb F v x : ℂ) with hσ
  have hσne : ∀ v {x : F}, x ≠ 0 → σ v x ≠ 0 := fun v x hx => by
    simp only [hσ, ofReal_ne_zero]; exact (map_ne_zero_iff _ (realEmb_injective F v)).mpr hx
  have hσD : ∀ v, σ v (algebraMap (𝓞 F) F D) ≠ 0 := fun v => hσne v hDF
  have hσA : ∀ v, σ v (A 1 0) ≠ 0 := fun v => hσne v hA
  have hD' : ∀ v, ((realEmb F v (algebraMap (𝓞 F) F D) : ℝ) : ℂ) ≠ 0 := hσD
  have hA' : ∀ v, ((realEmb F v (A 1 0) : ℝ) : ℂ) ≠ 0 := hσA
  -- the variable at the cusp
  set u : (InfinitePlace F → ℍ) → InfinitePlace F → ℂ := fun z v =>
    ((z v : ℂ) + σ v (A 1 1) / σ v (A 1 0)) / σ v (algebraMap (𝓞 F) F D) ^ 2 with hu
  have hDsq : ∀ v, 0 < (realEmb F v (algebraMap (𝓞 F) F D)) ^ 2 := fun v =>
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ((map_ne_zero_iff _ (realEmb_injective F v)).mpr hDF)))
  have huim : ∀ z v, (u z v).im = (z v).im / (realEmb F v (algebraMap (𝓞 F) F D)) ^ 2 := by
    intro z v
    simp only [hu, hσ]
    rw [← ofReal_pow, div_ofReal_im]
    simp
  have hupos : ∀ z v, 0 < (u z v).im := fun z v => by rw [huim]; exact div_pos (z v).im_pos (hDsq v)
  -- the point `Az` is `cuspPt a c u`
  have hdetA := sl2_det A
  have hpt : ∀ z : InfinitePlace F → ℍ, (fun v => (((slHom (realEmb F) A • z) v : ℍ) : ℂ)) =
      cuspPt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F c) (u z) := by
    intro z
    funext v
    have hden := denom_ne_zero ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)
    have hdetv : σ v (A 0 0) * σ v (A 1 1) - σ v (A 0 1) * σ v (A 1 0) = 1 := by
      simp only [hσ]; rw [← ofReal_mul, ← ofReal_mul, ← ofReal_sub, ← map_mul, ← map_mul, ← map_sub,
        hdetA, map_one, ofReal_one]
    rw [Pi.smul_apply', glPos_smul_eq, coe_smul_of_det_pos (det_glPos_pos _)]
    simp only [num, denom, slHom_apply_coe] at hden ⊢
    rw [cuspPt, ha, hcD, show (algebraMap (𝓞 F) F D * A 0 0) / (algebraMap (𝓞 F) F D * A 1 0) =
      A 0 0 / A 1 0 by field_simp]
    have key := cusp_identity (σ v (A 0 0)) (σ v (A 0 1)) (σ v (A 1 0)) (σ v (A 1 1)) (z v)
      (hσA v) hden hdetv
    simp only [hσ] at key
    rw [key, map_div₀, ofReal_div, map_mul, ofReal_mul]
    congr 2
    simp only [hu, hσ]
    field_simp [hD' v, hA' v]
  -- the expansion
  have hexp : ∀ z : InfinitePlace F → ℍ, (thetaQ Q ∣[(k : ℤ)] slHom (realEmb F) A) z =
      ((((∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ *
        (∏ i : Fin n, embDet (oneIdeals (F := F) i))⁻¹ : ℝ) : ℂ) *
        ∏ v, (-Complex.I / (2 * σ v (algebraMap (𝓞 F) F c) * σ v (algebraMap (𝓞 F) F D))) ^ k) *
      ∑' μ : dualSet (oneIdeals (F := F) (n := n)),
        thetaTerm ((1 / 4 : F) • (gramF Q)⁻¹) μ (u z) * gaussSumF Q a c μ := by
    intro z
    rw [slash_apply, thetaQ_eq_thetaLatH, thetaLatH, hpt z, thetaLat_one_cuspPt hQ a hc (hupos z)]
    have hfac : ∀ v, ((((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^ ((k : ℤ) - 1) : ℝ) : ℂ) *
        denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ (-(k : ℤ)) =
        ((σ v (A 1 0) * σ v (algebraMap (𝓞 F) F D) ^ 2 * u z v) ^ k)⁻¹ := by
      intro v
      rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul, _root_.zpow_neg, zpow_natCast]
      congr 2
      simp only [denom, slHom_apply_coe, hu, hσ]
      field_simp [hD' v, hA' v]
    simp_rw [hfac]
    have hcp : ∀ v, (-Complex.I * u z v / 2) ^ ((n : ℂ) / 2) = (-Complex.I * u z v / 2) ^ k := by
      intro v
      rw [show ((n : ℂ) / 2) = ((k : ℕ) : ℂ) by rw [hn]; push_cast; ring, Complex.cpow_natCast]
    simp_rw [hcp]
    have hune : ∀ v, u z v ≠ 0 := fun v h => by have := hupos z v; rw [h] at this; simp at this
    have hprod : (∏ v, (-Complex.I * u z v / 2) ^ k) *
        ∏ v, ((σ v (A 1 0) * σ v (algebraMap (𝓞 F) F D) ^ 2 * u z v) ^ k)⁻¹ =
        ∏ v, (-Complex.I / (2 * σ v (algebraMap (𝓞 F) F c) * σ v (algebraMap (𝓞 F) F D))) ^ k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [← inv_pow, ← mul_pow]
      congr 1
      simp only [hσ]
      rw [hcD, map_mul, ofReal_mul]
      field_simp [hune v, hD' v, hA' v]
    rw [← hprod]
    ring
  -- the limit
  have hlim := tendsto_tsum_thetaTerm_filter (isTotPosGram_dual hQ) zero_mem_dualSet_one
    (summable_norm_thetaTerm_dualSet hQ oneIdeals (z := fun _ => Complex.I) fun _ => by simp)
    (fun μ => gaussSumF Q a c μ) (fun μ => norm_gaussSumF_le Q a hc μ) (l := atImInftyPi) u
    (fun v => by simp_rw [huim]; exact (tendsto_im_atImInftyPi v).atTop_div_const (hDsq v))
  have := hlim.const_mul ((((∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ *
        (∏ i : Fin n, embDet (oneIdeals (F := F) i))⁻¹ : ℝ) : ℂ) *
        ∏ v, (-Complex.I / (2 * σ v (algebraMap (𝓞 F) F c) * σ v (algebraMap (𝓞 F) F D))) ^ k)
  refine (this.congr fun z => (hexp z).symm).trans_eq ?_
  · simp [thetaCuspConst, hσ]

end QuadFormsKB.HilbertModular
