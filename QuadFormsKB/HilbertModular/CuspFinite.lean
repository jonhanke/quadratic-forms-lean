/-
# Hilbert modular forms: finitely many cusps for $\Gamma(\mathfrak N)$, and reduced cusp vectors

**Cusp vectors.** A cusp $A\infty$ of $\mathrm{SL}_2(F)$ ($A \in \mathrm{SL}_2(F)$) is recorded by the row vector
$x_A = (0, 1)A^{-1} = (-A_{10}, A_{00}) \in F^2\setminus0$, up to $F^\times$; $\gamma A$ has $x_{\gamma A} = x_A\gamma^{-1}$, so
$\Gamma\backslash\mathbb{P}^1(F)$ is the set of $F^\times$-lines in $F^2$ modulo right multiplication by $\Gamma$. The ideal of a vector
is $\mathfrak b(x) = x_0\mathcal{O}_F + x_1\mathcal{O}_F$ (`cuspIdeal`).

**The congruence lemma** (`exists_gammaFullR_rowMul`): if $\mathfrak b(x) = \mathfrak b(x') = \mathfrak b$ and $x' \equiv x \pmod{\mathfrak N\mathfrak b}$
(coordinatewise), then $x' = x\gamma$ for some $\gamma \in \Gamma(\mathfrak N)$. *Proof* (strong approximation for $\mathrm{SL}_2$ in the form
needed): choose $u \in (\mathfrak b^{-1})^2$ with $u_0x_1 - u_1x_0 = 1$ (from $\mathfrak b^{-1}\mathfrak b = \mathcal{O}_F$), correct it by $w \in (\mathfrak N\mathfrak b^{-1})^2$
so that $u'_0x'_1 - u'_1x'_0 = 1$ for $u' = u + w$ (from $(\mathfrak N\mathfrak b^{-1})\mathfrak b = \mathfrak N$), and put
$\gamma = \begin{pmatrix}u_0&u_1\\x_0&x_1\end{pmatrix}^{-1}\begin{pmatrix}u'_0&u'_1\\x'_0&x'_1\end{pmatrix}$; each entry of $\gamma - 1$ is a sum of products
$\mathfrak b\cdot\mathfrak N\mathfrak b^{-1}$ and $\mathfrak b^{-1}\cdot\mathfrak N\mathfrak b$, so lies in $\mathfrak N$.

**Consequences.**
* `finite_image_of_invariant`: a $\Gamma(\mathfrak N)$-invariant function takes finitely many values on
  $\{x : \mathfrak b(x) = \mathfrak b\}$ for a nonzero integral $\mathfrak b$ (it factors through $(\mathcal{O}_F/\mathfrak N\mathfrak b)^2$).
* **Reduced vectors** (`IsRedVec`): fix an integral ideal $\mathfrak b_C$ in each ideal class $C$ (`repIdeal`); $x$ is reduced if
  $\mathfrak b(x) = \mathfrak b_C$ for $C = [\mathfrak b(x)]$. Every nonzero $x$ has a reduced multiple $tx$ (`exists_isRedVec_smul`), unique up to
  $\mathcal{O}_F^\times$ (`isRedVec_smul_unique`).
* **`finite_cusps`** (finiteness): there is a finite set $S$ of nonzero vectors with: every $x \ne 0$ has
  $t x\gamma \in S$ for some $t \in F^\times$, $\gamma \in \Gamma(\mathfrak N)$. Hence $\Gamma(\mathfrak N)\backslash\mathbb{P}^1(F)$ and
  $\Gamma_0(\mathfrak N)\backslash\mathbb{P}^1(F)$ are finite. (The bijection $\mathrm{SL}_2(\mathcal{O}_F)\backslash\mathbb{P}^1(F) \simeq \mathrm{Cl}_F$ is not formalized.)

Sources: Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions* (1971), Lemma 1.38 (the case $\mathbb{Z}$)
[unverified]; Freitag (1990), Ch. I §2 (cusps of Hilbert modular groups) [unverified]; Garrett (1990), Ch. 1 [unverified].
-/
import QuadFormsKB.HilbertModular.CuspClasses

open Matrix NumberField
open scoped MatrixGroups nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### Elements of $I\cdot\mathfrak b(x)$ -/

/-- **Elements of $I\,(\alpha, \gamma)$** are $a\alpha + b\gamma$ with $a, b \in I$. -/
lemma exists_of_mem_mul_cuspIdeal {I : FI} {α γ z : F} (hz : z ∈ I * cuspIdeal α γ) :
    ∃ a ∈ I, ∃ b ∈ I, z = a * α + b * γ := by
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul, cuspIdeal, FractionalIdeal.coe_add,
    FractionalIdeal.coe_spanSingleton, FractionalIdeal.coe_spanSingleton] at hz
  change z ∈ (I : Submodule (𝓞 F) F) * ((𝓞 F) ∙ α ⊔ (𝓞 F) ∙ γ) at hz
  rw [Submodule.mul_sup, Submodule.mem_sup] at hz
  obtain ⟨y, hy, y', hy', rfl⟩ := hz
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_mul_span_singleton.mp hy
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_mul_span_singleton.mp hy'
  exact ⟨a, ha, b, hb, rfl⟩

lemma mem_cuspIdeal_fst (α γ : F) : α ∈ cuspIdeal α γ := mem_cuspIdeal_iff.mpr ⟨1, 0, by simp⟩

lemma mem_cuspIdeal_snd (α γ : F) : γ ∈ cuspIdeal α γ := mem_cuspIdeal_iff.mpr ⟨0, 1, by simp⟩

lemma fi_add_mem {I : FI} {p q : F} (hp : p ∈ I) (hq : q ∈ I) : p + q ∈ I := by
  rw [← FractionalIdeal.mem_coe] at *; exact Submodule.add_mem _ hp hq

lemma fi_sub_mem {I : FI} {p q : F} (hp : p ∈ I) (hq : q ∈ I) : p - q ∈ I := by
  rw [← FractionalIdeal.mem_coe] at *; exact Submodule.sub_mem _ hp hq

lemma fi_neg_mem {I : FI} {p : F} (hp : p ∈ I) : -p ∈ I := by
  rw [← FractionalIdeal.mem_coe] at *; exact Submodule.neg_mem _ hp

/-! ### The congruence lemma -/

/-- **Congruent vectors with the same ideal are $\Gamma(\mathfrak N)$-equivalent**: if $\mathfrak b(x') = \mathfrak b(x) =: \mathfrak b \ne 0$ and
$x'_i - x_i \in \mathfrak N\mathfrak b$ ($i = 0, 1$), then $x' = x\gamma$ for some $\gamma \in \Gamma(\mathfrak N)$ (`rowMul`). -/
@[kb "freitag1990" "Ch. I §2, cusps of Γ(𝔑) (strong approximation for SL₂) [unverified]"]
theorem exists_gammaFullR_rowMul (𝔑 : Ideal (𝓞 F)) {x x' : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0)
    (hid : cuspIdeal x'.1 x'.2 = cuspIdeal x.1 x.2)
    (h1 : x'.1 - x.1 ∈ (𝔑 : FI) * cuspIdeal x.1 x.2) (h2 : x'.2 - x.2 ∈ (𝔑 : FI) * cuspIdeal x.1 x.2) :
    ∃ γ ∈ GammaFullR 𝔑, rowMul x (toF F γ) = x' := by
  set 𝔟 := cuspIdeal x.1 x.2 with h𝔟def
  have h𝔟 : 𝔟 ≠ 0 := cuspIdeal_ne_zero hx
  have hinv : 𝔟⁻¹ * 𝔟 = 1 := inv_mul_cancel₀ h𝔟
  have hN1 : 𝔟⁻¹ * ((𝔑 : FI) * 𝔟) = (𝔑 : FI) := by
    rw [mul_comm, mul_assoc, mul_comm 𝔟, hinv, mul_one]
  have hN2 : 𝔟 * ((𝔑 : FI) * 𝔟⁻¹) = (𝔑 : FI) := by
    rw [mul_comm, mul_assoc, hinv, mul_one]
  have hN3 : ((𝔑 : FI) * 𝔟⁻¹) * 𝔟 = (𝔑 : FI) := by
    rw [mul_assoc, hinv, mul_one]
  have hm1 : ∀ {p q : F}, p ∈ 𝔟⁻¹ → q ∈ (𝔑 : FI) * 𝔟 → p * q ∈ (𝔑 : FI) := fun hp hq => by
    have := FractionalIdeal.mul_mem_mul hp hq; rwa [hN1] at this
  have hm2 : ∀ {p q : F}, p ∈ 𝔟 → q ∈ (𝔑 : FI) * 𝔟⁻¹ → p * q ∈ (𝔑 : FI) := fun hp hq => by
    have := FractionalIdeal.mul_mem_mul hp hq; rwa [hN2] at this
  have hx0 : x.1 ∈ 𝔟 := mem_cuspIdeal_fst _ _
  have hx1 : x.2 ∈ 𝔟 := mem_cuspIdeal_snd _ _
  -- `u ∈ (𝔟⁻¹)²` with `u₀x₁ - u₁x₀ = 1`
  obtain ⟨a, ha, b, hb, hab⟩ := exists_of_mem_mul_cuspIdeal (I := 𝔟⁻¹) (z := 1)
    (by rw [hinv]; exact FractionalIdeal.one_mem_one _)
  have hu₁ : -a ∈ 𝔟⁻¹ := fi_neg_mem ha
  have hdet : b * x.2 - (-a) * x.1 = 1 := by linear_combination -hab
  -- the correction `w ∈ (𝔑𝔟⁻¹)²`
  set e₀ := x'.1 - x.1 with he₀
  set e₁ := x'.2 - x.2 with he₁
  set δ := b * e₁ - (-a) * e₀ with hδdef
  have hδ : -δ ∈ ((𝔑 : FI) * 𝔟⁻¹) * cuspIdeal x'.1 x'.2 := by
    rw [hid, hN3]
    exact fi_neg_mem (fi_sub_mem (hm1 hb h2) (hm1 hu₁ h1))
  obtain ⟨a', ha', b', hb', hab'⟩ := exists_of_mem_mul_cuspIdeal hδ
  have hw₁ : -a' ∈ (𝔑 : FI) * 𝔟⁻¹ := fi_neg_mem ha'
  set v₀ := b + b'
  set v₁ := -a + -a'
  have hdet' : v₀ * x'.2 - v₁ * x'.1 = 1 := by
    simp only [v₀, v₁]
    have hx'1 : x'.1 = x.1 + e₀ := by simp [e₀]
    have hx'2 : x'.2 = x.2 + e₁ := by simp [e₁]
    linear_combination hdet - hab' + 0 * hx'1
  -- the entries of `γ - 1` lie in `𝔑`
  have hb'N : b' ∈ (𝔑 : FI) * 𝔟⁻¹ := hb'
  have m00 : x.2 * b' - (-a) * e₀ ∈ (𝔑 : FI) := fi_sub_mem (hm2 hx1 hb'N) (hm1 hu₁ h1)
  have m01 : x.2 * (-a') - (-a) * e₁ ∈ (𝔑 : FI) := fi_sub_mem (hm2 hx1 hw₁) (hm1 hu₁ h2)
  have m10 : -(x.1 * b') + b * e₀ ∈ (𝔑 : FI) := fi_add_mem (fi_neg_mem (hm2 hx0 hb'N)) (hm1 hb h1)
  have m11 : -(x.1 * (-a')) + b * e₁ ∈ (𝔑 : FI) := fi_add_mem (fi_neg_mem (hm2 hx0 hw₁)) (hm1 hb h2)
  obtain ⟨n00, hn00, e00⟩ := (FractionalIdeal.mem_coeIdeal _).mp m00
  obtain ⟨n01, hn01, e01⟩ := (FractionalIdeal.mem_coeIdeal _).mp m01
  obtain ⟨n10, hn10, e10⟩ := (FractionalIdeal.mem_coeIdeal _).mp m10
  obtain ⟨n11, hn11, e11⟩ := (FractionalIdeal.mem_coeIdeal _).mp m11
  have hx'1 : x'.1 = x.1 + e₀ := by simp [e₀]
  have hx'2 : x'.2 = x.2 + e₁ := by simp [e₁]
  have hdetγ : (1 + n00) * (1 + n11) - n01 * n10 = 1 := by
    apply algebraMap_O_injective
    simp only [map_sub, map_mul, map_add, map_one, e00, e01, e10, e11]
    simp only [v₀, v₁] at hdet'
    rw [hx'1, hx'2] at hdet'
    linear_combination (((b + b') * (x.2 + e₁) + (a + a') * (x.1 + e₀)) - 2 - (b * x.2 + a * x.1 - 1) -
      (x.2 * b' + a * e₀) - (a' * x.1 + b * e₁)) * hdet + hdet'
  set γ : SL(2, 𝓞 F) := ⟨!![1 + n00, n01; n10, 1 + n11], by
    rw [det_fin_two_of]; exact hdetγ⟩ with hγdef
  refine ⟨γ, ?_, ?_⟩
  · rw [GammaFullR, MonoidHom.mem_ker]
    ext i j
    have z00 : Ideal.Quotient.mk 𝔑 n00 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hn00
    have z01 : Ideal.Quotient.mk 𝔑 n01 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hn01
    have z10 : Ideal.Quotient.mk 𝔑 n10 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hn10
    have z11 : Ideal.Quotient.mk 𝔑 n11 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hn11
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    fin_cases i <;> fin_cases j <;> simp [γ, z00, z01, z10, z11]
  · have t00 : toF F γ 0 0 = 1 + algebraMap (𝓞 F) F n00 := by rw [toF_apply]; simp [γ]
    have t01 : toF F γ 0 1 = algebraMap (𝓞 F) F n01 := by rw [toF_apply]; simp [γ]
    have t10 : toF F γ 1 0 = algebraMap (𝓞 F) F n10 := by rw [toF_apply]; simp [γ]
    have t11 : toF F γ 1 1 = 1 + algebraMap (𝓞 F) F n11 := by rw [toF_apply]; simp [γ]
    refine Prod.ext ?_ ?_
    · rw [rowMul_fst, t00, t10, e00, e10, hx'1]
      linear_combination (x'.1 - x.1) * hdet
    · rw [rowMul_snd, t01, t11, e01, e11, hx'2]
      linear_combination (x'.2 - x.2) * hdet

/-! ### Reduction modulo $\mathfrak N\mathfrak b$ -/

open Classical in
/-- A lift $F \to \mathcal{O}_F$ on the image of $\mathcal{O}_F$ (junk value $0$ elsewhere). -/
noncomputable def liftO (y : F) : 𝓞 F := if h : ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = y then h.choose else 0

lemma algebraMap_liftO {y : F} (h : ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = y) :
    algebraMap (𝓞 F) F (liftO y) = y := by
  classical
  rw [liftO, dite_eq_left_of_eq_true (eq_true h)]; exact h.choose_spec

/-- Reduction of a vector modulo an ideal $J$ (through `liftO`). -/
noncomputable def redVec (J : Ideal (𝓞 F)) (x : F × F) : (𝓞 F ⧸ J) × (𝓞 F ⧸ J) :=
  (Ideal.Quotient.mk J (liftO x.1), Ideal.Quotient.mk J (liftO x.2))

lemma exists_of_mem_coeIdeal {𝔟 : Ideal (𝓞 F)} {y : F} (h : y ∈ (𝔟 : FI)) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = y := by
  obtain ⟨a, -, ha⟩ := (FractionalIdeal.mem_coeIdeal _).mp h
  exact ⟨a, ha⟩

lemma ne_zero_of_cuspIdeal_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : 𝔟 ≠ ⊥) {x : F × F}
    (hx : cuspIdeal x.1 x.2 = (𝔟 : FI)) : x.1 ≠ 0 ∨ x.2 ≠ 0 := by
  by_contra h
  push Not at h
  rw [h.1, h.2, cuspIdeal, map_zero, add_zero] at hx
  exact h𝔟 (FractionalIdeal.coeIdeal_eq_zero.mp hx.symm)

/-- **Vectors with ideal $\mathfrak b$ and the same reduction modulo $\mathfrak N\mathfrak b$ are $\Gamma(\mathfrak N)$-equivalent.** -/
theorem exists_gammaFullR_of_redVec_eq (𝔑 : Ideal (𝓞 F)) {𝔟 : Ideal (𝓞 F)} (h𝔟 : 𝔟 ≠ ⊥) {x x' : F × F}
    (hx : cuspIdeal x.1 x.2 = (𝔟 : FI)) (hx' : cuspIdeal x'.1 x'.2 = (𝔟 : FI))
    (hred : redVec (𝔑 * 𝔟) x = redVec (𝔑 * 𝔟) x') :
    ∃ γ ∈ GammaFullR 𝔑, rowMul x (toF F γ) = x' := by
  have hmem : ∀ {y y' : F}, y ∈ (𝔟 : FI) → y' ∈ (𝔟 : FI) →
      Ideal.Quotient.mk (𝔑 * 𝔟) (liftO y) = Ideal.Quotient.mk (𝔑 * 𝔟) (liftO y') →
      y' - y ∈ (𝔑 : FI) * cuspIdeal x.1 x.2 := by
    intro y y' hy hy' he
    rw [hx, ← FractionalIdeal.coeIdeal_mul]
    have h1 : liftO y' - liftO y ∈ 𝔑 * 𝔟 := Ideal.Quotient.eq.mp he.symm
    refine (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, h1, ?_⟩
    rw [map_sub, algebraMap_liftO (exists_of_mem_coeIdeal hy),
      algebraMap_liftO (exists_of_mem_coeIdeal hy')]
  have hx0 : x.1 ∈ (𝔟 : FI) := hx ▸ mem_cuspIdeal_fst _ _
  have hx1 : x.2 ∈ (𝔟 : FI) := hx ▸ mem_cuspIdeal_snd _ _
  have hx'0 : x'.1 ∈ (𝔟 : FI) := hx' ▸ mem_cuspIdeal_fst _ _
  have hx'1 : x'.2 ∈ (𝔟 : FI) := hx' ▸ mem_cuspIdeal_snd _ _
  exact exists_gammaFullR_rowMul 𝔑 (ne_zero_of_cuspIdeal_eq h𝔟 hx) (hx'.trans hx.symm)
    (hmem hx0 hx'0 (congrArg Prod.fst hred)) (hmem hx1 hx'1 (congrArg Prod.snd hred))

lemma finite_quot_ideal {J : Ideal (𝓞 F)} (hJ : J ≠ ⊥) : Finite (𝓞 F ⧸ J) :=
  Ideal.finiteQuotientOfFreeOfNeBot J hJ

/-- **A $\Gamma(\mathfrak N)$-invariant function takes finitely many values on the vectors with ideal $\mathfrak b$**
($\mathfrak N, \mathfrak b \ne 0$ integral): it factors through the reduction modulo $\mathfrak N\mathfrak b$. -/
theorem finite_image_of_invariant {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥) {𝔟 : Ideal (𝓞 F)} (h𝔟 : 𝔟 ≠ ⊥)
    {α : Type*} (W : F × F → α) (hW : ∀ γ ∈ GammaFullR 𝔑, ∀ x, W (rowMul x (toF F γ)) = W x) :
    (W '' {x | cuspIdeal x.1 x.2 = (𝔟 : FI)}).Finite := by
  classical
  set S := {x : F × F | cuspIdeal x.1 x.2 = (𝔟 : FI)}
  have hJ : 𝔑 * 𝔟 ≠ ⊥ := mul_ne_zero h𝔑 h𝔟
  have := finite_quot_ideal hJ
  set ψ : (𝓞 F ⧸ (𝔑 * 𝔟)) × (𝓞 F ⧸ (𝔑 * 𝔟)) → Option α := fun q =>
    if h : ∃ x ∈ S, redVec (𝔑 * 𝔟) x = q then some (W h.choose) else none
  have hfin : (Set.range ψ).Finite := Set.finite_range ψ
  refine (hfin.preimage (Option.some_injective α).injOn).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have h : ∃ y ∈ S, redVec (𝔑 * 𝔟) y = redVec (𝔑 * 𝔟) x := ⟨x, hx, rfl⟩
  refine ⟨redVec (𝔑 * 𝔟) x, ?_⟩
  simp only [ψ]; rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨γ, hγ, hγx⟩ := exists_gammaFullR_of_redVec_eq 𝔑 h𝔟 h.choose_spec.1 hx h.choose_spec.2
  have := hW γ hγ h.choose
  rw [hγx] at this
  exact congrArg some this.symm

/-! ### Reduced vectors: one integral ideal per class -/

/-- **A fixed nonzero integral ideal in each ideal class** $C$ (`ClassGroup.mk0_surjective`). -/
noncomputable def repIdeal (C : ClassGroup (𝓞 F)) : Ideal (𝓞 F) :=
  ((ClassGroup.mk0_surjective C).choose : Ideal (𝓞 F))

lemma repIdeal_mem (C : ClassGroup (𝓞 F)) : repIdeal C ∈ (Ideal (𝓞 F))⁰ :=
  (ClassGroup.mk0_surjective C).choose.2

lemma repIdeal_ne_bot (C : ClassGroup (𝓞 F)) : repIdeal C ≠ ⊥ :=
  nonZeroDivisors.coe_ne_zero ⟨_, repIdeal_mem C⟩

lemma mk0_repIdeal (C : ClassGroup (𝓞 F)) : ClassGroup.mk0 ⟨repIdeal C, repIdeal_mem C⟩ = C :=
  (ClassGroup.mk0_surjective C).choose_spec

/-- **Reduced cusp vectors**: $x \ne 0$ with $\mathfrak b(x) = \mathfrak b_C$, the fixed integral ideal of the class $C = [\mathfrak b(x)]$
(`repIdeal`). In particular $x \in \mathcal{O}_F^2$. -/
def IsRedVec (x : F × F) : Prop :=
  (x.1 ≠ 0 ∨ x.2 ≠ 0) ∧ cuspIdeal x.1 x.2 = (repIdeal (cuspClass x.1 x.2) : FI)

lemma spanSingleton_unit (ε : (𝓞 F)ˣ) : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((ε : 𝓞 F) : F) = 1 := by
  rw [← map_one (FractionalIdeal.spanSingleton (𝓞 F)⁰), FractionalIdeal.spanSingleton_eq_spanSingleton]
  refine ⟨ε⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, ← map_mul, Units.inv_mul, map_one]

lemma cuspIdeal_unit_smul (ε : (𝓞 F)ˣ) (x : F × F) :
    cuspIdeal (ε • x).1 (ε • x).2 = cuspIdeal x.1 x.2 := by
  change cuspIdeal (((ε : 𝓞 F) : F) * x.1) (((ε : 𝓞 F) : F) * x.2) = _
  rw [cuspIdeal_smul, spanSingleton_unit, one_mul]

lemma unit_smul_ne_zero {x : F × F} (h : x.1 ≠ 0 ∨ x.2 ≠ 0) (ε : (𝓞 F)ˣ) :
    (ε • x).1 ≠ 0 ∨ (ε • x).2 ≠ 0 := by
  have hε : ((ε : 𝓞 F) : F) ≠ 0 := (map_ne_zero_iff _ algebraMap_O_injective).mpr ε.ne_zero
  exact h.imp (mul_ne_zero hε) (mul_ne_zero hε)

lemma cuspClass_unit_smul {x : F × F} (h : x.1 ≠ 0 ∨ x.2 ≠ 0) (ε : (𝓞 F)ˣ) :
    cuspClass (ε • x).1 (ε • x).2 = cuspClass x.1 x.2 :=
  cuspClass_smul ((map_ne_zero_iff _ algebraMap_O_injective).mpr ε.ne_zero) h

lemma isRedVec_unit_smul_iff (x : F × F) (ε : (𝓞 F)ˣ) : IsRedVec (ε • x) ↔ IsRedVec x := by
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x.1 ≠ 0 ∨ x.2 ≠ 0 := by
      by_contra hc; push Not at hc
      apply h1.elim <;> intro h <;> apply h <;> simp [Units.smul_def, Algebra.smul_def, hc.1, hc.2]
    refine ⟨hx, ?_⟩
    rw [cuspIdeal_unit_smul, cuspClass_unit_smul hx] at h2
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨unit_smul_ne_zero h1 ε, ?_⟩
    rw [cuspIdeal_unit_smul, cuspClass_unit_smul h1]
    exact h2

/-- Two nonzero fractional ideals in the same class differ by a principal factor: $I = tJ$, $t \in F^\times$. -/
lemma exists_eq_spanSingleton_mul_of_mk_eq {I J : FI} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ClassGroup.mk F (Units.mk0 I hI) = ClassGroup.mk F (Units.mk0 J hJ)) :
    ∃ t : F, t ≠ 0 ∧ I = FractionalIdeal.spanSingleton (𝓞 F)⁰ t * J := by
  have h1 : ClassGroup.mk F (Units.mk0 I hI * (Units.mk0 J hJ)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨t, ht⟩ := (ClassGroup.mk_eq_one_iff.mp h1).principal
  have hIJ : I * J⁻¹ = FractionalIdeal.spanSingleton (𝓞 F)⁰ t := by
    rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton, ← ht]
    simp
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at hIJ
    exact mul_ne_zero hI (inv_ne_zero hJ) hIJ
  refine ⟨t, ht0, ?_⟩
  rw [← hIJ, mul_assoc, inv_mul_cancel₀ hJ, mul_one]

lemma cuspClass_eq_mk0 (C : ClassGroup (𝓞 F)) :
    ClassGroup.mk F (Units.mk0 ((repIdeal C : Ideal (𝓞 F)) : FI)
      (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact repIdeal_ne_bot C)) = C := by
  conv_rhs => rw [← mk0_repIdeal C, ← ClassGroup.mk_mk0 F]
  congr 1

/-- **Every nonzero vector has a reduced multiple** $tx$, $t \in F^\times$. -/
theorem exists_isRedVec_smul {x : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) :
    ∃ t : F, t ≠ 0 ∧ IsRedVec (t * x.1, t * x.2) := by
  set C := cuspClass x.1 x.2
  have hI : ((repIdeal C : Ideal (𝓞 F)) : FI) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact repIdeal_ne_bot C
  have hcl : ClassGroup.mk F (Units.mk0 _ hI) = ClassGroup.mk F (Units.mk0 _ (cuspIdeal_ne_zero hx)) := by
    rw [cuspClass_eq_mk0, ← cuspClass_eq hx]
  obtain ⟨t, ht, he⟩ := exists_eq_spanSingleton_mul_of_mk_eq hI (cuspIdeal_ne_zero hx) hcl
  refine ⟨t, ht, ⟨hx.imp (mul_ne_zero ht) (mul_ne_zero ht), ?_⟩⟩
  rw [cuspClass_smul ht hx, cuspIdeal_smul, ← he]

/-- **The reduced multiple is unique up to units**: if $tx$ and $t'x$ are reduced then $t' = \varepsilon t$, $\varepsilon \in \mathcal{O}_F^\times$. -/
theorem isRedVec_smul_unique {x : F × F} (hx : x.1 ≠ 0 ∨ x.2 ≠ 0) {t t' : F} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (h : IsRedVec (t * x.1, t * x.2)) (h' : IsRedVec (t' * x.1, t' * x.2)) :
    ∃ ε : (𝓞 F)ˣ, ((ε : 𝓞 F) : F) * t = t' := by
  obtain ⟨-, e⟩ := h
  obtain ⟨-, e'⟩ := h'
  simp only at e e'
  rw [cuspClass_smul ht hx] at e
  rw [cuspClass_smul ht' hx] at e'
  rw [cuspIdeal_smul] at e e'
  have : FractionalIdeal.spanSingleton (𝓞 F)⁰ t = FractionalIdeal.spanSingleton (𝓞 F)⁰ t' :=
    mul_right_cancel₀ (cuspIdeal_ne_zero hx) (e.trans e'.symm)
  obtain ⟨ε, hε⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp this
  exact ⟨ε, by rw [← hε, Units.smul_def, Algebra.smul_def]⟩

/-! ### Finitely many cusps -/

/-- **$\Gamma(\mathfrak N)\backslash\mathbb{P}^1(F)$ is finite** (finiteness; $\mathfrak N \ne 0$): there is a finite set $S$ of nonzero row
vectors such that every nonzero $x \in F^2$ satisfies $(tx)\gamma \in S$ for some $t \in F^\times$ and $\gamma \in \Gamma(\mathfrak N)$. In terms of
cusps ($x = (0,1)A^{-1}$ for the cusp $A\infty$): every cusp is $\Gamma(\mathfrak N)$-equivalent to one of the finitely many cusps given by
$S$; as $\Gamma(\mathfrak N) \subseteq \Gamma_1(\mathfrak N) \subseteq \Gamma_0(\mathfrak N)$, the same holds for $\Gamma_1(\mathfrak N)$ and $\Gamma_0(\mathfrak N)$. -/
@[kb "freitag1990" "Ch. I §2, finiteness of the cusps of a congruence subgroup [unverified]"]
theorem finite_cusps {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥) :
    ∃ S : Set (F × F), S.Finite ∧ (∀ s ∈ S, s.1 ≠ 0 ∨ s.2 ≠ 0) ∧
      ∀ x : F × F, (x.1 ≠ 0 ∨ x.2 ≠ 0) → ∃ s ∈ S, ∃ t : F, t ≠ 0 ∧ ∃ γ ∈ GammaFullR 𝔑,
        rowMul (t * x.1, t * x.2) (toF F γ) = s := by
  classical
  set X : ClassGroup (𝓞 F) → Set (F × F) := fun C => {x | cuspIdeal x.1 x.2 = (repIdeal C : FI)}
  set J : ClassGroup (𝓞 F) → Ideal (𝓞 F) := fun C => 𝔑 * repIdeal C
  set ψ : (C : ClassGroup (𝓞 F)) → (𝓞 F ⧸ J C) × (𝓞 F ⧸ J C) → Option (F × F) := fun C q =>
    if h : ∃ x ∈ X C, redVec (J C) x = q then some h.choose else none
  set S : Set (F × F) := {s | ∃ C q, ψ C q = some s}
  have hfin : S.Finite := by
    have : ∀ C, Finite ((𝓞 F ⧸ J C) × (𝓞 F ⧸ J C)) := fun C => by
      have := finite_quot_ideal (mul_ne_zero h𝔑 (repIdeal_ne_bot C)); infer_instance
    have hU : (⋃ C, Set.range (ψ C)).Finite := Set.finite_iUnion fun C => Set.finite_range _
    refine (hU.preimage (Option.some_injective _).injOn).subset ?_
    rintro s ⟨C, q, hq⟩
    exact Set.mem_iUnion.mpr ⟨C, q, hq⟩
  have hS : ∀ C q s, ψ C q = some s → s ∈ X C ∧ redVec (J C) s = q := by
    intro C q s hs
    simp only [ψ] at hs
    split_ifs at hs with h
    · cases hs; exact h.choose_spec
  refine ⟨S, hfin, fun s ⟨C, q, hq⟩ => ne_zero_of_cuspIdeal_eq (repIdeal_ne_bot C) (hS C q s hq).1,
    fun x hx => ?_⟩
  obtain ⟨t, ht, hred⟩ := exists_isRedVec_smul hx
  set C := cuspClass (t * x.1) (t * x.2)
  have hX : (t * x.1, t * x.2) ∈ X C := hred.2
  have hex : ∃ y ∈ X C, redVec (J C) y = redVec (J C) (t * x.1, t * x.2) := ⟨_, hX, rfl⟩
  have hψ : ψ C (redVec (J C) (t * x.1, t * x.2)) = some hex.choose := by
    simp only [ψ]; rw [dite_eq_left_of_eq_true (eq_true hex)]
  refine ⟨hex.choose, ⟨C, _, hψ⟩, t, ht, ?_⟩
  exact exists_gammaFullR_of_redVec_eq 𝔑 (repIdeal_ne_bot C) hX hex.choose_spec.1
    hex.choose_spec.2.symm
