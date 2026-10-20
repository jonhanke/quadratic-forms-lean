/-
# Hilbert Eisenstein series I: series over pairs modulo units, and the transformation law

Let $F$ be a totally real field of degree $d$, $\mathcal{O} = \mathcal{O}_F$, $U = \mathcal{O}^\times$, and $\sigma_v$ ($v \in \iota$, the $d$ real
places) the real embeddings (`realEmb F v`). For a pair $x = (c, d) \in F \times F$ and $Z \in \mathbb{C}^\iota$ put
$$N(cZ + d) = \prod_{v}\big(\sigma_v(c)Z_v + \sigma_v(d)\big) \qquad (\texttt{eisDen}\ x\ Z).$$

**The series.** For a weight $W : F \times F \to \mathbb{C}$ and $k \in \mathbb{Z}$,
$$E_{W,k}(z) = \sum_{x \in U\backslash (F\times F)} W(x)\,N(cz + d)^{-k} \qquad (\texttt{eisSeries}\ W\ k),$$
the sum over the orbits of $U$ acting diagonally, $\varepsilon\cdot(c, d) = (\varepsilon c, \varepsilon d)$ (`UOrbit F`). Each orbit
contributes the term of its representative `Quotient.out`; under the **unit equivariance**
$$W(\varepsilon x) = N(\varepsilon)^k\,W(x), \qquad N(\varepsilon) = \prod_v\sigma_v(\varepsilon) = \pm1 \qquad (\texttt{IsUnitEquivariant}),$$
the term $W(x)N(cz+d)^{-k}$ is constant on orbits (`eisTerm_smul`), so the choice is immaterial (`eisTerm_out`). The orbit
$\{0\}$ contributes $0$ when $k \ne 0$ ($0^{-k} = 0$ in Lean).

This is the shape of Shimura's series (Duke 1978, (3.4)–(3.5) [unverified]) and Garrett (1990), Ch. 3 [unverified]:
summing over pairs *modulo units* is forced for $d \ge 2$, because $|N(\varepsilon cz + \varepsilon d)| = |N(cz+d)|$ and $U$ is
infinite. A classical Eisenstein series of level $\mathfrak N$ with character is the case
$W(c, d) = \chi(d)^{-1}\mathbf 1_{\mathfrak N}(c)\mathbf 1_{\mathcal O}(d)$ (`EisensteinChar.lean`); taking $W$ supported on
$\mathfrak b\mathfrak N \times \mathfrak b$ gives the other ideal-class components. *Convention:* the row $(c, d)$ is the bottom row of
a matrix, as in $j(\gamma, z) = cz + d$.

**The transformation law** (`eisSeries_slash`): for every $A \in \mathrm{SL}_2(F)$,
$$E_{W,k}\,|_k\,A = E_{W_A,k}, \qquad W_A(y) = W(yA^{-1}),$$
where $xA$ is the row vector times the matrix (`rowMul`). It is a reindexing of the orbit sum by $x \mapsto xA$
(`orbitMulEquiv`) together with $N\big(c(Az) + d\big)\prod_v j(A_v, z_v) = N\big((xA)_0z + (xA)_1\big)$ (`eisDen_smul_mul`), and
holds as an identity of `tsum`s with no convergence hypothesis. Convergence, holomorphy and the behaviour at the cusps are
in `EisensteinConv.lean`.
-/
import QuadFormsKB.HilbertModular.KoecherCusps

open Complex Matrix NumberField UpperHalfPlane
open scoped MatrixGroups ModularForm

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Row vectors times matrices -/

/-- **Row vector times matrix**: $xA = (x_0A_{00} + x_1A_{10},\ x_0A_{01} + x_1A_{11})$ for $x = (x_0, x_1) \in F^2$ and
$A \in \mathrm{SL}_2(F)$ (0-based entries). -/
def rowMul (x : F × F) (A : SL(2, F)) : F × F :=
  (x.1 * A 0 0 + x.2 * A 1 0, x.1 * A 0 1 + x.2 * A 1 1)

@[simp] lemma rowMul_fst (x : F × F) (A : SL(2, F)) : (rowMul x A).1 = x.1 * A 0 0 + x.2 * A 1 0 := rfl
@[simp] lemma rowMul_snd (x : F × F) (A : SL(2, F)) : (rowMul x A).2 = x.1 * A 0 1 + x.2 * A 1 1 := rfl

lemma rowMul_mul (x : F × F) (A B : SL(2, F)) : rowMul x (A * B) = rowMul (rowMul x A) B := by
  simp only [rowMul]
  ext <;> simp [mul_apply, Fin.sum_univ_two] <;> ring

@[simp] lemma rowMul_one (x : F × F) : rowMul x 1 = x := by
  simp [rowMul]

lemma rowMul_rowMul_inv (x : F × F) (A : SL(2, F)) : rowMul (rowMul x A) A⁻¹ = x := by
  rw [← rowMul_mul, mul_inv_cancel, rowMul_one]

lemma rowMul_inv_rowMul (x : F × F) (A : SL(2, F)) : rowMul (rowMul x A⁻¹) A = x := by
  rw [← rowMul_mul, inv_mul_cancel, rowMul_one]

/-- $x \mapsto xA$ as a bijection of $F^2$. -/
def rowMulEquiv (A : SL(2, F)) : F × F ≃ F × F where
  toFun x := rowMul x A
  invFun x := rowMul x A⁻¹
  left_inv x := rowMul_rowMul_inv x A
  right_inv x := rowMul_inv_rowMul x A

lemma rowMul_smul (ε : (𝓞 F)ˣ) (x : F × F) (A : SL(2, F)) :
    rowMul (ε • x) A = ε • rowMul x A := by
  change rowMul ((ε : F) * x.1, (ε : F) * x.2) A = ((ε : F) * (rowMul x A).1, (ε : F) * (rowMul x A).2)
  simp only [rowMul]
  ext <;> simp <;> ring

lemma smul_fst (ε : (𝓞 F)ˣ) (x : F × F) : (ε • x).1 = (ε : F) * x.1 := rfl
lemma smul_snd (ε : (𝓞 F)ˣ) (x : F × F) : (ε • x).2 = (ε : F) * x.2 := rfl

/-! ### Orbits of the units -/

variable (F) in
/-- **The orbits of $U = \mathcal{O}_F^\times$ on $F^2$**, acting by $\varepsilon\cdot(c, d) = (\varepsilon c, \varepsilon d)$. -/
abbrev UOrbit := MulAction.orbitRel.Quotient (𝓞 F)ˣ (F × F)

lemma orbitRel_iff {x y : F × F} :
    MulAction.orbitRel (𝓞 F)ˣ (F × F) x y ↔ ∃ ε : (𝓞 F)ˣ, ε • y = x := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

lemma exists_smul_out (x : F × F) :
    ∃ ε : (𝓞 F)ˣ, ε • x = (Quotient.mk _ x : UOrbit F).out := by
  have : MulAction.orbitRel (𝓞 F)ˣ (F × F) (Quotient.mk _ x : UOrbit F).out x :=
    Quotient.mk_out (s := MulAction.orbitRel (𝓞 F)ˣ (F × F)) x
  exact orbitRel_iff.mp this

/-- **Right multiplication by $A$ on orbits**: $Ux \mapsto U(xA)$ (well defined since $(\varepsilon x)A = \varepsilon(xA)$). -/
noncomputable def orbitMulEquiv (A : SL(2, F)) : UOrbit F ≃ UOrbit F :=
  Quotient.congr (rowMulEquiv A) fun a b => by
    simp only [rowMulEquiv, Equiv.coe_fn_mk, orbitRel_iff]
    constructor
    · rintro ⟨ε, rfl⟩; exact ⟨ε, (rowMul_smul ε b A).symm⟩
    · rintro ⟨ε, hε⟩
      refine ⟨ε, ?_⟩
      have := congrArg (fun y => rowMul y A⁻¹) hε
      simpa only [← rowMul_smul, rowMul_rowMul_inv] using this

lemma orbitMulEquiv_mk (A : SL(2, F)) (x : F × F) :
    orbitMulEquiv A (Quotient.mk _ x) = Quotient.mk _ (rowMul x A) := rfl

/-! ### Norms and the summand -/

/-- **The norm of $cZ + d$**: $N(cZ + d) = \prod_v\big(\sigma_v(c)Z_v + \sigma_v(d)\big)$ for $x = (c, d) \in F^2$ and $Z \in \mathbb{C}^\iota$. -/
noncomputable def eisDen (x : F × F) (Z : InfinitePlace F → ℂ) : ℂ :=
  ∏ v, ((realEmb F v x.1 : ℂ) * Z v + (realEmb F v x.2 : ℂ))

/-- **The norm of a unit**, $N(\varepsilon) = \prod_v\sigma_v(\varepsilon) \in \{\pm1\}$. -/
noncomputable def unitNorm (ε : (𝓞 F)ˣ) : ℝ := ∏ v, realEmb F v (ε : F)

lemma abs_unitNorm (ε : (𝓞 F)ˣ) : |unitNorm ε| = 1 := by
  rw [unitNorm, Finset.abs_prod]
  simp_rw [abs_realEmb]
  exact prod_place_unit ε

lemma unitNorm_ne_zero (ε : (𝓞 F)ˣ) : unitNorm ε ≠ 0 := by
  intro h; have := abs_unitNorm ε; rw [h, abs_zero] at this; exact zero_ne_one this

lemma unitNorm_mul (ε ε' : (𝓞 F)ˣ) : unitNorm (ε * ε') = unitNorm ε * unitNorm ε' := by
  simp [unitNorm, Finset.prod_mul_distrib]

lemma eisDen_smul (ε : (𝓞 F)ˣ) (x : F × F) (Z : InfinitePlace F → ℂ) :
    eisDen (ε • x) Z = unitNorm ε * eisDen x Z := by
  simp only [eisDen, unitNorm, smul_fst, smul_snd, map_mul, ofReal_mul, ofReal_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => by ring

/-- **The summand** $W(x)\,N(cZ + d)^{-k}$. -/
noncomputable def eisTerm (W : F × F → ℂ) (k : ℤ) (x : F × F) (Z : InfinitePlace F → ℂ) : ℂ :=
  W x * eisDen x Z ^ (-k)

/-- **Unit equivariance of a weight**: $W(\varepsilon x) = N(\varepsilon)^k W(x)$ for all units $\varepsilon$ and $x \in F^2$. It makes
the summand $W(x)N(cz+d)^{-k}$ constant on $U$-orbits. -/
def IsUnitEquivariant (W : F × F → ℂ) (k : ℤ) : Prop :=
  ∀ (ε : (𝓞 F)ˣ) (x : F × F), W (ε • x) = ((unitNorm ε : ℝ) : ℂ) ^ k * W x

lemma eisTerm_smul {W : F × F → ℂ} {k : ℤ} (hW : IsUnitEquivariant W k) (ε : (𝓞 F)ˣ)
    (x : F × F) (Z : InfinitePlace F → ℂ) : eisTerm W k (ε • x) Z = eisTerm W k x Z := by
  have hu : ((unitNorm ε : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (unitNorm_ne_zero ε)
  rw [eisTerm, eisTerm, hW, eisDen_smul, mul_zpow, zpow_neg ((unitNorm ε : ℝ) : ℂ)]
  field_simp

/-- The term of an orbit does not depend on the representative. -/
lemma eisTerm_out {W : F × F → ℂ} {k : ℤ} (hW : IsUnitEquivariant W k) (x : F × F)
    (Z : InfinitePlace F → ℂ) :
    eisTerm W k (Quotient.mk _ x : UOrbit F).out Z = eisTerm W k x Z := by
  obtain ⟨ε, hε⟩ := exists_smul_out x
  rw [← hε, eisTerm_smul hW]

/-- **The Eisenstein series on $\mathbb{C}^\iota$**: $\sum_{o \in U\backslash F^2}W(x_o)N(c_oZ + d_o)^{-k}$, $x_o$ = `o.out`. -/
noncomputable def eisSeriesC (W : F × F → ℂ) (k : ℤ) (Z : InfinitePlace F → ℂ) : ℂ :=
  ∑' o : UOrbit F, eisTerm W k o.out Z

/-- **The Hilbert Eisenstein series of weight $W$ and parallel weight $k$** on $\mathbb{H}^d$:
$$E_{W,k}(z) = \sum_{(c,d) \in U\backslash F^2}W(c, d)\,N(cz + d)^{-k},$$
one term per $U$-orbit (representative `Quotient.out`; immaterial under `IsUnitEquivariant`). Parameters: `W` (the
weight on pairs, the bottom rows $(c, d)$), `k` (the parallel weight). -/
@[kb "shimura1978" "§3, (3.4)–(3.5), Eisenstein series as sums over pairs modulo units [unverified]"]
noncomputable def eisSeries (W : F × F → ℂ) (k : ℤ) (z : InfinitePlace F → ℍ) : ℂ :=
  eisSeriesC W k fun v => (z v : ℂ)

/-! ### The transformation law -/

/-- **The transformed weight** $W_A(y) = W(yA^{-1})$. -/
def slashWeight (W : F × F → ℂ) (A : SL(2, F)) : F × F → ℂ := fun y => W (rowMul y A⁻¹)

lemma IsUnitEquivariant.slashWeight {W : F × F → ℂ} {k : ℤ} (hW : IsUnitEquivariant W k)
    (A : SL(2, F)) : IsUnitEquivariant (slashWeight W A) k := by
  intro ε x
  simp only [HilbertModular.slashWeight, rowMul_smul]
  exact hW ε _

lemma slashWeight_mul (W : F × F → ℂ) (A B : SL(2, F)) :
    slashWeight (slashWeight W A) B = slashWeight W (A * B) := by
  funext y
  simp only [slashWeight, _root_.mul_inv_rev, rowMul_mul]

@[simp] lemma slashWeight_one (W : F × F → ℂ) : slashWeight W 1 = W := by
  funext y; simp [slashWeight]

/-- **The automorphy factor and the norm**: $N\big(c(Az) + d\big)\prod_vj(A_v, z_v) = N\big((xA)_0z + (xA)_1\big)$. -/
lemma eisDen_smul_mul (x : F × F) (A : SL(2, F)) (z : InfinitePlace F → ℍ) :
    eisDen x (fun v => (((slHom (realEmb F) A • z) v : ℍ) : ℂ)) *
        ∏ v, denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) =
      eisDen (rowMul x A) fun v => (z v : ℂ) := by
  rw [eisDen, eisDen, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hd := denom_ne_zero ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)
  rw [Pi.smul_apply', glPos_smul_eq, coe_smul_of_det_pos (det_glPos_pos _)]
  have key : ∀ c d n D : ℂ, D ≠ 0 → (c * (n / D) + d) * D = c * n + d * D := by
    intro c d n D hD; field_simp
  rw [key _ _ _ _ hd]
  simp only [num, denom, slHom_apply_coe, rowMul, map_add, map_mul, ofReal_add, ofReal_mul]
  ring

/-- **The transformation law of $E_{W,k}$**: $E_{W,k}\,|_k\,A = E_{W_A,k}$ for $A \in \mathrm{SL}_2(F)$, $W_A(y) = W(yA^{-1})$
(`slashWeight`), for every unit-equivariant weight. An identity of `tsum`s: no convergence hypothesis is needed. -/
@[kb "shimura1978" "§3, transformation of Eisenstein series under SL₂(F) [unverified]"]
theorem eisSeries_slash {W : F × F → ℂ} {k : ℤ} (hW : IsUnitEquivariant W k) (A : SL(2, F)) :
    eisSeries W k ∣[k] slHom (realEmb F) A = eisSeries (slashWeight W A) k := by
  funext z
  rw [slash_apply]
  have hJ : ∏ v, ((((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^ (k - 1) : ℝ) : ℂ) *
      denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ (-k) =
      (∏ v, denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)) ^ (-k) := by
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul]
  rw [hJ, eisSeries, eisSeriesC, ← tsum_mul_right]
  have hW' := hW.slashWeight A
  have hterm : ∀ o : UOrbit F,
      eisTerm W k o.out (fun v => (((slHom (realEmb F) A • z) v : ℍ) : ℂ)) *
        (∏ v, denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)) ^ (-k) =
      eisTerm (slashWeight W A) k (orbitMulEquiv A o).out fun v => (z v : ℂ) := by
    intro o
    conv_rhs => rw [← Quotient.out_eq o, orbitMulEquiv_mk, eisTerm_out hW']
    rw [eisTerm, eisTerm, mul_assoc, ← mul_zpow, eisDen_smul_mul, slashWeight,
      rowMul_rowMul_inv]
  simp_rw [hterm]
  rw [eisSeries, eisSeriesC]
  exact (orbitMulEquiv A).tsum_eq fun o => eisTerm (slashWeight W A) k o.out fun v => (z v : ℂ)

/-- **Invariance**: if $W(yA^{-1}) = \lambda W(y)$ for all $y$, then $E_{W,k}\,|_k\,A = \lambda E_{W,k}$. -/
theorem eisSeries_slash_of_weight {W : F × F → ℂ} {k : ℤ} (hW : IsUnitEquivariant W k)
    (A : SL(2, F)) {c : ℂ} (hA : slashWeight W A = c • W) :
    eisSeries W k ∣[k] slHom (realEmb F) A = c • eisSeries W k := by
  rw [eisSeries_slash hW A, hA]
  funext z
  simp only [eisSeries, eisSeriesC, eisTerm, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left, mul_assoc]

end QuadFormsKB.HilbertModular
