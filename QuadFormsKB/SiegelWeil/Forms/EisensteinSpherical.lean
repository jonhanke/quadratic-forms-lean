/-
# The lattice function is $\mathrm{Sp}_{2r}(\mathcal O_v)$-invariant at good places
**Layer:** local, non-archimedean: a finite place $v$ of a number field $F$ which is good for $V$ (`IsGoodV`: $d_v = 0$, $v \nmid 2$,
all $a_i$ units).

**Result.** `weilRepSpV_oneSG_of_good`: for every $k \in \mathrm{Sp}_{2r}(F_v)$ with entries in $\mathcal O_v$,
$$\omega_v(k)\,\mathbf 1_{M_{n\times r}(\mathcal O_v)} = \mathbf 1_{M_{n\times r}(\mathcal O_v)}.$$
*Proof.* The elements fixing $\Phi_v = \mathbf 1_{L_v^r}$ form a subgroup. It contains $n(B)$ for $B$ integral symmetric
($\psi_v(\operatorname{tr}(B\,Q[X])) = 1$ on $L_v^r$, since $d_v = 0$), $m(A)$ for $A \in \mathrm{GL}_r(\mathcal O_v)$ ($\chi_V(\det A) = 1$,
$|\det A|_v = 1$, $L_v^rA = L_v^r$), and $w$ ($\gamma_V = 1$ and $L_v$ is self-dual, coordinate by coordinate). By the factorization
$k = n(-X)\,\bar n(Y)\,m(A)\,n(Z)$ over the local ring $\mathcal O_v$ (`symplectic_factor_local`) and $\bar n(Y) = w\,n(-Y)\,w^{-1}$, $k$ is a
product of such elements. For $r = 1$ this is `weilRepV_oneS_of_good` (`Weil/LocalK0.lean`).

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.4 (the unramified vector is $K$-fixed) [unverified];
Rallis, *On the Howe duality conjecture*, Compositio Math. 51 (1984), §5 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.LocalWhittaker
import QuadFormsKB.SiegelWeil.Forms.EisensteinHeight
import QuadFormsKB.SiegelWeil.Forms.SymplecticLocal

open MeasureTheory Matrix IsDedekindDomain NumberField WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open WeilRep WeilRep.LocalData WeilRep.Genus QuadFormsKB.Analysis

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m r : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- $g$ fixes the lattice function: $\omega_v(g)\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$. -/
def FixesOne (g : Sp r Fv) : Prop := weilRepSpV v a r g (oneSG v m r) = oneSG v m r

lemma fixesOne_one : FixesOne v a (1 : Sp r Fv) := by simp [FixesOne]

lemma fixesOne_mul {g h : Sp r Fv} (hg : FixesOne v a g) (hh : FixesOne v a h) : FixesOne v a (g * h) := by
  unfold FixesOne at *
  rw [map_mul, Module.End.mul_apply, hh, hg]

lemma fixesOne_inv {g : Sp r Fv} (hg : FixesOne v a g) : FixesOne v a g⁻¹ := by
  unfold FixesOne at *
  conv_lhs => rw [← hg]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

lemma coe_oneSG : ((oneSG v m r : Sg (localDataV v) m r) : PtG m r Fv → ℂ) = oneG v m r := rfl

/-- A product of matrices with entries in $\mathcal O_v$ has entries in $\mathcal O_v$. -/
lemma intMat_mul {ι κ μ : Type*} [Fintype κ] {M : Matrix ι κ Fv} {N : Matrix κ μ Fv}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1) : ∀ i j, Valued.v ((M * N) i j) ≤ 1 := by
  intro i j
  rw [mul_apply]
  exact Valuation.map_sum_le _ fun l _ => by rw [map_mul]; exact mul_le_one' (hM i l) (hN l j)

/-- $\omega_v(n(B))\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ for $B$ symmetric with entries in $\mathcal O_v$ ($d_v = 0$, $a_i \in \mathcal O_v$). -/
lemma fixesOne_spN (hd : diffExp v = 0) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (B : Matrix (Fin r) (Fin r) Fv)
    (hB : Bᵀ = B) (hBi : ∀ i j, Valued.v (B i j) ≤ 1) : FixesOne v a (spN B hB) := by
  unfold FixesOne
  apply Subtype.ext
  rw [weilRepSpV_spN, endN_apply _ _ hB, coe_oneSG]
  funext X
  have hBid : B.map (RingHom.id Fv) = B := by ext; rfl
  simp only [opNg, hBid]
  rw [oneVG_eq_indicator]
  split_ifs with hX
  · have hint : Valued.v (trace (B * QX a X)) ≤ 1 := by
      have hXt : ∀ i j, Valued.v (Xᵀ i j) ≤ 1 := fun i j => hX j i
      have hDg : ∀ i j, Valued.v ((diagonal fun i => (a i : Fv)) i j) ≤ 1 := by
        intro i j; rw [diagonal_apply]; split_ifs
        · exact ha i
        · simp
      have hQ := intMat_mul v (intMat_mul v hXt hDg) hX
      have hBQ := intMat_mul v hBi hQ
      simp only [trace, diag]
      exact Valuation.map_sum_le _ fun i _ => hBQ i i
    have : (localDataV v).ψ (trace (B * QX a X)) = 1 :=
      psiV_eq_one_of_le_exp v (by rw [hd]; simpa using hint)
    rw [this]; simp
  · simp

lemma valued_det_eq_one {A : GL (Fin r) Fv} (hA : ∀ i j, Valued.v ((A : Matrix (Fin r) (Fin r) Fv) i j) ≤ 1)
    (hA' : ∀ i j, Valued.v (((A⁻¹ : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv) i j) ≤ 1) :
    Valued.v (A : Matrix (Fin r) (Fin r) Fv).det = 1 := by
  have hle : ∀ M : Matrix (Fin r) (Fin r) Fv, (∀ i j, Valued.v (M i j) ≤ 1) → Valued.v M.det ≤ 1 := by
    intro M hM
    rw [det_apply]
    refine Valuation.map_sum_le _ fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul, map_mul]
    refine mul_le_one' ?_ ?_
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · rw [map_prod]; exact Finset.prod_le_one fun i _ => hM _ _
  have h1 := hle _ hA
  have h2 := hle _ hA'
  have hprod : Valued.v (A : Matrix (Fin r) (Fin r) Fv).det * Valued.v (((A⁻¹ : GL (Fin r) Fv) :
      Matrix (Fin r) (Fin r) Fv)).det = 1 := by
    rw [← map_mul, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  have : Valued.v (A : Matrix (Fin r) (Fin r) Fv).det * Valued.v (((A⁻¹ : GL (Fin r) Fv) :
      Matrix (Fin r) (Fin r) Fv)).det < 1 := mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

/-- $\omega_v(m(A))\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ for $A \in \mathrm{GL}_r(\mathcal O_v)$ at a good place. -/
lemma fixesOne_spM (hg : IsGoodV v a) (A : GL (Fin r) Fv)
    (hA : ∀ i j, Valued.v ((A : Matrix (Fin r) (Fin r) Fv) i j) ≤ 1)
    (hA' : ∀ i j, Valued.v (((A⁻¹ : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv) i j) ≤ 1) :
    FixesOne v a (spM A) := by
  have hdet := valued_det_eq_one v hA hA'
  unfold FixesOne
  apply Subtype.ext
  rw [weilRepSpV_spM, endM_apply, coe_oneSG]
  funext X
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id Fv) A = A := by ext; rfl
  simp only [opMg, hmap]
  rw [chiV_eq_one_of_good hg hdet, md_eq_one v hdet, Complex.ofReal_one, one_pow, one_mul, one_mul,
    oneVG_eq_indicator, oneVG_eq_indicator]
  have hiff : (∀ i l, Valued.v ((X * (A : Matrix (Fin r) (Fin r) Fv)) i l) ≤ 1) ↔ ∀ i l, Valued.v (X i l) ≤ 1 := by
    have hint : ∀ (Y : PtG m r Fv) (M : Matrix (Fin r) (Fin r) Fv), (∀ i j, Valued.v (M i j) ≤ 1) →
        (∀ i l, Valued.v (Y i l) ≤ 1) → ∀ i l, Valued.v ((Y * M) i l) ≤ 1 := by
      intro Y M hM hY i l
      rw [mul_apply]
      exact Valuation.map_sum_le _ fun j _ => by rw [map_mul]; exact mul_le_one' (hY i j) (hM j l)
    refine ⟨fun h => ?_, hint X _ hA⟩
    have := hint _ _ hA' h
    rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
  simp only [hiff]

/-- $\omega_v(w)\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ at a good place ($\gamma_V = 1$; $L_v$ is self-dual coordinate by coordinate). -/
lemma fixesOne_spW (hg : IsGoodV v a) : FixesOne v a (spW : Sp r Fv) := by
  unfold FixesOne
  apply Subtype.ext
  rw [weilRepSpV_spW, endW_apply, coe_oneSG, oneG, opWg_ptG (isOps_V v), gammaV_eq_one_of_good hg, one_pow,
    one_smul]
  congr 1
  funext i j
  exact Fa_ballIndV hg.1 (by rw [map_mul, hg.2.1, hg.2.2 i, one_mul])

/-! ### The factorization over $\mathcal O_v$ -/

/-- The integral matrix over $\mathcal O_v$ of an integral $g$. -/
def intMatSp (g : Sp r Fv) (hg : IsIntSp v g) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) 𝔬 :=
  fun x y => ⟨(g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) x y,
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ((norm_le_one_iff_valued v).mp (hg x y))⟩

lemma intMatSp_map (g : Sp r Fv) (hg : IsIntSp v g) :
    (intMatSp v g hg).map (algebraMap 𝔬 Fv) = (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) := by
  ext x y; rfl

lemma algebraMap_O_injective : Function.Injective (algebraMap 𝔬 Fv) := Subtype.val_injective

lemma intMatSp_mem (g : Sp r Fv) (hg : IsIntSp v g) : intMatSp v g hg ∈ symplecticGroup (Fin r) 𝔬 := by
  rw [SymplecticGroup.mem_iff]
  have h := g.2
  rw [SymplecticGroup.mem_iff, ← intMatSp_map v g hg] at h
  have hJ : (Matrix.J (Fin r) 𝔬).map (algebraMap 𝔬 Fv) = Matrix.J (Fin r) Fv := Matrix.map_J (Fin r) (algebraMap 𝔬 Fv)
  rw [← hJ, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul] at h
  exact Matrix.map_injective (algebraMap_O_injective v) h

lemma isIntSp_of_map {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) 𝔬} (g : Sp r Fv)
    (hg : (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) Fv) = M.map (algebraMap 𝔬 Fv)) : IsIntSp v g := by
  intro x y
  rw [hg, map_apply]
  exact (norm_le_one_iff_valued v).mpr (M x y).2

lemma valued_algebraMap_le_one (x : 𝔬) : Valued.v (algebraMap 𝔬 Fv x) ≤ 1 := x.2

/-- **The lattice function is $\mathrm{Sp}_{2r}(\mathcal O_v)$-invariant at a good place**: $\omega_v(k)\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ for every
$k \in \mathrm{Sp}_{2r}(F_v)$ with entries in $\mathcal O_v$, when $d_v = 0$, $v \nmid 2$ and all $a_i$ are units (`IsGoodV`). -/
@[kb "kudla1996" "§I.4 (the unramified vector is $\\mathrm{Sp}_{2n}(\\mathcal O)$-fixed) [unverified]"]
theorem weilRepSpV_oneSG_of_good (hg : IsGoodV v a) (k : Sp r Fv) (hk : IsIntSp v k) :
    weilRepSpV v a r k (oneSG v m r) = oneSG v m r := by
  have ha : ∀ i, Valued.v (a i : Fv) ≤ 1 := fun i => (hg.2.2 i).le
  obtain ⟨X, Y, Z, A, hX, hY, hZ, hA, hfac⟩ := symplectic_factor_local (intMatSp_mem v k hk)
  have hint : ∀ (M : Matrix (Fin r) (Fin r) 𝔬) i j, Valued.v ((M.map (algebraMap 𝔬 Fv)) i j) ≤ 1 :=
    fun M i j => valued_algebraMap_le_one v (M i j)
  have hXs : (-(X.map (algebraMap 𝔬 Fv)))ᵀ = -(X.map (algebraMap 𝔬 Fv)) := by
    rw [transpose_neg, ← transpose_map, hX]
  have hYs : (-(Y.map (algebraMap 𝔬 Fv)))ᵀ = -(Y.map (algebraMap 𝔬 Fv)) := by
    rw [transpose_neg, ← transpose_map, hY]
  have hZs : (Z.map (algebraMap 𝔬 Fv))ᵀ = Z.map (algebraMap 𝔬 Fv) := by rw [← transpose_map, hZ]
  have hAu : IsUnit (A.map (algebraMap 𝔬 Fv)).det := by
    have h := RingHom.map_det (algebraMap 𝔬 Fv) A
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]; exact hA.map _
  set AG : GL (Fin r) Fv := ((Matrix.isUnit_iff_isUnit_det _).mpr hAu).unit
  have hAG : (AG : Matrix (Fin r) (Fin r) Fv) = A.map (algebraMap 𝔬 Fv) := rfl
  have hAGinv : ((AG⁻¹ : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv) = A⁻¹.map (algebraMap 𝔬 Fv) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hAG, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hkeq : k = spN (-(X.map (algebraMap 𝔬 Fv))) hXs *
      (spW * spN (-(Y.map (algebraMap 𝔬 Fv))) hYs * spW⁻¹) * spM AG * spN (Z.map (algebraMap 𝔬 Fv)) hZs := by
    apply Subtype.ext
    have h1 : (1 : Matrix (Fin r) (Fin r) 𝔬).map (algebraMap 𝔬 Fv) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have h0 : (0 : Matrix (Fin r) (Fin r) 𝔬).map (algebraMap 𝔬 Fv) = 0 := Matrix.map_zero _ (map_zero _)
    have hnX : (-X).map (algebraMap 𝔬 Fv) = -(X.map (algebraMap 𝔬 Fv)) := Matrix.map_neg _ (map_neg _) X
    rw [← intMatSp_map v k hk, hfac]
    simp only [Matrix.map_mul, fromBlocks_map, Submonoid.coe_mul, spN_coe, spM_coe, spW_coe,
      SymplecticGroup.coe_inv, hAGinv, hAG, h1, h0, hnX, ← transpose_map]
    simp only [Matrix.J, fromBlocks_multiply, fromBlocks_transpose, transpose_map, fromBlocks_neg, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, transpose_one, transpose_zero,
      transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_zero, neg_neg]
  have hN : ∀ (B : Matrix (Fin r) (Fin r) 𝔬) (s : (B.map (algebraMap 𝔬 Fv))ᵀ = B.map (algebraMap 𝔬 Fv)),
      FixesOne v a (spN (B.map (algebraMap 𝔬 Fv)) s) :=
    fun B s => fixesOne_spN v a hg.1 ha _ s (hint B)
  have hN' : ∀ (B : Matrix (Fin r) (Fin r) 𝔬) (s : (-(B.map (algebraMap 𝔬 Fv)))ᵀ = -(B.map (algebraMap 𝔬 Fv))),
      FixesOne v a (spN (-(B.map (algebraMap 𝔬 Fv))) s) := by
    intro B s
    have e : -(B.map (algebraMap 𝔬 Fv)) = (-B).map (algebraMap 𝔬 Fv) := by rw [Matrix.map_neg _ (map_neg _)]
    refine fixesOne_spN v a hg.1 ha _ s fun i j => ?_
    rw [e]; exact hint _ i j
  have hW := fixesOne_spW (r := r) v a hg
  have hM : FixesOne v a (spM AG) := by
    refine fixesOne_spM v a hg AG ?_ ?_
    · rw [hAG]; exact hint A
    · rw [hAGinv]; exact hint _
  rw [hkeq]
  exact fixesOne_mul v a (fixesOne_mul v a (fixesOne_mul v a (hN' X hXs)
    (fixesOne_mul v a (fixesOne_mul v a hW (hN' Y hYs)) (fixesOne_inv v a hW))) hM) (hN Z hZs)

end QuadFormsKB.SiegelWeil.Forms
