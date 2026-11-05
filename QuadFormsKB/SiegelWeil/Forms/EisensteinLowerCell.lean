/-
# The lower Bruhat cells contribute nothing to the nonsingular Fourier coefficients of $E(g_Z, s_0)$
**Layer:** global over a totally real number field $F$ of degree $d$.

**Setting.** $Q = \sum_{i<n}b_ix_i^2$ totally positive over $\mathcal O_F$, $n = 2m$, $\Phi_v = \mathbf 1_{L_v^r}$, $r \ge 1$, $m > 4r^2$;
$E(g_Z, s_0) = \sum_{q\in P(F)\backslash\mathrm{Sp}_{2r}(F)}f(q\,g_Z, s_0)$ (`eisR`, the terms `eisTermR`); $c_T(f, Y)$ = `coeffR` (the $T$-th
Fourier coefficient at height $Y$ over the unit cube of the coordinates $t \in \mathbb R^J$).

**Idea** (Kudla 2008, §1; Weil 1965, Ch. II). The bottom block $C$ of a representative of $q$ has a kernel $K_q = \ker C \subseteq F^r$ that
depends only on $q$ (`kerQ`); $K_q = 0$ exactly on the big cell. The terms with a given kernel $K$ form a family stable under
$q \mapsto q\,n(\lambda)$, $\lambda \in \mathrm{Sym}_r(\mathcal O_F)$ (`kerQ_mulRight_spN`), which translates $Z$ by $\sigma(\lambda)$
(`eisTermR_mulRight_spN`); so their sum $G_K$ is $\mathrm{Sym}_r(\mathcal O_F)$-periodic. If $u \in K$, $u \ne 0$, then every term of $G_K$ is
invariant under the real translation $Z_{w_0} \mapsto Z_{w_0} + uv^{\mathsf T} + vu^{\mathsf T}$ at one real place $w_0$, $v$ any real vector
(`eisTermR_add_dirX`, by the matrix determinant lemma `det_add_sym_ker`). For $\det T \ne 0$ choose $v = \sigma_{w_0}(T_Gu) \ne 0$: the
character $e_T$ is nontrivial in that direction, so $c_T(G_K, Y) = 0$ (`integral_unitCube_eq_zero_of_shift`). Summing over $K$ (dominated
convergence, with the uniform majorant `exists_norm_globalSecR_le` + `exists_norm_det_CZD_ge_unif`) leaves the big cell $K = 0$.

**Results.**
* `kerQ`, `kerQ_mulRight_spN`, `kerQ_eq_bot_iff` (the kernel of the bottom block on cosets);
* `eisTermR_mulRight_spN`: $f(q\,n(\lambda)g_Z, s_0) = f(q\,g_{Z+\sigma(\lambda)}, s_0)$;
* `eisTermR_add_dirX`: the translation invariance above;
* **`coeffR_eisR_eq_coeffR_eisBigR`**: for $T$ with coefficients in $\mathcal O_F$ and $\det T_G \ne 0$, $c_T(E, Y) = c_T(E_{\mathrm{big}}, Y)$.

Sources: Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 (only the big cell contributes to the nonsingular
coefficients) [unverified]; Weil, Acta Math. 113 (1965), Ch. II [unverified]; Shimura, *On Eisenstein series*, Duke Math. J. 50 (1983),
§2 [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinMajorant
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfold
import QuadFormsKB.SiegelWeil.Forms.EisensteinSLInv
import QuadFormsKB.SiegelWeil.Forms.EisensteinDetLemmas
import QuadFormsKB.SiegelWeil.Forms.EisensteinArchUniform

open Matrix NumberField IsDedekindDomain Filter MeasureTheory
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-! ### The kernel of the bottom block on cosets -/

section Kernel

variable {k : Type*} [Field k] {r : ℕ}

/-- The kernel $\ker C_g \subseteq k^r$ of the bottom-left block of $g \in \mathrm{Sp}_{2r}(k)$. -/
def kerC (g : Sp r k) : Submodule k (Fin r → k) := LinearMap.ker (blockC g).mulVecLin

lemma mem_kerC {g : Sp r k} {u : Fin r → k} : u ∈ kerC g ↔ blockC g *ᵥ u = 0 := Iff.rfl

lemma kerC_mul_of_mem {p : Sp r k} (hp : p ∈ siegelP r k) (g : Sp r k) : kerC (p * g) = kerC g := by
  have hD : IsUnit (blockD p).det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have := det_blockD_of_mem_siegelP hp; rw [h0, zero_mul] at this; exact zero_ne_one this
  ext u
  rw [mem_kerC, mem_kerC, (blockCD_mul_of_mem_siegelP hp g).1, ← mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (fun x => (blockD p)⁻¹ *ᵥ x) h
    simp only [mulVec_mulVec, mulVec_zero] at this
    rwa [← Matrix.mul_assoc, nonsing_inv_mul _ hD, Matrix.one_mul] at this
  · intro h; rw [h, mulVec_zero]

lemma blockC_mul_spN (g : Sp r k) (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) :
    blockC (g * spN B hB) = blockC g := by
  unfold blockC
  rw [show ((g * spN B hB : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
    (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) * (spN B hB : Sp r k) from rfl, spN_coe]
  conv_lhs => rw [eq_fromBlocks g]
  rw [fromBlocks_multiply]
  simp [blockC]

lemma blockD_mul_spN (g : Sp r k) (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) :
    blockD (g * spN B hB) = blockC g * B + blockD g := by
  unfold blockD
  rw [show ((g * spN B hB : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
    (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) * (spN B hB : Sp r k) from rfl, spN_coe]
  conv_lhs => rw [eq_fromBlocks g]
  rw [fromBlocks_multiply]
  simp [blockC, blockD]

lemma kerC_mul_spN (g : Sp r k) (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) : kerC (g * spN B hB) = kerC g := by
  unfold kerC; rw [blockC_mul_spN]

/-- **The kernel of the bottom block on $P(k)\backslash\mathrm{Sp}_{2r}(k)$**: $\ker C_\gamma$ for any representative $\gamma$. -/
def kerQ (q : PQuot r k) : Submodule k (Fin r → k) :=
  Quotient.liftOn q kerC (fun g g' h => by
    have h' : g' * g⁻¹ ∈ siegelP r k := QuotientGroup.rightRel_apply.mp h
    have e : g' = (g' * g⁻¹) * g := by group
    rw [e, kerC_mul_of_mem h' g])

lemma kerQ_mk (g : Sp r k) : kerQ (Quotient.mk _ g : PQuot r k) = kerC g := rfl

lemma kerQ_eq_kerC_out (q : PQuot r k) : kerQ q = kerC q.out := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

/-- $\ker C = 0$ exactly on the big cell. -/
lemma kerQ_eq_bot_iff (q : PQuot r k) : kerQ q = ⊥ ↔ q ∈ bigCell r k := by
  induction q using Quotient.inductionOn with
  | h g =>
    show kerC g = ⊥ ↔ (blockC g).det ≠ 0
    rw [kerC, Matrix.ker_mulVecLin_eq_bot_iff, ne_eq, ← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro h ⟨v, hv0, hv⟩; exact hv0 (h v hv)
    · intro h v hv; by_contra h0; exact h ⟨v, h0, hv⟩

/-- The rows of $(C\ D)$ are independent: $uC = uD = 0 \Rightarrow u = 0$ (from $DA^{\mathsf T} - CB^{\mathsf T} = 1$). -/
lemma blocks_vecMul_eq_zero {K : Type*} [CommRing K] (f : k →+* K) (g : Sp r k) (u : Fin r → K)
    (hC : u ᵥ* (blockC g).map f = 0) (hD : u ᵥ* (blockD g).map f = 0) : u = 0 := by
  have h := SymplecticGroup.transpose_mem g.2
  rw [eq_fromBlocks g, fromBlocks_transpose, SymplecticGroup.fromBlocks_mem_iff] at h
  have h3 := h.2.2
  simp only [transpose_transpose] at h3
  -- h3 : A Dᵀ - B Cᵀ = 1, so D Aᵀ - C Bᵀ = 1
  have h4 : blockD g * (blockA g)ᵀ - blockC g * (blockB g)ᵀ = 1 := by
    have := congrArg transpose h3
    rwa [transpose_sub, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose, transpose_one] at this
  have h5 := congrArg f.mapMatrix h4
  simp only [map_sub, map_mul, map_one, RingHom.mapMatrix_apply] at h5
  calc u = u ᵥ* (1 : Matrix (Fin r) (Fin r) K) := (vecMul_one u).symm
    _ = u ᵥ* ((blockD g).map f * (blockA g)ᵀ.map f - (blockC g).map f * (blockB g)ᵀ.map f) := by rw [h5]
    _ = 0 := by rw [vecMul_sub, ← vecMul_vecMul, ← vecMul_vecMul, hC, hD, zero_vecMul, zero_vecMul, sub_zero]

end Kernel

/-! ### The terms of $E$ under translation -/

section Global

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

lemma kerQ_mulRight_spN (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (q : PQuot r F) :
    kerQ (pquotMulRight (spN B hB) q) = kerQ q := by
  induction q using Quotient.inductionOn with
  | h g => exact kerC_mul_spN g B hB

lemma denW_mul_spN (γ : Sp r F) (L : Matrix (Fin r) (Fin r) F) (hL : Lᵀ = L)
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (w : InfinitePlace F) :
    denW (γ * spN L hL) Z w = denW γ (fun w => Z w + realMat L w) w := by
  unfold denW realMat
  have hm : ((blockC γ * L).map fun x => ((realEmb F w x : ℝ) : ℂ)) =
      ((blockC γ).map fun x => ((realEmb F w x : ℝ) : ℂ)) * L.map fun x => ((realEmb F w x : ℝ) : ℂ) :=
    Matrix.map_mul (f := Complex.ofRealHom.comp (realEmb F w))
  rw [blockC_mul_spN, blockD_mul_spN, Matrix.map_add _ (by intros; simp), hm, mul_add]
  abel

lemma im_add_realMat' (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (L : Matrix (Fin r) (Fin r) F)
    (w : InfinitePlace F) : (Z w + realMat L w).map Complex.im = (Z w).map Complex.im := by
  ext i j; simp [realMat]

/-- **Right translation by $n(\lambda)$, $\lambda \in \mathrm{Sym}_r(\mathcal O_F)$, translates $Z$**:
$f(q\,n(\lambda)g_Z, s_0) = f(q\,g_{Z+\sigma(\lambda)}, s_0)$. -/
lemma eisTermR_mulRight_spN (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (L : Matrix (Fin r) (Fin r) F) (hL : Lᵀ = L) (hLi : IsIntMat L)
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (q : PQuot r F) :
    eisTermR b hb hbpos Z (pquotMulRight (spN L hL) q) = eisTermR b hb hbpos (fun w => Z w + realMat L w) q := by
  induction q using Quotient.inductionOn with
  | h γ =>
    rw [pquotMulRight_mk]
    show globalSecR _ _ _ _ (γ * spN L hL) = globalSecR _ _ _ _ γ
    unfold globalSecR
    rw [finSecR_mul_spN_int b hb γ L hL hLi]
    congr 1
    unfold archSecR denR
    simp only [denW_mul_spN, im_add_realMat']

/-! ### Translation invariance along the kernel -/

open Classical in
/-- A real direction at the single real place $w_0$ (zero at the other places). -/
def dirX (w0 : InfinitePlace F) (X : Matrix (Fin r) (Fin r) ℝ) : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ :=
  fun w => if w = w0 then X.map (fun x => (x : ℂ)) else 0

/-- $\sigma_w(u) \in \mathbb R^r$. -/
def realVecR (w : InfinitePlace F) (u : Fin r → F) : Fin r → ℝ := fun i => realEmb F w (u i)

lemma blockCw_mul_transpose' (γ : Sp r F) (w : InfinitePlace F) :
    blockCw γ w * (blockDw γ w)ᵀ = blockDw γ w * (blockCw γ w)ᵀ := by
  simp only [blockCw, blockDw, ← transpose_map, ← Matrix.map_mul]
  rw [blockC_mul_blockD_transpose]

/-- $\det(\sigma_w(C)Z_w + \sigma_w(D)) \ne 0$ on $\mathbb H_r^d$. -/
lemma det_denW_ne_zero (γ : Sp r F) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r)
    (w : InfinitePlace F) : (denW γ Z w).det ≠ 0 :=
  PhiArch.det_ne_zero (blockCw_mul_transpose' γ w)
    (fun u hC hD => blocks_vecMul_eq_zero (realEmb F w) γ u hC hD) (hZ w)

/-- **Translation invariance of the terms with $u \in \ker C$**: for $u \in K_q$ and any real vector $v$,
$f(q\,g_{Z'}, s_0) = f(q\,g_Z, s_0)$ where $Z'$ is $Z$ with $Z_{w_0}$ replaced by $Z_{w_0} + \sigma_{w_0}(u)v^{\mathsf T} + v\sigma_{w_0}(u)^{\mathsf T}$. -/
lemma eisTermR_add_dirX (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) (q : PQuot r F) {u : Fin r → F}
    (hu : u ∈ kerQ q) (w0 : InfinitePlace F) (v : Fin r → ℝ) :
    eisTermR b hb hbpos (Z + dirX w0 (vecMulVec (realVecR w0 u) v + vecMulVec v (realVecR w0 u))) q =
      eisTermR b hb hbpos Z q := by
  set X := vecMulVec (realVecR w0 u) v + vecMulVec v (realVecR w0 u)
  rw [eisTermR_eq_out, eisTermR_eq_out]
  unfold globalSecR
  congr 1
  have him : ∀ w, ((Z + dirX w0 X) w).map Complex.im = (Z w).map Complex.im := by
    intro w; ext i j; by_cases hw : w = w0 <;> simp [dirX, hw]
  have hden : denR q.out (Z + dirX w0 X) = denR q.out Z := by
    unfold denR
    refine Finset.prod_congr rfl fun w _ => ?_
    by_cases hw : w = w0
    · subst hw
      have h0 : blockC q.out *ᵥ u = 0 := by rw [← mem_kerC, ← kerQ_eq_kerC_out]; exact hu
      have hu' : blockCw q.out w *ᵥ realVecR w u = 0 := by
        funext i
        have := RingHom.map_mulVec (realEmb F w) (blockC q.out) u i
        rw [h0] at this
        simp only [Pi.zero_apply, map_zero] at this
        exact this.symm
      have := det_add_sym_ker (blockCw q.out w) (blockDw q.out w) (blockCw_mul_transpose' q.out w) (hZ w).1
        (det_denW_ne_zero q.out hZ w) (realVecR w u) v hu'
      have e1 : denW q.out (Z + dirX w X) w =
          (blockCw q.out w).map (fun x => (x : ℂ)) * (Z w + X.map (fun x => (x : ℂ))) +
            (blockDw q.out w).map (fun x => (x : ℂ)) := by
        simp only [denW, Pi.add_apply, dirX]; rfl
      rw [e1]
      exact this
    · simp [denW, dirX, hw]
  unfold archSecR
  rw [hden]
  simp only [him]

/-! ### Choice of the direction: the character is nontrivial along it -/

/-- Every family of real symmetric matrices is $X(s)$ for some coordinates $s$. -/
lemma exists_xMat_eq (X : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (hX : ∀ w, (X w)ᵀ = X w) :
    ∃ s : JR F r → ℝ, ∀ w, xMat s w = X w := by
  set s : JR F r → ℝ := fun q => (oBasis F).equivFun (fun w => X w q.1.1.1 q.1.1.2) q.2 with hs
  refine ⟨s, fun w => ?_⟩
  have hc : ∀ p : SymIdx r, xCoord s p = fun w => X w p.1.1 p.1.2 := by
    intro p
    show (oBasis F).equivFun.symm (fun j => (oBasis F).equivFun (fun w => X w p.1.1 p.1.2) j) = _
    exact (oBasis F).equivFun.symm_apply_apply _
  have e : xMat s w = symOf (fun p => xCoord s p w) := rfl
  rw [e]
  ext i j
  rw [symOf, of_apply]
  split_ifs with h
  · rw [hc]
  · rw [hc]; show X w j i = X w i j; exact congrFun (congrFun (hX w) i) j

lemma chiT_add (T : QuadForm F r) (t s : JR F r → ℝ) : chiT T (t + s) = chiT T t * chiT T s := by
  unfold chiT
  rw [← eT_add]
  congr 1
  funext w
  rw [xMat_add, Matrix.map_add _ (by intros; push_cast; ring)]
  simp only [Pi.add_apply, neg_add]

/-- **A direction along which $e_T$ is nontrivial**: for $\det T_G \ne 0$, $u \ne 0$ and a real place $w_0$ there are $v \in \mathbb R^r$ and
coordinates $s_0$ with $X(s_0) = $ `dirX` $w_0\,(\sigma_{w_0}(u)v^{\mathsf T} + v\sigma_{w_0}(u)^{\mathsf T})$ and $\chi_T(s_0) = -1$. -/
lemma exists_shift (T : QuadForm F r) (hdet : (gramT T).det ≠ 0) {u : Fin r → F} (hu0 : u ≠ 0)
    (w0 : InfinitePlace F) :
    ∃ (v : Fin r → ℝ) (s0 : JR F r → ℝ),
      (∀ w, (xMat s0 w).map (fun x => (x : ℂ)) =
        dirX w0 (vecMulVec (realVecR w0 u) v + vecMulVec v (realVecR w0 u)) w) ∧ chiT T s0 = -1 := by
  classical
  set A : Matrix (Fin r) (Fin r) ℝ := (gramT T).map (realEmb F w0) with hA
  set u' := realVecR w0 u
  set v0 := A *ᵥ u' with hv0
  have hAs : Aᵀ = A := by rw [hA, ← transpose_map, gramT_transpose]
  have hv0' : v0 = realVecR w0 (gramT T *ᵥ u) := by
    funext i; exact (RingHom.map_mulVec (realEmb F w0) (gramT T) u i).symm
  have hTu : gramT T *ᵥ u ≠ 0 := by
    intro h0; exact hu0 (by
      by_contra hne
      exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hne, h0⟩))
  have hv0ne : v0 ≠ 0 := by
    rw [hv0']
    intro h
    apply hTu
    funext i
    have := congrFun h i
    simp only [realVecR, Pi.zero_apply] at this
    exact (realEmb F w0).injective (this.trans (map_zero _).symm)
  have hP : 0 < v0 ⬝ᵥ v0 := by
    rcases Function.ne_iff.mp hv0ne with ⟨i, hi⟩
    have : 0 < v0 i * v0 i := mul_self_pos.mpr hi
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => v0 j * v0 j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i))
  set c : ℝ := 1 / (4 * (v0 ⬝ᵥ v0)) with hc
  set v := c • v0
  set X : Matrix (Fin r) (Fin r) ℝ := vecMulVec u' v + vecMulVec v u'
  have hXs : Xᵀ = X := by
    simp only [X, transpose_add, transpose_vecMulVec]; abel
  obtain ⟨s0, hs0⟩ := exists_xMat_eq (fun w => if w = w0 then X else 0) (fun w => by
    split_ifs <;> simp [hXs])
  refine ⟨v, s0, fun w => ?_, ?_⟩
  · rw [hs0]; by_cases hw : w = w0 <;> simp [dirX, hw, X]
  -- the pairing
  have hpair : ∑ i, ∑ j, A i j * X j i = 1 / 2 := by
    have e1 : ∑ i, ∑ j, A i j * X j i = v ⬝ᵥ (A *ᵥ u') + u' ⬝ᵥ (A *ᵥ v) := by
      simp only [X, Matrix.add_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum, mul_add,
        Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have e2 : u' ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u') := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hAs, dotProduct_comm]
    rw [e1, e2, ← hv0]
    simp only [v, smul_dotProduct, smul_eq_mul, hc]
    field_simp
    ring
  unfold chiT eT trPair
  have htr : ∑ w, ∑ i, ∑ j, (realEmb F w (gramT T i j) : ℂ) * (-(xMat s0 w).map (fun x => (x : ℂ))) j i =
      -((1 / 2 : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single w0]
    · rw [hs0, ite_eq_left_iff.mpr (fun h => absurd rfl h), ← hpair]
      push_cast
      simp only [Matrix.neg_apply, Matrix.map_apply, mul_neg, Finset.sum_neg_distrib, hA]
    · intro w _ hw
      rw [hs0, ite_eq_right_iff.mpr (fun h => absurd h hw)]
      simp
    · intro h; exact absurd (Finset.mem_univ w0) h
  rw [htr]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * -((1 / 2 : ℝ) : ℂ) = -(Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-! ### Vanishing of a coefficient integral under a shift -/

/-- If a $\mathbb Z^J$-periodic function $G$ satisfies $G(t + s_0) = cG(t)$ with $c \ne 1$, then $\int_{(0,1]^J}G = 0$. -/
lemma integral_unitCube_eq_zero_of_shift {J : Type*} [Fintype J] (G : (J → ℝ) → ℂ)
    (hG : ∀ (n : J → ℤ) t, G (t + fun j => (n j : ℝ)) = G t) (s0 : J → ℝ) {c : ℂ} (hc : c ≠ 1)
    (hs : ∀ t, G (t + s0) = c * G t) : ∫ t in unitCube J, G t = 0 := by
  have h := integral_unitCube_add G hG s0
  simp_rw [hs] at h
  rw [integral_const_mul] at h
  have : (c - 1) * ∫ t in unitCube J, G t = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc)

/-! ### The cube majorant and the interchange of sum and integral -/

/-- An absolutely and uniformly summable family of continuous functions can be integrated termwise over $(0,1]^J$. -/
lemma integral_unitCube_tsum {J ι : Type*} [Fintype J] [Countable ι] (f : ι → (J → ℝ) → ℂ) (G : ι → ℝ)
    (hG : Summable G) (hcont : ∀ i, Continuous (f i)) (hb : ∀ i, ∀ t ∈ Set.Icc (0 : J → ℝ) 1, ‖f i t‖ ≤ G i) :
    ∫ t in unitCube J, ∑' i, f i t = ∑' i, ∫ t in unitCube J, f i t := by
  have hsub : unitCube J ⊆ Set.Icc 0 1 := fun t ht => ⟨fun j => (ht j).1.le, fun j => (ht j).2⟩
  have hvol : volume (unitCube J) < ⊤ := by rw [volume_unitCube]; exact ENNReal.one_lt_top
  have hint : ∀ i, Integrable (f i) (volume.restrict (unitCube J)) := fun i =>
    IntegrableOn.of_bound hvol (hcont i).aestronglyMeasurable (G i)
      (by filter_upwards [ae_restrict_mem measurableSet_unitCube] with t ht using hb i t (hsub ht))
  have hsum : Summable fun i => ∫ t in unitCube J, ‖f i t‖ := by
    refine hG.of_nonneg_of_le (fun i => integral_nonneg fun t => norm_nonneg _) fun i => ?_
    have := norm_setIntegral_le_of_norm_le_const hvol (f := fun t => ‖f i t‖)
      (fun t ht => by rw [norm_norm]; exact hb i t (hsub ht))
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _), measureReal_def, volume_unitCube,
      ENNReal.toReal_one, mul_one] at this
    exact this
  exact (integral_tsum_of_summable_integral_norm hint hsum).symm

/-- $f_\infty(\gamma g_Z, s_0) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\cdot j(\gamma, Z)^{-m}$. -/
lemma archSecR_sZero (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (γ : Sp r F) :
    archSecR m Z (sZero m r) γ =
      (∏ w, ((((Z w).map Complex.im).det : ℝ) : ℂ) ^ ((m : ℂ) / 2)) * denR γ Z ^ (-(m : ℤ)) := by
  unfold archSecR
  rw [sZero_add_rhoR, sub_self, Complex.cpow_zero, mul_one]

lemma continuous_zPt_apply (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (w : InfinitePlace F) :
    Continuous fun t : JR F r → ℝ => zPt Y t w := by
  unfold zPt
  refine Continuous.add ?_ continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.map_apply]
  exact Complex.continuous_ofReal.comp (continuous_xMat_apply w i j)

lemma continuous_eisTermR_zPt (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ}
    (hY : ∀ w, (Y w).PosDef) (q : PQuot r F) : Continuous fun t => eisTermR b hb hbpos (zPt Y t) q := by
  simp only [eisTermR_eq_out, globalSecR, archSecR_sZero, zPt_im Y hY]
  refine Continuous.mul (Continuous.mul continuous_const ?_) continuous_const
  refine Continuous.zpow₀ ?_ _ (fun t => Or.inl ?_)
  · unfold denR
    refine continuous_finsetProd _ fun w _ => ?_
    unfold denW
    exact ((continuous_const.matrix_mul (continuous_zPt_apply Y w)).add continuous_const).matrix_det
  · unfold denR
    exact Finset.prod_ne_zero_iff.mpr fun w _ => det_denW_ne_zero _ (zPt_mem_siegelHF Y hY t) w

/-- **A majorant of the terms of $E$ uniform on the closed cube** ($Y$ fixed). -/
lemma exists_cube_majorant (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) :
    ∃ G : PQuot r F → ℝ, Summable G ∧
      ∀ t ∈ Set.Icc (0 : JR F r → ℝ) 1, ∀ q, ‖eisTermR b hb hbpos (zPt Y t) q‖ ≤ G q := by
  obtain ⟨K, G, -, hG, -, hbd⟩ := exists_norm_globalSecR_le b hb hbpos (fun v => oneSG v m r)
    (Filter.Eventually.of_forall fun _ => rfl) hr (sZero_hs hm)
  have hc : ∀ w, ∃ c : ℝ, 0 < c ∧ ∀ Z ∈ (fun t => zPt Y t w) '' Set.Icc (0 : JR F r → ℝ) 1, IsDetConst c Z :=
    fun w => exists_norm_det_CZD_ge_unif (isCompact_Icc.image (continuous_zPt_apply Y w))
      (by rintro _ ⟨t, -, rfl⟩; exact zPt_mem_siegelHF Y hY t w)
  choose c hc0 hcZ using hc
  refine ⟨fun q => (∏ v, ((Y v).det) ^ (((sZero m r).re + ((r : ℝ) + 1) / 2) / 2)) * K *
    ((∏ w, c w) / 2 ^ Fintype.card (InfinitePlace F)) ^ (-((sZero m r).re + ((r : ℝ) + 1) / 2)) * G q,
    hG.mul_left _, fun t ht q => ?_⟩
  rw [eisTermR_eq_out]
  have := hbd (zPt Y t) (zPt_mem_siegelHF Y hY t) c hc0 (fun w => hcZ w _ ⟨t, ht, rfl⟩) q
  simpa only [zPt_im Y hY] using this

/-! ### The kernel families and their coefficients -/

/-- **The sum $G_K(Z)$ of the terms of $E(g_Z, s_0)$ over the cosets with $\ker C = K$.** -/
def fibSum (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (K : Submodule F (Fin r → F)) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∑' x : {q : PQuot r F // kerQ q = K}, eisTermR b hb hbpos Z x.1

/-- $G_K$ is $\mathrm{Sym}_r(\mathcal O_F)$-periodic. -/
lemma fibSum_add_int (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (K : Submodule F (Fin r → F)) (L : Matrix (Fin r) (Fin r) F) (hL : Lᵀ = L) (hLi : IsIntMat L)
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    fibSum b hb hbpos K (fun w => Z w + realMat L w) = fibSum b hb hbpos K Z := by
  unfold fibSum
  simp only [← eisTermR_mulRight_spN b hb hbpos L hL hLi]
  set e : {q : PQuot r F // kerQ q = K} ≃ {q : PQuot r F // kerQ q = K} :=
    (pquotMulRight (spN L hL)).subtypeEquiv (fun q => by rw [kerQ_mulRight_spN])
  exact e.tsum_eq (fun x => eisTermR b hb hbpos Z x.1)

/-- **The nonsingular coefficients of $G_K$ vanish for $K \ne 0$.** -/
lemma integral_fibSum_eq_zero (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ}
    (hY : ∀ w, (Y w).PosDef) (T : QuadForm F r) (hT : IsIntMat T.coeff) (hdet : (gramT T).det ≠ 0)
    (K : Submodule F (Fin r → F)) (hK : K ≠ ⊥) :
    ∫ t in unitCube (JR F r), fibSum b hb hbpos K (zPt Y t) * chiT T t = 0 := by
  obtain ⟨u, huK, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨v, s0, hs0, hchi⟩ := exists_shift T hdet hu0 w0
  refine integral_unitCube_eq_zero_of_shift _ (fun n t => ?_) s0 (c := -1) (by norm_num) (fun t => ?_)
  · have hz : zPt Y (t + fun j => (n j : ℝ)) =
        fun w => zPt Y t w + realMat (symOf (symOEquiv n : SymIdx r → F)) w := by
      rw [← tOf_symOEquiv]; exact zPt_add_tOf Y t _
    rw [hz, chiT_add_int T hT t n,
      fibSum_add_int b hb hbpos K _ (symOf_transpose _) (isIntMat_symOf (symOEquiv n).2)]
  · have hz : zPt Y (t + s0) =
        zPt Y t + dirX w0 (vecMulVec (realVecR w0 u) v + vecMulVec v (realVecR w0 u)) := by
      funext w; rw [zPt_add, hs0]; rfl
    have hinv : fibSum b hb hbpos K
        (zPt Y t + dirX w0 (vecMulVec (realVecR w0 u) v + vecMulVec v (realVecR w0 u))) =
        fibSum b hb hbpos K (zPt Y t) :=
      tsum_congr fun x => eisTermR_add_dirX b hb hbpos (zPt_mem_siegelHF Y hY t) x.1
        (by rw [x.2]; exact huK) w0 v
    rw [hz, chiT_add, hchi, hinv]
    ring

/-- The kernel family $K = 0$ is the big cell: $G_0 = E_{\mathrm{big}}$. -/
lemma fibSum_bot (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : fibSum b hb hbpos ⊥ Z = eisBigR b hb Z := by
  unfold fibSum eisBigR
  rw [← (Equiv.subtypeEquivRight kerQ_eq_bot_iff).symm.tsum_eq]
  rw [← (bigCellEquiv r F).tsum_eq]
  rfl

/-! ### The comparison -/

/-- **The Siegel Eisenstein series $E(g_Z, s_0, \Phi)$ of degree $r$** as the sum of its terms over $P(F)\backslash\mathrm{Sp}_{2r}(F)$
(`eisR_eq_eisensteinR`). -/
def eisR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∑' q : PQuot r F, eisTermR b hb hbpos Z q

lemma eisR_eq_eisensteinR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    eisR b hb hbpos Z = eisensteinR (unitsOfInt b hb) (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl)
      (isArchSectionR_archSecR b hb hbpos Z (sZero m r)) := rfl

/-- **Only the big cell contributes to the nonsingular Fourier coefficients** ($m > 4r^2$): for $T$ with coefficients in $\mathcal O_F$ and
$\det T_G \ne 0$, $c_T(E, Y) = c_T(E_{\mathrm{big}}, Y)$ at every height $Y$. -/
@[kb "kudla2008" "§1 (only the big cell contributes to the nonsingular Fourier coefficients) [unverified]; weil1965 Ch. II [unverified]"]
theorem coeffR_eisR_eq_coeffR_eisBigR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    {Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ} (hY : ∀ w, (Y w).PosDef) (T : QuadForm F r)
    (hT : IsIntMat T.coeff) (hdet : (gramT T).det ≠ 0) :
    coeffR (eisR b hb hbpos) T Y = coeffR (eisBigR b hb) T Y := by
  classical
  have : Countable F := Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  have : Countable (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) :=
    inferInstanceAs (Countable (Fin r ⊕ Fin r → Fin r ⊕ Fin r → F))
  have : Countable (Sp r F) := Subtype.countable
  have : Countable (PQuot r F) := Quotient.countable
  obtain ⟨G, hG, hbd⟩ := exists_cube_majorant b hb hbpos hr hm hY
  set f : PQuot r F → (JR F r → ℝ) → ℂ := fun q t => eisTermR b hb hbpos (zPt Y t) q * chiT T t with hf
  have hfc : ∀ q, Continuous (f q) := fun q =>
    (continuous_eisTermR_zPt b hb hbpos hY q).mul (continuous_chiT T)
  have hfb : ∀ q, ∀ t ∈ Set.Icc (0 : JR F r → ℝ) 1, ‖f q t‖ ≤ G q := fun q t ht => by
    simp only [f, norm_mul, norm_chiT, mul_one]; exact hbd t ht q
  set a : PQuot r F → ℂ := fun q => ∫ t in unitCube (JR F r), f q t with ha_def
  have hvol : volume (unitCube (JR F r)) < ⊤ := by rw [volume_unitCube]; exact ENNReal.one_lt_top
  have ha : Summable a := by
    refine Summable.of_norm_bounded hG fun q => ?_
    have := norm_setIntegral_le_of_norm_le_const hvol (f := f q)
      (fun t ht => hfb q t ⟨fun j => (ht j).1.le, fun j => (ht j).2⟩)
    rwa [measureReal_def, volume_unitCube, ENNReal.toReal_one, mul_one] at this
  -- the coefficient of `E` is the sum of the coefficients of the terms
  have h1 : coeffR (eisR b hb hbpos) T Y = ∑' q, a q := by
    unfold coeffR eisR
    rw [← integral_unitCube_tsum f G hG hfc hfb]
    congr 1; funext t
    rw [tsum_mul_right]; rfl
  -- the coefficient of a kernel family
  have hfib : ∀ K : Submodule F (Fin r → F), ∑' x : {q : PQuot r F // kerQ q = K}, a x =
      ∫ t in unitCube (JR F r), fibSum b hb hbpos K (zPt Y t) * chiT T t := by
    intro K
    rw [← integral_unitCube_tsum (fun x : {q : PQuot r F // kerQ q = K} => f x) (fun x => G x)
      (hG.comp_injective Subtype.val_injective) (fun x => hfc x) (fun x => hfb x)]
    congr 1; funext t
    unfold fibSum
    rw [tsum_mul_right]
  -- regroup by kernels
  have hsig : HasSum (fun K : Submodule F (Fin r → F) => ∑' x : {q : PQuot r F // kerQ q = K}, a x)
      (∑' q, a q) := by
    have h0 : HasSum (a ∘ Equiv.sigmaFiberEquiv kerQ) (∑' q, a q) :=
      (Equiv.sigmaFiberEquiv kerQ).hasSum_iff.mpr ha.hasSum
    exact h0.sigma fun K => (ha.comp_injective Subtype.val_injective).hasSum
  have hsingle : HasSum (fun K : Submodule F (Fin r → F) => ∑' x : {q : PQuot r F // kerQ q = K}, a x)
      (∑' x : {q : PQuot r F // kerQ q = ⊥}, a x) := by
    refine hasSum_single ⊥ fun K hK => ?_
    rw [hfib K]
    exact integral_fibSum_eq_zero b hb hbpos hY T hT hdet K hK
  rw [h1, hsig.unique hsingle, hfib ⊥]
  unfold coeffR
  simp only [fibSum_bot]
  rfl

end Global

end QuadFormsKB.SiegelWeil.Forms
