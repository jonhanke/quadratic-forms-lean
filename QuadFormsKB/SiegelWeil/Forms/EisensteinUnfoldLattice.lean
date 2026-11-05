/-
# The lattice $\mathrm{Sym}_r(\mathcal O_F)$ and its characters (Siegel–Weil for forms by forms)

**Layer:** global over a totally real number field $F$ (algebra and the real embeddings).

**Setting.** Symmetric $r\times r$ matrices over $F$ in upper coordinates $u = (u_p)_{p = (i\le i')}$ (`symOf u`); the lattice
$\Lambda = \mathrm{Sym}_r(\mathcal O_F) = \{u : u_p \in \mathcal O_F\}$ (`symO F r`); the real coordinates `tOf u` of `EisensteinUnfoldCoord.lean`
(the coordinates of $\sigma(u_p)$ in the basis `oBasis F` of $\sigma(\mathcal O_F)$); a form $T$ in $r$ variables over $F$ with Gram matrix
$T_G = \frac12H_T$ (`gramT`) and $e_T(Z) = \exp\big(2\pi i\sum_w\operatorname{tr}(\sigma_w(T_G)Z_w)\big)$ (`eT`).

**Results.**
* `symOEquiv`: $\mathbb Z^J \cong \Lambda$, with `tOf_symOEquiv`: the real coordinates of $\lambda = $ `symOEquiv n` are $n$.
* `eT_add`: $e_T(Z + Z') = e_T(Z)e_T(Z')$; `trPair_realMat`: $\sum_w\operatorname{tr}(\sigma_w(T_G)\sigma_w(B)) = \operatorname{Tr}_{F/\mathbb Q}\operatorname{tr}(T_GB)$.
* **`eT_realMat_int`**: $e_T(\sigma(\lambda)) = 1$ for $T$ with coefficients in $\mathcal O_F$ and $\lambda \in \mathrm{Sym}_r(\mathcal O_F)$ (because
  $\operatorname{tr}(T_G\lambda) = \operatorname{tr}(C_T\lambda) \in \mathcal O_F$ for the coefficient matrix $C_T$ and $\lambda$ symmetric).
* `tsum_eq_tsum_quot`: $\sum_{u}G(u) = \sum_{q\in(\cdot)/\Lambda}\sum_{n\in\mathbb Z^J}G(\tilde q + \lambda_n)$ for absolutely summable $G$.

Sources: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfoldCoord
import QuadFormsKB.HilbertModular.ThetaGamma0

open Matrix NumberField IsDedekindDomain
open QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

variable (F r) in
/-- **The lattice** $\Lambda = \mathrm{Sym}_r(\mathcal O_F)$ in upper coordinates: $u$ with every $u_p \in \mathcal O_F$. -/
def symO : AddSubgroup (SymIdx r → F) :=
  AddSubgroup.pi Set.univ fun _ => (algebraMap (𝓞 F) F).range.toAddSubgroup

lemma mem_symO {u : SymIdx r → F} : u ∈ symO F r ↔ ∀ p, ∃ o : 𝓞 F, ιO o = u p := by
  simp [symO, AddSubgroup.mem_pi]

lemma isIntMat_symOf {u : SymIdx r → F} (hu : u ∈ symO F r) : IsIntMat (symOf u) := by
  intro i j
  rw [mem_symO] at hu
  simp only [symOf, of_apply]
  split_ifs
  · exact hu _
  · exact hu _

/-! ### Real coordinates -/

lemma fCoord_add (x y : F) : fCoord (x + y) = fCoord x + fCoord y := by
  unfold fCoord; rw [realVec_add, map_add]

lemma tOf_add (u u' : SymIdx r → F) : tOf (u + u') = tOf u + tOf u' := by
  funext q; simp only [tOf, Pi.add_apply, fCoord_add]

lemma realVec_injective : Function.Injective (realVec : F → InfinitePlace F → ℝ) := by
  intro x y h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := congrFun h w
  exact (realEmb F w).injective this

lemma fCoord_injective : Function.Injective (fCoord : F → _) := by
  intro x y h
  exact realVec_injective ((oBasis F).equivFun.injective h)

lemma tOf_injective : Function.Injective (tOf : (SymIdx r → F) → JR F r → ℝ) := by
  intro u u' h
  funext p
  apply fCoord_injective
  funext j
  exact congrFun h (p, j)

lemma exists_int_tOf {u : SymIdx r → F} (hu : u ∈ symO F r) : ∃ n : JR F r → ℤ, tOf u = fun q => (n q : ℝ) := by
  rw [mem_symO] at hu
  choose o ho using hu
  choose n hn using fun p => exists_int_fCoord (F := F) (o p)
  refine ⟨fun q => n q.1 q.2, ?_⟩
  funext q
  simp only [tOf]
  rw [← ho q.1, hn q.1]

lemma exists_symO_tOf (n : JR F r → ℤ) : ∃ u ∈ symO F r, tOf u = fun q => (n q : ℝ) := by
  choose o ho using fun p : SymIdx r => exists_int_of_fCoord (F := F) (fun j => n (p, j))
  refine ⟨fun p => ιO (o p), mem_symO.mpr fun p => ⟨o p, rfl⟩, ?_⟩
  funext q
  simp only [tOf, fCoord]
  rw [← ho q.1, LinearEquiv.apply_symm_apply]

/-- The integral coordinates of a lattice point. -/
def symOInt (u : symO F r) : JR F r → ℤ := (exists_int_tOf u.2).choose

lemma tOf_symOInt (u : symO F r) : tOf (u : SymIdx r → F) = fun q => (symOInt u q : ℝ) :=
  (exists_int_tOf u.2).choose_spec

lemma symOInt_bijective : Function.Bijective (symOInt (F := F) (r := r)) := by
  refine ⟨fun u u' h => Subtype.ext (tOf_injective ?_), fun n => ?_⟩
  · rw [tOf_symOInt, tOf_symOInt, h]
  · obtain ⟨u, hu, hun⟩ := exists_symO_tOf (F := F) n
    refine ⟨⟨u, hu⟩, ?_⟩
    funext q
    have := congrFun ((tOf_symOInt ⟨u, hu⟩).symm.trans hun) q
    exact_mod_cast this

/-- **$\mathbb Z^J \cong \mathrm{Sym}_r(\mathcal O_F)$**: the lattice point with integral coordinates $n$. -/
def symOEquiv : (JR F r → ℤ) ≃ symO F r := (Equiv.ofBijective _ symOInt_bijective).symm

lemma tOf_symOEquiv (n : JR F r → ℤ) : tOf (symOEquiv n : SymIdx r → F) = fun q => (n q : ℝ) := by
  rw [tOf_symOInt]
  have : symOInt (symOEquiv n) = n := (Equiv.ofBijective _ symOInt_bijective).apply_symm_apply n
  rw [this]

/-! ### The characters $e_T$ -/

lemma trPair_add (T : QuadForm F r) (Z Z' : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    trPair T (Z + Z') = trPair T Z + trPair T Z' := by
  simp only [trPair, Pi.add_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma trPair_neg (T : QuadForm F r) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    trPair T (-Z) = -trPair T Z := by
  simp only [trPair, Pi.neg_apply, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

lemma eT_add (T : QuadForm F r) (Z Z' : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    eT T (Z + Z') = eT T Z * eT T Z' := by
  rw [eT, eT, eT, trPair_add, mul_add, Complex.exp_add]

lemma eT_neg (T : QuadForm F r) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    eT T (-Z) = (eT T Z)⁻¹ := by
  rw [eT, eT, trPair_neg, mul_neg, Complex.exp_neg]

/-- $\sum_w\operatorname{tr}(\sigma_w(T_G)\sigma_w(B)) = \operatorname{Tr}_{F/\mathbb Q}\operatorname{tr}(T_GB)$. -/
lemma trPair_realMat (T : QuadForm F r) (B : Matrix (Fin r) (Fin r) F) :
    trPair T (realMat B) = ((Algebra.trace ℚ F (trace (gramT T * B)) : ℚ) : ℂ) := by
  have h := sum_realEmb (F := F) (trace (gramT T * B))
  have h' : (((Algebra.trace ℚ F (trace (gramT T * B)) : ℚ) : ℝ) : ℂ) =
      ∑ w, ((realEmb F w (trace (gramT T * B)) : ℝ) : ℂ) := by
    rw [← h]; push_cast; rfl
  rw [show ((Algebra.trace ℚ F (trace (gramT T * B)) : ℚ) : ℂ) =
      (((Algebra.trace ℚ F (trace (gramT T * B)) : ℚ) : ℝ) : ℂ) by push_cast; rfl, h']
  unfold trPair realMat
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [trace, diag, mul_apply, map_sum, map_mul, Complex.ofReal_sum, Complex.ofReal_mul, Matrix.map_apply]

/-- $\operatorname{tr}(T_GB) = \operatorname{tr}(C_TB)$ for $B$ symmetric ($T_G = \frac12(C_T + C_T^{\mathsf T})$). -/
lemma trace_gramT_mul (T : QuadForm F r) {B : Matrix (Fin r) (Fin r) F} (hB : Bᵀ = B) :
    trace (gramT T * B) = trace (T.coeff * B) := by
  have h1 : trace (T.coeffᵀ * B) = trace (T.coeff * B) := by
    rw [← trace_transpose, transpose_mul, transpose_transpose, hB, trace_mul_comm]
  rw [gramT, QuadForm.hessian, Matrix.smul_mul, trace_smul, Matrix.add_mul, trace_add, h1, smul_eq_mul]
  ring

lemma trace_mul_int {C B : Matrix (Fin r) (Fin r) F} (hC : IsIntMat C) (hB : IsIntMat B) :
    ∃ o : 𝓞 F, ιO o = trace (C * B) := by
  choose c hc using hC
  choose b hb' using hB
  refine ⟨∑ i, ∑ j, c i j * b j i, ?_⟩
  simp only [trace, diag, mul_apply, map_sum, map_mul, hc, hb']

/-- **$e_T(\sigma(\lambda)) = 1$** for $T$ with coefficients in $\mathcal O_F$ and $\lambda$ symmetric with entries in $\mathcal O_F$. -/
theorem eT_realMat_int (T : QuadForm F r) (hT : IsIntMat T.coeff) {B : Matrix (Fin r) (Fin r) F} (hB : Bᵀ = B)
    (hBi : IsIntMat B) : eT T (realMat B) = 1 := by
  rw [eT, trPair_realMat, trace_gramT_mul T hB]
  obtain ⟨o, ho⟩ := trace_mul_int hT hBi
  rw [← ho]
  exact cexp_trace_eq_one (algebraMap_mem_invDifferent o)

/-! ### Regrouping a sum over $\mathrm{Sym}_r(F)$ by cosets of $\Lambda$ -/

lemma sub_out_mem_symO (u : SymIdx r → F) :
    u - (QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r).out ∈ symO F r := by
  have h : (QuotientAddGroup.mk (QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r).out :
      (SymIdx r → F) ⧸ symO F r) = QuotientAddGroup.mk u := QuotientAddGroup.out_eq' _
  rw [QuotientAddGroup.eq] at h
  rwa [sub_eq_neg_add]

/-- $(q, \lambda) \mapsto \tilde q + \lambda$: $(\mathrm{Sym}_r(F)/\Lambda) \times \Lambda \cong \mathrm{Sym}_r(F)$. -/
def quotProdEquiv : ((SymIdx r → F) ⧸ symO F r) × symO F r ≃ (SymIdx r → F) where
  toFun x := x.1.out + x.2
  invFun u := (QuotientAddGroup.mk u, ⟨u - (QuotientAddGroup.mk u : (SymIdx r → F) ⧸ symO F r).out, sub_out_mem_symO u⟩)
  left_inv x := by
    obtain ⟨q, l⟩ := x
    have hq : (QuotientAddGroup.mk (q.out + (l : SymIdx r → F)) : (SymIdx r → F) ⧸ symO F r) = q := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.eq_zero_iff (l : SymIdx r → F) |>.mpr l.2, add_zero,
        QuotientAddGroup.out_eq']
    refine Prod.ext hq (Subtype.ext ?_)
    show q.out + (l : SymIdx r → F) - _ = (l : SymIdx r → F)
    rw [hq]; abel
  right_inv u := by simp only; abel

/-- $\sum_uG(u) = \sum_{q\in\mathrm{Sym}_r(F)/\Lambda}\sum_{n\in\mathbb Z^J}G(\tilde q + \lambda_n)$ for $G$ absolutely summable. -/
theorem tsum_eq_tsum_quot {G : (SymIdx r → F) → ℂ} (hG : Summable fun u => ‖G u‖) :
    ∑' u, G u = ∑' q : (SymIdx r → F) ⧸ symO F r, ∑' n : JR F r → ℤ, G (q.out + (symOEquiv n : SymIdx r → F)) := by
  set e := (quotProdEquiv (F := F) (r := r))
  have h1 : ∑' u, G u = ∑' x : ((SymIdx r → F) ⧸ symO F r) × symO F r, G (e x) :=
    (e.tsum_eq (f := G)).symm
  have hs : Summable fun x : ((SymIdx r → F) ⧸ symO F r) × symO F r => G (e x) :=
    (hG.of_norm).comp_injective e.injective
  have hsn : Summable fun x : ((SymIdx r → F) ⧸ symO F r) × symO F r => ‖G (e x)‖ :=
    hG.comp_injective e.injective
  rw [h1, hs.tsum_prod' (fun q => (hsn.prod_factor q).of_norm)]
  congr 1; funext q
  rw [← symOEquiv.tsum_eq]
  rfl

end QuadFormsKB.SiegelWeil.Forms
