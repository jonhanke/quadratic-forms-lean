/-
# The big-cell part of the Siegel Eisenstein series of degree $r$ at $s_0$

**Layer:** local at each finite place $v$ of a number field $F$ (dyadic places included), then global over a totally real $F$.

**Setting.** $Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus\{0\}$, $n = 2m$ (0-based indices); $L = \mathcal O_F^n$ and the finite datum
$\Phi_v = \mathbf 1_{L_v^r}$ at every finite place $v$ (`oneSG`); $s_0 = m - \frac{r+1}2$ (`sZero`); $Z = (Z_w)_w \in \mathbb H_r^d$; the
archimedean section of weight $m$ (`archSecR`); $w = \begin{pmatrix}0&1\\-1&0\end{pmatrix}$, $n(B) = \begin{pmatrix}1&B\\0&1\end{pmatrix}$.

**Results.**
* `fixesOne_spN_int` (local, every finite place): $\omega_v(n(\lambda))\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ for $\lambda \in \mathrm{Sym}_r(\mathcal O_v)$
  and $a_i \in \mathcal O_v$ (no condition on the different: $\psi_v$ is trivial on $\mathfrak d_v^{-1} \supseteq \mathcal O_v$). Hence
  `secRV_oneSG_mul_spN`: $f_v(g\,n(\lambda)) = f_v(g)$.
* `finSecR_sZero`: at $s = s_0$ the height factors disappear, $f_f(\gamma, s_0) = \prod_vf_{\Phi_v}(\gamma_v)$.
* **`finSecR_spW_spN_add`** (**periodicity of the singular-series coefficient**): for $\lambda \in \mathrm{Sym}_r(\mathcal O_F)$,
  $f_f(w\,n(B + \lambda), s_0) = f_f(w\,n(B), s_0)$.
* **`archSecR_spW_spN`**: $f_\infty(w\,n(B)g_Z, s_0) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\cdot\prod_w\det\big(-(Z_w + \sigma_w(B))\big)^{-m}$.
* **`eisensteinR_eq_lower_add_bigCell`** (**the Bruhat splitting of $E$**): for $m > 4r^2$ (so that $E(g_Z, s_0, \Phi)$ converges absolutely,
  `summable_norm_globalSecR`),
  $$E(g_Z, s_0, \Phi) = \sum_{P(F)\gamma,\ \det C_\gamma = 0}f(\gamma g_Z, s_0)\ +\ \sum_{B\in\mathrm{Sym}_r(F)}f_\infty(w\,n(B)g_Z, s_0)\,f_f(w\,n(B), s_0),$$
  both series absolutely convergent (`summable_norm_bigCellTerm`). The second sum is the big-cell part whose $T$-th Fourier
  coefficients are unfolded in `EisensteinUnfold.lean`.

For $r = 1$ these are the degree-one `eisenstein_eq_bruhat`, `finSec_wMat_nMat`, `archSec_wMat_nMat` (`SiegelWeil/`).

Sources: Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), Ch. II [unverified];
Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 (the Bruhat decomposition $P\backslash G = \bigsqcup_jPw_jN$) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinSummable
import QuadFormsKB.SiegelWeil.Forms.BruhatBigCell

open Matrix NumberField IsDedekindDomain Filter WithZero
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-! ### Local: $n(\lambda)$, $\lambda$ integral, fixes the lattice function at every finite place -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m r : ℕ}

local notation "Fv" => v.adicCompletion F

variable (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- $\omega_v(n(B))\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ for $B$ symmetric with entries in $\mathcal O_v$ and $a_i \in \mathcal O_v$, at every finite
place (dyadic and ramified places included). -/
lemma fixesOne_spN_int (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (B : Matrix (Fin r) (Fin r) Fv)
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
    have : (localDataV v).ψ (trace (B * QX a X)) = 1 := psiV_eq_one_of_le_one v hint
    rw [this]; simp
  · simp

/-- $f_v(g\,n(\lambda)) = f_v(g)$ for the lattice function and $\lambda \in \mathrm{Sym}_r(\mathcal O_v)$. -/
lemma secRV_oneSG_mul_spN (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (g : Sp r Fv) (B : Matrix (Fin r) (Fin r) Fv)
    (hB : Bᵀ = B) (hBi : ∀ i j, Valued.v (B i j) ≤ 1) :
    secRV v a (oneSG v m r) (g * spN B hB) = secRV v a (oneSG v m r) g := by
  rw [secRV_eq, secRV_eq, map_mul, Module.End.mul_apply, fixesOne_spN_int v a ha B hB hBi]

end Local

/-! ### Global -/

section Global

variable {F : Type} [Field F] [NumberField F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

lemma sZero_add_rhoR : sZero m r + rhoR r = m := by unfold sZero rhoR; ring

/-- **At $s_0$ the height factors disappear**: $f_f(\gamma, s_0) = \prod_vf_{\Phi_v}(\gamma_v)$. -/
lemma finSecR_sZero (a : Fin (2 * m) → Fˣ) (Φ : ∀ v : HeightOneSpectrum (𝓞 F), Sg (localDataV v) m r) (γ : Sp r F) :
    finSecR a Φ γ (sZero m r) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), secRV v (aV a v) (Φ v) (locSpV v γ) := by
  unfold finSecR secSR
  congr 1; funext v
  rw [sub_self, neg_zero, Complex.cpow_zero, mul_one]

/-- An $r\times r$ matrix over $F$ with entries in $\mathcal O_F$. -/
def IsIntMat (B : Matrix (Fin r) (Fin r) F) : Prop := ∀ i j, ∃ o : 𝓞 F, ιO o = B i j

lemma valued_algebraMap_int (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (ιO o)) ≤ 1 :=
  (LocalDensity.NF.ι v o).2

include F in
lemma aV_unitsOfInt_le_one (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (i : Fin (2 * m)) :
    Valued.v ((aV (unitsOfInt b hb) v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 := by
  rw [← aOfInt_eq_aV]; exact aOfInt_le_one v b hb i

/-- **Periodicity of the finite section under $\mathrm{Sym}_r(\mathcal O_F)$**: $f_f(\gamma\,n(\lambda), s_0) = f_f(\gamma, s_0)$ for the lattice
function $\Phi_v = \mathbf 1_{L_v^r}$ at every $v$ and $\lambda$ symmetric with entries in $\mathcal O_F$. -/
theorem finSecR_mul_spN_int (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (γ : Sp r F)
    (L : Matrix (Fin r) (Fin r) F) (hL : Lᵀ = L) (hLi : IsIntMat L) :
    finSecR (unitsOfInt b hb) (fun v => oneSG v m r) (γ * spN L hL) (sZero m r) =
      finSecR (unitsOfInt b hb) (fun v => oneSG v m r) γ (sZero m r) := by
  rw [finSecR_sZero, finSecR_sZero]
  congr 1; funext v
  rw [map_mul, locSp_spN]
  refine secRV_oneSG_mul_spN v _ (aV_unitsOfInt_le_one b hb v) _ _ _ fun i j => ?_
  obtain ⟨o, ho⟩ := hLi i j
  rw [Matrix.map_apply, ← ho]
  exact valued_algebraMap_int v o

/-- **`finSecR_spW_spN_add`**: $f_f(w\,n(B + \lambda), s_0) = f_f(w\,n(B), s_0)$ for $\lambda \in \mathrm{Sym}_r(\mathcal O_F)$. -/
theorem finSecR_spW_spN_add (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (B L : Matrix (Fin r) (Fin r) F)
    (hB : Bᵀ = B) (hL : Lᵀ = L) (hLi : IsIntMat L) :
    finSecR (unitsOfInt b hb) (fun v => oneSG v m r) (spW * spN (B + L) (by rw [transpose_add, hB, hL])) (sZero m r) =
      finSecR (unitsOfInt b hb) (fun v => oneSG v m r) (spW * spN B hB) (sZero m r) := by
  rw [← finSecR_mul_spN_int b hb (spW * spN B hB) L hL hLi, mul_assoc, ← spN_add]

/-! ### The archimedean section on the big cell -/

variable [IsTotallyReal F]

lemma blockD_spW_spN {k : Type*} [Field k] (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) :
    blockD (spW * spN B hB) = -B := by
  unfold blockD; rw [spW_spN_coe]; simp

lemma denW_spW_spN (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ)
    (w : InfinitePlace F) :
    denW (spW * spN B hB) Z w = -(Z w + B.map (fun x => (realEmb F w x : ℂ))) := by
  rw [denW, blockC_spW_spN, blockD_spW_spN]
  rw [neg_add]
  congr 1
  · ext i j; simp [Matrix.map_neg]
  · ext i j; simp

/-- **The archimedean section on the big cell at $s_0$**:
$f_\infty(w\,n(B)g_Z, s_0) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\cdot\big(\prod_w\det(-(Z_w + \sigma_w(B)))\big)^{-m}$. -/
theorem archSecR_spW_spN (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    archSecR m Z (sZero m r) (spW * spN B hB) =
      (∏ w, ((((Z w).map Complex.im).det : ℝ) : ℂ) ^ ((m : ℂ) / 2)) *
        (∏ w, (-(Z w + B.map (fun x => (realEmb F w x : ℂ)))).det) ^ (-(m : ℤ)) := by
  unfold archSecR
  rw [sZero_add_rhoR, sub_self, Complex.cpow_zero, mul_one]
  congr 2
  unfold denR
  exact Finset.prod_congr rfl fun w _ => by rw [denW_spW_spN]

/-! ### The Bruhat splitting -/

/-- The term of the Eisenstein series at a coset $q \in P(F)\backslash\mathrm{Sp}_{2r}(F)$ (through `Quotient.lift`). -/
def eisTermR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (q : PQuot r F) : ℂ :=
  Quotient.lift (globalSecR (unitsOfInt b hb) (fun v => oneSG v m r) (archSecR m Z (sZero m r)) (sZero m r))
    (globalSecR_lift (unitsOfInt b hb) (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl)
      (isArchSectionR_archSecR b hb hbpos Z (sZero m r))) q

/-- **The big-cell term** $f_\infty(w\,n(B)g_Z, s_0)\,f_f(w\,n(B), s_0)$ for $B \in \mathrm{Sym}_r(F)$. -/
def bigCellTerm (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ)
    (B : SymMat r F) : ℂ :=
  archSecR m Z (sZero m r) (spW * spN B.1 B.2) *
    finSecR (unitsOfInt b hb) (fun v => oneSG v m r) (spW * spN B.1 B.2) (sZero m r)

lemma eisTermR_bigCellMap (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (B : SymMat r F) :
    eisTermR b hb hbpos Z (bigCellMap B) = bigCellTerm b hb Z B := rfl

lemma eisTermR_eq_out (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (q : PQuot r F) :
    eisTermR b hb hbpos Z q = globalSecR (unitsOfInt b hb) (fun v => oneSG v m r) (archSecR m Z (sZero m r)) (sZero m r)
      q.out := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

lemma sZero_hs (hm : 4 * (r : ℝ) ^ 2 < m) : 4 * (r : ℝ) ^ 2 < (sZero m r).re + ((r : ℝ) + 1) / 2 := by
  have : (sZero m r).re = (m : ℝ) - ((r : ℝ) + 1) / 2 := by simp [sZero]
  rw [this]; linarith

/-- **Absolute convergence of $E(g_Z, s_0, \Phi)$** for $m > 4r^2$, as a sum of `eisTermR` over $P(F)\backslash\mathrm{Sp}_{2r}(F)$. -/
theorem summable_norm_eisTermR (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (hr : 1 ≤ r) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) (hm : 4 * (r : ℝ) ^ 2 < m) :
    Summable fun q : PQuot r F => ‖eisTermR b hb hbpos Z q‖ := by
  have h := summable_norm_globalSecR b hb hbpos (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl) hr hZ
    (sZero_hs hm)
  refine h.congr fun q => ?_
  rw [eisTermR_eq_out]

/-- **The big-cell terms are absolutely summable** over $B \in \mathrm{Sym}_r(F)$ ($m > 4r^2$). -/
theorem summable_norm_bigCellTerm (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    (hr : 1 ≤ r) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) (hm : 4 * (r : ℝ) ^ 2 < m) :
    Summable fun B : SymMat r F => ‖bigCellTerm b hb Z B‖ := by
  have h := (summable_norm_eisTermR b hb hbpos hr hZ hm).comp_injective (bigCellMap_injective (k := F) (r := r))
  refine h.congr fun B => ?_
  simp only [Function.comp, eisTermR_bigCellMap]

/-- **The Bruhat splitting of $E(g_Z, s_0, \Phi)$** ($m > 4r^2$): the Eisenstein series is the sum over the lower cells ($\det C = 0$) plus
the big-cell sum $\sum_{B\in\mathrm{Sym}_r(F)}f_\infty(w\,n(B)g_Z, s_0)f_f(w\,n(B), s_0)$. -/
@[kb "kudla2008" "§1 (the Bruhat decomposition of $P\\backslash G$; the big cell $PwN$) [unverified]; weil1965 Ch. II [unverified]"]
theorem eisensteinR_eq_lower_add_bigCell (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelHF F r) (hm : 4 * (r : ℝ) ^ 2 < m) :
    eisensteinR (unitsOfInt b hb) (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl)
        (isArchSectionR_archSecR b hb hbpos Z (sZero m r)) =
      (∑' q : ↥(bigCell r F)ᶜ, eisTermR b hb hbpos Z q) + ∑' B : SymMat r F, bigCellTerm b hb Z B := by
  have hs := (summable_norm_eisTermR b hb hbpos hr hZ hm).of_norm
  have e1 : eisensteinR (unitsOfInt b hb) (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl)
      (isArchSectionR_archSecR b hb hbpos Z (sZero m r)) = ∑' q, eisTermR b hb hbpos Z q := rfl
  rw [e1, ← hs.tsum_subtype_add_tsum_subtype_compl (bigCell r F), add_comm]
  congr 1
  rw [← (bigCellEquiv r F).tsum_eq]
  rfl

end Global

end QuadFormsKB.SiegelWeil.Forms
