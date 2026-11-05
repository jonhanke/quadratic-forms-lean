/-
# Periodicity of $\mathcal E^{(r)}$ under $\mathrm{Sym}_r(\mathfrak d^{-1})$, and vanishing of the coefficients at non-integral forms (Siegel–Weil for forms by forms)

**Layer:** local at each finite place $v$ of a number field $F$ (dyadic places included), then global over a totally real $F$.

**Setting.** $\mathfrak d^{-1} = $ `FractionalIdeal.dual ℤ ℚ 1` is the inverse different of $F$; $\psi_v$ is trivial on $\mathfrak d_v^{-1} = \{x : v(x) \le \exp(d_v)\}$
(`psiV_eq_one_of_le_exp`). $\Phi_v = \mathbf 1_{L_v^r}$ with $L = \mathcal O_F^n$ and $Q = \sum b_ix_i^2$, $b_i \in \mathcal O_F\setminus\{0\}$.
$e_T(Z) = \exp(2\pi i\sum_w\operatorname{tr}(\sigma_w(T_G)Z_w))$ (`eT`), $Z + B$ is `addB B Z`.

**Results.**
* `IsDualMat B`: all entries of $B$ lie in $\mathfrak d^{-1}$ (weaker than `IsIntMat`, `algebraMap_mem_invDifferent`).
* `fixesOne_spN_dual` (local, every finite place): $\omega_v(n(\lambda))\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ for $\lambda$ symmetric with $v(\lambda_{ij}) \le \exp(d_v)$
  (since $\operatorname{tr}(\lambda Q[X])$ has valuation $\le \exp(d_v)$ by the ultrametric inequality). Hence `secRV_oneSG_mul_spN_dual` and
  **`finSecR_mul_spN_dual`**: $f_f(\gamma\,n(\lambda), s_0) = f_f(\gamma, s_0)$ for $\lambda \in \mathrm{Sym}_r(\mathfrak d^{-1})$.
* **`eisHolR_addB_dual`**: $\mathcal E^{(r)}(Z + B) = \mathcal E^{(r)}(Z)$ for $B \in \mathrm{Sym}_r(\mathfrak d^{-1})$ (not only $\mathrm{Sym}_r(\mathcal O_F)$).
* **`exists_dualMat_eT_ne_one`** (duality): if a coefficient of $T$ is not in $\mathcal O_F$ there is $B \in \mathrm{Sym}_r(\mathfrak d^{-1})$ with $e_T(\sigma(B)) \ne 1$
  (from $\mathfrak d^{-1\,-1} = \mathcal O_F$, `FractionalIdeal.dual_dual`).
* **`coeff_eq_zero_of_not_int`**: an absolutely convergent expansion $f = \sum_Ta(T)e_T$ on $\mathbb H_r^d$ of a function invariant under
  $\mathrm{Sym}_r(\mathfrak d^{-1})$ has $a(T) = 0$ whenever $T$ has a coefficient outside $\mathcal O_F$ (uniqueness of coefficients, `eq_of_hasSum_eT`).

Sources: Neukirch, *Algebraic number theory* (1999), Ch. III §2 (the different and its inverse) [unverified]; Freitag, *Siegelsche Modulfunktionen*
(1983), Ch. I (Fourier expansions of Siegel modular forms) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.HolExpPeriodic
import QuadFormsKB.SiegelWeil.Forms.EisensteinBigCell
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfoldLattice
import QuadFormsKB.SiegelWeil.Forms.FourierUnique

open Matrix NumberField IsDedekindDomain Filter WithZero
open scoped nonZeroDivisors
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-! ### Local -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m r : ℕ}

local notation "Fv" => v.adicCompletion F

variable (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- $\omega_v(n(B))\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ for $B$ symmetric with $v(B_{ij}) \le \exp(d_v)$ (entries in $\mathfrak d_v^{-1}$)
and $a_i \in \mathcal O_v$, at every finite place. -/
lemma fixesOne_spN_dual (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (B : Matrix (Fin r) (Fin r) Fv)
    (hB : Bᵀ = B) (hBi : ∀ i j, Valued.v (B i j) ≤ exp (diffExp v : ℤ)) : FixesOne v a (spN B hB) := by
  unfold FixesOne
  apply Subtype.ext
  rw [weilRepSpV_spN, endN_apply _ _ hB, coe_oneSG]
  funext X
  have hBid : B.map (RingHom.id Fv) = B := by ext; rfl
  simp only [opNg, hBid]
  rw [oneVG_eq_indicator]
  split_ifs with hX
  · have hint : Valued.v (trace (B * QX a X)) ≤ exp (diffExp v : ℤ) := by
      have hXt : ∀ i j, Valued.v (Xᵀ i j) ≤ 1 := fun i j => hX j i
      have hDg : ∀ i j, Valued.v ((diagonal fun i => (a i : Fv)) i j) ≤ 1 := by
        intro i j; rw [diagonal_apply]; split_ifs
        · exact ha i
        · simp
      have hQ := intMat_mul v (intMat_mul v hXt hDg) hX
      simp only [trace, diag]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [mul_apply]
      refine Valuation.map_sum_le _ fun l _ => ?_
      rw [map_mul]
      calc Valued.v (B i l) * Valued.v (QX a X l i) ≤ Valued.v (B i l) * 1 := by gcongr; exact hQ l i
        _ ≤ _ := by rw [mul_one]; exact hBi i l
    have : (localDataV v).ψ (trace (B * QX a X)) = 1 := psiV_eq_one_of_le_exp v hint
    rw [this]; simp
  · simp

/-- $f_v(g\,n(\lambda)) = f_v(g)$ for the lattice function and $\lambda$ with entries in $\mathfrak d_v^{-1}$. -/
lemma secRV_oneSG_mul_spN_dual (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (g : Sp r Fv) (B : Matrix (Fin r) (Fin r) Fv)
    (hB : Bᵀ = B) (hBi : ∀ i j, Valued.v (B i j) ≤ exp (diffExp v : ℤ)) :
    secRV v a (oneSG v m r) (g * spN B hB) = secRV v a (oneSG v m r) g := by
  rw [secRV_eq, secRV_eq, map_mul, Module.End.mul_apply, fixesOne_spN_dual v a ha B hB hBi]

end Local

/-! ### Global -/

section Global

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- **Entries in the inverse different**: $B_{ij} \in \mathfrak d^{-1}$ for all $i, j$. -/
def IsDualMat {r : ℕ} (B : Matrix (Fin r) (Fin r) F) : Prop :=
  ∀ i j, B i j ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)

/-- **Periodicity of the finite section under $\mathrm{Sym}_r(\mathfrak d^{-1})$**: $f_f(\gamma\,n(\lambda), s_0) = f_f(\gamma, s_0)$. -/
theorem finSecR_mul_spN_dual (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (γ : Sp r F)
    (L : Matrix (Fin r) (Fin r) F) (hL : Lᵀ = L) (hLi : IsDualMat L) :
    finSecR (unitsOfInt b hb) (fun v => oneSG v m r) (γ * spN L hL) (sZero m r) =
      finSecR (unitsOfInt b hb) (fun v => oneSG v m r) γ (sZero m r) := by
  rw [finSecR_sZero, finSecR_sZero]
  congr 1; funext v
  rw [map_mul, locSp_spN]
  refine secRV_oneSG_mul_spN_dual v _ (aV_unitsOfInt_le_one b hb v) _ _ _ fun i j => ?_
  rw [Matrix.map_apply]
  exact (mem_dual_one_iff _).mp (hLi i j) v

/-- **Periodicity**: $\mathcal E^{(r)}(Z + B) = \mathcal E^{(r)}(Z)$ for $B \in \mathrm{Sym}_r(\mathfrak d^{-1})$, $Z \in \mathbb H_r^d$. -/
theorem eisHolR_addB_dual (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {B : Matrix (Fin r) (Fin r) F} (hB : Bᵀ = B) (hBi : IsDualMat B) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelHF F r) : eisHolR b hb hbpos (addB B Z) = eisHolR b hb hbpos Z := by
  have hZ' := addB_mem hB hZ
  have hterm : ∀ q : PQuot r F, holQ b hb hbpos (addB B Z) q = holQ b hb hbpos Z (pquotMulRight (spN B hB) q) := by
    intro q
    induction q using Quotient.inductionOn with
    | h γ =>
      rw [pquotMulRight_mk, holQ_mk b hb hbpos hZ', holQ_mk b hb hbpos hZ, holTermR, holTermR, denR_addB γ B hB,
        finSecR_mul_spN_dual b hb γ B hB hBi]
  rw [eisHolR, eisHolR]
  simp only [hterm]
  exact (pquotMulRight (spN B hB)).tsum_eq (holQ b hb hbpos Z)

/-! ### Duality -/

/-- **Duality**: a form with a coefficient outside $\mathcal O_F$ has a nontrivial character $B \mapsto e_T(\sigma(B))$ on
$\mathrm{Sym}_r(\mathfrak d^{-1})$. -/
theorem exists_dualMat_eT_ne_one (T : QuadForm F r) (hT : ¬ IsIntMat T.coeff) :
    ∃ B : Matrix (Fin r) (Fin r) F, ∃ _ : Bᵀ = B, IsDualMat B ∧ eT T (realMat B) ≠ 1 := by
  unfold IsIntMat at hT
  push_neg at hT
  obtain ⟨i, j, hc⟩ := hT
  set c := T.coeff i j with hcdef
  have hij : i ≤ j := by
    by_contra h
    exact hc 0 (by rw [map_zero, hcdef, T.upper (not_le.mp h)])
  -- a dual element `d` with `Tr (c d) ∉ ℤ`
  have hne : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hc' : c ∉ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [FractionalIdeal.dual_dual]
    intro h
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp h
    exact hc o ho
  rw [FractionalIdeal.mem_dual hne] at hc'
  push_neg at hc'
  obtain ⟨d, hd, hdn⟩ := hc'
  let B : Matrix (Fin r) (Fin r) F := Matrix.of fun p q => if (p = i ∧ q = j) ∨ (p = j ∧ q = i) then d else 0
  have hBs : Bᵀ = B := by
    ext p q
    simp only [B, transpose_apply, of_apply]
    by_cases h : (p = i ∧ q = j) ∨ (p = j ∧ q = i)
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]
  have hBd : IsDualMat B := by
    intro p q
    simp only [B, of_apply]
    split_ifs
    · exact hd
    · exact Submodule.zero_mem _
  have htr : trace (T.coeff * B) = c * d := by
    rcases hij.lt_or_eq with hlt | heq
    · have hji : T.coeff j i = 0 := T.upper hlt
      have hsplit : ∀ p q : Fin r, T.coeff p q * B q p =
          (if q = i ∧ p = j then T.coeff j i * d else 0) + (if q = j ∧ p = i then c * d else 0) := by
        intro p q
        simp only [B, of_apply]
        by_cases h1 : q = i ∧ p = j
        · have h2 : ¬ (q = j ∧ p = i) := fun h => hlt.ne (h1.1.symm.trans h.1)
          rw [if_pos (Or.inl ⟨h1.1, h1.2⟩), if_pos h1, if_neg h2, h1.1, h1.2]
          ring
        · by_cases h2 : q = j ∧ p = i
          · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, h2.1, h2.2]
            simp [hcdef]
          · rw [if_neg (by tauto), if_neg h1, if_neg h2]
            simp
      simp only [trace, diag, mul_apply]
      simp only [hsplit, Finset.sum_add_distrib, ite_and]
      simp [hji]
    · subst heq
      simp only [trace, diag, mul_apply, B, of_apply]
      simp [hcdef, ite_and]
  refine ⟨B, hBs, hBd, ?_⟩
  rw [eT, trPair_realMat, trace_gramT_mul T hBs, htr]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2 : (((Algebra.trace ℚ F (c * d) : ℚ)) : ℂ) = (n : ℂ) := by
    have h0 : (2 * Real.pi * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
    apply mul_left_cancel₀ h0
    rw [hn]; ring
  have h3 : Algebra.trace ℚ F (c * d) = (n : ℚ) := by exact_mod_cast h2
  apply hdn
  refine ⟨n, ?_⟩
  rw [Algebra.traceForm_apply, h3]
  simp

/-- **Vanishing of the coefficients at non-integral forms**: if $f = \sum_Ta(T)e_T$ converges absolutely on $\mathbb H_r^d$ and $f$ is
invariant under $Z \mapsto Z + B$ for all $B \in \mathrm{Sym}_r(\mathfrak d^{-1})$, then $a(T) = 0$ for every $T$ with a coefficient outside
$\mathcal O_F$. -/
theorem coeff_eq_zero_of_not_int {a : QuadForm F r → ℂ}
    {f : (InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) → ℂ}
    (hsum : ∀ Z ∈ siegelHF F r, Summable fun T => ‖a T * eT T Z‖)
    (hexp : ∀ Z ∈ siegelHF F r, HasSum (fun T => a T * eT T Z) (f Z))
    (hper : ∀ B : Matrix (Fin r) (Fin r) F, Bᵀ = B → IsDualMat B → ∀ Z ∈ siegelHF F r, f (addB B Z) = f Z)
    (T : QuadForm F r) (hT : ¬ IsIntMat T.coeff) : a T = 0 := by
  obtain ⟨B, hBs, hBd, hne⟩ := exists_dualMat_eT_ne_one T hT
  have hadd : ∀ (T' : QuadForm F r) Z, eT T' (addB B Z) = eT T' Z * eT T' (realMat B) := by
    intro T' Z
    have : addB B Z = Z + realMat B := by funext w; rfl
    rw [this, eT_add]
  have hterm : ∀ Z (T' : QuadForm F r), a T' * eT T' (addB B Z) = (a T' * eT T' (realMat B)) * eT T' Z := by
    intro Z T'; rw [hadd]; ring
  have h := eq_of_hasSum_eT (a := fun T' => a T' * eT T' (realMat B)) (b := a) (f := f)
    (fun Z hZ => by
      have := hsum _ (addB_mem hBs hZ)
      simpa only [hterm] using this)
    hsum
    (fun Z hZ => by
      have := hexp _ (addB_mem hBs hZ)
      rw [hper B hBs hBd Z hZ] at this
      simpa only [hterm] using this)
    hexp
  have h1 := congrFun h T
  have h2 : a T * (eT T (realMat B) - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3) hne

end Global

end QuadFormsKB.SiegelWeil.Forms
