/-
# Siegel's $\Phi$ operator on the degree-$r$ theta series over a totally real field
**Layer:** global over a totally real number field $F$; classical analysis on $\mathbb H_{r+1}^d$ (no local input).

**Setting.** As in `ThetaR.lean`: $Q$ totally positive definite on $F^n$, $M \subseteq F^n$ a lattice, $Z = (Z_v)_v \in \mathbb H_r^d$. For real $t > 0$,
$$Z \oplus it = \Big(\begin{pmatrix} it & 0\\ 0 & Z_v\end{pmatrix}\Big)_v \in \mathbb H_{r+1}^d\qquad(\texttt{blockZ}\ Z\ t),$$
the new variable being the first one (index $0$, the others shifted by one: 0-based indices). For $X \in F^{n\times(r+1)}$ write $x_0$ for its
first column (`col0`) and $X'$ for the other $r$ columns (`colTail`).

**Results.**
* `blockZ_mem`: $Z \oplus it \in \mathbb H_{r+1}^d$ for $Z \in \mathbb H_r^d$, $t > 0$;
* `eT_blockZ`: $e_{Q[X]}(Z \oplus it) = e_{Q[X']}(Z)\exp\big(-2\pi t\sum_v\sigma_v(Q(x_0))\big)$;
* **`tendsto_thetaR_blockZ`** (Siegel's $\Phi$ operator): $\theta^{(r+1)}_M(Z \oplus it) \to \theta^{(r)}_M(Z)$ as $t \to \infty$;
* **`tendsto_thetaGenR_blockZ`**: the same for the genus average, $\Phi\,\theta^{(r+1)}_{\mathrm{gen}(L)} = \theta^{(r)}_{\mathrm{gen}(L)}$.

*Proof.* Dominated convergence for sums (Tannery): the terms with $x_0 = 0$ do not depend on $t$ and are those of $\theta^{(r)}_M(Z)$; the others
tend to $0$ because $\sum_v\sigma_v(Q(x_0)) > 0$; for $t \ge 1$ every term is bounded by its value at $t = 1$, which is summable
(`summable_norm_thetaRTerm` in degree $r + 1$).

Source: Siegel, *Einführung in die Theorie der Modulfunktionen n-ten Grades*, Math. Ann. 116 (1939), §§ on the operator $\Phi$
[unverified]; Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I [unverified]. In the Siegel–Weil comparison $\Phi$ lowers the degree:
$\Phi E^{(r+1)} = E^{(r)}$ and $\Phi\theta^{(r+1)}_{\mathrm{gen}} = \theta^{(r)}_{\mathrm{gen}}$ (Kudla, *Some extensions of the Siegel–Weil formula*
(2008), §1 [unverified]).
-/
import QuadFormsKB.SiegelWeil.Forms.ThetaR

open Matrix NumberField Complex Filter Topology
open QuadFormsKB.HilbertModular QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n r : ℕ}

/-- **The point $Z \oplus it$** of $\mathbb H_{r+1}^d$: at every real place $v$ the block matrix $\begin{pmatrix} it & 0\\ 0 & Z_v\end{pmatrix}$ (new index $0$). -/
def blockZ (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) :
    InfinitePlace F → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun v => Matrix.of fun i j =>
    Fin.cases (Fin.cases (I * t) (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => Z v i' j') j) i

@[simp] lemma blockZ_zero_zero (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (v : InfinitePlace F) :
    blockZ Z t v 0 0 = I * t := rfl
@[simp] lemma blockZ_zero_succ (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (v : InfinitePlace F) (j : Fin r) :
    blockZ Z t v 0 j.succ = 0 := rfl
@[simp] lemma blockZ_succ_zero (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (v : InfinitePlace F) (i : Fin r) :
    blockZ Z t v i.succ 0 = 0 := rfl
@[simp] lemma blockZ_succ_succ (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (v : InfinitePlace F) (i j : Fin r) :
    blockZ Z t v i.succ j.succ = Z v i j := rfl

/-- $Z \oplus it \in \mathbb H_{r+1}^d$ for $Z \in \mathbb H_r^d$ and $t > 0$. -/
lemma blockZ_mem {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) {t : ℝ} (ht : 0 < t) :
    blockZ Z t ∈ siegelHF F (r + 1) := by
  intro v
  obtain ⟨hsym, hY⟩ := hZ v
  refine ⟨?_, ?_⟩
  · ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · rfl
    · rfl
    · rfl
    · simpa using congrFun (congrFun hsym i') j'
  · set Y' := (Z v).map Complex.im
    have hY' := posDef_iff_dotProduct_mulVec.mp hY
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · ext i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · simp
      · simp
      · simp
      · have := congrFun (congrFun hY'.1 i') j'
        simpa [Y'] using this
    · set x' : Fin r → ℝ := fun i => x i.succ
      have key : star x ⬝ᵥ ((blockZ Z t v).map Complex.im *ᵥ x) = t * x 0 ^ 2 + star x' ⬝ᵥ (Y' *ᵥ x') := by
        simp only [dotProduct, mulVec, Fin.sum_univ_succ, Matrix.map_apply, blockZ_zero_zero, blockZ_zero_succ,
          blockZ_succ_zero, blockZ_succ_succ, Complex.zero_im, zero_mul, Finset.sum_const_zero, add_zero, x', Y',
          star_trivial]
        simp
        ring
      rw [key]
      by_cases h0 : x' = 0
      · have hx0 : x 0 ≠ 0 := by
          intro hx0; apply hx; funext i; refine Fin.cases hx0 (fun i' => ?_) i
          exact congrFun h0 i'
        rw [h0]; simp only [star_zero, zero_dotProduct, add_zero]; positivity
      · have := hY'.2 h0
        have : 0 ≤ t * x 0 ^ 2 := by positivity
        linarith

/-- The first column $x_0$ of $X \in F^{n\times(r+1)}$. -/
def col0 (X : Matrix (Fin n) (Fin (r + 1)) F) : Fin n → F := fun i => X i 0

/-- The last $r$ columns $X'$ of $X \in F^{n\times(r+1)}$. -/
def colTail (X : Matrix (Fin n) (Fin (r + 1)) F) : Matrix (Fin n) (Fin r) F := fun i j => X i j.succ

/-- $e_{Q[X]}(Z \oplus it) = e_{Q[X']}(Z)\exp\big(-2\pi t\sum_v\sigma_v(Q(x_0))\big)$. -/
lemma eT_blockZ (Q : QuadForm F n) (X : Matrix (Fin n) (Fin (r + 1)) F)
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (t : ℝ) :
    eT (Q.compMat X) (blockZ Z t) =
      eT (Q.compMat (colTail X)) Z * ((Real.exp (-(2 * Real.pi * t) * ∑ v, realEmb F v (Q.eval (col0 X))) : ℝ) : ℂ) := by
  have hG := gramT_compMat Q X
  have hG' := gramT_compMat Q (colTail X)
  have h00 : gramT (Q.compMat X) 0 0 = Q.eval (col0 X) := by
    rw [hG, eval_eq_gramT]
    simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, col0, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hss : ∀ i j, gramT (Q.compMat X) i.succ j.succ = gramT (Q.compMat (colTail X)) i j := by
    intro i j; rw [hG, hG']; rfl
  have htr : trPair (Q.compMat X) (blockZ Z t) =
      trPair (Q.compMat (colTail X)) Z + I * t * ∑ v, (realEmb F v (Q.eval (col0 X)) : ℂ) := by
    simp only [trPair, Fin.sum_univ_succ, blockZ_zero_zero, blockZ_zero_succ, blockZ_succ_zero, blockZ_succ_succ,
      mul_zero, Finset.sum_const_zero, add_zero, h00, hss, Finset.sum_add_distrib, Finset.mul_sum]
    rw [zero_add, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [eT, eT, htr, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Siegel's $\Phi$ operator on $\theta_M$:** $\theta^{(r+1)}_M(Z \oplus it) \to \theta^{(r)}_M(Z)$ as $t \to \infty$. -/
@[kb "siegel1939" "the operator Phi on theta series of degree r [unverified]"]
theorem tendsto_thetaR_blockZ {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (M : Lat F n)
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    Tendsto (fun t : ℝ => thetaR Q M.1 (blockZ Z t)) atTop (𝓝 (thetaR Q M.1 Z)) := by
  classical
  set S : frames M.1 (r + 1) → ℝ := fun X => ∑ v, realEmb F v (Q.eval (col0 X.1)) with hSdef
  have hpos : ∀ X : frames M.1 (r + 1), col0 X.1 ≠ 0 → 0 < S X := by
    intro X hX
    obtain ⟨v0⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hv : ∀ v, 0 < realEmb F v (Q.eval (col0 X.1)) := by
      intro v
      have h := hQ _ hX (complexEmb v)
      rw [complexEmb_apply] at h
      exact_mod_cast h
    exact Finset.sum_pos (fun v _ => hv v) ⟨v0, Finset.mem_univ _⟩
  have hS0 : ∀ X : frames M.1 (r + 1), 0 ≤ S X := by
    intro X
    by_cases hX : col0 X.1 = 0
    · simp [hSdef, hX, QuadForm.eval, QuadForm.evalIn]
    · exact (hpos X hX).le
  set g : frames M.1 (r + 1) → ℂ := fun X => if col0 X.1 = 0 then eT (Q.compMat (colTail X.1)) Z else 0 with hg
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (t : ℝ) (X : frames M.1 (r + 1)) => eT (Q.compMat X.1) (blockZ Z t)) (g := g)
    (bound := fun X => ‖eT (Q.compMat X.1) (blockZ Z 1)‖)
    (summable_norm_thetaRTerm hQ M.2 (blockZ_mem hZ one_pos))
    (fun X => by
      simp only [eT_blockZ]
      by_cases hX : col0 X.1 = 0
      · have h0 : Q.eval (0 : Fin n → F) = 0 := by simp [QuadForm.eval, QuadForm.evalIn]
        simp only [hg, hX, ite_true, h0, map_zero, Finset.sum_const_zero, mul_zero, Real.exp_zero,
          Complex.ofReal_one, mul_one]
        exact tendsto_const_nhds
      · simp only [hg, hX, ite_false]
        have hSp := hpos X hX
        have h1 : Tendsto (fun t : ℝ => -(2 * Real.pi * t) * S X) atTop atBot := by
          have h2 : Tendsto (fun t : ℝ => (2 * Real.pi * S X) * t) atTop atTop :=
            tendsto_id.const_mul_atTop (by positivity)
          refine (tendsto_neg_atTop_atBot.comp h2).congr fun t => ?_
          simp only [Function.comp_apply]; ring
        have h3 := (Complex.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_atBot.comp h1)
        have h4 := h3.const_mul (eT (Q.compMat (colTail X.1)) Z)
        simp only [Complex.ofReal_zero, mul_zero] at h4
        exact h4)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht X
      rw [eT_blockZ, eT_blockZ, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      gcongr
      have := hS0 X
      simp only [hSdef] at this
      nlinarith [Real.pi_pos])
  -- the limit sum is the degree-`r` theta series
  let ext : frames M.1 r → frames M.1 (r + 1) := fun X' =>
    ⟨fun i j => Fin.cases 0 (fun j' => X'.1 i j') j, fun j => by
      refine Fin.cases ?_ (fun j' => ?_) j
      · convert M.1.zero_mem using 1
        funext i; rfl
      · simpa using X'.2 j'⟩
  have hinj : Function.Injective ext := by
    intro X Y h
    apply Subtype.ext
    funext i j
    have := congrFun (congrFun (congrArg Subtype.val h) i) j.succ
    simpa [ext] using this
  have hsupp : Function.support g ⊆ Set.range ext := by
    intro X hX
    have hX0 : col0 X.1 = 0 := by
      by_contra h; exact hX (by simp [hg, h])
    refine ⟨⟨colTail X.1, fun j => X.2 j.succ⟩, ?_⟩
    apply Subtype.ext
    funext i j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simpa [ext, col0] using (congrFun hX0 i).symm
    · rfl
  have hgext : ∀ X', g (ext X') = eT (Q.compMat X'.1) Z := by
    intro X'
    have h0 : col0 (ext X').1 = 0 := by funext i; rfl
    simp only [hg, h0, ite_true]
    rfl
  have hlim : ∑' X, g X = thetaR Q M.1 Z := by
    rw [← hinj.tsum_eq hsupp]
    simp only [hgext]
    rfl
  rw [← hlim]
  exact hT

/-- **Siegel's $\Phi$ operator on the genus average:** $\theta^{(r+1)}_{\mathrm{gen}(L)}(Z \oplus it) \to \theta^{(r)}_{\mathrm{gen}(L)}(Z)$. -/
@[kb "siegel1939" "the operator Phi on the genus theta series [unverified]"]
theorem tendsto_thetaGenR_blockZ {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    Tendsto (fun t : ℝ => thetaGenR Q L (blockZ Z t)) atTop (𝓝 (thetaGenR Q L Z)) := by
  have hfin := genusClasses_finite hQ L hLi
  simp only [thetaGenR, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun c _ => Tendsto.const_mul _ ?_)
  exact tendsto_thetaR_blockZ hQ c.out hZ

end QuadFormsKB.SiegelWeil.Forms
