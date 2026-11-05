/-
# Periodicity of the holomorphic Siegel Eisenstein series (Siegel–Weil for forms by forms)

**Layer:** global over a totally real number field $F$.

**Setting.** As in `PhiEisenstein.lean`: $\mathcal E^{(r)}(Z) = \sum_{\gamma\in P(F)\backslash\mathrm{Sp}_{2r}(F)}j(\gamma, Z)^{-m}f_f(\gamma, s_0)$ (`eisHolR`), the
lattice function $\Phi_v = \mathbf 1_{L_v^r}$ at every finite place. For $B$ symmetric over $F$, $Z + B$ is $(Z_w + \sigma_w(B))_w$ (`addB`).

**Results.**
* `denR_addB`: $j(\gamma, Z + B) = j(\gamma n(B), Z)$ (the blocks of $\gamma n(B)$ are $C$ and $CB + D$).
* **`eisHolR_addB`**: $\mathcal E^{(r)}(Z + B) = \mathcal E^{(r)}(Z)$ for $B \in \mathrm{Sym}_r(\mathcal O_F)$ and $Z \in \mathbb H_r^d$ (reindexing
  $P(F)\gamma \mapsto P(F)\gamma n(B)$, `pquotMulRight`; $f_f(\gamma n(B), s_0) = f_f(\gamma, s_0)$ is `finSecR_mul_spN_int`).

Source: Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 [unverified]; Klingen, *Introductory lectures on Siegel
modular forms* (1990), §5 [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.PhiEisenstein

open Matrix NumberField Filter Topology
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- $Z + B = (Z_w + \sigma_w(B))_w$. -/
def addB (B : Matrix (Fin r) (Fin r) F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    InfinitePlace F → Matrix (Fin r) (Fin r) ℂ :=
  fun w => Z w + B.map fun x => (realEmb F w x : ℂ)

lemma addB_mem {B : Matrix (Fin r) (Fin r) F} (hB : Bᵀ = B) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelHF F r) : addB B Z ∈ siegelHF F r := by
  intro w
  obtain ⟨hs, hY⟩ := hZ w
  refine ⟨?_, ?_⟩
  · rw [addB, Matrix.transpose_add, hs, ← Matrix.transpose_map, hB]
  · have : (addB B Z w).map Complex.im = (Z w).map Complex.im := by
      ext i j; simp [addB]
    rw [this]; exact hY

lemma blockCD_mul_spN (γ : Sp r F) (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) :
    blockC (γ * spN B hB) = blockC γ ∧ blockD (γ * spN B hB) = blockC γ * B + blockD γ := by
  have e : ((γ * spN B hB : Sp r F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      fromBlocks (blockA γ) (blockB γ) (blockC γ) (blockD γ) * fromBlocks 1 B 0 1 := by
    rw [← spN_coe B hB, ← eq_fromBlocks]; rfl
  constructor
  · show ((γ * spN B hB : Sp r F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).toBlocks₂₁ = _
    rw [e, fromBlocks_multiply, toBlocks_fromBlocks₂₁, Matrix.mul_one, Matrix.mul_zero, add_zero]
  · show ((γ * spN B hB : Sp r F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).toBlocks₂₂ = _
    rw [e, fromBlocks_multiply, toBlocks_fromBlocks₂₂, Matrix.mul_one]

/-- $j(\gamma, Z + B) = j(\gamma n(B), Z)$. -/
lemma denR_addB (γ : Sp r F) (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    denR γ (addB B Z) = denR (γ * spN B hB) Z := by
  unfold denR
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain ⟨hC, hD⟩ := blockCD_mul_spN γ B hB
  rw [denW, denW, hC, hD, addB, Matrix.mul_add]
  have hm : ((blockC γ * B + blockD γ).map fun x => (realEmb F w x : ℂ)) =
      ((blockC γ).map fun x => (realEmb F w x : ℂ)) * (B.map fun x => (realEmb F w x : ℂ)) +
        (blockD γ).map fun x => (realEmb F w x : ℂ) := by
    rw [← map_mul_emb]; ext i j; simp
  rw [hm, add_assoc]

/-- **Periodicity**: $\mathcal E^{(r)}(Z + B) = \mathcal E^{(r)}(Z)$ for $B \in \mathrm{Sym}_r(\mathcal O_F)$, $Z \in \mathbb H_r^d$. -/
theorem eisHolR_addB (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {B : Matrix (Fin r) (Fin r) F} (hB : Bᵀ = B) (hBi : IsIntMat B) {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ siegelHF F r) : eisHolR b hb hbpos (addB B Z) = eisHolR b hb hbpos Z := by
  have hZ' := addB_mem hB hZ
  have hterm : ∀ q : PQuot r F, holQ b hb hbpos (addB B Z) q = holQ b hb hbpos Z (pquotMulRight (spN B hB) q) := by
    intro q
    induction q using Quotient.inductionOn with
    | h γ =>
      rw [pquotMulRight_mk, holQ_mk b hb hbpos hZ', holQ_mk b hb hbpos hZ, holTermR, holTermR, denR_addB γ B hB,
        finSecR_mul_spN_int b hb γ B hB hBi]
  rw [eisHolR, eisHolR]
  simp only [hterm]
  exact (pquotMulRight (spN B hB)).tsum_eq (holQ b hb hbpos Z)

end QuadFormsKB.SiegelWeil.Forms
