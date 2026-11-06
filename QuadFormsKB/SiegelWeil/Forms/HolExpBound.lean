/-
# A uniform majorant of the holomorphic Siegel Eisenstein series on compact sets
**Layer:** global over a totally real number field $F$.

**Setting.** As in `PhiEisenstein.lean`: $\mathcal E^{(r)}(Z) = \sum_qh(Z, q)$ with $h(Z, P\gamma) = j(\gamma, Z)^{-m}f_f(\gamma, s_0)$ (`holQ`),
$m > 4r^2$, $r \ge 1$.

**Result.** **`exists_holQ_majorant`**: for compact sets $S_w \subseteq \mathbb H_r$ (one per real place $w$) there are $M \ge 0$ and a summable
$G \ge 0$ on $P(F)\backslash\mathrm{Sp}_{2r}(F)$ with $|h(Z, q)| \le M\,G(q)$ for every $Z$ with $Z_w \in S_w$ for all $w$. *Proof:* the majorant
`exists_norm_globalSecR_le` is $\prod_w\det(\operatorname{Im}Z_w)^{\tau/2}K(\prod_wc_w/2^d)^{-\tau}G(q)$ with $\tau = \operatorname{Re}s_0 + \rho_r = m$, so
dividing by $\prod_w\det(\operatorname{Im}Z_w)^{m/2}$ leaves a bound depending on $Z$ only through the constants $c_w$, which are uniform on
$S_w$ by `exists_norm_det_CZD_ge_unif`.

Consequences (Weierstrass test): continuity and separate holomorphy of $\mathcal E^{(r)}$, and boundedness on compact sets.

Source: Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (convergence of Eisenstein series) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.PhiEisenstein
import QuadFormsKB.SiegelWeil.Forms.EisensteinMajorant
import QuadFormsKB.SiegelWeil.Forms.EisensteinArchUniform

open Matrix NumberField Filter Topology
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

lemma sZero_re_add (m r : ℕ) : (sZero m r).re + ((r : ℝ) + 1) / 2 = m := by
  simp [sZero]

lemma norm_prodIm {Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelHF F r) :
    ‖prodIm m Z‖ = ∏ w, ((Z w).map Complex.im).det ^ ((m : ℝ) / 2) := by
  unfold prodIm
  rw [norm_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (det_im_pos hZ w)]
  congr 1
  simp

/-- **A majorant of the terms of $\mathcal E^{(r)}$, uniform on compact sets.** -/
theorem exists_holQ_majorant (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (hr : 1 ≤ r) (hm : 4 * (r : ℝ) ^ 2 < m)
    {S : InfinitePlace F → Set (Matrix (Fin r) (Fin r) ℂ)} (hS : ∀ w, IsCompact (S w)) (hSH : ∀ w, S w ⊆ siegelH r) :
    ∃ (M : ℝ) (G : PQuot r F → ℝ), Summable G ∧ (∀ q, 0 ≤ G q) ∧
      ∀ Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ, (∀ w, Z w ∈ S w) → ∀ q, ‖holQ b hb hbpos Z q‖ ≤ M * G q := by
  obtain ⟨K, G, -, hG, hG0, hmaj⟩ := exists_norm_globalSecR_le b hb hbpos (fun v => oneSG v m r)
    (Filter.Eventually.of_forall fun _ => rfl) hr (sZero_hs hm)
  choose c hc using fun w => exists_norm_det_CZD_ge_unif (hS w) (hSH w)
  refine ⟨K * ((∏ w, c w) / 2 ^ Fintype.card (InfinitePlace F)) ^ (-(m : ℝ)), G, hG, hG0, fun Z hZS q => ?_⟩
  have hZ : Z ∈ siegelHF F r := fun w => hSH w (hZS w)
  have h1 := hmaj Z hZ c (fun w => (hc w).1) (fun w => (hc w).2 (Z w) (hZS w)) q
  rw [sZero_re_add] at h1
  have hP : 0 < ∏ v, ((Z v).map Complex.im).det ^ ((m : ℝ) / 2) :=
    Finset.prod_pos fun w _ => Real.rpow_pos_of_pos (det_im_pos hZ w) _
  rw [holQ, norm_div, norm_prodIm hZ, div_le_iff₀ hP, eisTermR_eq_out]
  calc ‖globalSecR (unitsOfInt b hb) (fun v => oneSG v m r) (archSecR m Z (sZero m r)) (sZero m r) q.out‖
      ≤ (∏ v, ((Z v).map Complex.im).det ^ ((m : ℝ) / 2)) * K *
          ((∏ w, c w) / 2 ^ Fintype.card (InfinitePlace F)) ^ (-(m : ℝ)) * G q := h1
    _ = _ := by ring

end QuadFormsKB.SiegelWeil.Forms
