/-
# The Siegel–Weil identity $\mathcal E^{(r)} = \theta^{(r)}_{\mathrm{gen}(L)}$ from the Fourier expansion of $E$

**Layer:** global over a totally real number field $F$ whose ring of integers is a principal ideal domain.

**Setting.** $Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F$ totally positive, $n = 2m$ (0-based indices); $\mathcal E^{(r)}(Z) =
\det(\operatorname{Im}Z)^{-m/2}E^{(r)}(g_Z, s_0, \Phi)$ (`eisHolR`, `PhiEisenstein.lean`) with $\Phi_v = \mathbf 1_{L_v^r}$; on the theta side any
totally positive definite form $Q'$ on $F^n$ and any lattice $L$ on which $Q'$ is integral (in the application $Q' = Q$ and $L = \mathcal O_F^n$).
$R$ is the target degree and $m > 4R^2$ (the range where the convergence `summable_norm_eisTermR` holds in every degree $r \le R$).

**Results.**
* `repCountT_zero`, `repMassT_zero`: in degree $0$, $r_M(\varnothing) = 1$ and $\mathrm{repMassT}(L, \varnothing) = \mathrm{Mass}(L)$.
* **`eisHolR_eq_thetaGenR_of_expansion`**: suppose that for every $r \le R$ the series $\mathcal E^{(r)}$ has an absolutely convergent Fourier
  expansion $\sum_Ta_r(T)e_T$ on $\mathbb H_r^d$, supported on totally positive semidefinite forms, and that $a_r(T) =
  \mathrm{repMassT}(L, T)/\mathrm{Mass}(L)$ for every $T$ with $\det T_G \ne 0$ and $1 \le r \le R$. Then $\mathcal E^{(r)} = \theta^{(r)}_{\mathrm{gen}(L)}$
  on $\mathbb H_r^d$ for every $r \le R$. The remaining fields of `IsPhiFamily` are proved: invariance `eisHolR_actU`, Siegel's $\Phi$
  `tendsto_eisHolR_blockZ`, and degree $0$ (`eisHolR_zero`, `repMassT_zero`).

The two hypotheses are exactly the open Eisenstein-side items: the Fourier expansion of $E$ and the nonsingular
coefficients (`coeffR_eisBigR_eq_thetaCoeff` for the big cell plus the vanishing of the lower cells). They are
hypotheses of this reduction lemma, not cited inputs.

Sources: Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965) [unverified]; Klingen,
*Introductory lectures on Siegel modular forms* (1990), §5 [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.PhiEisenstein

open Matrix NumberField Filter Topology
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Frames

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

instance : Subsingleton (QuadForm F 0) := ⟨fun T T' => by ext i; exact i.elim0⟩

/-- $r_M(\varnothing) = 1$: the empty frame. -/
lemma repCountT_zero (Q : QuadForm F n) (M : Lat F n) (T : QuadForm F 0) : repCountT Q M T = 1 := by
  unfold repCountT
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, fun j => j.elim0, Subsingleton.elim _ _⟩, fun X => Subtype.ext ?_⟩
  ext i j; exact j.elim0

/-- $\mathrm{repMassT}(L, \varnothing) = \mathrm{Mass}(L)$. -/
lemma repMassT_zero (Q : QuadForm F n) (L : Lat F n) (T : QuadForm F 0) : repMassT Q L T = mass Q L := by
  unfold repMassT mass
  refine finsum_mem_congr rfl fun c _ => ?_
  rw [latClass_repCountT_eq, repCountT_zero, Nat.cast_one, one_div]

lemma eT_zero (T : QuadForm F 0) (Z : InfinitePlace F → Matrix (Fin 0) (Fin 0) ℂ) : eT T Z = 1 := by
  simp [eT, trPair]

lemma zero_mem_siegelHF : (fun _ => 0 : InfinitePlace F → Matrix (Fin 0) (Fin 0) ℂ) ∈ siegelHF F 0 := by
  intro w
  refine ⟨Subsingleton.elim _ _, ?_⟩
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  exact ⟨by ext i; exact i.elim0, fun x hx => absurd (Subsingleton.elim x 0) hx⟩

/-- **The Siegel–Weil identity in degrees $r \le R$ from the Fourier expansion of $E$** ($\mathcal O_F$ a principal ideal domain,
$m > 4R^2$): given absolutely convergent expansions $\mathcal E^{(r)} = \sum_Ta_r(T)e_T$ supported on totally positive semidefinite forms whose
nonsingular coefficients are Siegel's $\mathrm{repMassT}(L, T)/\mathrm{Mass}(L)$ ($1 \le r \le R$), $\mathcal E^{(r)} = \theta^{(r)}_{\mathrm{gen}(L)}$. -/
@[kb "weil1965" "Ch. II–IV (the Siegel–Weil formula from the Fourier coefficients and Siegel's Φ operator) [unverified]"]
theorem eisHolR_eq_thetaGenR_of_expansion [IsPrincipalIdealRing (𝓞 F)] {m : ℕ} (b : Fin (2 * m) → 𝓞 F)
    (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) {Q : QuadForm F n} (hQ : IsTotallyPosDef Q)
    (L : Lat F n) (hLi : IsIntegral Q L.1) (R : ℕ) (hm : 4 * (R : ℝ) ^ 2 < m) (a : ∀ r : ℕ, QuadForm F r → ℂ)
    (hsum : ∀ r ≤ R, ∀ Z ∈ siegelHF F r, Summable fun T => ‖a r T * eT T Z‖)
    (hexp : ∀ r ≤ R, ∀ Z ∈ siegelHF F r, HasSum (fun T => a r T * eT T Z) (eisHolR (r := r) b hb hbpos Z))
    (hpsd : ∀ r ≤ R, ∀ T, a r T ≠ 0 → IsTotPSD T)
    (hfull : ∀ r, 1 ≤ r → r ≤ R → ∀ T : QuadForm F r, (gramT T).det ≠ 0 →
      a r T = ((repMassT Q L T / mass Q L : ℝ) : ℂ)) :
    ∀ r ≤ R, ∀ Z ∈ siegelHF F r, eisHolR b hb hbpos Z = thetaGenR Q L Z := by
  have hfam : IsPhiFamily R a (fun r => eisHolR (r := r) b hb hbpos) :=
    ⟨hsum, hexp, hpsd, fun r _ U hU Z hZ => eisHolR_actU b hb hbpos hU hZ, fun r hr Z hZ => by
      refine tendsto_eisHolR_blockZ b hb hbpos hZ ?_
      have h1 : ((r : ℝ) + 1) ≤ R := by exact_mod_cast hr
      have h0 : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
      nlinarith⟩
  refine eq_thetaGenR_of_coeff_full_rank hQ L hLi hfam fun r hr T hT => ?_
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    have h1 := hexp 0 (Nat.zero_le _) _ zero_mem_siegelHF
    rw [eisHolR_zero b hb hbpos zero_mem_siegelHF] at h1
    have h2 : HasSum (fun T' : QuadForm F 0 => a 0 T' * eT T' (fun _ => 0)) (a 0 T) := by
      have := hasSum_single (f := fun T' : QuadForm F 0 => a 0 T' * eT T' (fun _ => 0)) T
        (fun T' hT' => absurd (Subsingleton.elim T' T) hT')
      simpa [eT_zero] using this
    rw [h2.unique h1, repMassT_zero, div_self (mass_pos hQ L hLi).ne', Complex.ofReal_one]
  · exact hfull r hpos hr T hT

end QuadFormsKB.SiegelWeil.Forms
