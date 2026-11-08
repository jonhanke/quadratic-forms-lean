/-
# O'Meara §101B, Example 101:10: $\operatorname{cls}^+K \ne \operatorname{cls}K$ for even $n$

**Layer:** $F$ a number field, $V = F^n$ with a nondegenerate `Q : QuadForm F n`, lattices `Lat F n`, classes
`IsIsometric` / `IsProperIsometric`; local lattices at the finite spots in O'Meara's terms (`Sec101TenAux.lean`).

**Proves**
* `exists_lat_det_ne_neg_one`: for even $n \ge 2$ some lattice $K$ has $O^+(K) = O(K)$ (O'Meara's construction from
  65:20, 92:8 and 81:14);
* `omeara101_10 : OMeara101_10 F` (**Example 101:10**, the named statement of `Sec101Named.lean`). Unconditional.
-/
import QuadFormsKB.Literature.OMeara.Sec101TenAux
import QuadFormsKB.Literature.OMeara.Sec42Index

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open OMeara.QIn (glEquiv)

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### Example 101:10 -/

section Main

theorem qk_self_eq : qk Q F = QuadForm.toQuadraticForm Q := by
  ext x
  rw [qk_apply, QuadForm.toQuadraticForm_apply]

/-- The matrix $G = (B(e_i, e_j))$ of the standard base of a regular $V = F^n$ is invertible. -/
theorem det_gram_single_ne_zero (hQ : Q.Nondegenerate) :
    (OMeara.gram (QuadForm.toQuadraticForm Q) (fun i => (Pi.single i 1 : Fin n → F))).det ≠ 0 := by
  have hnd : (QuadraticMap.associated (qk Q F)).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr
      (QuadraticMap.nondegenerate_polar_iff.mp (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn F hQ))
  have h := OMeara.det_gram_ne_zero_of_regular (qk Q F) hnd (Pi.basisFun F (Fin n))
  rwa [OMeara.basisFun_coe, qk_self_eq] at h

/-- **The lattice $K$ of Example 101:10** (O'Meara 1973, §101B, pp. 292–293): for a regular $V = F^n$ with $n \ge 2$
even, there is a lattice $K$ on $V$ with $O^+(K) = O(K)$, i.e. no $\sigma \in O(V)$ with $\sigma K = K$ has
$\det\sigma = -1$.

*Proof* (O'Meara's). Let $G$ be the matrix of the standard base and $c = \det G$ (so $dV = c$). Choose a set $S$ of
spots as in §65 (non-dyadic, almost all spots, $J_F = P_FJ_F^S$; O'Meara's $W$) at which $c$ and the non-zero entries
of $G$ are units (`exists_sConventions_strong`); then $L_\mathfrak p = \mathfrak o_\mathfrak p^n$ is unimodular for
$\mathfrak p \in S$. By 65:20 pick $\mathfrak q \ne \mathfrak q'$ in $S$ at which $c$ is a square and at which the same
$S$-units are squares. By 92:8 there are lattices $K_\mathfrak q$, $K_{\mathfrak q'}$ with
$\theta(O^-(K_\mathfrak q)) \subseteq \Delta F_\mathfrak q^{\times 2}$ ($\Delta$ a non-square unit) and
$\theta(O^-(K_{\mathfrak q'})) \subseteq F_{\mathfrak q'}^{\times 2}$; glue them with $\mathfrak o_\mathfrak p^n$ elsewhere
(81:14). If $\sigma K = K$ with $\det\sigma = -1$ and $\theta(\sigma) = a$, then $\operatorname{ord}_\mathfrak p a$ is even
for $\mathfrak p \in S$ (92:5 at the unimodular $\mathfrak o_\mathfrak p^n$, and at $\mathfrak q, \mathfrak q'$), so
$a/\beta^2$ is an $S$-unit for some $\beta$ ($J_F = P_FJ_F^S$); it is a square at $\mathfrak q'$ but not at $\mathfrak q$,
contradicting the choice of $\mathfrak q, \mathfrak q'$.

*Update:* O'Meara also requires $S_\mathfrak pV = 1$ on $W$; this is not needed, since at $\mathfrak q$ the unimodular
$L_\mathfrak q$ and the square discriminant already give $V_\mathfrak q \cong \langle 1, \dots, 1\rangle$ (92:2), which is
what 92:8 uses. -/
theorem exists_lat_det_ne_neg_one (hQ : Q.Nondegenerate) (hn : 2 ≤ n) (hev : Even n) :
    ∃ K : Lat F n, ∀ σ : orthGroup Q F, glImage (σ : GL (Fin n) F) K.1 = K.1 →
      ((σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det ≠ -1 := by
  classical
  set G := OMeara.gram (QuadForm.toQuadraticForm Q) (fun i => (Pi.single i 1 : Fin n → F)) with hGdef
  have hG0 : G.det ≠ 0 := det_gram_single_ne_zero Q hQ
  set Θ : Finset F :=
    insert G.det ((Finset.univ.image fun p : Fin n × Fin n => G p.1 p.2).filter (· ≠ 0)) with hΘ
  have hΘ0 : ∀ θ ∈ Θ, θ ≠ 0 := by
    intro θ hθ
    rcases Finset.mem_insert.mp hθ with rfl | h
    · exact hG0
    · exact (Finset.mem_filter.mp h).2
  obtain ⟨S, hS, hΘS, -⟩ := OMeara.exists_sConventions_strong (F := F) F Θ hΘ0
  set T := hS.cofinite.toFinset with hT
  have hTS : ∀ w, w ∉ T ↔ w ∈ S := fun w => by simp [hT]
  have hdetS : ∀ w ∈ S, w.valuation F G.det = 1 := fun w hw =>
    hΘS _ (Finset.mem_insert_self _ _) w hw
  have hentS : ∀ w ∈ S, ∀ i j, G i j ≠ 0 → w.valuation F (G i j) = 1 := fun w hw i j h =>
    hΘS _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩, h⟩)) w hw
  have h2S : ∀ w ∈ S, IsUnit (2 : w.adicCompletionIntegers F) := fun w hw =>
    Hanke2011Structure.isUnit_two_of_not_mem w (hS.nondyadic w hw)
  have hUS : ∀ w ∈ S, OMeara.IsUnimodular (qk Q (w.adicCompletion F))
      (std w : Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F)) :=
    fun w hw => isUnimodular_std Q w (by omega) (hentS w hw) (hdetS w hw)
  have hsqw : ∀ w, OMeara.SqAt w G.det → IsSquare (OMeara.gram (qk Q (w.adicCompletion F))
      (fun i => (Pi.single i 1 : Fin n → w.adicCompletion F))).det := by
    intro w hw
    rw [gram_qk_single, show (G.map (algebraMap F (w.adicCompletion F))).det =
      algebraMap F (w.adicCompletion F) G.det from (RingHom.map_det _ G).symm]
    exact hw
  -- Proposition 65:20
  let cU : HN.SUnit (F := F) T := ⟨Units.mk0 G.det hG0, fun w hw => hdetS w ((hTS w).mp hw)⟩
  obtain ⟨q, q', hqq', hqT, hq'T, hcq, hcq', htwin⟩ := OMeara.exists_twin_spots T cU
  have hqS := (hTS q).mp hqT
  have hq'S := (hTS q').mp hq'T
  -- Example 92:8 at every spot of `S` where `c` is a square
  have hloc : ∀ (w : HeightOneSpectrum (𝓞 F)) (ε : w.adicCompletionIntegers F),
      ∃ M : Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F),
        M.IsLattice (w.adicCompletion F) ∧
        (w ∈ S → OMeara.SqAt w G.det → IsUnit ε → ∀ σ ∈ OMeara.orthLat (qk Q (w.adicCompletion F)) M,
          LinearEquiv.det σ = -1 → ∀ c, OMeara.HasSpinorNorm (qk Q (w.adicCompletion F)) σ c →
            ∃ s, s ≠ 0 ∧ c = algebraMap _ (w.adicCompletion F) ε * s ^ 2) := by
    intro w ε
    by_cases h : w ∈ S ∧ OMeara.SqAt w G.det ∧ IsUnit ε
    · obtain ⟨M, hM, hMi⟩ :=
        exists_local_improper Q w hQ hn hev (h2S w h.1) (hUS w h.1) (hsqw w h.2.1) h.2.2
      exact ⟨M, hM, fun _ _ _ => hMi⟩
    · exact ⟨std w, isLattice_of_bounds w le_rfl le_rfl, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose Ml hMl hMli using hloc
  -- non-square units
  have hns : ∀ w : HeightOneSpectrum (𝓞 F), ∃ Δ : w.adicCompletionIntegers F,
      w ∈ S → IsUnit Δ ∧ ¬ IsSquare Δ := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨Δ, hΔ, hΔn, -⟩ := OMeara.exists_nonsquare_unit (h2S w hw)
      exact ⟨Δ, fun _ => ⟨hΔ, hΔn⟩⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose Δf hΔf using hns
  let εf : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletionIntegers F := fun w => if w = q then Δf w else 1
  have hεu : ∀ w ∈ S, IsUnit (εf w) := by
    intro w hw
    simp only [εf]
    split_ifs
    · exact (hΔf w hw).1
    · exact isUnit_one
  -- the glued lattice (81:14)
  let fam : LocFamily F n :=
    { M := fun w => if w = q ∨ w = q' then Ml w (εf w) else std w
      isLattice := fun w => by
        split_ifs
        · exact hMl w _
        · exact isLattice_of_bounds w le_rfl le_rfl
      eventually_std := by
        refine Filter.eventually_cofinite.mpr
          (((Set.finite_singleton q).union (Set.finite_singleton q')).subset ?_)
        intro w hw
        by_contra hc
        simp only [Set.mem_union, Set.mem_singleton_iff] at hc
        simp only [Set.mem_ofPred_eq] at hw
        rw [if_neg hc] at hw
        exact hw rfl }
  refine ⟨⟨fam.glue, fam.glue_isLattice⟩, fun σ hσK hdet => ?_⟩
  obtain ⟨a, ha0, hsn⟩ := exists_hasSpinorNorm_orthMap Q hQ σ
  have hτ : ∀ w : HeightOneSpectrum (𝓞 F), glEquiv (w.adicCompletion F) ((orthMap Q (w.adicCompletion F) σ : orthGroup Q _) :
      GL (Fin n) _) ∈ OMeara.orthLat (qk Q _) (fam.M w) := fun w => by
    rw [← fam.loc_glue w]; exact glEquiv_orthMap_mem_orthLat Q w hσK
  have hτdet : ∀ w : HeightOneSpectrum (𝓞 F), LinearEquiv.det (glEquiv (w.adicCompletion F)
      ((orthMap Q (w.adicCompletion F) σ : orthGroup Q _) : GL (Fin n) _)) = -1 := fun w => by
    apply det_glEquiv_eq_neg_one (F := F)
    rw [orthMap_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_neg, map_one]
  have hspec : ∀ w : HeightOneSpectrum (𝓞 F), (w = q ∨ w = q') → ∃ s : w.adicCompletion F, s ≠ 0 ∧
      algebraMap F _ a = algebraMap _ _ (εf w) * s ^ 2 := by
    intro w hw
    have hwS : w ∈ S := by rcases hw with rfl | rfl; exacts [hqS, hq'S]
    have hwsq : OMeara.SqAt w G.det := by rcases hw with rfl | rfl; exacts [hcq, hcq']
    have hM : fam.M w = Ml w (εf w) := if_pos hw
    exact hMli w (εf w) hwS hwsq (hεu w hwS) _ (hM ▸ hτ w) (hτdet w) _ (hsn w)
  have heven : ∀ w ∈ S, ∃ k : ℤ, w.valuation F a = WithZero.exp (2 * k) := by
    intro w hwS
    by_cases hw : w = q ∨ w = q'
    · obtain ⟨s, hs, h⟩ := hspec w hw
      exact exists_valuation_eq_exp_two_mul w (hεu w hwS) hs h
    · have hM : fam.M w = std w := if_neg hw
      have hτw := hτ w
      rw [hM] at hτw
      have hnd := nondegenerate_qk Q w hQ
      have hstd : (std w : Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F)).IsLattice
          (w.adicCompletion F) := isLattice_of_bounds w le_rfl le_rfl
      have hfr : 1 ≤ Module.finrank (w.adicCompletion F) (Fin n → w.adicCompletion F) := by
        rw [Module.finrank_fin_fun]; omega
      obtain ⟨ε, hε, hεn⟩ := OMeara.exists_hasSpinorNorm_unit_of_isUnimodular
        (R := w.adicCompletionIntegers F) (qk Q (w.adicCompletion F)) (h2S w hwS) hnd hfr hstd (hUS w hwS) hτw
      obtain ⟨s, hs, h⟩ := OMeara.HasSpinorNorm.eq_mul_sq (qk Q (w.adicCompletion F)) hnd (hsn w) hεn
      exact exists_valuation_eq_exp_two_mul w hε hs h
  obtain ⟨β, hβ0, hβ⟩ := OMeara.exists_div_sq_valuation_eq_one hS subset_rfl ha0 heven
  have hδ0 : a / β ^ 2 ≠ 0 := div_ne_zero ha0 (pow_ne_zero 2 hβ0)
  let δ : HN.SUnit (F := F) T := ⟨Units.mk0 (a / β ^ 2) hδ0, fun w hw => hβ w ((hTS w).mp hw)⟩
  have hsq' : OMeara.SqAt q' (a / β ^ 2) := by
    obtain ⟨s, hs, h⟩ := hspec q' (Or.inr rfl)
    have h1 : εf q' = 1 := if_neg (Ne.symm hqq')
    rw [h1, map_one, one_mul] at h
    refine ⟨s / algebraMap F _ β, ?_⟩
    rw [map_div₀, map_pow, h]
    ring
  have hsq : OMeara.SqAt q (a / β ^ 2) := (htwin δ).mpr hsq'
  obtain ⟨s, hs, h⟩ := hspec q (Or.inl rfl)
  have h1 : εf q = Δf q := if_pos rfl
  rw [h1] at h
  apply (hΔf q hqS).2
  apply isSquare_of_isSquare_algebraMap q (hΔf q hqS).1
  obtain ⟨r, hr⟩ := hsq
  have hb : algebraMap F (q.adicCompletion F) β ≠ 0 := (map_ne_zero _).mpr hβ0
  rw [map_div₀, map_pow, h, div_eq_iff (pow_ne_zero 2 hb)] at hr
  refine ⟨r * algebraMap F _ β / s, ?_⟩
  field_simp
  linear_combination hr

/-- **Example 101:10** (O'Meara 1973, §101B, pp. 292–293): the named statement `OMeara101_10 F` holds for every
number field $F$: if $V = F^n$ is regular with $n \ge 2$ even, there is a lattice $K$ on $V$ with
$\operatorname{cls}^+K \ne \operatorname{cls}K$. Unconditional.

*Proof* (O'Meara's). Take $K$ with $O^+(K) = O(K)$ (`exists_lat_det_ne_neg_one`) and a symmetry $\tau$ of $V$: then
$\tau K \in \operatorname{cls}K$, and $\tau K = \gamma K$ with $\gamma$ proper would give the improper unit
$\tau^{-1}\gamma \in O(K)$. -/
@[kb "omeara1963" "§101B, 101:10, pp. 292–293"]
theorem omeara101_10 : OMeara101_10 F := by
  refine ⟨fun n Q hQ hn hev => ?_⟩
  obtain ⟨K, hK⟩ := exists_lat_det_ne_neg_one Q hQ hn hev
  obtain ⟨x, hx⟩ := ArchTest.exists_evalIn_ne_zero hQ (by omega)
  let τ : orthGroup Q F := symm Q F x
  refine ⟨K, ⟨glImage (τ : GL (Fin n) F) K.1, glImage_isLattice _ K.2⟩, ⟨τ, τ.2, rfl⟩, ?_⟩
  rintro ⟨γ, hγ, hγK⟩
  apply hK (τ⁻¹ * γ)
  · rw [Subgroup.coe_mul, glImage_mul, hγK, Subgroup.coe_inv, ← glImage_mul, inv_mul_cancel, glImage_one]
  · have h1 := symm_det Q F hx
    have h2 := Tamagawa.mem_soSub.mp hγ
    have e := congrArg Units.val
      (show detHom Q F (τ⁻¹ * γ) = (detHom Q F τ)⁻¹ * detHom Q F γ by rw [map_mul, map_inv])
    rw [Units.val_mul, Units.val_inv_eq_inv_val, detHom_val, detHom_val, detHom_val] at e
    rw [e, h2]
    have h1' : ((τ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = -1 := h1
    rw [h1']
    norm_num

end Main

end QuadFormsKB.Lattices
