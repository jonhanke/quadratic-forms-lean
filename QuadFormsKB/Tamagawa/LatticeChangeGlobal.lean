/-
# the $\tau(SO)$ does not depend on the lattice

**Layer:** a totally real number field $F$; the Tamagawa number `tauSO` of a form over $\mathcal O_F$ (computed with the
standard lattice $\mathcal O_F^n$).

$\tau(SO(V)) = \mu_{\mathrm{Tam}}(K_{SO})\cdot\mathrm{mass}_{SO}$ is defined with the lattice $L = \mathcal O_F^n$ of the form $Q_0$. A
different lattice $M = g\mathcal O_F^n$ in the same space, or a rescaling, is the form $Q_1 = c\,(Q_0\circ g)$. This file proves
$\tau(Q_1) = \tau(Q_0)$:
* `mass_similar`: $\mathrm{Mass}(c\,(Q\circ g), L) = \mathrm{Mass}(Q, gL)$ (similar spaces, transported classes and genera);
* `mass_image_eq`: $\mathrm{Mass}(Q, M) = \mathrm{Mass}(Q, L)\cdot\prod_\mathfrak p r_\mathfrak p$, $r_\mathfrak p = [O(L_\mathfrak p) : \cap]/[O(M_\mathfrak p) : \cap]$
  (`mass_mul_vol_eq` and the restricted-product index);
* the local identity (`localDensity_mul_relRatio`) at every prime and the product formula for the Jacobians;
* **`tauSO_smul_compMat_diagonal`**: $\tau(c\,(Q_0\circ D)) = \tau(Q_0)$ for diagonal $D$;
  `tauSO_compMat_unimodular`: $\tau(Q_0\circ U) = \tau(Q_0)$ for $U \in \mathrm{GL}_n(\mathcal O_F)$;
* **`tauSO_smul_compMat`**: $\tau(c\,(Q_0\circ g)) = \tau(Q_0)$ for every $g \in M_n(\mathcal O_F)$ with $\det g \ne 0$, when $\mathcal O_F$ is a
  PID (Smith normal form, `Submodule.exists_smith_normal_form_of_rank_eq`).

Sources: Weil 1982, §2.2.1, p. 14 (local measures are independent of the coordinates), Thm. 2.3.1, pp. 21–22
($(c\omega) = (\omega)$, product formula) and §2.4, p. 22 (the Tamagawa measure does not depend on $\omega$); O'Meara 1963, §102 (mass of a genus) [unverified].
-/
import QuadFormsKB.Tamagawa.LatticeChangeLocal
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.LatChange

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm

/-! ### The mass of similar spaces -/

section MassSimilar

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) {c : F} (hc : c ≠ 0) (g : GL (Fin n) F)

theorem gR_self : gR g F = g := by ext a b; simp

include hc in
theorem mem_orthGroup_F {h : GL (Fin n) F} :
    h ∈ orthGroup (c • Q.compMat g.val) F ↔ g * h * g⁻¹ ∈ orthGroup Q F := by
  rw [mem_orthGroup_smul_compMat Q hc g F, gR_self]

include hc in
theorem isIsometric_similar_iff (M M' : Submodule (𝓞 F) (Fin n → F)) :
    IsIsometric (c • Q.compMat g.val) M M' ↔ IsIsometric Q (glImage g M) (glImage g M') := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨g * γ * g⁻¹, (mem_orthGroup_F Q hc g).mp hγ, ?_⟩
    rw [← glImage_mul, show g * γ * g⁻¹ * g = g * γ by group, glImage_mul]
  · rintro ⟨γ, hγ, he⟩
    refine ⟨g⁻¹ * γ * g, (mem_orthGroup_F Q hc g).mpr (by
      rw [show g * (g⁻¹ * γ * g) * g⁻¹ = γ by group]; exact hγ), ?_⟩
    rw [glImage_mul, glImage_mul, he, ← glImage_mul, inv_mul_cancel, glImage_one]

include hc in
theorem sameGenus_similar_iff (M M' : Submodule (𝓞 F) (Fin n → F)) :
    SameGenus (c • Q.compMat g.val) M M' ↔ SameGenus Q (glImage g M) (glImage g M') := by
  refine forall_congr' fun v => ?_
  rw [loc_glImage, loc_glImage]
  constructor
  · rintro ⟨k, hk, he⟩
    refine ⟨gR g _ * k * (gR g _)⁻¹, (mem_orthGroup_smul_compMat Q hc g _).mp hk, ?_⟩
    rw [← locAct_mul, show gR g (v.adicCompletion F) * k * (gR g _)⁻¹ * gR g _ = gR g _ * k by group,
      locAct_mul, he]
  · rintro ⟨k, hk, he⟩
    refine ⟨(gR g _)⁻¹ * k * gR g _, (mem_orthGroup_smul_compMat Q hc g _).mpr (by
      rw [show gR g (v.adicCompletion F) * ((gR g _)⁻¹ * k * gR g _) * (gR g _)⁻¹ = k by group]; exact hk), ?_⟩
    rw [locAct_mul, locAct_mul, he, ← locAct_mul, inv_mul_cancel, locAct_one]

include hc in
theorem card_autLat_similar (M : Submodule (𝓞 F) (Fin n → F)) :
    Nat.card (autLat (c • Q.compMat g.val) M) = Nat.card (autLat Q (glImage g M)) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨⟨g * γ * g⁻¹, (mem_orthGroup_F Q hc g).mp γ.1.2⟩, ?_⟩
      invFun := fun γ => ⟨⟨g⁻¹ * γ * g, (mem_orthGroup_F Q hc g).mpr (by
        rw [show g * (g⁻¹ * (γ : GL (Fin n) F) * g) * g⁻¹ = γ by group]; exact γ.1.2)⟩, ?_⟩
      left_inv := fun γ => by apply Subtype.ext; apply Subtype.ext; simp only; group
      right_inv := fun γ => by apply Subtype.ext; apply Subtype.ext; simp only; group }
  · rw [mem_autLat]
    show glImage (g * (γ : GL (Fin n) F) * g⁻¹) (glImage g M) = glImage g M
    rw [← glImage_mul, show g * (γ : GL (Fin n) F) * g⁻¹ * g = g * γ by group, glImage_mul,
      (mem_autLat _).mp γ.2]
  · rw [mem_autLat]
    show glImage (g⁻¹ * (γ : GL (Fin n) F) * g) M = M
    rw [glImage_mul, glImage_mul, (mem_autLat _).mp γ.2, ← glImage_mul, inv_mul_cancel, glImage_one]

include hc in
/-- **Masses of similar spaces:** $\mathrm{Mass}(c\,(Q\circ g), L) = \mathrm{Mass}(Q, gL)$ ($g \in \mathrm{GL}_n(F)$, $c \ne 0$): $M \mapsto gM$
carries classes to classes, the genus of $L$ onto the genus of $gL$, and $O(M)$ onto $O(gM)$ (conjugation by $g$). -/
theorem mass_similar (L : Lat F n) : mass (c • Q.compMat g.val) L = mass Q (Lat.image g L) := by
  let e : LatClass (c • Q.compMat g.val) → LatClass Q :=
    Quotient.map (Lat.image g) fun M M' h => (isIsometric_similar_iff Q hc g M.1 M'.1).mp h
  have he : ∀ M : Lat F n, e (Quotient.mk _ M) = Quotient.mk _ (Lat.image g M) := fun _ => rfl
  refine finsum_mem_eq_of_bijOn e ⟨?_, ?_, ?_⟩ ?_
  · rintro _ ⟨M, rfl, hM⟩
    exact ⟨Lat.image g M, (he M).symm, (sameGenus_similar_iff Q hc g L.1 M.1).mp hM⟩
  · rintro _ ⟨M, rfl, -⟩ _ ⟨M', rfl, -⟩ h
    rw [he, he] at h
    exact Quotient.sound ((isIsometric_similar_iff Q hc g M.1 M'.1).mpr (Quotient.exact h))
  · rintro _ ⟨N, rfl, hN⟩
    let M : Lat F n := Lat.image g⁻¹ N
    have hgM : Lat.image g M = N := Subtype.ext (by
      show glImage g (glImage g⁻¹ N.1) = N.1
      rw [← glImage_mul, mul_inv_cancel, glImage_one])
    refine ⟨Quotient.mk _ M, ⟨M, rfl, (sameGenus_similar_iff Q hc g L.1 M.1).mpr ?_⟩, by rw [he, hgM]⟩
    rw [show glImage g M.1 = N.1 from congrArg Subtype.val hgM]; exact hN
  · rintro _ ⟨M, rfl, -⟩
    rw [he]
    show ((Nat.card (autLat _ M.1) : ℕ) : ℝ)⁻¹ = ((Nat.card (autLat Q (glImage g M.1)) : ℕ) : ℝ)⁻¹
    rw [card_autLat_similar Q hc g M.1]

end MassSimilar

/-! ### The mass of a second lattice in the same space -/

section MassImage

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **$\mathrm{Mass}(M) = \mathrm{Mass}(L)\cdot r(O(\hat L), O(\hat M))$** for two integral lattices in one totally positive definite
space, $r(A,B) = [A : A\cap B]/[B : A\cap B]$ (`mass_mul_vol_eq`, i.e. $\mathrm{Mass}(L)\,\mu(O(\hat L))$ is the volume of
$O(V)(F)\backslash O(V)(\mathbb A_f)$ for every $L$). -/
theorem mass_eq_mass_mul_relRatio {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L M : Lat F n) (hLi : IsIntegral Q L.1)
    (hMi : IsIntegral Q M.1) : mass Q M = mass Q L * relRatio (locStab Q L) (locStab Q M) := by
  set KL := locStab Q L
  set KM := locStab Q M
  set K' := KM ⊓ KL
  have hML : KM.Commensurable KL := commensurable_locStab Q L M
  have hK' : K'.Commensurable KL := by
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · rw [Subgroup.inf_relIndex_right]; exact hML.1.relIndex_ne_zero
    · rw [Subgroup.relIndex_eq_one.mpr inf_le_right]; exact one_ne_zero
  have e1 := mass_mul_vol_eq hQ L hLi KL 1 K' inf_le_right (Subgroup.Commensurable.refl _) hK'
  have e2 := mass_mul_vol_eq hQ M hMi KL 1 K' inf_le_left hML hK'
  rw [idxVol_self] at e1
  rw [← e1] at e2
  have hr : idxVol KL 1 KM = relRatio KM KL := by simp [idxVol, relRatio]
  rw [hr] at e2
  have hpos : relRatio KM KL ≠ 0 :=
    (relRatio_pos ⟨hML.2.relIndex_ne_zero, hML.1.relIndex_ne_zero⟩).ne'
  have hinv : relRatio KL KM = (relRatio KM KL)⁻¹ := by simp [relRatio]
  rw [hinv, mul_one] at *
  rw [← e2]; field_simp

/-- **The global ratio is the product of the local ratios** (over the finitely many primes where the lattices differ). -/
theorem relRatio_locStab_eq_prod (Q : QuadForm F n) (M : Lat F n) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, loc v M.1 = std v) :
    relRatio (locStab Q (stdLat F n)) (locStab Q M) =
      ∏ v ∈ S, relRatio (stdStab Q v) (stabLat v (orthGroup Q (v.adicCompletion F)).subtype (loc v M.1)) := by
  classical
  set B' : (v : HeightOneSpectrum (𝓞 F)) → Subgroup (orthGroup Q (v.adicCompletion F)) :=
    fun v => stabLat v (orthGroup Q (v.adicCompletion F)).subtype (loc v M.1)
  have hB : ∀ v ∉ S, B' v = stdStab Q v := fun v hv => by
    simp only [B']; rw [hS v hv, stdStab_eq_stabLat]
  have hA : ∀ v ∉ S, stdStab Q v = stdStab Q v := fun _ _ => rfl
  have hAm : ∀ h : OAf Q, h ∈ locStab Q (stdLat F n) ↔ ∀ v, h v ∈ stdStab Q v := mem_locStab_intVec Q
  have hBm : ∀ h : OAf Q, h ∈ locStab Q M ↔ ∀ v, h v ∈ B' v := fun h => Iff.rfl
  have e1 := relIndex_restrictedPi S (fun v => stdStab Q v) B' hA hB _ _ hAm hBm
  have e2 := relIndex_restrictedPi S B' (fun v => stdStab Q v) hB hA _ _ hBm hAm
  unfold relRatio
  rw [e1, e2, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]

end MassImage

/-! ### Local and archimedean bookkeeping -/

section Bookkeeping

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem stabB_eq (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) {c : 𝓞 F} (hc : c ≠ 0) (cv : Fin n → 𝓞 F)
    (hcv : ∀ a, cv a ≠ 0) :
    stabB v Q₀ hc cv hcv = stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)).subtype
      (locAct v (gR (gDiag cv hcv) (v.adicCompletion F)) (std v)) := by
  ext σ
  rw [stabB, Subgroup.mem_map_equiv]
  show locAct v (((conjD v Q₀ hc cv hcv).symm σ : orthGroup _ _) : GL (Fin n) _) (std v) = std v ↔
    locAct v (σ : GL (Fin n) _) (locAct v (gR (gDiag cv hcv) _) (std v)) = locAct v (gR (gDiag cv hcv) _) (std v)
  rw [conjD, conjOrth_symm_apply, locAct_mul, locAct_mul, locAct_eq_iff, inv_inv]

theorem loc_image_gDiag (v : HeightOneSpectrum (𝓞 F)) (cv : Fin n → 𝓞 F) (hcv : ∀ a, cv a ≠ 0) :
    loc v (Lat.image (gDiag cv hcv) (stdLat F n)).1 = locAct v (gR (gDiag cv hcv) (v.adicCompletion F)) (std v) := by
  show loc v (glImage _ intVec) = _
  rw [loc_glImage, loc_intVec]

/-- **The exact power of $\varpi$ in $x$ and the absolute value:** $q^{\mathrm{ord}_\mathfrak p x}\,|x|_\mathfrak p = 1$ ($x \in \mathcal O_F\setminus 0$). -/
theorem q_pow_ord_mul_norm (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F} (hx : x ≠ 0) :
    (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ ord (NF.irreducible_π v) (NF.ι v x) *
      ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F x)‖ = 1 := by
  set c := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {x})).factors
  have hv := v.intValuation_if_neg hx
  have h1 : NF.π v ^ c ∣ NF.ι v x := by
    rw [NF.π_pow_dvd_ι_iff]
    exact (v.intValuation_le_pow_iff_mem _ _).1 (by rw [hv])
  have h2 : ¬ NF.π v ^ (c + 1) ∣ NF.ι v x := by
    rw [NF.π_pow_dvd_ι_iff]
    intro h
    have := (v.intValuation_le_pow_iff_mem _ _).2 h
    rw [hv, WithZero.exp_le_exp] at this
    push_cast at this; omega
  have hord : ord (NF.irreducible_π v) (NF.ι v x) = c := by
    obtain ⟨u, hxu, hu⟩ := DVR.dvr_exact (NF.irreducible_π v) h1 h2
    obtain ⟨w, hw, hxw⟩ := exists_eq_ord (NF.irreducible_π v) (NF.ι_ne_zero v hx)
    exact eq_of_pow_mul_unit (NF.irreducible_π v) hw hu (hxw.symm.trans hxu)
  have h := HeightOneSpectrum.embedding_mul_absNorm (K := F) v hx
  rw [HeightOneSpectrum.maxPowDividing, map_pow, Nat.cast_pow] at h
  rw [hord, NF.q_completion, mul_comm]
  exact h

/-- $\prod_{a \le b}f_af_b = \big(\prod_af_a\big)^{n+1}$. -/
theorem prod_upperIdx_mul {M : Type*} [CommMonoid M] (f : Fin n → M) :
    ∏ p : DVR.UpperIdx n, (f p.1.1 * f p.1.2) = (∏ a, f a) ^ (n + 1) := by
  classical
  rw [Finset.prod_mul_distrib]
  have e1 : ∏ p : DVR.UpperIdx n, f p.1.1 = ∏ a, f a ^ (Finset.univ.filter fun b => a ≤ b).card := by
    rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2) (fun p => by simp)
      (fun p => f p.1), Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product]
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
      exact Finset.prod_const (s := Finset.univ.filter fun b => a ≤ b) (f a)
  have e2 : ∏ p : DVR.UpperIdx n, f p.1.2 = ∏ b, f b ^ (Finset.univ.filter fun a => a ≤ b).card := by
    rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2) (fun p => by simp)
      (fun p => f p.2), Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product_right]
    · refine Finset.prod_congr rfl fun b _ => ?_
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
      exact Finset.prod_const (s := Finset.univ.filter fun a => a ≤ b) (f b)
  rw [e1, e2, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← pow_add]
  congr 1
  have : (Finset.univ.filter fun b : Fin n => a ≤ b).card + (Finset.univ.filter fun b : Fin n => b ≤ a).card =
      (Finset.univ : Finset (Fin n)).card + 1 := by
    rw [← Finset.card_union_add_card_inter]
    have hu : (Finset.univ.filter fun b : Fin n => a ≤ b) ∪ (Finset.univ.filter fun b => b ≤ a) = Finset.univ := by
      ext b; simp [le_total]
    have hi : (Finset.univ.filter fun b : Fin n => a ≤ b) ∩ (Finset.univ.filter fun b => b ≤ a) = {a} := by
      ext b
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
      · rintro rfl; exact ⟨le_rfl, le_rfl⟩
    rw [hu, hi, Finset.card_singleton]
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- **Scaling the archimedean volume:** $\mathrm{vol}(SO_n)$ at $x d$ is $x^{-(n+1)/2}$ times that at $d$. -/
theorem archVolSO_mul (n : ℕ) {x d : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) :
    archVolSO n (x * d) = x ^ (-((n : ℝ) + 1) / 2) * archVolSO n d := by
  unfold archVolSO
  rw [Real.mul_rpow hx hd]; ring

end Bookkeeping

/-! ### The product formula for the Jacobians -/

section ProductFormula

variable {F : Type} [Field F] [NumberField F]

/-- $\prod_\mathfrak p|x|_\mathfrak p^{-1} = \prod_\sigma|\sigma(x)| = |N_{F/\mathbb Q}(x)|$ for $x \in \mathcal O_F\setminus 0$. -/
theorem tprod_norm_inv {x : 𝓞 F} (hx : x ≠ 0) :
    ∏' v : HeightOneSpectrum (𝓞 F), ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F x)‖⁻¹ =
      ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F x)‖ := by
  have hx' : algebraMap (𝓞 F) F x ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hx
  have h2 := NumberField.FinitePlace.prod_eq_inv_abs_norm hx'
  rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm] at h2
  simp only [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply] at h2
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F x)‖).Finite := by
    have h0 : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
      have h_span_nezero : Ideal.span {x} ≠ 0 := by simp [hx]
      simp only [← Ideal.dvd_span_singleton]
      exact Ideal.finite_factors h_span_nezero
    refine h0.subset fun v hv => ?_
    by_contra h
    exact hv ((NumberField.FinitePlace.norm_eq_one_iff_notMem F v x).mpr h)
  have hfin' : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F x)‖⁻¹).Finite := by
    exact hfin.subset fun v hv h => hv (by simp only [h, inv_one])
  rw [tprod_eq_finprod hfin', finprod_inv_distrib, h2, prod_norm_embeddings]
  push_cast
  rw [inv_inv]

end ProductFormula

/-! ### $\tau(c\,(Q_0\circ D)) = \tau(Q_0)$ -/

section Diagonal

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem isIntegral_image (Q₀ : QuadForm (𝓞 F) n) (G : Matrix (Fin n) (Fin n) (𝓞 F)) (g : GL (Fin n) F)
    (hg : g.val = G.map (algebraMap (𝓞 F) F)) :
    IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (Lat.image g (stdLat F n)).1 := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨y', rfl⟩ := mem_intVec_iff_exists.mp hy
  refine ⟨Q₀.eval (G *ᵥ y'), ?_⟩
  show _ = (Q₀.map (algebraMap (𝓞 F) F)).evalIn F (g.val *ᵥ intCoe y')
  have : g.val *ᵥ intCoe y' = fun i => algebraMap (𝓞 F) F ((G *ᵥ y') i) := by
    rw [hg]; funext i; exact (RingHom.map_mulVec (algebraMap (𝓞 F) F) G y' i).symm
  rw [this, ← eval_map_comp]

theorem isIntegral_std (Q₀ : QuadForm (𝓞 F) n) : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n).1 := by
  have := isIntegral_image Q₀ 1 1 (by simp)
  rwa [show Lat.image (1 : GL (Fin n) F) (stdLat F n) = stdLat F n from Subtype.ext (glImage_one _)] at this

theorem gDiag_val_map (cv : Fin n → 𝓞 F) (hcv : ∀ a, cv a ≠ 0) :
    (gDiag cv hcv).val = (diagonal cv).map (algebraMap (𝓞 F) F) := by
  rw [gDiag_val, diagonal_map (map_zero _)]

/-- **The Jacobian of $S \mapsto c\,(S\circ D)$**: $w = c^{n(n+1)/2}(\prod_ac_a)^{n+1} = \prod_{a\le b}c\,c_ac_b$. -/
def jac (c : 𝓞 F) (cv : Fin n → 𝓞 F) : 𝓞 F := c ^ Fintype.card (DVR.UpperIdx n) * (∏ a, cv a) ^ (n + 1)

theorem jac_eq_prod (c : 𝓞 F) (cv : Fin n → 𝓞 F) : jac c cv = ∏ p : DVR.UpperIdx n, wts c cv p := by
  rw [jac, ← prod_upperIdx_mul, show c ^ Fintype.card (DVR.UpperIdx n) = ∏ _p : DVR.UpperIdx n, c by
    rw [Finset.prod_const, Finset.card_univ], ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => by rw [wts, mul_assoc]

theorem jac_ne_zero {c : 𝓞 F} (hc : c ≠ 0) {cv : Fin n → 𝓞 F} (hcv : ∀ a, cv a ≠ 0) : jac c cv ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun a _ => hcv a))

/-- **The local Jacobian factor is $|w|_\mathfrak p^{-1}$.** -/
theorem prod_q_pow_ord_eq (v : HeightOneSpectrum (𝓞 F)) {c : 𝓞 F} (hc : c ≠ 0) {cv : Fin n → 𝓞 F}
    (hcv : ∀ a, cv a ≠ 0) :
    (∏ p : DVR.UpperIdx n, (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ ord (NF.irreducible_π v) (NF.ι v (wts c cv p))) =
      ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (jac c cv))‖⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [jac_eq_prod, map_prod, map_prod, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun p _ => q_pow_ord_mul_norm v (mul_ne_zero (mul_ne_zero hc (hcv _)) (hcv _))

theorem detGram_Q₁ (Q₀ : QuadForm (𝓞 F) n) (c : 𝓞 F) (cv : Fin n → 𝓞 F) (σ : F →ₐ[ℚ] ℂ) :
    detGram (c • Q₀.compMat (diagonal cv)) σ =
      (‖σ (algebraMap (𝓞 F) F c)‖ ^ n * ‖σ (algebraMap (𝓞 F) F (∏ a, cv a))‖ ^ 2) * detGram Q₀ σ := by
  simp only [detGram, det_hessian_Q₁, map_mul, map_pow, map_div₀, norm_mul, norm_pow, norm_div]
  ring

/-- **The archimedean Jacobian:** $\mathrm{vol}(SO(V_\sigma))$ for $Q_1$ times $|\sigma(w)|$ is that for $Q_0$. -/
theorem archVolSO_Q₁ (Q₀ : QuadForm (𝓞 F) n) {c : 𝓞 F} (hc : c ≠ 0) {cv : Fin n → 𝓞 F} (hcv : ∀ a, cv a ≠ 0)
    (σ : F →ₐ[ℚ] ℂ) :
    archVolSO n (detGram (c • Q₀.compMat (diagonal cv)) σ) * ‖σ (algebraMap (𝓞 F) F (jac c cv))‖ =
      archVolSO n (detGram Q₀ σ) := by
  set x := ‖σ (algebraMap (𝓞 F) F c)‖
  set y := ‖σ (algebraMap (𝓞 F) F (∏ a, cv a))‖
  have hx : 0 < x := norm_pos_iff.mpr ((map_ne_zero σ).mpr (coe_ne_zero hc))
  have hy : 0 < y := norm_pos_iff.mpr ((map_ne_zero σ).mpr (coe_ne_zero (Finset.prod_ne_zero_iff.mpr fun a _ => hcv a)))
  rw [detGram_Q₁, archVolSO_mul n (d := detGram Q₀ σ) (by positivity) (norm_nonneg _), jac, map_mul, map_pow, map_pow, map_mul,
    map_pow, map_pow, norm_mul, norm_pow, norm_pow]
  change (x ^ n * y ^ 2) ^ (-((n : ℝ) + 1) / 2) * archVolSO n (detGram Q₀ σ) *
    (x ^ Fintype.card (DVR.UpperIdx n) * y ^ (n + 1)) = _
  have hN : (Fintype.card (DVR.UpperIdx n) : ℝ) = (n : ℝ) * (n + 1) / 2 := by
    rw [DVR.card_upperIdx, Nat.cast_div (Nat.even_mul_succ_self n).two_dvd (by norm_num)]; push_cast; ring
  have e : (x ^ n * y ^ 2) ^ (-((n : ℝ) + 1) / 2) * (x ^ Fintype.card (DVR.UpperIdx n) * y ^ (n + 1)) = 1 := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast x n, ← Real.rpow_natCast y 2,
      ← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le, ← Real.rpow_natCast x, ← Real.rpow_natCast y (n + 1), hN]
    rw [mul_mul_mul_comm, ← Real.rpow_add hx, ← Real.rpow_add hy]
    have h1 : (n : ℝ) * (-((n : ℝ) + 1) / 2) + (n : ℝ) * (n + 1) / 2 = 0 := by ring
    have h2 : ((2 : ℕ) : ℝ) * (-((n : ℝ) + 1) / 2) + ((n + 1 : ℕ) : ℝ) = 0 := by push_cast; ring
    rw [h1, h2, Real.rpow_zero, Real.rpow_zero, mul_one]
  calc (x ^ n * y ^ 2) ^ (-((n : ℝ) + 1) / 2) * archVolSO n (detGram Q₀ σ) *
        (x ^ Fintype.card (DVR.UpperIdx n) * y ^ (n + 1))
      = ((x ^ n * y ^ 2) ^ (-((n : ℝ) + 1) / 2) * (x ^ Fintype.card (DVR.UpperIdx n) * y ^ (n + 1))) *
        archVolSO n (detGram Q₀ σ) := by ring
    _ = _ := by rw [e, one_mul]

/-- **The $\tau(SO)$ is invariant under $Q_0 \mapsto c\,(Q_0\circ D)$**, $D = \mathrm{diag}(c_0,\dots,c_{n-1})$ over $\mathcal O_F$
($c, c_a \ne 0$; $n \ne 0, 2$ so that $\prod_\mathfrak p\alpha_\mathfrak p$ converges; both forms totally positive definite): the form
of the lattice $D\mathcal O_F^n$, rescaled by $c$, has the same Tamagawa number.

*Proof.* $\tau = \mu_{\mathrm{Tam}}(K_{SO})\cdot 2\,\mathrm{Mass}$ (`mass_SO_eq_two_mul_mass`); $\mathrm{Mass}(Q_1, L) = \mathrm{Mass}(Q_0, DL)
= \mathrm{Mass}(Q_0, L)\prod_\mathfrak p r_\mathfrak p$ (`mass_similar`, `mass_eq_mass_mul_relRatio`, `relRatio_locStab_eq_prod`);
$\alpha_\mathfrak p(Q_1)\,r_\mathfrak p = |w|_\mathfrak p^{-1}\alpha_\mathfrak p(Q_0)$ (`localDensity_mul_relRatio`); the archimedean volumes change by
$|\sigma(w)|^{-1}$ (`archVolSO_Q₁`); and $\prod_\mathfrak p|w|_\mathfrak p^{-1} = \prod_\sigma|\sigma(w)|$ (product formula). -/
@[kb "weil1982" "§2.2.1, p. 14; Thm. 2.3.1, pp. 21-22; §2.4, p. 22 (independent of choices)"]
theorem tauSO_smul_compMat_diagonal (hn0 : n ≠ 0) (hn2 : n ≠ 2) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) {c : 𝓞 F} (hc : c ≠ 0) (cv : Fin n → 𝓞 F)
    (hcv : ∀ a, cv a ≠ 0) (hpd₁ : IsTotallyPosDef ((c • Q₀.compMat (diagonal cv)).map (algebraMap (𝓞 F) F))) :
    tauSO (c • Q₀.compMat (diagonal cv)) = tauSO Q₀ := by
  classical
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  set Q₁ := c • Q₀.compMat (diagonal cv)
  set M : Lat F n := Lat.image (gDiag cv hcv) (stdLat F n)
  have hQ₁ : Q₁.Nondegenerate := nondegenerate_Q₁ hc hQ₀ hcv
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  -- `τ = μ · 2 Mass`
  have hτ₁ : tauSO Q₁ = tamagawaK Q₁ * (2 * mass (Q₁.map (algebraMap (𝓞 F) F)) (stdLat F n)) := by
    unfold tauSO; rw [mass_SO_eq_two_mul_mass Q₁ hQ₁ hn hpd₁ (isIntegral_std Q₁)]
  have hτ₀ : tauSO Q₀ = tamagawaK Q₀ * (2 * mass QF (stdLat F n)) := by
    unfold tauSO; rw [mass_SO_eq_two_mul_mass Q₀ hQ₀ hn hpd (isIntegral_std Q₀)]
  -- the masses
  have hm1 : mass (Q₁.map (algebraMap (𝓞 F) F)) (stdLat F n) = mass QF M := by
    rw [show Q₁.map (algebraMap (𝓞 F) F) = Q1F Q₀ (c := c) cv hcv from map_Q₁ Q₀ c cv hcv]
    exact mass_similar QF (coe_ne_zero hc) _ _
  have hm2 := mass_eq_mass_mul_relRatio hpd (stdLat F n) M (isIntegral_std Q₀)
    (isIntegral_image Q₀ (diagonal cv) _ (gDiag_val_map cv hcv))
  -- the finite set of primes where `M ≠ L`
  have hSfin : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v M.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std M.2)
  set S := hSfin.toFinset
  have hS : ∀ v ∉ S, loc v M.1 = std v := fun v hv => by
    by_contra h; exact hv (hSfin.mem_toFinset.mpr h)
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => relRatio (stdStab QF v) (stabB v Q₀ hc cv hcv)
  have hstab : ∀ v, stabLat v (orthGroup QF (v.adicCompletion F)).subtype (loc v M.1) = stabB v Q₀ hc cv hcv :=
    fun v => by rw [stabB_eq, ← loc_image_gDiag]
  have hR : relRatio (locStab QF (stdLat F n)) (locStab QF M) = ∏ v ∈ S, r v := by
    rw [relRatio_locStab_eq_prod QF M S hS]
    exact Finset.prod_congr rfl fun v _ => by rw [hstab]
  have hr1 : ∀ v ∉ S, r v = 1 := fun v hv => by
    simp only [r]; rw [← hstab, hS v hv, ← stdStab_eq_stabLat, relRatio_self]
  have hr0 : ∀ v, r v ≠ 0 := fun v => by
    simp only [r]; rw [← hstab, stdStab_eq_stabLat]
    exact (relRatio_pos (commens_stabLat v _ (std_isLattice v)
      (loc_isLattice v M.2))).ne'
  -- the Jacobian
  set w := jac c cv
  have hw : w ≠ 0 := jac_ne_zero hc hcv
  set Φ : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ∏ p : DVR.UpperIdx n, (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ ord (NF.irreducible_π v) (NF.ι v (wts c cv p))
  have hΦ : ∀ v, Φ v = ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F w)‖⁻¹ :=
    fun v => prod_q_pow_ord_eq v hc hcv
  have hTfin : {v : HeightOneSpectrum (𝓞 F) | w ∈ v.asIdeal}.Finite := by
    have h_span_nezero : Ideal.span {w} ≠ 0 := by simp [hw]
    simp only [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors h_span_nezero
  set S' := S ∪ hTfin.toFinset
  have hΦ1 : ∀ v ∉ S', Φ v = 1 := fun v hv => by
    rw [hΦ, (NumberField.FinitePlace.norm_eq_one_iff_notMem F v w).mpr, inv_one]
    intro h; exact hv (Finset.mem_union_right _ (hTfin.mem_toFinset.mpr h))
  have hr1' : ∀ v ∉ S', r v = 1 := fun v hv => hr1 v (fun h => hv (Finset.mem_union_left _ h))
  -- the local identities, in Siegel's normalization
  have hloc : ∀ v, r v * NF.siegelDensity v Q₁ Q₁ * 1 ^ 0 = Φ v * NF.siegelDensity v Q₀ Q₀ := fun v => by
    have := localDensity_mul_relRatio v Q₀ hc cv hcv hQ₀
    simp only [NF.siegelDensity, if_true, pow_zero, mul_one]
    linear_combination (1 / 2 : ℝ) * this
  have hE := tprod_local_identity S' 0 (fun v => NF.siegelDensity v Q₁ Q₁) Φ (fun v => NF.siegelDensity v Q₀ Q₀)
    r (fun _ => 1) hr1' (fun _ _ => rfl) hr0 (fun _ => one_ne_zero) hloc
    (multipliable_of_ne_finset_one hΦ1) (multipliable_siegelDensity hn0 hn2 Q₀ hQ₀)
  simp only [pow_zero, one_mul] at hE
  have hSS' : ∏ v ∈ S', r v = ∏ v ∈ S, r v :=
    (Finset.prod_subset Finset.subset_union_left fun v _ hv => hr1 v hv).symm
  rw [hSS'] at hE
  have hΦprod : ∏' v, Φ v = ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F w)‖ := by
    rw [show Φ = fun v => ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F w)‖⁻¹ from funext hΦ]
    exact tprod_norm_inv hw
  rw [hΦprod] at hE
  -- the archimedean factors
  have hA : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₁ σ)) * ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F w)‖ =
      ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => archVolSO_Q₁ Q₀ hc hcv σ
  -- assemble
  rw [hτ₁, hτ₀, hm1, hm2, hR]
  unfold tamagawaK
  rw [← hA]
  set R := ∏ v ∈ S, r v
  set T₁ := ∏' v, NF.siegelDensity v Q₁ Q₁
  set T₀ := ∏' v, NF.siegelDensity v Q₀ Q₀
  set Nw := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F w)‖
  have hE' : R * T₁ = Nw * T₀ := hE
  linear_combination (|(discr F : ℝ)| ^ (-((n : ℝ) * (n - 1) / 4)) *
    (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₁ σ)) * 2 * mass QF (stdLat F n)) * hE'

end Diagonal

/-! ### Unimodular changes of basis -/

section Unimodular

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem one_smul_form (S : QuadForm F n) : (1 : F) • S = S := by ext a b; simp [smul_coeff]

/-- $\prod_\sigma|\sigma(u)| = 1$ for a unit $u$ of $\mathcal O_F$. -/
theorem prod_norm_unit {u : 𝓞 F} (hu : IsUnit u) : ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F u)‖ = 1 := by
  rw [prod_norm_embeddings]
  have h := NumberField.isUnit_iff_norm.mp hu
  rw [RingOfIntegers.coe_norm] at h
  rw [← Rat.cast_abs, h, Rat.cast_one]

theorem siegelDensity_compMat_unimodular (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n)
    (U : GL (Fin n) (𝓞 F)) :
    NF.siegelDensity v (Q₀.compMat U.val) (Q₀.compMat U.val) = NF.siegelDensity v Q₀ Q₀ := by
  have h : Siegel.IsometricGL (NF.Qp v Q₀) (NF.Qp v (Q₀.compMat U.val)) :=
    ⟨GeneralLinearGroup.map (NF.ι v) U, fun x => by
      rw [← eval_compMat, NF.Qp, NF.Qp, ← map_compMat]; rfl⟩
  simp only [NF.siegelDensity, NF.localDensityForm_eq_completion]
  rw [DVR.localDensityForm_congr_left h, DVR.localDensityForm_congr_right _ h]

theorem detGram_compMat_unimodular (Q₀ : QuadForm (𝓞 F) n) (U : GL (Fin n) (𝓞 F)) (σ : F →ₐ[ℚ] ℂ) :
    detGram (Q₀.compMat U.val) σ = ‖σ (algebraMap (𝓞 F) F U.val.det)‖ ^ 2 * detGram Q₀ σ := by
  simp only [detGram, hessian_compMat, det_mul, det_transpose, map_mul, map_div₀, norm_mul, norm_div]
  ring

/-- **$\tau(SO)$ is invariant under $\mathrm{GL}_n(\mathcal O_F)$:** $\tau(Q_0\circ U) = \tau(Q_0)$. -/
theorem tauSO_compMat_unimodular (hn0 : n ≠ 0) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (U : GL (Fin n) (𝓞 F))
    (hpdU : IsTotallyPosDef ((Q₀.compMat U.val).map (algebraMap (𝓞 F) F))) :
    tauSO (Q₀.compMat U.val) = tauSO Q₀ := by
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  set gU := GeneralLinearGroup.map (algebraMap (𝓞 F) F) U
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hdetU : IsUnit U.val.det := (Matrix.isUnit_iff_isUnit_det _).mp U.isUnit
  have hQU : (Q₀.compMat U.val).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_compMat, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hdetU.ne_zero hQ₀) hdetU.ne_zero
  have hτU : tauSO (Q₀.compMat U.val) = tamagawaK (Q₀.compMat U.val) *
      (2 * mass ((Q₀.compMat U.val).map (algebraMap (𝓞 F) F)) (stdLat F n)) := by
    unfold tauSO; rw [mass_SO_eq_two_mul_mass _ hQU hn hpdU (isIntegral_std _)]
  have hτ₀ : tauSO Q₀ = tamagawaK Q₀ * (2 * mass QF (stdLat F n)) := by
    unfold tauSO; rw [mass_SO_eq_two_mul_mass Q₀ hQ₀ hn hpd (isIntegral_std Q₀)]
  have hmass : mass ((Q₀.compMat U.val).map (algebraMap (𝓞 F) F)) (stdLat F n) = mass QF (stdLat F n) := by
    have e : (Q₀.compMat U.val).map (algebraMap (𝓞 F) F) = (1 : F) • QF.compMat gU.val := by
      rw [one_smul_form, ← map_compMat]; rfl
    rw [e, mass_similar QF one_ne_zero gU]
    congr 1
    exact Subtype.ext (glImage_map_intVec U)
  have hT : tamagawaK (Q₀.compMat U.val) = tamagawaK Q₀ := by
    unfold tamagawaK
    simp only [siegelDensity_compMat_unimodular]
    congr 2
    have hx : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ (algebraMap (𝓞 F) F U.val.det)‖ := fun σ =>
      norm_pos_iff.mpr ((map_ne_zero σ).mpr (coe_ne_zero hdetU.ne_zero))
    have hσ : ∀ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram (Q₀.compMat U.val) σ) =
        (‖σ (algebraMap (𝓞 F) F U.val.det)‖ ^ (n + 1))⁻¹ * archVolSO n (detGram Q₀ σ) := fun σ => by
      rw [detGram_compMat_unimodular, archVolSO_mul n (d := detGram Q₀ σ) (by positivity) (norm_nonneg _)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hx σ).le, ← Real.rpow_natCast, ← Real.rpow_neg (hx σ).le]
      congr 1; push_cast; ring
    rw [Finset.prod_congr rfl fun σ _ => hσ σ, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow,
      prod_norm_unit hdetU, one_pow, inv_one, one_mul]
  rw [hτU, hτ₀, hmass, hT]

end Unimodular

/-! ### Smith normal form of a matrix over a PID -/

section Smith

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}

theorem mulVec_injective_of_det_ne_zero {G : Matrix (Fin n) (Fin n) R} (hG : G.det ≠ 0) :
    Function.Injective G.mulVec := by
  intro x y h
  have h1 : G.adjugate *ᵥ (G *ᵥ x) = G.adjugate *ᵥ (G *ᵥ y) := by rw [h]
  rw [mulVec_mulVec, mulVec_mulVec, adjugate_mul, smul_mulVec, smul_mulVec, one_mulVec, one_mulVec] at h1
  funext i
  exact mul_left_cancel₀ hG (congrFun h1 i)

theorem eq_zero_of_mul_eq_zero {A X : Matrix (Fin n) (Fin n) R} (hA : A.det ≠ 0) (h : A * X = 0) : X = 0 := by
  have := congrArg (fun M => A.adjugate * M) h
  simp only [← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero] at this
  ext i j
  have := congrFun (congrFun this i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_left hA

variable [IsPrincipalIdealRing R]

/-- **Smith normal form** over a PID: a nonsingular $G$ is $U\,\mathrm{diag}(a)\,V$ with $U, V \in \mathrm{GL}_n(R)$, $a_i \ne 0$
(from Mathlib's `Submodule.exists_smith_normal_form_of_rank_eq` for the column span of $G$). -/
theorem exists_smith_decomp (G : Matrix (Fin n) (Fin n) R) (hG : G.det ≠ 0) :
    ∃ (U V : GL (Fin n) R) (a : Fin n → R), (∀ i, a i ≠ 0) ∧ G = U.val * diagonal a * V.val := by
  classical
  set N : Submodule R (Fin n → R) := LinearMap.range (Matrix.mulVecLin G)
  have hrank : Module.finrank R N = Module.finrank R (Fin n → R) :=
    LinearMap.finrank_range_of_inj (mulVec_injective_of_det_ne_zero hG)
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq (Pi.basisFun R (Fin n)) hrank
  have ha : ∀ i, a i ≠ 0 := fun i h => by
    apply ab'.ne_zero i
    apply Subtype.ext
    rw [hab, h, zero_smul]; rfl
  -- `U`: the columns `b' j`
  set U : Matrix (Fin n) (Fin n) R := (Pi.basisFun R (Fin n)).toMatrix b'
  have hU : U * b'.toMatrix (Pi.basisFun R (Fin n)) = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hUapp : ∀ i j, U i j = b' j i := fun i j => by
    simp [U, Module.Basis.toMatrix_apply]
  -- `V`: the coordinates of the columns of `G` in the basis `ab'`
  have hcol : ∀ j, G *ᵥ Pi.single j 1 ∈ N := fun j => ⟨Pi.single j 1, rfl⟩
  set V : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ab'.repr ⟨G *ᵥ Pi.single j 1, hcol j⟩ i
  have hGUV : G = U * diagonal a * V := by
    ext k j
    have e := congrArg (fun x : N => (x : Fin n → R) k) (ab'.sum_repr ⟨G *ᵥ Pi.single j 1, hcol j⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hab, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have hGkj : G k j = (G *ᵥ Pi.single j 1) k := by rw [mulVec_single_one]; rfl
    rw [hGkj, ← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diagonal_mul, hUapp]; simp only [V, Matrix.of_apply]; ring
  -- `W`: preimages of the basis `ab'`; `V W = 1`
  have hpre : ∀ i, ∃ w : Fin n → R, G *ᵥ w = ab' i := fun i => (ab' i).2
  choose w hw using hpre
  set W : Matrix (Fin n) (Fin n) R := Matrix.of fun j i => w i j
  have hGW : G * W = U * diagonal a := by
    ext k i
    have : (G * W) k i = (G *ᵥ w i) k := by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, W]
    rw [this, hw, hab, mul_diagonal, hUapp]; simp [mul_comm]
  have hUa : (U * diagonal a).det ≠ 0 := by
    rw [det_mul, det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun i _ => ha i)
    have := congrArg Matrix.det hU
    rw [det_mul, det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hVW : V * W = 1 := by
    have : U * diagonal a * (V * W - 1) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← hGUV, hGW, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mul_eq_zero hUa this)
  refine ⟨⟨U, b'.toMatrix (Pi.basisFun R (Fin n)), hU, mul_eq_one_comm.mp hU⟩,
    ⟨V, W, hVW, mul_eq_one_comm.mp hVW⟩, a, ha, hGUV⟩

end Smith

/-! ### Any integral change of lattice -/

section General

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem isTotallyPosDef_compMat_iff (S : QuadForm (𝓞 F) n) (V : GL (Fin n) (𝓞 F)) :
    IsTotallyPosDef ((S.compMat V.val).map (algebraMap (𝓞 F) F)) ↔ IsTotallyPosDef (S.map (algebraMap (𝓞 F) F)) := by
  set VF := GeneralLinearGroup.map (algebraMap (𝓞 F) F) V
  have e : ∀ x, ((S.compMat V.val).map (algebraMap (𝓞 F) F)).eval x = (S.map (algebraMap (𝓞 F) F)).eval (VF.val *ᵥ x) := by
    intro x; rw [← map_compMat, eval_compMat]; rfl
  have hinj : ∀ x, VF.val *ᵥ x = 0 ↔ x = 0 := fun x => by
    constructor
    · intro h
      have := congrArg (fun y => (VF⁻¹ : GL (Fin n) F).val *ᵥ y) h
      simpa [mulVec_mulVec, ← Units.val_mul] using this
    · rintro rfl; simp
  constructor
  · intro h y hy
    have := h ((VF⁻¹ : GL (Fin n) F).val *ᵥ y) (fun h0 => hy (by
      have := congrArg (fun x => VF.val *ᵥ x) h0
      simpa [mulVec_mulVec, ← Units.val_mul] using this))
    rwa [e, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this
  · intro h x hx
    rw [e]; exact h _ (fun h0 => hx ((hinj x).mp h0))

theorem nondegenerate_compMat_unimodular {S : QuadForm (𝓞 F) n} (hS : S.Nondegenerate) (U : GL (Fin n) (𝓞 F)) :
    (S.compMat U.val).Nondegenerate := by
  have hdetU : IsUnit U.val.det := (Matrix.isUnit_iff_isUnit_det _).mp U.isUnit
  rw [QuadForm.Nondegenerate, hessian_compMat, det_mul, det_mul, det_transpose]
  exact mul_ne_zero (mul_ne_zero hdetU.ne_zero hS) hdetU.ne_zero

/-- **The $\tau(SO)$ does not depend on the lattice** (nor on rescaling): for $\mathcal O_F$ a PID, $g \in M_n(\mathcal O_F)$ with
$\det g \ne 0$ and $c \in \mathcal O_F\setminus 0$ (both forms totally positive definite, $n \ne 0, 2$),
$$\tau\big(c\,(Q_0\circ g)\big) = \tau(Q_0),$$
i.e. the Tamagawa number computed with the lattice $g\mathcal O_F^n$ (and the form rescaled by $c$) is the one computed with $\mathcal O_F^n$.
*Proof:* Smith normal form $g = U\,\mathrm{diag}(a)\,V$ (`exists_smith_decomp`), `tauSO_compMat_unimodular` twice and
`tauSO_smul_compMat_diagonal`. -/
@[kb "weil1982" "§2.2.1, p. 14; Thm. 2.3.1, pp. 21-22; §2.4, p. 22 (independent of choices)"]
theorem tauSO_smul_compMat [IsPrincipalIdealRing (𝓞 F)] (hn0 : n ≠ 0) (hn2 : n ≠ 2) (Q₀ : QuadForm (𝓞 F) n)
    (hQ₀ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) {c : 𝓞 F} (hc : c ≠ 0)
    (G : Matrix (Fin n) (Fin n) (𝓞 F)) (hG : G.det ≠ 0)
    (hpd₁ : IsTotallyPosDef ((c • Q₀.compMat G).map (algebraMap (𝓞 F) F))) :
    tauSO (c • Q₀.compMat G) = tauSO Q₀ := by
  obtain ⟨U, V, a, ha, rfl⟩ := exists_smith_decomp G hG
  set Q₂ := Q₀.compMat U.val
  set Q₃ := c • Q₂.compMat (diagonal a)
  have e : c • Q₀.compMat (U.val * diagonal a * V.val) = Q₃.compMat V.val := by
    rw [← compMat_mul, ← compMat_mul, smul_compMat]
  rw [e] at hpd₁ ⊢
  have hQ₂ : Q₂.Nondegenerate := nondegenerate_compMat_unimodular hQ₀ U
  have hpd₂ : IsTotallyPosDef (Q₂.map (algebraMap (𝓞 F) F)) := (isTotallyPosDef_compMat_iff Q₀ U).mpr hpd
  have hpd₃ : IsTotallyPosDef (Q₃.map (algebraMap (𝓞 F) F)) := (isTotallyPosDef_compMat_iff Q₃ V).mp hpd₁
  have hQ₃ : Q₃.Nondegenerate := nondegenerate_Q₁ hc hQ₂ ha
  rw [tauSO_compMat_unimodular hn0 Q₃ hQ₃ hpd₃ V hpd₁,
    tauSO_smul_compMat_diagonal hn0 hn2 Q₂ hQ₂ hpd₂ hc a ha hpd₃,
    tauSO_compMat_unimodular hn0 Q₀ hQ₀ hpd U hpd₂]

end General

end QuadFormsKB.Tamagawa.LatChange
