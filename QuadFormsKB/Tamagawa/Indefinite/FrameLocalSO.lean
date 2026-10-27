/-
# The local identity for frames with special orthogonal groups

**Layer:** the completion $F_\mathfrak p$ of a number field at a finite prime (dyadic included). $Q_0$ over $\mathcal O_F$ of rank
$N = r + n'$, $T_0$ of rank $r$, an adapted frame $Q_0\circ g = T_0\perp Q'$ (`AdaptedFrameT`), $\Xi = gE$ the frame of the first
$r$ columns of $g$, $L_\mathfrak p = \mathfrak o_\mathfrak p^N$, $K = SO(L_\mathfrak p)$, $K' = SO(\mathfrak o_\mathfrak p^{n'})$ for $Q'$.

**Defines**
* `locIota`: $SO(Q')(F_\mathfrak p)\to SO(Q_0)(F_\mathfrak p)$, $h\mapsto g\,\mathrm{diag}(1_r, h)\,g^{-1}$ (the stabilizer of $\Xi$);
* `locFrameSet`: the integral frames $y = \varphi\Xi$, $\varphi\in SO(Q_0)(F_\mathfrak p)$, $y\in\mathfrak o_\mathfrak p^{N\times r}$; its $K$-orbits
  `LocOrbit`, representatives $\varphi_o$, the orbit stabilizers $K_o = \{h : \varphi_o\iota(h)\varphi_o^{-1}\in K\}$ (`locOrbitStab`);
* `locOrbitSum` $=\sum_o\mu_\mathfrak p(K)/\mu'_\mathfrak p(K_o)$ for the local Tamagawa measures `muLocSO` (the local factor of Weil's
  measure of the integral adelic frames, `frameOrbitSum`).

**Proves**
* **`locOrbitSum_eq`** (the local identity for frames with $SO$; Weil 1982, §3.4 and §4.5 [unverified]):
  $$\sum_o\frac{\mu_\mathfrak p(K)}{\mu'_\mathfrak p(K_o)} = \beta_\mathfrak p(Q_0, T_0)\,\frac{|\det g|_\mathfrak p^{\,n'+1}}{|\det H_{T_0}|_\mathfrak p^{\,n'}}.$$
  From `frameLocalIdentityGen` ($W\beta(Q_0,Q_0)|\det H_T|^{n'} = \beta(Q',Q')\beta(Q_0,T_0)|\det g|^{n'+1}$,
  types are
  $O(Q')$-orbits of lattices $M\supseteq E$ with weights $\mu(O(\mathfrak o^{n'}))/\mu(\mathrm{Stab}(M))$): the $K$-orbits of frames
  correspond to the $SO(Q')$-orbits of those lattices ($y = \varphi\Xi\leftrightarrow M = g^{-1}\varphi^{-1}L_\mathfrak p$, $K_o =$ the stabilizer
  of $M$), every lattice has an improper automorph (`relIndex_soStab`), so the $SO$-sum equals the $O$-sum (`tsum_orbits_index_two`),
  and $\mu_\mathfrak p(K) = \tfrac12\beta_\mathfrak p(Q_0,Q_0)$, $\mu'_\mathfrak p(K') = \tfrac12\beta_\mathfrak p(Q',Q')$ (`muLocSO_soStabSO`).
Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameLocalGen
import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamUnimodular

open MeasureTheory Set Matrix MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Frames LocalDensity QuadForm

/-! ### Orbit sums under a subgroup of index two (abstract) -/

section IndexTwo

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Y : Type*} [MulAction G Y]

/-- **Measure of a subgroup not inside $H'$**: $\mu(S) = 2\mu(S\cap H')$ if $S\not\le H'$, $[G:H']=2$. -/
theorem measure_eq_two_mul_inf (μ : Measure G) [μ.IsMulLeftInvariant] (H' S : Subgroup G) (hH' : H'.index = 2)
    (hS : ¬ S ≤ H') (hmeasH : MeasurableSet (H' : Set G)) :
    μ (S : Set G) = 2 * μ ((S ⊓ H' : Subgroup G) : Set G) := by
  obtain ⟨s, hsS, hsH⟩ := IsConcreteLE.not_le_iff_exists.mp hS
  have h1 := measure_inter_add_sdiff (μ := μ) (S : Set G) hmeasH
  have h2 : (S : Set G) \ H' = s • ((S ⊓ H' : Subgroup G) : Set G) := by
    ext x
    simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul, Subgroup.coe_inf, Set.mem_inter_iff]
    constructor
    · rintro ⟨hxS, hxH⟩
      refine ⟨s⁻¹ * x, ⟨S.mul_mem (S.inv_mem hsS) hxS, ?_⟩, by simp⟩
      rw [Subgroup.mul_mem_iff_of_index_two hH', inv_mem_iff]
      simp [hsH, hxH]
    · rintro ⟨y, ⟨hyS, hyH⟩, rfl⟩
      refine ⟨S.mul_mem hsS hyS, fun h => hsH ?_⟩
      exact ((Subgroup.mul_mem_iff_of_index_two hH').mp h).mpr hyH
  have h3 : (S : Set G) ∩ H' = ((S ⊓ H' : Subgroup G) : Set G) := (Subgroup.coe_inf S H').symm
  rw [h2, measure_smul, h3] at h1
  rw [← h1, two_mul]

theorem stab_smul_mem_iff (a : G) (x : Y) (s : G) : s ∈ stabilizer G (a • x) ↔ a⁻¹ * s * a ∈ stabilizer G x := by
  simp only [mem_stabilizer_iff]
  rw [mul_smul, mul_smul, inv_smul_eq_iff]

theorem measure_stab_smul (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (a : G) (x : Y) :
    μ (stabilizer G (a • x) : Set G) = μ (stabilizer G x : Set G) := by
  have e : (stabilizer G (a • x) : Set G) =
      (fun s => s * a) ⁻¹' ((fun t => a⁻¹ * t) ⁻¹' (stabilizer G x : Set G)) := by
    ext s
    simp only [Set.mem_preimage, SetLike.mem_coe]
    rw [stab_smul_mem_iff, mul_assoc]
  rw [e, measure_preimage_mul_right, measure_preimage_mul]

theorem stab_smul_le_iff (H' : Subgroup G) [H'.Normal] (a : G) (x : Y) :
    stabilizer G (a • x) ≤ H' ↔ stabilizer G x ≤ H' := by
  have key : ∀ (a : G) (x : Y), stabilizer G x ≤ H' → stabilizer G (a • x) ≤ H' := by
    intro a x h s hs
    have h1 := h ((stab_smul_mem_iff a x s).mp hs)
    have h2 := Subgroup.Normal.conj_mem ‹H'.Normal› _ h1 a
    have e : a * (a⁻¹ * s * a) * a⁻¹ = s := by group
    rwa [e] at h2
  refine ⟨fun h => ?_, key a x⟩
  have := key a⁻¹ (a • x) h
  simpa using this

theorem measure_inf_stab_smul (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (H' : Subgroup G)
    (a : G) (ha : a ∈ H') (x : Y) :
    μ ((H' ⊓ stabilizer G (a • x) : Subgroup G) : Set G) = μ ((H' ⊓ stabilizer G x : Subgroup G) : Set G) := by
  have e : ((H' ⊓ stabilizer G (a • x) : Subgroup G) : Set G) =
      (fun s => s * a) ⁻¹' ((fun t => a⁻¹ * t) ⁻¹' ((H' ⊓ stabilizer G x : Subgroup G) : Set G)) := by
    ext s
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf]
    rw [stab_smul_mem_iff, ← mul_assoc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨H'.mul_mem (H'.mul_mem (H'.inv_mem ha) h1) ha, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := H'.mul_mem (H'.mul_mem ha h1) (H'.inv_mem ha)
      simpa [mul_assoc] using this
  rw [e, measure_preimage_mul_right, measure_preimage_mul]

theorem map_stabilizer_subtype (H' : Subgroup G) (x : Y) :
    (stabilizer H' x).map H'.subtype = H' ⊓ stabilizer G x := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_stabilizer_iff, Subgroup.subtype_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩; exact ⟨h.2, hh⟩
  · rintro ⟨hg, hs⟩; exact ⟨⟨g, hg⟩, hs, rfl⟩

/-- **Orbit sums under an index-two subgroup.** Let $G'$ act on $Y$, $H'\le G'$ open of index $2$, $\mu$ a left and right
invariant measure on $G'$, $K_0\le G'$ with $K_0\not\le H'$ ($H'$ measurable). Then, in $[0,\infty]$,
$$\sum_{G'\text{-orbits}}\frac{\mu(K_0)}{\mu(\mathrm{Stab}_{G'}(M))} = \sum_{H'\text{-orbits}}\frac{\mu(K_0\cap H')}{\mu(\mathrm{Stab}_{H'}(M))}.$$
(Per $G'$-orbit: one $H'$-orbit if the stabilizer meets $G'\setminus H'$, two conjugate ones otherwise.) *Update:* the
hypotheses "every stabilizer has finite positive measure and is measurable" of the first draft of this statement are not
needed (the identity holds in $[0,\infty]$ with $a/0 = \infty$), so they were dropped. -/
theorem tsum_orbits_index_two (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (H' K₀ : Subgroup G)
    (hH' : H'.index = 2) (hK₀ : ¬ K₀ ≤ H') (hmeasH : MeasurableSet (H' : Set G)) :
    ∑' o : orbitRel.Quotient G Y, μ K₀ / μ (stabilizer G (Quotient.out o)) =
      ∑' o : orbitRel.Quotient H' Y, μ (K₀ ⊓ H' : Subgroup G) / μ ((stabilizer H' (Quotient.out o)).map H'.subtype) := by
  classical
  have : H'.Normal := Subgroup.normal_of_index_eq_two hH'
  obtain ⟨σ, hσ⟩ : ∃ σ : G, σ ∉ H' := by
    by_contra h
    have : H' = ⊤ := eq_top_iff.mpr fun x _ => by_contra fun hx => h ⟨x, hx⟩
    rw [this, Subgroup.index_top] at hH'
    omega
  have hK2 : μ (K₀ : Set G) = 2 * μ ((K₀ ⊓ H' : Subgroup G) : Set G) :=
    measure_eq_two_mul_inf μ H' K₀ hH' hK₀ hmeasH
  set c' : ℝ≥0∞ := μ ((K₀ ⊓ H' : Subgroup G) : Set G) with hc'
  let π : orbitRel.Quotient H' Y → orbitRel.Quotient G Y := fun o' => Quotient.mk'' (Quotient.out o' : Y)
  let f : orbitRel.Quotient H' Y → ℝ≥0∞ := fun o' =>
    μ (K₀ ⊓ H' : Subgroup G) / μ ((stabilizer H' (Quotient.out o')).map H'.subtype)
  have hπmk : ∀ x : Y, π (Quotient.mk'' x) = Quotient.mk'' x := by
    intro x
    have h1 : orbitRel H' Y (Quotient.out (Quotient.mk'' x : orbitRel.Quotient H' Y)) x :=
      Quotient.exact' (Quotient.out_eq' _)
    obtain ⟨h, hh⟩ := orbitRel_apply.mp h1
    exact Quotient.sound' (orbitRel_apply.mpr ⟨(h : G), hh⟩)
  -- all elements of a fibre lie in the `G`-orbit of the representative
  have hmem : ∀ (o : orbitRel.Quotient G Y) (o' : orbitRel.Quotient H' Y), π o' = o →
      ∃ a : G, a • (Quotient.out o : Y) = Quotient.out o' := by
    intro o o' h
    have h1 : orbitRel G Y (Quotient.out o') (Quotient.out o) := by
      apply Quotient.exact'
      rw [Quotient.out_eq']
      exact h
    exact orbitRel_apply.mp h1
  have hsum : ∑' o' : orbitRel.Quotient H' Y, f o' =
      ∑' o : orbitRel.Quotient G Y, ∑' b : π ⁻¹' {o}, f b := (ENNReal.tsum_fiberwise f π).symm
  show _ = ∑' o' : orbitRel.Quotient H' Y, f o'
  rw [hsum]
  refine tsum_congr fun o => ?_
  set M : Y := Quotient.out o with hM
  have hoM : (Quotient.mk'' M : orbitRel.Quotient G Y) = o := Quotient.out_eq' o
  have hfo : ∀ o' : orbitRel.Quotient H' Y, π o' = o → ∃ a : G, a • M = Quotient.out o' ∧
      f o' = c' / μ ((H' ⊓ stabilizer G (a • M) : Subgroup G) : Set G) := by
    intro o' ho'
    obtain ⟨a, ha⟩ := hmem o o' ho'
    refine ⟨a, ha, ?_⟩
    simp only [f, hc', ← ha, map_stabilizer_subtype]
    rfl
  by_cases hB : stabilizer G M ≤ H'
  · -- two `H'`-orbits over `o`
    set w := μ (stabilizer G M : Set G) with hw
    have hfB : ∀ o' : orbitRel.Quotient H' Y, π o' = o → f o' = c' / w := by
      intro o' ho'
      obtain ⟨a, -, hf⟩ := hfo o' ho'
      rw [hf, inf_eq_right.mpr ((stab_smul_le_iff H' a M).mpr hB), measure_stab_smul]
    have hrel : ∀ (x : G) (hx : x ∉ H') (a : G) (ha : a ∉ H'),
        (Quotient.mk'' (a • M) : orbitRel.Quotient H' Y) = Quotient.mk'' (x • M) := by
      intro x hx a ha
      refine Quotient.sound' (orbitRel_apply.mpr ⟨⟨a * x⁻¹, ?_⟩, ?_⟩)
      · rw [Subgroup.mul_mem_iff_of_index_two hH', inv_mem_iff]; simp [ha, hx]
      · show (a * x⁻¹) • x • M = a • M
        rw [← mul_smul, inv_mul_cancel_right]
    have hfib : (π ⁻¹' {o} : Set (orbitRel.Quotient H' Y)) =
        ↑({Quotient.mk'' M, Quotient.mk'' (σ • M)} : Finset (orbitRel.Quotient H' Y)) := by
      ext o'
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff]
      constructor
      · intro ho'
        obtain ⟨a, ha, -⟩ := hfo o' ho'
        have hoo : o' = Quotient.mk'' (a • M) := by rw [ha]; exact (Quotient.out_eq' o').symm
        by_cases haH : a ∈ H'
        · left; rw [hoo]; exact Quotient.sound' (orbitRel_apply.mpr ⟨⟨a, haH⟩, rfl⟩)
        · right; rw [hoo]; exact hrel σ hσ a haH
      · rintro (rfl | rfl)
        · rw [hπmk]; exact hoM
        · rw [hπmk, ← hoM]
          exact Quotient.sound' (orbitRel_apply.mpr ⟨σ, rfl⟩)
    have hne : (Quotient.mk'' M : orbitRel.Quotient H' Y) ≠ Quotient.mk'' (σ • M) := by
      intro h
      obtain ⟨h', hh'⟩ := orbitRel_apply.mp (Quotient.exact' h)
      have hs : (h' : G) * σ ∈ stabilizer G M := by
        rw [mem_stabilizer_iff, mul_smul]; exact hh'
      have := hB hs
      rw [Subgroup.mul_mem_iff_of_index_two hH'] at this
      exact hσ (this.mp h'.2)
    have hmk : π (Quotient.mk'' M) = o := by rw [hπmk]; exact hoM
    have hmk' : π (Quotient.mk'' (σ • M)) = o := by
      rw [hπmk, ← hoM]
      exact Quotient.sound' (orbitRel_apply.mpr ⟨σ, rfl⟩)
    have hsumB : ∑' b : (π ⁻¹' {o} : Set (orbitRel.Quotient H' Y)), f b =
        f (Quotient.mk'' M) + f (Quotient.mk'' (σ • M)) := by
      rw [hfib, Finset.tsum_subtype' _ f, Finset.sum_pair hne]
    rw [hsumB, hfB _ hmk, hfB _ hmk', ENNReal.div_add_div_same, ← two_mul, ← hK2]
  · obtain ⟨s, hsS, hsH⟩ := IsConcreteLE.not_le_iff_exists.mp hB
    have hmk : π (Quotient.mk'' M) = o := by rw [hπmk]; exact hoM
    have hsing : ∀ o', π o' = o → o' = Quotient.mk'' M := by
      intro o' ho'
      obtain ⟨a, ha, -⟩ := hfo o' ho'
      have hoo : o' = Quotient.mk'' (a • M) := by rw [ha]; exact (Quotient.out_eq' o').symm
      rw [hoo]
      by_cases haH : a ∈ H'
      · exact Quotient.sound' (orbitRel_apply.mpr ⟨⟨a, haH⟩, rfl⟩)
      · refine Quotient.sound' (orbitRel_apply.mpr ⟨⟨a * s, ?_⟩, ?_⟩)
        · rw [Subgroup.mul_mem_iff_of_index_two hH']; simp [haH, hsH]
        · show (a * s) • M = a • M
          rw [mul_smul, mem_stabilizer_iff.mp hsS]
    rw [tsum_eq_single (⟨Quotient.mk'' M, hmk⟩ : (π ⁻¹' {o} : Set (orbitRel.Quotient H' Y)))
      (fun b hb => absurd (Subtype.ext (hsing b.1 b.2)) hb)]
    obtain ⟨a, ha, hf⟩ := hfo (Quotient.mk'' M) hmk
    have hnot : ¬ stabilizer G (a • M) ≤ H' := fun h => hB ((stab_smul_le_iff H' a M).mp h)
    have h2 := measure_eq_two_mul_inf μ H' (stabilizer G (a • M)) hH' hnot hmeasH
    rw [measure_stab_smul, inf_comm] at h2
    show _ = f (Quotient.mk'' M)
    rw [hf, hK2, h2]
    exact ENNReal.mul_div_mul_left _ _ two_ne_zero ENNReal.ofNat_ne_top

end IndexTwo

/-! ### The local objects -/

section Local

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F))
  (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
  (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))

local notation "Fv" => v.adicCompletion F
local notation "gv" => Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g

/-- Conjugating an isometry of $P$ by a change of coordinates $g$ with $Q \circ g = P$ gives an isometry of $Q$. -/
theorem orth_conj_of_compMat {N : ℕ} {Q P : QuadForm F N} (g k : GL (Fin N) Fv)
    (hg : (Q.map (algebraMap F Fv)).compMat g.val = P.map (algebraMap F Fv)) (hk : k ∈ orthGroup P Fv) :
    g * k * g⁻¹ ∈ orthGroup Q Fv := by
  rw [mem_orthGroup_iff_compMat] at hk ⊢
  rw [Units.val_mul, Units.val_mul, ← compMat_mul, ← compMat_mul, hg, hk, ← hg, compMat_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, compMat_one]

/-- The frame over $F_\mathfrak p$ in terms of the $F$-forms. -/
theorem frameF : ((Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F Fv)).compMat (gv).val =
    (blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))).map (algebraMap F Fv) := by
  rw [← map_Qp_eq]; exact frameG_local v Q₀ T₀ fr

theorem frameF_inv : ((blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))).map
    (algebraMap F Fv)).compMat (gv⁻¹).val = (Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F Fv) := by
  rw [← frameF v Q₀ T₀ fr, compMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, compMat_one]

/-- $g\,\mathrm{diag}(1, h)\,g^{-1}$ is an isometry of $Q_0$ for $h \in O(Q')$. -/
theorem conj_blockGLB_mem (h : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) :
    gv * blockGLB (r := r) (h : GL (Fin n') Fv) * gv⁻¹ ∈ orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv :=
  orth_conj_of_compMat v _ _ (frameF v Q₀ T₀ fr)
    (orthEmbB (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F)) Fv h).2

theorem det_conj_blockGLB (h : GL (Fin n') Fv) :
    (gv * blockGLB (r := r) h * gv⁻¹).val.det = h.val.det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, blockGLB_val, det_blockMat_diag, det_one, one_mul]
  rw [mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]

/-- **The stabilizer embedding at $\mathfrak p$**: $h\mapsto g\,\mathrm{diag}(1_r, h)\,g^{-1}$, $SO(Q')(F_\mathfrak p)\to SO(Q_0)(F_\mathfrak p)$. -/
def locIota : SOv v fr.Q' →* SOv v Q₀ where
  toFun h := ⟨⟨gv * blockGLB (r := r) ((h : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n') Fv) * gv⁻¹,
    conj_blockGLB_mem v Q₀ T₀ fr h.1⟩, by
      rw [mem_soSub]
      show (gv * blockGLB (r := r) ((h : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n') Fv) * gv⁻¹).val.det = 1
      rw [det_conj_blockGLB]; exact h.2⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    show gv * blockGLB (r := r) (1 : GL (Fin n') Fv) * gv⁻¹ = 1
    rw [map_one, mul_one, mul_inv_cancel]
  map_mul' a b := by
    apply Subtype.ext; apply Subtype.ext
    show gv * blockGLB (r := r) ((a * b : SOv v fr.Q').1.1 : GL (Fin n') Fv) * gv⁻¹ = _
    show _ = (gv * blockGLB (r := r) ((a : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n') Fv) * gv⁻¹) *
      (gv * blockGLB (r := r) ((b : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n') Fv) * gv⁻¹)
    have : ((a * b : SOv v fr.Q').1.1 : GL (Fin n') Fv) = (a.1.1 : GL (Fin n') Fv) * b.1.1 := rfl
    rw [this, map_mul]
    group

theorem locIota_val (h : SOv v fr.Q') :
    (((locIota v Q₀ T₀ fr h : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin (r + n')) Fv) =
      gv * blockGLB (r := r) ((h : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n') Fv) * gv⁻¹ := rfl

/-- The base frame $\Xi = gE$ at $\mathfrak p$. -/
abbrev locBase : Matrix (Fin (r + n')) (Fin r) Fv := (gv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)

/-- The matrix of an element of $SO(Q)(F_\mathfrak p)$. -/
def soMat {N : ℕ} {Q : QuadForm (𝓞 F) N} (φ : SOv v Q) : Matrix (Fin N) (Fin N) Fv :=
  (((φ : orthGroup (Q.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin N) Fv)).val

theorem soMat_mul {N : ℕ} {Q : QuadForm (𝓞 F) N} (φ ψ : SOv v Q) : soMat v (φ * ψ) = soMat v φ * soMat v ψ := rfl

theorem soMat_one {N : ℕ} {Q : QuadForm (𝓞 F) N} : soMat v (1 : SOv v Q) = 1 := rfl

theorem soMat_inv_mul {N : ℕ} {Q : QuadForm (𝓞 F) N} (φ : SOv v Q) : soMat v φ⁻¹ * soMat v φ = 1 := by
  rw [← soMat_mul, inv_mul_cancel, soMat_one]

theorem soMat_mul_inv {N : ℕ} {Q : QuadForm (𝓞 F) N} (φ : SOv v Q) : soMat v φ * soMat v φ⁻¹ = 1 := by
  rw [← soMat_mul, mul_inv_cancel, soMat_one]

local notation "𝔬" => v.adicCompletionIntegers F
local notation "TF" => T₀.map (algebraMap (𝓞 F) F)
local notation "QF'" => fr.Q'.map (algebraMap (𝓞 F) F)

/-- $x \in \mathfrak o_\mathfrak p^N$ iff all entries have valuation $\le 1$. -/
theorem mem_std_iff' {N : ℕ} (x : Fin N → Fv) : x ∈ std v ↔ ∀ i, Valued.v (x i) ≤ 1 := by
  constructor
  · intro hy i; have := hy i; rwa [neg_zero, WithZero.exp_zero] at this
  · intro h i; rw [neg_zero, WithZero.exp_zero]; exact h i

theorem mem_locAct_iff_inv {N : ℕ} (g : GL (Fin N) Fv) (M : Submodule 𝔬 (Fin N → Fv)) (x : Fin N → Fv) :
    x ∈ locAct v g M ↔ g⁻¹.val *ᵥ x ∈ M := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hxy' : g.val *ᵥ y = x := hxy
    rw [← hxy', mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    exact hy
  · intro h
    exact ⟨_, h, mulVec_inv_mulVec g x⟩

theorem locAct_inj {N : ℕ} (g : GL (Fin N) Fv) (A B : Submodule 𝔬 (Fin N → Fv)) :
    locAct v g A = locAct v g B ↔ A = B := by
  constructor
  · intro h
    have := congrArg (locAct v g⁻¹) h
    rwa [locAct_inv_locAct, locAct_inv_locAct] at this
  · intro h; rw [h]

/-- The matrix of an element of $SO(Q)(F_\mathfrak p)$ as an element of $\mathrm{GL}_N(F_\mathfrak p)$. -/
abbrev soGL {N : ℕ} {Q : QuadForm (𝓞 F) N} (φ : SOv v Q) : GL (Fin N) Fv :=
  ((φ : orthGroup (Q.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin N) Fv)

theorem soMat_eq {N : ℕ} {Q : QuadForm (𝓞 F) N} (φ : SOv v Q) : soMat v φ = (soGL v φ).val := rfl

theorem soGL_mul {N : ℕ} {Q : QuadForm (𝓞 F) N} (φ ψ : SOv v Q) : soGL v (φ * ψ) = soGL v φ * soGL v ψ := rfl

theorem soGL_inv {N : ℕ} {Q : QuadForm (𝓞 F) N} (φ : SOv v Q) : soGL v φ⁻¹ = (soGL v φ)⁻¹ := rfl

theorem soGL_mem {N : ℕ} {Q : QuadForm (𝓞 F) N} (φ : SOv v Q) :
    soGL v φ ∈ orthGroup (Q.map (algebraMap (𝓞 F) F)) Fv := φ.1.2

theorem mem_soStabSO_iff {N : ℕ} {Q : QuadForm (𝓞 F) N} (k : SOv v Q) :
    k ∈ soStabSO v Q ↔ locAct v (soGL v k) (std v) = std v := Iff.rfl

/-- $g\,k\,g^{-1}$ is an isometry of $T \perp Q'$ for $k$ an isometry of $Q_0$ (inverse change of coordinates). -/
theorem conj_inv_mem (k : GL (Fin (r + n')) Fv) (hk : k ∈ orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv) :
    gv⁻¹ * k * gv ∈ orthGroup (blockForm TF QF') Fv := by
  have := orth_conj_of_compMat v gv⁻¹ k (frameF_inv v Q₀ T₀ fr) hk
  simpa using this

/-- **The lattice of a rotation**: $M_\varphi = g^{-1}\varphi^{-1}\mathfrak o_\mathfrak p^N$. -/
def latPhi (φ : SOv v Q₀) : Submodule 𝔬 (Fin (r + n') → Fv) := locAct v (gv⁻¹ * (soGL v φ)⁻¹) (std v)

theorem stdCol_mem_latPhi_iff (φ : SOv v Q₀) (j : Fin r) :
    stdCol v (n' := n') j ∈ latPhi v Q₀ T₀ fr φ ↔ ∀ i, Valued.v ((soMat v φ * locBase v Q₀ T₀ fr) i j) ≤ 1 := by
  unfold latPhi
  rw [mem_locAct_iff_inv, mem_std_iff']
  have : (gv⁻¹ * (soGL v φ)⁻¹)⁻¹ = soGL v φ * gv := by group
  have e : (soGL v φ * gv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) =
      soMat v φ * locBase v Q₀ T₀ fr := by
    simp only [soMat, locBase, Units.val_mul, Matrix.mul_assoc]
  rw [this, mulVec_stdCol]
  show (∀ i, Valued.v (((soGL v φ * gv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) :
    Matrix (Fin (r + n')) (Fin r) Fv) i j) ≤ 1) ↔ _
  rw [e]

/-- The point of $Y_\mathfrak p(\Lambda)$ attached to a rotation $\varphi$ with $\varphi\Xi$ integral. -/
def Mphi (φ : SOv v Q₀) (hφ : ∀ j, stdCol v (n' := n') j ∈ latPhi v Q₀ T₀ fr φ) :
    LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v)) :=
  ⟨latPhi v Q₀ T₀ fr φ, ⟨⟨gv⁻¹ * (soGL v φ)⁻¹ * gv, conj_inv_mem v Q₀ T₀ fr _ (soGL_mem v φ⁻¹)⟩, by
    show locAct v (gv⁻¹ * (soGL v φ)⁻¹ * gv) (locAct v gv⁻¹ (std v)) = latPhi v Q₀ T₀ fr φ
    rw [← locAct_mul, mul_inv_cancel_right]; rfl⟩, hφ⟩

theorem Mphi_val (φ : SOv v Q₀) (hφ) : (Mphi v Q₀ T₀ fr φ hφ).1 = latPhi v Q₀ T₀ fr φ := rfl

theorem latPhi_mul_stab {k φ : SOv v Q₀} (hk : k ∈ soStabSO v Q₀) :
    latPhi v Q₀ T₀ fr (k * φ) = latPhi v Q₀ T₀ fr φ := by
  have hk' : locAct v (soGL v k)⁻¹ (std v) = std v :=
    (mem_soStabSO_iff v k⁻¹).mp ((soStabSO v Q₀).inv_mem hk)
  unfold latPhi
  rw [soGL_mul, _root_.mul_inv_rev, ← mul_assoc, locAct_mul (gv⁻¹ * (soGL v φ)⁻¹), hk']

theorem latPhi_eq_iff (φ φ' : SOv v Q₀) :
    latPhi v Q₀ T₀ fr φ = latPhi v Q₀ T₀ fr φ' ↔ φ' * φ⁻¹ ∈ soStabSO v Q₀ := by
  rw [mem_soStabSO_iff, soGL_mul, soGL_inv]
  unfold latPhi
  rw [locAct_mul, locAct_mul, locAct_mul, locAct_inj,
    locAct_eq_iff (g := soGL v φ') (M := locAct v (soGL v φ)⁻¹ (std v)) (N := std v)]

theorem latPhi_mul_iota (φ : SOv v Q₀) (a : SOv v fr.Q') :
    locAct v (blockGLB (r := r) ((a : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n') Fv))
      (latPhi v Q₀ T₀ fr φ) = latPhi v Q₀ T₀ fr (φ * (locIota v Q₀ T₀ fr a)⁻¹) := by
  unfold latPhi
  have hι : soGL v (locIota v Q₀ T₀ fr a) =
      gv * blockGLB (r := r) ((a : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n') Fv) * gv⁻¹ :=
    locIota_val v Q₀ T₀ fr a
  rw [← locAct_mul, soGL_mul, soGL_inv, _root_.mul_inv_rev, inv_inv, hι]
  congr 1
  group

theorem locIota_mul_base (a : SOv v fr.Q') :
    soMat v (locIota v Q₀ T₀ fr a) * locBase v Q₀ T₀ fr = locBase v Q₀ T₀ fr := by
  have hE := embB_mul_stdFrameMat v TF QF' (a : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv)
  rw [embB_apply] at hE
  simp only [soMat, locIota_val, locBase, Units.val_mul, Matrix.mul_assoc, gcancel', hE]

/-! #### Topology and measures of the stabilizers of the lattices of $Y_\mathfrak p(\Lambda)$ -/

theorem continuous_blockMat_one :
    Continuous (fun D : Matrix (Fin n') (Fin n') Fv =>
      (blockMat (1 : Matrix (Fin r) (Fin r) Fv) 0 0 D : Matrix (Fin (r + n')) (Fin (r + n')) Fv)) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => simp only [blockMat_castAdd_castAdd]; exact continuous_const
    | right j => simp only [blockMat_castAdd_natAdd]; exact continuous_const
  | right i =>
    induction j using Fin.addCases with
    | left j => simp only [blockMat_natAdd_castAdd]; exact continuous_const
    | right j => simp only [blockMat_natAdd_natAdd]; exact continuous_id.matrix_elem i j

theorem continuous_blockGLB :
    Continuous (fun a : GL (Fin n') Fv => (blockGLB (r := r) a : GL (Fin (r + n')) Fv)) :=
  Units.continuous_map (f := (blockHomB (r := r) : Matrix (Fin n') (Fin n') Fv →*
    Matrix (Fin (r + n')) (Fin (r + n')) Fv)) (continuous_blockMat_one v)

theorem continuous_embB : Continuous (fun a : orthGroup QF' Fv => embB v TF QF' a) :=
  (continuous_blockGLB v (r := r)).comp continuous_subtype_val

theorem isOpen_stabilizerY (M : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) :
    IsOpen (stabilizer (orthGroup QF' Fv) M : Set (orthGroup QF' Fv)) := by
  obtain ⟨h, hh⟩ := M.2.1
  have hMc : M.1 = locAct v ((h : GL (Fin (r + n')) Fv) * gv⁻¹) (std v) := by rw [← hh, locAct_mul]
  have : (stabilizer (orthGroup QF' Fv) M : Set (orthGroup QF' Fv)) =
      (fun a : orthGroup QF' Fv => embB v TF QF' a) ⁻¹'
        {x | locAct v x (locAct v ((h : GL (Fin (r + n')) Fv) * gv⁻¹) (std v)) =
          locAct v ((h : GL (Fin (r + n')) Fv) * gv⁻¹) (std v)} := by
    ext a
    simp only [SetLike.mem_coe, mem_stabilizer_iff, Set.mem_preimage]
    show _ ↔ locAct v (embB v TF QF' a) (locAct v ((h : GL (Fin (r + n')) Fv) * gv⁻¹) (std v)) = _
    rw [← hMc]
    exact ⟨fun hs => congrArg Subtype.val hs, fun hs => Subtype.ext hs⟩
  rw [this]
  exact (isOpen_stab_locAct v _).preimage (continuous_embB v Q₀ T₀ fr)

theorem stabilizerY_relIndex_ne_zero (M : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) :
    (stdStab QF' v).relIndex (stabilizer (orthGroup QF' Fv) M) ≠ 0 ∧
      (stabilizer (orthGroup QF' Fv) M).relIndex (stdStab QF' v) ≠ 0 := by
  set ψ : orthGroup QF' Fv →* GL (Fin (r + n')) Fv := embB v TF QF'
  have h1 : stabilizer (orthGroup QF' Fv) M = stabLat v ψ M.1 := by
    ext h'; rw [mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h2 : stdStab QF' v = stabLat v ψ (std v) := by
    ext h'; exact (mem_stdStab_orthEmbB_iff TF QF' v h').symm
  have hM : M.1.IsLattice Fv := by
    obtain ⟨h, hh⟩ := M.2.1
    rw [← hh]
    exact locAct_isLattice _ (locAct_isLattice _ (std_isLattice v))
  rw [h1, h2]
  exact ⟨relIndex_stabLat_ne_zero v ψ hM (std_isLattice v), relIndex_stabLat_ne_zero v ψ (std_isLattice v) hM⟩

/-- **The weight of a type as a ratio of Haar measures**: $\mu(O(\mathfrak o^{n'}))/\mu(\mathrm{Stab}(M)) = w(M)$. -/
theorem measure_stdStab_div_stab (hQ' : fr.Q'.Nondegenerate) (M : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) :
    muLoc v fr.Q' 1 (stdStab QF' v : Set (orthGroup QF' Fv)) /
      muLoc v fr.Q' 1 (stabilizer (orthGroup QF' Fv) M : Set (orthGroup QF' Fv)) =
    ENNReal.ofReal (locFrameWeightG v TF QF' (locAct v gv⁻¹ (std v)) M) := by
  have := isHaarMeasure_muLoc v fr.Q' hQ' one_pos
  set μ := muLoc v fr.Q' 1 with hμ
  obtain ⟨h21, h12⟩ := stabilizerY_relIndex_ne_zero v Q₀ T₀ fr M
  have hA := isOpen_stdStab v QF'
  have hB := isOpen_stabilizerY v Q₀ T₀ fr M
  have e := measure_toReal_eq_relRatio_mul μ hA hB h12 h21
  have hAfin : μ (stdStab QF' v : Set (orthGroup QF' Fv)) ≠ ⊤ := by
    rw [hμ, muLoc_stdStab]; exact ENNReal.ofReal_ne_top
  have hBfin : μ (stabilizer (orthGroup QF' Fv) M : Set (orthGroup QF' Fv)) ≠ ⊤ := by
    have hI : IsOpen (((stdStab QF' v) ⊓ stabilizer (orthGroup QF' Fv) M : Subgroup _) : Set (orthGroup QF' Fv)) :=
      hA.inter hB
    have := measure_subgroup_eq_relIndex_mul μ hI inf_le_right
      (by rw [Subgroup.inf_relIndex_right]; exact h21)
    rw [this]
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ne_top_of_le_ne_top hAfin ?_)
    exact measure_mono (by exact_mod_cast inf_le_left)
  have hBpos : μ (stabilizer (orthGroup QF' Fv) M : Set (orthGroup QF' Fv)) ≠ 0 :=
    (hB.measure_pos μ ⟨1, (stabilizer (orthGroup QF' Fv) M).one_mem⟩).ne'
  have hBr : 0 < (μ (stabilizer (orthGroup QF' Fv) M : Set (orthGroup QF' Fv))).toReal :=
    ENNReal.toReal_pos hBpos hBfin
  have key : (μ (stdStab QF' v : Set (orthGroup QF' Fv))).toReal /
      (μ (stabilizer (orthGroup QF' Fv) M : Set (orthGroup QF' Fv))).toReal =
      locFrameWeightG v TF QF' (locAct v gv⁻¹ (std v)) M := by
    rw [e]; field_simp; rfl
  rw [← key, ENNReal.ofReal_div_of_pos hBr, ENNReal.ofReal_toReal hAfin, ENNReal.ofReal_toReal hBfin]

theorem det_conj_inv {N : ℕ} (g x : GL (Fin N) Fv) : (g⁻¹ * x * g).val.det = x.val.det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  have : g⁻¹.val.det * g.val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  linear_combination x.val.det * this

theorem det_embB (a : orthGroup QF' Fv) : (embB v TF QF' a).val.det = (a : GL (Fin n') Fv).val.det := by
  rw [embB_val, det_blockMat_diag, det_one, one_mul]

/-- **The stabilizer of $\Xi$ in $SO(Q_0)$ is $\iota(SO(Q'))$**: if $\varphi'\Xi = \varphi\Xi$ then $\varphi' = \varphi\,\iota(a)$. -/
theorem Xi_stab (hT : T₀.Nondegenerate) (φ φ' : SOv v Q₀)
    (h : soMat v φ' * locBase v Q₀ T₀ fr = soMat v φ * locBase v Q₀ T₀ fr) :
    ∃ a : SOv v fr.Q', φ' = φ * locIota v Q₀ T₀ fr a := by
  have hTF := fl_hess_ne_v v T₀ hT
  set ψ : SOv v Q₀ := φ⁻¹ * φ' with hψ
  have hψΞ : soMat v ψ * locBase v Q₀ T₀ fr = locBase v Q₀ T₀ fr := by
    rw [hψ, soMat_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, soMat_inv_mul, Matrix.one_mul]
  set k : GL (Fin (r + n')) Fv := gv⁻¹ * soGL v ψ * gv with hk
  have hkO : k ∈ orthGroup (blockForm TF QF') Fv := conj_inv_mem v Q₀ T₀ fr _ (soGL_mem v ψ)
  have hkE : k.val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = stdFrameMat := by
    have : k.val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) =
        gv⁻¹.val * (soMat v ψ * locBase v Q₀ T₀ fr) := by
      simp only [hk, Units.val_mul, soMat, locBase, Matrix.mul_assoc]
    rw [this, hψΞ]
    exact gcancel' v gv stdFrameMat
  obtain ⟨a, ha⟩ := exists_embB_eq v TF QF' hTF ((mem_orthGroup_iff_compMat v _ _).mp hkO) hkE
  have hdet : (a : GL (Fin n') Fv).val.det = 1 := by
    rw [← det_embB v Q₀ T₀ fr, ha, hk, det_conj_inv]
    exact ψ.2
  let a' : SOv v fr.Q' := ⟨a, hdet⟩
  have hι : soGL v (locIota v Q₀ T₀ fr a') = soGL v ψ := by
    have e : soGL v (locIota v Q₀ T₀ fr a') = gv * blockGLB (r := r) (a : GL (Fin n') Fv) * gv⁻¹ :=
      locIota_val v Q₀ T₀ fr a'
    have : blockGLB (r := r) (a : GL (Fin n') Fv) = k := ha
    rw [e, this, hk]; group
  refine ⟨a', ?_⟩
  have : locIota v Q₀ T₀ fr a' = ψ := Subtype.ext (Subtype.ext hι)
  rw [this, hψ, mul_inv_cancel_left]

/-- **The integral frames in the orbit of $\Xi$**: $y = \varphi\Xi$, $\varphi\in SO(Q_0)(F_\mathfrak p)$, with integral entries. -/
def locFrameSet : Set (Matrix (Fin (r + n')) (Fin r) Fv) :=
  {y | (∃ φ : SOv v Q₀, y = soMat v φ * locBase v Q₀ T₀ fr) ∧ ∀ i j, Valued.v (y i j) ≤ 1}

/-- Same $SO(L_\mathfrak p)$-orbit. -/
def locOrbitSetoid : Setoid (locFrameSet v Q₀ T₀ fr) where
  r y y' := ∃ k : SOv v Q₀, k ∈ soStabSO v Q₀ ∧ y'.1 = soMat v k * y.1
  iseqv := by
    refine ⟨fun y => ⟨1, (soStabSO v Q₀).one_mem, by rw [soMat_one, Matrix.one_mul]⟩, ?_, ?_⟩
    · rintro y y' ⟨k, hk, h⟩
      refine ⟨k⁻¹, (soStabSO v Q₀).inv_mem hk, ?_⟩
      rw [h, ← Matrix.mul_assoc, soMat_inv_mul, Matrix.one_mul]
    · rintro y y' y'' ⟨k, hk, h⟩ ⟨k', hk', h'⟩
      refine ⟨k' * k, (soStabSO v Q₀).mul_mem hk' hk, ?_⟩
      rw [h', h, soMat_mul, Matrix.mul_assoc]

/-- **The $SO(L_\mathfrak p)$-orbits of integral frames of $T_0$** in the $SO(Q_0)(F_\mathfrak p)$-orbit of $\Xi$. -/
abbrev LocOrbit : Type := Quotient (locOrbitSetoid v Q₀ T₀ fr)

/-- A representative $\varphi_o$ with $\varphi_o\Xi$ in the orbit $o$. -/
def locOrbitRep (o : LocOrbit v Q₀ T₀ fr) : SOv v Q₀ :=
  ((Quotient.out o : locFrameSet v Q₀ T₀ fr).2.1).choose

/-- **The stabilizer of the orbit** $K_o = \{h\in SO(Q')(F_\mathfrak p) : \varphi_o\,\iota(h)\,\varphi_o^{-1}\in SO(L_\mathfrak p)\}$. -/
def locOrbitStab (o : LocOrbit v Q₀ T₀ fr) : Subgroup (SOv v fr.Q') :=
  ((soStabSO v Q₀).comap (MulAut.conj (locOrbitRep v Q₀ T₀ fr o)).toMonoidHom).comap (locIota v Q₀ T₀ fr)

/-! ### Integral frames and lattices of $Y_\mathfrak p(\Lambda)$ -/

/-- The rotation chosen for an integral frame $y = \varphi\Xi$. -/
def frPhi (y : locFrameSet v Q₀ T₀ fr) : SOv v Q₀ := y.2.1.choose

theorem frPhi_spec (y : locFrameSet v Q₀ T₀ fr) :
    y.1 = soMat v (frPhi v Q₀ T₀ fr y) * locBase v Q₀ T₀ fr := y.2.1.choose_spec

theorem frPhi_int (y : locFrameSet v Q₀ T₀ fr) :
    ∀ j, stdCol v (n' := n') j ∈ latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y) :=
  fun j => (stdCol_mem_latPhi_iff v Q₀ T₀ fr _ j).mpr fun i => by
    rw [← frPhi_spec]; exact y.2.2 i j

theorem locOrbitRep_eq (o : LocOrbit v Q₀ T₀ fr) :
    locOrbitRep v Q₀ T₀ fr o = frPhi v Q₀ T₀ fr (Quotient.out o) := rfl

/-- **The lattice of an integral frame**: $y = \varphi\Xi \mapsto M = g^{-1}\varphi^{-1}\mathfrak o_\mathfrak p^N \in Y_\mathfrak p(\Lambda)$. -/
def Th (y : locFrameSet v Q₀ T₀ fr) : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v)) :=
  Mphi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y) (frPhi_int v Q₀ T₀ fr y)

theorem Th_val (y : locFrameSet v Q₀ T₀ fr) : (Th v Q₀ T₀ fr y).1 = latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y) := rfl

theorem smul_Mphi_val (a : SOv v fr.Q') (φ : SOv v Q₀) (hφ) :
    (a • Mphi v Q₀ T₀ fr φ hφ).1 = latPhi v Q₀ T₀ fr (φ * (locIota v Q₀ T₀ fr a)⁻¹) :=
  latPhi_mul_iota v Q₀ T₀ fr φ a

theorem Th_rel (hT : T₀.Nondegenerate) {y y' : locFrameSet v Q₀ T₀ fr} (k : SOv v Q₀) (hk : k ∈ soStabSO v Q₀)
    (hy : y'.1 = soMat v k * y.1) :
    ∃ a : SOv v fr.Q', a • Th v Q₀ T₀ fr y = Th v Q₀ T₀ fr y' := by
  obtain ⟨b, hb⟩ := Xi_stab v Q₀ T₀ fr hT (k * frPhi v Q₀ T₀ fr y) (frPhi v Q₀ T₀ fr y') (by
    calc soMat v (frPhi v Q₀ T₀ fr y') * locBase v Q₀ T₀ fr = y'.1 := (frPhi_spec v Q₀ T₀ fr y').symm
      _ = soMat v k * y.1 := hy
      _ = soMat v k * (soMat v (frPhi v Q₀ T₀ fr y) * locBase v Q₀ T₀ fr) := by rw [← frPhi_spec]
      _ = soMat v (k * frPhi v Q₀ T₀ fr y) * locBase v Q₀ T₀ fr := by rw [soMat_mul, Matrix.mul_assoc])
  refine ⟨b⁻¹, Subtype.ext ?_⟩
  have e1 : (b⁻¹ • Th v Q₀ T₀ fr y).1 =
      latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y * (locIota v Q₀ T₀ fr b⁻¹)⁻¹) :=
    smul_Mphi_val v Q₀ T₀ fr b⁻¹ _ _
  have e2 : (Th v Q₀ T₀ fr y').1 = latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y') := rfl
  rw [e1, e2, hb, mul_assoc, latPhi_mul_stab v Q₀ T₀ fr hk, map_inv, inv_inv]

theorem Th_inj {y y' : locFrameSet v Q₀ T₀ fr} (a : SOv v fr.Q') (ha : a • Th v Q₀ T₀ fr y = Th v Q₀ T₀ fr y') :
    ∃ k : SOv v Q₀, k ∈ soStabSO v Q₀ ∧ y'.1 = soMat v k * y.1 := by
  have e1 : (a • Th v Q₀ T₀ fr y).1 =
      latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y * (locIota v Q₀ T₀ fr a)⁻¹) :=
    smul_Mphi_val v Q₀ T₀ fr a _ _
  have e2 : (Th v Q₀ T₀ fr y').1 = latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y') := rfl
  have hl : latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y * (locIota v Q₀ T₀ fr a)⁻¹) =
      latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y') := by
    rw [← e1, ← e2]; exact congrArg Subtype.val ha
  have h1 := (latPhi_eq_iff v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y * (locIota v Q₀ T₀ fr a)⁻¹)
    (frPhi v Q₀ T₀ fr y')).mp hl
  have hι : soMat v (locIota v Q₀ T₀ fr a)⁻¹ * locBase v Q₀ T₀ fr = locBase v Q₀ T₀ fr := by
    rw [← map_inv]; exact locIota_mul_base v Q₀ T₀ fr a⁻¹
  set x : SOv v Q₀ := frPhi v Q₀ T₀ fr y * (locIota v Q₀ T₀ fr a)⁻¹ with hx
  have hxΞ : soMat v x * locBase v Q₀ T₀ fr = y.1 := by
    rw [hx, soMat_mul, Matrix.mul_assoc, hι, ← frPhi_spec]
  refine ⟨frPhi v Q₀ T₀ fr y' * x⁻¹, h1, ?_⟩
  calc y'.1 = soMat v (frPhi v Q₀ T₀ fr y') * locBase v Q₀ T₀ fr := frPhi_spec v Q₀ T₀ fr y'
    _ = soMat v ((frPhi v Q₀ T₀ fr y' * x⁻¹) * x) * locBase v Q₀ T₀ fr := by rw [inv_mul_cancel_right]
    _ = soMat v (frPhi v Q₀ T₀ fr y' * x⁻¹) * (soMat v x * locBase v Q₀ T₀ fr) := by
      rw [soMat_mul v (frPhi v Q₀ T₀ fr y' * x⁻¹) x, Matrix.mul_assoc]
    _ = _ := by rw [hxΞ]

/-- The rotation attached to a lattice of $Y_\mathfrak p(\Lambda)$ (improper automorphs of $\mathfrak o_\mathfrak p^N$ make it proper). -/
theorem exists_rot (hQ₀ : Q₀.Nondegenerate) (hn : 0 < r + n') (h : orthGroup (blockForm TF QF') Fv) :
    ∃ φ : SOv v Q₀, latPhi v Q₀ T₀ fr φ = locAct v (h : GL (Fin (r + n')) Fv) (locAct v gv⁻¹ (std v)) := by
  set χ : GL (Fin (r + n')) Fv := gv * (h : GL (Fin (r + n')) Fv) * gv⁻¹ with hχdef
  have hχ : χ ∈ orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv :=
    orth_conj_of_compMat v gv (h : GL (Fin (r + n')) Fv) (frameF v Q₀ T₀ fr) h.2
  obtain ⟨ρ, hρ, hρdet⟩ := exists_stdStab_det_neg_one v Q₀ hQ₀ hn
  have hdet := det_eq_one_or_neg_one (Q₀.map (algebraMap (𝓞 F) F)) (nondegenerate_QF Q₀ hQ₀)
    (⟨χ, hχ⟩ : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)
  obtain ⟨χ', hχ', hdet', hact⟩ : ∃ (χ' : GL (Fin (r + n')) Fv), χ' ∈ orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv ∧
      χ'.val.det = 1 ∧ locAct v χ' (std v) = locAct v χ (std v) := by
    rcases hdet with h1 | h1
    · exact ⟨χ, hχ, h1, rfl⟩
    · refine ⟨χ * (ρ : GL (Fin (r + n')) Fv), (orthGroup _ Fv).mul_mem hχ ρ.2, ?_, ?_⟩
      · rw [Units.val_mul, Matrix.det_mul]
        have h2 : (ρ : GL (Fin (r + n')) Fv).val.det = -1 := hρdet
        have h3 : χ.val.det = -1 := h1
        rw [h2, h3]; norm_num
      · rw [locAct_mul]
        have : locAct v (ρ : GL (Fin (r + n')) Fv) (std v) = std v := hρ
        rw [this]
  let φ : SOv v Q₀ := (⟨⟨χ', hχ'⟩, hdet'⟩ : SOv v Q₀)⁻¹
  refine ⟨φ, ?_⟩
  show locAct v (gv⁻¹ * ((χ')⁻¹)⁻¹) (std v) = _
  rw [inv_inv, locAct_mul, hact, hχdef, ← locAct_mul, ← locAct_mul]
  congr 1
  group

/-- **From orbits of frames to orbits of lattices** (well defined by `Th_rel`). -/
def ThQ (hT : T₀.Nondegenerate) : LocOrbit v Q₀ T₀ fr →
    orbitRel.Quotient (soSub QF' Fv) (LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) :=
  Quotient.lift (fun y => Quotient.mk'' (Th v Q₀ T₀ fr y)) (fun y y' h => by
    obtain ⟨k, hk, hy⟩ := h
    obtain ⟨a, ha⟩ := Th_rel v Q₀ T₀ fr hT k hk hy
    refine Quotient.sound' (orbitRel_apply.mpr ⟨a⁻¹, ?_⟩)
    show a⁻¹ • Th v Q₀ T₀ fr y' = Th v Q₀ T₀ fr y
    rw [← ha, inv_smul_smul])

theorem ThQ_mk (hT : T₀.Nondegenerate) (y : locFrameSet v Q₀ T₀ fr) :
    ThQ v Q₀ T₀ fr hT (Quotient.mk _ y) = Quotient.mk'' (Th v Q₀ T₀ fr y) := rfl

theorem ThQ_bijective (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate) (hn : 0 < r + n') :
    Function.Bijective (ThQ v Q₀ T₀ fr hT) := by
  constructor
  · intro o₁ o₂ h
    induction o₁ using Quotient.inductionOn with | _ y₁ => ?_
    induction o₂ using Quotient.inductionOn with | _ y₂ => ?_
    rw [ThQ_mk, ThQ_mk] at h
    obtain ⟨a, ha⟩ := orbitRel_apply.mp (Quotient.exact' h)
    obtain ⟨k, hk, hy⟩ := Th_inj v Q₀ T₀ fr a ha
    exact (Quotient.sound (show (locOrbitSetoid v Q₀ T₀ fr).r y₂ y₁ from ⟨k, hk, hy⟩)).symm
  · intro o'
    induction o' using Quotient.inductionOn' with | _ M => ?_
    obtain ⟨h, hh⟩ := M.2.1
    obtain ⟨φ, hφ⟩ := exists_rot v Q₀ T₀ fr hQ₀ hn h
    have hMφ : M.1 = latPhi v Q₀ T₀ fr φ := by rw [hφ, hh]
    have hint : ∀ i j, Valued.v ((soMat v φ * locBase v Q₀ T₀ fr) i j) ≤ 1 := fun i j =>
      (stdCol_mem_latPhi_iff v Q₀ T₀ fr φ j).mp (by rw [← hMφ]; exact M.2.2 j) i
    let y : locFrameSet v Q₀ T₀ fr := ⟨soMat v φ * locBase v Q₀ T₀ fr, ⟨φ, rfl⟩, hint⟩
    refine ⟨Quotient.mk _ y, ?_⟩
    rw [ThQ_mk]
    obtain ⟨b, hb⟩ := Xi_stab v Q₀ T₀ fr hT φ (frPhi v Q₀ T₀ fr y) (frPhi_spec v Q₀ T₀ fr y).symm
    apply Quotient.sound'
    refine orbitRel_apply.mpr ⟨b⁻¹, Subtype.ext ?_⟩
    have e1 : (b⁻¹ • M).1 = locAct v (blockGLB (r := r)
        ((b⁻¹ : orthGroup (fr.Q'.map (algebraMap (𝓞 F) F)) Fv) : GL (Fin n') Fv)) M.1 := rfl
    show (b⁻¹ • M).1 = latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y)
    rw [e1, hMφ]
    refine (latPhi_mul_iota v Q₀ T₀ fr φ b⁻¹).trans ?_
    rw [hb, map_inv, inv_inv]

/-- **The orbit stabilizer $K_o$ is the stabilizer of the lattice $M = \Theta(y_o)$** in $SO(Q')(F_\mathfrak p)$. -/
theorem locOrbitStab_eq (o : LocOrbit v Q₀ T₀ fr) :
    locOrbitStab v Q₀ T₀ fr o =
      stabilizer (soSub QF' Fv) (Th v Q₀ T₀ fr (Quotient.out o)) := by
  ext h
  set y := (Quotient.out o : locFrameSet v Q₀ T₀ fr) with hy
  have e1 : (h • Th v Q₀ T₀ fr y).1 =
      latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y * (locIota v Q₀ T₀ fr h)⁻¹) :=
    smul_Mphi_val v Q₀ T₀ fr h _ _
  have e2 : (Th v Q₀ T₀ fr y).1 = latPhi v Q₀ T₀ fr (frPhi v Q₀ T₀ fr y) := rfl
  have e3 : frPhi v Q₀ T₀ fr y * (frPhi v Q₀ T₀ fr y * (locIota v Q₀ T₀ fr h)⁻¹)⁻¹ =
      frPhi v Q₀ T₀ fr y * locIota v Q₀ T₀ fr h * (frPhi v Q₀ T₀ fr y)⁻¹ := by group
  have e4 : (h • Th v Q₀ T₀ fr y = Th v Q₀ T₀ fr y) ↔ ((h • Th v Q₀ T₀ fr y).1 = (Th v Q₀ T₀ fr y).1) :=
    ⟨congrArg Subtype.val, Subtype.ext⟩
  rw [mem_stabilizer_iff, e4, e1, e2, latPhi_eq_iff, e3]
  exact Iff.rfl

/-! ### Finiteness of the local types -/

local notation "QB" => blockForm TF QF'
local notation "Qov" => QuadForm.map (algebraMap 𝔬 Fv) (NF.Qp v Q₀)

open LocalDensity.DVR in
/-- **There are finitely many local types** (extracted from the proof of `frameLocalIdentityGen`: the $K$-orbits of the
integral frames of the types are pairwise separated modulo $\pi^s$). -/
theorem finite_types (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate) :
    Finite (LocFrameTypesG v TF QF' (locAct v gv⁻¹ (std v))) := by
  classical
  have hπ := NF.irreducible_π v
  set Qo := NF.Qp v Q₀ with hQodef
  set To := NF.Qp v T₀ with hTodef
  have hQo : Qo.Nondegenerate := NF.nondegenerate_Qp v hQ₀
  have h2 : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  have h4 : (4 : 𝔬) ≠ 0 := by
    rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  obtain ⟨Pd, dg, hPdet, hdg, hP⟩ := lid_exists_diag_local v T₀ hT
  choose fi hfi hfi' using fun i => DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h4 (hdg i))
  set f := Finset.univ.sup fi with hfdef
  have hf : ∀ i, ¬ NF.π v ^ (f + 1) ∣ 4 * dg i := fun i hh =>
    hfi' i ((pow_dvd_pow _ (by have := Finset.le_sup (f := fi) (Finset.mem_univ i); omega)).trans hh)
  choose hτ yo hτM hτy hτQ using fun t : LocFrameTypesG v TF QF' (locAct v gv⁻¹ (std v)) =>
    frameType_data v Q₀ T₀ fr (locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t)
  have hρ : ∀ (κ : KL v (Qov) (std v)) (z : Fin (r + n') × Fin r → 𝔬),
      ((frameHom r 𝔬).comp (repStd v (Qov))) κ *ᵥ z = frameMat r (repStd v (Qov) κ) *ᵥ z := fun _ _ => rfl
  have hxa : ∀ (κ : KL v (Qov) (std v)) (z : Fin (r + n') × Fin r → 𝔬), formF Qo z = tc To →
      formF Qo (frameMat r (repStd v (Qov) κ) *ᵥ z) = tc To := by
    intro κ z hz
    rw [formF_frameMat_of_compMat _ (compMat_repStd v rfl κ), hz]
  have hdisjAll : ∀ s, r * f + 1 ≤ s → ∀ t t', ∀ a ∈ gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ (yo t),
      ∀ a' ∈ gOrbit ((frameHom r 𝔬).comp (repStd v (Qov))) ⊤ (yo t'), (∀ i, NF.π v ^ s ∣ a i - a' i) → t = t' := by
    rintro s hs t t' a ⟨κ, -, ha⟩ a' ⟨κ', -, ha'⟩ haa'
    have hQa : formF Qo a = tc To := by rw [← ha, hρ]; exact hxa κ _ (hτQ t)
    have hQa' : formF Qo a' = tc To := by rw [← ha', hρ]; exact hxa κ' _ (hτQ t')
    obtain ⟨M₀, hM₀, hM₀a, -⟩ := exists_frame_openMat hπ Qo To hPdet hP hdg hf hs hQa hQa'
      (fun i => by rw [← dvd_neg, neg_sub]; exact haa' i)
    obtain ⟨τT, hτT⟩ := exists_repStd_eq v rfl hQo M₀ hM₀
    set κ₀ := κ'⁻¹ * τT * κ with hκ₀def
    have hκ₀ : frameMat r (repStd v (Qov) κ₀) *ᵥ yo t = yo t' := by
      have hτ' : ((frameHom r 𝔬).comp (repStd v (Qov))) τT *ᵥ a = a' := by
        rw [hρ, hτT]; exact hM₀a
      show ((frameHom r 𝔬).comp (repStd v (Qov))) κ₀ *ᵥ yo t = yo t'
      rw [hκ₀def, map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, ha, hτ', ← ha']
      exact mulVec_inv_mulVec_g ((frameHom r 𝔬).comp (repStd v (Qov))) κ' _
    obtain ⟨a₀, ha₀⟩ := lattice_of_orbit v Q₀ T₀ fr hT (hτ t) (hτ t') (yo t) (yo t') (hτy t) (hτy t') κ₀ hκ₀
    have hmem : locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t' ∈
        orbit (orthGroup QF' Fv) (locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t) := by
      refine ⟨a₀, Subtype.ext ?_⟩
      rw [LocFrameSetG.smul_val, ← hτM t, ← hτM t']
      exact ha₀
    have := Quotient.sound' (s₁ := orbitRel _ _) hmem
    rw [locFrameRepG_mk, locFrameRepG_mk] at this
    exact this.symm
  have := DVR.finite_vec (ι := Fin (r + n') × Fin r) (NF.π v) hπ (r * f + 1)
  refine Finite.of_injective (fun t => DVR.redI (NF.π v) (r * f + 1) (yo t)) fun t t' htt => ?_
  exact hdisjAll (r * f + 1) le_rfl t t' (yo t) ⟨1, Subgroup.mem_top 1, by simp⟩ (yo t')
    ⟨1, Subgroup.mem_top 1, by simp⟩ ((DVR.redI_eq_iff _ _ _ _).mp htt)

/-- **The local factor of Weil's measure of the integral frames**: $\sum_o\mu_\mathfrak p(K)/\mu'_\mathfrak p(K_o)$. -/
def locOrbitSum : ℝ≥0∞ :=
  ∑' o : LocOrbit v Q₀ T₀ fr, muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) /
    muLocSO v fr.Q' 1 (locOrbitStab v Q₀ T₀ fr o : Set (SOv v fr.Q'))

theorem locFrameWeightG_nonneg (M : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) :
    0 ≤ locFrameWeightG v TF QF' (locAct v gv⁻¹ (std v)) M := by
  unfold locFrameWeightG; positivity

/-- **The weighted sum over the $O(Q')$-orbits of lattices** in $[0,\infty]$ is the type sum $W_\mathfrak p(\Lambda)$. -/
theorem tsum_weights_eq (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate) (hQ' : fr.Q'.Nondegenerate) :
    ∑' t : orbitRel.Quotient (orthGroup QF' Fv) (LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))),
      muLoc v fr.Q' 1 (stdStab QF' v : Set (orthGroup QF' Fv)) /
        muLoc v fr.Q' 1 (stabilizer (orthGroup QF' Fv) (Quotient.out t) : Set (orthGroup QF' Fv)) =
    ENNReal.ofReal (locFrameTypeSumG v TF QF' (locAct v gv⁻¹ (std v))) := by
  classical
  have := finite_types v Q₀ T₀ fr hQ₀ hT
  have : Fintype (LocFrameTypesG v TF QF' (locAct v gv⁻¹ (std v))) := Fintype.ofFinite _
  have := Weil.isMulRightInvariant_muLoc v fr.Q' hQ'
  have hterm : ∀ t : LocFrameTypesG v TF QF' (locAct v gv⁻¹ (std v)),
      muLoc v fr.Q' 1 (stdStab QF' v : Set (orthGroup QF' Fv)) /
        muLoc v fr.Q' 1 (stabilizer (orthGroup QF' Fv) (Quotient.out t) : Set (orthGroup QF' Fv)) =
      ENNReal.ofReal (locFrameWeightG v TF QF' (locAct v gv⁻¹ (std v))
        (locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t)) := by
    intro t
    obtain ⟨a, ha⟩ : ∃ a : orthGroup QF' Fv, a • (Quotient.out t : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) =
        locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t := by
      have h1 : orbitRel (orthGroup QF' Fv) (LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v)))
          (locFrameRepG v TF QF' (locAct v gv⁻¹ (std v)) t) (Quotient.out t) := by
        apply Quotient.exact'
        rw [locFrameRepG_mk, Quotient.out_eq']
      exact orbitRel_apply.mp h1
    rw [← measure_stdStab_div_stab v Q₀ T₀ fr hQ', ← ha, measure_stab_smul]
  rw [tsum_congr hterm, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun t _ => locFrameWeightG_nonneg v Q₀ T₀ fr _),
    locFrameTypeSumG, finsum_eq_sum_of_fintype]

/-- **The measure of the stabilizer $K_o$ in $SO(Q')$** is the measure of the stabilizer in $SO(Q')$ of the representative of the
lattice orbit (as subgroups of $O(Q')$). -/
theorem muLocSO_locOrbitStab (hQ' : fr.Q'.Nondegenerate) (hn' : 0 < n') (hT : T₀.Nondegenerate)
    (o : LocOrbit v Q₀ T₀ fr) :
    muLocSO v fr.Q' 1 (locOrbitStab v Q₀ T₀ fr o : Set (SOv v fr.Q')) =
      muLoc v fr.Q' 1 (((stabilizer (soSub QF' Fv)
        (Quotient.out (ThQ v Q₀ T₀ fr hT o) : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v)))).map
          (soSub QF' Fv).subtype : Subgroup (orthGroup QF' Fv)) : Set (orthGroup QF' Fv)) := by
  have := Weil.isMulRightInvariant_muLoc v fr.Q' hQ'
  rw [muLocSO_eq_comap v fr.Q' hQ' hn' one_pos, (measurableEmbedding_soSub v fr.Q' hQ').comap_apply]
  set x := Th v Q₀ T₀ fr (Quotient.out o) with hx
  have hq : ThQ v Q₀ T₀ fr hT o = Quotient.mk'' x := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  obtain ⟨a, ha⟩ := orbitRel_apply.mp (Quotient.exact' (Quotient.out_eq'
    (Quotient.mk'' x : orbitRel.Quotient (soSub QF' Fv) (LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))))))
  have ha' : (a : orthGroup QF' Fv) • x = Quotient.out (Quotient.mk'' x :
      orbitRel.Quotient (soSub QF' Fv) (LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v)))) := ha
  rw [hq, ← ha', locOrbitStab_eq]
  have e : Subtype.val '' (stabilizer (soSub QF' Fv) x : Set (SOv v fr.Q')) =
      ((stabilizer (soSub QF' Fv) x).map (soSub QF' Fv).subtype : Set (orthGroup QF' Fv)) := by
    rw [Subgroup.coe_map]; rfl
  have e2 : ((stabilizer (soSub QF' Fv) ((a : orthGroup QF' Fv) • x)).map (soSub QF' Fv).subtype : Subgroup _) =
      (soSub QF' Fv ⊓ stabilizer (orthGroup QF' Fv) ((a : orthGroup QF' Fv) • x)) :=
    map_stabilizer_subtype (soSub QF' Fv) _
  rw [e, e2, measure_inf_stab_smul _ _ _ a.2, ← map_stabilizer_subtype]

/-- **The local identity for frames, special orthogonal form** (every finite prime, dyadic included):
$$\sum_o\frac{\mu_\mathfrak p(SO(L_\mathfrak p))}{\mu'_\mathfrak p(K_o)} = \beta_\mathfrak p(Q_0,T_0)\,|\det g|_\mathfrak p^{\,n'+1}\,|\det H_{T_0}|_\mathfrak p^{-n'}.$$ -/
@[kb "weil1982" "§3.4 and §4.5 (local identity for frames, SO form) [unverified]"]
theorem locOrbitSum_eq (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate) (hn' : 1 ≤ n') :
    locOrbitSum v Q₀ T₀ fr = ENNReal.ofReal (NF.localDensityForm v Q₀ T₀ *
      ‖algebraMap F Fv fr.g.val.det‖ ^ (n' + 1) / ‖algebraMap F Fv (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n') := by
  classical
  have hn0 : 0 < n' := hn'
  have hN : 0 < r + n' := by omega
  have hQ' : fr.Q'.Nondegenerate := adapted_nondegenerate Q₀ T₀ fr hQ₀
  have := Weil.isMulRightInvariant_muLoc v fr.Q' hQ'
  -- the improper automorph of `O(Q')`
  obtain ⟨ρ, hρ, hρdet⟩ := exists_stdStab_det_neg_one v fr.Q' hQ' hn0
  have hQF' := nondegenerate_QF fr.Q' hQ'
  have hH2 : (soSub QF' Fv).index = 2 := by
    have := relIndex_soSub_eq_two QF' hQF' ⊤ ρ (Subgroup.mem_top _) hρdet
    rwa [Subgroup.relIndex_top_right, inf_top_eq] at this
  have hK₀ : ¬ stdStab QF' v ≤ soSub QF' Fv := by
    intro h
    have h1 : (ρ : GL (Fin n') Fv).val.det = 1 := h hρ
    rw [hρdet] at h1
    have : (2 : Fv) = 0 := by linear_combination -h1
    exact two_ne_zero this
  have hmeasH : MeasurableSet (soSub QF' Fv : Set (orthGroup QF' Fv)) := (isOpen_soSub v QF' hQF').measurableSet
  have hAbs := tsum_orbits_index_two (Y := LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) (muLoc v fr.Q' 1)
    (soSub QF' Fv) (stdStab QF' v) hH2 hK₀ hmeasH
  rw [tsum_weights_eq v Q₀ T₀ fr hQ₀ hT hQ'] at hAbs
  -- numbers
  have hβ₀ := LatChange.localDensityForm_self_pos v Q₀ hQ₀
  have hβ' := LatChange.localDensityForm_self_pos v fr.Q' hQ'
  set β₀ := NF.localDensityForm v Q₀ Q₀ with hβ₀def
  set β' := NF.localDensityForm v fr.Q' fr.Q' with hβ'def
  have hA : muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (1 / 2 * β₀) := by
    rw [muLocSO_soStabSO]
    simp [NF.siegelDensity, hβ₀def]
  have hC : muLoc v fr.Q' 1 ((stdStab QF' v ⊓ soSub QF' Fv : Subgroup (orthGroup QF' Fv)) : Set (orthGroup QF' Fv)) =
      ENNReal.ofReal (1 / 2 * β') := by
    have := muLoc_soStab v fr.Q' hQ' hn0 one_pos
    rw [inf_comm]
    rw [show ((soSub QF' Fv ⊓ stdStab QF' v : Subgroup (orthGroup QF' Fv)) : Set (orthGroup QF' Fv)) =
      (soStab v fr.Q' : Set (orthGroup QF' Fv)) from rfl, this]
    simp [NF.siegelDensity, hβ'def]
  set e := Equiv.ofBijective (ThQ v Q₀ T₀ fr hT) (ThQ_bijective v Q₀ T₀ fr hQ₀ hT hN) with he
  set C := muLoc v fr.Q' 1 ((stdStab QF' v ⊓ soSub QF' Fv : Subgroup (orthGroup QF' Fv)) : Set (orthGroup QF' Fv)) with hCdef
  set ρ' : ℝ≥0∞ := ENNReal.ofReal (β₀ / β') with hρ'
  have hAC : muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) = ρ' * C := by
    rw [hA, hC, hρ', ← ENNReal.ofReal_mul (div_nonneg hβ₀.le hβ'.le)]
    congr 1
    field_simp
  have hterm : ∀ o : LocOrbit v Q₀ T₀ fr,
      muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) / muLocSO v fr.Q' 1 (locOrbitStab v Q₀ T₀ fr o : Set (SOv v fr.Q')) =
      ρ' * (C / muLoc v fr.Q' 1 (((stabilizer (soSub QF' Fv)
        (Quotient.out (e o) : LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v)))).map
          (soSub QF' Fv).subtype : Subgroup (orthGroup QF' Fv)) : Set (orthGroup QF' Fv))) := by
    intro o
    rw [muLocSO_locOrbitStab v Q₀ T₀ fr hQ' hn0 hT o, hAC, mul_div_assoc]
    rfl
  unfold locOrbitSum
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  have hsum := Equiv.tsum_eq e (fun o' : orbitRel.Quotient (soSub QF' Fv)
    (LocFrameSetG v TF QF' (locAct v gv⁻¹ (std v))) => C / muLoc v fr.Q' 1 (((stabilizer (soSub QF' Fv)
      (Quotient.out o')).map (soSub QF' Fv).subtype : Subgroup (orthGroup QF' Fv)) : Set (orthGroup QF' Fv)))
  rw [hsum, ← hAbs, hρ', ← ENNReal.ofReal_mul (div_nonneg hβ₀.le hβ'.le)]
  -- the identity
  have hid := frameLocalIdentityGen v Q₀ hQ₀ T₀ hT fr
  have hHT : ‖algebraMap F Fv (algebraMap (𝓞 F) F T₀.hessian.det)‖ ≠ 0 := by
    have h1 : algebraMap (𝓞 F) F T₀.hessian.det ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
    exact norm_ne_zero_iff.mpr ((map_ne_zero_iff _ (algebraMap F Fv).injective).mpr h1)
  congr 1
  rw [div_mul_eq_mul_div, div_eq_div_iff hβ'.ne' (pow_ne_zero _ hHT)]
  linear_combination hid

end Local

end QuadFormsKB.Tamagawa.Indefinite
