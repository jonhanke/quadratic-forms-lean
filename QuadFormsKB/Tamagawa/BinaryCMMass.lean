import QuadFormsKB.Tamagawa.BinaryCMClasses

/-!
# The mass of the maximal order of $F(\sqrt{-D})$

**Layer:** $F$ totally real, $E = F(\theta)$ a CM extension, $\theta^2 = -D$; $Q = \langle1,D\rangle$, `latE` $= c^{-1}(\mathcal O_E)$.

**Proves**
* (general) `mass_eq_orbitMass`: the mass of a genus is the orbit mass of $O(V)(F)$ acting on the genus (as a set of lattices);
  `orbitMass_so_eq_two_mul`: for $SO(V)(F)$ (index $2$) the orbit mass doubles (`orbitMass_subgroup`).
* `orbitRel_latJ_iff`: two lattices $(\sigma\delta)^{-1}\mathfrak B\sigma\mathfrak B'$ are properly isometric iff the $j$ takes the same value on
  $[\mathfrak B]$ (via `exists_normOne_smul_iff`); every lattice of the genus is properly isometric to one of them
  (`exists_orbitRel_latJ`, via `mem_range_jHom_iff`: the Hasse norm theorem and an ideal Hilbert 90).
* `orbitsEquivRange`: proper classes in the genus of $\mathcal O_E$ $\simeq$ the image of $j : \mathrm{Cl}_E \to$ `PairClass`;
  `card_stabilizer_so`: every proper stabilizer has $w_E$ elements (`properAutEquiv`, `card_normOneUnits`).
* **`mass_latE`**: $$\mathrm{Mass}(\mathcal O_E, \langle1,D\rangle) = \frac{h_E\,[\mu_E : \{u/\sigma u\}]}{2^{t+1}\,h_F\,w_E},$$
  $t$ = number of ramified primes (`card_principalGenus_mul_card_strAmb`-type count, `card_strAmb_mul_index`).

Source: Shimura 2010, §4 [unverified]; Conway–Sloane 1988, §2 (proper vs improper classes) [unverified].

-/

open NumberField IsDedekindDomain Matrix MulAction
open scoped nonZeroDivisors
open NumberField.Units

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

open Lattices QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne

/-! ### The genus as a set with an action of $O(V)(F)$ -/

section General

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (L : Lat F n)

/-- **The genus of `L` as a type** (lattices $M$ with $M \in \mathrm{gen}(L)$). -/
abbrev GenusSet := {M : Lat F n // SameGenus Q L.1 M.1}

/-- $O(V)(F)$ acts on the genus by $\gamma\cdot M = \gamma M$. -/
def genusSmul (γ : orthGroup Q F) (M : GenusSet Q L) : GenusSet Q L :=
  ⟨Lat.image (γ : GL (Fin n) F) M.1, SameGenus.trans Q M.2 (IsIsometric.sameGenus Q ⟨γ, γ.2, rfl⟩)⟩

instance genusAction : MulAction (orthGroup Q F) (GenusSet Q L) where
  smul := genusSmul Q L
  one_smul _ := Subtype.ext (Subtype.ext (glImage_one _))
  mul_smul _ _ _ := Subtype.ext (Subtype.ext (glImage_mul _ _ _))

theorem genus_smul_val (γ : orthGroup Q F) (M : GenusSet Q L) :
    ((γ • M : GenusSet Q L).1.1) = glImage (γ : GL (Fin n) F) M.1.1 := rfl

theorem mem_stabilizer_genus_iff (γ : orthGroup Q F) (M : GenusSet Q L) :
    γ ∈ stabilizer (orthGroup Q F) M ↔ γ ∈ autLat Q M.1.1 := by
  rw [mem_stabilizer_iff, mem_autLat]
  constructor
  · intro h; exact congrArg (fun N : GenusSet Q L => N.1.1) h
  · intro h; exact Subtype.ext (Subtype.ext h)

/-- **The mass of a genus is the orbit mass of $O(V)(F)$ on the genus.** -/
theorem mass_eq_orbitMass : mass Q L = orbitMass (orthGroup Q F) (GenusSet Q L) := by
  classical
  let Φ : orbitRel.Quotient (orthGroup Q F) (GenusSet Q L) → LatClass Q := fun ω => Quotient.mk _ ω.out.1
  have hΦ : ∀ M : GenusSet Q L, Φ (Quotient.mk'' M) = Quotient.mk _ M.1 := by
    intro M
    apply Quotient.sound
    obtain ⟨γ, hγ⟩ := out_mem_orbit (Quotient.mk'' M : orbitRel.Quotient (orthGroup Q F) (GenusSet Q L)) M rfl
    show IsIsometric Q (Quotient.out (Quotient.mk'' M : orbitRel.Quotient _ _)).1.1 M.1.1
    rw [← hγ]
    exact IsIsometric.symm Q ⟨γ, γ.2, rfl⟩
  have hinj : Function.Injective Φ := by
    intro ω₁ ω₂ h
    induction ω₁ using Quotient.inductionOn' with | h M₁ => ?_
    induction ω₂ using Quotient.inductionOn' with | h M₂ => ?_
    rw [hΦ, hΦ] at h
    obtain ⟨γ, hγ, he⟩ := Quotient.exact h
    apply Quotient.sound'
    rw [orbitRel_apply]
    refine ⟨(⟨γ, hγ⟩ : orthGroup Q F)⁻¹, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    rw [genus_smul_val, ← he, Subgroup.coe_inv, ← glImage_mul, inv_mul_cancel, glImage_one]
  have hrange : Φ '' Set.univ = genusClasses Q L := by
    ext c
    constructor
    · rintro ⟨ω, -, rfl⟩
      exact ⟨ω.out.1, rfl, ω.out.2⟩
    · rintro ⟨M, rfl, hM⟩
      exact ⟨Quotient.mk'' ⟨M, hM⟩, Set.mem_univ _, hΦ ⟨M, hM⟩⟩
  unfold mass orbitMass
  rw [← hrange, finsum_mem_image hinj.injOn, finsum_mem_univ]
  congr 1
  ext ω
  show ((Nat.card (autLat Q ω.out.1.1) : ℝ))⁻¹ = _
  congr 2
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun γ => mem_stabilizer_genus_iff Q L γ ω.out)).symm

theorem finite_orbits_genus {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1) :
    Finite (orbitRel.Quotient (orthGroup Q F) (GenusSet Q L)) := by
  classical
  let Φ : orbitRel.Quotient (orthGroup Q F) (GenusSet Q L) → LatClass Q := fun ω => Quotient.mk _ ω.out.1
  have hinj : Function.Injective Φ := by
    intro ω₁ ω₂ h
    obtain ⟨γ, hγ, he⟩ := Quotient.exact h
    rw [← Quotient.out_eq' ω₁, ← Quotient.out_eq' ω₂]
    apply Quotient.sound'
    rw [orbitRel_apply]
    refine ⟨(⟨γ, hγ⟩ : orthGroup Q F)⁻¹, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    rw [genus_smul_val, ← he, Subgroup.coe_inv, ← glImage_mul, inv_mul_cancel, glImage_one]
  have hsub : Set.range Φ ⊆ genusClasses Q L := by
    rintro _ ⟨ω, rfl⟩; exact ⟨ω.out.1, rfl, ω.out.2⟩
  have hfin := (genusClasses_finite hQ L hLi).subset hsub
  have : Finite (Set.range Φ) := Set.finite_coe_iff.mpr hfin
  exact Finite.of_injective_finite_range hinj

theorem finite_stabilizer_genus {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    (M : GenusSet Q L) : Finite (stabilizer (orthGroup Q F) M) := by
  have := finite_autLat hQ M.1.2 (SameGenus.isIntegral Q hLi M.2)
  exact Finite.of_equiv _ (Equiv.subtypeEquivRight fun γ => (mem_stabilizer_genus_iff Q L γ M).symm)

/-- $[O(V)(F) : SO(V)(F)] = 2$ for nondegenerate $Q$ in positive rank. -/
theorem index_soSub (hQ : Q.Nondegenerate) (hn : 0 < n) : (soSub Q F).index = 2 := by
  obtain ⟨ρ, hρ⟩ := exists_orthGroup_det_neg_one Q hQ hn
  rw [Subgroup.index_eq_two_iff]
  refine ⟨ρ, fun b => ?_⟩
  have hmem : ∀ g : orthGroup Q F, g ∈ soSub Q F ↔ (g : GL (Fin n) F).val.det = 1 := fun _ => Iff.rfl
  rw [hmem, hmem, Subgroup.coe_mul, Units.val_mul, det_mul, hρ]
  rcases det_eq_one_or_neg_one Q hQ b with h | h <;> rw [h] <;> norm_num

/-- **The $SO$-orbit mass is twice the $O$-orbit mass** on the genus. -/
theorem orbitMass_so_eq_two_mul {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (hn : 0 < n) (L : Lat F n)
    (hLi : IsIntegral Q L.1) :
    orbitMass (soSub Q F) (GenusSet Q L) = 2 * mass Q L := by
  have hidx := index_soSub Q hQ.nondegenerate hn
  have : (soSub Q F).FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  have := finite_orbits_genus hQ L hLi
  rw [orbitMass_subgroup (soSub Q F) (finite_stabilizer_genus hQ L hLi), hidx, mass_eq_orbitMass]
  norm_num

end General

/-! ### Proper classes in the genus of $\mathcal O_E$ -/

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {D : 𝓞 F} (S : SqrtData D E)

local notation "QD" => formF (diagForm1 D)

theorem latOf_injective : Function.Injective (latOf S) := by
  intro A A' h
  exact Submodule.comap_injective_of_surjective (f := cLin S) (fun z => ⟨coordOf S z, cE_coordOf S z⟩) h

theorem cE_e0 : cE S ![1, 0] = 1 := by simp [cE]

/-- **Proper isometries between lattices of submodules of $E$ are norm-one multipliers.** -/
theorem exists_so_glImage_iff (A A' : Submodule (𝓞 F) E) :
    (∃ γ ∈ orthGroup QD F, γ.val.det = 1 ∧ glImage γ (latOf S A) = latOf S A') ↔
      ∃ u : E, Algebra.norm F u = 1 ∧ smulLat u A = A' := by
  constructor
  · rintro ⟨γ, hγ, hdet, he⟩
    obtain ⟨u, hu, rfl⟩ := exists_rotE_eq S hγ hdet
    exact ⟨u, hu, latOf_injective S (by rw [← glImage_rotE S hu, he])⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨rotE S hu, rotE_mem S hu, det_rotE S hu, glImage_rotE S hu A⟩

variable [IsTotallyReal F]

/-- A triple $(\mathfrak B, \mathfrak B', \delta)$ with $\mathfrak B\mathfrak B' = (\delta)$ (input of the $j$). -/
structure JTriple (E : Type) [Field E] [NumberField E] where
  B : (Ideal (𝓞 E))⁰
  B' : (Ideal (𝓞 E))⁰
  δ : 𝓞 E
  h : (B : Ideal (𝓞 E)) * (B' : Ideal (𝓞 E)) = Ideal.span {δ}

theorem JTriple.δ_ne_zero (T : JTriple E) : T.δ ≠ 0 := by
  intro h0
  have := T.h
  rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, ← Ideal.zero_eq_bot] at this
  exact mul_ne_zero (nonZeroDivisors.coe_ne_zero T.B) (nonZeroDivisors.coe_ne_zero T.B') this

theorem JTriple.B_ne_bot (T : JTriple E) : (T.B : Ideal (𝓞 E)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero T.B

theorem conj_coe_ne_zero {x : 𝓞 E} (hx : x ≠ 0) : conj F E (x : E) ≠ 0 := by
  simpa using algebraMap_ne_zero hx

/-- **The lattice $(\sigma\delta)^{-1}\mathfrak B\,\sigma\mathfrak B'$** of a triple, as an element of the genus of $\mathcal O_E$. -/
def latJ (T : JTriple E) : GenusSet QD (latEL S) :=
  ⟨⟨latI S (conj F E (T.δ : E))⁻¹ ((T.B : Ideal (𝓞 E)) * conjIdeal F (T.B' : Ideal (𝓞 E))),
    isLattice_latI S (inv_ne_zero (conj_coe_ne_zero T.δ_ne_zero)) ne_bot_of_mul_eq_span⟩,
    sameGenus_latI_jPair S T.B_ne_bot T.δ_ne_zero T.h⟩

/-- The pair of a triple. -/
abbrev jPair (T : JTriple E) : NormPairs F E := jPairOf T.B T.B' T.δ T.h

theorem norm_inv' (x : E) : Algebra.norm F x⁻¹ = (Algebra.norm F x)⁻¹ := by
  rw [← one_div, norm_div', map_one, one_div]

theorem norm_inv_conj_mul (x : 𝓞 E) (hx : x ≠ 0) :
    Algebra.norm F (conj F E (x : E))⁻¹ * ((Algebra.intNorm (𝓞 F) (𝓞 E) x : 𝓞 F) : F) = 1 := by
  rw [coe_intNorm, nrm, norm_inv', norm_conj, inv_mul_cancel₀]
  exact Algebra.norm_ne_zero_iff.mpr (algebraMap_ne_zero hx)

/-- The proper-isometry orbit relation on the genus, unfolded. -/
theorem orbitRel_so_iff (M M' : GenusSet QD (latEL S)) :
    orbitRel (soSub QD F) (GenusSet QD (latEL S)) M M' ↔
      ∃ γ ∈ orthGroup QD F, γ.val.det = 1 ∧ glImage γ M'.1.1 = M.1.1 := by
  rw [orbitRel_apply]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1.1, g.1.2, g.2, congrArg (fun N : GenusSet QD (latEL S) => N.1.1) hg⟩
  · rintro ⟨γ, hγ, hdet, he⟩
    exact ⟨⟨⟨γ, hγ⟩, hdet⟩, Subtype.ext (Subtype.ext he)⟩

/-- **Two lattices of triples are properly isometric iff their pairs are properly equivalent** (iff $j$ agrees). -/
theorem orbitRel_latJ_iff (T T' : JTriple E) :
    orbitRel (soSub QD F) (GenusSet QD (latEL S)) (latJ S T) (latJ S T') ↔
      ((jPair T : NormPairs F E) : PairClass F E) = ((jPair T' : NormPairs F E) : PairClass F E) := by
  rw [orbitRel_so_iff]
  show (∃ γ ∈ orthGroup QD F, γ.val.det = 1 ∧ glImage γ (latOf S _) = latOf S _) ↔ _
  rw [exists_so_glImage_iff, exists_normOne_smul_iff (norm_inv_conj_mul T'.δ T'.δ_ne_zero)
    (norm_inv_conj_mul T.δ T.δ_ne_zero), Con.eq]
  have e : ∀ p q : NormPairs F E, pairCon F E p q ↔ PairRel F E p q := fun _ _ => Iff.rfl
  rw [e]
  constructor
  · rintro ⟨α, β, hα, hβ, h1, h2⟩
    exact ⟨β, α, hβ, hα, h1.symm, h2.symm⟩
  · rintro ⟨α, β, hα, hβ, h1, h2⟩
    exact ⟨β, α, hβ, hα, h1.symm, h2.symm⟩

/-- **Every lattice of the genus is properly isometric to the lattice of a triple.** -/
theorem exists_orbitRel_latJ [IsTotallyComplex E] (M : GenusSet QD (latEL S)) :
    ∃ T : JTriple E, orbitRel (soSub QD F) (GenusSet QD (latEL S)) (latJ S T) M := by
  obtain ⟨d, 𝔄, hd, h𝔄, hrel, hM⟩ := exists_pair_of_genus S M.1.2 M.2
  let p : NormPairs F E := ⟨(𝔄, d ^ 2), h𝔄, hrel⟩
  have hd' : (d : F) ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hd
  have hp : (p : PairClass F E) ∈ Set.range (jHom F E) := by
    rw [mem_range_jHom_iff]
    refine ⟨(isPos_mk p).mpr fun w => ?_, ?_⟩
    · show 0 < Siegel.realEmb w (((d ^ 2 : 𝓞 F)) : F)
      have h0 : Siegel.realEmb w (d : F) ≠ 0 := (map_ne_zero _).mpr hd'
      push_cast
      rw [map_pow]
      positivity
    · funext v
      rw [genusHom_mk]
      show genusSym E v (((d ^ 2 : 𝓞 F)) : F) = 1
      push_cast
      rw [← norm_algebraMap_F (E := E)]
      exact genusSym_norm v _
  obtain ⟨c, hc⟩ := hp
  obtain ⟨B, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨B', δ, hB⟩ := exists_mul_eq_span B
  refine ⟨⟨B, B', δ, hB⟩, ?_⟩
  rw [jHom_mk0 hB, Con.eq] at hc
  rw [orbitRel_so_iff]
  show ∃ γ ∈ orthGroup QD F, γ.val.det = 1 ∧ glImage γ M.1.1 = latOf S _
  rw [hM]
  show ∃ γ ∈ orthGroup QD F, γ.val.det = 1 ∧ glImage γ (latOf S _) = latOf S _
  rw [exists_so_glImage_iff]
  have h1 : Algebra.norm F (algebraMap F E (d : F))⁻¹ * (((d ^ 2 : 𝓞 F)) : F) = 1 := by
    push_cast
    rw [norm_inv', norm_algebraMap_F, inv_mul_cancel₀ (pow_ne_zero 2 hd')]
  obtain ⟨u, hu, he⟩ := (exists_normOne_smul_iff (𝔄 := (B : Ideal (𝓞 E)) * conjIdeal F (B' : Ideal (𝓞 E)))
    (𝔅 := 𝔄) (norm_inv_conj_mul δ (JTriple.δ_ne_zero ⟨B, B', δ, hB⟩)) h1).mpr hc
  refine ⟨u⁻¹, by rw [norm_inv', hu, inv_one], ?_⟩
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rw [← he, smulLat_inv_smulLat hu0]

/-! ### Counting proper classes and stabilizers -/

variable [IsTotallyComplex E]

theorem exists_triple (g : Set.range (jHom F E)) :
    ∃ T : JTriple E, ((jPair T : NormPairs F E) : PairClass F E) = g := by
  obtain ⟨_, c, rfl⟩ := g
  obtain ⟨B, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨B', δ, hB⟩ := exists_mul_eq_span B
  exact ⟨⟨B, B', δ, hB⟩, (jHom_mk0 hB).symm⟩

/-- A triple representing a value of $j$. -/
def tripleOf (g : Set.range (jHom F E)) : JTriple E := (exists_triple g).choose

theorem jPair_tripleOf (g : Set.range (jHom F E)) :
    ((jPair (tripleOf g) : NormPairs F E) : PairClass F E) = g := (exists_triple g).choose_spec

/-- The map from the image of $j$ to the proper classes in the genus of $\mathcal O_E$. -/
def orbitsMap (g : Set.range (jHom F E)) : orbitRel.Quotient (soSub QD F) (GenusSet QD (latEL S)) :=
  Quotient.mk'' (latJ S (tripleOf g))

/-- **Proper classes in the genus of $\mathcal O_E$ $\simeq$ the image of $j$** (the $j : \mathrm{Cl}_E \to$ `PairClass`). -/
theorem orbitsMap_bijective : Function.Bijective (orbitsMap S (F := F) (E := E)) := by
  constructor
  · intro g₁ g₂ h
    have h' := Quotient.exact' h
    rw [orbitRel_latJ_iff, jPair_tripleOf, jPair_tripleOf] at h'
    exact Subtype.ext h'
  · intro ω
    induction ω using Quotient.inductionOn' with | h M => ?_
    obtain ⟨T, hT⟩ := exists_orbitRel_latJ S M
    let g : Set.range (jHom F E) := ⟨jHom F E (ClassGroup.mk0 T.B), Set.mem_range_self _⟩
    refine ⟨g, ?_⟩
    have h1 : orbitRel (soSub QD F) (GenusSet QD (latEL S)) (latJ S (tripleOf g)) (latJ S T) := by
      rw [orbitRel_latJ_iff, jPair_tripleOf]
      exact jHom_mk0 T.h
    show (Quotient.mk'' (latJ S (tripleOf g)) : orbitRel.Quotient _ _) = Quotient.mk'' M
    rw [Quotient.sound' h1, Quotient.sound' hT]

theorem rotE_congr {u v : E} (h : u = v) (hu : Algebra.norm F u = 1) (hv : Algebra.norm F v = 1) :
    rotE S hu = rotE S hv := by subst h; rfl

theorem cE_rotE_e0 {u : E} (hu : Algebra.norm F u = 1) : cE S ((rotE S hu).val *ᵥ ![1, 0]) = u := by
  rw [cE_rotE_mulVec, cE_e0, mul_one]

theorem norm_cE_e0_of_so {γ : GL (Fin 2) F} (hγ : γ ∈ orthGroup QD F) (hdet : γ.val.det = 1) :
    Algebra.norm F (cE S (γ.val *ᵥ ![1, 0])) = 1 := by
  obtain ⟨u, hu, rfl⟩ := exists_rotE_eq S hγ hdet
  rw [cE_rotE_e0]; exact hu

theorem rotE_cE_e0 {γ : GL (Fin 2) F} (hγ : γ ∈ orthGroup QD F) (hdet : γ.val.det = 1) :
    rotE S (norm_cE_e0_of_so S hγ hdet) = γ := by
  obtain ⟨u, hu, rfl⟩ := exists_rotE_eq S hγ hdet
  exact rotE_congr S (cE_rotE_e0 S hu) _ hu

theorem smulLat_comm (a b : E) (L : Submodule (𝓞 F) E) : smulLat a (smulLat b L) = smulLat b (smulLat a L) := by
  rw [smulLat_smulLat, smulLat_smulLat, mul_comm]

/-- **Every proper stabilizer in the genus of $\mathcal O_E$ has $w_E$ elements:** $SO(M) \simeq \{u : N(u) = 1,\ u\mathfrak A = \mathfrak A\}
\simeq \{u \in \mathcal O_E^\times : N(u) = 1\} = \mu_E$ (`properAutEquiv`, `card_normOneUnits`). -/
theorem card_stabilizer_so (M : GenusSet QD (latEL S)) :
    Nat.card (stabilizer (soSub QD F) M) = torsionOrder E := by
  obtain ⟨d, 𝔄, hd, h𝔄, -, hM⟩ := exists_pair_of_genus S M.1.2 M.2
  set dE := algebraMap F E (algebraMap (𝓞 F) F d)
  have hdE : dE⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F E).injective]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hd
  have hMA : M.1.1 = latOf S (smulLat dE⁻¹ (idealLat F 𝔄)) := hM
  have key : ∀ u : E, (smulLat u (smulLat dE⁻¹ (idealLat F 𝔄)) = smulLat dE⁻¹ (idealLat F 𝔄) ↔
      smulLat u (idealLat F 𝔄) = idealLat F 𝔄) := fun u => by
    rw [smulLat_comm]
    exact ⟨fun h => smulLat_cancel hdE h, fun h => by rw [h]⟩
  have hstab : ∀ g : soSub QD F, g ∈ stabilizer (soSub QD F) M ↔
      glImage (g : orthGroup QD F).1 (latOf S (smulLat dE⁻¹ (idealLat F 𝔄))) =
        latOf S (smulLat dE⁻¹ (idealLat F 𝔄)) := fun g => by
    rw [mem_stabilizer_iff, ← hMA]
    constructor
    · intro h; exact congrArg (fun N : GenusSet QD (latEL S) => N.1.1) h
    · intro h; exact Subtype.ext (Subtype.ext h)
  rw [← card_normOneUnits (F := F), ← Nat.card_congr (properAutEquiv (F := F) h𝔄)]
  refine Nat.card_congr
    { toFun := fun g => ⟨cE S ((g : soSub QD F).1.1.val *ᵥ ![1, 0]),
        norm_cE_e0_of_so S (g : soSub QD F).1.2 (g : soSub QD F).2, by
          have h1 := (hstab g).mp g.2
          rw [← rotE_cE_e0 S (g : soSub QD F).1.2 (g : soSub QD F).2, glImage_rotE] at h1
          exact (key _).mp (latOf_injective S h1)⟩
      invFun := fun u => ⟨⟨⟨rotE S u.2.1, rotE_mem S u.2.1⟩, det_rotE S u.2.1⟩, by
          rw [hstab]
          show glImage (rotE S u.2.1) _ = _
          rw [glImage_rotE, (key _).mpr u.2.2]⟩
      left_inv := fun g => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        exact rotE_cE_e0 S (g : soSub QD F).1.2 (g : soSub QD F).2
      right_inv := fun u => Subtype.ext (cE_rotE_e0 S u.2.1) }

theorem finite_range_jHom : (Set.range (jHom F E)).Finite := Set.finite_range _

/-- The proper orbit mass of the genus of $\mathcal O_E$: $\#\mathrm{im}(j)/w_E$. -/
theorem orbitMass_so_latE :
    orbitMass (soSub QD F) (GenusSet QD (latEL S)) = Nat.card (Set.range (jHom F E)) / torsionOrder E := by
  classical
  let e := Equiv.ofBijective _ (orbitsMap_bijective S (F := F) (E := E))
  have : Finite (Set.range (jHom F E)) := finite_range_jHom.to_subtype
  have : Finite (orbitRel.Quotient (soSub QD F) (GenusSet QD (latEL S))) := Finite.of_equiv _ e
  have : Fintype (orbitRel.Quotient (soSub QD F) (GenusSet QD (latEL S))) := Fintype.ofFinite _
  unfold orbitMass
  rw [finsum_eq_sum_of_fintype]
  simp_rw [card_stabilizer_so S]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, ← Nat.card_congr e,
    div_eq_mul_inv]

/-- $\#\mathrm{im}(j)\cdot\#\mathrm{Cl}^{\mathrm{str}}_E = h_E$ (the $j$, kernel = strongly ambiguous classes). -/
theorem card_range_jHom_mul_card_strAmb :
    Nat.card (Set.range (jHom F E)) * Nat.card (StrAmb F E) = classNumber E := by
  rw [classNumber, ← Nat.card_eq_fintype_card, ← card_range_mul_card_ker (jHom F E)]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c => (jHom_eq_one_iff c).symm)

/-- **The mass of the maximal order** of $E = F(\sqrt{-D})$ for $\langle1,D\rangle$:
$$\mathrm{Mass}(\mathcal O_E) = \frac{\#\mathrm{im}(j)}{2w_E} = \frac{h_E\,[\mu_E : \{u/\sigma u\}]}{2^{t+1}\,h_F\,w_E},$$
$t$ the number of ramified primes. *Proof:* $\mathrm{Mass} = \frac12\,\mathrm{mass}_{SO}$ (`orbitMass_so_eq_two_mul`); the proper classes are the image of $j$
(`orbitsMap_bijective`) and every proper stabilizer is $\mu_E$ (`card_stabilizer_so`); the counts (`card_range_jHom_mul_card_strAmb`,
`card_strAmb_mul_index`). -/
@[kb "shimura2010" "§4 (mass of the norm form of a CM order) [unverified]"]
theorem mass_latE (hpd : IsTotallyPosDef QD) {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hT : ∀ 𝔭, 𝔭 ∈ T ↔ relChar E 𝔭 = 0) :
    mass QD (latEL S) = (classNumber E * (conjQuotGroup F E).index : ℝ) /
      (2 ^ (T.card + 1) * classNumber F * torsionOrder E) := by
  have h2 := orbitMass_so_eq_two_mul hpd two_pos (latEL S) (isIntegral_latE S)
  rw [orbitMass_so_latE] at h2
  have h3 := card_range_jHom_mul_card_strAmb (F := F) (E := E)
  have h4 := card_strAmb_mul_index (F := F) (E := E) hT
  have hw : (0 : ℝ) < torsionOrder E := by exact_mod_cast torsionOrder_pos E
  have hs : (0 : ℝ) < Nat.card (StrAmb F E) := by
    have : Nat.card (StrAmb F E) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h4
      exact (mul_ne_zero (pow_ne_zero _ two_ne_zero) (classNumber_ne_zero F)) h4.symm
    exact_mod_cast Nat.pos_of_ne_zero this
  have hF : (0 : ℝ) < classNumber F := by exact_mod_cast Nat.pos_of_ne_zero (classNumber_ne_zero F)
  have h3' : (Nat.card (Set.range (jHom F E)) : ℝ) * Nat.card (StrAmb F E) = classNumber E := by exact_mod_cast h3
  have h4' : (Nat.card (StrAmb F E) : ℝ) * (conjQuotGroup F E).index = 2 ^ T.card * classNumber F := by
    exact_mod_cast h4
  have hm : mass QD (latEL S) = Nat.card (Set.range (jHom F E)) / (2 * torsionOrder E) := by
    rw [eq_div_iff (by positivity)]
    rw [div_eq_iff hw.ne'] at h2
    linarith
  rw [hm, div_eq_div_iff (by positivity) (by positivity), pow_succ]
  linear_combination (-(2 * (torsionOrder E : ℝ) * Nat.card (Set.range (jHom F E)))) * h4' +
    (2 * (torsionOrder E : ℝ) * (conjQuotGroup F E).index) * h3'

end QuadFormsKB.Tamagawa.BinaryCM
