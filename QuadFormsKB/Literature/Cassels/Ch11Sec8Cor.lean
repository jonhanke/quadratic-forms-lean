/-
# Cassels, Chapter 11, Theorem 8.4, Corollary 1: chains with $p = 2$ only

**Layer:** integer forms and Cassels' chains of Theorem 6.1 (`Ch11Sec6.lean`, substitution `casselsSubst`); the
completions $\mathbb Z_p$ = `ℤ_[p]`; equivalence over a ring `Siegel.IsometricGL`.

**Proves** Cassels' Theorem 8.4, Corollary 1 (p. 233) (`exists_chain_two_of_kneser`): under the hypotheses of
Theorem 8.4 the forms $f_1, f_2$ can be connected by a chain as in Theorem 6.1 with $p = 2$ in every step (ii).
*Deviation:* the rational equivalence of $f_1, f_2$ (which Cassels deduces from the local equivalences at $p \ne 2$
and at $\infty$, p. 233) is taken as a hypothesis; equivalence over $\mathbb R$ is then not needed.
*Proof:* in $V = (\mathbb Q^n, f_1)$ with $\Lambda = \mathbb Z^n$ and $\Gamma$ the lattice of $f_2$, Theorem 8.4
(`exists_soSub_locAct_eq_of_local_rat`, with $U_p \subseteq \theta(\Lambda_p)$ from Lemma 3.7, Corollary) gives
$\sigma \in O^+(V)$ with $\sigma\Gamma_p = \Lambda_p$ for $p \ne 2$; so $I(\Lambda, \sigma\Gamma)$ is a power of $2$
((4.2)–(4.3)), and the chain of Theorem 6.1 for $(\Lambda, \sigma\Gamma)$ uses only primes dividing it.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec6Genus
import QuadFormsKB.Literature.Cassels.Ch11Sec8Kneser
import QuadFormsKB.Literature.Cassels.Ch11Thm13

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ}

/-- Isotropy transfers along a ring homomorphism of fields over $\mathbb Q$. -/
theorem isotropicIn_of_ringHom (Q : QuadForm ℚ n) {K L : Type} [Field K] [Field L] [Algebra ℚ K]
    [Algebra ℚ L] (f : K →+* L) (hK : Q.IsotropicIn K) : Q.IsotropicIn L := by
  obtain ⟨x, hx, h⟩ := hK
  have hf : algebraMap ℚ L = f.comp (algebraMap ℚ K) := Subsingleton.elim _ _
  refine ⟨f ∘ x, ?_, ?_⟩
  · intro h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa using this
  · have : QuadForm.evalIn L Q (f ∘ x) = f (QuadForm.evalIn K Q x) := by
      simp only [QuadForm.evalIn, map_sum, hf]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [this, h, map_zero]

section PadicIso

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- Isotropy over $\mathbb Q_p$ ($p$ the prime of $q$) gives isotropy over the completion at $q$. -/
theorem isotropicIn_adicCompletion_of_padic (Q : QuadForm ℚ n) (q : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ)
    [Fact p.Prime] (h : p = (Rat.HeightOneSpectrum.primesEquiv q : ℕ)) (hi : Q.IsotropicIn ℚ_[p]) :
    Q.IsotropicIn (q.adicCompletion ℚ) := by
  subst h
  exact isotropicIn_of_ringHom Q
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv q).symm.toAlgEquiv.toRingEquiv.toRingHom hi

end PadicIso

/-- The one-prime half of `sameGenus_latOf_iff`: a $\mathfrak o_v$-isometry of the Gram forms gives a local
isometry of $V_v$ carrying $(\gamma\mathbb Z^n)_v$ to $(\delta\mathbb Z^n)_v$. -/
theorem exists_loc_of_isometricGL {F : Type*} [Field F] [NumberField F] (Q : QuadForm F n)
    (γ δ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ)) (hδ : IsIntegral Q (latOf δ))
    (v : HeightOneSpectrum (𝓞 F))
    (hfin : Siegel.IsometricGL ((gramZ Q γ hγ).map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)))
      ((gramZ Q δ hδ).map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)))) :
    ∃ g ∈ orthGroup Q (v.adicCompletion F), locAct v g (loc v (latOf γ)) = loc v (latOf δ) := by
  have hloc : ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : GL (Fin n) F),
      loc v (latOf ε) = locAct v (GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) ε) (std v) :=
    fun v ε => by rw [latOf, loc_glImage, loc_intVec]
  obtain ⟨P₀, hP₀⟩ := hfin
  set γv := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ
  set δv := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) δ
  set P := GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) P₀
  have hval : ∀ y, Q.evalIn _ (γv.val *ᵥ (P.val *ᵥ y)) = Q.evalIn _ (δv.val *ᵥ y) := by
    refine evalIn_eq_of_evalIn_o v (A := fun y => Q.evalIn _ (γv.val *ᵥ (P.val *ᵥ y)))
      (B := fun y => Q.evalIn _ (δv.val *ᵥ y)) (fun c y => ?_) (fun c y => ?_) (fun x => ?_)
    · simp only [mulVec_smul, evalIn_smul']
    · simp only [mulVec_smul, evalIn_smul']
    · have h1 := congrArg (fun t : v.adicCompletionIntegers F => (t : v.adicCompletion F)) (hP₀ x)
      rw [coe_eval_gramZ_map, coe_eval_gramZ_map] at h1
      have e : (P.val *ᵥ fun i => ((x i : v.adicCompletionIntegers F) : v.adicCompletion F)) =
          fun i => (((P₀.val *ᵥ x) i : v.adicCompletionIntegers F) : v.adicCompletion F) := by
        funext i; exact (RingHom.map_mulVec (algebraMap _ (v.adicCompletion F)) P₀.val x i).symm
      change Q.evalIn _ (γ.val.map (algebraMap F _) *ᵥ (P.val *ᵥ _)) =
        Q.evalIn _ (δ.val.map (algebraMap F _) *ᵥ _)
      rw [e]; exact h1
  refine ⟨δv * P⁻¹ * γv⁻¹, mem_orthGroup_of_evalIn Q fun z => ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← hval, mulVec_inv_mulVec,
      mulVec_inv_mulVec]
  · rw [hloc, hloc, ← locAct_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, locAct_mul,
      show P⁻¹ = GeneralLinearGroup.map (algebraMap _ (v.adicCompletion F)) P₀⁻¹ from (map_inv _ _).symm,
      locAct_map_std]

/-- If $\sigma_v$ carries $L_v$ to $M_v$, then $\sigma^{-1}M$ has the same localization $L_v$. -/
theorem loc_glImage_inv_eq {F : Type*} [Field F] [NumberField F] (Q : QuadForm F n) (σ : orthGroup Q F)
    (v : HeightOneSpectrum (𝓞 F)) (L M : Lat F n)
    (h : locAct v ((orthMap Q (v.adicCompletion F) σ : orthGroup Q _) : GL (Fin n) _) (loc v L.1) =
      loc v M.1) :
    loc v (glImage ((σ⁻¹ : orthGroup Q F) : GL (Fin n) F) M.1) = loc v L.1 := by
  rw [loc_glImage]
  have : GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) ((σ⁻¹ : orthGroup Q F) : GL (Fin n) F) =
      ((orthMap Q (v.adicCompletion F) σ : orthGroup Q _) : GL (Fin n) _)⁻¹ := by
    rw [Subgroup.coe_inv, map_inv]; rfl
  rw [this, ← h, locAct_inv_locAct]

/-- Equivalence over $\mathbb Z_p$ ($p \ne 2$) gives equivalence over $\mathfrak o_v$ for $v$ over $p$. -/
theorem local_isometricGL_o (f₁ f₂ : QuadForm ℤ n)
    (hp : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      Siegel.IsometricGL (f₁.map (Int.castRingHom ℤ_[p])) (f₂.map (Int.castRingHom ℤ_[p])))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : Rat.HeightOneSpectrum.natGenerator v ≠ 2) :
    Siegel.IsometricGL ((f₁.map toOQ).map (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ)))
      ((f₂.map toOQ).map (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ))) := by
  have : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let φ := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
  have h := hp (Rat.HeightOneSpectrum.primesEquiv v : ℕ) hv
  rw [← isometricGL_map_ringEquiv φ.symm, QuadForm.map_map, QuadForm.map_map] at h
  rw [QuadForm.map_map, QuadForm.map_map, RingHom.ext_int
    ((algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ)).comp toOQ)
    (φ.symm.toRingHom.comp (Int.castRingHom _))]
  exact h

/-- **Cassels, Theorem 8.4, Corollary 1** (Ch. 11, p. 233): *the forms $f_1, f_2$ (of Theorem 8.4) can be connected
with a sequence of forms $g_v$ as described in Theorem 6.1 such that always $p = 2$ in (ii).* Hypotheses of
Theorem 8.4: classically integral, the same determinant $d$ ($\det H = 2^nd$), $n \ge 3$, isotropic over
$\mathbb Q_2$, equivalent over $\mathbb Z_p$ for $p \ne 2$, $p^{n(n-1)/2} \nmid d$ for $p \ne 2$; plus rational
equivalence (module docstring). -/
@[kb "cassels1978" "Ch. 11, Thm. 8.4, Cor. 1, p. 233 (rational equivalence assumed)"]
theorem exists_chain_two_of_kneser (hn : 3 ≤ n) (f₁ f₂ : QuadForm ℤ n)
    (h₁ : IsClassicallyIntegral f₁) (h₂ : IsClassicallyIntegral f₂)
    (hd : f₁.hessian.det = f₂.hessian.det) (hd0 : f₁.hessian.det ≠ 0)
    (hQ : Siegel.IsometricGL (f₁.map (Int.castRingHom ℚ)) (f₂.map (Int.castRingHom ℚ)))
    (hiso : (f₁.map (Int.castRingHom ℚ)).IsotropicIn ℚ_[2])
    (hp : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      Siegel.IsometricGL (f₁.map (Int.castRingHom ℤ_[p])) (f₂.map (Int.castRingHom ℤ_[p])))
    (hdet : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ^ (n * (n - 1) / 2) ∣ f₁.hessian.det) :
    ∃ (V : ℕ) (g : Fin (V + 1) → QuadForm ℤ n), g 0 = f₁ ∧ g (Fin.last V) = f₂ ∧
      (∀ v, IsClassicallyIntegral (g v) ∧ (g v).hessian.det = f₁.hessian.det) ∧
      ∀ v : Fin V,
        (∃ U : Matrix (Fin n) (Fin n) ℤ, U.det = 1 ∧ ∀ x, (g v.succ).eval x = (g v.castSucc).eval (U *ᵥ x)) ∨
        ∀ x : Fin n → ℚ, ((g v.succ).map (Int.castRingHom ℚ)).evalIn ℚ x =
          ((g v.castSucc).map (Int.castRingHom ℚ)).evalIn ℚ (casselsSubst 2 x) := by
  classical
  have hn2 : 2 ≤ n := by omega
  obtain ⟨g, hg1, hFg⟩ := exists_pos_det_one f₁ f₂ (by omega) hd hd0 hQ
  set Q := f₁.map (Int.castRingHom ℚ) with hQdef
  have hQnd : Q.Nondegenerate := nondegenerate_map_of_det_ne_zero f₁ hd0
  have hF1 : FormOf f₁ 1 f₁ := fun x => by simp
  have hi1 := isIntegral_latOf hF1
  have hi2 := isIntegral_latOf hFg
  obtain ⟨q, hq2⟩ := exists_place_natGen Nat.prime_two
  have hne2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ q → Rat.HeightOneSpectrum.natGenerator v ≠ 2 :=
    fun v hv h => hv (natGen_injective' (h.trans hq2.symm))
  set L : Lat ℚ n := ⟨latOf 1, latOf_isLattice 1⟩ with hL
  set Δ : Lat ℚ n := ⟨latOf g, latOf_isLattice g⟩ with hΔ
  have e1 : latOf (1 : GL (Fin n) ℚ) = (stdLat : Lat ℚ n).1 := by rw [latOf, glImage_one]; rfl
  have hLs : L = stdLat := Subtype.ext e1
  -- isotropy at the place over 2
  have hqiso : Q.IsotropicIn (q.adicCompletion ℚ) := by
    convert isotropicIn_adicCompletion_of_padic Q q 2 hq2.symm hiso
    exact Subsingleton.elim _ _
  -- local isometries
  have hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ q →
      ∃ g' ∈ orthGroup Q (v.adicCompletion ℚ), locAct v g' (loc v L.1) = loc v Δ.1 := by
    intro v hv
    obtain ⟨g', hg', he⟩ := exists_loc_of_isometricGL Q 1 g hi1 hi2 v (by
      rw [gramZ_eq_map hF1 hi1, gramZ_eq_map hFg hi2]
      exact local_isometricGL_o f₁ f₂ hp v (hne2 v hv))
    exact ⟨g', by convert hg'; exact Subsingleton.elim _ _, he⟩
  -- units
  have hunits : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ q → ∀ u : (v.adicCompletion ℚ)ˣ,
      Valued.v (u : v.adicCompletion ℚ) = 1 → u ∈ localSpinorNormGroup Q hQnd v L := by
    intro v hvq
    rw [hLs]
    have hv2 : ¬ (2 : 𝓞 ℚ) ∈ v.asIdeal := fun h =>
      hne2 v hvq ((two_mem_iff_natGenerator v).mp h)
    have hL' : loc v (stdLat : Lat ℚ n).1 = std v := loc_intVec v
    have hγ : loc v (stdLat : Lat ℚ n).1 = locAct v (1 : GL (Fin n) (v.adicCompletion ℚ)) (std v) := by
      rw [locAct_one]; exact hL'
    have hint : ∀ x ∈ loc v (stdLat : Lat ℚ n).1,
        Valued.v (Q.evalIn (v.adicCompletion ℚ) x) ≤ 1 := by
      intro x hx; rw [hL'] at hx; exact valued_evalIn_le_one_int v f₁ hx
    by_contra hnot
    have hpr := Rat.HeightOneSpectrum.prime_natGenerator v
    have hd' := valued_det_le_of_not_units_mem Q v hQnd hv2 stdLat
      (by convert hint; exact Subsingleton.elim _ _) hnot 1 hγ
    rw [locGram_one_int_det, valued_intCast_le_iff] at hd'
    exact hdet _ hpr (hne2 v hvq) hd'
  obtain ⟨σ, hσ, hσv⟩ := exists_soSub_locAct_eq_of_local_rat Q hQnd hn q hqiso L Δ hloc hunits
  set τ : orthGroup Q ℚ := σ⁻¹ with hτ
  have hτdet : ((τ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1 :=
    Tamagawa.mem_soSub.mp ((Tamagawa.soSub Q ℚ).inv_mem hσ)
  set T : GL (Fin n) ℚ := (τ : GL (Fin n) ℚ) * g with hT
  have hT1 : (T : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
    rw [hT, Units.val_mul, det_mul, hτdet, hg1, one_mul]
  have hF' : FormOf f₁ T f₂ := fun x => by
    rw [hFg x, hT, Units.val_mul, ← mulVec_mulVec]
    have := evalIn_mulVec_of_mem Q τ.2 (g.val *ᵥ x)
    simp only [hQdef, map_evalIn_rat] at this
    exact this.symm
  set Γ : Lat ℚ n := ⟨latOf T, latOf_isLattice T⟩ with hΓ
  have hlocT : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ q → loc v Γ.1 = loc v L.1 := by
    intro v hv
    have e : Γ.1 = glImage (τ : GL (Fin n) ℚ) (latOf g) := by
      rw [hΓ, hT]
      change latOf _ = _
      rw [latOf, glImage_mul]; rfl
    rw [e]
    have h := hσv v hv
    convert loc_glImage_inv_eq Q σ v L Δ (by convert h <;> exact Subsingleton.elim _ _) using 2
  have hΛ1 : Tamagawa.SiegelSpace.latIndex L = 1 := by
    have := latIndex_latOf (1 : GL (Fin n) ℚ); simpa using this
  have hΓ1 : Tamagawa.SiegelSpace.latIndex Γ = 1 := by
    have := latIndex_latOf T; rw [hT1] at this; simpa using this
  have hlat : Tamagawa.SiegelSpace.latIndex L = Tamagawa.SiegelSpace.latIndex Γ := hΛ1.trans hΓ1.symm
  have hI : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Rat.HeightOneSpectrum.natGenerator w ∣ casselsI L Γ → w = q := by
    intro w hw
    by_contra hne
    exact (loc_eq_iff_not_dvd_casselsI hlat w).mp (hlocT w hne).symm hw
  have hrt := exists_chain_coreD hn2 f₁ f₂ h₁ h₂ hd T hT1 hF' Γ rfl
  obtain ⟨V, c, h0, hl, hP, hr⟩ := exists_fin_of_reflTransGen
    (ChainRelD f₁ (casselsI L Γ)) (GoodForm f₁) (fun a b h => h.2.1) hrt ⟨h₁, rfl⟩
  refine ⟨V, c, h0, hl, fun v => hP v, fun v => ?_⟩
  rcases (hr v).2.2 with hU | ⟨p, hp', hpm, hsub⟩
  · exact Or.inl hU
  · refine Or.inr ?_
    obtain ⟨w, hw⟩ := exists_place_natGen hp'
    have hwq := hI w (hw ▸ hpm)
    have hp2 : p = 2 := by rw [← hw, hwq, hq2]
    subst hp2
    exact hsub

end QuadFormsKB.Lattices
