/-
# The genus theta series $\theta_{\mathrm{Gen}}$ over a totally real field

**Setting.** $F$ totally real, $Q_0$ a form over $\mathcal{O}_F$ in $n = 2k$ variables, $Q = Q_0 \otimes F$ on $V = F^n$ (`formF Q₀`), and
$L = \mathcal{O}_F^n$ (`stdLat`). The genus and the class set are those of `Lattices` (`Lattices.genusClasses`, `Lattices.mass`): classes of
lattices $M \subseteq F^n$ in the genus of $L$ in $(V, Q)$, with weights $1/|O(M)|$ (full orthogonal group, the convention of this repository).

**Definitions.**
* `thetaLatt Q M` $= \theta_M(z) = \sum_{x\in M}e\big(\sum_v\sigma_v(Q(x))z_v\big)$ for any $\mathcal{O}_F$-lattice $M \subseteq F^n$;
* **`thetaGen Q L`** $= \theta_{\mathrm{Gen}(L)} = \mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\theta_M/|O(M)|$ (a representative of each class);
* `GenusFree Q L`: every lattice in the genus of $L$ is free, $M = \gamma\mathcal{O}_F^n$.

**Freeness.** The theta transformation law is for free lattices (forms over $\mathcal{O}_F$). Every lattice in the genus of a
free lattice is free (its Steinitz class is a genus invariant: $M_\mathfrak p = g_\mathfrak pL_\mathfrak p$ with $\det g_\mathfrak p = \pm1$), but the
structure theory of finitely generated modules over a Dedekind domain is not in Mathlib, so `GenusFree` is a **hypothesis** of the
modularity theorems here. It is *not* a cited result in disguise: it says nothing about theta series or modular forms. It is
**proved** when $\mathcal{O}_F$ is a principal ideal domain (`genusFree_of_isPrincipalIdealRing`), and for the genus of $\mathcal O_F^n$
over **every** number field, any class number (`genusFree_of_nondegenerate`, `genusFree_formF` in `SteinitzGenus.lean`, from
`Lattices.Steinitz.exists_latOf_of_sameGenus`).

**Main results** ($Q_0$ totally positive definite, $n = 2k$):
* `thetaLatt_latOf`: for $M = \gamma\mathcal{O}_F^n$, $\theta_M = \theta_{Q_\gamma}$ with the Gram form $Q_\gamma$ (`Lattices.gramZ`);
* `formSameGenus_gramZ`: the Gram form of a free lattice in the genus of $L$ is in the genus of $Q_0$ (`FormSameGenus`);
* **`thetaGen_mem_modularFormChar`**: $\theta_{\mathrm{Gen}} \in M_k(\Gamma_0(\mathfrak N), \chi_{Q_0})$ for every theta level $\mathfrak N \ne 0$ of $Q_0$, all
  classes sharing the level (`isThetaLevelF_of_formSameGenus`) and the character (`thetaCharF_eq_of_formSameGenus`);
* **`tendsto_thetaGen_slash`**: at every cusp $A\infty$, $\theta_{\mathrm{Gen}}\,|_k\,A$ has the same constant term as $\theta_{Q_0}$
  (`thetaCuspVal`), because every class has it and the weights $|O(M)|^{-1}/\mathrm{Mass}$ sum to $1$;
* `thetaLatt_sub_thetaGen_mem_cuspFormChar`: $\theta_M - \theta_{\mathrm{Gen}} \in S_k(\Gamma_0(\mathfrak N), \chi_{Q_0})$ for $M$ in the genus.

Over $\mathbb{Q}$: `Siegel.thetaGen`, `Siegel.thetaGenCusp` (`Siegel/ThetaCuspidal.lean`).

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935) [unverified]; Shimura (1973),
§2 [unverified]; O'Meara (1963), §§82, 102 (genus, class, mass) [unverified].
-/
import QuadFormsKB.HilbertModular.ThetaGenusInv
import QuadFormsKB.HilbertModular.ThetaPosDef
import QuadFormsKB.Lattices.FreeBridge

open Matrix NumberField Complex Filter Topology IsDedekindDomain
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-! ### Theta series of lattices -/

/-- **The theta series of an $\mathcal{O}_F$-lattice** $M \subseteq F^n$ for a form $Q$ over $F$:
$\theta_M(z) = \sum_{x\in M}e\big(\sum_v\sigma_v(Q(x))z_v\big)$ (`tsum`; a junk value where it diverges).
Parameters: `Q` (the form on $F^n$), `M` (the lattice). -/
@[kb "shimura1973" "§2, theta series of a lattice [unverified]"]
noncomputable def thetaLatt (Q : QuadForm F n) (M : Submodule (𝓞 F) (Fin n → F))
    (z : InfinitePlace F → UpperHalfPlane) : ℂ :=
  ∑' x : M, cexp (2 * Real.pi * Complex.I * ∑ v, (realEmb F v (Q.eval (x : Fin n → F)) : ℂ) * (z v : ℂ))

/-- $\mathcal{O}_F^n \simeq \gamma\mathcal{O}_F^n$, $x \mapsto \gamma x$. -/
noncomputable def latOfEquiv (γ : GL (Fin n) F) : (Fin n → 𝓞 F) ≃ latOf γ :=
  Equiv.ofBijective (fun x => ⟨γ.val *ᵥ intCoe x, mulVec_mem_glImage (intCoe_mem x)⟩) (by
    constructor
    · intro x y hxy
      have h1 : γ.val *ᵥ intCoe x = γ.val *ᵥ intCoe y := congrArg Subtype.val hxy
      have h2 : intCoe x = intCoe y := by
        have := congrArg (fun w => (γ⁻¹).val *ᵥ w) h1
        simpa [mulVec_mulVec, ← Units.val_mul] using this
      funext i
      exact algebraMap_O_injective (congrFun h2 i)
    · rintro ⟨y, w, hw, rfl⟩
      obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hw
      exact ⟨x, rfl⟩)

/-- **The theta series of a free lattice is the theta series of its Gram form**: $\theta_{\gamma\mathcal{O}_F^n} = \theta_{Q_\gamma}$,
$Q_\gamma(x) = Q(\gamma x)$ (`Lattices.gramZ`). -/
theorem thetaLatt_latOf (Q : QuadForm F n) (γ : GL (Fin n) F) (h : IsIntegral Q (latOf γ)) :
    thetaLatt Q (latOf γ) = thetaQ (gramZ Q γ h) := by
  funext z
  rw [thetaLatt, thetaQ, ← (latOfEquiv γ).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [algebraMap_eval_gramZ]
  rfl

/-! ### The genus theta series -/

/-- **Every lattice in the genus of $L$ is free**: $M = \gamma\mathcal{O}_F^n$ for some $\gamma \in \mathrm{GL}_n(F)$ (a hypothesis of the
modularity theorems; proved for $\mathcal{O}_F$ a PID, `genusFree_of_isPrincipalIdealRing`, and for the genus of $\mathcal O_F^n$
over every number field, `genusFree_of_nondegenerate`). -/
def GenusFree (Q : QuadForm F n) (L : Lat F n) : Prop :=
  ∀ M : Lat F n, SameGenus Q L.1 M.1 → ∃ γ : GL (Fin n) F, M.1 = latOf γ

/-- **The genus theta series** (mass-weighted, Siegel's average):
$$\theta_{\mathrm{Gen}(L)}(z) = \mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{\theta_M(z)}{|O(M)|},\qquad
  \mathrm{Mass}(L) = \sum_{\mathrm{cls}(M)}\frac1{|O(M)|},$$
summed over the classes of `Lattices.genusClasses` (`genusClasses`, a `finsum`), $\theta_M$ for the representative `c.out`, $O(M)$ the full orthogonal
group (`LatClass.autCard`). Parameters: `Q` (the form on $F^n$), `L` (the lattice). -/
@[kb "siegel1935" "the genus theta series (Siegel's average), over F [unverified]"]
noncomputable def thetaGen (Q : QuadForm F n) (L : Lat F n) (z : InfinitePlace F → UpperHalfPlane) : ℂ :=
  ((mass Q L : ℝ) : ℂ)⁻¹ * ∑ᶠ c ∈ genusClasses Q L, ((LatClass.autCard Q c : ℂ))⁻¹ * thetaLatt Q c.out.1 z

lemma sameGenus_out {Q : QuadForm F n} {L : Lat F n} {c : LatClass Q} (hc : c ∈ genusClasses Q L) :
    SameGenus Q L.1 c.out.1 := by
  obtain ⟨M, rfl, hM⟩ := hc
  have hiso : IsIsometric Q M.1 (Quotient.out (Quotient.mk (latSetoid Q) M)).1 :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (latSetoid Q) M)).symm
  exact hM.trans Q (hiso.sameGenus Q)

/-! ### The standard lattice of a form over $\mathcal{O}_F$ -/

/-- The form $Q_0 \otimes F$ on $F^n$. -/
noncomputable abbrev formF (Q₀ : QuadForm (𝓞 F) n) : QuadForm F n := Q₀.map (algebraMap (𝓞 F) F)

/-- The standard lattice $\mathcal{O}_F^n$. -/
abbrev stdLat : Lat F n := ⟨intVec, intVec_isLattice⟩

lemma latOf_one : latOf (1 : GL (Fin n) F) = intVec := glImage_one _

lemma isIntegral_stdLat (Q₀ : QuadForm (𝓞 F) n) : IsIntegral (formF Q₀) (intVec : Submodule (𝓞 F) (Fin n → F)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_intVec_iff_exists.mp hx
  exact ⟨Q₀.eval y, by rw [← eval_map_comp]⟩

lemma isIntegral_latOf_one (Q₀ : QuadForm (𝓞 F) n) : IsIntegral (formF Q₀) (latOf (1 : GL (Fin n) F)) := by
  rw [latOf_one]; exact isIntegral_stdLat Q₀

lemma gramZ_one (Q₀ : QuadForm (𝓞 F) n) : gramZ (formF Q₀) 1 (isIntegral_latOf_one Q₀) = Q₀ := by
  refine QuadForm.ext_eval fun x => algebraMap_O_injective ?_
  rw [algebraMap_eval_gramZ, Units.val_one, one_mulVec, ← eval_map_comp]

/-- **The Gram form of a free lattice in the genus of $\mathcal{O}_F^n$ is in the genus of $Q_0$** (`sameGenus_latOf_iff`). -/
theorem formSameGenus_gramZ (Q₀ : QuadForm (𝓞 F) n) {γ : GL (Fin n) F}
    (hg : SameGenus (formF Q₀) intVec (latOf γ)) (h : IsIntegral (formF Q₀) (latOf γ)) :
    FormSameGenus Q₀ (gramZ (formF Q₀) γ h) := by
  have := (sameGenus_latOf_iff (formF Q₀) 1 γ (isIntegral_latOf_one Q₀) h).mp (by rwa [latOf_one])
  rwa [gramZ_one] at this

/-- The Gram form of a lattice in a totally positive definite space is totally positive definite. -/
theorem isTotPosGram_gramZ {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (γ : GL (Fin n) F)
    (h : IsIntegral (formF Q₀) (latOf γ)) : IsTotPosGram (gramF (gramZ (formF Q₀) γ h)) := by
  refine isTotPosGram_of_isTotallyPosDef fun y hy => ?_
  rw [gramZ_map, eval_gramFormF_col]
  refine hQ _ fun h0 => hy ?_
  have := congrArg (fun w => (γ⁻¹).val *ᵥ w) h0
  simpa [mulVec_mulVec, ← Units.val_mul] using this

/-! ### Modularity and constant terms of $\theta_{\mathrm{Gen}}$ -/

section Main

variable {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k)
  {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥)

include hQ in
lemma isTotPosGram_Q₀ : IsTotPosGram (gramF Q₀) := isTotPosGram_of_isTotallyPosDef hQ

include hQ hn hlev h𝔑 in
/-- **Every free lattice $M$ in the genus of $\mathcal{O}_F^n$**: $\theta_M \in M_k(\Gamma_0(\mathfrak N), \chi_{Q_0})$, and at every cusp $\theta_M$ has
the constant term of $\theta_{Q_0}$. -/
theorem thetaLatt_genus {M : Submodule (𝓞 F) (Fin n → F)} (hM : SameGenus (formF Q₀) intVec M)
    (hfree : ∃ γ : GL (Fin n) F, M = latOf γ) :
    thetaLatt (formF Q₀) M ∈ modularFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k ∧
      ∀ A : SL(2, F), Tendsto (thetaLatt (formF Q₀) M ∣[(k : ℤ)] slHom (realEmb F) A) atImInftyPi
        (𝓝 (thetaCuspVal Q₀ k A)) := by
  obtain ⟨γ, rfl⟩ := hfree
  have hi : IsIntegral (formF Q₀) (latOf γ) := SameGenus.isIntegral _ (isIntegral_stdLat Q₀) hM
  rw [thetaLatt_latOf _ γ hi]
  have hQ₀ := isTotPosGram_Q₀ hQ
  have hfs := formSameGenus_gramZ Q₀ hM hi
  have hQc := isTotPosGram_gramZ hQ γ hi
  have hlevc := isThetaLevelF_of_formSameGenus hQ₀ hQc hfs hlev
  refine ⟨?_, fun A => ?_⟩
  · have := thetaQ_mem_modularFormChar' hQc hn hlevc h𝔑
    rwa [thetaCharF_eq_of_formSameGenus hQ₀ hQc hfs hn hlev hlevc h𝔑] at this
  · have := tendsto_thetaQ_slash_thetaCuspVal hQc hn A
    rwa [thetaCuspVal_eq_of_formSameGenus hQ₀ hQc hfs] at this

lemma thetaGen_eq_sum {Q : QuadForm F n} {L : Lat F n} (hfin : (genusClasses Q L).Finite) :
    thetaGen Q L = ((mass Q L : ℝ) : ℂ)⁻¹ • ∑ c ∈ hfin.toFinset,
      ((LatClass.autCard Q c : ℂ))⁻¹ • thetaLatt Q c.out.1 := by
  funext z
  rw [thetaGen, finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp [Finset.sum_apply, smul_eq_mul]

include hQ hn hlev h𝔑 in
/-- **$\theta_{\mathrm{Gen}} \in M_k(\Gamma_0(\mathfrak N), \chi_{Q_0})$** for $Q_0$ totally positive definite of rank $n = 2k$, $\mathfrak N \ne 0$ a theta
level of $Q_0$ (`IsThetaLevelF`), and the genus of $\mathcal{O}_F^n$ free (`GenusFree`). All classes share the level
(`isThetaLevelF_of_formSameGenus`) and the character (`thetaCharF_eq_of_formSameGenus`). -/
@[kb "siegel1935" "θ_Gen is a modular form of the level and character of Q, over F [unverified]"]
theorem thetaGen_mem_modularFormChar (hfree : GenusFree (formF Q₀) stdLat) :
    thetaGen (formF Q₀) stdLat ∈ modularFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k := by
  have hfin := genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)
  rw [thetaGen_eq_sum hfin]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_)
  have hc' := sameGenus_out ((Set.Finite.mem_toFinset _).mp hc)
  exact (thetaLatt_genus hQ hn hlev h𝔑 hc' (hfree _ hc')).1

include hQ hn hlev h𝔑 in
/-- **The constant terms of $\theta_{\mathrm{Gen}}$ at every cusp are those of $\theta_{Q_0}$**: for every $A \in \mathrm{SL}_2(F)$,
$\theta_{\mathrm{Gen}}\,|_k\,A \to$ `thetaCuspVal Q₀ k A` (the Gauss-sum formula, `tendsto_thetaQ_slash`). *Proof:* each class has
this constant term (`thetaLatt_genus`: the local isometries at each prime make the Gauss sums equal), and
$\sum_{\mathrm{cls}(M)}|O(M)|^{-1} = \mathrm{Mass}$. -/
@[kb "siegel1935" "constant terms of θ_Gen at the cusps, over F [unverified]"]
theorem tendsto_thetaGen_slash (hfree : GenusFree (formF Q₀) stdLat) (A : SL(2, F)) :
    Tendsto (thetaGen (formF Q₀) stdLat ∣[(k : ℤ)] slHom (realEmb F) A) atImInftyPi
      (𝓝 (thetaCuspVal Q₀ k A)) := by
  have hfin := genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)
  have hlim : ∀ c ∈ hfin.toFinset, Tendsto (fun z => ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ *
      (thetaLatt (formF Q₀) c.out.1 ∣[(k : ℤ)] slHom (realEmb F) A) z) atImInftyPi
      (𝓝 (((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * thetaCuspVal Q₀ k A)) := by
    intro c hc
    have hc' := sameGenus_out ((Set.Finite.mem_toFinset _).mp hc)
    exact ((thetaLatt_genus hQ hn hlev h𝔑 hc' (hfree _ hc')).2 A).const_mul _
  have hsum := tendsto_finsetSum hfin.toFinset hlim
  have hm := mass_pos hQ stdLat (isIntegral_stdLat Q₀)
  have hmass : ((mass (formF Q₀) stdLat : ℝ) : ℂ) =
      ∑ c ∈ hfin.toFinset, ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ := by
    rw [mass_eq_sum hQ stdLat (isIntegral_stdLat Q₀)]; push_cast; rfl
  have key : ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
      ∑ c ∈ hfin.toFinset, ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * thetaCuspVal Q₀ k A =
      thetaCuspVal Q₀ k A := by
    rw [← Finset.sum_mul, ← hmass, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_mul]
  have h2 := hsum.const_mul ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹
  rw [key] at h2
  refine h2.congr fun z => ?_
  rw [thetaGen_eq_sum hfin, smul_slash, sum_slash']
  simp only [smul_slash, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

include hQ hn hlev h𝔑 in
/-- **$\theta_M - \theta_{\mathrm{Gen}}$ is a cusp form** for every lattice $M$ in the genus of $\mathcal{O}_F^n$ (free genus):
$\theta_M - \theta_{\mathrm{Gen}} \in S_k(\Gamma_0(\mathfrak N), \chi_{Q_0})$. Over $\mathbb{Q}$: `Siegel.thetaGenCusp`. -/
@[kb "siegel1935" "θ_M − θ_Gen is a cusp form, over F [unverified]"]
theorem thetaLatt_sub_thetaGen_mem_cuspFormChar (hfree : GenusFree (formF Q₀) stdLat) (M : Lat F n)
    (hM : SameGenus (formF Q₀) intVec M.1) :
    thetaLatt (formF Q₀) M.1 - thetaGen (formF Q₀) stdLat ∈
      cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k := by
  obtain ⟨h1, h2⟩ := thetaLatt_genus hQ hn hlev h𝔑 hM (hfree M hM)
  have hG := thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree
  have hsub := (modularFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k).sub_mem h1 hG
  exact ⟨⟨hsub.1.1, hsub.1.2.1, fun A =>
    isZeroAtImInftyPi_sub (h2 A) (tendsto_thetaGen_slash hQ hn hlev h𝔑 hfree A)⟩, hsub⟩

end Main

/-! ### Freeness when $\mathcal{O}_F$ is a principal ideal domain -/

/-- **Over a PID every lattice in $F^n$ is free**: $M = \gamma\mathcal{O}_F^n$ for some $\gamma \in \mathrm{GL}_n(F)$ (structure theorem over a
PID, Mathlib's `Module.free_of_finite_type_torsion_free'`; the columns of $\gamma$ are a basis of $M$). -/
theorem exists_latOf_of_isPrincipalIdealRing [IsPrincipalIdealRing (𝓞 F)] (M : Lat F n) :
    ∃ γ : GL (Fin n) F, M.1 = latOf γ := by
  classical
  have : Module.Finite (𝓞 F) M.1 := Module.Finite.iff_fg.mpr M.2.fg
  have : Module.Free (𝓞 F) M.1 := Module.free_of_finite_type_torsion_free'
  set b := Module.Free.chooseBasis (𝓞 F) M.1
  set ι := Module.Free.ChooseBasisIndex (𝓞 F) M.1
  set v : ι → (Fin n → F) := fun i => (b i : Fin n → F) with hv
  have hli : LinearIndependent F v := by
    have h1 := b.linearIndependent.map' M.1.subtype (Submodule.ker_subtype _)
    exact (LinearIndependent.iff_fractionRing (𝓞 F) F).mp h1
  have hspanO : Submodule.span (𝓞 F) (Set.range v) = M.1 := by
    have := congrArg (Submodule.map M.1.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hspan : ⊤ ≤ Submodule.span F (Set.range v) := by
    rw [← M.2.span_eq_top]
    refine Submodule.span_le.mpr fun x hx => ?_
    have hx' : x ∈ Submodule.span (𝓞 F) (Set.range v) := by rw [hspanO]; exact hx
    exact Submodule.span_le_restrictScalars (𝓞 F) F _ hx'
  set bF := Module.Basis.mk hli hspan
  have hcard : Fintype.card ι = n := by
    rw [← Module.finrank_eq_card_basis bF]; simp
  set e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  set γM : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => v (e.symm j) i
  have hcol : ∀ j, γM.col j = v (e.symm j) := fun j => by ext i; rfl
  have hu : IsUnit γM := by
    refine Matrix.linearIndependent_col_iff_isUnit.mp ?_
    have : γM.col = v ∘ e.symm := funext hcol
    rw [this]
    exact hli.comp _ e.symm.injective
  refine ⟨hu.unit, ?_⟩
  have hmul : ∀ y : Fin n → F, hu.unit.val *ᵥ y = ∑ j, y j • v (e.symm j) := by
    intro y
    rw [← sum_smul_col]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [IsUnit.unit_spec, mulVec_single_one]
    exact hcol j
  ext x
  rw [latOf, mem_glImage]
  constructor
  · intro hx
    rw [← hspanO] at hx
    obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hx
    refine ⟨fun j => algebraMap (𝓞 F) F (c (e.symm j)), intCoe_mem _, ?_⟩
    rw [hmul, Finsupp.sum_fintype c (fun i a => a • v i) (fun i => zero_smul _ _)]
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact algebraMap_smul F (c (e.symm j)) (v (e.symm j))
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := mem_intVec_iff_exists.mp hy
    rw [hmul]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [show (intCoe a j) • v (e.symm j) = a j • v (e.symm j) from
      algebraMap_smul F (a j) (v (e.symm j))]
    exact Submodule.smul_mem _ _ (b (e.symm j)).2

/-- **For $\mathcal{O}_F$ a PID the genus is free** (`GenusFree`), so the theorems above hold unconditionally when $h_F = 1$. -/
theorem genusFree_of_isPrincipalIdealRing [IsPrincipalIdealRing (𝓞 F)] (Q : QuadForm F n) (L : Lat F n) :
    GenusFree Q L := fun M _ => exists_latOf_of_isPrincipalIdealRing M

end QuadFormsKB.HilbertModular
