/-
# Weil's local orbital identity: from the primes to the input

**Layer:** the finite adelic orthogonal group $O(Q')(\mathbb A_f)$ acting on $Y = \{M \in \mathrm{gen}(\mathcal O_F^{n+1}) : e_0 \in M\}$
(`CompSet`), its local components (`LocalOrbital.lean`), and the product formula of $F$.

The input `LocalOrbitalIdentity Q₀' m` reads
$$\Big(\sum_{t \in O(Q')(\mathbb A_f)\backslash Y} w(t)\Big)\prod_\mathfrak p\alpha_\mathfrak p(L, L)
  = |N_{F/\mathbb Q}(2m)|^n\prod_\mathfrak p\alpha_\mathfrak p(L', L')\prod_\mathfrak p\beta_\mathfrak p(L, m).$$
This file proves it from the local identities at the primes $\mathfrak p \mid 2m$ (Weil 1982, §§3.4–3.5 [unverified locator];
Kitaoka 1993, §6.8 [unverified]).

**Proves**
* `relIndex_restrictedPi`: indices of "product" subgroups of a restricted product are products of local indices.
* `compWeight_smul`: the global weight $w(M) = \mu(K_0')/\mu(K_M)$ is constant on $O(Q')(\mathbb A_f)$-orbits
  (from $\mathrm{dcMass}(\Gamma, K_M) = \mathrm{Mass}(L')\,w(M)$ and $\mathrm{dcMass}(\Gamma, hKh^{-1}) = \mathrm{dcMass}(\Gamma, K)$).
* `mem_orbit_compSet_iff`, `typeEquiv`: global types are the families of local types at the primes $\mathfrak p \mid 2m$
  (one local type elsewhere, `exists_smul_locStdPt`); `glueComp` glues a lattice with prescribed local types.
* `compWeight_glueComp`, **`typeSum_eq_prod`**: $\sum_t w(t) = \prod_{\mathfrak p\mid2m}W_\mathfrak p$, the factorization of the type
  sum over the primes.
* `prod_absTwoM`: $\prod_{\mathfrak p\mid 2m}|2m|_\mathfrak p = |N(2m)|^{-1}$ (Mathlib's product formula).
* **`localOrbitalIdentity_of_local`**, `localOrbitalIdentity_of_local'`: the local identities at $\mathfrak p \mid 2m$ (and
  convergence of the Euler products) give `LocalOrbitalIdentity`.
* `localOrbitalIdentity_of_orbitCount`: the same with the orbit-count input `LocalTypeOrbitCount` at $\mathfrak p \mid 2m$.
* `localOrbitalIdentity_of_massFormula`, `massFormula_succ_of_local`, `tamagawaNumberTwo_succ_of_local` ($n \ge 3$): the induction step with `LocalOrbitalIdentity` replaced by the local identity at the primes dividing $2m$.
* **`siegelFormulaAt_of_massFormula`**, `siegelFormulaAt_of_tamagawa`: the mass formula (equivalently $\tau(SO) = 2$) in
  ranks $n+1$ and $n$ gives Siegel's formula for $m$ (the direction used for the induction step).

**Scope.** Any totally real $F$ (no class number hypothesis: everything is adelic and lattice-theoretic, with
non-free lattices allowed); $L = \mathcal O_F e_0 \perp \mathcal O_F^n$; $Q$ totally positive definite. The remaining input is
`LocalOrbitalIdentityAt v Q₀' m` at the finitely many $\mathfrak p \mid 2m$.
-/
import QuadFormsKB.Tamagawa.LocalOrbital

open NumberField IsDedekindDomain Matrix MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

/-! ### Indices in a restricted product -/

section RestrictedIndex

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {K : ∀ i, Subgroup (G i)}

/-- The index of a product of subgroups is the product of the indices (dependent version of Mathlib's `index_pi`). -/
theorem index_pi_dep [Fintype ι] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

/-- **Indices of "product" subgroups of a restricted product.** If $A = \{h : h_i \in A_i\ \forall i\}$ and
$B = \{h : h_i \in B_i\ \forall i\}$ with $A_i = B_i = K_i$ outside a finite set $S$, then
$[A : A \cap B] = \prod_{i\in S}[A_i : A_i\cap B_i]$. -/
theorem relIndex_restrictedPi (S : Finset ι) (A' B' : ∀ i, Subgroup (G i)) (hA : ∀ i ∉ S, A' i = K i)
    (hB : ∀ i ∉ S, B' i = K i) (A B : Subgroup (Πʳ i, [G i, K i]))
    (hAm : ∀ h, h ∈ A ↔ ∀ i, h i ∈ A' i) (hBm : ∀ h, h ∈ B ↔ ∀ i, h i ∈ B' i) :
    B.relIndex A = ∏ i ∈ S, (B' i).relIndex (A' i) := by
  classical
  let f : A →* ((i : S) → A' i) :=
    { toFun := fun a i => ⟨(a : Πʳ i, [G i, K i]) i, (hAm a).mp a.2 i⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro x
    let y : Πʳ i, [G i, K i] := ⟨fun i => if hi : i ∈ S then (x ⟨i, hi⟩ : G i) else 1, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi
      simp only [show i ∉ S from hi, ↓reduceDIte]; exact (K i).one_mem⟩
    have hy : y ∈ A := by
      rw [hAm]
      intro i
      show (if hi : i ∈ S then (x ⟨i, hi⟩ : G i) else 1) ∈ A' i
      split_ifs with hi
      · exact (x ⟨i, hi⟩).2
      · exact (A' i).one_mem
    refine ⟨⟨y, hy⟩, funext fun i => Subtype.ext ?_⟩
    show (if hi : (i : ι) ∈ S then (x ⟨i, hi⟩ : G i) else 1) = (x i : G i)
    simp only [i.2, ↓reduceDIte]
  have hcomap : B.subgroupOf A = (Subgroup.pi Set.univ fun i : S => (B' i).subgroupOf (A' i)).comap f := by
    ext a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hBm]
    constructor
    · intro h i _
      rw [Subgroup.mem_subgroupOf]; exact h i
    · intro h i
      by_cases hi : i ∈ S
      · have := h ⟨i, hi⟩ (Set.mem_univ _)
        rwa [Subgroup.mem_subgroupOf] at this
      · rw [hB i hi, ← hA i hi]; exact (hAm a).mp a.2 i
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hf, index_pi_dep]
  rw [← Finset.prod_coe_sort S]
  rfl

end RestrictedIndex


/-! ### Masses are invariant under conjugating the subgroup -/

section Conj

/-- **Masses along an equivariant bijection** are equal. -/
theorem orbitMass_congr_equiv {H X₁ X₂ : Type*} [Group H] [MulAction H X₁] [MulAction H X₂] (e : X₁ ≃ X₂)
    (he : ∀ (h : H) x, e (h • x) = h • e x) : orbitMass H X₁ = orbitMass H X₂ := by
  refine orbitMass_eq_of_map e (fun a b => ?_) (fun y => ⟨e.symm y, by rw [e.apply_symm_apply]; exact mem_orbit_self y⟩)
    (fun x => ?_)
  · constructor
    · rintro ⟨h, rfl⟩; exact ⟨h, (he h b).symm⟩
    · rintro ⟨h, hh⟩
      exact ⟨h, e.injective (by rw [he]; exact hh)⟩
  · have : stabilizer H (e x) = stabilizer H x := by
      ext h
      rw [mem_stabilizer_iff, mem_stabilizer_iff, ← he]
      exact e.injective.eq_iff
    rw [this]

variable {G : Type*} [Group G]

/-- **$\mathrm{dcMass}(\Gamma, gKg^{-1}) = \mathrm{dcMass}(\Gamma, K)$**: $xK \mapsto xg^{-1}\cdot gKg^{-1}$ is a $\Gamma$-equivariant bijection. -/
theorem dcMass_map_conj (Γ K : Subgroup G) (g : G) :
    dcMass Γ (K.map (MulAut.conj g).toMonoidHom) = dcMass Γ K := by
  set K' := K.map (MulAut.conj g).toMonoidHom
  have hK' : ∀ x, x ∈ K' ↔ g⁻¹ * x * g ∈ K := by
    intro x
    rw [Subgroup.mem_map_equiv (f := MulAut.conj g), MulAut.conj_symm_apply]
  let e : G ⧸ K ≃ G ⧸ K' :=
    { toFun := Quotient.map' (· * g⁻¹) (fun a b h => by
        rw [QuotientGroup.leftRel_apply] at h ⊢
        rw [hK']; simpa [mul_assoc] using h)
      invFun := Quotient.map' (· * g) (fun a b h => by
        rw [QuotientGroup.leftRel_apply] at h ⊢
        rw [hK'] at h; simpa [mul_assoc] using h)
      left_inv := fun x => by
        induction x using Quotient.inductionOn' with | h a => ?_
        show (Quotient.mk'' (a * g⁻¹ * g) : G ⧸ K) = Quotient.mk'' a
        rw [inv_mul_cancel_right]
      right_inv := fun x => by
        induction x using Quotient.inductionOn' with | h a => ?_
        show (Quotient.mk'' (a * g * g⁻¹) : G ⧸ K') = Quotient.mk'' a
        rw [mul_inv_cancel_right] }
  refine (orbitMass_congr_equiv e fun γ x => ?_).symm
  induction x using Quotient.inductionOn' with | h a => ?_
  show (Quotient.mk'' ((γ : G) * a * g⁻¹) : G ⧸ K') = Quotient.mk'' ((γ : G) * (a * g⁻¹))
  rw [mul_assoc]

end Conj


/-! ### The global weights do not depend on the representative -/

section Weights

open Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (m : F) (Q' : QuadForm F n) (L : Lat F (n + 1))

/-- **The weight of a lattice** $M \in Y$: $w(M) = [K_0' : K_M\cap K_0']/[K_M : K_M\cap K_0']$; `typeWeight t` is
`compWeight t.out`. -/
def compWeight (y : CompSet m Q' L) : ℝ :=
  ((stabilizer (OAf Q') y).relIndex (locStab Q' (stdLat F n)) : ℝ) /
    ((locStab Q' (stdLat F n)).relIndex (stabilizer (OAf Q') y) : ℝ)

theorem typeWeight_eq_compWeight (t : orbitRel.Quotient (OAf Q') (CompSet m Q' L)) :
    typeWeight m Q' L t = compWeight m Q' L t.out := rfl

theorem dcMass_compSet_eq (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n).1)
    (y : CompSet m Q' L) :
    dcMass (ratPoints Q') (stabilizer (OAf Q') y) = mass Q' (stdLat F n) * compWeight m Q' L y := by
  have hK := commensurable_stabilizer_compSet m Q' L y
  have := finite_orbits hpd' (stdLat F n) hLi'
  have h := dcMass_mul_idxVol (ratPoints Q') (locStab Q' (stdLat F n)) (stabilizer (OAf Q') y) 1 hK
    (finite_stabilizer hpd' (stdLat F n) hLi')
  rw [one_mul, ← mass_eq_dcMass] at h
  have h1 : ((stabilizer (OAf Q') y).relIndex (locStab Q' (stdLat F n)) : ℝ) ≠ 0 := by
    exact_mod_cast hK.1.relIndex_ne_zero
  have h2 : ((locStab Q' (stdLat F n)).relIndex (stabilizer (OAf Q') y) : ℝ) ≠ 0 := by
    exact_mod_cast hK.2.relIndex_ne_zero
  unfold idxVol at h
  unfold compWeight
  rw [← h]
  field_simp

/-- **The weight is constant on $O(Q')(\mathbb A_f)$-orbits** (this is the unimodularity of $O(Q')(\mathbb A_f)$ on the
relevant subgroups, obtained here from the finiteness of the mass): $\mathrm{Mass}(L')\,w(M) = \mathrm{dcMass}(O(Q')(F), K_M)$
and $K_{hM} = hK_Mh^{-1}$ (`dcMass_map_conj`). -/
theorem compWeight_smul (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n).1) (h : OAf Q')
    (y : CompSet m Q' L) : compWeight m Q' L (h • y) = compWeight m Q' L y := by
  have h1 := dcMass_compSet_eq m Q' L hpd' hLi' (h • y)
  rw [stabilizer_smul_eq_stabilizer_map_conj, dcMass_map_conj, dcMass_compSet_eq m Q' L hpd' hLi' y] at h1
  exact (mul_left_cancel₀ (mass_pos hpd' (stdLat F n) hLi').ne' h1).symm

theorem compWeight_of_mem_orbit (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n).1)
    {y y' : CompSet m Q' L} (h : y' ∈ orbit (OAf Q') y) : compWeight m Q' L y' = compWeight m Q' L y := by
  obtain ⟨h, rfl⟩ := h
  exact compWeight_smul m Q' L hpd' hLi' h y

end Weights

/-! ### Local components of the global type set -/

section Components

open Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (m : F) (Q' : QuadForm F n)

local notation "QS" => splitForm m Q'

theorem loc_stdLat {N : ℕ} (v : HeightOneSpectrum (𝓞 F)) : loc v (stdLat F N).1 = std v := loc_intVec v

/-- **The local component** $M_\mathfrak p \in Y_\mathfrak p$ of $M \in Y$ ($L = \mathcal O_F^{n+1}$). -/
def locOf (v : HeightOneSpectrum (𝓞 F)) (M : CompSet m Q' (stdLat F (n + 1))) : LocCompSet v m Q' :=
  ⟨loc v M.1.1, by
      obtain ⟨g, hg, hgM⟩ := M.2.1 v
      rw [loc_stdLat] at hgM
      exact ⟨⟨g, hg⟩, hgM⟩,
    by rw [← locVec_e₀ v]; exact locVec_mem_loc v M.2.2⟩

theorem locOf_val (v : HeightOneSpectrum (𝓞 F)) (M : CompSet m Q' (stdLat F (n + 1))) :
    (locOf m Q' v M).1 = loc v M.1.1 := rfl

theorem locOf_smul (v : HeightOneSpectrum (𝓞 F)) (h : OAf Q') (M : CompSet m Q' (stdLat F (n + 1))) :
    locOf m Q' v (h • M) = h v • locOf m Q' v M :=
  Subtype.ext (loc_latSMul QS (orthEmbAf m Q' h) M.1 v)

/-- **Global orbits are determined prime by prime:** $M' \in O(Q')(\mathbb A_f)\,M$ iff $M'_\mathfrak p \in O(Q')(F_\mathfrak p)\,M_\mathfrak p$
for every $\mathfrak p$ (take $h_\mathfrak p = 1$ where $M_\mathfrak p = M'_\mathfrak p$, which is almost everywhere). -/
theorem mem_orbit_compSet_iff (M M' : CompSet m Q' (stdLat F (n + 1))) :
    M' ∈ orbit (OAf Q') M ↔ ∀ v, locOf m Q' v M' ∈ orbit (orthGroup Q' (v.adicCompletion F)) (locOf m Q' v M) := by
  classical
  constructor
  · rintro ⟨h, rfl⟩ v
    exact ⟨h v, (locOf_smul m Q' v h M).symm⟩
  · intro hloc
    choose hv hhv using hloc
    let hp : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q' (v.adicCompletion F) := fun v =>
      if loc v M.1.1 = loc v M'.1.1 then 1 else hv v
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hp v ∈ stdStab Q' v := by
      filter_upwards [loc_eventually_std M.1.2, loc_eventually_std M'.1.2] with v h1 h2
      have : loc v M.1.1 = loc v M'.1.1 := h1.trans h2.symm
      simp only [hp, this, ↓reduceIte]
      exact (stdStab Q' v).one_mem
    let hA : OAf Q' := ⟨hp, hev⟩
    refine ⟨hA, Subtype.ext (Subtype.ext (loc_injective (hA • M).1.2 M'.1.2 fun v => ?_))⟩
    have e := locOf_smul m Q' v hA M
    have e2 : loc v (hA • M).1.1 = (locOf m Q' v (hA • M)).1 := rfl
    rw [e2, e]
    show (hp v • locOf m Q' v M).1 = _
    simp only [hp]
    split_ifs with heq
    · rw [one_smul]; exact heq
    · have := congrArg Subtype.val (hhv v)
      exact this

end Components


/-! ### Factorization of the type sum over the primes dividing $2m$ -/

section Factor

open Lattices LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (m₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) n)

local notation "mF" => algebraMap (𝓞 F) F m₀
local notation "QF'" => Q₀'.map (algebraMap (𝓞 F) F)
local notation "Lstd" => stdLat F (n + 1)

/-- **The primes dividing $2m$** (a finite set, $m \ne 0$): the only primes with possibly several local types. -/
def badSet (hm : m₀ ≠ 0) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.mp (eventually_not_mem (mul_ne_zero (two_ne_zero (α := 𝓞 F)) hm))).toFinset

theorem mem_badSet (hm : m₀ ≠ 0) {v : HeightOneSpectrum (𝓞 F)} : v ∈ badSet m₀ hm ↔ 2 * m₀ ∈ v.asIdeal := by
  simp [badSet]

variable (hm : m₀ ≠ 0)

local notation "S" => badSet m₀ hm

/-- **Global types to local types at the primes dividing $2m$:** $t \mapsto (t_\mathfrak p)_{\mathfrak p \mid 2m}$. -/
def typeMap : orbitRel.Quotient (OAf QF') (CompSet mF QF' Lstd) → ((v : S) → LocTypes v mF QF') :=
  Quotient.lift (fun M v => Quotient.mk'' (locOf mF QF' v M)) (fun a b hab => funext fun v => by
    exact Quotient.sound' ((mem_orbit_compSet_iff mF QF' b a).mp hab v))

theorem typeMap_mk (M : CompSet mF QF' Lstd) (v : S) :
    typeMap m₀ Q₀' hm (Quotient.mk'' M) v = Quotient.mk'' (locOf mF QF' v M) := rfl

theorem typeMap_injective : Function.Injective (typeMap m₀ Q₀' hm) := by
  intro t t' h
  induction t using Quotient.inductionOn' with | h M => ?_
  induction t' using Quotient.inductionOn' with | h M' => ?_
  apply Quotient.sound'
  show M ∈ orbit (OAf QF') M'
  rw [mem_orbit_compSet_iff]
  intro v
  by_cases hv : v ∈ S
  · have := congrFun h ⟨v, hv⟩
    rw [typeMap_mk, typeMap_mk] at this
    exact Quotient.exact' this
  · have h2m : 2 * m₀ ∉ v.asIdeal := fun h' => hv ((mem_badSet m₀ hm).mpr h')
    obtain ⟨g, hg⟩ := exists_smul_locStdPt v m₀ Q₀' h2m (locOf mF QF' v M)
    obtain ⟨g', hg'⟩ := exists_smul_locStdPt v m₀ Q₀' h2m (locOf mF QF' v M')
    exact ⟨g * g'⁻¹, by show (g * g'⁻¹) • _ = _; rw [mul_smul, ← hg', inv_smul_smul, hg]⟩

open Classical in
/-- The local family glued from representatives of local types at the primes dividing $2m$ (and
$\mathfrak o_\mathfrak p^{n+1}$ elsewhere). -/
def glueFam (f : (v : S) → LocTypes v mF QF') : LocFamily F (n + 1) where
  M v := if hv : v ∈ S then (locRep v mF QF' (f ⟨v, hv⟩)).1 else std v
  isLattice v := by
    split_ifs with hv
    · obtain ⟨g, hg⟩ := (locRep v mF QF' (f ⟨v, hv⟩)).2.1
      rw [← hg]
      exact locAct_isLattice _ (isLattice_of_bounds v le_rfl le_rfl)
    · exact isLattice_of_bounds v le_rfl le_rfl
  eventually_std := by
    filter_upwards [(S).finite_toSet.compl_mem_cofinite] with v hv
    simp only [show v ∉ S from hv, ↓reduceDIte]

open Classical in
/-- **The glued lattice** with prescribed local types. -/
def glueComp (f : (v : S) → LocTypes v mF QF') : CompSet mF QF' Lstd :=
  ⟨⟨(glueFam m₀ Q₀' hm f).glue, (glueFam m₀ Q₀' hm f).glue_isLattice⟩, by
      intro v
      rw [loc_stdLat, LocFamily.loc_glue]
      show ∃ g ∈ _, _ = if hv : v ∈ S then _ else _
      split_ifs with hv
      · obtain ⟨g, hg⟩ := (locRep v mF QF' (f ⟨v, hv⟩)).2.1
        exact ⟨g, g.2, hg⟩
      · exact ⟨1, (orthGroup _ _).one_mem, locAct_one _⟩,
    by
      rw [mem_iff_forall_loc (glueFam m₀ Q₀' hm f).glue_isLattice]
      intro v
      rw [LocFamily.loc_glue, locVec_e₀]
      show _ ∈ if hv : v ∈ S then _ else _
      split_ifs with hv
      · exact (locRep v mF QF' (f ⟨v, hv⟩)).2.2
      · exact e₀_mem_std v⟩

theorem locOf_glueComp (f : (v : S) → LocTypes v mF QF') (v : S) :
    locOf mF QF' v (glueComp m₀ Q₀' hm f) = locRep v mF QF' (f v) := by
  classical
  apply Subtype.ext
  rw [locOf_val]
  show loc (v : HeightOneSpectrum (𝓞 F)) (glueFam m₀ Q₀' hm f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : (v : HeightOneSpectrum (𝓞 F)) ∈ S then _ else _) = _
  simp only [v.2, ↓reduceDIte]

theorem locOf_glueComp_of_not_mem (f : (v : S) → LocTypes v mF QF') {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) : locOf mF QF' v (glueComp m₀ Q₀' hm f) = locStdPt v mF QF' := by
  classical
  apply Subtype.ext
  rw [locOf_val]
  show loc v (glueFam m₀ Q₀' hm f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : v ∈ S then _ else _) = _
  simp only [hv, ↓reduceDIte]
  rfl

theorem typeMap_glueComp (f : (v : S) → LocTypes v mF QF') :
    typeMap m₀ Q₀' hm (Quotient.mk'' (glueComp m₀ Q₀' hm f)) = f := by
  funext v
  rw [typeMap_mk, locOf_glueComp, locRep_mk]

/-- **Global types = families of local types at the primes dividing $2m$** (`typeMap` is bijective). -/
def typeEquiv : orbitRel.Quotient (OAf QF') (CompSet mF QF' Lstd) ≃ ((v : S) → LocTypes v mF QF') :=
  Equiv.ofBijective _ ⟨typeMap_injective m₀ Q₀' hm, fun f => ⟨_, typeMap_glueComp m₀ Q₀' hm f⟩⟩

/-- **The global weight of a glued lattice is the product of the local weights**
(`relIndex_restrictedPi`: the stabilizers are products of local stabilizers, equal to $O(\mathfrak o_\mathfrak p^n)$ off $2m$). -/
theorem compWeight_glueComp (f : (v : S) → LocTypes v mF QF') :
    compWeight mF QF' Lstd (glueComp m₀ Q₀' hm f) = ∏ v : S, locWeight v mF QF' (locRep v mF QF' (f v)) := by
  classical
  set y := glueComp m₀ Q₀' hm f
  set A' : (v : HeightOneSpectrum (𝓞 F)) → Subgroup (orthGroup QF' (v.adicCompletion F)) :=
    fun v => stabilizer (orthGroup QF' (v.adicCompletion F)) (locOf mF QF' v y)
  have hA : ∀ v ∉ S, A' v = stdStab QF' v := by
    intro v hv
    simp only [A']
    rw [locOf_glueComp_of_not_mem m₀ Q₀' hm f hv, stabilizer_locStdPt]
  have hB : ∀ v ∉ S, stdStab QF' v = stdStab QF' v := fun _ _ => rfl
  have hAm : ∀ h, h ∈ stabilizer (OAf QF') y ↔ ∀ v, h v ∈ A' v := by
    intro h
    rw [stabilizer_compSet, Subgroup.mem_comap]
    show (∀ v, _ = _) ↔ _
    refine forall_congr' fun v => ?_
    simp only [A', mem_stabilizer_iff]
    constructor
    · intro hh; exact Subtype.ext hh
    · intro hh; exact congrArg Subtype.val hh
  have hBm : ∀ h, h ∈ locStab QF' (stdLat F n) ↔ ∀ v, h v ∈ stdStab QF' v := mem_locStab_intVec QF'
  have e1 := relIndex_restrictedPi S A' (fun v => stdStab QF' v) hA hB _ _ hAm hBm
  have e2 := relIndex_restrictedPi S (fun v => stdStab QF' v) A' hB hA _ _ hBm hAm
  unfold compWeight
  rw [e1, e2, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [A', locWeight]
  rw [locOf_glueComp]

/-- **The type sum factors over the primes dividing $2m$**: for
$Q = \langle m\rangle\perp Q'$ totally positive definite with $\mathcal O_F^{n+1}$ integral,
$$\sum_{t\in O(Q')(\mathbb A_f)\backslash Y} w(t) = \prod_{\mathfrak p \mid 2m} W_\mathfrak p,\qquad W_\mathfrak p = \sum_{t_\mathfrak p} w_\mathfrak p(t_\mathfrak p).$$
*Proof:* global types are the families of local types (`typeEquiv`; one local type off $2m$, `exists_smul_locStdPt`), the
weight of a global type may be computed on the glued representative (`compWeight_of_mem_orbit`), where it is the
product of the local weights (`compWeight_glueComp`); then expand the product of sums. -/
@[kb "weil1982" "§3.5 (type sum as a product of local sums) [unverified locator]"]
theorem typeSum_eq_prod (hpd : IsTotallyPosDef (splitForm mF QF')) (hLi : IsIntegral (splitForm mF QF') Lstd.1) :
    ∑ᶠ t : orbitRel.Quotient (OAf QF') (CompSet mF QF' Lstd), typeWeight mF QF' Lstd t =
      ∏ v ∈ S, locTypeSum v mF QF' := by
  classical
  have hmF : mF ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm
  have hpd' := isTotallyPosDef_of_splitForm hpd
  have hLi' := isIntegral_of_splitForm hLi
  have hfin := finite_types mF QF' Lstd hpd hLi hmF
  have hfinP : Finite ((v : S) → LocTypes v mF QF') := Finite.of_equiv _ (typeEquiv m₀ Q₀' hm)
  have hfinv : ∀ v : S, Finite (LocTypes v mF QF') := by
    intro v
    let f₀ : (v : S) → LocTypes v mF QF' := fun w => Quotient.mk'' (locStdPt w mF QF')
    exact Finite.of_injective (fun x => Function.update f₀ v x) (Function.update_injective f₀ v)
  let _ : Fintype (orbitRel.Quotient (OAf QF') (CompSet mF QF' Lstd)) := Fintype.ofFinite _
  let _ : ∀ v : S, Fintype (LocTypes v mF QF') := fun v => Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have step : ∀ t, typeWeight mF QF' Lstd t =
      compWeight mF QF' Lstd (glueComp m₀ Q₀' hm (typeEquiv m₀ Q₀' hm t)) := by
    intro t
    rw [typeWeight_eq_compWeight]
    refine compWeight_of_mem_orbit mF QF' Lstd hpd' hLi' ?_
    have h1 : (Quotient.mk'' (glueComp m₀ Q₀' hm (typeEquiv m₀ Q₀' hm t)) :
        orbitRel.Quotient (OAf QF') (CompSet mF QF' Lstd)) = t :=
      typeMap_injective m₀ Q₀' hm (typeMap_glueComp m₀ Q₀' hm _)
    have h2 : (Quotient.mk'' t.out : orbitRel.Quotient (OAf QF') (CompSet mF QF' Lstd)) =
        Quotient.mk'' (glueComp m₀ Q₀' hm (typeEquiv m₀ Q₀' hm t)) := by
      rw [h1, Quotient.out_eq']
    exact Quotient.exact' h2
  rw [Finset.sum_congr rfl fun t _ => step t,
    Equiv.sum_comp (typeEquiv m₀ Q₀' hm) (fun f => compWeight mF QF' Lstd (glueComp m₀ Q₀' hm f))]
  simp_rw [compWeight_glueComp]
  rw [← Finset.prod_coe_sort S]
  simp_rw [locTypeSum, finsum_eq_sum_of_fintype]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end Factor


/-! ### The product formula for $2m$ -/

section ProductFormula

variable {F : Type} [Field F] [NumberField F]

/-- $\prod_\sigma|\sigma(x)| = |N_{F/\mathbb Q}(x)|$. -/
theorem prod_norm_embeddings (x : F) : ∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  rw [← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, Complex.norm_ratCast]

/-- **The product formula for $2m$:** $\prod_{\mathfrak p \mid 2m}|2m|_\mathfrak p = |N_{F/\mathbb Q}(2m)|^{-1}$ (`normTwoM`), from
Mathlib's `FinitePlace.prod_eq_inv_abs_norm`. -/
@[kb "weil1982" "§2.1 (product formula) [unverified]"]
theorem prod_absTwoM (m₀ : 𝓞 F) (hm : m₀ ≠ 0) :
    ∏ v ∈ badSet m₀ hm, absTwoM v m₀ = (normTwoM m₀)⁻¹ := by
  have hx : (algebraMap (𝓞 F) F (2 * m₀)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ RingOfIntegers.coe_injective]; exact mul_ne_zero two_ne_zero hm
  have h1 : ∏ v ∈ badSet m₀ hm, absTwoM v m₀ = ∏ᶠ v, absTwoM v m₀ := by
    refine (finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_).symm
    by_contra h
    exact hv (absTwoM_eq_one v fun h' => h ((mem_badSet m₀ hm).mpr h'))
  have h2 := NumberField.FinitePlace.prod_eq_inv_abs_norm hx
  rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm] at h2
  simp only [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply] at h2
  rw [h1]
  unfold absTwoM normTwoM
  rw [h2, prod_norm_embeddings]
  push_cast
  rfl

end ProductFormula

/-! ### Products of local identities -/

section TProd

variable {ι : Type*}

/-- **Assembling local identities into a product identity** (the $\prod_\mathfrak p$ of `LocalOrbitalIdentity`): if
$W_v a_v c_v^n = b_v\beta_v$ for every $v$, with $W_v = c_v = 1$ off a finite set $S$, $W_v, c_v \ne 0$, and $\prod b_v$,
$\prod\beta_v$ convergent, then $\big(\prod_S W_v\big)\prod_v a_v = \big(\prod_S c_v\big)^{-n}\prod_v b_v\prod_v\beta_v$. -/
theorem tprod_local_identity (S : Finset ι) (n : ℕ) (a b β W c : ι → ℝ) (hW : ∀ v ∉ S, W v = 1)
    (hc : ∀ v ∉ S, c v = 1) (hW0 : ∀ v, W v ≠ 0) (hc0 : ∀ v, c v ≠ 0)
    (hloc : ∀ v, W v * a v * c v ^ n = b v * β v) (hb : Multipliable b) (hβ : Multipliable β) :
    (∏ v ∈ S, W v) * ∏' v, a v = (∏ v ∈ S, c v)⁻¹ ^ n * (∏' v, b v) * ∏' v, β v := by
  set g : ι → ℝ := fun v => (W v * c v ^ n)⁻¹
  have hg1 : ∀ v ∉ S, g v = 1 := fun v hv => by simp [g, hW v hv, hc v hv]
  have ha : a = fun v => b v * β v * g v := by
    funext v
    have h := hloc v
    simp only [g]
    have : W v * c v ^ n ≠ 0 := mul_ne_zero (hW0 v) (pow_ne_zero _ (hc0 v))
    rw [eq_mul_inv_iff_mul_eq₀ this]
    linear_combination h
  have hgm : Multipliable g := multipliable_of_ne_finset_one hg1
  have hgt : ∏' v, g v = ∏ v ∈ S, g v := tprod_eq_prod hg1
  rw [ha, (hb.mul hβ).tprod_mul hgm, hb.tprod_mul hβ, hgt]
  have hprod : ∏ v ∈ S, g v = (∏ v ∈ S, W v)⁻¹ * ((∏ v ∈ S, c v)⁻¹) ^ n := by
    simp only [g, Finset.prod_inv_distrib, Finset.prod_mul_distrib, Finset.prod_pow, mul_inv, inv_pow]
  have hW' : ∏ v ∈ S, W v ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hW0 v
  rw [hprod]
  field_simp

/-- The same with $\prod a_v$ convergent and $\prod b_v$ convergent to a nonzero limit (then $\prod\beta_v$ converges). -/
theorem tprod_local_identity' (S : Finset ι) (n : ℕ) (a b β W c : ι → ℝ) (hW : ∀ v ∉ S, W v = 1)
    (hc : ∀ v ∉ S, c v = 1) (hW0 : ∀ v, W v ≠ 0) (hc0 : ∀ v, c v ≠ 0)
    (hloc : ∀ v, W v * a v * c v ^ n = b v * β v) (ha : Multipliable a) (hb : Multipliable b)
    (hb0 : ∏' v, b v ≠ 0) :
    (∏ v ∈ S, W v) * ∏' v, a v = (∏ v ∈ S, c v)⁻¹ ^ n * (∏' v, b v) * ∏' v, β v := by
  have hbv : ∀ v, b v ≠ 0 := by
    intro v h0
    exact hb0 (tprod_of_exists_eq_zero ⟨v, h0⟩)
  have hβeq : β = fun v => W v * c v ^ n * a v / b v := by
    funext v
    rw [eq_div_iff (hbv v)]
    linear_combination (hloc v).symm
  have hβm : Multipliable β := by
    rw [hβeq]
    have hfin : Multipliable fun v => W v * c v ^ n :=
      multipliable_of_ne_finset_one (s := S) fun v hv => by simp [hW v hv, hc v hv]
    exact (hfin.mul ha).div₀ hb hb0
  exact tprod_local_identity S n a b β W c hW hc hW0 hc0 hloc hb hβm

end TProd

/-! ### Weil's local orbital identity: from the primes to the input -/

section Assembly

open LocalDensity Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **The product of the local orbital identities is `LocalOrbitalIdentity`** (Weil 1982, §3.4–3.5 [unverified locator];
Kitaoka 1993, §6.8 [unverified]). For $Q_0 = \langle m\rangle\perp Q_0'$ over $\mathcal O_F$, totally positive definite with
$\mathcal O_F^{n+1}$ integral, $m \ne 0$: if the local identity holds at the finitely many primes $\mathfrak p \mid 2m$
(`LocalOrbitalIdentityAt`; at all other primes it is a theorem, `localOrbitalIdentityAt_of_not_mem`) and the Euler
products $\prod_\mathfrak p\alpha_\mathfrak p(L')$, $\prod_\mathfrak p\beta_\mathfrak p(L, m)$ converge, then
$$\Big(\sum_t w(t)\Big)\prod_\mathfrak p\alpha_\mathfrak p(L) = |N(2m)|^n\prod_\mathfrak p\alpha_\mathfrak p(L')\prod_\mathfrak p\beta_\mathfrak p(L, m).$$
*Proof:* the type sum is $\prod_{\mathfrak p\mid2m}W_\mathfrak p$ (`typeSum_eq_prod`), $\prod_{\mathfrak p\mid 2m}|2m|_\mathfrak p = |N(2m)|^{-1}$
(`prod_absTwoM`), and the local identities multiply (`tprod_local_identity`). -/
@[kb "weil1982" "§3.4-3.5 (local fibration, product over p) [unverified locator]"]
theorem localOrbitalIdentity_of_local (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : Lattices.IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), 2 * m ∈ v.asIdeal → LocalOrbitalIdentityAt v Q₀' m)
    (hb : Multipliable fun v => NF.siegelDensity v Q₀' Q₀')
    (hβ : Multipliable fun v => NF.localDensity v (splitForm m Q₀') m) :
    LocalOrbitalIdentity Q₀' m := by
  rw [map_splitForm_alg] at hpd hLi
  have hmF : algebraMap (𝓞 F) F m ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map (isTotallyPosDef_of_splitForm hpd).nondegenerate
  have hloc : ∀ v, LocalOrbitalIdentityAt v Q₀' m := fun v => by
    by_cases h : 2 * m ∈ v.asIdeal
    · exact hbad v h
    · exact localOrbitalIdentityAt_of_not_mem v m Q₀' hQ' h
  set S := badSet m hm
  have hnotS : ∀ v ∉ S, 2 * m ∉ v.asIdeal := fun v hv h => hv ((mem_badSet m hm).mpr h)
  have hW : ∀ v ∉ S, locTypeSum v (algebraMap (𝓞 F) F m) (Q₀'.map (algebraMap (𝓞 F) F)) = 1 :=
    fun v hv => locTypeSum_eq_one v m Q₀' (hnotS v hv)
  have hc : ∀ v ∉ S, absTwoM v m = 1 := fun v hv => absTwoM_eq_one v (hnotS v hv)
  have hsum := typeSum_eq_prod m Q₀' hm hpd hLi
  have hpos := typeSum_pos hpd hLi hmF
  rw [hsum] at hpos
  have hW0 : ∀ v, locTypeSum v (algebraMap (𝓞 F) F m) (Q₀'.map (algebraMap (𝓞 F) F)) ≠ 0 := by
    intro v
    by_cases hv : v ∈ S
    · exact Finset.prod_ne_zero_iff.mp hpos.ne' v hv
    · rw [hW v hv]; exact one_ne_zero
  have hc0 : ∀ v, absTwoM v m ≠ 0 := fun v => (absTwoM_pos v hm).ne'
  refine ⟨?_⟩
  rw [hsum, tprod_local_identity S n _ _ _ _ _ hW hc hW0 hc0 (fun v => (hloc v).typeSum_eq) hb hβ,
    prod_absTwoM m hm, inv_inv]

/-- **`LocalOrbitalIdentity` from the bad primes, with the convergence of $\prod\alpha_\mathfrak p(L)$ and of
$\prod\alpha_\mathfrak p(L') \ne 0$** (then $\prod\beta_\mathfrak p(L, m)$ converges; `tprod_local_identity'`). This is the form used
in the induction, where both Euler products are known to converge (`hasProd_siegelDensity_odd/even`) and
$\prod\alpha_\mathfrak p(L') \ne 0$ follows from the mass formula in rank $n$. -/
@[kb "weil1982" "§3.4-3.5 (local fibration, product over p) [unverified locator]"]
theorem localOrbitalIdentity_of_local' (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : Lattices.IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), 2 * m ∈ v.asIdeal → LocalOrbitalIdentityAt v Q₀' m)
    (ha : Multipliable fun v => NF.siegelDensity v (splitForm m Q₀') (splitForm m Q₀'))
    (hb : Multipliable fun v => NF.siegelDensity v Q₀' Q₀')
    (hb0 : ∏' v, NF.siegelDensity v Q₀' Q₀' ≠ 0) :
    LocalOrbitalIdentity Q₀' m := by
  rw [map_splitForm_alg] at hpd hLi
  have hmF : algebraMap (𝓞 F) F m ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map (isTotallyPosDef_of_splitForm hpd).nondegenerate
  have hloc : ∀ v, LocalOrbitalIdentityAt v Q₀' m := fun v => by
    by_cases h : 2 * m ∈ v.asIdeal
    · exact hbad v h
    · exact localOrbitalIdentityAt_of_not_mem v m Q₀' hQ' h
  set S := badSet m hm
  have hnotS : ∀ v ∉ S, 2 * m ∉ v.asIdeal := fun v hv h => hv ((mem_badSet m hm).mpr h)
  have hW : ∀ v ∉ S, locTypeSum v (algebraMap (𝓞 F) F m) (Q₀'.map (algebraMap (𝓞 F) F)) = 1 :=
    fun v hv => locTypeSum_eq_one v m Q₀' (hnotS v hv)
  have hc : ∀ v ∉ S, absTwoM v m = 1 := fun v hv => absTwoM_eq_one v (hnotS v hv)
  have hsum := typeSum_eq_prod m Q₀' hm hpd hLi
  have hpos := typeSum_pos hpd hLi hmF
  rw [hsum] at hpos
  have hW0 : ∀ v, locTypeSum v (algebraMap (𝓞 F) F m) (Q₀'.map (algebraMap (𝓞 F) F)) ≠ 0 := by
    intro v
    by_cases hv : v ∈ S
    · exact Finset.prod_ne_zero_iff.mp hpos.ne' v hv
    · rw [hW v hv]; exact one_ne_zero
  have hc0 : ∀ v, absTwoM v m ≠ 0 := fun v => (absTwoM_pos v hm).ne'
  refine ⟨?_⟩
  rw [hsum, tprod_local_identity' S n _ _ _ _ _ hW hc hW0 hc0 (fun v => (hloc v).typeSum_eq) ha hb hb0,
    prod_absTwoM m hm, inv_inv]

end Assembly


/-! ### Consequences for Weil's induction -/

section Induction

open LocalDensity Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **$\prod_\mathfrak p\alpha_\mathfrak p(L, L)$ converges in every rank $N \ne 0, 2$** (`hasProd_siegelDensity_odd/even`). -/
theorem multipliable_siegelDensity {N : ℕ} (hN0 : N ≠ 0) (hN2 : N ≠ 2) (Q₀ : QuadForm (𝓞 F) N)
    (hQ : Q₀.Nondegenerate) : Multipliable fun v => NF.siegelDensity v Q₀ Q₀ := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · exact (hasProd_siegelDensity_even k (by omega) Q₀ hQ).multipliable
  · exact (hasProd_siegelDensity_odd k Q₀ hQ).multipliable

/-- The mass formula in rank $n$ makes $\prod_\mathfrak p\alpha_\mathfrak p(L') \ne 0$. -/
theorem tprod_siegelDensity_ne_zero {N : ℕ} (Q₀ : QuadForm (𝓞 F) N)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N).1) (h : MassFormulaHolds Q₀) :
    ∏' v, NF.siegelDensity v Q₀ Q₀ ≠ 0 := by
  have hpos := mass_pos hpd (stdLat F N) hLi
  unfold MassFormulaHolds at h
  rw [h] at hpos
  have hT : tamagawaK Q₀ ≠ 0 := (inv_pos.mp hpos).ne'
  unfold tamagawaK at hT
  exact right_ne_zero_of_mul hT

/-- **`LocalOrbitalIdentity` in the induction, from the primes dividing $2m$** ($n \ge 3$): given the local orbital identity
at the finitely many $\mathfrak p \mid 2m$ and the mass formula in rank $n$, the input holds. -/
theorem localOrbitalIdentity_of_massFormula (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hn : 3 ≤ n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), 2 * m ∈ v.asIdeal → LocalOrbitalIdentityAt v Q₀' m)
    (hIH : MassFormulaHolds Q₀') : LocalOrbitalIdentity Q₀' m := by
  have hpd₀ := hpd
  have hLi₀ := hLi
  rw [map_splitForm_alg] at hpd₀ hLi₀
  have hpd' := isTotallyPosDef_of_splitForm hpd₀
  have hLi' := isIntegral_of_splitForm hLi₀
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map hpd'.nondegenerate
  have hQ : (splitForm m Q₀').Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  exact localOrbitalIdentity_of_local' m hm Q₀' hpd hLi hbad
    (multipliable_siegelDensity (by omega) (by omega) _ hQ)
    (multipliable_siegelDensity (by omega) (by omega) _ hQ')
    (tprod_siegelDensity_ne_zero Q₀' hpd' hLi' hIH)

/-- **`LocalOrbitalIdentity` from the orbit counts at the primes dividing $2m$** ($n \ge 3$, mass formula in rank $n$):
the input is now `LocalTypeOrbitCount` (no densities, no Jacobian) at the finitely many $\mathfrak p \mid 2m$
(`localOrbitalIdentityAt_of_orbitCount`). -/
@[kb "weil1982" "§3.4-3.5 (local fibration, product over p) [unverified locator]"]
theorem localOrbitalIdentity_of_orbitCount (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hn : 3 ≤ n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), 2 * m ∈ v.asIdeal → LocalTypeOrbitCount v Q₀' m)
    (hIH : MassFormulaHolds Q₀') : LocalOrbitalIdentity Q₀' m := by
  have hpd₀ := hpd
  rw [map_splitForm_alg] at hpd₀
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map (isTotallyPosDef_of_splitForm hpd₀).nondegenerate
  exact localOrbitalIdentity_of_massFormula m hm Q₀' hn hpd hLi
    (fun v h => localOrbitalIdentityAt_of_orbitCount v m hm Q₀' hQ' (hbad v h)) hIH

/-- **Weil's induction step with the local identity discharged away from $2m$** ($n \ge 3$): Siegel's formula for $m$,
the local orbital identity at the primes $\mathfrak p \mid 2m$, and the mass formula in rank $n$ give the mass formula in
rank $n + 1$ (`massFormula_succ` with `localOrbitalIdentity_of_massFormula`). -/
@[kb "weil1982" "§4.5, pp. 100-109 (induction on m); Thm. 4.5.1, p. 109"]
theorem massFormula_succ_of_local (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hn : 3 ≤ n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hS : SiegelFormulaAt (splitForm m Q₀') m)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), 2 * m ∈ v.asIdeal → LocalOrbitalIdentityAt v Q₀' m)
    (hIH : MassFormulaHolds Q₀') : MassFormulaHolds (splitForm m Q₀') :=
  massFormula_succ m hm Q₀' hpd hLi hS (localOrbitalIdentity_of_massFormula m hm Q₀' hn hpd hLi hbad hIH) hIH

/-- **$\tau(SO) = 2$ in rank $n + 1$** from Siegel's formula for $m$, the local identity at $\mathfrak p \mid 2m$ and the mass
formula in rank $n$ ($n \ge 3$). -/
@[kb "weil1982" "Thm. 4.5.1, p. 109 (τ(SO) = 2 for m ≥ 3)"]
theorem tamagawaNumberTwo_succ_of_local (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hn : 3 ≤ n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hS : SiegelFormulaAt (splitForm m Q₀') m)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), 2 * m ∈ v.asIdeal → LocalOrbitalIdentityAt v Q₀' m)
    (hIH : MassFormulaHolds Q₀') : TamagawaNumberTwo (splitForm m Q₀') :=
  tamagawaNumberTwo_succ m hm Q₀' hpd hLi hS (localOrbitalIdentity_of_massFormula m hm Q₀' hn hpd hLi hbad hIH)
    hIH

/-- **The mass formula in ranks $n+1$ and $n$ gives Siegel's formula for $m$** (Weil 1982,
§4.5, p. 100 and Thm. 4.5.1, p. 109; Siegel 1935 [unverified]): with the global reduction (`repMass_eq_mass_mul`), the local orbital
identity and the archimedean identity (`archProd_splitForm`),
$$\sum_{\mathrm{cls}(M)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L')\,W = \frac{W}{\mu_{\mathrm{Tam}}(K_{SO}(Q_0'))}
  = \frac{S(L, m)}{\mu_{\mathrm{Tam}}(K_{SO}(Q_0))} = \mathrm{Mass}(L)\,S(L, m).$$ -/
@[kb "weil1982" "§4.5, p. 100 (τ(G) = 2 is equivalent to Siegel's main theorem); Thm. 4.5.1, p. 109"]
theorem siegelFormulaAt_of_massFormula (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hloc : LocalOrbitalIdentity Q₀' m) (hMF : MassFormulaHolds (splitForm m Q₀'))
    (hIH : MassFormulaHolds Q₀') : SiegelFormulaAt (splitForm m Q₀') m := by
  have hpdS := hpd
  have hLiS := hLi
  unfold MassFormulaHolds at hIH hMF
  set QF' := Q₀'.map (algebraMap (𝓞 F) F)
  set mF := algebraMap (𝓞 F) F m
  have hsplit := map_splitForm_alg m Q₀'
  rw [hsplit] at hpd hLi
  have hmF : mF ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm
  have hpd' := isTotallyPosDef_of_splitForm hpd
  have hLi' := isIntegral_of_splitForm hLi
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map hpd'.nondegenerate
  have hR := repMass_eq_mass_mul mF QF' (stdLat F (n + 1)) hpd hLi hmF hpd' hLi'
  have hloc' := hloc.typeSum_eq
  set W := ∑ᶠ t : orbitRel.Quotient (OAf QF') (CompSet mF QF' (stdLat F (n + 1))),
    typeWeight mF QF' (stdLat F (n + 1)) t
  set A := ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v (splitForm m Q₀') (splitForm m Q₀')
  set A' := ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀' Q₀'
  set B := ∏' v : HeightOneSpectrum (𝓞 F), NF.localDensity v (splitForm m Q₀') m
  set Pr := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram (splitForm m Q₀') σ)
  set Pr' := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀' σ)
  set ρ := ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (n + 1) ‖σ mF‖ (detGram (splitForm m Q₀') σ)
  set Nm := normTwoM m
  set δ := |(NumberField.discr F : ℝ)|
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have harch : Pr * Nm ^ n = Pr' * ρ := archProd_splitForm m hm Q₀' hQ'
  have hT : tamagawaK (splitForm m Q₀') = δ ^ (-(((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1) / 4)) * Pr * A := rfl
  have hT' : tamagawaK Q₀' = δ ^ (-((n : ℝ) * (n - 1) / 4)) * Pr' * A' := rfl
  have hSP : siegelProduct (splitForm m Q₀') m = δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * ρ * B := rfl
  have hδe : δ ^ (-(((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1) / 4)) =
      δ ^ (-((n : ℝ) * (n - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  -- nonvanishing of the Tamagawa constants
  have hT0 : tamagawaK (splitForm m Q₀') ≠ 0 := by
    have hpos := mass_pos hpdS (stdLat F (n + 1)) hLiS
    rw [hMF] at hpos; exact (inv_pos.mp hpos).ne'
  have hT0' : tamagawaK Q₀' ≠ 0 := by
    have hpos := mass_pos hpd' (stdLat F n) hLi'
    rw [hIH] at hpos; exact (inv_pos.mp hpos).ne'
  refine ⟨?_⟩
  rw [hsplit, hR, hIH]
  rw [← hsplit, hMF]
  have key : W * tamagawaK (splitForm m Q₀') = siegelProduct (splitForm m Q₀') m * tamagawaK Q₀' := by
    rw [hT, hT', hSP, hδe]
    linear_combination (δ ^ (-((n : ℝ) * (n - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * Pr) * hloc' +
      (δ ^ (-((n : ℝ) * (n - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) * A' * B) * harch
  field_simp
  linear_combination key

/-- **Siegel's formula for $m$ from $\tau(SO) = 2$ in ranks $n + 1$ and $n$** ($n \ge 3$), given the local orbital identity at
the primes $\mathfrak p \mid 2m$: the direction needed for the induction (`massFormula` turns $\tau = 2$ into the mass formula). -/
@[kb "weil1982" "§4.5, p. 100 (τ(G) = 2 is equivalent to Siegel's main theorem); Thm. 4.5.1, p. 109"]
theorem siegelFormulaAt_of_tamagawa (m : 𝓞 F) (hm : m ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hn : 3 ≤ n)
    (hpd : IsTotallyPosDef ((splitForm m Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m Q₀').map (algebraMap (𝓞 F) F)) (stdLat F (n + 1)).1)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), 2 * m ∈ v.asIdeal → LocalOrbitalIdentityAt v Q₀' m)
    (hτ : TamagawaNumberTwo (splitForm m Q₀')) (hτ' : TamagawaNumberTwo Q₀') :
    SiegelFormulaAt (splitForm m Q₀') m := by
  have hpd₀ := hpd
  have hLi₀ := hLi
  rw [map_splitForm_alg] at hpd₀ hLi₀
  have hpd' := isTotallyPosDef_of_splitForm hpd₀
  have hLi' := isIntegral_of_splitForm hLi₀
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map hpd'.nondegenerate
  have hQ : (splitForm m Q₀').Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hIH : MassFormulaHolds Q₀' := massFormula Q₀' hQ' (by omega) hpd' hLi' hτ'
  have hMF : MassFormulaHolds (splitForm m Q₀') := massFormula _ hQ (by omega) hpd hLi hτ
  exact siegelFormulaAt_of_massFormula m hm Q₀' hpd hLi
    (localOrbitalIdentity_of_massFormula m hm Q₀' hn hpd hLi hbad hIH) hMF hIH

end Induction

end QuadFormsKB.Tamagawa
