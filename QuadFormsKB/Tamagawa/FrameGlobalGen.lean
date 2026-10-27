/-
# The type sum of an arbitrary lattice for frames as a product of local type sums

**Layer:** $F$ a number field, an **arbitrary** integral lattice $L$ in the split space $V = (F^{r+n'}, T\perp Q')$ with $T_0$, $Q_0'$ over
$\mathcal O_F$; the local types of `FrameLocal.lean` based at an arbitrary $\mathfrak o_\mathfrak p$-lattice $\Lambda$.

`FrameGlobal.lean` factors the type sum of the standard lattice $L = \mathcal O_F^{r+n'}$ over the primes in `frameBadSet`. Here $L$ is any
lattice (in practice $g^{-1}\mathcal O_F^{N}$ for an adapted frame $g$), exactly as `GeneralFactor.lean` generalizes
the vector case.

**Defines**
* `LocFrameSetG` $= Y_\mathfrak p(\Lambda) = \{M \in O(V)(F_\mathfrak p)\,\Lambda : E \subseteq M\}$ with its $O(Q')(F_\mathfrak p)$-action, `LocFrameTypesG`,
  `locFrameRepG`, `locFrameWeightG` and `locFrameTypeSumG` $W_\mathfrak p(\Lambda)$; for $\Lambda = \mathfrak o_\mathfrak p^{r+n'}$ these agree with
  `locFrameTypeSum` (`locFrameTypeSumG_std`);
* `frameBadSetG` $= S \cup \{\mathfrak p : L_\mathfrak p \ne \mathfrak o_\mathfrak p^{r+n'}\}$ (finite), $S$ = `frameBadSet`.

**Proves**
* `locFrameTypeSumG_eq_one_of_good`: $W_\mathfrak p(L_\mathfrak p) = 1$ if $L_\mathfrak p = \mathfrak o_\mathfrak p^{r+n'}$ and $\mathfrak p \notin S$;
* **`typeSumT_eq_finprod_gen`** (Weil 1982, §3.5 [unverified locator]):
  $\sum_{t} w(t) = \prod_\mathfrak p W_\mathfrak p(L_\mathfrak p)$, a product with finite support
  (global types are the families of local types at `frameBadSetG`, glued with `LocFamily.glue`; weights multiply by `relIndex_restrictedPi`).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameGlobal

open NumberField IsDedekindDomain Matrix MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity LocalDensity.DVR

/-! ### Local types of frames based at an arbitrary lattice -/

section LocalTypesG

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T : QuadForm F r)
  (Q' : QuadForm F n') (Λ : Submodule (v.adicCompletionIntegers F) (Fin (r + n') → v.adicCompletion F))

local notation "QB" => blockForm T Q'
local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The local type set based at $\Lambda$:** $Y_\mathfrak p(\Lambda) = \{M \in O(V)(F_\mathfrak p)\cdot\Lambda : e_0, \dots, e_{r-1} \in M\}$ for
$V = (F^{r+n'}, T\perp Q')$ (Weil 1982, §3.4 [unverified]). For $\Lambda = \mathfrak o_\mathfrak p^{r+n'}$ this is `LocFrameSet`. -/
def LocFrameSetG : Type _ :=
  {M : Submodule 𝔬 (Fin (r + n') → Fv) //
    (∃ g : orthGroup QB Fv, locAct v (g : GL (Fin (r + n')) Fv) Λ = M) ∧ ∀ j, stdCol v (n' := n') j ∈ M}

instance LocFrameSetG.instMulAction : MulAction (orthGroup Q' Fv) (LocFrameSetG v T Q' Λ) where
  smul h M := ⟨locAct v (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv) M.1, by
      obtain ⟨g, hg⟩ := M.2.1
      exact ⟨orthEmbB T Q' Fv h * g, by rw [Subgroup.coe_mul, locAct_mul, hg]⟩,
    stdCol_mem_locAct_orthEmbB v T Q' h M.2.2⟩
  one_smul M := Subtype.ext (by
    show locAct v (orthEmbB T Q' Fv 1 : GL (Fin (r + n')) Fv) M.1 = M.1
    rw [map_one, OneMemClass.coe_one, locAct_one])
  mul_smul a b M := Subtype.ext (by
    show locAct v (orthEmbB T Q' Fv (a * b) : GL (Fin (r + n')) Fv) M.1 =
      locAct v (orthEmbB T Q' Fv a : GL (Fin (r + n')) Fv) (locAct v (orthEmbB T Q' Fv b : GL (Fin (r + n')) Fv) M.1)
    rw [map_mul, Subgroup.coe_mul, locAct_mul])

theorem LocFrameSetG.smul_val (h : orthGroup Q' Fv) (M : LocFrameSetG v T Q' Λ) :
    (h • M).1 = locAct v (orthEmbB T Q' Fv h : GL (Fin (r + n')) Fv) M.1 := rfl

/-- The point $\Lambda \in Y_\mathfrak p(\Lambda)$, when $\Lambda$ contains the columns of the standard frame. -/
def locFrameStdPtG (h : ∀ j, stdCol v (n' := n') j ∈ Λ) : LocFrameSetG v T Q' Λ :=
  ⟨Λ, ⟨1, locAct_one _⟩, h⟩

/-- **The local types** at $\mathfrak p$ based at $\Lambda$: the $O(Q')(F_\mathfrak p)$-orbits on $Y_\mathfrak p(\Lambda)$. -/
abbrev LocFrameTypesG : Type _ := orbitRel.Quotient (orthGroup Q' Fv) (LocFrameSetG v T Q' Λ)

/-- The representative of a local type: $\Lambda$ for its own type (when $\Lambda \in Y_\mathfrak p(\Lambda)$), `Quotient.out` otherwise. -/
def locFrameRepG (t : LocFrameTypesG v T Q' Λ) : LocFrameSetG v T Q' Λ := by
  classical
  exact if h : ∀ j, stdCol v (n' := n') j ∈ Λ then
    (if (Quotient.mk'' (locFrameStdPtG v T Q' Λ h) : LocFrameTypesG v T Q' Λ) = t then locFrameStdPtG v T Q' Λ h
      else t.out)
  else t.out

theorem locFrameRepG_mk (t : LocFrameTypesG v T Q' Λ) :
    (Quotient.mk'' (locFrameRepG v T Q' Λ t) : LocFrameTypesG v T Q' Λ) = t := by
  classical
  unfold locFrameRepG
  split_ifs with h h2
  · exact h2
  · exact Quotient.out_eq' t
  · exact Quotient.out_eq' t

/-- **The local weight** of $M \in Y_\mathfrak p(\Lambda)$: with $K_M = \mathrm{Stab}_{O(Q')(F_\mathfrak p)}(M)$ and $K_0' = O(\mathfrak o_\mathfrak p^{n'})$,
$w_\mathfrak p(M) = [K_0' : K_M\cap K_0']/[K_M : K_M \cap K_0']$ (the formula of `locFrameWeight`). -/
def locFrameWeightG (M : LocFrameSetG v T Q' Λ) : ℝ :=
  ((stabilizer (orthGroup Q' Fv) M).relIndex (stdStab Q' v) : ℝ) /
    ((stdStab Q' v).relIndex (stabilizer (orthGroup Q' Fv) M) : ℝ)

/-- **The local type sum** $W_\mathfrak p(\Lambda) = \sum_t w_\mathfrak p(M_t)$ based at $\Lambda$. -/
def locFrameTypeSumG : ℝ := ∑ᶠ t : LocFrameTypesG v T Q' Λ, locFrameWeightG v T Q' Λ (locFrameRepG v T Q' Λ t)

/-- For $\Lambda = \mathfrak o_\mathfrak p^{r+n'}$ the general local type sum is `locFrameTypeSum`. -/
theorem locFrameTypeSumG_std : locFrameTypeSumG v T Q' (std v) = locFrameTypeSum v T Q' := by
  classical
  unfold locFrameTypeSumG locFrameTypeSum
  refine finsum_congr fun t => ?_
  by_cases h : (Quotient.mk'' (locFrameStdPt v T Q') : LocFrameTypes v T Q') = t
  · have h' : (Quotient.mk'' (locFrameStdPtG v T Q' (std v) (fun j => stdCol_mem_std v j)) :
        LocFrameTypesG v T Q' (std v)) = t := h
    have e1 : locFrameRepG v T Q' (std v) t = locFrameStdPtG v T Q' (std v) (fun j => stdCol_mem_std v j) := by
      unfold locFrameRepG
      rw [dif_pos (fun j => stdCol_mem_std v j), if_pos h']
    have e2 : locFrameRep v T Q' t = locFrameStdPt v T Q' := by
      unfold locFrameRep
      rw [if_pos h]
    rw [e1, e2]
    rfl
  · have h' : ¬ (Quotient.mk'' (locFrameStdPtG v T Q' (std v) (fun j => stdCol_mem_std v j)) :
        LocFrameTypesG v T Q' (std v)) = t := h
    have e1 : locFrameRepG v T Q' (std v) t = t.out := by
      unfold locFrameRepG
      rw [dif_pos (fun j => stdCol_mem_std v j), if_neg h']
    have e2 : locFrameRep v T Q' t = t.out := by
      unfold locFrameRep
      rw [if_neg h]
      rfl
    rw [e1, e2]
    rfl

end LocalTypesG

/-! ### Local components of the global type set of a general lattice -/

section ComponentsG

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T : QuadForm F r) (Q' : QuadForm F n')
  (L : Lat F (r + n'))

/-- **The local component** $M_\mathfrak p \in Y_\mathfrak p(L_\mathfrak p)$ of $M \in Y$ (general $L$). -/
def locOfTG (v : HeightOneSpectrum (𝓞 F)) (M : CompSetT T Q' L) : LocFrameSetG v T Q' (loc v L.1) :=
  ⟨loc v M.1.1, by
      obtain ⟨g, hg, hgM⟩ := M.2.1 v
      exact ⟨⟨g, hg⟩, hgM⟩,
    fun j => by
      rw [← locVec_stdFrameCol v j]; exact locVec_mem_loc v (M.2.2 j)⟩

theorem locOfTG_val (v : HeightOneSpectrum (𝓞 F)) (M : CompSetT T Q' L) :
    (locOfTG T Q' L v M).1 = loc v M.1.1 := rfl

theorem locOfTG_smul (v : HeightOneSpectrum (𝓞 F)) (h : OAf Q') (M : CompSetT T Q' L) :
    locOfTG T Q' L v (h • M) = h v • locOfTG T Q' L v M := by
  refine Subtype.ext ?_
  rw [LocFrameSetG.smul_val, locOfTG_val, locOfTG_val, CompSetT.smul_val]
  exact loc_latSMul (blockForm T Q') (orthEmbBAf T Q' h) M.1 v

/-- **Global orbits are determined prime by prime** (frames, general $L$). -/
theorem mem_orbit_compSetT_iffG (M M' : CompSetT T Q' L) :
    M' ∈ orbit (OAf Q') M ↔
      ∀ v, locOfTG T Q' L v M' ∈ orbit (orthGroup Q' (v.adicCompletion F)) (locOfTG T Q' L v M) := by
  classical
  constructor
  · rintro ⟨h, rfl⟩ v
    exact ⟨h v, (locOfTG_smul T Q' L v h M).symm⟩
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
    have e := locOfTG_smul T Q' L v hA M
    have e2 : loc v (hA • M).1.1 = (locOfTG T Q' L v (hA • M)).1 := rfl
    rw [e2, e]
    show (hp v • locOfTG T Q' L v M).1 = _
    simp only [hp]
    split_ifs with heq
    · rw [one_smul]; exact heq
    · have := congrArg Subtype.val (hhv v)
      exact this

end ComponentsG

/-! ### Factorization of the type sum of a general lattice -/

section FactorG

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
  (Q₀' : QuadForm (𝓞 F) n') (hQ' : Q₀'.Nondegenerate) (L : Lat F (r + n'))

local notation "TF" => T₀.map (algebraMap (𝓞 F) F)
local notation "QF'" => Q₀'.map (algebraMap (𝓞 F) F)

open Classical in
/-- **The exceptional primes** of $(L, T_0)$: the primes of `frameBadSet` and those with $L_\mathfrak p \ne \mathfrak o_\mathfrak p^{r+n'}$ (finite). -/
def frameBadSetG : Finset (HeightOneSpectrum (𝓞 F)) :=
  frameBadSet T₀ hT ∪ (Filter.eventually_cofinite.mp (loc_eventually_std L.2)).toFinset

theorem not_mem_frameBadSetG {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ frameBadSetG T₀ hT L) :
    v ∉ frameBadSet T₀ hT ∧ loc v L.1 = std v := by
  simp [frameBadSetG] at hv
  exact hv

theorem finite_loc_ne_std : {v : HeightOneSpectrum (𝓞 F) | loc v L.1 ≠ std v}.Finite :=
  Filter.eventually_cofinite.mp (loc_eventually_std L.2)

local notation "S" => frameBadSetG T₀ hT L

include hQ' in
/-- At a prime outside $S$, every $M \in Y_\mathfrak p(L_\mathfrak p)$ is in the type of $L_\mathfrak p = \mathfrak o_\mathfrak p^{r+n'}$. -/
theorem exists_smul_of_not_memG {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (M M' : LocFrameSetG v TF QF' (loc v L.1)) : M' ∈ orbit (orthGroup QF' (v.adicCompletion F)) M := by
  obtain ⟨hv0, hL⟩ := not_mem_frameBadSetG T₀ hT L hv
  have key : ∀ N : LocFrameSetG v TF QF' (loc v L.1), ∃ h : orthGroup QF' (v.adicCompletion F),
      (h • locFrameStdPt v TF QF').1 = N.1 := by
    intro N
    obtain ⟨h, hh⟩ := exists_smul_locFrameStdPt T₀ hT Q₀' hQ' hv0 ⟨N.1, by rw [← hL]; exact N.2.1, N.2.2⟩
    exact ⟨h, congrArg Subtype.val hh⟩
  obtain ⟨h, hh⟩ := key M
  obtain ⟨h', hh'⟩ := key M'
  refine ⟨h' * h⁻¹, Subtype.ext ?_⟩
  show locAct v (orthEmbB TF QF' _ (h' * h⁻¹) : GL (Fin (r + n')) (v.adicCompletion F)) M.1 = M'.1
  rw [← hh, ← hh', LocFrameSet.smul_val, LocFrameSet.smul_val, ← locAct_mul, ← Subgroup.coe_mul, ← map_mul,
    inv_mul_cancel_right]

/-- **Global types to local types at the primes of $S$** (general $L$). -/
def typeMapTG : orbitRel.Quotient (OAf QF') (CompSetT TF QF' L) →
    ((v : S) → LocFrameTypesG v TF QF' (loc v L.1)) :=
  Quotient.lift (fun M v => Quotient.mk'' (locOfTG TF QF' L v M)) (fun a b hab => funext fun v => by
    exact Quotient.sound' ((mem_orbit_compSetT_iffG TF QF' L b a).mp hab v))

theorem typeMapTG_mk (M : CompSetT TF QF' L) (v : S) :
    typeMapTG T₀ hT Q₀' L (Quotient.mk'' M) v = Quotient.mk'' (locOfTG TF QF' L v M) := rfl

include hQ' in
theorem typeMapTG_injective : Function.Injective (typeMapTG T₀ hT Q₀' L) := by
  intro t t' h
  induction t using Quotient.inductionOn' with | h M => ?_
  induction t' using Quotient.inductionOn' with | h M' => ?_
  apply Quotient.sound'
  show M ∈ orbit (OAf QF') M'
  rw [mem_orbit_compSetT_iffG]
  intro v
  by_cases hv : v ∈ S
  · have := congrFun h ⟨v, hv⟩
    rw [typeMapTG_mk, typeMapTG_mk] at this
    exact Quotient.exact' this
  · exact exists_smul_of_not_memG T₀ hT Q₀' hQ' L hv _ _

open Classical in
/-- The local family glued from representatives of local types at the primes of $S$ (and $L_\mathfrak p$ elsewhere). -/
def glueFamTG (f : (v : S) → LocFrameTypesG v TF QF' (loc v L.1)) : LocFamily F (r + n') where
  M v := if hv : v ∈ S then (locFrameRepG v TF QF' (loc v L.1) (f ⟨v, hv⟩)).1 else loc v L.1
  isLattice v := by
    split_ifs with hv
    · obtain ⟨g, hg⟩ := (locFrameRepG v TF QF' (loc v L.1) (f ⟨v, hv⟩)).2.1
      rw [← hg]
      exact locAct_isLattice _ (loc_isLattice v L.2)
    · exact loc_isLattice v L.2
  eventually_std := by
    filter_upwards [(S).finite_toSet.compl_mem_cofinite] with v hv
    have hv' : v ∉ S := hv
    simp only [hv', ↓reduceDIte]
    exact (not_mem_frameBadSetG T₀ hT L hv').2

open Classical in
/-- **The glued lattice** with prescribed local types. -/
def glueCompTG (f : (v : S) → LocFrameTypesG v TF QF' (loc v L.1)) : CompSetT TF QF' L :=
  ⟨⟨(glueFamTG T₀ hT Q₀' L f).glue, (glueFamTG T₀ hT Q₀' L f).glue_isLattice⟩, by
      intro v
      rw [LocFamily.loc_glue]
      show ∃ g ∈ _, _ = if hv : v ∈ S then _ else _
      split_ifs with hv
      · obtain ⟨g, hg⟩ := (locFrameRepG v TF QF' (loc v L.1) (f ⟨v, hv⟩)).2.1
        exact ⟨g, g.2, hg⟩
      · exact ⟨1, (orthGroup _ _).one_mem, locAct_one _⟩,
    fun j => by
      rw [mem_iff_forall_loc (glueFamTG T₀ hT Q₀' L f).glue_isLattice]
      intro v
      rw [LocFamily.loc_glue, locVec_stdFrameCol]
      show _ ∈ if hv : v ∈ S then _ else _
      split_ifs with hv
      · exact (locFrameRepG v TF QF' (loc v L.1) (f ⟨v, hv⟩)).2.2 j
      · rw [(not_mem_frameBadSetG T₀ hT L hv).2]
        exact stdCol_mem_std v j⟩

theorem locOfTG_glueCompTG (f : (v : S) → LocFrameTypesG v TF QF' (loc v L.1)) (v : S) :
    locOfTG TF QF' L v (glueCompTG T₀ hT Q₀' L f) = locFrameRepG v TF QF' (loc v L.1) (f v) := by
  classical
  apply Subtype.ext
  rw [locOfTG_val]
  show loc (v : HeightOneSpectrum (𝓞 F)) (glueFamTG T₀ hT Q₀' L f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : (v : HeightOneSpectrum (𝓞 F)) ∈ S then _ else _) = _
  simp only [v.2, ↓reduceDIte]

theorem locOfTG_glueCompTG_of_not_mem (f : (v : S) → LocFrameTypesG v TF QF' (loc v L.1))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : (locOfTG TF QF' L v (glueCompTG T₀ hT Q₀' L f)).1 = std v := by
  classical
  rw [locOfTG_val]
  show loc v (glueFamTG T₀ hT Q₀' L f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : v ∈ S then _ else _) = _
  simp only [hv, ↓reduceDIte]
  exact (not_mem_frameBadSetG T₀ hT L hv).2

theorem typeMapTG_glueCompTG (f : (v : S) → LocFrameTypesG v TF QF' (loc v L.1)) :
    typeMapTG T₀ hT Q₀' L (Quotient.mk'' (glueCompTG T₀ hT Q₀' L f)) = f := by
  funext v
  rw [typeMapTG_mk, locOfTG_glueCompTG, locFrameRepG_mk]

include hQ' in
/-- **Global types = families of local types at the primes of $S$** (general $L$). -/
def typeEquivTG : orbitRel.Quotient (OAf QF') (CompSetT TF QF' L) ≃
    ((v : S) → LocFrameTypesG v TF QF' (loc v L.1)) :=
  Equiv.ofBijective _ ⟨typeMapTG_injective T₀ hT Q₀' hQ' L, fun f => ⟨_, typeMapTG_glueCompTG T₀ hT Q₀' L f⟩⟩

/-- **The global weight of a glued lattice is the product of the local weights.** -/
theorem compWeightT_glueCompTG (f : (v : S) → LocFrameTypesG v TF QF' (loc v L.1)) :
    compWeightT TF QF' L (glueCompTG T₀ hT Q₀' L f) =
      ∏ v : S, locFrameWeightG v TF QF' (loc v L.1) (locFrameRepG v TF QF' (loc v L.1) (f v)) := by
  classical
  set y := glueCompTG T₀ hT Q₀' L f
  set A' : (v : HeightOneSpectrum (𝓞 F)) → Subgroup (orthGroup QF' (v.adicCompletion F)) :=
    fun v => stabilizer (orthGroup QF' (v.adicCompletion F)) (locOfTG TF QF' L v y)
  have hA : ∀ v ∉ S, A' v = stdStab QF' v := by
    intro v hv
    simp only [A']
    ext h
    rw [mem_stabilizer_iff, ← mem_stdStab_orthEmbB_iff TF QF' v h]
    have e := locOfTG_glueCompTG_of_not_mem T₀ hT Q₀' L f hv
    constructor
    · intro hh
      have := congrArg Subtype.val hh
      rw [LocFrameSetG.smul_val, e] at this
      exact this
    · intro hh
      apply Subtype.ext
      rw [LocFrameSetG.smul_val, e]
      exact hh
  have hB : ∀ v ∉ S, stdStab QF' v = stdStab QF' v := fun _ _ => rfl
  have hAm : ∀ h, h ∈ stabilizer (OAf QF') y ↔ ∀ v, h v ∈ A' v := by
    intro h
    rw [stabilizer_compSetT, Subgroup.mem_comap]
    show (∀ v, _ = _) ↔ _
    refine forall_congr' fun v => ?_
    simp only [A', mem_stabilizer_iff]
    constructor
    · intro hh; exact Subtype.ext hh
    · intro hh; exact congrArg Subtype.val hh
  have hBm : ∀ h, h ∈ locStab QF' (stdLat F n') ↔ ∀ v, h v ∈ stdStab QF' v := mem_locStab_intVec QF'
  have e1 := relIndex_restrictedPi S A' (fun v => stdStab QF' v) hA hB _ _ hAm hBm
  have e2 := relIndex_restrictedPi S (fun v => stdStab QF' v) A' hB hA _ _ hBm hAm
  unfold compWeightT
  rw [e1, e2, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [A', locFrameWeightG]
  rw [locOfTG_glueCompTG]

end FactorG

/-- **One local type of weight $1$ at the good primes** (cf. O'Meara 1963, §92): if $\Lambda = \mathfrak o_\mathfrak p^{r+n'}$ and
$\mathfrak p \notin S$ (`frameBadSet`), $W_\mathfrak p(\Lambda) = 1$ (`locFrameTypeSum_eq_one`). -/
theorem locFrameTypeSumG_eq_one_of_eq_std {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T₀ : QuadForm (𝓞 F) r)
    (hT : T₀.Nondegenerate) (Q₀' : QuadForm (𝓞 F) n') (hQ' : Q₀'.Nondegenerate)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ frameBadSet T₀ hT)
    {Λ : Submodule (v.adicCompletionIntegers F) (Fin (r + n') → v.adicCompletion F)} (hΛ : Λ = std v) :
    locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) Λ = 1 := by
  subst hΛ
  rw [locFrameTypeSumG_std]
  exact locFrameTypeSum_eq_one T₀ hT Q₀' hQ' hv

/-- **The local factor is $1$ at the good primes:** if $L_\mathfrak p = \mathfrak o_\mathfrak p^{r+n'}$ and $\mathfrak p \notin S$ (`frameBadSet`), then
$W_\mathfrak p(L_\mathfrak p) = 1$. -/
theorem locFrameTypeSumG_eq_one_of_good {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T₀ : QuadForm (𝓞 F) r)
    (hT : T₀.Nondegenerate) (Q₀' : QuadForm (𝓞 F) n') (hQ' : Q₀'.Nondegenerate) (L : Lat F (r + n'))
    {v : HeightOneSpectrum (𝓞 F)} (hL : loc v L.1 = std v) (hv : v ∉ frameBadSet T₀ hT) :
    locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (loc v L.1) = 1 :=
  locFrameTypeSumG_eq_one_of_eq_std T₀ hT Q₀' hQ' hv hL

/-- **The type sum of an arbitrary lattice factors over the primes** (Weil 1982, §3.5 [unverified locator]): for $T_0\perp Q_0'$ totally
positive definite and $L$ integral for it,
$$\sum_{t\in O(Q')(\mathbb A_f)\backslash Y} w(t) = \prod_\mathfrak p W_\mathfrak p(L_\mathfrak p),\qquad
  Y = \{M \in \mathrm{gen}(L) : E \subseteq M\},$$
where the product has finite support (only the primes of `frameBadSetG` contribute) and $W_\mathfrak p$ = `locFrameTypeSumG`. -/
@[kb "weil1982" "§3.5 (type sum as a product of local sums, general lattice) [unverified locator]"]
theorem typeSumT_eq_finprod_gen {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T₀ : QuadForm (𝓞 F) r)
    (hT : T₀.Nondegenerate) (Q₀' : QuadForm (𝓞 F) n') (L : Lat F (r + n'))
    (hpd : IsTotallyPosDef ((blockForm T₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral (blockForm (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F))) L.1) :
    ∑ᶠ t : orbitRel.Quotient (OAf (Q₀'.map (algebraMap (𝓞 F) F)))
        (CompSetT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) L),
      typeWeightT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) L t =
    ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (loc v L.1) := by
  classical
  have hpd₀ : IsTotallyPosDef (blockForm (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F))) := by
    have := hpd
    rw [map_blockForm] at this
    exact this
  have hpd' := isTotallyPosDef_of_blockForm_right hpd₀
  have hLi' : IsIntegral (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F n').1 := isIntegral_stdLat_map _
  have hQ' : Q₀'.Nondegenerate := (nondeg_map_alg Q₀').mpr hpd'.nondegenerate
  have hfin := finite_typesT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) L
    hpd₀ hLi ((nondeg_map_alg T₀).mp hT)
  -- the finprod is a product over S
  have hsub : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (loc v L.1)) ⊆
        ↑(frameBadSetG T₀ hT L) := by
    intro v hv
    by_contra hvS
    obtain ⟨hv0, hL⟩ := not_mem_frameBadSetG T₀ hT L (by simpa using hvS)
    exact hv (locFrameTypeSumG_eq_one_of_good T₀ hT Q₀' hQ' L hL hv0)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  by_cases hall : ∀ w : frameBadSetG T₀ hT L, Nonempty (LocFrameTypesG w (T₀.map (algebraMap (𝓞 F) F))
      (Q₀'.map (algebraMap (𝓞 F) F)) (loc w L.1))
  swap
  · push_neg at hall
    obtain ⟨w₀, hw₀⟩ := hall
    have hR : ∏ v ∈ frameBadSetG T₀ hT L, locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F))
        (Q₀'.map (algebraMap (𝓞 F) F)) (loc v L.1) = 0 := by
      refine Finset.prod_eq_zero w₀.2 ?_
      rw [locFrameTypeSumG, finsum_of_isEmpty]
    have hE : IsEmpty (orbitRel.Quotient (OAf (Q₀'.map (algebraMap (𝓞 F) F)))
        (CompSetT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) L)) :=
      ⟨fun t => hw₀.false (typeMapTG T₀ hT Q₀' L t w₀)⟩
    rw [hR, finsum_of_isEmpty]
  have hfinP : Finite ((v : frameBadSetG T₀ hT L) → LocFrameTypesG v (T₀.map (algebraMap (𝓞 F) F))
      (Q₀'.map (algebraMap (𝓞 F) F)) (loc v L.1)) := Finite.of_equiv _ (typeEquivTG T₀ hT Q₀' hQ' L)
  have hfinv : ∀ v : frameBadSetG T₀ hT L, Finite (LocFrameTypesG v (T₀.map (algebraMap (𝓞 F) F))
      (Q₀'.map (algebraMap (𝓞 F) F)) (loc v L.1)) := by
    intro v
    let f₀ : (w : frameBadSetG T₀ hT L) → LocFrameTypesG w (T₀.map (algebraMap (𝓞 F) F))
      (Q₀'.map (algebraMap (𝓞 F) F)) (loc w L.1) := fun w => Classical.choice (hall w)
    exact Finite.of_injective (fun x => Function.update f₀ v x) (Function.update_injective f₀ v)
  let _ : Fintype (orbitRel.Quotient (OAf (Q₀'.map (algebraMap (𝓞 F) F)))
    (CompSetT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) L)) :=
    Fintype.ofFinite _
  let _ : ∀ v : frameBadSetG T₀ hT L, Fintype (LocFrameTypesG v (T₀.map (algebraMap (𝓞 F) F))
    (Q₀'.map (algebraMap (𝓞 F) F)) (loc v L.1)) := fun v => Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have step : ∀ t, typeWeightT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) L t =
      compWeightT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) L
        (glueCompTG T₀ hT Q₀' L (typeEquivTG T₀ hT Q₀' hQ' L t)) := by
    intro t
    rw [typeWeightT_eq_compWeightT]
    refine compWeightT_of_mem_orbit _ _ _ hpd' hLi' ?_
    have h1 : (Quotient.mk'' (glueCompTG T₀ hT Q₀' L (typeEquivTG T₀ hT Q₀' hQ' L t)) :
        orbitRel.Quotient (OAf (Q₀'.map (algebraMap (𝓞 F) F)))
          (CompSetT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) L)) = t :=
      typeMapTG_injective T₀ hT Q₀' hQ' L (typeMapTG_glueCompTG T₀ hT Q₀' L _)
    have h2 : (Quotient.mk'' t.out : orbitRel.Quotient (OAf (Q₀'.map (algebraMap (𝓞 F) F)))
          (CompSetT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) L)) =
        Quotient.mk'' (glueCompTG T₀ hT Q₀' L (typeEquivTG T₀ hT Q₀' hQ' L t)) := by
      rw [h1, Quotient.out_eq']
    exact Quotient.exact' h2
  rw [Finset.sum_congr rfl fun t _ => step t,
    Equiv.sum_comp (typeEquivTG T₀ hT Q₀' hQ' L) (fun f => compWeightT (T₀.map (algebraMap (𝓞 F) F))
      (Q₀'.map (algebraMap (𝓞 F) F)) L (glueCompTG T₀ hT Q₀' L f))]
  simp_rw [compWeightT_glueCompTG]
  rw [← Finset.prod_coe_sort (frameBadSetG T₀ hT L)]
  simp_rw [locFrameTypeSumG, finsum_eq_sum_of_fintype]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end QuadFormsKB.Tamagawa.Frames
