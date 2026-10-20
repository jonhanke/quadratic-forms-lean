/-
# Lattices over $\mathcal O_F$: the class set as a double coset space

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$ (`Lattices/Genus.lean`). This generalizes the AWS
notes' D15–D16 (`AWS/Adelic.lean`, for $F = \mathbb Q$) to every number field, and **proves** the gluing input
there (Lemma 4.5.1, `AWS.LatticeGluing`), here `LocFamily.loc_glue`.

**Defines**
* `stdStab Q v` $= O(V)(\mathfrak o_\mathfrak p)$, the stabilizer of $\mathfrak o_\mathfrak p^n$ in $O(V)(F_\mathfrak p)$;
* `OAf Q` $= O(V)(\mathbb A_f)$: the restricted product $\prod'_\mathfrak p O(V)(F_\mathfrak p)$ with respect to the
  $O(V)(\mathfrak o_\mathfrak p)$ (Mathlib's `RestrictedProduct`), with the diagonal embedding
  `diagF : O(V)(F) →* O(V)(𝔸_f)` and the rational points `ratPoints Q`;
* the action of $O(V)(\mathbb A_f)$ on lattices (`latAction`): $h \cdot L$ is the lattice with localizations
  $h_\mathfrak p L_\mathfrak p$ (it exists and is unique by gluing);
* `locStab Q L` $= O(\hat L) = \{h : h_\mathfrak p L_\mathfrak p = L_\mathfrak p\ \forall \mathfrak p\}$.

**Proves**
* `diagF_smul`: a rational $\gamma$ acts by $L \mapsto \gamma L$;
* `orbit_eq_genus` (AWS Lemma 4.5.2 over $F$): the $O(V)(\mathbb A_f)$-orbit of $L$ is its genus;
* `stabilizer_eq_locStab`: $\mathrm{Stab}(L) = O(\hat L)$;
* `classRel_iff`: two lattices in the genus are in the same $O(V)(F)$-orbit iff they are isometric;
* `dosetEquivClassesInGenus` (AWS D16 over $F$):
  $O(V)(F)\backslash O(V)(\mathbb A_f)/O(\hat L) \simeq \{\text{classes in } \mathrm{gen}(L)\}$;
* `card_autLat_eq` ((4.11) of the AWS notes over $F$): $|O(V)(F) \cap \alpha O(\hat L)\alpha^{-1}| = |O(\alpha L)|$.
-/
import QuadFormsKB.Lattices.Genus
import QuadFormsKB.Literature.AWS.DoubleCosets

open NumberField IsDedekindDomain Matrix
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- **Lattices in $F^n$:** finitely generated $\mathcal O_F$-submodules spanning $F^n$ (not necessarily free). -/
abbrev Lat (F : Type*) [Field F] [NumberField F] (n : ℕ) : Type _ :=
  {L : Submodule (𝓞 F) (Fin n → F) // L.IsLattice F}

theorem Lat.ext {L M : Lat F n} (h : L.1 = M.1) : L = M := Subtype.ext h

/-- **The family of localizations** of a lattice. -/
abbrev Lat.locFamily (L : Lat F n) : LocFamily F n := Lattices.locFamily L.2

variable (Q : QuadForm F n)

/-! ### The finite adelic orthogonal group -/

/-- **The local stabilizer** $O(V)(\mathfrak o_\mathfrak p) = \{g \in O(V)(F_\mathfrak p) : g\,\mathfrak o_\mathfrak p^n = \mathfrak o_\mathfrak p^n\}$. -/
@[kb "hanke2011aws" "§4.2, p. 56 (over F)"]
def stdStab (v : HeightOneSpectrum (𝓞 F)) : Subgroup (orthGroup Q (v.adicCompletion F)) where
  carrier := {g | locAct v (g : GL (Fin n) (v.adicCompletion F)) (std v) = std v}
  mul_mem' {a b} ha hb := by
    change locAct v (((a * b : orthGroup Q _)) : GL (Fin n) _) (std v) = std v
    rw [Subgroup.coe_mul, locAct_mul, show locAct v (b : GL (Fin n) _) (std v) = std v from hb]
    exact ha
  one_mem' := locAct_one _
  inv_mem' {a} ha := by
    change locAct v (((a⁻¹ : orthGroup Q _)) : GL (Fin n) _) (std v) = std v
    rw [Subgroup.coe_inv, locAct_eq_iff, inv_inv]
    exact (show locAct v (a : GL (Fin n) _) (std v) = std v from ha).symm

/-- **The finite adelic orthogonal group** $O(V)(\mathbb A_f) = \prod'_\mathfrak p O(V)(F_\mathfrak p)$, restricted with
respect to the $O(V)(\mathfrak o_\mathfrak p)$ (for $F = \mathbb Q$: `AWS.OAf`). -/
@[kb "hanke2011aws" "§4.2, p. 56 (over F)"]
abbrev OAf : Type _ :=
  Πʳ v : HeightOneSpectrum (𝓞 F), [orthGroup Q (v.adicCompletion F), stdStab Q v]

/-- **The diagonal embedding** $O(V)(F) \to O(V)(\mathbb A_f)$, $\gamma \mapsto (\gamma)_\mathfrak p$ (a rational
isometry stabilizes $\mathfrak o_\mathfrak p^n$ for almost all $\mathfrak p$, `eventually_locAct_std`). -/
def diagF : orthGroup Q F →* OAf Q where
  toFun γ := ⟨fun v => orthMap Q (v.adicCompletion F) γ, by
    filter_upwards [eventually_locAct_std (γ : GL (Fin n) F)] with v hv
    exact hv⟩
  map_one' := by ext v : 1; exact map_one (orthMap Q _)
  map_mul' a b := by ext v : 1; exact map_mul (orthMap Q _) a b

/-- **The rational points** $O(V)(F) \le O(V)(\mathbb A_f)$, embedded diagonally. -/
abbrev ratPoints : Subgroup (OAf Q) := (diagF Q).range

/-! ### The action on lattices -/

/-- The local lattices $(h_\mathfrak p L_\mathfrak p)_\mathfrak p$ for $h \in O(V)(\mathbb A_f)$ (almost all standard). -/
def smulFamily (h : OAf Q) (L : Lat F n) : LocFamily F n where
  M v := locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (loc v L.1)
  isLattice v := locAct_isLattice _ (loc_isLattice v L.2)
  eventually_std := by
    filter_upwards [h.2, loc_eventually_std L.2] with v hv hL
    rw [hL]; exact hv

/-- **$h \cdot L$** for $h \in O(V)(\mathbb A_f)$: the lattice glued from $(h_\mathfrak p L_\mathfrak p)_\mathfrak p$
(AWS notes pp. 61–62 for $F = \mathbb Q$). -/
@[kb "hanke2011aws" "§4.5, pp. 61-62 (over F)"]
def latSMul (h : OAf Q) (L : Lat F n) : Lat F n :=
  ⟨(smulFamily Q h L).glue, (smulFamily Q h L).glue_isLattice⟩

theorem loc_latSMul (h : OAf Q) (L : Lat F n) (v : HeightOneSpectrum (𝓞 F)) :
    loc v (latSMul Q h L).1 = locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (loc v L.1) :=
  (smulFamily Q h L).loc_glue v

/-- **$O(V)(\mathbb A_f)$ acts on lattices in $V$.** -/
@[instance_reducible]
def latAction : MulAction (OAf Q) (Lat F n) where
  smul := latSMul Q
  one_smul L := Lat.ext <| loc_injective (latSMul Q 1 L).2 L.2 fun v => by
    change loc v (latSMul Q 1 L).1 = _
    rw [loc_latSMul]; exact locAct_one _
  mul_smul a b L := Lat.ext <| loc_injective (latSMul Q (a * b) L).2 (latSMul Q a (latSMul Q b L)).2
    fun v => by
      change loc v (latSMul Q (a * b) L).1 = loc v (latSMul Q a (latSMul Q b L)).1
      rw [loc_latSMul, loc_latSMul, loc_latSMul]
      exact locAct_mul _ _ _

/-- **The image $\gamma L$ as a lattice.** -/
def Lat.image (γ : GL (Fin n) F) (L : Lat F n) : Lat F n := ⟨glImage γ L.1, glImage_isLattice γ L.2⟩

/-- **A rational isometry acts by $L \mapsto \gamma L$** (AWS notes p. 62 for $F = \mathbb Q$, `AWS.diag_smul`). -/
@[kb "hanke2011aws" "§4.5, p. 62 (over F)"]
theorem diagF_smul (γ : orthGroup Q F) (L : Lat F n) :
    latSMul Q (diagF Q γ) L = Lat.image (γ : GL (Fin n) F) L := by
  apply Lat.ext
  apply loc_injective (latSMul Q _ L).2 (Lat.image _ L).2
  intro v
  rw [loc_latSMul, Lat.image, loc_glImage]
  rfl

/-! ### Genus and stabilizers -/

/-- **The genus of $L$** as a set of lattices: the $M$ with `SameGenus Q L M`. -/
def latGenus (L : Lat F n) : Set (Lat F n) := {M | SameGenus Q L.1 M.1}

/-- **AWS Lemma 4.5.2 over $F$: the orbit of $L$ under $O(V)(\mathbb A_f)$ is the genus of $L$.** For the converse
inclusion take $h_\mathfrak p$ carrying $L_\mathfrak p$ to $M_\mathfrak p$ where $L_\mathfrak p \ne M_\mathfrak p$ (finitely many
$\mathfrak p$), and $h_\mathfrak p = 1$ elsewhere. -/
@[kb "hanke2011aws" "§4.5, Lemma 4.5.2, p. 62 (over F)"]
theorem orbit_eq_genus (L : Lat F n) :
    @MulAction.orbit (OAf Q) (Lat F n) (latAction Q).toSMul L = latGenus Q L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  ext M
  constructor
  · rintro ⟨h, rfl⟩ v
    exact ⟨h v, (h v).2, (loc_latSMul Q h L v).symm⟩
  · intro hM
    classical
    choose k hk hk' using hM
    let hp : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q (v.adicCompletion F) := fun v =>
      if loc v L.1 = loc v M.1 then 1 else ⟨k v, hk v⟩
    have hpspec : ∀ v, locAct v ((hp v : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v M.1 := by
      intro v
      simp only [hp]
      split_ifs with he
      · rw [← he]; exact locAct_one _
      · exact hk' v
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hp v ∈ stdStab Q v := by
      filter_upwards [loc_eventually_std L.2, loc_eventually_std M.2] with v h1 h2
      have : loc v L.1 = loc v M.1 := h1.trans h2.symm
      simp only [hp, this, ↓reduceIte]
      exact (stdStab Q v).one_mem
    let hA : OAf Q := ⟨hp, hev⟩
    refine ⟨hA, Lat.ext (loc_injective (latSMul Q hA L).2 M.2 fun v => ?_)⟩
    change loc v (latSMul Q hA L).1 = _
    rw [loc_latSMul]
    exact hpspec v

/-- **The adelic stabilizer** $O(\hat L) = \{h \in O(V)(\mathbb A_f) : h_\mathfrak p L_\mathfrak p = L_\mathfrak p\ \forall \mathfrak p\}
= \prod_\mathfrak p O(L_\mathfrak p)$ (for $L = \mathcal O_F^n$: $\prod_\mathfrak p O(V)(\mathfrak o_\mathfrak p)$). -/
@[kb "hanke2011aws" "§4.5, p. 62 (over F)"]
def locStab (L : Lat F n) : Subgroup (OAf Q) where
  carrier := {h | ∀ v, locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v L.1}
  mul_mem' {a b} ha hb v := by
    change locAct v (((a v * b v : orthGroup Q _)) : GL (Fin n) _) _ = _
    rw [Subgroup.coe_mul, locAct_mul, hb v, ha v]
  one_mem' v := locAct_one _
  inv_mem' {a} ha v := by
    change locAct v (((a v)⁻¹ : orthGroup Q _) : GL (Fin n) _) _ = _
    rw [Subgroup.coe_inv, locAct_eq_iff, inv_inv]
    exact (ha v).symm

/-- **$\mathrm{Stab}_{O(V)(\mathbb A_f)}(L) = O(\hat L)$** (AWS notes p. 62 for $F = \mathbb Q$, `AWS.stabilizer_std`). -/
@[kb "hanke2011aws" "§4.5, p. 62 (over F)"]
theorem stabilizer_eq_locStab (L : Lat F n) :
    @MulAction.stabilizer (OAf Q) (Lat F n) _ (latAction Q) L = locStab Q L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  ext h
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hh v
    have := congrArg (fun M : Lat F n => loc v M.1) hh
    change loc v (latSMul Q h L).1 = _ at this
    rwa [loc_latSMul] at this
  · intro hh
    refine Lat.ext (loc_injective (latSMul Q h L).2 L.2 fun v => ?_)
    change loc v (latSMul Q h L).1 = _
    rw [loc_latSMul]; exact hh v

/-- **$O(\hat{\mathcal O}_F^n) = \prod_\mathfrak p O(V)(\mathfrak o_\mathfrak p)$.** -/
theorem mem_locStab_intVec (h : OAf Q) :
    h ∈ locStab Q ⟨intVec, intVec_isLattice⟩ ↔ ∀ v, h v ∈ stdStab Q v := by
  change (∀ v, locAct v _ (loc v intVec) = loc v intVec) ↔ _
  simp only [loc_intVec]; rfl

/-! ### Classes in the genus as double cosets -/

/-- **The class relation:** two lattices in the genus of $L$ lie in the same $O(V)(F)$-orbit iff they are isometric
(`IsIsometric`). -/
theorem classRel_iff (L : Lat F n) (M M' : @MulAction.orbit (OAf Q) (Lat F n) (latAction Q).toSMul L) :
    (@AWS.classSetoid (OAf Q) (Lat F n) _ (latAction Q) (ratPoints Q) L) M M' ↔
      IsIsometric Q (M : Lat F n).1 (M' : Lat F n).1 := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  constructor
  · rintro ⟨_, ⟨γ, rfl⟩, hγ⟩
    refine ⟨γ, γ.2, ?_⟩
    have : latSMul Q (diagF Q γ) M = M' := hγ
    rw [diagF_smul] at this
    exact congrArg Subtype.val this
  · rintro ⟨γ, hγ, he⟩
    refine ⟨diagF Q ⟨γ, hγ⟩, ⟨⟨γ, hγ⟩, rfl⟩, ?_⟩
    change latSMul Q (diagF Q ⟨γ, hγ⟩) M = M'
    rw [diagF_smul]
    exact Lat.ext he

/-- **The class set as a double coset space (AWS D16 over $F$):**
$$O(V)(F)\backslash O(V)(\mathbb A_f)/O(\hat L) \;\simeq\; \{\text{classes in } \mathrm{gen}(L)\},$$
where the classes in the genus are the $O(V)(F)$-orbits on the genus `latGenus Q L` (`orbit_eq_genus`), i.e. the
isometry classes of lattices in the genus (`classRel_iff`). Unconditional: the gluing input of the $\mathbb Q$ version
is proved here (`LocFamily.loc_glue`). -/
@[kb "hanke2011aws" "§4.5, p. 62 (over F)"]
def dosetEquivClassesInGenus (L : Lat F n) :
    DoubleCoset.Quotient (ratPoints Q : Set (OAf Q)) (locStab Q L) ≃
      @AWS.ClassesInGenus (OAf Q) (Lat F n) _ (latAction Q) (ratPoints Q) L := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  rw [← stabilizer_eq_locStab Q L]
  exact AWS.dosetEquivClasses (ratPoints Q) L

omit Q in
/-- A number field has a finite prime ($\mathcal O_F$ is not a field). -/
instance nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨p, hp, hpr⟩ := Ring.not_isField_iff_exists_prime.mp (RingOfIntegers.not_isField F)
  exact ⟨⟨p, hpr, hp⟩⟩

/-- `diagF` is injective. -/
theorem diagF_injective : Function.Injective (diagF Q) := by
  intro a b h
  obtain ⟨v⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
  have h1 : (a : GL (Fin n) F).val.map (algebraMap F (v.adicCompletion F)) =
      (b : GL (Fin n) F).val.map (algebraMap F (v.adicCompletion F)) :=
    congrArg (fun x : OAf Q =>
      ((x v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)).val) h
  apply Subtype.ext; apply Units.ext
  ext i j
  exact (algebraMap F (v.adicCompletion F)).injective (congrFun (congrFun h1 i) j)

/-- **The automorphism group of $\alpha L$ ((4.11) of the AWS notes over $F$):** for $\alpha \in O(V)(\mathbb A_f)$, the
rational points of $\alpha\,O(\hat L)\,\alpha^{-1}$ are in bijection with $O(\alpha L)$. -/
@[kb "hanke2011aws" "§4.6, (4.11), p. 64 (over F)"]
theorem card_autLat_eq (α : OAf Q) (L : Lat F n) :
    Nat.card (ratPoints Q ⊓ AWS.conjSub α (locStab Q L) : Subgroup (OAf Q)) =
      Nat.card (autLat Q (latSMul Q α L).1) := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  rw [← stabilizer_eq_locStab Q L, ← AWS.stabilizer_smul]
  symm
  refine Nat.card_congr
    { toFun := fun γ => ⟨diagF Q γ.1, ⟨⟨γ.1, rfl⟩, ?_⟩⟩
      invFun := fun h => ⟨h.2.1.choose, ?_⟩
      left_inv := fun γ => ?_
      right_inv := fun h => ?_ }
  · refine MulAction.mem_stabilizer_iff.mpr ?_
    change latSMul Q (diagF Q γ.1) _ = _
    rw [diagF_smul]
    exact Lat.ext γ.2
  · show glImage _ _ = _
    have h2 := MulAction.mem_stabilizer_iff.mp h.2.2
    rw [← h.2.1.choose_spec] at h2
    change latSMul Q (diagF Q h.2.1.choose) _ = _ at h2
    rw [diagF_smul] at h2
    exact congrArg Subtype.val h2
  · apply Subtype.ext
    apply diagF_injective Q
    exact (⟨γ.1, rfl⟩ : diagF Q γ.1 ∈ (diagF Q).range).choose_spec
  · apply Subtype.ext
    exact h.2.1.choose_spec

end QuadFormsKB.Lattices
