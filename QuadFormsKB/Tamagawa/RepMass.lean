/-
# The weighted representation number and its reduction to complements

**Layer:** lattices in $(F^n, Q)$ over a totally real number field $F$ (`Lattices/`), the finite adelic orthogonal
group (`Lattices/ClassSet.lean`), and the split form $Q = \langle m\rangle \perp Q'$ (`Tamagawa/SplitForm.lean`).

**Defines**
* `repCount Q M m` $= r_M(m) = \#\{v \in M : Q(v) = m\}$, and its value on a class (`LatClass.repCount`);
* `repMass Q L m` $= \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)} r_M(m)/|O(M)|$, the **weighted representation number**
  of the genus. Siegel's genus average is $r_{\mathrm{gen}}(L, m) = \mathrm{repMass}/\mathrm{Mass}$.
* For $Q = \langle m\rangle \perp Q'$ and $L$ in $(F^{n+1}, Q)$: `CompSet` $= Y = \{M \in \mathrm{gen}(L) : e_0 \in M\}$, acted on by
  $O(Q')(\mathbb A_f)$ through $\mathrm{diag}(1, \cdot)$, and `typeWeight` $w(t) = \mu(K_0')/\mu(K_t)$ for an orbit
  ("local type") $t$ with stabilizer $K_t$, $K_0' = O(\hat{\mathcal O}_F^n)$ (a ratio of indices).

**Proves**
* `finite_repSet`: $r_M(m) < \infty$ (totally positive definite $Q$, integral $M$);
* `repMass_eq_finsum_dcMass` (**the global reduction**, Weil's orbit counting; Weil 1982, §3.4–3.5 [unverified locator];
  Kitaoka 1993, §6.8 [unverified]): for $Q = \langle m\rangle\perp Q'$ nondegenerate, $m \ne 0$,
  $$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|}
    = \sum_{t \in O(Q')(\mathbb A_f)\backslash Y}\mathrm{dcMass}\big(O(Q')(F), K_t\big).$$
  *Proof:* pairs $(M, v)$, $v \in M$, $Q(v) = m$, under $O(Q)(F)$ (`orbitMass_eq_finsum_fiber`); by Witt's theorem
  $O(Q)(F)$ is transitive on $\{Q(v) = m\}$, so the pairs reduce to $Y$ under the stabilizer of $e_0$, which is $O(Q')(F)$
  (`orbitMass_eq_fiber_of_transitive`, `exists_orthEmb_eq`); then decompose by the orbits of $O(Q')(\mathbb A_f)$
  (`orbitMass_eq_finsum_dcMass`).
* `repMass_eq_mass_mul` (**complements' masses**): the same, with each double-coset mass expressed by the mass of the
  complement genus $\mathrm{gen}(\mathcal O_F^n, Q')$:
  $$\sum_{\mathrm{cls}(M)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^n, Q')\cdot\sum_{t}w(t),\qquad
    w(t) = \frac{\mu(K_0')}{\mu(K_t)} = \frac{[K_0' : K_0'\cap K_t]}{[K_t : K_0'\cap K_t]}.$$
  All lattices $M \cap e_0^\perp$ live in the one space $(F^n, Q')$, so one mass suffices; the local types enter only
  through the volumes $\mu(K_t)$ (`dcMass_mul_idxVol`, `commensurable_locStab`). Siegel's version
  $r_{\mathrm{gen}}(L,m)\,\mathrm{Mass}(L) = \sum_{\mathcal G} c_{\mathcal G}\mathrm{Mass}(\mathcal G)$ over genera $\mathcal G$ of
  complements is this identity grouped by genera (each genus of $Q'$-lattices has mass $\mathrm{Mass}(\mathcal O_F^n)\,
  \mu(K_0')/\mu(K_{\mathcal G})$).
-/
import QuadFormsKB.Tamagawa.OrbitDecomp
import QuadFormsKB.Tamagawa.SplitForm
import QuadFormsKB.Tamagawa.LatticeStab

open NumberField IsDedekindDomain Matrix MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices

/-! ### Representation numbers of lattices -/

section RepCount

variable {F : Type*} [Field F] [NumberField F] {N : ℕ} (Q : QuadForm F N)

/-- **The representation number** $r_M(m) = \#\{v \in M : Q(v) = m\}$ of $m \in F$ by the lattice $M$ (a `Nat.card`;
finite for totally positive definite $Q$ and integral $M$, `finite_repSet`). -/
@[kb "omeara1963" "§82A, p. 220"]
def repCount (M : Lat F N) (m : F) : ℕ := Nat.card {v : Fin N → F // v ∈ M.1 ∧ Q.eval v = m}

theorem eval_mulVec_of_mem {γ : GL (Fin N) F} (hγ : γ ∈ orthGroup Q F) (v : Fin N → F) :
    Q.eval (γ.val *ᵥ v) = Q.eval v :=
  evalIn_mulVec_of_mem Q hγ v

/-- **Isometric lattices represent $m$ equally often:** $r_{\gamma M}(m) = r_M(m)$ for $\gamma \in O(V)(F)$. -/
theorem repCount_glImage {γ : GL (Fin N) F} (hγ : γ ∈ orthGroup Q F) (M : Lat F N) (m : F) :
    repCount Q (Lat.image γ M) m = repCount Q M m := by
  refine Nat.card_congr
    { toFun := fun v => ⟨γ⁻¹.val *ᵥ v.1, ?_, ?_⟩
      invFun := fun v => ⟨γ.val *ᵥ v.1, ?_, ?_⟩
      left_inv := fun v => Subtype.ext (by simp [mulVec_mulVec])
      right_inv := fun v => Subtype.ext (by simp [mulVec_mulVec]) }
  · obtain ⟨y, hy, hyv⟩ := (mem_glImage).mp v.2.1
    rw [← hyv, mulVec_mulVec, Units.inv_mul, one_mulVec]; exact hy
  · rw [eval_mulVec_of_mem Q ((orthGroup Q F).inv_mem hγ)]; exact v.2.2
  · exact mulVec_mem_glImage v.2.1
  · rw [eval_mulVec_of_mem Q hγ]; exact v.2.2

theorem repCount_of_isIsometric {M M' : Lat F N} (h : IsIsometric Q M.1 M'.1) (m : F) :
    repCount Q M m = repCount Q M' m := by
  obtain ⟨γ, hγ, he⟩ := h
  rw [← repCount_glImage Q hγ M m]
  congr 1
  exact Lattices.Lat.ext he

/-- **$r_M(m)$ of a class** (well defined by `repCount_of_isIsometric`). -/
def LatClass.repCount (c : LatClass Q) (m : F) : ℕ :=
  Quotient.lift (fun M : Lat F N => Tamagawa.repCount Q M m) (fun _ _ h => repCount_of_isIsometric Q h m) c

/-- **The weighted representation number of the genus of $L$:**
$$\mathrm{repMass}(L, m) = \sum_{\mathrm{cls}(M) \subseteq \mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|},$$
a `finsum` over the classes in the genus, $O(M)$ including improper automorphisms (the library's convention).
Siegel's genus
average is $r_{\mathrm{gen}}(L, m) = \mathrm{repMass}(L,m)/\mathrm{Mass}(L)$ (Siegel 1935 [unverified]; for
$F = \mathbb Q$ and forms, `Siegel.genusRepAvg`). -/
@[kb "siegel1935" "§1 (genus average) [unverified]"]
def repMass (L : Lat F N) (m : F) : ℝ :=
  ∑ᶠ c ∈ genusClasses Q L, (LatClass.repCount Q c m : ℝ) / LatClass.autCard Q c

/-- **Finitely many representations:** for totally positive definite $Q$ and an integral lattice $M$,
$\{v \in M : Q(v) = m\}$ is finite (its vectors have trace form $\mathrm{Tr}(2m)$ in a $\mathbb Z$-frame). -/
theorem finite_repSet {Q : QuadForm F N} (hQ : IsTotallyPosDef Q) {M : Submodule (𝓞 F) (Fin N → F)}
    (hM : M.IsLattice F) (hMi : IsIntegral Q M) (m : F) :
    Finite {v : Fin N → F // v ∈ M ∧ Q.eval v = m} := by
  classical
  have := zLat_isLattice hM
  set b := frame hM
  set G := gram Q b
  let f : {v : Fin N → F // v ∈ M ∧ Q.eval v = m} → (Fin (zrank F N) → ℤ) := fun v =>
    b.repr ⟨v.1, v.2.1⟩
  have hf : ∀ v, ((f v ⬝ᵥ (G *ᵥ f v) : ℤ) : ℚ) = Algebra.trace ℚ F (2 * m) := by
    intro v
    rw [dotProduct_gram Q hMi b (f v)]
    have h2 : ∑ i, f v i • (b i : Fin N → F) = v.1 := (coe_eq_sum b ⟨v.1, v.2.1⟩).symm
    rw [h2, trForm_apply, bil_self, v.2.2]
  set T : ℤ := ⌈(Algebra.trace ℚ F (2 * m) : ℚ)⌉
  have hS := finite_short_vectors (gram_isPosDefInt hQ hMi b) T
  have := hS.to_subtype
  refine Finite.of_injective (fun v => (⟨f v, ?_⟩ : {y : Fin (zrank F N) → ℤ | y ⬝ᵥ (G *ᵥ y) ≤ T})) ?_
  · show f v ⬝ᵥ (G *ᵥ f v) ≤ T
    have h1 := hf v
    have : ((f v ⬝ᵥ (G *ᵥ f v) : ℤ) : ℚ) ≤ T := by rw [h1]; exact Int.le_ceil _
    exact_mod_cast this
  · intro v w h
    have h' : f v = f w := congrArg Subtype.val h
    apply Subtype.ext
    have e1 := coe_eq_sum b ⟨v.1, v.2.1⟩
    have e2 := coe_eq_sum b ⟨w.1, w.2.1⟩
    simp only at e1 e2
    rw [e1, e2]
    simp only [f] at h'
    rw [h']

end RepCount

/-! ### Rational isometries acting on lattices, vectors and pairs -/

section Pairs

variable {F : Type*} [Field F] [NumberField F] {N : ℕ} (Q : QuadForm F N)

/-- **$O(V)(F)$ acts on lattices** by $\gamma\cdot M = \gamma M$ (`Lat.image`). -/
@[instance_reducible]
def ratAct : MulAction (orthGroup Q F) (Lat F N) where
  smul γ M := Lat.image (γ : GL (Fin N) F) M
  one_smul M := Lattices.Lat.ext (glImage_one M.1)
  mul_smul _ _ M := Lattices.Lat.ext (glImage_mul _ _ M.1)

/-- **$O(V)(F)$ acts on vectors** by $\gamma\cdot v = \gamma v$. -/
@[instance_reducible]
def vecAct : MulAction (orthGroup Q F) (Fin N → F) where
  smul γ v := (γ : GL (Fin N) F).val *ᵥ v
  one_smul v := by
    show ((1 : orthGroup Q F) : GL (Fin N) F).val *ᵥ v = v
    rw [OneMemClass.coe_one, Units.val_one, one_mulVec]
  mul_smul a b v := by
    show ((a * b : orthGroup Q F) : GL (Fin N) F).val *ᵥ v = (a : GL (Fin N) F).val *ᵥ
      ((b : GL (Fin N) F).val *ᵥ v)
    rw [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]

attribute [local instance] ratAct vecAct

theorem ratAct_smul (γ : orthGroup Q F) (M : Lat F N) : γ • M = Lat.image (γ : GL (Fin N) F) M := rfl

theorem vecAct_smul (γ : orthGroup Q F) (v : Fin N → F) : γ • v = (γ : GL (Fin N) F).val *ᵥ v := rfl

theorem image_mem_latGenus {L M : Lat F N} (hM : M ∈ latGenus Q L) (γ : orthGroup Q F) :
    Lat.image (γ : GL (Fin N) F) M ∈ latGenus Q L :=
  SameGenus.trans Q hM (IsIsometric.sameGenus Q ⟨γ, γ.2, rfl⟩)

variable (L : Lat F N) (m : F)

/-- **The genus of $L$** as an $O(V)(F)$-set. -/
def genSMA : SubMulAction (orthGroup Q F) (Lat F N) where
  carrier := latGenus Q L
  smul_mem' γ _ hM := image_mem_latGenus Q hM γ

/-- **The pairs** $(M, v)$ with $M \in \mathrm{gen}(L)$, $v \in M$, $Q(v) = m$, as an $O(V)(F)$-set. -/
def pairSMA : SubMulAction (orthGroup Q F) (Lat F N × (Fin N → F)) where
  carrier := {p | p.1 ∈ latGenus Q L ∧ p.2 ∈ p.1.1 ∧ Q.eval p.2 = m}
  smul_mem' γ p hp := ⟨image_mem_latGenus Q hp.1 γ, mulVec_mem_glImage hp.2.1,
    (eval_mulVec_of_mem Q γ.2 p.2).trans hp.2.2⟩

/-- **The level set** $\{v : Q(v) = m\}$ as an $O(V)(F)$-set. -/
def levelSMA : SubMulAction (orthGroup Q F) (Fin N → F) where
  carrier := {v | Q.eval v = m}
  smul_mem' γ v hv := (eval_mulVec_of_mem Q γ.2 v).trans hv

/-- The projection of a pair $(M, v)$ to the lattice $M$. -/
def pairToGen : pairSMA Q L m → genSMA Q L := fun p => ⟨p.1.1, p.2.1⟩

/-- The projection of a pair $(M, v)$ to the vector $v$. -/
def pairToLevel : pairSMA Q L m → levelSMA Q m := fun p => ⟨p.1.2, p.2.2.2⟩

theorem pairToGen_smul (γ : orthGroup Q F) (p : pairSMA Q L m) :
    pairToGen Q L m (γ • p) = γ • pairToGen Q L m p := rfl

theorem pairToLevel_smul (γ : orthGroup Q F) (p : pairSMA Q L m) :
    pairToLevel Q L m (γ • p) = γ • pairToLevel Q L m p := rfl

/-- The fibre of the projection to $M$ is the set of representations of $m$ by $M$. -/
def fiberEquiv (M : genSMA Q L) :
    {p : pairSMA Q L m // pairToGen Q L m p = M} ≃ {v : Fin N → F // v ∈ (M : Lat F N).1 ∧ Q.eval v = m} :=
    { toFun := fun p => ⟨p.1.1.2, by
        have h := p.2
        have h1 : (p.1 : Lat F N × (Fin N → F)).1 = M := congrArg Subtype.val h
        exact ⟨h1 ▸ p.1.2.2.1, p.1.2.2.2⟩⟩
      invFun := fun v => ⟨⟨((M : Lat F N), v.1), M.2, v.2.1, v.2.2⟩, rfl⟩
      left_inv := fun p => by
        rcases p with ⟨⟨⟨M', w⟩, hp⟩, hpM⟩
        have : M' = (M : Lat F N) := congrArg Subtype.val hpM
        subst this
        rfl
      right_inv := fun v => rfl }

theorem card_fiber_pairToGen (M : genSMA Q L) :
    Nat.card {p : pairSMA Q L m // pairToGen Q L m p = M} = repCount Q (M : Lat F N) m :=
  Nat.card_congr (fiberEquiv Q L m M)

/-- The stabilizer of $M$ in $O(V)(F)$ is $O(M)$. -/
theorem card_stabilizer_gen (M : genSMA Q L) :
    Nat.card (stabilizer (orthGroup Q F) M) = Nat.card (autLat Q (M : Lat F N).1) := by
  refine Nat.card_congr
    { toFun := fun γ => ⟨γ.1, (mem_autLat Q).mpr (congrArg (fun x : genSMA Q L => (x : Lat F N).1)
        (mem_stabilizer_iff.mp γ.2))⟩
      invFun := fun γ => ⟨γ.1, mem_stabilizer_iff.mpr (Subtype.ext (Lattices.Lat.ext ((mem_autLat Q).mp γ.2)))⟩
      left_inv := fun γ => rfl
      right_inv := fun γ => rfl }

/-- The class of an $O(V)(F)$-orbit in the genus. -/
def orbitClass : orbitRel.Quotient (orthGroup Q F) (genSMA Q L) → LatClass Q :=
  fun ω => Quotient.mk _ (ω.out : Lat F N)

theorem mem_orbit_gen_iff (M M' : genSMA Q L) :
    M ∈ orbit (orthGroup Q F) M' ↔ IsIsometric Q (M' : Lat F N).1 (M : Lat F N).1 := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, γ.2, congrArg (fun x : genSMA Q L => (x : Lat F N).1) hγ⟩
  · rintro ⟨γ, hγ, he⟩
    exact ⟨⟨γ, hγ⟩, Subtype.ext (Lattices.Lat.ext he)⟩

theorem orbitClass_injective : Function.Injective (orbitClass Q L) := by
  intro ω₁ ω₂ h
  have h' := Quotient.exact h
  rw [← Quotient.out_eq' ω₁, ← Quotient.out_eq' ω₂]
  apply Quotient.sound'
  rw [orbitRel_apply, mem_orbit_gen_iff]
  exact IsIsometric.symm Q h'

theorem orbitClass_image : orbitClass Q L '' Set.univ = genusClasses Q L := by
  ext c
  constructor
  · rintro ⟨ω, -, rfl⟩
    exact ⟨(ω.out : Lat F N), rfl, ω.out.2⟩
  · rintro ⟨M, rfl, hM⟩
    refine ⟨Quotient.mk'' ⟨M, hM⟩, Set.mem_univ _, ?_⟩
    apply Quotient.sound
    have h1 : (Quotient.mk'' ⟨M, hM⟩ : orbitRel.Quotient (orthGroup Q F) (genSMA Q L)).out ∈
        orbit (orthGroup Q F) (⟨M, hM⟩ : genSMA Q L) := out_mem_orbit _ _ rfl
    exact IsIsometric.symm Q ((mem_orbit_gen_iff Q L _ _).mp h1)

/-- **Finitely many classes in the genus**, as $O(V)(F)$-orbits. -/
theorem finite_orbits_gen {Q : QuadForm F N} (hQ : IsTotallyPosDef Q) (L : Lat F N) (hLi : IsIntegral Q L.1) :
    Finite (orbitRel.Quotient (orthGroup Q F) (genSMA Q L)) := by
  have h := (genusClasses_finite hQ L hLi).subset (orbitClass_image Q L).le
  have := (h.of_finite_image (orbitClass_injective Q L).injOn)
  exact Set.finite_univ_iff.mp this

/-- **The weighted representation number as an orbit mass of pairs:**
$\mathrm{repMass}(L, m) = \mathrm{mass}_{O(V)(F)}\{(M, v) : M \in \mathrm{gen}(L),\ v \in M,\ Q(v) = m\}$. -/
theorem repMass_eq_orbitMass_pairs {Q : QuadForm F N} (hQ : IsTotallyPosDef Q) (L : Lat F N)
    (hLi : IsIntegral Q L.1) (m : F) :
    repMass Q L m = orbitMass (orthGroup Q F) (pairSMA Q L m) := by
  have := finite_orbits_gen hQ L hLi
  have hstab : ∀ M : genSMA Q L, Finite (stabilizer (orthGroup Q F) M) := by
    intro M
    have := finite_autLat hQ (M : Lat F N).2 (SameGenus.isIntegral Q hLi M.2)
    apply Nat.finite_of_card_ne_zero
    rw [card_stabilizer_gen]; exact Nat.card_pos.ne'
  have hfin : ∀ M : genSMA Q L, Finite {p : pairSMA Q L m // pairToGen Q L m p = M} := by
    intro M
    have := finite_repSet hQ (M : Lat F N).2 (SameGenus.isIntegral Q hLi M.2) m
    exact Finite.of_equiv _ (fiberEquiv Q L m M).symm
  rw [orbitMass_eq_finsum_fiber (pairToGen Q L m) (pairToGen_smul Q L m) hstab hfin]
  unfold repMass
  rw [← orbitClass_image Q L, finsum_mem_image (orbitClass_injective Q L).injOn, finsum_mem_univ]
  congr 1
  ext ω
  rw [card_fiber_pairToGen, card_stabilizer_gen]
  rfl

end Pairs

end QuadFormsKB.Tamagawa

/-! ### The split case: reduction to lattices containing $e_0$ -/

namespace QuadFormsKB.Tamagawa

open Lattices

section Split

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (m : F) (Q' : QuadForm F n)

local notation "QS" => splitForm m Q'

attribute [local instance] ratAct vecAct

theorem eval_splitForm_e₀ : (QS).eval (e₀ : Fin (n + 1) → F) = m := by
  rw [QuadForm.eval, evalIn_splitForm_e₀]; rfl

/-- The base point $e_0$ of the level set $\{Q(v) = m\}$. -/
def e₀Level : levelSMA QS m := ⟨e₀, eval_splitForm_e₀ m Q'⟩

theorem locVec_e₀ (v : HeightOneSpectrum (𝓞 F)) :
    locVec v (e₀ : Fin (n + 1) → F) = (e₀ : Fin (n + 1) → v.adicCompletion F) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem e₀_mem_latSMul (h : OAf Q') {M : Lat F (n + 1)} (hM : (e₀ : Fin (n + 1) → F) ∈ M.1) :
    (e₀ : Fin (n + 1) → F) ∈ (latSMul QS (orthEmbAf m Q' h) M).1 := by
  rw [mem_iff_forall_loc (latSMul QS _ M).2]
  intro v
  rw [loc_latSMul, locVec_e₀]
  refine ⟨e₀, ?_, ?_⟩
  · rw [← locVec_e₀]; exact locVec_mem_loc v hM
  · simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
    exact orthEmb_mulVec_e₀ m Q' _ (h v)

theorem latSMul_mem_latGenus (h : OAf QS) {L M : Lat F (n + 1)} (hM : M ∈ latGenus QS L) :
    latSMul QS h M ∈ latGenus QS L := by
  rw [← orbit_eq_genus] at hM ⊢
  obtain ⟨g, rfl⟩ := hM
  exact ⟨h * g, (latSMul_mul QS _ _ L)⟩

variable (L : Lat F (n + 1))

/-- **The lattices of the genus containing $e_0$**, $Y = \{M \in \mathrm{gen}(L) : e_0 \in M\}$. The group
$O(Q')(\mathbb A_f)$ acts on $Y$ through $\mathrm{diag}(1, \cdot)$ (`CompSet.instMulAction`); its orbits are the **local
types** of the pairs $(M, e_0)$, and $M \cap e_0^\perp$ is the complement lattice in $(F^n, Q')$. -/
def CompSet : Type _ := {M : Lat F (n + 1) // M ∈ latGenus QS L ∧ (e₀ : Fin (n + 1) → F) ∈ M.1}

instance CompSet.instMulAction : MulAction (OAf Q') (CompSet m Q' L) where
  smul h M := ⟨latSMul QS (orthEmbAf m Q' h) M.1, latSMul_mem_latGenus m Q' _ M.2.1,
    e₀_mem_latSMul m Q' h M.2.2⟩
  one_smul M := Subtype.ext (by
    show latSMul QS (orthEmbAf m Q' 1) M.1 = M.1
    rw [map_one]; exact (latAction QS).one_smul M.1)
  mul_smul a b M := Subtype.ext (by
    show latSMul QS (orthEmbAf m Q' (a * b)) M.1 = latSMul QS (orthEmbAf m Q' a) (latSMul QS (orthEmbAf m Q' b) M.1)
    rw [map_mul, latSMul_mul])

theorem CompSet.smul_val (h : OAf Q') (M : CompSet m Q' L) :
    (h • M).1 = latSMul QS (orthEmbAf m Q' h) M.1 := rfl

/-- **The stabilizer of a type** containing $M$: $K_M = \{h \in O(Q')(\mathbb A_f) : \mathrm{diag}(1, h) \in O(\hat M)\}$. -/
theorem stabilizer_compSet (y : CompSet m Q' L) :
    stabilizer (OAf Q') y = (locStab QS y.1).comap (orthEmbAf m Q') := by
  ext h
  rw [mem_stabilizer_iff, Subgroup.mem_comap, ← stabilizer_eq_locStab QS]
  rw [@MulAction.mem_stabilizer_iff _ _ _ (latAction QS)]
  constructor
  · intro hh; exact congrArg Subtype.val hh
  · intro hh; exact Subtype.ext hh

/-! #### Witt's theorem: from pairs to $Y$ -/

/-- **Witt transitivity** on the level set: every $v$ with $Q(v) = m$ is $\gamma e_0$. -/
theorem transitive_level (hQ : (QS).Nondegenerate) (hm : m ≠ 0) (x : levelSMA QS m) :
    ∃ γ : orthGroup QS F, γ • e₀Level m Q' = x := by
  obtain ⟨γ, hγ⟩ := exists_orthGroup_mulVec_eq m Q' hQ hm x.2
  exact ⟨γ, Subtype.ext hγ⟩

/-- The stabilizer of $e_0$ in $O(Q)(F)$. -/
abbrev Stab₀ : Subgroup (orthGroup QS F) := stabilizer (orthGroup QS F) (e₀Level m Q')

/-- $O(Q')(F) \to \mathrm{Stab}(e_0)$, $g \mapsto \mathrm{diag}(1, g)$. -/
def orthEmbStab : orthGroup Q' F →* Stab₀ m Q' where
  toFun g := ⟨orthEmb m Q' F g, mem_stabilizer_iff.mpr (Subtype.ext (orthEmb_mulVec_e₀ m Q' F g))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem orthEmbStab_bijective (hm : m ≠ 0) : Function.Bijective (orthEmbStab m Q') := by
  constructor
  · intro a b h
    exact orthEmb_injective m Q' F (congrArg Subtype.val h)
  · intro s
    have hs : ((s : orthGroup QS F) : GL (Fin (n + 1)) F).val *ᵥ (e₀ : Fin (n + 1) → F) = e₀ :=
      congrArg Subtype.val (mem_stabilizer_iff.mp s.2)
    have h2 : algebraMap F F (2 * m) ≠ 0 := by
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      exact mul_ne_zero two_ne_zero hm
    obtain ⟨g, hg⟩ := exists_orthEmb_eq m Q' F h2 s hs
    exact ⟨g, Subtype.ext hg⟩

/-- **$\mathrm{Stab}_{O(Q)(F)}(e_0) \cong O(Q')(F)$**, the latter embedded in $O(Q')(\mathbb A_f)$ as its rational points. -/
def stabEquiv (hm : m ≠ 0) : Stab₀ m Q' ≃* ratPoints Q' :=
  (MulEquiv.ofBijective _ (orthEmbStab_bijective m Q' hm)).symm.trans
    (MonoidHom.ofInjective (diagF_injective Q'))

theorem stabEquiv_smul (hm : m ≠ 0) (s : Stab₀ m Q') (M : Lat F (n + 1)) :
    latSMul QS (orthEmbAf m Q' (stabEquiv m Q' hm s : OAf Q')) M = (s : orthGroup QS F) • M := by
  set g' := (MulEquiv.ofBijective _ (orthEmbStab_bijective m Q' hm)).symm s
  have hs : orthEmbStab m Q' g' = s :=
    MulEquiv.apply_symm_apply (MulEquiv.ofBijective (orthEmbStab m Q') (orthEmbStab_bijective m Q' hm)) s
  have h1 : (stabEquiv m Q' hm s : OAf Q') = diagF Q' g' := rfl
  rw [h1, orthEmbAf_diagF, diagF_smul, ratAct_smul, ← hs]
  rfl

variable (L : Lat F (n + 1))

/-- The fibre of the pairs over $e_0$. -/
abbrev Fib₀ : Type _ := {p : pairSMA QS L m // pairToLevel QS L m p = e₀Level m Q'}

@[instance_reducible]
def fibAct : MulAction (Stab₀ m Q') (Fib₀ m Q' L) :=
  fiberAction (pairToLevel QS L m) (pairToLevel_smul QS L m) (e₀Level m Q')

attribute [local instance] fibAct

theorem fib_vec (p : Fib₀ m Q' L) : (p.1 : Lat F (n + 1) × (Fin (n + 1) → F)).2 = e₀ :=
  congrArg Subtype.val p.2

/-- A pair $(M, e_0)$ gives $M \in Y$. -/
def fibToComp (p : Fib₀ m Q' L) : CompSet m Q' L :=
  ⟨(p.1 : Lat F (n + 1) × (Fin (n + 1) → F)).1, p.1.2.1, fib_vec m Q' L p ▸ p.1.2.2.1⟩

/-- $M \in Y$ gives the pair $(M, e_0)$. -/
def compToFib (y : CompSet m Q' L) : Fib₀ m Q' L :=
  ⟨⟨(y.1, e₀), y.2.1, y.2.2, eval_splitForm_e₀ m Q'⟩, rfl⟩

theorem fibToComp_compToFib (y : CompSet m Q' L) : fibToComp m Q' L (compToFib m Q' L y) = y := rfl

theorem fib_smul_val (s : Stab₀ m Q') (p : Fib₀ m Q' L) :
    ((s • p).1 : Lat F (n + 1) × (Fin (n + 1) → F)) =
      ((s : orthGroup QS F) • (p.1 : Lat F (n + 1) × (Fin (n + 1) → F)).1,
        (s : orthGroup QS F) • (p.1 : Lat F (n + 1) × (Fin (n + 1) → F)).2) := rfl

theorem smul_fib_iff (hm : m ≠ 0) (s : Stab₀ m Q') (a b : Fib₀ m Q' L) :
    s • b = a ↔ (stabEquiv m Q' hm s : OAf Q') • fibToComp m Q' L b = fibToComp m Q' L a := by
  constructor
  · intro h
    apply Subtype.ext
    rw [CompSet.smul_val, stabEquiv_smul]
    have := congrArg (fun p : Fib₀ m Q' L => (p.1 : Lat F (n + 1) × (Fin (n + 1) → F)).1) h
    simp only [fib_smul_val] at this
    exact this
  · intro h
    have h1 := congrArg Subtype.val h
    rw [CompSet.smul_val, stabEquiv_smul] at h1
    apply Subtype.ext; apply Subtype.ext
    rw [fib_smul_val]
    refine Prod.ext h1 ?_
    show (s : orthGroup QS F) • (b.1 : Lat F (n + 1) × (Fin (n + 1) → F)).2 =
      (a.1 : Lat F (n + 1) × (Fin (n + 1) → F)).2
    rw [fib_vec, fib_vec]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp s.2)

/-- **The pairs over $e_0$ are $Y$:** $\mathrm{mass}_{\mathrm{Stab}(e_0)}(\text{pairs over } e_0) = \mathrm{mass}_{O(Q')(F)}(Y)$. -/
theorem orbitMass_fib_eq (hm : m ≠ 0) :
    orbitMass (Stab₀ m Q') (Fib₀ m Q' L) = orbitMass (ratPoints Q') (CompSet m Q' L) := by
  refine orbitMass_eq_of_map (fibToComp m Q' L) ?_ ?_ ?_
  · intro a b
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨stabEquiv m Q' hm s, (smul_fib_iff m Q' L hm s a b).mp hs⟩
    · rintro ⟨γ, hγ⟩
      refine ⟨(stabEquiv m Q' hm).symm γ, (smul_fib_iff m Q' L hm _ a b).mpr ?_⟩
      rw [MulEquiv.apply_symm_apply]
      exact hγ
  · intro y
    exact ⟨compToFib m Q' L y, mem_orbit_self y⟩
  · intro x
    refine (Nat.card_congr ((stabEquiv m Q' hm).toEquiv.subtypeEquiv fun s => ?_)).symm
    rw [mem_stabilizer_iff, mem_stabilizer_iff]
    exact smul_fib_iff m Q' L hm s x x

theorem finite_orbits_pairs (hpd : IsTotallyPosDef QS) (hLi : IsIntegral QS L.1) :
    Finite (orbitRel.Quotient (orthGroup QS F) (pairSMA QS L m)) := by
  have := finite_orbits_gen hpd L hLi
  exact finite_orbits_of_fiber (pairToGen QS L m) (pairToGen_smul QS L m) fun M => by
    have := finite_repSet hpd (M : Lat F (n + 1)).2 (SameGenus.isIntegral QS hLi M.2) m
    exact Finite.of_equiv _ (fiberEquiv QS L m M).symm

theorem fib_orbit_of (a b : Fib₀ m Q' L) (h : a.1 ∈ orbit (orthGroup QS F) b.1) :
    a ∈ orbit (Stab₀ m Q') b := by
  obtain ⟨γ, hγ⟩ := h
  have hγ' : γ • b.1 = a.1 := hγ
  have hγs : γ ∈ Stab₀ m Q' := by
    rw [mem_stabilizer_iff]
    have := congrArg (pairToLevel QS L m) hγ'
    rw [pairToLevel_smul, b.2, a.2] at this
    exact this
  exact ⟨⟨γ, hγs⟩, Subtype.ext hγ'⟩

theorem finite_orbits_fib (hpd : IsTotallyPosDef QS) (hLi : IsIntegral QS L.1) :
    Finite (orbitRel.Quotient (Stab₀ m Q') (Fib₀ m Q' L)) := by
  have := finite_orbits_pairs m Q' L hpd hLi
  exact finite_orbits_of_map (H₂ := orthGroup QS F) (fun p : Fib₀ m Q' L => p.1) (fib_orbit_of m Q' L)

theorem finite_orbits_compSet (hpd : IsTotallyPosDef QS) (hLi : IsIntegral QS L.1) (hm : m ≠ 0) :
    Finite (orbitRel.Quotient (ratPoints Q') (CompSet m Q' L)) := by
  have := finite_orbits_fib m Q' L hpd hLi
  refine finite_orbits_of_map (H₂ := Stab₀ m Q') (compToFib m Q' L) ?_
  rintro a b ⟨s, hs⟩
  have h := (smul_fib_iff m Q' L hm s (compToFib m Q' L a) (compToFib m Q' L b)).mp hs
  rw [fibToComp_compToFib, fibToComp_compToFib] at h
  exact ⟨stabEquiv m Q' hm s, h⟩

/-- **The global reduction (Weil's orbit counting):** for $Q = \langle m\rangle \perp Q'$ totally positive definite,
$m \ne 0$ and $L$ integral,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \sum_{t \in O(Q')(\mathbb A_f)\backslash Y}
  \mathrm{dcMass}\big(O(Q')(F), K_t\big),\qquad Y = \{M \in \mathrm{gen}(L) : e_0 \in M\},$$
$K_t = \mathrm{Stab}_{O(Q')(\mathbb A_f)}(M_t)$ for a representative $M_t$ = `t.out` (Weil 1982, §3.4–3.5 [unverified locator];
Siegel 1935, §§2–3 [unverified]; Kitaoka 1993, §6.8 [unverified]). See the module docstring for the proof. -/
@[kb "weil1982" "§3.4-3.5 (orbit counting) [unverified locator]"]
theorem repMass_eq_finsum_dcMass (hpd : IsTotallyPosDef QS) (hLi : IsIntegral QS L.1) (hm : m ≠ 0) :
    repMass QS L m = ∑ᶠ t : orbitRel.Quotient (OAf Q') (CompSet m Q' L),
      dcMass (ratPoints Q') (stabilizer (OAf Q') t.out) := by
  have := finite_orbits_compSet m Q' L hpd hLi hm
  rw [repMass_eq_orbitMass_pairs hpd L hLi m,
    orbitMass_eq_fiber_of_transitive (pairToLevel QS L m) (pairToLevel_smul QS L m) (e₀Level m Q')
      (transitive_level m Q' hpd.nondegenerate hm)]
  rw [show @orbitMass (Stab₀ m Q') (Fib₀ m Q' L) _ (fiberAction (pairToLevel QS L m) (pairToLevel_smul QS L m)
    (e₀Level m Q')) = orbitMass (Stab₀ m Q') (Fib₀ m Q' L) from rfl, orbitMass_fib_eq m Q' L hm]
  exact orbitMass_eq_finsum_dcMass (ratPoints Q')

/-! #### The masses of the complements -/

/-- **The weight of a local type** $t \in O(Q')(\mathbb A_f)\backslash Y$: with $K_t$ the stabilizer of the representative
$M_t$ = `t.out` and $K_0' = O(\hat{\mathcal O}_F^n)$ in $O(Q')(\mathbb A_f)$,
$$w(t) = \frac{\mu(K_0')}{\mu(K_t)} = \frac{[K_0' : K_t \cap K_0']}{[K_t : K_t \cap K_0']}$$
for any Haar measure $\mu$ (`idxVol`). It is a product over the primes of local index ratios, $1$ at almost all
primes, and does not depend on the representative. -/
@[kb "weil1982" "§3.5 [unverified locator]"]
def typeWeight (t : orbitRel.Quotient (OAf Q') (CompSet m Q' L)) : ℝ :=
  ((stabilizer (OAf Q') t.out).relIndex (locStab Q' (stdLat F n)) : ℝ) /
    ((locStab Q' (stdLat F n)).relIndex (stabilizer (OAf Q') t.out) : ℝ)

theorem commensurable_stabilizer_compSet (y : CompSet m Q' L) :
    (stabilizer (OAf Q') y).Commensurable (locStab Q' (stdLat F n)) := by
  rw [stabilizer_compSet, ← comap_orthEmbAf_locStab_intVec m Q']
  exact (commensurable_locStab QS (stdLat F (n + 1)) y.1).comap _

/-- **The mass of a type:** $\mathrm{dcMass}(O(Q')(F), K_t) = \mathrm{Mass}(\mathcal O_F^n, Q')\cdot w(t)$
(`dcMass_mul_idxVol`, `mass_eq_dcMass`). -/
theorem dcMass_type_eq (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n).1)
    (t : orbitRel.Quotient (OAf Q') (CompSet m Q' L)) :
    dcMass (ratPoints Q') (stabilizer (OAf Q') t.out) = mass Q' (stdLat F n) * typeWeight m Q' L t := by
  have hK := commensurable_stabilizer_compSet m Q' L t.out
  have := finite_orbits hpd' (stdLat F n) hLi'
  have h := dcMass_mul_idxVol (ratPoints Q') (locStab Q' (stdLat F n)) (stabilizer (OAf Q') t.out) 1 hK
    (finite_stabilizer hpd' (stdLat F n) hLi')
  rw [one_mul, ← mass_eq_dcMass] at h
  have h1 : ((stabilizer (OAf Q') t.out).relIndex (locStab Q' (stdLat F n)) : ℝ) ≠ 0 := by
    exact_mod_cast hK.1.relIndex_ne_zero
  have h2 : ((locStab Q' (stdLat F n)).relIndex (stabilizer (OAf Q') t.out) : ℝ) ≠ 0 := by
    exact_mod_cast hK.2.relIndex_ne_zero
  unfold idxVol at h
  unfold typeWeight
  rw [← h]
  field_simp

theorem finite_types (hpd : IsTotallyPosDef QS) (hLi : IsIntegral QS L.1) (hm : m ≠ 0) :
    Finite (orbitRel.Quotient (OAf Q') (CompSet m Q' L)) := by
  have := finite_orbits_compSet m Q' L hpd hLi hm
  refine Finite.of_surjective (fun ω : orbitRel.Quotient (ratPoints Q') (CompSet m Q' L) =>
    (Quotient.mk'' ω.out : orbitRel.Quotient (OAf Q') (CompSet m Q' L))) fun t => ?_
  refine ⟨Quotient.mk'' t.out, ?_⟩
  conv_rhs => rw [← Quotient.out_eq' t]
  apply Quotient.sound'
  rw [orbitRel_apply]
  obtain ⟨γ, hγ⟩ := out_mem_orbit (Quotient.mk'' t.out : orbitRel.Quotient (ratPoints Q') (CompSet m Q' L))
    t.out rfl
  exact ⟨(γ : OAf Q'), hγ⟩

/-- **The global reduction in terms of the complement mass** (Weil's induction step, global part): for
$Q = \langle m\rangle \perp Q'$ with $Q, Q'$ totally positive definite, $m \ne 0$, $L$ and $\mathcal O_F^n$ integral,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^n, Q')\cdot
  \sum_{t \in O(Q')(\mathbb A_f)\backslash Y} w(t).$$
The sum over local types $t$ is finite (`finite_types`) and purely adelic: $w(t) = \mu(K_0')/\mu(K_t)$. -/
@[kb "weil1982" "§3.4-3.5 (orbit counting) [unverified locator]"]
theorem repMass_eq_mass_mul (hpd : IsTotallyPosDef QS) (hLi : IsIntegral QS L.1) (hm : m ≠ 0)
    (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n).1) :
    repMass QS L m = mass Q' (stdLat F n) * ∑ᶠ t : orbitRel.Quotient (OAf Q') (CompSet m Q' L),
      typeWeight m Q' L t := by
  have := finite_types m Q' L hpd hLi hm
  rw [repMass_eq_finsum_dcMass m Q' L hpd hLi hm, mul_finsum]
  exact finsum_congr fun t => dcMass_type_eq m Q' L hpd' hLi' t

end Split

end QuadFormsKB.Tamagawa
