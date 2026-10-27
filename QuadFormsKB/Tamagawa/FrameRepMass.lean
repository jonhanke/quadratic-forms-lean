/-
# The weighted representation number of a form, and Weil's reduction to complements for frames

**Layer:** lattices in $(F^N, Q)$ over a totally real number field $F$ (`Lattices/`), the finite adelic orthogonal group, and the
orthogonal sum $T\perp Q'$ (`BlockForm.lean`).

**Defines**
* `repCountT Q M T` $= r_M(T) = \#\{X \in M^r : Q\circ X = T\}$ (frames of $T$ in $M$; columns in $M$) and its value on a class;
* `repMassT Q L T` $= \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)} r_M(T)/|O(M)|$;
* for $Q = T\perp Q'$ and $L$ in $(F^{r+n'}, Q)$: `CompSetT` $= Y = \{M \in \mathrm{gen}(L) : E \subseteq M\}$ (the columns of the standard
  frame lie in $M$), acted on by $O(Q')(\mathbb A_f)$ through $\mathrm{diag}(1_r, \cdot)$, and `typeWeightT` $w(t) = \mu(K_0')/\mu(K_t)$.

**Proves**
* `repMassT_eq_mass_mul` (**Weil's orbit counting for frames**; Weil 1982, §3.4–3.5 [unverified locator]; Kitaoka 1993, §6.8
  [unverified]): for $Q = T\perp Q'$ totally positive definite and $L$, $\mathcal O_F^{n'}$ integral,
  $$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^{n'}, Q')\cdot\sum_{t\in O(Q')(\mathbb A_f)\backslash Y}w(t).$$
  *Proof:* as `repMass_eq_mass_mul`: pairs $(M, X)$ under $O(Q)(F)$; Witt's theorem makes $O(Q)(F)$ transitive on
  the frames of $T$
  (`exists_orthGroup_mul_stdFrameMat`) and the stabilizer of $E$ is $\mathrm{diag}(1_r, O(Q')(F))$ (`exists_orthEmbB_eq`); then the orbits of
  $O(Q')(\mathbb A_f)$ on $Y$ and the complement mass (`dcMass_mul_idxVol`).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.RepMass
import QuadFormsKB.Tamagawa.BlockForm

open NumberField IsDedekindDomain Matrix MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices

section RepCount

variable {F : Type*} [Field F] [NumberField F] {N r : ℕ} (Q : QuadForm F N)

/-- **The representation number** $r_M(T) = \#\{X \in M^r : Q\circ X = T\}$ of a form $T$ of rank $r$ by the lattice $M$: the number of
frames $X \in F^{N\times r}$ with all columns in $M$ and Gram form $T$ (O'Meara 1963, §82A, p. 220, for $r = 1$; Siegel 1935 [unverified]). -/
@[kb "siegel1935" "§1 (representation numbers of forms) [unverified]"]
def repCountT (M : Lat F N) (T : QuadForm F r) : ℕ :=
  Nat.card {X : Matrix (Fin N) (Fin r) F // (∀ j, (fun i => X i j) ∈ M.1) ∧ Q.compMat X = T}

theorem col_mul {R : Type*} [CommRing R] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R) (X : Matrix (Fin b) (Fin c) R)
    (j : Fin c) : (fun i => (A * X) i j) = A *ᵥ (fun i => X i j) := by
  ext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Each column of a frame of $T$ has value the diagonal coefficient of $T$. -/
theorem eval_col_of_compMat {X : Matrix (Fin N) (Fin r) F} {T : QuadForm F r} (h : Q.compMat X = T) (j : Fin r) :
    Q.eval (fun i => X i j) = T.coeff j j := by
  rw [← h, QuadForm.compMat_coeff]; simp

/-- Isometries preserve the Gram form of a frame: $Q\circ(\gamma X) = Q\circ X$. -/
theorem compMat_orth {γ : GL (Fin N) F} (hγ : γ ∈ orthGroup Q F) (X : Matrix (Fin N) (Fin r) F) :
    Q.compMat (γ.val * X) = Q.compMat X :=
  QuadForm.eq_of_eval_eq fun y => by
    rw [QuadForm.eval_compMat, QuadForm.eval_compMat, ← mulVec_mulVec, eval_mulVec_of_mem Q hγ]

/-- **$O(V)(F)$ acts on frames** by $\gamma\cdot X = \gamma X$ (left multiplication). -/
@[instance_reducible]
def frameAct : MulAction (orthGroup Q F) (Matrix (Fin N) (Fin r) F) where
  smul γ X := (γ : GL (Fin N) F).val * X
  one_smul X := by
    show ((1 : orthGroup Q F) : GL (Fin N) F).val * X = X
    rw [OneMemClass.coe_one, Units.val_one, Matrix.one_mul]
  mul_smul a b X := by
    show ((a * b : orthGroup Q F) : GL (Fin N) F).val * X = (a : GL (Fin N) F).val *
      ((b : GL (Fin N) F).val * X)
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]

/-- **Isometric lattices represent $T$ equally often:** $r_{\gamma M}(T) = r_M(T)$ for $\gamma \in O(V)(F)$. -/
theorem repCountT_glImage {γ : GL (Fin N) F} (hγ : γ ∈ orthGroup Q F) (M : Lat F N) (T : QuadForm F r) :
    repCountT Q (Lat.image γ M) T = repCountT Q M T := by
  refine Nat.card_congr
    { toFun := fun X => ⟨γ⁻¹.val * X.1, ?_, ?_⟩
      invFun := fun X => ⟨γ.val * X.1, ?_, ?_⟩
      left_inv := fun X => Subtype.ext (by
        show γ.val * (γ⁻¹.val * X.1) = X.1
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
      right_inv := fun X => Subtype.ext (by
        show γ⁻¹.val * (γ.val * X.1) = X.1
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]) }
  · intro j
    obtain ⟨y, hy, hyv⟩ := (mem_glImage).mp (X.2.1 j)
    rw [col_mul, ← hyv, mulVec_mulVec, Units.inv_mul, one_mulVec]; exact hy
  · rw [compMat_orth Q ((orthGroup Q F).inv_mem hγ)]; exact X.2.2
  · intro j
    rw [col_mul]; exact mulVec_mem_glImage (X.2.1 j)
  · rw [compMat_orth Q hγ]; exact X.2.2

theorem repCountT_of_isIsometric {M M' : Lat F N} (h : IsIsometric Q M.1 M'.1) (T : QuadForm F r) :
    repCountT Q M T = repCountT Q M' T := by
  obtain ⟨γ, hγ, he⟩ := h
  rw [← repCountT_glImage Q hγ M T]
  congr 1
  exact Lattices.Lat.ext he

/-- $r_M(T)$ of a class. -/
def LatClass.repCountT (c : LatClass Q) (T : QuadForm F r) : ℕ :=
  Quotient.lift (fun M : Lat F N => Frames.repCountT Q M T) (fun _ _ h => repCountT_of_isIsometric Q h T) c

/-- **The weighted representation number of $T$ by the genus of $L$:**
$\mathrm{repMassT}(L, T) = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)} r_M(T)/|O(M)|$ ($O(M)$ including improper automorphisms). -/
@[kb "siegel1935" "§1 (genus average) [unverified]"]
def repMassT (L : Lat F N) (T : QuadForm F r) : ℝ :=
  ∑ᶠ c ∈ genusClasses Q L, (LatClass.repCountT Q c T : ℝ) / LatClass.autCard Q c

end RepCount

/-! ### Rational isometries acting on lattices, frames and pairs -/

section Pairs

variable {F : Type*} [Field F] [NumberField F] {N r : ℕ} (Q : QuadForm F N)

attribute [local instance] ratAct frameAct

theorem frameAct_smul (γ : orthGroup Q F) (X : Matrix (Fin N) (Fin r) F) :
    γ • X = (γ : GL (Fin N) F).val * X := rfl

/-- **Finitely many frames:** for totally positive definite $Q$ and an integral lattice $M$, $r_M(T) < \infty$
(each column lies in $M$ and has the prescribed value, `finite_repSet`). -/
theorem finite_repSetT {Q : QuadForm F N} (hQ : IsTotallyPosDef Q) {M : Lat F N} (hMi : IsIntegral Q M.1)
    (T : QuadForm F r) :
    Finite {X : Matrix (Fin N) (Fin r) F // (∀ j, (fun i => X i j) ∈ M.1) ∧ Q.compMat X = T} := by
  classical
  have hj : ∀ j : Fin r, Finite {v : Fin N → F // v ∈ M.1 ∧ Q.eval v = T.coeff j j} :=
    fun j => finite_repSet hQ M.2 hMi _
  refine Finite.of_injective
    (fun X j => (⟨fun i => X.1 i j, X.2.1 j, eval_col_of_compMat Q X.2.2 j⟩ :
      {v : Fin N → F // v ∈ M.1 ∧ Q.eval v = T.coeff j j})) ?_
  intro X Y h
  apply Subtype.ext
  ext i j
  exact congrFun (congrArg Subtype.val (congrFun h j)) i

variable (L : Lat F N) (T : QuadForm F r)

/-- **The pairs** $(M, X)$ with $M \in \mathrm{gen}(L)$, columns of $X$ in $M$, $Q\circ X = T$, as an $O(V)(F)$-set. -/
def pairSMAT : SubMulAction (orthGroup Q F) (Lat F N × Matrix (Fin N) (Fin r) F) where
  carrier := {p | p.1 ∈ latGenus Q L ∧ (∀ j, (fun i => p.2 i j) ∈ p.1.1) ∧ Q.compMat p.2 = T}
  smul_mem' γ p hp := ⟨image_mem_latGenus Q hp.1 γ, fun j => by
      have h := mulVec_mem_glImage (γ := (γ : GL (Fin N) F)) (hp.2.1 j)
      rw [← col_mul] at h
      exact h, (compMat_orth Q γ.2 p.2).trans hp.2.2⟩

/-- **The level set** $\{X : Q\circ X = T\}$ of frames as an $O(V)(F)$-set. -/
def levelSMAT : SubMulAction (orthGroup Q F) (Matrix (Fin N) (Fin r) F) where
  carrier := {X | Q.compMat X = T}
  smul_mem' γ X hX := (compMat_orth Q γ.2 X).trans hX

/-- The projection of a pair $(M, X)$ to the lattice $M$. -/
def pairToGenT : pairSMAT Q L T → genSMA Q L := fun p => ⟨p.1.1, p.2.1⟩

/-- The projection of a pair $(M, X)$ to the frame $X$. -/
def pairToLevelT : pairSMAT Q L T → levelSMAT Q T := fun p => ⟨p.1.2, p.2.2.2⟩

theorem pairToGenT_smul (γ : orthGroup Q F) (p : pairSMAT Q L T) :
    pairToGenT Q L T (γ • p) = γ • pairToGenT Q L T p := rfl

theorem pairToLevelT_smul (γ : orthGroup Q F) (p : pairSMAT Q L T) :
    pairToLevelT Q L T (γ • p) = γ • pairToLevelT Q L T p := rfl

/-- The fibre of the projection to $M$ is the set of frames of $T$ in $M$. -/
def fiberEquivT (M : genSMA Q L) :
    {p : pairSMAT Q L T // pairToGenT Q L T p = M} ≃
      {X : Matrix (Fin N) (Fin r) F // (∀ j, (fun i => X i j) ∈ (M : Lat F N).1) ∧ Q.compMat X = T} :=
    { toFun := fun p => ⟨p.1.1.2, fun j => by
        have h : (p.1 : Lat F N × Matrix (Fin N) (Fin r) F).1 = M := congrArg Subtype.val p.2
        have h2 := p.1.2.2.1 j
        rw [h] at h2
        exact h2, p.1.2.2.2⟩
      invFun := fun X => ⟨⟨((M : Lat F N), X.1), M.2, X.2.1, X.2.2⟩, rfl⟩
      left_inv := fun p => by
        rcases p with ⟨⟨⟨M', w⟩, hp⟩, hpM⟩
        have : M' = (M : Lat F N) := congrArg Subtype.val hpM
        subst this
        rfl
      right_inv := fun X => rfl }

theorem card_fiber_pairToGenT (M : genSMA Q L) :
    Nat.card {p : pairSMAT Q L T // pairToGenT Q L T p = M} = repCountT Q (M : Lat F N) T :=
  Nat.card_congr (fiberEquivT Q L T M)

/-- **The weighted representation number of frames as an orbit mass of pairs.** -/
theorem repMassT_eq_orbitMass_pairs {Q : QuadForm F N} (hQ : IsTotallyPosDef Q) (L : Lat F N)
    (hLi : IsIntegral Q L.1) (T : QuadForm F r) :
    repMassT Q L T = orbitMass (orthGroup Q F) (pairSMAT Q L T) := by
  have := finite_orbits_gen hQ L hLi
  have hstab : ∀ M : genSMA Q L, Finite (stabilizer (orthGroup Q F) M) := by
    intro M
    have := finite_autLat hQ (M : Lat F N).2 (SameGenus.isIntegral Q hLi M.2)
    apply Nat.finite_of_card_ne_zero
    rw [card_stabilizer_gen]; exact Nat.card_pos.ne'
  have hfin : ∀ M : genSMA Q L, Finite {p : pairSMAT Q L T // pairToGenT Q L T p = M} := by
    intro M
    have := finite_repSetT hQ (M := (M : Lat F N)) (SameGenus.isIntegral Q hLi M.2) T
    exact Finite.of_equiv _ (fiberEquivT Q L T M).symm
  rw [orbitMass_eq_finsum_fiber (pairToGenT Q L T) (pairToGenT_smul Q L T) hstab hfin]
  unfold repMassT
  rw [← orbitClass_image Q L, finsum_mem_image (orbitClass_injective Q L).injOn, finsum_mem_univ]
  congr 1
  ext ω
  rw [card_fiber_pairToGenT, card_stabilizer_gen]
  rfl

end Pairs

section Split

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (T : QuadForm F r) (Q' : QuadForm F n')

local notation "QB" => blockForm T Q'

variable (L : Lat F (r + n'))

attribute [local instance] ratAct frameAct

omit [NumberField F] in
theorem map_self_quadForm {n : ℕ} (S : QuadForm F n) : S.map (algebraMap F F) = S := by
  apply QuadForm.ext
  simp [QuadForm.map]

omit [NumberField F] in
theorem hessian_map_self {n : ℕ} (S : QuadForm F n) : S.hessian.map (algebraMap F F) = S.hessian := by
  simp

theorem locVec_stdFrameMat (v : HeightOneSpectrum (𝓞 F)) (j : Fin r) :
    locVec v (fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) i j) =
      fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) (v.adicCompletion F)) i j := by
  ext i
  simp [stdFrameMat, locVec_apply]

theorem frame_mem_latSMul (h : OAf Q') {M : Lat F (r + n')}
    (hM : ∀ j : Fin r, (fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) i j) ∈ M.1) :
    ∀ j : Fin r, (fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) i j) ∈
      (latSMul QB (orthEmbBAf T Q' h) M).1 := by
  intro j
  rw [mem_iff_forall_loc (latSMul QB _ M).2]
  intro v
  rw [loc_latSMul, locVec_stdFrameMat]
  refine ⟨fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) (v.adicCompletion F)) i j, ?_, ?_⟩
  · rw [← locVec_stdFrameMat]; exact locVec_mem_loc v (hM j)
  · simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
    rw [← col_mul]
    exact congrArg (fun A => fun i => A i j) (orthEmbB_mul_stdFrameMat T Q' (v.adicCompletion F) (h v))

theorem latSMul_mem_latGenusB (h : OAf QB) {L M : Lat F (r + n')} (hM : M ∈ latGenus QB L) :
    latSMul QB h M ∈ latGenus QB L := by
  rw [← orbit_eq_genus] at hM ⊢
  obtain ⟨g, rfl⟩ := hM
  exact ⟨h * g, (latSMul_mul QB _ _ L)⟩

/-- **The lattices of the genus containing the standard frame**, $Y = \{M \in \mathrm{gen}(L) : e_0, \dots, e_{r-1} \in M\}$. -/
def CompSetT : Type _ :=
  {M : Lat F (r + n') // M ∈ latGenus QB L ∧ ∀ j : Fin r, (fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) i j) ∈ M.1}

/-- $O(Q')(\mathbb A_f)$ acts on $Y$ through $\mathrm{diag}(1_r, \cdot)$. -/
instance CompSetT.instMulAction : MulAction (OAf Q') (CompSetT T Q' L) where
  smul h M := ⟨latSMul QB (orthEmbBAf T Q' h) M.1, latSMul_mem_latGenusB T Q' _ M.2.1,
    frame_mem_latSMul T Q' h M.2.2⟩
  one_smul M := Subtype.ext (by
    show latSMul QB (orthEmbBAf T Q' 1) M.1 = M.1
    rw [map_one]; exact (latAction QB).one_smul M.1)
  mul_smul a b M := Subtype.ext (by
    show latSMul QB (orthEmbBAf T Q' (a * b)) M.1 =
      latSMul QB (orthEmbBAf T Q' a) (latSMul QB (orthEmbBAf T Q' b) M.1)
    rw [map_mul, latSMul_mul])

theorem CompSetT.smul_val (h : OAf Q') (M : CompSetT T Q' L) :
    (h • M).1 = latSMul QB (orthEmbBAf T Q' h) M.1 := rfl

/-- **The weight of a local type** $t$: $w(t) = [K_0' : K_t\cap K_0']/[K_t : K_t\cap K_0']$, $K_t$ the stabilizer of `t.out`. -/
@[kb "weil1982" "§3.5 [unverified locator]"]
def typeWeightT (t : orbitRel.Quotient (OAf Q') (CompSetT T Q' L)) : ℝ :=
  ((stabilizer (OAf Q') t.out).relIndex (locStab Q' (stdLat F n')) : ℝ) /
    ((locStab Q' (stdLat F n')).relIndex (stabilizer (OAf Q') t.out) : ℝ)

/-- **The stabilizer of a type** containing $M$: $K_M = \{h : \mathrm{diag}(1_r, h) \in O(\hat M)\}$. -/
theorem stabilizer_compSetT (y : CompSetT T Q' L) :
    stabilizer (OAf Q') y = (locStab QB y.1).comap (orthEmbBAf T Q') := by
  ext h
  rw [mem_stabilizer_iff, Subgroup.mem_comap, ← stabilizer_eq_locStab QB]
  rw [@MulAction.mem_stabilizer_iff _ _ _ (latAction QB)]
  constructor
  · intro hh; exact congrArg Subtype.val hh
  · intro hh; exact Subtype.ext hh

/-! #### Witt's theorem: from pairs to $Y$ -/

/-- The standard frame as a point of the level set. -/
def stdLevel : levelSMAT QB T := ⟨stdFrameMat, compMat_stdFrameMat T Q'⟩

theorem hT_map (hT : T.Nondegenerate) : (T.hessian.map (algebraMap F F)).det ≠ 0 := by
  rw [hessian_map_self]; exact hT

/-- **Witt transitivity** on the level set: every frame $X$ of $T$ is $\gamma E$. -/
theorem transitive_levelT (hQ : (QB).Nondegenerate) (hT : T.Nondegenerate) (x : levelSMAT QB T) :
    ∃ γ : orthGroup QB F, γ • stdLevel T Q' = x := by
  have hQ' : ((QB).hessian.map (algebraMap F F)).det ≠ 0 := by
    rw [hessian_map_self]; exact hQ
  obtain ⟨γ, hγ⟩ := exists_orthGroup_mul_stdFrameMat T Q' F hQ' (hT_map T hT)
    (X := x.1) (by rw [map_self_quadForm, map_self_quadForm]; exact x.2)
  exact ⟨γ, Subtype.ext hγ⟩

/-- The stabilizer of $E$ in $O(T\perp Q')(F)$. -/
abbrev Stab₀T : Subgroup (orthGroup QB F) := stabilizer (orthGroup QB F) (stdLevel T Q')

/-- $O(Q')(F) \to \mathrm{Stab}(E)$, $g \mapsto \mathrm{diag}(1_r, g)$. -/
def orthEmbStabT : orthGroup Q' F →* Stab₀T T Q' where
  toFun g := ⟨orthEmbB T Q' F g, mem_stabilizer_iff.mpr (Subtype.ext (orthEmbB_mul_stdFrameMat T Q' F g))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem orthEmbStabT_bijective (hT : T.Nondegenerate) : Function.Bijective (orthEmbStabT T Q') := by
  constructor
  · intro a b h
    exact orthEmbB_injective T Q' F (congrArg Subtype.val h)
  · intro s
    have hs : ((s : orthGroup QB F) : GL (Fin (r + n')) F).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) =
        stdFrameMat :=
      congrArg Subtype.val (mem_stabilizer_iff.mp s.2)
    obtain ⟨g, hg⟩ := exists_orthEmbB_eq T Q' F (hT_map T hT) s hs
    exact ⟨g, Subtype.ext hg⟩

/-- **$\mathrm{Stab}_{O(T\perp Q')(F)}(E) \cong O(Q')(F)$**, embedded in $O(Q')(\mathbb A_f)$ as rational points. -/
def stabEquivT (hT : T.Nondegenerate) : Stab₀T T Q' ≃* ratPoints Q' :=
  (MulEquiv.ofBijective _ (orthEmbStabT_bijective T Q' hT)).symm.trans
    (MonoidHom.ofInjective (diagF_injective Q'))

theorem stabEquivT_smul (hT : T.Nondegenerate) (s : Stab₀T T Q') (M : Lat F (r + n')) :
    latSMul QB (orthEmbBAf T Q' (stabEquivT T Q' hT s : OAf Q')) M = (s : orthGroup QB F) • M := by
  set g' := (MulEquiv.ofBijective _ (orthEmbStabT_bijective T Q' hT)).symm s
  have hs : orthEmbStabT T Q' g' = s :=
    MulEquiv.apply_symm_apply (MulEquiv.ofBijective (orthEmbStabT T Q') (orthEmbStabT_bijective T Q' hT)) s
  have h1 : (stabEquivT T Q' hT s : OAf Q') = diagF Q' g' := rfl
  rw [h1, orthEmbBAf_diagF, diagF_smul, ratAct_smul, ← hs]
  rfl

/-- The fibre of the pairs over $E$. -/
abbrev Fib₀T : Type _ := {p : pairSMAT QB L T // pairToLevelT QB L T p = stdLevel T Q'}

@[instance_reducible]
def fibActT : MulAction (Stab₀T T Q') (Fib₀T T Q' L) :=
  fiberAction (pairToLevelT QB L T) (pairToLevelT_smul QB L T) (stdLevel T Q')

attribute [local instance] fibActT

theorem fib_vecT (p : Fib₀T T Q' L) :
    (p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).2 = stdFrameMat :=
  congrArg Subtype.val p.2

/-- A pair $(M, E)$ gives $M \in Y$. -/
def fibToCompT (p : Fib₀T T Q' L) : CompSetT T Q' L :=
  ⟨(p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).1, p.1.2.1, fun j => by
    have h := p.1.2.2.1 j
    rw [fib_vecT T Q' L p] at h
    exact h⟩

/-- $M \in Y$ gives the pair $(M, E)$. -/
def compToFibT (y : CompSetT T Q' L) : Fib₀T T Q' L :=
  ⟨⟨(y.1, stdFrameMat), y.2.1, y.2.2, compMat_stdFrameMat T Q'⟩, rfl⟩

theorem fibToCompT_compToFibT (y : CompSetT T Q' L) : fibToCompT T Q' L (compToFibT T Q' L y) = y := rfl

theorem fibT_smul_val (s : Stab₀T T Q') (p : Fib₀T T Q' L) :
    ((s • p).1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F) =
      ((s : orthGroup QB F) • (p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).1,
        (s : orthGroup QB F) • (p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).2) := rfl

theorem smul_fibT_iff (hT : T.Nondegenerate) (s : Stab₀T T Q') (a b : Fib₀T T Q' L) :
    s • b = a ↔ (stabEquivT T Q' hT s : OAf Q') • fibToCompT T Q' L b = fibToCompT T Q' L a := by
  constructor
  · intro h
    apply Subtype.ext
    rw [CompSetT.smul_val, stabEquivT_smul]
    have := congrArg (fun p : Fib₀T T Q' L => (p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).1) h
    simp only [fibT_smul_val] at this
    exact this
  · intro h
    have h1 := congrArg Subtype.val h
    rw [CompSetT.smul_val, stabEquivT_smul] at h1
    apply Subtype.ext; apply Subtype.ext
    rw [fibT_smul_val]
    refine Prod.ext h1 ?_
    show (s : orthGroup QB F) • (b.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).2 =
      (a.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).2
    rw [fib_vecT, fib_vecT]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp s.2)

/-- **The pairs over $E$ are $Y$.** -/
theorem orbitMass_fibT_eq (hT : T.Nondegenerate) :
    orbitMass (Stab₀T T Q') (Fib₀T T Q' L) = orbitMass (ratPoints Q') (CompSetT T Q' L) := by
  refine orbitMass_eq_of_map (fibToCompT T Q' L) ?_ ?_ ?_
  · intro a b
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨stabEquivT T Q' hT s, (smul_fibT_iff T Q' L hT s a b).mp hs⟩
    · rintro ⟨γ, hγ⟩
      refine ⟨(stabEquivT T Q' hT).symm γ, (smul_fibT_iff T Q' L hT _ a b).mpr ?_⟩
      rw [MulEquiv.apply_symm_apply]
      exact hγ
  · intro y
    exact ⟨compToFibT T Q' L y, mem_orbit_self y⟩
  · intro x
    refine (Nat.card_congr ((stabEquivT T Q' hT).toEquiv.subtypeEquiv fun s => ?_)).symm
    rw [mem_stabilizer_iff, mem_stabilizer_iff]
    exact smul_fibT_iff T Q' L hT s x x

theorem finite_orbits_pairsT (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) :
    Finite (orbitRel.Quotient (orthGroup QB F) (pairSMAT QB L T)) := by
  have := finite_orbits_gen hpd L hLi
  exact finite_orbits_of_fiber (pairToGenT QB L T) (pairToGenT_smul QB L T) fun M => by
    have := finite_repSetT hpd (M := (M : Lat F (r + n'))) (SameGenus.isIntegral QB hLi M.2) T
    exact Finite.of_equiv _ (fiberEquivT QB L T M).symm

theorem fibT_orbit_of (a b : Fib₀T T Q' L) (h : a.1 ∈ orbit (orthGroup QB F) b.1) :
    a ∈ orbit (Stab₀T T Q') b := by
  obtain ⟨γ, hγ⟩ := h
  have hγ' : γ • b.1 = a.1 := hγ
  have hγs : γ ∈ Stab₀T T Q' := by
    rw [mem_stabilizer_iff]
    have := congrArg (pairToLevelT QB L T) hγ'
    rw [pairToLevelT_smul, b.2, a.2] at this
    exact this
  exact ⟨⟨γ, hγs⟩, Subtype.ext hγ'⟩

theorem finite_orbits_fibT (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) :
    Finite (orbitRel.Quotient (Stab₀T T Q') (Fib₀T T Q' L)) := by
  have := finite_orbits_pairsT T Q' L hpd hLi
  exact finite_orbits_of_map (H₂ := orthGroup QB F) (fun p : Fib₀T T Q' L => p.1) (fibT_orbit_of T Q' L)

theorem finite_orbits_compSetT (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) (hT : T.Nondegenerate) :
    Finite (orbitRel.Quotient (ratPoints Q') (CompSetT T Q' L)) := by
  have := finite_orbits_fibT T Q' L hpd hLi
  refine finite_orbits_of_map (H₂ := Stab₀T T Q') (compToFibT T Q' L) ?_
  rintro a b ⟨s, hs⟩
  have h := (smul_fibT_iff T Q' L hT s (compToFibT T Q' L a) (compToFibT T Q' L b)).mp hs
  rw [fibToCompT_compToFibT, fibToCompT_compToFibT] at h
  exact ⟨stabEquivT T Q' hT s, h⟩

/-- **The global reduction for frames:** $\mathrm{repMass}_T(L) = \sum_t \mathrm{dcMass}(O(Q')(F), K_t)$. -/
theorem repMassT_eq_finsum_dcMass (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) (hT : T.Nondegenerate) :
    repMassT QB L T = ∑ᶠ t : orbitRel.Quotient (OAf Q') (CompSetT T Q' L),
      dcMass (ratPoints Q') (stabilizer (OAf Q') t.out) := by
  have := finite_orbits_compSetT T Q' L hpd hLi hT
  rw [repMassT_eq_orbitMass_pairs hpd L hLi T,
    orbitMass_eq_fiber_of_transitive (pairToLevelT QB L T) (pairToLevelT_smul QB L T) (stdLevel T Q')
      (transitive_levelT T Q' hpd.nondegenerate hT)]
  rw [show @orbitMass (Stab₀T T Q') (Fib₀T T Q' L) _ (fiberAction (pairToLevelT QB L T) (pairToLevelT_smul QB L T)
    (stdLevel T Q')) = orbitMass (Stab₀T T Q') (Fib₀T T Q' L) from rfl, orbitMass_fibT_eq T Q' L hT]
  exact orbitMass_eq_finsum_dcMass (ratPoints Q')

theorem commensurable_stabilizer_compSetT (y : CompSetT T Q' L) :
    (stabilizer (OAf Q') y).Commensurable (locStab Q' (stdLat F n')) := by
  rw [stabilizer_compSetT, ← comap_orthEmbBAf_locStab_intVec T Q']
  exact (commensurable_locStab QB (stdLat F (r + n')) y.1).comap _

/-- **The mass of a type:** $\mathrm{dcMass}(O(Q')(F), K_t) = \mathrm{Mass}(\mathcal O_F^{n'}, Q')\cdot w(t)$. -/
theorem dcMass_type_eqT (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1)
    (t : orbitRel.Quotient (OAf Q') (CompSetT T Q' L)) :
    dcMass (ratPoints Q') (stabilizer (OAf Q') t.out) = mass Q' (stdLat F n') * typeWeightT T Q' L t := by
  have hK := commensurable_stabilizer_compSetT T Q' L t.out
  have := finite_orbits hpd' (stdLat F n') hLi'
  have h := dcMass_mul_idxVol (ratPoints Q') (locStab Q' (stdLat F n')) (stabilizer (OAf Q') t.out) 1 hK
    (finite_stabilizer hpd' (stdLat F n') hLi')
  rw [one_mul, ← mass_eq_dcMass] at h
  have h1 : ((stabilizer (OAf Q') t.out).relIndex (locStab Q' (stdLat F n')) : ℝ) ≠ 0 := by
    exact_mod_cast hK.1.relIndex_ne_zero
  have h2 : ((locStab Q' (stdLat F n')).relIndex (stabilizer (OAf Q') t.out) : ℝ) ≠ 0 := by
    exact_mod_cast hK.2.relIndex_ne_zero
  unfold idxVol at h
  unfold typeWeightT
  rw [← h]
  field_simp

theorem finite_typesT (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) (hT : T.Nondegenerate) :
    Finite (orbitRel.Quotient (OAf Q') (CompSetT T Q' L)) := by
  have := finite_orbits_compSetT T Q' L hpd hLi hT
  refine Finite.of_surjective (fun ω : orbitRel.Quotient (ratPoints Q') (CompSetT T Q' L) =>
    (Quotient.mk'' ω.out : orbitRel.Quotient (OAf Q') (CompSetT T Q' L))) fun t => ?_
  refine ⟨Quotient.mk'' t.out, ?_⟩
  conv_rhs => rw [← Quotient.out_eq' t]
  apply Quotient.sound'
  rw [orbitRel_apply]
  obtain ⟨γ, hγ⟩ := out_mem_orbit (Quotient.mk'' t.out : orbitRel.Quotient (ratPoints Q') (CompSetT T Q' L))
    t.out rfl
  exact ⟨(γ : OAf Q'), hγ⟩

/-- **Weil's orbit counting for frames** (see the module docstring). -/
@[kb "weil1982" "§3.4-3.5 (orbit counting) [unverified locator]"]
theorem repMassT_eq_mass_mul (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) (hT : T.Nondegenerate)
    (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1) :
    repMassT QB L T = mass Q' (stdLat F n') * ∑ᶠ t : orbitRel.Quotient (OAf Q') (CompSetT T Q' L), typeWeightT T Q' L t := by
  have := finite_typesT T Q' L hpd hLi hT
  rw [repMassT_eq_finsum_dcMass T Q' L hpd hLi hT, mul_finsum]
  exact finsum_congr fun t => dcMass_type_eqT T Q' L hpd' hLi' t

end Split

end QuadFormsKB.Tamagawa.Frames
