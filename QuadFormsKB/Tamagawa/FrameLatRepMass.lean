/-
# Weil's reduction to complements for embeddings of lattices

**Layer:** lattices in $(F^N, Q)$ over a number field $F$, the finite adelic orthogonal group, the orthogonal sum $T\perp Q'$; the
represented object is a quadratic lattice $T = (T_\ell, T)$ (`FrameLatDefs.lean`).

**Proves**
* `repCountLat_stdLat`, `repMassLat_stdLat`: for $T_\ell = \mathcal O_F^r$ the counts are the `repCountT`, `repMassT`;
* `repMassLat_compMat`: transport along $g \in \mathrm{GL}_N(F)$;
* `repMassLat_eq_zero_of_not_rep`: no frame of $T$ over $F$, no embedding;
* `repMassLat_pos_of_mem`: an embedding into $L$ makes the genus count positive;
* **`repMassLat_eq_mass_mul`** (Weil's orbit counting, Weil 1982, §3.4–3.5 [unverified locator]): for $Q = T\perp Q'$ totally positive
  definite and $L$ integral,
  $$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r(M, T)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^{n'}, Q')\sum_{t\in O(Q')(\mathbb A_f)\backslash Y}w(t),
  \qquad Y = \{M \in \mathrm{gen}(L) : E\,T_\ell \subseteq M\}.$$
  *Proof:* as `repMassT_eq_mass_mul`, with the condition "the columns of $X$ lie in $M$" replaced by $X\,T_\ell \subseteq M$.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameLatDefs

open NumberField IsDedekindDomain Matrix MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.FramesLat

open QuadFormsKB.Tamagawa Lattices Frames QuadFormsKB.HilbertModular

section Basic

variable {F : Type*} [Field F] [NumberField F] {N r : ℕ} (Q : QuadForm F N)

/-- For $T_\ell = \mathcal O_F^r$, embeddings of $T_\ell$ are frames with columns in $M$. -/
theorem repCountLat_stdLat (M : Lat F N) (T : QuadForm F r) : repCountLat Q M (stdLat F r) T = repCountT Q M T := by
  have key : ∀ X : Matrix (Fin N) (Fin r) F,
      (∀ t ∈ (stdLat F r).1, X *ᵥ t ∈ M.1) ↔ ∀ j, (fun i => X i j) ∈ M.1 := by
    intro X
    constructor
    · intro h j
      have h1 : (Pi.single j (1 : F) : Fin r → F) ∈ (stdLat F r).1 :=
        mem_intVec_iff_exists.mpr ⟨Pi.single j 1, by ext k; by_cases hk : k = j <;> simp [hk, intCoe]⟩
      have := h _ h1
      rwa [show X *ᵥ (Pi.single j (1 : F) : Fin r → F) = fun i => X i j by
        ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]] at this
    · intro h t ht
      obtain ⟨y, rfl⟩ := mem_intVec_iff_exists.mp ht
      have : X *ᵥ intCoe y = ∑ j, (y j) • (fun i => X i j) := by
        ext i
        simp [Matrix.mulVec, dotProduct, intCoe, Finset.sum_apply, Algebra.smul_def, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => M.1.smul_mem _ (h j)
  unfold repCountLat repCountT
  exact Nat.card_congr (Equiv.subtypeEquivRight fun X => and_congr_left_iff.mpr fun _ => key X)

theorem repMassLat_stdLat (L : Lat F N) (T : QuadForm F r) : repMassLat Q L (stdLat F r) T = repMassT Q L T := by
  unfold repMassLat repMassT
  refine finsum_mem_congr rfl fun c _ => ?_
  obtain ⟨M, rfl⟩ := Quotient.exists_rep c
  show ((repCountLat Q M (stdLat F r) T : ℕ) : ℝ) / _ = ((repCountT Q M T : ℕ) : ℝ) / _
  rw [repCountLat_stdLat]

/-- No frame of $T$ over $F$: no embedding. -/
theorem repMassLat_eq_zero_of_not_rep (L : Lat F N) (Tl : Lat F r) (T : QuadForm F r)
    (h : ¬ ∃ X : Matrix (Fin N) (Fin r) F, Q.compMat X = T) : repMassLat Q L Tl T = 0 := by
  unfold repMassLat
  have hz : ∀ c ∈ genusClasses Q L, (LatClass.repCountLat Q c Tl T : ℝ) / LatClass.autCard Q c = 0 := by
    intro c _
    obtain ⟨M, rfl⟩ := Quotient.exists_rep c
    have h0 : repCountLat Q M Tl T = 0 := by
      unfold repCountLat
      rw [Nat.card_eq_zero]
      left
      exact ⟨fun X => h ⟨X.1, X.2.2⟩⟩
    show ((repCountLat Q M Tl T : ℕ) : ℝ) / _ = 0
    rw [h0, Nat.cast_zero, zero_div]
  exact (finsum_mem_congr rfl hz).trans (finsum_mem_zero _)

/-- **Finitely many embeddings:** for totally positive definite $Q$ and an integral lattice $M$, $r(M, T) < \infty$
(multiplying $X$ by $d\cdot 1_r$ with $d\,\mathcal O_F^r \subseteq T_\ell$ gives a frame with columns in $M$, `finite_repSetT`). -/
theorem finite_repSetLat {Q : QuadForm F N} (hQ : IsTotallyPosDef Q) {M : Lat F N} (hMi : IsIntegral Q M.1)
    (Tl : Lat F r) (T : QuadForm F r) :
    Finite {X : Matrix (Fin N) (Fin r) F // (∀ t ∈ Tl.1, X *ᵥ t ∈ M.1) ∧ Q.compMat X = T} := by
  classical
  obtain ⟨d, hd0, hd, -⟩ := exists_global_bounds Tl.2
  set c : F := algebraMap (𝓞 F) F d with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  set D : Matrix (Fin r) (Fin r) F := Matrix.diagonal fun _ => c
  have := finite_repSetT hQ hMi (T.compMat D)
  refine Finite.of_injective (fun X => (⟨X.1 * D, fun j => ?_, ?_⟩ :
    {Y : Matrix (Fin N) (Fin r) F // (∀ j, (fun i => Y i j) ∈ M.1) ∧ Q.compMat Y = T.compMat D})) ?_
  · rw [col_mul]
    have h1 : (Pi.single j (1 : F) : Fin r → F) ∈ (intVec : Submodule (𝓞 F) (Fin r → F)) :=
      mem_intVec_iff_exists.mpr ⟨Pi.single j 1, by ext k; by_cases hk : k = j <;> simp [hk, intCoe]⟩
    have h2 := X.2.1 _ (hd _ h1)
    convert h2 using 2
    ext k
    by_cases hk : k = j <;> simp [D, hk, hc, Algebra.smul_def]
  · rw [← QuadForm.compMat_mul, X.2.2]
  · intro X Y h
    apply Subtype.ext
    ext i j
    have := congrFun (congrFun (congrArg Subtype.val h) i) j
    simp only [D, Matrix.mul_diagonal] at this
    exact mul_right_cancel₀ hc0 this

end Basic

/-! ### Rational isometries acting on pairs $(M, X)$ -/

section Pairs

variable {F : Type*} [Field F] [NumberField F] {N r : ℕ} (Q : QuadForm F N)

attribute [local instance] ratAct frameAct

variable (L : Lat F N) (Tl : Lat F r) (T : QuadForm F r)

/-- **The pairs** $(M, X)$ with $M \in \mathrm{gen}(L)$, $X\,T_\ell \subseteq M$, $Q\circ X = T$, as an $O(V)(F)$-set. -/
def pairSMAL : SubMulAction (orthGroup Q F) (Lat F N × Matrix (Fin N) (Fin r) F) where
  carrier := {p | p.1 ∈ latGenus Q L ∧ (∀ t ∈ Tl.1, p.2 *ᵥ t ∈ p.1.1) ∧ Q.compMat p.2 = T}
  smul_mem' γ p hp := ⟨image_mem_latGenus Q hp.1 γ, fun t ht => by
      have h := mulVec_mem_glImage (γ := (γ : GL (Fin N) F)) (hp.2.1 t ht)
      rw [mulVec_mulVec] at h
      exact h, (compMat_orth Q γ.2 p.2).trans hp.2.2⟩

/-- The projection of a pair $(M, X)$ to the lattice $M$. -/
def pairToGenL : pairSMAL Q L Tl T → genSMA Q L := fun p => ⟨p.1.1, p.2.1⟩

/-- The projection of a pair $(M, X)$ to the frame $X$. -/
def pairToLevelL : pairSMAL Q L Tl T → levelSMAT Q T := fun p => ⟨p.1.2, p.2.2.2⟩

theorem pairToGenL_smul (γ : orthGroup Q F) (p : pairSMAL Q L Tl T) :
    pairToGenL Q L Tl T (γ • p) = γ • pairToGenL Q L Tl T p := rfl

theorem pairToLevelL_smul (γ : orthGroup Q F) (p : pairSMAL Q L Tl T) :
    pairToLevelL Q L Tl T (γ • p) = γ • pairToLevelL Q L Tl T p := rfl

/-- The fibre of the projection to $M$ is the set of embeddings of $T$ in $M$. -/
def fiberEquivL (M : genSMA Q L) :
    {p : pairSMAL Q L Tl T // pairToGenL Q L Tl T p = M} ≃
      {X : Matrix (Fin N) (Fin r) F // (∀ t ∈ Tl.1, X *ᵥ t ∈ (M : Lat F N).1) ∧ Q.compMat X = T} :=
    { toFun := fun p => ⟨p.1.1.2, fun t ht => by
        have h : (p.1 : Lat F N × Matrix (Fin N) (Fin r) F).1 = M := congrArg Subtype.val p.2
        have h2 := p.1.2.2.1 t ht
        rw [h] at h2
        exact h2, p.1.2.2.2⟩
      invFun := fun X => ⟨⟨((M : Lat F N), X.1), M.2, X.2.1, X.2.2⟩, rfl⟩
      left_inv := fun p => by
        rcases p with ⟨⟨⟨M', w⟩, hp⟩, hpM⟩
        have : M' = (M : Lat F N) := congrArg Subtype.val hpM
        subst this
        rfl
      right_inv := fun X => rfl }

theorem card_fiber_pairToGenL (M : genSMA Q L) :
    Nat.card {p : pairSMAL Q L Tl T // pairToGenL Q L Tl T p = M} = repCountLat Q (M : Lat F N) Tl T :=
  Nat.card_congr (fiberEquivL Q L Tl T M)

/-- **The weighted number of embeddings as an orbit mass of pairs.** -/
theorem repMassLat_eq_orbitMass_pairs {Q : QuadForm F N} (hQ : IsTotallyPosDef Q) (L : Lat F N)
    (hLi : IsIntegral Q L.1) (Tl : Lat F r) (T : QuadForm F r) :
    repMassLat Q L Tl T = orbitMass (orthGroup Q F) (pairSMAL Q L Tl T) := by
  have := finite_orbits_gen hQ L hLi
  have hstab : ∀ M : genSMA Q L, Finite (stabilizer (orthGroup Q F) M) := by
    intro M
    have := finite_autLat hQ (M : Lat F N).2 (SameGenus.isIntegral Q hLi M.2)
    apply Nat.finite_of_card_ne_zero
    rw [card_stabilizer_gen]; exact Nat.card_pos.ne'
  have hfin : ∀ M : genSMA Q L, Finite {p : pairSMAL Q L Tl T // pairToGenL Q L Tl T p = M} := by
    intro M
    have := finite_repSetLat hQ (M := (M : Lat F N)) (SameGenus.isIntegral Q hLi M.2) Tl T
    exact Finite.of_equiv _ (fiberEquivL Q L Tl T M).symm
  rw [orbitMass_eq_finsum_fiber (pairToGenL Q L Tl T) (pairToGenL_smul Q L Tl T) hstab hfin]
  unfold repMassLat
  rw [← orbitClass_image Q L, finsum_mem_image (orbitClass_injective Q L).injOn, finsum_mem_univ]
  congr 1
  ext ω
  rw [card_fiber_pairToGenL, card_stabilizer_gen]
  rfl

end Pairs

section Transport

variable {F : Type*} [Field F] [NumberField F] {N r : ℕ}

attribute [local instance] ratAct frameAct

/-- **Transport of the embedding number**: $r(g^{-1}M, Q\circ g;\,T) = r(M, Q;\,T)$, by $X \mapsto gX$. -/
theorem repCountLat_compMat (Q₁ : QuadForm F N) (g : GL (Fin N) F) (M : Lat F N) (Tl : Lat F r) (T : QuadForm F r) :
    repCountLat (Q₁.compMat g.val) (Lat.image g⁻¹ M) Tl T = repCountLat Q₁ M Tl T := by
  refine Nat.card_congr
    { toFun := fun X => ⟨g.val * X.1, ?_, ?_⟩
      invFun := fun X => ⟨g⁻¹.val * X.1, ?_, ?_⟩
      left_inv := fun X => Subtype.ext (by
        show g⁻¹.val * (g.val * X.1) = X.1
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul])
      right_inv := fun X => Subtype.ext (by
        show g.val * (g⁻¹.val * X.1) = X.1
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]) }
  · intro t ht
    obtain ⟨y, hy, hyv⟩ := (mem_glImage).mp (X.2.1 t ht)
    rw [← Matrix.mulVec_mulVec, ← hyv, mulVec_mulVec, Units.mul_inv, one_mulVec]; exact hy
  · rw [← QuadForm.compMat_mul]; exact X.2.2
  · intro t ht
    rw [← Matrix.mulVec_mulVec]; exact mulVec_mem_glImage (X.2.1 t ht)
  · rw [QuadForm.compMat_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]; exact X.2.2

/-- **Transport along a change of coordinates**: $\mathrm{repMass}(Q\circ g, g^{-1}L, T) = \mathrm{repMass}(Q, L, T)$. -/
theorem repMassLat_compMat {Q : QuadForm F N} (hpd : IsTotallyPosDef Q) (g : GL (Fin N) F) {L : Lat F N}
    (hLi : IsIntegral Q L.1) (Tl : Lat F r) (T : QuadForm F r) :
    repMassLat (Q.compMat g.val) (Lat.image g⁻¹ L) Tl T = repMassLat Q L Tl T := by
  set Q₁ := Q
  set Q₂ := Q₁.compMat g.val
  set L₂ := Lat.image g⁻¹ L
  rw [repMassLat_eq_orbitMass_pairs (isTotallyPosDef_compMat Q₁ g hpd) L₂ (isIntegral_compMat Q₁ g hLi) Tl T,
    repMassLat_eq_orbitMass_pairs hpd L hLi Tl T]
  let φ : orthGroup Q₂ F →* orthGroup Q₁ F :=
    { toFun := fun γ => ⟨g * (γ : GL (Fin N) F) * g⁻¹, by
        have := (conj_mem_orthGroup_iff Q₁ g F γ).mp γ.2
        simpa [GeneralLinearGroup.map] using this⟩
      map_one' := by ext1; simp
      map_mul' := fun a b => by ext1; simp [mul_assoc] }
  have hφ : ∀ γ₁ : orthGroup Q₁ F, ∃ γ : orthGroup Q₂ F, φ γ = γ₁ := by
    intro γ₁
    refine ⟨⟨g⁻¹ * (γ₁ : GL (Fin N) F) * g, (conj_mem_orthGroup_iff Q₁ g F _).mpr ?_⟩, ?_⟩
    · have : GeneralLinearGroup.map (algebraMap F F) g * (g⁻¹ * (γ₁ : GL (Fin N) F) * g) *
          (GeneralLinearGroup.map (algebraMap F F) g)⁻¹ = γ₁ := by
        have hg : GeneralLinearGroup.map (algebraMap F F) g = g := by ext; simp [GeneralLinearGroup.map]
        rw [hg]; group
      rw [this]; exact γ₁.2
    · apply Subtype.ext
      show g * (g⁻¹ * (γ₁ : GL (Fin N) F) * g) * g⁻¹ = γ₁
      group
  have hφinj : Function.Injective φ := by
    intro a b h
    have := congrArg (fun γ : orthGroup Q₁ F => g⁻¹ * (γ : GL (Fin N) F) * g) h
    apply Subtype.ext
    simpa [φ, mul_assoc] using this
  let P : pairSMAL Q₂ L₂ Tl T → pairSMAL Q₁ L Tl T := fun p =>
    ⟨(Lat.image g p.1.1, g.val * p.1.2), by
      obtain ⟨hM, hx, hQ⟩ := p.2
      refine ⟨?_, fun t ht => ?_, ?_⟩
      · show SameGenus Q₁ L.1 (glImage g p.1.1.1)
        have := sameGenus_compMat Q₁ g hM
        rwa [show glImage g L₂.1 = L.1 from glImage_inv_glImage g L.1] at this
      · have h := mulVec_mem_glImage (γ := g) (hx t ht)
        rw [mulVec_mulVec] at h
        exact h
      · rw [← QuadForm.compMat_mul]; exact hQ⟩
  have hPsmul : ∀ (γ : orthGroup Q₂ F) (p : pairSMAL Q₂ L₂ Tl T), P (γ • p) = φ γ • P p := by
    intro γ p
    apply Subtype.ext
    show (Lat.image g (Lat.image (γ : GL (Fin N) F) p.1.1), g.val * ((γ : GL (Fin N) F).val * p.1.2)) =
      (Lat.image (g * (γ : GL (Fin N) F) * g⁻¹) (Lat.image g p.1.1),
        (g * (γ : GL (Fin N) F) * g⁻¹).val * (g.val * p.1.2))
    refine Prod.ext (Subtype.ext ?_) ?_
    · show glImage g (glImage _ _) = glImage _ (glImage g _)
      rw [← glImage_mul, ← glImage_mul, inv_mul_cancel_right]
    · have hc : g⁻¹.val * (g.val * p.1.2) = p.1.2 := by
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      simp only [Units.val_mul, Matrix.mul_assoc, hc]
  have hPinj : Function.Injective P := by
    intro a b h
    have h1 := congrArg (fun p : pairSMAL Q₁ L Tl T => (p : Lat F N × Matrix (Fin N) (Fin r) F)) h
    simp only [P, Prod.mk.injEq] at h1
    apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) ?_
    · have := congrArg (fun M : Lat F N => glImage g⁻¹ M.1) h1.1
      simpa [Lat.image, ← glImage_mul, glImage_one] using this
    · have := congrArg (fun x => g⁻¹.val * x) h1.2
      simpa [← Matrix.mul_assoc] using this
  have hPsurj : Function.Surjective P := by
    intro q
    obtain ⟨hM, hx, hQ⟩ := q.2
    refine ⟨⟨(Lat.image g⁻¹ q.1.1, g⁻¹.val * q.1.2), ?_, fun t ht => ?_, ?_⟩, ?_⟩
    · show SameGenus Q₂ (glImage g⁻¹ L.1) (glImage g⁻¹ q.1.1.1)
      apply sameGenus_compMat'
      rw [glImage_inv_glImage, glImage_inv_glImage]; exact hM
    · have h := mulVec_mem_glImage (γ := g⁻¹) (hx t ht)
      rw [mulVec_mulVec] at h
      exact h
    · change (Q₁.compMat g.val).compMat (g⁻¹.val * q.1.2) = T
      rw [QuadForm.compMat_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      exact hQ
    · apply Subtype.ext
      refine Prod.ext (Subtype.ext ?_) ?_
      · exact glImage_inv_glImage g q.1.1.1
      · show g.val * (g⁻¹.val * q.1.2) = q.1.2
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  refine orbitMass_eq_of_map P (fun a b => ?_) (fun y => ?_) (fun x => ?_)
  · constructor
    · rintro ⟨γ, rfl⟩; exact ⟨φ γ, (hPsmul γ b).symm⟩
    · rintro ⟨γ₁, hγ₁⟩
      obtain ⟨γ, rfl⟩ := hφ γ₁
      exact ⟨γ, hPinj (by rw [hPsmul]; exact hγ₁)⟩
  · obtain ⟨x, hx⟩ := hPsurj y
    exact ⟨x, by rw [hx]; exact mem_orbit_self y⟩
  · refine Nat.card_congr ((MulEquiv.ofBijective φ ⟨hφinj, fun γ₁ => hφ γ₁⟩).toEquiv.subtypeEquiv fun γ => ?_).symm
    rw [mem_stabilizer_iff, mem_stabilizer_iff]
    show γ • x = x ↔ φ γ • P x = P x
    rw [← hPsmul]
    exact hPinj.eq_iff.symm

end Transport

section Positivity

variable {F : Type*} [Field F] [NumberField F] {N r : ℕ}

/-- **Positivity:** if $T$ embeds into $L$ itself, the genus count is positive. -/
theorem repMassLat_pos_of_mem {Q : QuadForm F N} (hpd : IsTotallyPosDef Q) {L : Lat F N} (hLi : IsIntegral Q L.1)
    (Tl : Lat F r) (T : QuadForm F r) (X : Matrix (Fin N) (Fin r) F) (hX : ∀ t ∈ Tl.1, X *ᵥ t ∈ L.1)
    (hXT : Q.compMat X = T) : 0 < repMassLat Q L Tl T := by
  have hfin := genusClasses_finite hpd L hLi
  unfold repMassLat
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hc₀ : (Quotient.mk (latSetoid Q) L : LatClass Q) ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨L, rfl, SameGenus.refl Q L.1⟩
  have hterm : ∀ c ∈ hfin.toFinset, 0 ≤ (LatClass.repCountLat Q c Tl T : ℝ) / LatClass.autCard Q c :=
    fun c _ => by positivity
  refine Finset.sum_pos' hterm ⟨_, hc₀, ?_⟩
  have h1 : 0 < LatClass.autCard Q (Quotient.mk (latSetoid Q) L : LatClass Q) := by
    show 0 < Nat.card (autLat Q L.1)
    have := finite_autLat hpd L.2 hLi
    exact Nat.card_pos
  have h2 : 0 < LatClass.repCountLat Q (Quotient.mk (latSetoid Q) L : LatClass Q) Tl T := by
    show 0 < repCountLat Q L Tl T
    have := finite_repSetLat hpd hLi Tl T
    have : Nonempty {X : Matrix (Fin N) (Fin r) F // (∀ t ∈ Tl.1, X *ᵥ t ∈ L.1) ∧ Q.compMat X = T} :=
      ⟨⟨X, hX, hXT⟩⟩
    exact Nat.card_pos
  have h1' : (0 : ℝ) < LatClass.autCard Q (Quotient.mk (latSetoid Q) L : LatClass Q) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < LatClass.repCountLat Q (Quotient.mk (latSetoid Q) L : LatClass Q) Tl T := by exact_mod_cast h2
  exact div_pos h2' h1'

end Positivity

/-! ### Weil's orbit counting for embeddings of a lattice -/

section Split

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (T : QuadForm F r) (Q' : QuadForm F n')

local notation "QB" => blockForm T Q'

variable (L : Lat F (r + n')) (Tl : Lat F r)

attribute [local instance] ratAct frameAct

/-- $E\,t$ localizes to $E\,t$: $\iota_\mathfrak p(E t) = E\,\iota_\mathfrak p(t)$. -/
theorem locVec_stdFrameMat_mulVec (v : HeightOneSpectrum (𝓞 F)) (t : Fin r → F) :
    locVec v ((stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) *ᵥ t) =
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) (v.adicCompletion F)) *ᵥ locVec v t := by
  ext i
  simp only [locVec_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [stdFrameMat, Matrix.of_apply]
  split_ifs <;> simp

theorem frame_mem_latSMulL (h : OAf Q') {M : Lat F (r + n')}
    (hM : ∀ t ∈ Tl.1, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) *ᵥ t ∈ M.1) :
    ∀ t ∈ Tl.1, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) *ᵥ t ∈
      (latSMul QB (orthEmbBAf T Q' h) M).1 := by
  intro t ht
  rw [mem_iff_forall_loc (latSMul QB _ M).2]
  intro v
  rw [loc_latSMul]
  refine ⟨locVec v ((stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) *ᵥ t), locVec_mem_loc v (hM t ht), ?_⟩
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  rw [locVec_stdFrameMat_mulVec]
  exact orthEmbB_mulVec_stdFrameMat v T Q' (h v) _

/-- **The lattices of the genus containing $E\,T_\ell$**, $Y = \{M \in \mathrm{gen}(L) : E\,T_\ell \subseteq M\}$. -/
def CompSetL : Type _ :=
  {M : Lat F (r + n') // M ∈ latGenus QB L ∧
    ∀ t ∈ Tl.1, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) *ᵥ t ∈ M.1}

/-- $O(Q')(\mathbb A_f)$ acts on $Y$ through $\mathrm{diag}(1_r, \cdot)$. -/
instance CompSetL.instMulAction : MulAction (OAf Q') (CompSetL T Q' L Tl) where
  smul h M := ⟨latSMul QB (orthEmbBAf T Q' h) M.1, latSMul_mem_latGenusB T Q' _ M.2.1,
    frame_mem_latSMulL T Q' Tl h M.2.2⟩
  one_smul M := Subtype.ext (by
    show latSMul QB (orthEmbBAf T Q' 1) M.1 = M.1
    rw [map_one]; exact (latAction QB).one_smul M.1)
  mul_smul a b M := Subtype.ext (by
    show latSMul QB (orthEmbBAf T Q' (a * b)) M.1 =
      latSMul QB (orthEmbBAf T Q' a) (latSMul QB (orthEmbBAf T Q' b) M.1)
    rw [map_mul, latSMul_mul])

theorem CompSetL.smul_val (h : OAf Q') (M : CompSetL T Q' L Tl) :
    (h • M).1 = latSMul QB (orthEmbBAf T Q' h) M.1 := rfl

/-- **The weight of a local type** $t$: $w(t) = [K_0' : K_t\cap K_0']/[K_t : K_t\cap K_0']$, $K_t$ the stabilizer of `t.out`. -/
@[kb "weil1982" "§3.5 [unverified locator]"]
def typeWeightL (t : orbitRel.Quotient (OAf Q') (CompSetL T Q' L Tl)) : ℝ :=
  ((stabilizer (OAf Q') t.out).relIndex (locStab Q' (stdLat F n')) : ℝ) /
    ((locStab Q' (stdLat F n')).relIndex (stabilizer (OAf Q') t.out) : ℝ)

/-- **The stabilizer of a type** containing $M$: $K_M = \{h : \mathrm{diag}(1_r, h) \in O(\hat M)\}$. -/
theorem stabilizer_compSetL (y : CompSetL T Q' L Tl) :
    stabilizer (OAf Q') y = (locStab QB y.1).comap (orthEmbBAf T Q') := by
  ext h
  rw [mem_stabilizer_iff, Subgroup.mem_comap, ← stabilizer_eq_locStab QB]
  rw [@MulAction.mem_stabilizer_iff _ _ _ (latAction QB)]
  constructor
  · intro hh; exact congrArg Subtype.val hh
  · intro hh; exact Subtype.ext hh

/-- The fibre of the pairs over $E$. -/
abbrev FibL₀ : Type _ := {p : pairSMAL QB L Tl T // pairToLevelL QB L Tl T p = stdLevel T Q'}

@[instance_reducible]
def fibActL : MulAction (Stab₀T T Q') (FibL₀ T Q' L Tl) :=
  fiberAction (pairToLevelL QB L Tl T) (pairToLevelL_smul QB L Tl T) (stdLevel T Q')

attribute [local instance] fibActL

theorem fib_vecL (p : FibL₀ T Q' L Tl) :
    (p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).2 = stdFrameMat :=
  congrArg Subtype.val p.2

/-- A pair $(M, E)$ gives $M \in Y$. -/
def fibToCompL (p : FibL₀ T Q' L Tl) : CompSetL T Q' L Tl :=
  ⟨(p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).1, p.1.2.1, fun t ht => by
    have h := p.1.2.2.1 t ht
    rw [fib_vecL T Q' L Tl p] at h
    exact h⟩

/-- $M \in Y$ gives the pair $(M, E)$. -/
def compToFibL (y : CompSetL T Q' L Tl) : FibL₀ T Q' L Tl :=
  ⟨⟨(y.1, stdFrameMat), y.2.1, y.2.2, compMat_stdFrameMat T Q'⟩, rfl⟩

theorem fibToCompL_compToFibL (y : CompSetL T Q' L Tl) : fibToCompL T Q' L Tl (compToFibL T Q' L Tl y) = y := rfl

theorem fibL_smul_val (s : Stab₀T T Q') (p : FibL₀ T Q' L Tl) :
    ((s • p).1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F) =
      ((s : orthGroup QB F) • (p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).1,
        (s : orthGroup QB F) • (p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).2) := rfl

theorem smul_fibL_iff (hT : T.Nondegenerate) (s : Stab₀T T Q') (a b : FibL₀ T Q' L Tl) :
    s • b = a ↔ (stabEquivT T Q' hT s : OAf Q') • fibToCompL T Q' L Tl b = fibToCompL T Q' L Tl a := by
  constructor
  · intro h
    apply Subtype.ext
    rw [CompSetL.smul_val, stabEquivT_smul]
    have := congrArg (fun p : FibL₀ T Q' L Tl => (p.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).1) h
    simp only [fibL_smul_val] at this
    exact this
  · intro h
    have h1 := congrArg Subtype.val h
    rw [CompSetL.smul_val, stabEquivT_smul] at h1
    apply Subtype.ext; apply Subtype.ext
    rw [fibL_smul_val]
    refine Prod.ext h1 ?_
    show (s : orthGroup QB F) • (b.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).2 =
      (a.1 : Lat F (r + n') × Matrix (Fin (r + n')) (Fin r) F).2
    rw [fib_vecL, fib_vecL]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp s.2)

/-- **The pairs over $E$ are $Y$.** -/
theorem orbitMass_fibL_eq (hT : T.Nondegenerate) :
    orbitMass (Stab₀T T Q') (FibL₀ T Q' L Tl) = orbitMass (ratPoints Q') (CompSetL T Q' L Tl) := by
  refine orbitMass_eq_of_map (fibToCompL T Q' L Tl) ?_ ?_ ?_
  · intro a b
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨stabEquivT T Q' hT s, (smul_fibL_iff T Q' L Tl hT s a b).mp hs⟩
    · rintro ⟨γ, hγ⟩
      refine ⟨(stabEquivT T Q' hT).symm γ, (smul_fibL_iff T Q' L Tl hT _ a b).mpr ?_⟩
      rw [MulEquiv.apply_symm_apply]
      exact hγ
  · intro y
    exact ⟨compToFibL T Q' L Tl y, mem_orbit_self y⟩
  · intro x
    refine (Nat.card_congr ((stabEquivT T Q' hT).toEquiv.subtypeEquiv fun s => ?_)).symm
    rw [mem_stabilizer_iff, mem_stabilizer_iff]
    exact smul_fibL_iff T Q' L Tl hT s x x

theorem finite_orbits_pairsL (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) :
    Finite (orbitRel.Quotient (orthGroup QB F) (pairSMAL QB L Tl T)) := by
  have := finite_orbits_gen hpd L hLi
  exact finite_orbits_of_fiber (pairToGenL QB L Tl T) (pairToGenL_smul QB L Tl T) fun M => by
    have := finite_repSetLat hpd (M := (M : Lat F (r + n'))) (SameGenus.isIntegral QB hLi M.2) Tl T
    exact Finite.of_equiv _ (fiberEquivL QB L Tl T M).symm

theorem fibL_orbit_of (a b : FibL₀ T Q' L Tl) (h : a.1 ∈ orbit (orthGroup QB F) b.1) :
    a ∈ orbit (Stab₀T T Q') b := by
  obtain ⟨γ, hγ⟩ := h
  have hγ' : γ • b.1 = a.1 := hγ
  have hγs : γ ∈ Stab₀T T Q' := by
    rw [mem_stabilizer_iff]
    have := congrArg (pairToLevelL QB L Tl T) hγ'
    rw [pairToLevelL_smul, b.2, a.2] at this
    exact this
  exact ⟨⟨γ, hγs⟩, Subtype.ext hγ'⟩

theorem finite_orbits_fibL (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) :
    Finite (orbitRel.Quotient (Stab₀T T Q') (FibL₀ T Q' L Tl)) := by
  have := finite_orbits_pairsL T Q' L Tl hpd hLi
  exact finite_orbits_of_map (H₂ := orthGroup QB F) (fun p : FibL₀ T Q' L Tl => p.1) (fibL_orbit_of T Q' L Tl)

theorem finite_orbits_compSetL (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) (hT : T.Nondegenerate) :
    Finite (orbitRel.Quotient (ratPoints Q') (CompSetL T Q' L Tl)) := by
  have := finite_orbits_fibL T Q' L Tl hpd hLi
  refine finite_orbits_of_map (H₂ := Stab₀T T Q') (compToFibL T Q' L Tl) ?_
  rintro a b ⟨s, hs⟩
  have h := (smul_fibL_iff T Q' L Tl hT s (compToFibL T Q' L Tl a) (compToFibL T Q' L Tl b)).mp hs
  rw [fibToCompL_compToFibL, fibToCompL_compToFibL] at h
  exact ⟨stabEquivT T Q' hT s, h⟩

/-- **The global reduction for embeddings of a lattice:** $\mathrm{repMass}(L) = \sum_t \mathrm{dcMass}(O(Q')(F), K_t)$. -/
theorem repMassLat_eq_finsum_dcMass (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) (hT : T.Nondegenerate) :
    repMassLat QB L Tl T = ∑ᶠ t : orbitRel.Quotient (OAf Q') (CompSetL T Q' L Tl),
      dcMass (ratPoints Q') (stabilizer (OAf Q') t.out) := by
  have := finite_orbits_compSetL T Q' L Tl hpd hLi hT
  rw [repMassLat_eq_orbitMass_pairs hpd L hLi Tl T,
    orbitMass_eq_fiber_of_transitive (pairToLevelL QB L Tl T) (pairToLevelL_smul QB L Tl T) (stdLevel T Q')
      (transitive_levelT T Q' hpd.nondegenerate hT)]
  rw [show @orbitMass (Stab₀T T Q') (FibL₀ T Q' L Tl) _ (fiberAction (pairToLevelL QB L Tl T)
    (pairToLevelL_smul QB L Tl T) (stdLevel T Q')) = orbitMass (Stab₀T T Q') (FibL₀ T Q' L Tl) from rfl,
    orbitMass_fibL_eq T Q' L Tl hT]
  exact orbitMass_eq_finsum_dcMass (ratPoints Q')

theorem commensurable_stabilizer_compSetL (y : CompSetL T Q' L Tl) :
    (stabilizer (OAf Q') y).Commensurable (locStab Q' (stdLat F n')) := by
  rw [stabilizer_compSetL, ← comap_orthEmbBAf_locStab_intVec T Q']
  exact (commensurable_locStab QB (stdLat F (r + n')) y.1).comap _

/-- **The mass of a type:** $\mathrm{dcMass}(O(Q')(F), K_t) = \mathrm{Mass}(\mathcal O_F^{n'}, Q')\cdot w(t)$. -/
theorem dcMass_type_eqL (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1)
    (t : orbitRel.Quotient (OAf Q') (CompSetL T Q' L Tl)) :
    dcMass (ratPoints Q') (stabilizer (OAf Q') t.out) = mass Q' (stdLat F n') * typeWeightL T Q' L Tl t := by
  have hK := commensurable_stabilizer_compSetL T Q' L Tl t.out
  have := finite_orbits hpd' (stdLat F n') hLi'
  have h := dcMass_mul_idxVol (ratPoints Q') (locStab Q' (stdLat F n')) (stabilizer (OAf Q') t.out) 1 hK
    (finite_stabilizer hpd' (stdLat F n') hLi')
  rw [one_mul, ← mass_eq_dcMass] at h
  have h1 : ((stabilizer (OAf Q') t.out).relIndex (locStab Q' (stdLat F n')) : ℝ) ≠ 0 := by
    exact_mod_cast hK.1.relIndex_ne_zero
  have h2 : ((locStab Q' (stdLat F n')).relIndex (stabilizer (OAf Q') t.out) : ℝ) ≠ 0 := by
    exact_mod_cast hK.2.relIndex_ne_zero
  unfold idxVol at h
  unfold typeWeightL
  rw [← h]
  field_simp

theorem finite_typesL (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) (hT : T.Nondegenerate) :
    Finite (orbitRel.Quotient (OAf Q') (CompSetL T Q' L Tl)) := by
  have := finite_orbits_compSetL T Q' L Tl hpd hLi hT
  refine Finite.of_surjective (fun ω : orbitRel.Quotient (ratPoints Q') (CompSetL T Q' L Tl) =>
    (Quotient.mk'' ω.out : orbitRel.Quotient (OAf Q') (CompSetL T Q' L Tl))) fun t => ?_
  refine ⟨Quotient.mk'' t.out, ?_⟩
  conv_rhs => rw [← Quotient.out_eq' t]
  apply Quotient.sound'
  rw [orbitRel_apply]
  obtain ⟨γ, hγ⟩ := out_mem_orbit (Quotient.mk'' t.out : orbitRel.Quotient (ratPoints Q') (CompSetL T Q' L Tl))
    t.out rfl
  exact ⟨(γ : OAf Q'), hγ⟩

/-- **Weil's orbit counting for embeddings of a lattice** (see the module docstring). -/
@[kb "weil1982" "§3.4-3.5 (orbit counting, lattices) [unverified locator]"]
theorem repMassLat_eq_mass_mul (hpd : IsTotallyPosDef QB) (hLi : IsIntegral QB L.1) (hT : T.Nondegenerate)
    (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1) :
    repMassLat QB L Tl T =
      mass Q' (stdLat F n') * ∑ᶠ t : orbitRel.Quotient (OAf Q') (CompSetL T Q' L Tl), typeWeightL T Q' L Tl t := by
  have := finite_typesL T Q' L Tl hpd hLi hT
  rw [repMassLat_eq_finsum_dcMass T Q' L Tl hpd hLi hT, mul_finsum]
  exact finsum_congr fun t => dcMass_type_eqL T Q' L Tl hpd' hLi' t

end Split

end QuadFormsKB.Tamagawa.FramesLat
