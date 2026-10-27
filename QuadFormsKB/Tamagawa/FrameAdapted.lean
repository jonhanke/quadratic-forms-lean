/-
# Coordinates adapted to a frame of $T$, and transport of the frame count

**Layer:** forms over a number field $F$ in coordinates (`QuadForm F N`), lattices of $F^N$ (`Lat`), the weighted frame count
$\mathrm{repMass}_T(L) = \sum_{\mathrm{cls}\,M\subseteq\mathrm{gen}\,L}r_M(T)/|O(M)|$ (`FrameRepMass.lean`), the orthogonal sum
$T\perp Q'$ (`BlockForm.lean`). This is the rank $r$ version of `OrbitalFrame.lean`, which treats $r = 1$.

For the orbital Euler product of a frame we count frames of $T$ in the genus of $\mathcal O_F^{N}$ for a form $Q_0$ that is **not** split.
Weil's argument uses coordinates adapted to a frame $X$ of $T$: an $F$-basis $(X\,|\,Y)$ with the columns of $Y$ orthogonal to those of
$X$, so that $Q(g x) = T(x_0, \dots, x_{r-1}) + Q'(x_r, \dots, x_{r+n'-1})$, $g = (X\,|\,Y)$.

**Defines**
* `AdaptedFrameT Q T`: $g \in \mathrm{GL}_{r+n'}(F)$ and a form $Q'$ over $\mathcal O_F$ in $n'$ variables with $Q\circ g = T\perp Q'$.

**Proves**
* `exists_adaptedFrameT`: if $X \in F^{(r+n')\times r}$ has $Q\circ X = T$ with $T$ nondegenerate, then $Q$ has a frame adapted to $T$.
  *Proof:* $X^{\mathsf T}H X = H_T$ is invertible, so $X^\perp = \ker(X^{\mathsf T}H)$ has dimension $n'$ and meets $\operatorname{span}(X)$
  trivially; take $X$ and $d$ times a basis of $X^\perp$, $d \in \mathcal O_F$ clearing the denominators of the Gram form on $X^\perp$.
* `repCountT_compMat`, `repMassT_compMat` (**transport**): for $g \in \mathrm{GL}_N(F)$,
  $\mathrm{repMass}_T(Q\circ g, g^{-1}L) = \mathrm{repMass}_T(Q, L)$ ($Q$ totally positive definite, $L$ integral): the pairs $(M, X)$
  correspond by $(M, X) \mapsto (gM, gX)$, the orthogonal groups by conjugation. (`isTotallyPosDef_compMat`, `isIntegral_compMat` of
  `OrbitalFrame.lean` supply the hypotheses on $Q\circ g$ and $g^{-1}L$.)

Sources: Weil 1982, §4.5, p. 109 (coordinates adapted to a frame) [unverified]; O'Meara 1963, 42:1, p. 90, and 42:4, p. 91. Indices are
0-based (the columns of $X$ are the first $r$ columns of $g$, indexed $0, \dots, r-1$).
-/
import QuadFormsKB.Tamagawa.FrameRepMass
import QuadFormsKB.Tamagawa.OrbitalFrame

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open NumberField IsDedekindDomain Lattices LocalDensity QuadForm QuadFormsKB.Tamagawa

/-! ### Transport of the frame count along a change of coordinates -/

section Transport

variable {F : Type*} [Field F] [NumberField F] {N r : ℕ} (Q₁ : QuadForm F N) (g : GL (Fin N) F)

attribute [local instance] ratAct frameAct

/-- **Transport of the representation number**: $r_{g^{-1}M}(Q\circ g;\,T) = r_M(Q;\,T)$, by $X \mapsto gX$. -/
theorem repCountT_compMat (M : Lat F N) (T : QuadForm F r) :
    repCountT (Q₁.compMat g.val) (Lat.image g⁻¹ M) T = repCountT Q₁ M T := by
  refine Nat.card_congr
    { toFun := fun X => ⟨g.val * X.1, ?_, ?_⟩
      invFun := fun X => ⟨g⁻¹.val * X.1, ?_, ?_⟩
      left_inv := fun X => Subtype.ext (by
        show g⁻¹.val * (g.val * X.1) = X.1
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul])
      right_inv := fun X => Subtype.ext (by
        show g.val * (g⁻¹.val * X.1) = X.1
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]) }
  · intro j
    obtain ⟨y, hy, hyv⟩ := (mem_glImage).mp (X.2.1 j)
    rw [col_mul, ← hyv, mulVec_mulVec, Units.mul_inv, one_mulVec]; exact hy
  · rw [← QuadForm.compMat_mul]; exact X.2.2
  · intro j
    rw [col_mul]; exact mulVec_mem_glImage (X.2.1 j)
  · rw [QuadForm.compMat_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]; exact X.2.2

/-- **Transport of the genus count of frames along a change of coordinates**: for $Q$ totally positive definite, $L$ integral and
$g \in \mathrm{GL}_N(F)$, $\mathrm{repMass}_T(Q\circ g, g^{-1}L) = \mathrm{repMass}_T(Q, L)$. -/
theorem repMassT_compMat (hpd : IsTotallyPosDef Q₁) {L : Lat F N} (hLi : IsIntegral Q₁ L.1) (T : QuadForm F r) :
    repMassT (Q₁.compMat g.val) (Lat.image g⁻¹ L) T = repMassT Q₁ L T := by
  set Q₂ := Q₁.compMat g.val
  set L₂ := Lat.image g⁻¹ L
  rw [repMassT_eq_orbitMass_pairs (isTotallyPosDef_compMat Q₁ g hpd) L₂ (isIntegral_compMat Q₁ g hLi) T,
    repMassT_eq_orbitMass_pairs hpd L hLi T]
  -- the group isomorphism
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
  -- the pair map
  let P : pairSMAT Q₂ L₂ T → pairSMAT Q₁ L T := fun p =>
    ⟨(Lat.image g p.1.1, g.val * p.1.2), by
      obtain ⟨hM, hx, hQ⟩ := p.2
      refine ⟨?_, fun j => ?_, ?_⟩
      · show SameGenus Q₁ L.1 (glImage g p.1.1.1)
        have := sameGenus_compMat Q₁ g hM
        rwa [show glImage g L₂.1 = L.1 from glImage_inv_glImage g L.1] at this
      · have h := mulVec_mem_glImage (γ := g) (hx j)
        rw [← col_mul] at h
        exact h
      · rw [← QuadForm.compMat_mul]; exact hQ⟩
  have hPsmul : ∀ (γ : orthGroup Q₂ F) (p : pairSMAT Q₂ L₂ T), P (γ • p) = φ γ • P p := by
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
    have h1 := congrArg (fun p : pairSMAT Q₁ L T => (p : Lat F N × Matrix (Fin N) (Fin r) F)) h
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
    refine ⟨⟨(Lat.image g⁻¹ q.1.1, g⁻¹.val * q.1.2), ?_, fun j => ?_, ?_⟩, ?_⟩
    · show SameGenus Q₂ (glImage g⁻¹ L.1) (glImage g⁻¹ q.1.1.1)
      apply sameGenus_compMat'
      rw [glImage_inv_glImage, glImage_inv_glImage]; exact hM
    · have h := mulVec_mem_glImage (γ := g⁻¹) (hx j)
      rw [← col_mul] at h
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

/-! ### Coordinates adapted to a frame of $T$ -/

section Frame

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ}

/-- **A frame adapted to $T$** for $Q$ over $F$ in $r + n'$ variables: $g \in \mathrm{GL}_{r+n'}(F)$ and a form $Q'$ over $\mathcal O_F$ in
$n'$ variables with $Q\circ g = T\perp Q'$, i.e. $Q(g x) = T(x_0, \dots, x_{r-1}) + Q'(x_r, \dots, x_{r+n'-1})$. The first $r$ columns of $g$
form a frame $X$ of $T$ ($Q\circ X = T$), the last $n'$ span $X^\perp$ and are scaled so that the complement form is integral (Weil 1982,
§4.5, p. 109 [unverified]; O'Meara 1963, 42:1, p. 90, and 42:4, p. 91). Fields: `g`, `Q'`, `compMat_eq`. -/
structure AdaptedFrameT (Q : QuadForm F (r + n')) (T : QuadForm F r) where
  /-- The change of coordinates (first $r$ columns a frame of $T$). -/
  g : GL (Fin (r + n')) F
  /-- The complement form, over $\mathcal O_F$. -/
  Q' : QuadForm (𝓞 F) n'
  /-- $Q\circ g = T\perp Q'$. -/
  compMat_eq : Q.compMat g.val = blockForm T (Q'.map (algebraMap (𝓞 F) F))

/-- **Existence of an adapted frame** (O'Meara 1963, 42:4, p. 91, with 42:1, p. 90): if $X \in F^{(r+n')\times r}$ satisfies $Q\circ X = T$
with $T$ nondegenerate, then $Q$ has a frame adapted to $T$. *Proof:* $X^{\mathsf T}HX = H_T$ is invertible, so $X^\perp = \ker(X^{\mathsf T}H)$
has dimension $n'$ and meets the column space of $X$ trivially; take $X$ and $d$ times a basis of $X^\perp$, $d \in \mathcal O_F$ clearing
the denominators of the Gram form on $X^\perp$. -/
theorem exists_adaptedFrameT (Q : QuadForm F (r + n')) (T : QuadForm F r) (hT : T.Nondegenerate)
    (X : Matrix (Fin (r + n')) (Fin r) F) (hX : Q.compMat X = T) : Nonempty (AdaptedFrameT Q T) := by
  classical
  set H := Q.hessian with hH
  have hHT : Xᵀ * H * X = T.hessian := by rw [← hX, hessian_compMat]
  have hdetT : T.hessian.det ≠ 0 := hT
  have hdetT' : IsUnit T.hessian.det := isUnit_iff_ne_zero.mpr hdetT
  -- the map `y ↦ Xᵀ H y` and its kernel `X^⊥`
  let φ : (Fin (r + n') → F) →ₗ[F] (Fin r → F) :=
    { toFun := fun y => (Xᵀ * H) *ᵥ y
      map_add' := fun a b => Matrix.mulVec_add _ _ _
      map_smul' := fun c a => by simp [Matrix.mulVec_smul] }
  have hrange : LinearMap.range φ = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ⟨X *ᵥ (T.hessian⁻¹ *ᵥ c), ?_⟩
    show (Xᵀ * H) *ᵥ (X *ᵥ (T.hessian⁻¹ *ᵥ c)) = c
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, hHT, Matrix.mul_nonsing_inv _ hdetT', one_mulVec]
  set W := LinearMap.ker φ
  have hW : Module.finrank F W = n' := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange] at this
    simp only [finrank_top, Module.finrank_fin_fun] at this
    change r + Module.finrank F W = r + n' at this
    omega
  let b := Module.finBasisOfFinrankEq F W hW
  let Bm : Matrix (Fin (r + n')) (Fin n') F := Matrix.of fun i k => (b k : Fin (r + n') → F) i
  have hBmW : ∀ y : Fin n' → F, Bm *ᵥ y ∈ W := by
    intro y
    have : Bm *ᵥ y = ∑ k, y k • (b k : Fin (r + n') → F) := by
      funext i; simp [Bm, mulVec, dotProduct, mul_comm]
    rw [this]
    exact W.sum_mem fun k _ => W.smul_mem _ (b k).2
  have hφB : ∀ y, (Xᵀ * H) *ᵥ (Bm *ᵥ y) = 0 := fun y => hBmW y
  have hφB' : ∀ y, Xᵀ *ᵥ (H *ᵥ (Bm *ᵥ y)) = 0 := fun y => by
    have := hφB y
    rwa [← Matrix.mulVec_mulVec] at this
  -- clearing denominators of `Q ∘ Bm`
  set Q'' := Q.compMat Bm
  obtain ⟨d₀, hd₀⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    (Finset.univ.image fun p : Fin n' × Fin n' => Q''.coeff p.1 p.2)
  set d : 𝓞 F := (d₀ : 𝓞 F)
  have hd : d ≠ 0 := nonZeroDivisors.coe_ne_zero d₀
  have hdF : (d : F) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (𝓞 F) F)]
    exact fun h => hd (RingOfIntegers.coe_injective h)
  have hint : ∀ i j, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = (d : F) ^ 2 * Q''.coeff i j := by
    intro i j
    obtain ⟨a, ha⟩ := hd₀ (Q''.coeff i j) (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
    refine ⟨d * a, ?_⟩
    rw [map_mul, ha, Algebra.smul_def, pow_two, ← mul_assoc]
  choose a ha using hint
  let Q'o : QuadForm (𝓞 F) n' := QuadForm.ofUpper a
  have hQ'o : Q'o.map (algebraMap (𝓞 F) F) = Q.compMat ((d : F) • Bm) := by
    refine ext_upper fun i j hij => ?_
    rw [compMat_smul_coeff]
    simp only [Q'o, QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply, if_pos hij]
    exact ha i j
  -- the matrix `G = (X | d Bm)`
  let G : Matrix (Fin (r + n')) (Fin (r + n')) F :=
    Matrix.of fun i j => (Fin.append (fun a => X i a) (fun k => (d : F) * Bm i k) : Fin (r + n') → F) j
  have hGv : ∀ x : Fin (r + n') → F, G *ᵥ x =
      X *ᵥ (fun a => x (Fin.castAdd n' a)) + ((d : F) • Bm) *ᵥ (fun k => x (Fin.natAdd r k)) := by
    intro x
    funext i
    simp only [G, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Pi.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hGinj : ∀ x, G *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hGv] at hx
    set u : Fin r → F := fun a => x (Fin.castAdd n' a) with hu_def
    set w : Fin n' → F := fun k => x (Fin.natAdd r k) with hw_def
    have h1 := congrArg (fun y => (Xᵀ * H) *ᵥ y) hx
    have h2 : (Xᵀ * H) *ᵥ (X *ᵥ u) = T.hessian *ᵥ u := by rw [Matrix.mulVec_mulVec, hHT]
    have h3 : (Xᵀ * H) *ᵥ (((d : F) • Bm) *ᵥ w) = 0 := by
      rw [smul_mulVec, mulVec_smul, hφB, smul_zero]
    simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at h1
    rw [h2, h3, add_zero] at h1
    have hu : u = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdetT h1
    rw [hu, mulVec_zero, zero_add, smul_mulVec] at hx
    have h4 : Bm *ᵥ w = 0 := (smul_eq_zero.mp hx).resolve_left hdF
    have h5 : ∑ k, w k • b k = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      rw [← h4]; funext i; simp [Bm, mulVec, dotProduct, mul_comm]
    have h6 := b.linearIndependent
    have h7 : ∀ k, w k = 0 := fun k => (Fintype.linearIndependent_iff.mp h6) _ h5 k
    funext i
    induction i using Fin.addCases with
    | left i => simpa [hu_def] using congrFun hu i
    | right k => simpa [hw_def] using h7 k
  have hdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hx0 (hGinj x hx)
  let g : GL (Fin (r + n')) F := Matrix.GeneralLinearGroup.mk'' G hdet
  refine ⟨⟨g, Q'o, ?_⟩⟩
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat, show g.val = G from rfl, hGv]
  refine Eq.trans ?_ (evalIn_blockForm F T (Q'o.map (algebraMap (𝓞 F) F)) x).symm
  set u : Fin r → F := fun a => x (Fin.castAdd n' a) with hu_def
  set w : Fin n' → F := fun k => x (Fin.natAdd r k) with hw_def
  have e1 : Q.eval (X *ᵥ u) = T.eval u := by rw [← eval_compMat, hX]
  have e2 : Q.eval (((d : F) • Bm) *ᵥ w) = (Q'o.map (algebraMap (𝓞 F) F)).eval w := by
    rw [← eval_compMat, ← hQ'o]
  have hdot : ∀ v : Fin (r + n') → F, (X *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Xᵀ *ᵥ v) := by
    intro v
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have e4 : Xᵀ *ᵥ (H *ᵥ (((d : F) • Bm) *ᵥ w)) = 0 := by
    rw [smul_mulVec, mulVec_smul, mulVec_smul, hφB', smul_zero]
  have e3 : (X *ᵥ u) ⬝ᵥ (H *ᵥ (((d : F) • Bm) *ᵥ w)) = 0 := by
    rw [hdot, e4, dotProduct_zero]
  have hp := eval_polar Q (X *ᵥ u) (((d : F) • Bm) *ᵥ w)
  rw [e3] at hp
  show Q.eval (X *ᵥ u + ((d : F) • Bm) *ᵥ w) = T.eval u + (Q'o.map (algebraMap (𝓞 F) F)).eval w
  linear_combination hp + e1 + e2

end Frame

end QuadFormsKB.Tamagawa.Frames
