/-
# Kneser neighbours, part 5: the neighbour relation averaged over the genus

**Layer:** integral forms (`QuadForm ℤ n`), their $\mathrm{GL}_n(\mathbb{Z})$-classes in a genus (`Siegel/Genus.lean`), and
$p$-neighbour lattices (`Siegel/Neighbors.lean`, `Siegel/NeighborGenus.lean`).

**Defines** the neighbour matrices `nbMats Q Q' p` ($g \in \mathrm{GL}_n(\mathbb{Q})$ with $g\mathbb{Z}^n$ a $p$-neighbour of
$\mathbb{Z}^n$ for $Q$ and $Q(g\vec{x}) = Q'(\vec{x})$), the class of a neighbour (`nbClass`; the class of its Gram form in any basis,
`hasClass`), and the neighbour multiplicities $N(Q, c') = \#\{L' \sim_p \mathbb{Z}^n : [L'] = c'\}$ (`nbCount`).

**Proves**
- the **double-counting identity** $N(Q, [Q'])\,|\mathrm{Aut}(Q')| = \#\,\mathrm{nbMats}(Q, Q') = N(Q', [Q])\,|\mathrm{Aut}(Q)|$
  (`card_nbMats`, `card_nbMats_symm`; the neighbour relation is symmetric, $g \mapsto g^{-1}$, and the matrices with a given
  lattice form an $\mathrm{Aut}(Q')$-torsor);
- the **genus-averaged neighbour relation** for $n = 4$ (`genusRepAvg_neighbor_four`): for $Q$ positive definite, $p$ an
  odd prime, $p \nmid \det H$, $\varepsilon = \left(\frac{\det H}{p}\right)$, with $r_{\mathrm{Gen}}(m) = $ `genusRepAvg Q m`,
$$r_{\mathrm{Gen}}(p^2m) + \big(p + [p \mid m]\,\varepsilon p\big)\,r_{\mathrm{Gen}}(m) + p^2\,[p^2 \mid m]\,r_{\mathrm{Gen}}(m/p^2)
  = (p^2 + p + 1 + \varepsilon p)\,r_{\mathrm{Gen}}(m).$$
So $\theta_{\mathrm{Gen}}$ is an eigenvector of the neighbour operator with eigenvalue the number of neighbours,
$p^2 + p + 1 + \varepsilon p$; this is a $T(p^2)$-type relation (see `Siegel/EichlerCommutation.lean`), **not** the $T_p$-relation
$r(pm) + \chi(p)p\,r(m/p) = (1 + \chi(p)p)\,r(m)$.
-/
import QuadFormsKB.Siegel.NeighborGenus

open Matrix

namespace QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### Changing the basis of a lattice -/

section BasisChange

/-- $\mathrm{GL}_n(\mathbb{Z}) \to \mathrm{GL}_n(\mathbb{Q})$. -/
abbrev toGLQ : GL (Fin n) ℤ →* GL (Fin n) ℚ := Units.map (Int.castRingHom ℚ).mapMatrix.toMonoidHom

theorem toGLQ_val (U : GL (Fin n) ℤ) : ((toGLQ U : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) =
    (U : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ) := rfl

theorem toGLQ_injective : Function.Injective (toGLQ (n := n)) := by
  intro U V h
  ext i j
  have := congrArg (fun g : GL (Fin n) ℚ => (g : Matrix (Fin n) (Fin n) ℚ) i j) h
  simpa [toGLQ_val] using this

theorem mulVec_cv_int (U : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    U.map (Int.castRingHom ℚ) *ᵥ cv x = cv (U *ᵥ x) := by
  ext i; simp [mulVec, dotProduct]

theorem eval_map_rat (Q : QuadForm ℤ n) (y : Fin n → ℚ) :
    (Q.map (Int.castRingHom ℚ)).eval y = Q.evalIn ℚ y := by
  simp [QuadForm.map, QuadForm.evalIn]

/-- An identity $Q_1(U\vec{y}) = Q_2(\vec{y})$ on $\mathbb{Z}^n$ holds on $\mathbb{Q}^n$. -/
theorem evalIn_rat_of_int {Q₁ Q₂ : QuadForm ℤ n} {U : Matrix (Fin n) (Fin n) ℤ}
    (h : ∀ y, Q₁.eval (U *ᵥ y) = Q₂.eval y) (x : Fin n → ℚ) :
    Q₁.evalIn ℚ (U.map (Int.castRingHom ℚ) *ᵥ x) = Q₂.evalIn ℚ x := by
  rw [← eval_map_rat, ← eval_map_rat]
  exact eval_mulVec_map _ h x

/-- Unimodular changes of basis do not change the lattice: $g U\mathbb{Z}^n = g\mathbb{Z}^n$. -/
theorem imgLat_mul_toGLQ (g : Matrix (Fin n) (Fin n) ℚ) (U : GL (Fin n) ℤ) :
    imgLat (g * (toGLQ U : Matrix (Fin n) (Fin n) ℚ)) = imgLat g := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨(U : Matrix (Fin n) (Fin n) ℤ) *ᵥ c, by rw [← mulVec_mulVec, toGLQ_val, mulVec_cv_int]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨((U⁻¹ : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) *ᵥ c, ?_⟩
    rw [← mulVec_mulVec, toGLQ_val, mulVec_cv_int, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_mulVec]

/-- **Two bases of a lattice differ by $\mathrm{GL}_n(\mathbb{Z})$:** if $g\mathbb{Z}^n = h\mathbb{Z}^n$ then $g = hU$ with $U \in \mathrm{GL}_n(\mathbb{Z})$. -/
theorem exists_GLZ_of_imgLat_eq {g h : GL (Fin n) ℚ}
    (heq : imgLat (g : Matrix (Fin n) (Fin n) ℚ) = imgLat (h : Matrix (Fin n) (Fin n) ℚ)) :
    ∃ U : GL (Fin n) ℤ, h * toGLQ U = g := by
  -- an integral matrix from containment of lattices
  have integral : ∀ a b : GL (Fin n) ℚ, imgLat (a : Matrix (Fin n) (Fin n) ℚ) ≤ imgLat (b : Matrix (Fin n) (Fin n) ℚ) →
      ∃ A : Matrix (Fin n) (Fin n) ℤ, A.map (Int.castRingHom ℚ) = ((b⁻¹ * a : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) := by
    intro a b hab
    have hcol : ∀ j, ∃ c : Fin n → ℤ, (a : Matrix (Fin n) (Fin n) ℚ) *ᵥ cv (Pi.single j 1) =
        (b : Matrix (Fin n) (Fin n) ℚ) *ᵥ cv c := fun j => hab ⟨Pi.single j 1, rfl⟩
    choose C hC using hcol
    refine ⟨Matrix.of fun i j => C j i, ?_⟩
    ext i j
    have := congrArg (fun w => ((b⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ w) (hC j)
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at this
    have := congrFun this i
    simp only [cv_apply] at this
    rw [Matrix.map_apply, of_apply, eq_intCast, ← this]
    simp [mulVec, dotProduct, Pi.single_apply]
  obtain ⟨A, hA⟩ := integral g h heq.le
  obtain ⟨B, hB⟩ := integral h g heq.ge
  have hinj : ∀ X Y : Matrix (Fin n) (Fin n) ℤ, X.map (Int.castRingHom ℚ) = Y.map (Int.castRingHom ℚ) → X = Y := by
    intro X Y hXY; ext i j; have := congrFun (congrFun hXY i) j; simpa using this
  have hAB : A * B = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hA, hB, ← Units.val_mul]
    simp [Matrix.map_one])
  have hBA : B * A = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hA, hB, ← Units.val_mul]
    simp [Matrix.map_one])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  rw [Units.val_mul]
  change (h : Matrix (Fin n) (Fin n) ℚ) * A.map (Int.castRingHom ℚ) = g
  rw [hA, ← Units.val_mul, mul_inv_cancel_left]

end BasisChange

/-! ### Neighbour matrices and the symmetry of the neighbour relation -/

section Symm

variable {p : ℕ} [hp : Fact p.Prime]

theorem map_imgLat (g h : Matrix (Fin n) (Fin n) ℚ) :
    (imgLat h).toAddSubgroup.map (Matrix.mulVecLin g).toAddMonoidHom = (imgLat (g * h)).toAddSubgroup := by
  ext x
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe,
    Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩; exact ⟨c, by rw [mulVec_mulVec]⟩
  · rintro ⟨c, rfl⟩; exact ⟨h *ᵥ cv c, ⟨c, rfl⟩, by rw [mulVec_mulVec]⟩

/-- **The neighbour relation is symmetric:** if $g\mathbb{Z}^n$ is a $p$-neighbour of $\mathbb{Z}^n$ for $Q$ and $Q'(\vec{x}) = Q(g\vec{x})$, then
$g^{-1}\mathbb{Z}^n$ is a $p$-neighbour of $\mathbb{Z}^n$ for $Q'$ (apply $g$: it maps the pair $(g^{-1}\mathbb{Z}^n, \mathbb{Z}^n)$ to
$(\mathbb{Z}^n, g\mathbb{Z}^n)$). -/
theorem isNeighbor_inv {Q Q' : QuadForm ℤ n} {g : GL (Fin n) ℚ} (hL : IsNeighbor Q p (imgLat (g : Matrix (Fin n) (Fin n) ℚ)))
    (hQ' : ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x)) :
    IsNeighbor Q' p (imgLat ((g⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)) := by
  set G : Matrix (Fin n) (Fin n) ℚ := (g : Matrix (Fin n) (Fin n) ℚ)
  set φ := (Matrix.mulVecLin G).toAddMonoidHom
  have hφ : Function.Injective φ := by
    intro x y hxy
    have := congrArg (fun w => ((g⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ w) hxy
    simpa [φ, G, mulVec_mulVec, ← Units.val_mul] using this
  have h1 : (imgLat ((g⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)).toAddSubgroup.map φ = (stdLat n).toAddSubgroup := by
    rw [map_imgLat, ← Units.val_mul, mul_inv_cancel, Units.val_one, ← stdLat_eq_imgLat_one]
  have h2 : (stdLat n).toAddSubgroup.map φ = (imgLat G).toAddSubgroup := by
    rw [stdLat_eq_imgLat_one, map_imgLat, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hφ, h1, h2]; exact hL.relIndex_self
  · rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hφ, h1, h2]; exact hL.relIndex_std
  · rintro _ ⟨c, rfl⟩
    refine ⟨Q.eval c, ?_⟩
    rw [hQ', mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, evalIn_cv]

/-- **The neighbour matrices** of $(Q, Q')$: $g \in \mathrm{GL}_n(\mathbb{Q})$ with $g\mathbb{Z}^n$ a $p$-neighbour of $\mathbb{Z}^n$ (for $Q$) and
$Q'(\vec{x}) = Q(g\vec{x})$. -/
def nbMats (Q Q' : QuadForm ℤ n) (p : ℕ) : Set (GL (Fin n) ℚ) :=
  {g | IsNeighbor Q p (imgLat (g : Matrix (Fin n) (Fin n) ℚ)) ∧ ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x)}

/-- **Symmetry of the neighbour matrices:** $g \mapsto g^{-1}$ is a bijection $\mathrm{nbMats}(Q, Q') \to \mathrm{nbMats}(Q', Q)$. -/
theorem card_nbMats_symm (Q Q' : QuadForm ℤ n) : Nat.card (nbMats Q Q' p) = Nat.card (nbMats Q' Q p) := by
  have key : ∀ {Q Q' : QuadForm ℤ n} {g : GL (Fin n) ℚ}, g ∈ nbMats Q Q' p → g⁻¹ ∈ nbMats Q' Q p := by
    intro Q Q' g ⟨hL, hQ'⟩
    refine ⟨isNeighbor_inv hL hQ', fun x => ?_⟩
    rw [hQ', mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  exact Nat.card_congr
    { toFun := fun g => ⟨g.1⁻¹, key g.2⟩
      invFun := fun g => ⟨g.1⁻¹, by simpa using key g.2⟩
      left_inv := fun g => by simp
      right_inv := fun g => by simp }

end Symm

/-! ### The class of a neighbour and the multiplicities $N(Q, c')$ -/

section Classes

variable {p : ℕ} [hp : Fact p.Prime]

/-- **$L$ has class $c$:** $L = g\mathbb{Z}^n$ for some $g \in \mathrm{GL}_n(\mathbb{Q})$ whose Gram form $Q'' = Q \circ g$ is integral of class $c$. -/
def hasClass (Q : QuadForm ℤ n) (L : Submodule ℤ (Fin n → ℚ)) (c : QClass n) : Prop :=
  ∃ g : GL (Fin n) ℚ, imgLat (g : Matrix (Fin n) (Fin n) ℚ) = L ∧
    ∃ Q'' : QuadForm ℤ n, classOf Q'' = c ∧ ∀ x, Q''.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x)

/-- **Gram forms of two bases are $\mathbb{Z}$-equivalent.** -/
theorem intEquiv_of_bases {Q Q₁ Q₂ : QuadForm ℤ n} {g₁ g₂ : GL (Fin n) ℚ}
    (heq : imgLat (g₁ : Matrix (Fin n) (Fin n) ℚ) = imgLat (g₂ : Matrix (Fin n) (Fin n) ℚ))
    (h₁ : ∀ x, Q₁.evalIn ℚ x = Q.evalIn ℚ ((g₁ : Matrix (Fin n) (Fin n) ℚ) *ᵥ x))
    (h₂ : ∀ x, Q₂.evalIn ℚ x = Q.evalIn ℚ ((g₂ : Matrix (Fin n) (Fin n) ℚ) *ᵥ x)) : IntEquiv Q₂ Q₁ := by
  obtain ⟨U, hU⟩ := exists_GLZ_of_imgLat_eq heq
  refine ⟨U, fun y => ?_⟩
  have : (Q₂.eval ((U : Matrix (Fin n) (Fin n) ℤ) *ᵥ y) : ℚ) = Q₁.eval y := by
    rw [← evalIn_cv, ← evalIn_cv, ← mulVec_cv_int, h₂, h₁, mulVec_mulVec, ← toGLQ_val, ← Units.val_mul, hU]
  exact_mod_cast this

theorem hasClass_unique {Q : QuadForm ℤ n} {L : Submodule ℤ (Fin n → ℚ)} {c₁ c₂ : QClass n}
    (h₁ : hasClass Q L c₁) (h₂ : hasClass Q L c₂) : c₁ = c₂ := by
  obtain ⟨g₁, hg₁, Q₁, rfl, hQ₁⟩ := h₁
  obtain ⟨g₂, hg₂, Q₂, rfl, hQ₂⟩ := h₂
  exact classOf_eq_classOf_iff.mpr (intEquiv_of_bases (hg₂.trans hg₁.symm) hQ₂ hQ₁)

/-- Every $p$-neighbour has a class, and it lies in the genus of $Q$ (`exists_gram_of_mem_neighbors`). -/
theorem exists_hasClass {Q : QuadForm ℤ n} (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    {L : Submodule ℤ (Fin n → ℚ)} (hL : L ∈ neighbors Q p) : ∃ c ∈ genusClasses Q, hasClass Q L c := by
  obtain ⟨g, hg, rfl, Q', hQ', hgen⟩ := exists_gram_of_mem_neighbors hp2 hdet hL
  set gU := Matrix.nonsingInvUnit g (isUnit_iff_ne_zero.mpr hg)
  have e : (gU : Matrix (Fin n) (Fin n) ℚ) = g := rfl
  exact ⟨classOf Q', classOf_mem_genusClasses_iff.mpr hgen, gU, by rw [e], Q', rfl, by rw [e]; exact hQ'⟩

open Classical in
/-- **The class of a neighbour** $L'$ (the class of the Gram form of any basis; junk `classOf Q` if $L'$ has none). -/
noncomputable def nbClass (Q : QuadForm ℤ n) (L : Submodule ℤ (Fin n → ℚ)) : QClass n :=
  if h : ∃ c, hasClass Q L c then h.choose else classOf Q

theorem nbClass_spec {Q : QuadForm ℤ n} (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    {L : Submodule ℤ (Fin n → ℚ)} (hL : L ∈ neighbors Q p) :
    nbClass Q L ∈ genusClasses Q ∧ ∀ c, hasClass Q L c ↔ nbClass Q L = c := by
  obtain ⟨c, hc, hcl⟩ := exists_hasClass hp2 hdet hL
  have h : ∃ c, hasClass Q L c := ⟨c, hcl⟩
  have e : nbClass Q L = c := by
    unfold nbClass; rw [dif_pos h]; exact hasClass_unique h.choose_spec hcl
  refine ⟨e ▸ hc, fun c' => ⟨fun h' => e.trans (hasClass_unique hcl h'), fun h' => ?_⟩⟩
  rw [← h', e]; exact hcl

open Classical in
/-- **The neighbour multiplicity** $N(Q, c) = \#\{L' \sim_p \mathbb{Z}^n : [L'] = c\}$. -/
noncomputable def nbCount (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (c : QClass n) : ℕ :=
  ((neighbors Q p).filter fun L => nbClass Q L = c).card

/-- **The bases of a neighbour with Gram form $Q'$ form an $\mathrm{Aut}(Q')$-torsor:** if $L'$ has class $[Q']$, then
$\#\{g : g\mathbb{Z}^n = L',\ Q \circ g = Q'\} = |\mathrm{Aut}(Q')|$. -/
theorem card_bases_eq {Q Q' : QuadForm ℤ n} {L : Submodule ℤ (Fin n → ℚ)} (hL : hasClass Q L (classOf Q')) :
    Nat.card {g : GL (Fin n) ℚ // imgLat (g : Matrix (Fin n) (Fin n) ℚ) = L ∧
      ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x)} = Nat.card (Aut Q') := by
  obtain ⟨g₁, hg₁, Q'', hcl, hQ''⟩ := hL
  obtain ⟨v, hv⟩ := classOf_eq_classOf_iff.mp hcl
  -- a base point g₀ with Q ∘ g₀ = Q'
  set g₀ : GL (Fin n) ℚ := g₁ * toGLQ v
  have hg₀L : imgLat (g₀ : Matrix (Fin n) (Fin n) ℚ) = L := by
    rw [Units.val_mul, imgLat_mul_toGLQ, hg₁]
  have hg₀Q : ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ ((g₀ : Matrix (Fin n) (Fin n) ℚ) *ᵥ x) := by
    intro x
    rw [Units.val_mul, ← mulVec_mulVec, ← hQ'', toGLQ_val, evalIn_rat_of_int hv]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun u : Aut Q' => ⟨g₀ * toGLQ u.1, by rw [Units.val_mul, imgLat_mul_toGLQ, hg₀L], fun x => by
      rw [Units.val_mul, ← mulVec_mulVec, ← hg₀Q, toGLQ_val, evalIn_rat_of_int u.2]⟩) ⟨?_, ?_⟩)
  · intro u₁ u₂ h
    have := congrArg (fun g : {g : GL (Fin n) ℚ // _} => g.1) h
    simp only [mul_right_inj] at this
    exact Subtype.ext (toGLQ_injective this)
  · rintro ⟨g, hgL, hgQ⟩
    obtain ⟨U, hU⟩ := exists_GLZ_of_imgLat_eq (hgL.trans hg₀L.symm)
    have hUaut : U ∈ Aut Q' := by
      intro y
      have : (Q'.eval ((U : Matrix (Fin n) (Fin n) ℤ) *ᵥ y) : ℚ) = Q'.eval y := by
        rw [← evalIn_cv, ← evalIn_cv, ← mulVec_cv_int, hg₀Q, hgQ, mulVec_mulVec, ← toGLQ_val,
          ← Units.val_mul, hU]
      exact_mod_cast this
    exact ⟨⟨U, hUaut⟩, Subtype.ext hU⟩

/-- **Counting neighbour matrices:** $\#\,\mathrm{nbMats}(Q, Q') = N(Q, [Q'])\cdot|\mathrm{Aut}(Q')|$ ($Q'$ positive definite, so
$\mathrm{Aut}(Q')$ is finite). -/
theorem card_nbMats {Q Q' : QuadForm ℤ n} (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    (hQ' : IntQF.PosDef Q') : Nat.card (nbMats Q Q' p) = nbCount Q p (classOf Q') * Nat.card (Aut Q') := by
  classical
  set S := (neighbors Q p).filter fun L => nbClass Q L = classOf Q'
  let F : S → Type := fun L => {g : GL (Fin n) ℚ // imgLat (g : Matrix (Fin n) (Fin n) ℚ) = L.1 ∧
      ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x)}
  have hS : ∀ L : S, hasClass Q L.1 (classOf Q') := by
    intro L
    have hL := (Finset.mem_filter.mp L.2)
    exact ((nbClass_spec hp2 hdet hL.1).2 _).mpr hL.2
  have hF : ∀ L : S, Nat.card (F L) = Nat.card (Aut Q') := fun L => card_bases_eq (hS L)
  haveI : Finite (Aut Q') := hQ'.finite_aut
  haveI : ∀ L : S, Finite (F L) := fun L => by
    have h := hF L
    exact Nat.finite_of_card_ne_zero (by rw [h]; exact (hQ'.card_aut_pos).ne')
  have e : nbMats Q Q' p ≃ Σ L : S, F L :=
    { toFun := fun g => ⟨⟨imgLat (g.1 : Matrix (Fin n) (Fin n) ℚ), Finset.mem_filter.mpr
          ⟨(mem_neighbors_iff hdet).mpr g.2.1,
            ((nbClass_spec hp2 hdet ((mem_neighbors_iff hdet).mpr g.2.1)).2 _).mp
              ⟨g.1, rfl, Q', rfl, g.2.2⟩⟩⟩, ⟨g.1, rfl, g.2.2⟩⟩
      invFun := fun x => ⟨x.2.1, by
          refine ⟨?_, x.2.2.2⟩
          rw [x.2.2.1]
          exact (mem_neighbors_iff hdet).mp (Finset.mem_filter.mp x.1.2).1⟩
      left_inv := fun g => rfl
      right_inv := fun x => by
        obtain ⟨⟨L, hL⟩, g, hgL, hgQ⟩ := x
        exact Sigma.subtype_ext (Subtype.ext hgL) rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [hF]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  rfl

end Classes

/-! ### Summing over the genus -/

section GenusSum

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Every neighbour is counted once:** $\sum_{c' \in \mathrm{Gen}(Q)} N(Q, c') = \#\{p\text{-neighbours}\}$. -/
theorem sum_nbCount {Q : QuadForm ℤ n} (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (T : Finset (QClass n))
    (hT : ∀ c, c ∈ T ↔ c ∈ genusClasses Q) : ∑ c ∈ T, nbCount Q p c = (neighbors Q p).card := by
  classical
  symm
  unfold nbCount
  exact Finset.card_eq_sum_card_fiberwise fun L hL => (hT _).mpr (nbClass_spec hp2 hdet hL).1

/-- **Sum of $r_{L'}(m)$ by classes:** $\sum_{L' \sim_p \mathbb{Z}^n} r_{L'}(m) = \sum_{c'} N(Q, c')\, r_{c'}(m)$. -/
theorem sum_latRep_eq_sum_classes {Q : QuadForm ℤ n} (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    (T : Finset (QClass n)) (hT : ∀ c, c ∈ T ↔ c ∈ genusClasses Q) (m : ℤ) :
    ∑ L ∈ neighbors Q p, (latRep Q L m : ℝ) = ∑ c ∈ T, (nbCount Q p c : ℝ) * c.repNum m := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := nbClass Q) (t := T)
    (fun L hL => (hT _).mpr (nbClass_spec hp2 hdet hL).1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold nbCount
  rw [Finset.cast_card, Finset.sum_mul, one_mul]
  refine Finset.sum_congr rfl fun L hL => ?_
  obtain ⟨hLn, hLc⟩ := Finset.mem_filter.mp hL
  obtain ⟨g, rfl, Q'', hcl, hQ''⟩ := ((nbClass_spec hp2 hdet hLn).2 c).mpr hLc
  rw [latRep_imgLat (g.isUnit.map Matrix.detMonoidHom |>.ne_zero) hQ'' m, ← hcl, QClass.repNum_classOf]

/-- **The double-counting identity** (symmetry of the weighted neighbour graph): for positive definite $Q, Q'$ with
$p \nmid \det H, \det H'$,
$$N(Q, [Q'])\cdot|\mathrm{Aut}(Q')| = N(Q', [Q])\cdot|\mathrm{Aut}(Q)|.$$ -/
@[kb "hanke2011aws" "§1.10, weighted p-neighbor graph, p. 23"]
theorem nbCount_mul_autCard {Q Q' : QuadForm ℤ n} (hp2 : p ≠ 2) (hQ : IntQF.PosDef Q) (hQ' : IntQF.PosDef Q')
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (hdet' : ¬ (p : ℤ) ∣ Q'.hessian.det) :
    nbCount Q p (classOf Q') * Nat.card (Aut Q') = nbCount Q' p (classOf Q) * Nat.card (Aut Q) := by
  rw [← card_nbMats hp2 hdet hQ', ← card_nbMats hp2 hdet' hQ, card_nbMats_symm]

theorem out_spec {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {c : QClass n} (hc : c ∈ genusClasses Q) :
    classOf (Quotient.out (s := intSetoid n) c) = c ∧ SameGenus Q (Quotient.out (s := intSetoid n) c) ∧
      IntQF.PosDef (Quotient.out (s := intSetoid n) c) ∧
      (Quotient.out (s := intSetoid n) c).hessian.det = Q.hessian.det := by
  have h1 : classOf (Quotient.out (s := intSetoid n) c) = c := Quotient.out_eq _
  have h2 : SameGenus Q (Quotient.out (s := intSetoid n) c) := by
    rw [← h1] at hc; exact classOf_mem_genusClasses_iff.mp hc
  exact ⟨h1, h2, h2.posDef hQ, (SameGenus.det_hessian_eq hQ h2).symm⟩

/-- **The genus average of the neighbour sums** (general $n$; $Q$ positive definite, $p$ an odd prime, $p \nmid \det H$):
with $Q_c$ a representative of the class $c$,
$$\sum_{c \in \mathrm{Gen}(Q)} \frac{1}{|\mathrm{Aut}(c)|}\sum_{L' \sim_p \mathbb{Z}^n} r^{Q_c}_{L'}(m)
  = \sum_{c \in \mathrm{Gen}(Q)} \frac{\#\{p\text{-neighbours of } Q_c\}\; r_c(m)}{|\mathrm{Aut}(c)|}.$$
*Proof:* expand by classes (`sum_latRep_eq_sum_classes`), swap the sums, use `nbCount_mul_autCard`, and sum the
multiplicities (`sum_nbCount`). -/
theorem genus_sum_neighbors {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (hp2 : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (T : Finset (QClass n)) (hT : ∀ c, c ∈ T ↔ c ∈ genusClasses Q)
    (m : ℤ) :
    ∑ c ∈ T, (∑ L ∈ neighbors (Quotient.out (s := intSetoid n) c) p,
        (latRep (Quotient.out (s := intSetoid n) c) L m : ℝ)) / c.autCard =
      ∑ c ∈ T, ((neighbors (Quotient.out (s := intSetoid n) c) p).card : ℝ) * c.repNum m / c.autCard := by
  set R : QClass n → QuadForm ℤ n := fun c => Quotient.out (s := intSetoid n) c
  have hR : ∀ c ∈ T, classOf (R c) = c ∧ SameGenus Q (R c) ∧ IntQF.PosDef (R c) ∧
      (R c).hessian.det = Q.hessian.det := fun c hc => out_spec hQ ((hT c).mp hc)
  have hTR : ∀ c ∈ T, ∀ c', c' ∈ T ↔ c' ∈ genusClasses (R c) := by
    intro c hc c'; rw [hT, genusClasses_eq_of_sameGenus (hR c hc).2.1]
  have hdetR : ∀ c ∈ T, ¬ (p : ℤ) ∣ (R c).hessian.det := fun c hc => by rw [(hR c hc).2.2.2]; exact hdet
  have hauto : ∀ c ∈ T, (c.autCard : ℝ) = Nat.card (Aut (R c)) := by
    intro c hc; conv_lhs => rw [← (hR c hc).1]
    rw [QClass.autCard_classOf]
  have hapos : ∀ c ∈ T, (0 : ℝ) < c.autCard := by
    intro c hc; rw [hauto c hc]; exact_mod_cast (hR c hc).2.2.1.card_aut_pos
  -- expand by classes
  have h1 : ∀ c ∈ T, (∑ L ∈ neighbors (R c) p, (latRep (R c) L m : ℝ)) =
      ∑ c' ∈ T, (nbCount (R c) p c' : ℝ) * c'.repNum m :=
    fun c hc => sum_latRep_eq_sum_classes hp2 (hdetR c hc) T (hTR c hc) m
  -- the symmetry
  have h2 : ∀ c ∈ T, ∀ c' ∈ T, (nbCount (R c) p c' : ℝ) / c.autCard = (nbCount (R c') p c : ℝ) / c'.autCard := by
    intro c hc c' hc'
    have := nbCount_mul_autCard hp2 (hR c hc).2.2.1 (hR c' hc').2.2.1 (hdetR c hc) (hdetR c' hc')
    rw [(hR c hc).1, (hR c' hc').1] at this
    have h' : (nbCount (R c) p c' : ℝ) * c'.autCard = (nbCount (R c') p c : ℝ) * c.autCard := by
      rw [hauto c hc, hauto c' hc']; exact_mod_cast this
    rw [div_eq_div_iff (hapos c hc).ne' (hapos c' hc').ne']; linarith
  calc ∑ c ∈ T, (∑ L ∈ neighbors (R c) p, (latRep (R c) L m : ℝ)) / c.autCard
      = ∑ c ∈ T, ∑ c' ∈ T, (nbCount (R c) p c' : ℝ) / c.autCard * c'.repNum m := by
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [h1 c hc, Finset.sum_div]
        exact Finset.sum_congr rfl fun c' _ => by ring
    _ = ∑ c' ∈ T, ∑ c ∈ T, (nbCount (R c') p c : ℝ) * c'.repNum m / c'.autCard := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c' hc' => Finset.sum_congr rfl fun c hc => ?_
        rw [h2 c hc c' hc']; ring
    _ = ∑ c' ∈ T, ((neighbors (R c') p).card : ℝ) * c'.repNum m / c'.autCard := by
        refine Finset.sum_congr rfl fun c' hc' => ?_
        rw [← Finset.sum_div, ← Finset.sum_mul, ← sum_nbCount hp2 (hdetR c' hc') T (hTR c' hc')]
        push_cast; rfl

end GenusSum

/-! ### The genus-averaged neighbour relation for $n = 4$ -/

section Four

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Eichler commutation for the genus, $n = 4$** (coefficient form of $K_p\,\theta_{\mathrm{Gen}} = (p^2 + p + 1 + \varepsilon p)\,\theta_{\mathrm{Gen}}$):
for $Q$ positive definite quaternary, $p$ an odd prime, $p \nmid \det H$, $\varepsilon = \left(\frac{\det H}{p}\right)$, and every $m \in \mathbb{Z}$,
$$r_{\mathrm{Gen}}(p^2m) + \big(p + [p \mid m]\,\varepsilon p\big)\,r_{\mathrm{Gen}}(m) + p^2\,[p^2 \mid m]\,r_{\mathrm{Gen}}(m/p^2)
  = (p^2 + p + 1 + \varepsilon p)\,r_{\mathrm{Gen}}(m),$$
where $r_{\mathrm{Gen}}$ = `genusRepAvg Q` is the $1/|\mathrm{Aut}|$-weighted genus average over $\mathrm{GL}_4(\mathbb{Z})$-classes. The
eigenvalue is the number of $p$-neighbours (`card_neighbors_four`).

*Remark.* This is the neighbour ($T(p^2)$-type) relation; it does **not** give the $T_p$-relation
$r_{\mathrm{Gen}}(pm) + \chi(p)p\,r_{\mathrm{Gen}}(m/p) = (1 + \chi(p)p)\,r_{\mathrm{Gen}}(m)$ (odd powers of $p$ are not related). -/
@[kb "hanke2011aws" "§1.10, p. 23 (p-neighbour graph); Eichler commutation relation"]
theorem genusRepAvg_neighbor_four {Q : QuadForm ℤ 4} (hQ : IntQF.PosDef Q) (hp2 : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (m : ℤ) :
    genusRepAvg Q ((p : ℤ) ^ 2 * m) +
        ((p : ℝ) + (if (p : ℤ) ∣ m then (legendreSym p Q.hessian.det : ℝ) * p else 0)) * genusRepAvg Q m +
        (p : ℝ) ^ 2 * (if (p : ℤ) ^ 2 ∣ m then genusRepAvg Q (m / (p : ℤ) ^ 2) else 0) =
      ((p : ℝ) ^ 2 + p + 1 + (legendreSym p Q.hessian.det : ℝ) * p) * genusRepAvg Q m := by
  classical
  have hF := genusFinite hQ
  set T := hF.finite_classes.toFinset
  have hT : ∀ c, c ∈ T ↔ c ∈ genusClasses Q := fun c => Set.Finite.mem_toFinset _
  have G := genus_sum_neighbors hQ hp2 hdet T hT m
  set R : QClass 4 → QuadForm ℤ 4 := fun c => Quotient.out (s := intSetoid 4) c
  set ε : ℤ := legendreSym p Q.hessian.det
  have hR : ∀ c ∈ T, classOf (R c) = c ∧ SameGenus Q (R c) ∧ IntQF.PosDef (R c) ∧
      (R c).hessian.det = Q.hessian.det := fun c hc => out_spec hQ ((hT c).mp hc)
  have hdetR : ∀ c ∈ T, ¬ (p : ℤ) ∣ (R c).hessian.det := fun c hc => by rw [(hR c hc).2.2.2]; exact hdet
  have hrep : ∀ c ∈ T, ∀ M, c.repNum M = repNum (R c) M := by
    intro c hc M; conv_lhs => rw [← (hR c hc).1]
    rw [QClass.repNum_classOf]
  -- the single-lattice identity and the neighbour count for each class
  have hL : ∀ c ∈ T, (∑ L ∈ neighbors (R c) p, (latRep (R c) L m : ℝ)) =
      repNum (R c) ((p : ℤ) ^ 2 * m) + ((p : ℝ) + (if (p : ℤ) ∣ m then (ε : ℝ) * p else 0)) * repNum (R c) m +
        (p : ℝ) ^ 2 * repNumDiv (R c) p m := by
    intro c hc
    have h := sum_latRep_neighbors_four (hR c hc).2.2.1 hp2 (hdetR c hc) m
    rw [(hR c hc).2.2.2] at h
    have h' : ((∑ L ∈ neighbors (R c) p, (latRep (R c) L m : ℤ) : ℤ) : ℝ) = _ := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    rw [h']
  have hN : ∀ c ∈ T, ((neighbors (R c) p).card : ℝ) = (p : ℝ) ^ 2 + p + 1 + (ε : ℝ) * p := by
    intro c hc
    have h := card_neighbors_four hp2 (hdetR c hc) (Q := R c) (p := p)
    rw [(hR c hc).2.2.2] at h
    exact_mod_cast h
  have G1 : ∑ c ∈ T, ((repNum (R c) ((p : ℤ) ^ 2 * m) : ℝ) +
        ((p : ℝ) + (if (p : ℤ) ∣ m then (ε : ℝ) * p else 0)) * repNum (R c) m +
        (p : ℝ) ^ 2 * repNumDiv (R c) p m) / c.autCard =
      ∑ c ∈ T, ((p : ℝ) ^ 2 + p + 1 + (ε : ℝ) * p) * c.repNum m / c.autCard := by
    calc _ = ∑ c ∈ T, (∑ L ∈ neighbors (R c) p, (latRep (R c) L m : ℝ)) / c.autCard :=
          Finset.sum_congr rfl fun c hc => by rw [hL c hc]
      _ = ∑ c ∈ T, ((neighbors (R c) p).card : ℝ) * c.repNum m / c.autCard := G
      _ = _ := Finset.sum_congr rfl fun c hc => by rw [hN c hc]
  -- in terms of genusRepSum
  have hS : ∀ M, genusRepSum Q M = ∑ c ∈ T, (repNum (R c) M : ℝ) / c.autCard := by
    intro M; rw [genusRepSum_eq_sum hF M]
    exact Finset.sum_congr rfl fun c hc => by rw [hrep c hc]
  have hD : (∑ c ∈ T, (repNumDiv (R c) p m : ℝ) / c.autCard) =
      if (p : ℤ) ^ 2 ∣ m then genusRepSum Q (m / (p : ℤ) ^ 2) else 0 := by
    unfold repNumDiv
    split_ifs with hm
    · rw [hS]
    · simp
  have key : genusRepSum Q ((p : ℤ) ^ 2 * m) +
      ((p : ℝ) + (if (p : ℤ) ∣ m then (ε : ℝ) * p else 0)) * genusRepSum Q m +
      (p : ℝ) ^ 2 * (if (p : ℤ) ^ 2 ∣ m then genusRepSum Q (m / (p : ℤ) ^ 2) else 0) =
      ((p : ℝ) ^ 2 + p + 1 + (ε : ℝ) * p) * genusRepSum Q m := by
    rw [hS, hS, ← hD, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    convert G1 using 1
    · exact Finset.sum_congr rfl fun c _ => by ring
    · exact Finset.sum_congr rfl fun c hc => by rw [hrep c hc]; ring
  have hmass := mass_pos hQ hF
  unfold genusRepAvg
  split_ifs at key ⊢ with h1 h2 h2
  all_goals
    field_simp
    linear_combination key

end Four

end QuadFormsKB.Siegel.Kneser
