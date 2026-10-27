/-
# Coordinates adapted to a vector of norm $\rho$, and transport of the genus count

**Layer:** forms over a number field $F$ in coordinates (`QuadForm F N`), lattices of $F^N$ (`Lat`), the weighted count
$\mathrm{repMass}(L, t) = \sum_{\mathrm{cls}\,M\subseteq\mathrm{gen}\,L}r_M(t)/|O(M)|$.

For the orbital Euler product we count vectors of norm $t$ in the genus of $\mathcal O_F^N$ for a form $Q_0$ that is **not** split.
Weil's argument uses coordinates adapted to a vector $\xi$ of norm $\rho$: an $F$-basis $(\xi, b_1, \dots, b_{N-1})$ with
$b_i \perp \xi$, so that $Q(g x) = \rho x_0^2 + Q'(x_1, \dots, x_{N-1})$, $g = (\xi\,|\,b_1\,|\cdots|\,b_{N-1})$.

**Proves**
* `repMass_compMat` (**transport**): for $g \in \mathrm{GL}_N(F)$, $\mathrm{repMass}_{Q\circ g}(g^{-1}L, t) = \mathrm{repMass}_Q(L, t)$ ($Q$ totally positive
  definite, $L$ integral): the pairs $(M, x)$ correspond by $(M, x) \mapsto (gM, gx)$, the orthogonal groups by conjugation.
* `isTotallyPosDef_compMat`, `isIntegral_compMat`.
* `AdaptedFrame`, `exists_adaptedFrame`: if $Q$ represents $\rho \ne 0$ over $F$, there are $g \in \mathrm{GL}_N(F)$ and a form $Q_0'$ over
  $\mathcal O_F$ in $N - 1$ variables with $Q\circ g = \langle\rho\rangle\perp Q_0'$.

Sources: Weil 1982, §4.5, p. 109 (coordinates adapted to $\xi_\rho$) [unverified]; O'Meara 1963, §42 [unverified]. Indices are
0-based ($e_0$ is the first basis vector).
-/
import QuadFormsKB.Tamagawa.IdealEuler
import QuadFormsKB.Tamagawa.GeneralFactor

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices LocalDensity QuadForm

attribute [local instance] ratAct vecAct

/-! ### Change of coordinates -/

section Transport

variable {F : Type*} [Field F] [NumberField F] {N : ℕ} (Q₁ : QuadForm F N) (g : GL (Fin N) F)

theorem evalIn_compMat_gl (K : Type*) [CommRing K] [Algebra F K] (x : Fin N → K) :
    (Q₁.compMat g.val).evalIn K x = Q₁.evalIn K ((g.val.map (algebraMap F K)) *ᵥ x) := by
  rw [evalIn_eq_eval_map, evalIn_eq_eval_map, ← map_compMat, eval_compMat]

/-- **Conjugation identifies the orthogonal groups**: $\gamma \in O(Q\circ g)(K)$ iff $g\gamma g^{-1} \in O(Q)(K)$. -/
theorem conj_mem_orthGroup_iff (K : Type*) [Field K] [Algebra F K] [CharZero K] (γ : GL (Fin N) K) :
    γ ∈ orthGroup (Q₁.compMat g.val) K ↔
      GeneralLinearGroup.map (algebraMap F K) g * γ * (GeneralLinearGroup.map (algebraMap F K) g)⁻¹ ∈
        orthGroup Q₁ K := by
  set gK := GeneralLinearGroup.map (algebraMap F K) g
  have hgK : gK.val = g.val.map (algebraMap F K) := rfl
  have key : ∀ z, (Q₁.compMat g.val).evalIn K z = Q₁.evalIn K (gK.val *ᵥ z) := by
    intro z; rw [evalIn_compMat_gl, hgK]
  have hv : ∀ (A B : GL (Fin N) K) (z : Fin N → K), (A * B).val *ᵥ z = A.val *ᵥ (B.val *ᵥ z) := by
    intro A B z; rw [Units.val_mul, mulVec_mulVec]
  constructor
  · intro hγ
    refine mem_orthGroup_of_evalIn _ fun z => ?_
    rw [hv, hv, ← key, evalIn_mulVec_of_mem _ hγ, key, ← hv, mul_inv_cancel, Units.val_one, one_mulVec]
  · intro hγ
    refine mem_orthGroup_of_evalIn _ fun z => ?_
    rw [key, key]
    have h1 := evalIn_mulVec_of_mem _ hγ (gK.val *ᵥ z)
    rwa [hv, hv, ← hv gK⁻¹, inv_mul_cancel, Units.val_one, one_mulVec] at h1

theorem isTotallyPosDef_compMat (h : IsTotallyPosDef Q₁) : IsTotallyPosDef (Q₁.compMat g.val) := by
  intro x hx
  rw [eval_compMat]
  apply h
  intro h0
  apply hx
  have := congrArg (fun y => g⁻¹.val *ᵥ y) h0
  simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, mulVec_zero] using this

theorem evalIn_self_compMat (x : Fin N → F) : (Q₁.compMat g.val).evalIn F x = Q₁.evalIn F (g.val *ᵥ x) := by
  rw [evalIn_compMat_gl]; rfl

theorem isIntegral_compMat {L : Lat F N} (h : IsIntegral Q₁ L.1) :
    IsIntegral (Q₁.compMat g.val) (Lat.image g⁻¹ L).1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  show (Q₁.compMat g.val).evalIn F (g⁻¹.val *ᵥ y) ∈ _
  rw [evalIn_self_compMat, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  exact h y hy

theorem sameGenus_compMat {L M : Submodule (𝓞 F) (Fin N → F)} (h : SameGenus (Q₁.compMat g.val) L M) :
    SameGenus Q₁ (glImage g L) (glImage g M) := by
  intro v
  obtain ⟨γ, hγ, hγM⟩ := h v
  set gv := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) g
  refine ⟨gv * γ * gv⁻¹, (conj_mem_orthGroup_iff Q₁ g _ γ).mp hγ, ?_⟩
  rw [loc_glImage, loc_glImage, ← locAct_mul]
  simp only [gv, mul_assoc, inv_mul_cancel, mul_one]
  rw [locAct_mul, hγM]

theorem sameGenus_compMat' {L M : Submodule (𝓞 F) (Fin N → F)} (h : SameGenus Q₁ (glImage g L) (glImage g M)) :
    SameGenus (Q₁.compMat g.val) L M := by
  intro v
  obtain ⟨γ, hγ, hγM⟩ := h v
  set gv := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) g
  refine ⟨gv⁻¹ * γ * gv, (conj_mem_orthGroup_iff Q₁ g _ _).mpr (by
    rw [show gv * (gv⁻¹ * γ * gv) * gv⁻¹ = γ by group]; exact hγ), ?_⟩
  rw [loc_glImage, loc_glImage] at hγM
  rw [locAct_mul, locAct_mul, hγM, ← locAct_mul, inv_mul_cancel, locAct_one]

theorem glImage_inv_glImage (L : Submodule (𝓞 F) (Fin N → F)) : glImage g (glImage g⁻¹ L) = L := by
  rw [← glImage_mul, mul_inv_cancel, glImage_one]

/-- **Transport of the genus count along a change of coordinates**: for $Q$ totally positive definite, $L$ integral and
$g \in \mathrm{GL}_N(F)$, $\mathrm{repMass}_{Q\circ g}(g^{-1}L, t) = \mathrm{repMass}_Q(L, t)$. -/
theorem repMass_compMat (hpd : IsTotallyPosDef Q₁) {L : Lat F N} (hLi : IsIntegral Q₁ L.1) (t : F) :
    repMass (Q₁.compMat g.val) (Lat.image g⁻¹ L) t = repMass Q₁ L t := by
  set Q₂ := Q₁.compMat g.val
  set L₂ := Lat.image g⁻¹ L
  rw [repMass_eq_orbitMass_pairs (isTotallyPosDef_compMat Q₁ g hpd) L₂ (isIntegral_compMat Q₁ g hLi) t,
    repMass_eq_orbitMass_pairs hpd L hLi t]
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
  let P : pairSMA Q₂ L₂ t → pairSMA Q₁ L t := fun p =>
    ⟨(Lat.image g p.1.1, g.val *ᵥ p.1.2), by
      obtain ⟨hM, hx, hQ⟩ := p.2
      refine ⟨?_, mulVec_mem_glImage hx, ?_⟩
      · show SameGenus Q₁ L.1 (glImage g p.1.1.1)
        have := sameGenus_compMat Q₁ g hM
        rwa [show glImage g L₂.1 = L.1 from glImage_inv_glImage g L.1] at this
      · exact (evalIn_self_compMat Q₁ g p.1.2).symm.trans hQ⟩
  have hPsmul : ∀ (γ : orthGroup Q₂ F) (p : pairSMA Q₂ L₂ t), P (γ • p) = φ γ • P p := by
    intro γ p
    apply Subtype.ext
    show (Lat.image g (Lat.image (γ : GL (Fin N) F) p.1.1), g.val *ᵥ ((γ : GL (Fin N) F).val *ᵥ p.1.2)) =
      (Lat.image (g * (γ : GL (Fin N) F) * g⁻¹) (Lat.image g p.1.1),
        (g * (γ : GL (Fin N) F) * g⁻¹).val *ᵥ (g.val *ᵥ p.1.2))
    refine Prod.ext (Subtype.ext ?_) ?_
    · show glImage g (glImage _ _) = glImage _ (glImage g _)
      rw [← glImage_mul, ← glImage_mul, inv_mul_cancel_right]
    · rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  have hPinj : Function.Injective P := by
    intro a b h
    have h1 := congrArg (fun p : pairSMA Q₁ L t => (p : Lat F N × (Fin N → F))) h
    simp only [P, Prod.mk.injEq] at h1
    apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) ?_
    · have := congrArg (fun M : Lat F N => glImage g⁻¹ M.1) h1.1
      simpa [Lat.image, ← glImage_mul, glImage_one] using this
    · have := congrArg (fun x => g⁻¹.val *ᵥ x) h1.2
      simpa [mulVec_mulVec] using this
  have hPsurj : Function.Surjective P := by
    intro q
    obtain ⟨hM, hx, hQ⟩ := q.2
    refine ⟨⟨(Lat.image g⁻¹ q.1.1, g⁻¹.val *ᵥ q.1.2), ?_, mulVec_mem_glImage hx, ?_⟩, ?_⟩
    · show SameGenus Q₂ (glImage g⁻¹ L.1) (glImage g⁻¹ q.1.1.1)
      apply sameGenus_compMat'
      rw [glImage_inv_glImage, glImage_inv_glImage]; exact hM
    · show Q₂.evalIn F (g⁻¹.val *ᵥ q.1.2) = t
      rw [evalIn_self_compMat, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact hQ
    · apply Subtype.ext
      refine Prod.ext (Subtype.ext ?_) ?_
      · exact glImage_inv_glImage g q.1.1.1
      · show g.val *ᵥ (g⁻¹.val *ᵥ q.1.2) = q.1.2
        rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
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

/-! ### Coordinates adapted to a vector of norm $\rho$ -/

section Frame

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- **A frame adapted to $\rho$** for $Q$ over $F$ in $n+1$ variables: $g \in \mathrm{GL}_{n+1}(F)$ and a form $Q_0'$ over $\mathcal O_F$ in $n$
variables with $Q\circ g = \langle\rho\rangle\perp Q_0'$, i.e. $Q(g x) = \rho x_0^2 + Q_0'(x_1, \dots, x_n)$; the first column $\xi = ge_0$ has
$Q(\xi) = \rho$ and the others span $\xi^\perp$ (Weil 1982, §4.5, p. 109: the stabilizer of $\xi$ is $O(\xi^\perp)$). Fields: `g`, `Q'`,
`compMat_eq`. -/
structure AdaptedFrame (Q : QuadForm F (n + 1)) (ρ : F) where
  /-- The change of coordinates (first column $\xi$, $Q(\xi) = \rho$). -/
  g : GL (Fin (n + 1)) F
  /-- The complement form, over $\mathcal O_F$. -/
  Q' : QuadForm (𝓞 F) n
  /-- $Q\circ g = \langle\rho\rangle\perp Q'$. -/
  compMat_eq : Q.compMat g.val = splitForm ρ (Q'.map (algebraMap (𝓞 F) F))

theorem compMat_smul_coeff {A : Type*} [CommRing A] {N r : ℕ} (Q : QuadForm A N) (d : A)
    (X : Matrix (Fin N) (Fin r) A) (i j : Fin r) :
    (Q.compMat (d • X)).coeff i j = d ^ 2 * (Q.compMat X).coeff i j := by
  rw [compMat_coeff, compMat_coeff]
  split_ifs
  · have : (fun l => (d • X) l i) = d • fun l => X l i := by funext l; simp
    rw [this, eval_smul_gen]
  · have h1 : (fun l => (d • X) l i) = d • fun l => X l i := by funext l; simp
    have h2 : (fun l => (d • X) l j) = d • fun l => X l j := by funext l; simp
    rw [h1, h2, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  · simp

/-- **Existence of an adapted frame** (O'Meara 1963, §42 [unverified]): if $Q(\xi) = \rho \ne 0$ for some $\xi \in F^{n+1}$, then $Q$ has a frame
adapted to $\rho$. *Proof:* $\xi^\perp = \ker B(\xi, \cdot)$ has dimension $n$ and does not contain $\xi$ ($B(\xi,\xi) = 2\rho$); take $\xi$ and $d$ times a
basis of $\xi^\perp$, $d \in \mathcal O_F$ clearing the denominators of the Gram form on $\xi^\perp$. -/
theorem exists_adaptedFrame (Q : QuadForm F (n + 1)) {ξ : Fin (n + 1) → F} {ρ : F} (hξ : Q.eval ξ = ρ)
    (hρ : ρ ≠ 0) : Nonempty (AdaptedFrame Q ρ) := by
  classical
  set H := Q.hessian
  -- the functional `B(ξ, ·)` and its kernel `ξ^⊥`
  let φ : (Fin (n + 1) → F) →ₗ[F] F :=
    { toFun := fun y => (H *ᵥ ξ) ⬝ᵥ y
      map_add' := fun a b => by simp [dotProduct_add]
      map_smul' := fun c a => by simp [dotProduct_smul] }
  have hφξ : φ ξ = 2 * ρ := by
    show (H *ᵥ ξ) ⬝ᵥ ξ = 2 * ρ
    rw [← hξ, dotProduct_comm, dotProduct_hessian_self]
  have hφ0 : φ ξ ≠ 0 := by rw [hφξ]; exact mul_ne_zero two_ne_zero hρ
  set W := LinearMap.ker φ
  have hrange : LinearMap.range φ = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ⟨(c / φ ξ) • ξ, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hφ0]
  have hW : Module.finrank F W = n := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrange] at this
    simp only [finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
    change 1 + Module.finrank F (LinearMap.ker φ) = n + 1 at this
    show Module.finrank F (LinearMap.ker φ) = n
    omega
  let b := Module.finBasisOfFinrankEq F W hW
  let Bm : Matrix (Fin (n + 1)) (Fin n) F := Matrix.of fun i k => (b k : Fin (n + 1) → F) i
  -- clearing denominators of `Q ∘ Bm`
  set Q'' := Q.compMat Bm
  obtain ⟨d₀, hd₀⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    (Finset.univ.image fun p : Fin n × Fin n => Q''.coeff p.1 p.2)
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
  let Q'o : QuadForm (𝓞 F) n := QuadForm.ofUpper a
  have hQ'o : Q'o.map (algebraMap (𝓞 F) F) = Q.compMat ((d : F) • Bm) := by
    refine ext_upper fun i j hij => ?_
    rw [compMat_smul_coeff]
    simp only [Q'o, QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply, if_pos hij]
    exact ha i j
  -- the matrix `G = (ξ | d b₀ | … | d b_{n-1})`
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.of fun i j => (Fin.cons (ξ i) (fun k => (d : F) * Bm i k) : Fin (n + 1) → F) j
  have hGv : ∀ x : Fin (n + 1) → F, G *ᵥ x = x 0 • ξ + ((d : F) • Bm) *ᵥ Fin.tail x := by
    intro x
    funext i
    simp only [G, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Fin.tail]
    ring_nf
  have hBmW : ∀ y : Fin n → F, Bm *ᵥ y ∈ W := by
    intro y
    have : Bm *ᵥ y = ∑ k, y k • (b k : Fin (n + 1) → F) := by
      funext i; simp [Bm, mulVec, dotProduct, mul_comm]
    rw [this]
    exact W.sum_mem fun k _ => W.smul_mem _ (b k).2
  have hφB : ∀ y, φ (Bm *ᵥ y) = 0 := fun y => hBmW y
  have hGinj : ∀ x, G *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hGv] at hx
    have h1 := congrArg φ hx
    rw [map_add, map_smul, smul_mulVec, map_smul, hφB, smul_zero, add_zero, map_zero, smul_eq_mul] at h1
    have hx0 : x 0 = 0 := (mul_eq_zero.mp h1).resolve_right hφ0
    rw [hx0, zero_smul, zero_add, smul_mulVec] at hx
    have h2 : Bm *ᵥ Fin.tail x = 0 := (smul_eq_zero.mp hx).resolve_left hdF
    have h3 : ∑ k, Fin.tail x k • b k = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      rw [← h2]; funext i; simp [Bm, mulVec, dotProduct, mul_comm]
    have h4 := b.linearIndependent
    have h5 : ∀ k, Fin.tail x k = 0 := fun k => (Fintype.linearIndependent_iff.mp h4) _ h3 k
    funext i
    refine Fin.cases hx0 (fun k => h5 k) i
  have hdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hx0 (hGinj x hx)
  let g : GL (Fin (n + 1)) F := Matrix.GeneralLinearGroup.mk'' G hdet
  refine ⟨⟨g, Q'o, ?_⟩⟩
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat, show g.val = G from rfl, hGv, hQ'o, add_comm (x 0 • ξ), eval_add_smul_gen]
  have horth : (H *ᵥ (((d : F) • Bm) *ᵥ Fin.tail x)) ⬝ᵥ ξ = 0 := by
    rw [hess_dot_comm, smul_mulVec, dotProduct_smul]
    have := hφB (Fin.tail x)
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this, smul_zero]
  rw [horth, mul_zero, add_zero, hξ]
  conv_rhs => rw [← Fin.cons_self_tail x, eval_splitForm_cons, eval_compMat]
  ring

end Frame

end QuadFormsKB.Tamagawa
