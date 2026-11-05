/-
# O'Meara 93:28, proof of the necessity: representations for a first component with $m$ blocks, and the flip

**Proves**
* `rep_flip_of_hyperbolic`: if $FB \to FB' \perp \langle -c\rangle$ and $\operatorname{rank} B = \operatorname{rank} B'$
  (regular lattices, $c \ne 0$), then $FB' \to FB \perp \langle c\rangle$. (The hyperbolicity of $FB$, that the
  book's wording suggests, is not needed: Witt ring identity $[B'] - [z] = [B] + [c]$ from $[B'] - [c] = [B] + [z]$.)
-/
import QuadFormsKB.Literature.OMeara.Sec93FRepTransfer
import QuadFormsKB.Literature.OMeara.Sec93FNecRep
import QuadFormsKB.Literature.OMeara.Sec93FNecBlock
import QuadFormsKB.Literature.OMeara.Sec93FMerge

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.NecBlocks

open RepTransfer
open QuadFormsKB.OMeara.D18 (subQ spanF)

section Flip

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {U U' H T : Type*} [AddCommGroup U] [Module F U] [AddCommGroup U'] [Module F U']
  [AddCommGroup H] [Module F H] [AddCommGroup T] [Module F T]

/-- **Splitting off an embedded nonsingular summand**: if $H$ is nonsingular and embeds in $T$, then
$T \cong H \perp Z$ for a subspace $Z \subseteq T$, with $\dim Z + \dim H = \dim T$. -/
theorem exists_complement [FiniteDimensional F T] {QT : QuadraticForm F T} {QH : QuadraticForm F H}
    (hH : (polarBilin QH).Nondegenerate) {f : H →ₗ[F] T} (hf : Function.Injective f)
    (hQ : ∀ x, QT (f x) = QH x) :
    ∃ Z : Submodule F T, Nonempty ((QH.prod (QT.comp Z.subtype)).IsometryEquiv QT) ∧
      finrank F Z + finrank F H = finrank F T := by
  classical
  set B : LinearMap.BilinForm F T := associated QT with hB
  have hrefl : B.IsRefl := fun x y h => by
    have h' : bil QT x y = 0 := h
    show bil QT y x = 0
    rw [bil_comm]; exact h'
  set S : Submodule F T := LinearMap.range f with hS
  have hbil : ∀ a b : H, bil QT (f a) (f b) = bil QH a b := by
    intro a b
    have h1 := RepTransfer.polar_eq_two_bil QT (f a) (f b)
    have h2 := RepTransfer.polar_eq_two_bil QH a b
    have h3 : polar QT (f a) (f b) = polar QH a b := QuadraticForm.Witt.polar_map_of_map_app hQ a b
    have h2' : (2 : F) ≠ 0 := two_ne_zero' F
    apply mul_left_cancel₀ h2'
    rw [← h1, ← h2, h3]
  have hSnd : (B.restrict S).Nondegenerate := by
    have key : ∀ x : S, (∀ y : S, B x y = 0) → x = 0 := by
      rintro ⟨_, a, rfl⟩ hx
      have ha : a = 0 := by
        rw [QuadraticForm.nondegenerate_polarBilin_iff] at hH
        refine hH a fun b => ?_
        rw [RepTransfer.polar_eq_two_bil, ← hbil]
        have : bil QT (f a) (f b) = 0 := hx ⟨f b, b, rfl⟩
        rw [this, mul_zero]
      subst ha; simp
    refine ⟨fun x hx => key x fun y => hx y, fun y hy => key y fun x => ?_⟩
    have h' : bil QT (x : T) (y : T) = 0 := hy x
    show bil QT (y : T) (x : T) = 0
    exact (bil_comm QT (y : T) (x : T)).trans h'
  have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hSnd
  set Z := B.orthogonal S with hZ
  have hZmem : ∀ z : T, z ∈ Z → ∀ a : H, bil QT (f a) z = 0 := by
    intro z hz a
    exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hz) (f a) ⟨a, rfl⟩
  refine ⟨Z, ⟨?_⟩, ?_⟩
  · let e : H ≃ₗ[F] S := LinearEquiv.ofInjective f hf
    let e2 : (H × Z) ≃ₗ[F] T :=
      (e.prodCongr (LinearEquiv.refl F Z)).trans (Submodule.prodEquivOfIsCompl S Z hc)
    refine { e2 with map_app' := fun p => ?_ }
    show QT ((e2 p : T)) = QH p.1 + QT (p.2 : T)
    have : (e2 p : T) = f p.1 + (p.2 : T) := rfl
    rw [this, Q_add, hZmem _ p.2.2 p.1, hQ]
    ring
  · have := Submodule.finrank_add_eq_of_isCompl hc
    have h2 : finrank F S = finrank F H := (LinearEquiv.ofInjective f hf).finrank_eq.symm
    omega

/-- A one-dimensional form $Z$ embeds in the hyperbolic plane $\langle c\rangle \perp \langle -c\rangle$ ($c \ne 0$):
$c(x^2 - y^2) = z$ has the solution $x = (1 + z/c)/2$, $y = (z/c - 1)/2$, $(x, y) \ne 0$. -/
theorem rep_one_dim_hyp {Z : Type*} [AddCommGroup Z] [Module F Z] (QZ : QuadraticForm F Z)
    (hZ : finrank F Z = 1) {c : F} (hc : c ≠ 0) :
    Rep QZ ((c • (QuadraticMap.sq : QuadraticForm F F)).prod
      ((-c) • (QuadraticMap.sq : QuadraticForm F F))) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero' F
  haveI : FiniteDimensional F Z := Module.finite_of_finrank_eq_succ hZ
  let b : Basis (Fin 1) F Z := Module.finBasisOfFinrankEq F Z hZ
  set z := QZ (b 0) with hz
  set x : F := (1 + z / c) / 2 with hx
  set y : F := (z / c - 1) / 2 with hy
  have hxy : x - y = 1 := by rw [hx, hy]; field_simp; ring
  have hxy2 : c * (x * x - y * y) = z := by
    have : x * x - y * y = (x - y) * (x + y) := by ring
    have hxpy : x + y = z / c := by rw [hx, hy]; field_simp; ring
    rw [this, hxy, one_mul, hxpy]; field_simp
  have hv : ∀ v : Z, v = b.repr v 0 • b 0 := fun v => by
    have := b.sum_repr v
    rw [Fin.sum_univ_one] at this
    exact this.symm
  refine ⟨(b.coord 0).smulRight ((x, y) : F × F), ?_, fun v => ?_⟩
  · intro v w hvw
    have h1 : b.coord 0 v • ((x, y) : F × F) = b.coord 0 w • ((x, y) : F × F) := hvw
    have hne : ((x, y) : F × F) ≠ 0 := fun h => by
      have h1 : x = 0 := congrArg Prod.fst h
      have h2 : y = 0 := congrArg Prod.snd h
      have : x - y = 0 := by rw [h1, h2]; ring
      rw [hxy] at this; exact one_ne_zero this
    have h2 : b.coord 0 v = b.coord 0 w := by
      by_contra hne'
      apply hne
      have : (b.coord 0 v - b.coord 0 w) • ((x, y) : F × F) = 0 := by rw [sub_smul, h1, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')
    rw [hv v, hv w]; exact congrArg (· • b 0) h2
  · have hcoord : ∀ v : Z, QZ v = (b.repr v 0) ^ 2 * z := fun v => by
      conv_lhs => rw [hv v]
      rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]
    simp only [LinearMap.smulRight_apply, QuadraticMap.prod_apply, Prod.smul_mk, Basis.coord_apply]
    rw [hcoord v]
    simp only [QuadraticMap.smul_apply, QuadraticMap.sq_apply, smul_eq_mul]
    rw [← hxy2]; ring

/-- **The flip (abstract form)**: if $B \to B' \perp \langle -c\rangle$ with $\dim B = \dim B'$, then
$B' \to B \perp \langle c\rangle$. (With $B' \perp \langle -c\rangle \cong B \perp Z$, $Z$ a line, cancel $\langle -c\rangle$
in $B' \perp \langle -c\rangle \to (B \perp \langle c\rangle) \perp \langle -c\rangle$, using that $Z$ embeds in the
hyperbolic plane $\langle c\rangle \perp \langle -c\rangle$.) -/
theorem rep_flip [FiniteDimensional F U] [FiniteDimensional F U'] {B : QuadraticForm F U}
    {B' : QuadraticForm F U'} (hB : (polarBilin B).Nondegenerate) {c : F} (hc : c ≠ 0)
    (hdim : finrank F U = finrank F U')
    (h : Rep B (B'.prod ((-c) • (QuadraticMap.sq : QuadraticForm F F)))) :
    Rep B' (B.prod (c • (QuadraticMap.sq : QuadraticForm F F))) := by
  obtain ⟨f, hf, hQ⟩ := h
  obtain ⟨Z, ⟨eZ⟩, hZdim⟩ := exists_complement hB hf hQ
  have hZ1 : finrank F Z = 1 := by
    rw [Module.finrank_prod, Module.finrank_self] at hZdim
    omega
  have hCp := nondegenerate_smul_sq (F := F) hc
  have hCm := nondegenerate_smul_sq (F := F) (neg_ne_zero.2 hc)
  have hZrep := rep_one_dim_hyp ((B'.prod ((-c) • (QuadraticMap.sq : QuadraticForm F F))).comp Z.subtype)
    hZ1 hc
  have h3 := Rep.prod_left B hZrep
  have h' := Rep.congr eZ.symm (assoc3 B (c • (QuadraticMap.sq : QuadraticForm F F))
    ((-c) • (QuadraticMap.sq : QuadraticForm F F))) h3
  exact Rep.cancel_right (QuadraticForm.nondegenerate_polarBilin_prod hB hCp) hCm h'

end Flip

section Lattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- $\dim FL = \operatorname{rank} L$ for a finitely generated regular lattice. -/
theorem finrank_spanF_of_isRegular {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) :
    finrank F (D18.spanF F L) = finrank R L := by
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hfg
  exact D18.finrank_spanF Q L b (Transfer28.det_gram_ne_zero_of_isRegular Q hreg b)

/-- **(2) The flip** (O'Meara 1963, §93F, proof of 93:28, p. 271, "$FL_t \perp \langle \dots\rangle \cong FK_t^{-1} \perp
\langle a_t\rangle$ since $FL_t$ is hyperbolic ... by Witt's theorem"): for finitely generated regular lattices
$B$, $B'$ of the same rank and $c \ne 0$, $FB \to FB' \perp \langle -c\rangle$ implies $FB' \to FB \perp \langle c\rangle$.
The hyperbolicity of $FB$ (a block base of $B$) is not needed. -/
@[kb "omeara1963" "§93F, proof of 93:28, p. 271 (the flip: FB → FB' ⊥ ⟨-c⟩ gives FB' → FB ⊥ ⟨c⟩; Witt)"]
theorem rep_flip_of_hyperbolic [FiniteDimensional F V] {B B' : Submodule R V} (hBfg : B.FG) (hB'fg : B'.FG)
    (hBreg : IsRegular Q B) (hB'reg : IsRegular Q B') (hrk : finrank R B = finrank R B') {c : F} (hc : c ≠ 0)
    (h : SpanRepresents Q B B' (-c)) : SpanRepresents Q B' B c := by
  rw [spanRepresents_iff_rep] at h ⊢
  refine rep_flip (nondegenerate_subQ Q hBreg) hc ?_ h
  rw [finrank_spanF_of_isRegular Q hBfg hBreg, finrank_spanF_of_isRegular Q hB'fg hB'reg, hrk]

end Lattice

section Frame

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [CharZero F]
  [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **From a frame (a family spanning $FM$) to `SpanRepresents`**: if $v_i$ ($i \in \iota$) are linearly independent
over $F$ with $F\text{-span} = FM$, $M$ regular, and $X_i = (u_i, t_i) \in V \times F$ satisfy $u_i \in FN$ and
$B(u_i, u_j) + c\,t_it_j = B(v_i, v_j)$, then $FM \to FN \perp \langle c\rangle$. -/
theorem spanRepresents_of_frame_family {ι : Type*} [Fintype ι] [DecidableEq ι] {M N : Submodule R V}
    [FiniteDimensional F V] (hreg : IsRegular Q M) (c : F) (v : ι → V) (hli : LinearIndependent F v)
    (hsp : span F (Set.range v) = span F (M : Set V)) (X : ι → V × F)
    (hX : ∀ k, (X k).1 ∈ span F (N : Set V))
    (hG : ∀ k l, bil Q (X k).1 (X l).1 + c * ((X k).2 * (X l).2) = bil Q (v k) (v l)) :
    SpanRepresents Q M N c := by
  classical
  let b : Basis ι F (span F (M : Set V)) := (Basis.span hli).map (LinearEquiv.ofEq _ _ hsp)
  have hb : ∀ k, (b k : V) = v k := fun k => by simp [b, Basis.span_apply]
  let g : ι → span F (N : Set V) × F := fun k => (⟨(X k).1, hX k⟩, (X k).2)
  let f : span F (M : Set V) →ₗ[F] span F (N : Set V) × F := b.constr F g
  have hfb : ∀ k, f (b k) = g k := fun k => by simp [f]
  have hfx : ∀ x, f x = ∑ k, b.repr x k • g k := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, hfb]
  have hfx' : ∀ x, (((f x).1 : V), (f x).2) = ∑ k, b.repr x k • X k := by
    intro x
    rw [hfx x]
    ext <;> simp [g, Prod.fst_sum, Prod.snd_sum]
  have hxv : ∀ x : span F (M : Set V), (x : V) = ∑ k, b.repr x k • v k := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, hb]
  have hgramW : gram (NecBase.repForm Q c) X = gram Q v := by
    ext k l
    simp only [gram, Matrix.of_apply, NecBase.bil_repForm]
    exact hG k l
  have hiso : ∀ x, Q ((f x).1 : V) + c * (f x).2 ^ 2 = Q (x : V) := by
    intro x
    have e1 := congrArg (NecBase.repForm Q c) (hfx' x)
    rw [NecBase.repForm_apply] at e1
    have e2 : NecBase.repForm Q c (∑ k, b.repr x k • X k) =
        b.repr x ⬝ᵥ gram (NecBase.repForm Q c) X *ᵥ b.repr x :=
      D18.Q_sum_gram (NecBase.repForm Q c) X (b.repr x)
    have e3 : Q (x : V) = b.repr x ⬝ᵥ gram Q v *ᵥ b.repr x := by
      rw [hxv x]; exact D18.Q_sum_gram Q v _
    simp only at e1
    rw [e3, ← hgramW, ← e2, ← e1]; ring
  refine ⟨f, ?_, hiso⟩
  -- injectivity from the nonsingularity of `FM`
  have hnd := nondegenerate_subQ Q hreg
  rw [QuadraticForm.nondegenerate_polarBilin_iff] at hnd
  let φ : span F (M : Set V) →ₗ[F] V × F :=
    ((span F (N : Set V)).subtype ∘ₗ LinearMap.fst F _ F ∘ₗ f).prod (LinearMap.snd F _ F ∘ₗ f)
  have hφ : ∀ z, φ z = (((f z).1 : V), (f z).2) := fun z => rfl
  have hQ' : ∀ z, NecBase.repForm Q c (φ z) = (subQ Q M) z := by
    intro z
    rw [hφ, NecBase.repForm_apply]
    show Q ((f z).1 : V) + c * ((f z).2 * (f z).2) = Q (z : V)
    rw [← hiso z]; ring
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  refine hnd x fun y => ?_
  have h1 := QuadraticForm.Witt.polar_map_of_map_app (f := φ) (Q := subQ Q M)
    (Q' := NecBase.repForm Q c) hQ' x y
  have hx' : φ x = 0 := by rw [hφ, hx]; rfl
  rw [hx'] at h1
  rw [← h1]
  simp [QuadraticMap.polar]

end Frame

section Induction

open NecBlock NecBase Sat93 Arith28 Transfer28

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **$m$ rounds of O'Meara's argument** (induction on $m$ as in `NecBlock.block_disc`): a family of $m$ pairs in
$K_1$ with `BlockData` ($Q(z_k^{(1)}) \in a_0\mathfrak o^\times$) and a vector $\zeta \in V \times F$ orthogonal to all of
them with $Q(\zeta) \in a_0 + \mathfrak w$ give $m$ mutually orthogonal hyperbolic pairs in
$\operatorname{span}\{z_k^{(i)}, \zeta\}$ of the space $V \times F$ with the form $Q(x) + a_0 t^2$. -/
theorem rep_blocks_ind (h2p : ¬ IsUnit (2 : R)) [Finite (ResidueField R)] {K₁ : Submodule R V}
    (hK1 : ∀ u ∈ K₁, ∀ v ∈ K₁, ∃ r : R, algebraMap R F r = bil Q u v)
    {s₂ : Submodule R F} (hs₂R : ∀ z ∈ s₂, ∃ r ∈ maximalIdeal R, algebraMap R F r = z)
    {g₁ g₂ : AddSubgroup F} (hg₂₁ : g₂ ≤ g₁) (hsq₂ : ∀ x ∈ g₂, ∀ r : R, algebraMap R F r ^ 2 * x ∈ g₂)
    (h2s : ∀ z ∈ s₂, 2 * z ∈ g₂) (hsg : ∀ z ∈ s₂, ∀ x ∈ g₁, z ^ 2 * x ∈ g₂) {X : Submodule R F}
    (key : ∀ c : R, c ∈ maximalIdeal R → ∀ α ∈ g₁, ∀ β ∈ g₂,
      SqEquivMod X ((1 - algebraMap R F c) ^ 2 + α * β) 1)
    {a₀ w : F} (ha0 : a₀ ≠ 0) (hw0 : w ≠ 0) (ha0R : ∃ r : R, algebraMap R F r = a₀)
    (hw1 : ∃ r : R, algebraMap R F r = w) (hw2 : ∃ r : R, algebraMap R F r * w = 2)
    (hf : ∀ x ∈ X, ∃ ρ ∈ maximalIdeal R, x = algebraMap R F ρ * (4 * a₀ / w))
    (hAα : ∀ z ∈ g₁, ∃ α b : R, z = a₀ * algebraMap R F α ^ 2 + w * algebraMap R F b)
    (hρa : ∀ z ∈ g₂, ∃ ρ ∈ maximalIdeal R, z = algebraMap R F ρ * a₀) :
    ∀ (m : ℕ) (z : Fin m → V × V), BlockData Q K₁ s₂ g₁ g₂ z →
      (∀ k, ∃ u : R, IsUnit u ∧ Q (z k).1 = a₀ * algebraMap R F u) →
      ∀ ζ : V × F, (∀ k, bil Q (z k).1 ζ.1 = 0 ∧ bil Q (z k).2 ζ.1 = 0) →
      (∃ b : R, repForm Q a₀ ζ = a₀ + w * algebraMap R F b) →
      ∃ r : Fin m → (V × F) × (V × F),
        (∀ S : Submodule F (V × F), (∀ k, ((z k).1, (0 : F)) ∈ S ∧ ((z k).2, (0 : F)) ∈ S) → ζ ∈ S →
          ∀ k, (r k).1 ∈ S ∧ (r k).2 ∈ S) ∧
        (∀ k, repForm Q a₀ (r k).1 = 0 ∧ repForm Q a₀ (r k).2 = 0 ∧
          bil (repForm Q a₀) (r k).1 (r k).2 = 1) ∧
        (∀ k l, k ≠ l → bil (repForm Q a₀) (r k).1 (r l).1 = 0 ∧ bil (repForm Q a₀) (r k).1 (r l).2 = 0 ∧
          bil (repForm Q a₀) (r k).2 (r l).1 = 0 ∧ bil (repForm Q a₀) (r k).2 (r l).2 = 0) := by
  classical
  have hs₂R' : ∀ z ∈ s₂, ∃ r : R, algebraMap R F r = z := fun z hz => by
    obtain ⟨r, -, hr⟩ := hs₂R z hz; exact ⟨r, hr⟩
  have hsmul : ∀ {x y : F}, x ∈ s₂ → (∃ r : R, algebraMap R F r = y) → x * y ∈ s₂ := by
    rintro x y hx ⟨r, rfl⟩
    rw [mul_comm, ← Algebra.smul_def]; exact smul_mem _ _ hx
  have hQW : ∀ u : V, repForm Q a₀ (u, 0) = Q u := fun u => by rw [NecBase.repForm_apply]; simp
  have hbW : ∀ u v : V, bil (repForm Q a₀) (u, 0) (v, 0) = bil Q u v := fun u v => by rw [NecBase.bil_repForm]; simp
  have hbζ : ∀ (u : V) (ζ : V × F), bil (repForm Q a₀) (u, 0) ζ = bil Q u ζ.1 := fun u ζ => by
    rw [NecBase.bil_repForm]; simp
  intro m
  induction m with
  | zero =>
    intro z _ _ ζ _ _
    exact ⟨fun k => k.elim0, fun S _ _ k => k.elim0, fun k => k.elim0, fun k => k.elim0⟩
  | succ m ih =>
    intro z hz hunit ζ hζ hζQ
    set p := z 0 with hpdef
    obtain ⟨A, hA⟩ := hK1 _ (hz.mem₁ 0) _ (hz.mem₁ 0)
    obtain ⟨Bv, hBv⟩ := hK1 _ (hz.mem₁ 0) _ (hz.mem₂ 0)
    obtain ⟨C, hC⟩ := hK1 _ (hz.mem₂ 0) _ (hz.mem₂ 0)
    rw [bil_self] at hA hC
    obtain ⟨c, hcm, hc⟩ := hs₂R _ (neg_mem (hz.b 0))
    have hbil : bil Q p.1 p.2 = 1 - algebraMap R F c := by rw [hc]; ring
    have hp : SqEquivMod X (bil Q p.1 p.2 ^ 2 - Q p.1 * Q p.2) 1 := by
      have := key c hcm (Q p.1) (hz.q₁ 0) (-Q p.2) (neg_mem (hz.q₂ 0))
      convert this using 1; rw [hbil]; ring
    have hunitp : IsUnit (A * C - Bv ^ 2) := by
      obtain ⟨⟨u, hu, hu'⟩, -⟩ := hp
      rw [mul_one] at hu'
      have : A * C - Bv ^ 2 = -u := IsFractionRing.injective R F (by
        rw [map_sub, map_mul, map_pow, map_neg, hA, hC, hBv]; linear_combination -hu')
      rw [this]; exact hu.neg
    have hne : ∀ k : Fin m, k.succ ≠ 0 := fun k => Fin.succ_ne_zero k
    obtain ⟨r₀, r₁, hr₀, hr₁, ho₀, ho₁⟩ : ∃ r₀ r₁ : Fin m → R, (∀ k, algebraMap R F (r₀ k) ∈ s₂) ∧
        (∀ k, algebraMap R F (r₁ k) ∈ s₂) ∧
        (∀ k, bil Q ((z k.succ).1 + r₀ k • p.1 + r₁ k • p.2) p.1 = 0) ∧
        (∀ k, bil Q ((z k.succ).1 + r₀ k • p.1 + r₁ k • p.2) p.2 = 0) := by
      choose r₀ r₁ h1 h2 h3 h4 using fun k : Fin m => exists_orth_pair Q hA.symm hBv.symm hC.symm hunitp
        (hz.c₁₁ k.succ 0 (hne k)) (hz.c₁₂ k.succ 0 (hne k)) hs₂R'
      exact ⟨r₀, r₁, h1, h2, h3, h4⟩
    obtain ⟨r₂, r₃, hr₂, hr₃, ho₂, ho₃⟩ : ∃ r₂ r₃ : Fin m → R, (∀ k, algebraMap R F (r₂ k) ∈ s₂) ∧
        (∀ k, algebraMap R F (r₃ k) ∈ s₂) ∧
        (∀ k, bil Q ((z k.succ).2 + r₂ k • p.1 + r₃ k • p.2) p.1 = 0) ∧
        (∀ k, bil Q ((z k.succ).2 + r₂ k • p.1 + r₃ k • p.2) p.2 = 0) := by
      choose r₂ r₃ h1 h2 h3 h4 using fun k : Fin m => exists_orth_pair Q hA.symm hBv.symm hC.symm hunitp
        (by rw [bil_comm]; exact hz.c₁₂ 0 k.succ (hne k).symm) (hz.c₂₂ k.succ 0 (hne k)) hs₂R'
      exact ⟨r₂, r₃, h1, h2, h3, h4⟩
    set ww : Fin m → V × V := fun k =>
      ((z k.succ).1 + r₀ k • p.1 + r₁ k • p.2, (z k.succ).2 + r₂ k • p.1 + r₃ k • p.2) with hww
    have hcorrK : ∀ a b : R, a • p.1 + b • p.2 ∈ K₁ := fun a b =>
      add_mem (smul_mem _ _ (hz.mem₁ 0)) (smul_mem _ _ (hz.mem₂ 0))
    have hcorrB : ∀ a b : R, algebraMap R F a ∈ s₂ → algebraMap R F b ∈ s₂ → ∀ t ∈ K₁,
        bil Q (a • p.1 + b • p.2) t ∈ s₂ := by
      intro a b ha hb t ht
      rw [bil_add_left, bil_rsmul_left, bil_rsmul_left]
      exact add_mem (hsmul ha (hK1 _ (hz.mem₁ 0) _ ht)) (hsmul hb (hK1 _ (hz.mem₂ 0) _ ht))
    have hcorrQ : ∀ a b : R, algebraMap R F a ∈ s₂ → Q (a • p.1 + b • p.2) ∈ g₂ := by
      intro a b ha
      rw [Q_add, ← algebraMap_smul F a p.1, ← algebraMap_smul F b p.2, QuadraticMap.map_smul,
        QuadraticMap.map_smul, bil_smul_left, bil_smul_right]
      refine add_mem (add_mem ?_ ?_) ?_
      · rw [← pow_two]; exact hsg _ ha _ (hz.q₁ 0)
      · have : algebraMap R F a * (algebraMap R F b * bil Q p.1 p.2) ∈ s₂ := by
          refine hsmul ha ?_
          obtain ⟨r, hr⟩ := hK1 _ (hz.mem₁ 0) _ (hz.mem₂ 0)
          exact ⟨b * r, by rw [map_mul, hr]⟩
        exact h2s _ this
      · rw [← pow_two]; exact hsq₂ _ (hz.q₂ 0) b
    have horth : ∀ {y : V} {a b : R}, bil Q (y + a • p.1 + b • p.2) p.1 = 0 →
        bil Q (y + a • p.1 + b • p.2) p.2 = 0 → ∀ a' b' : R,
          bil Q (y + a • p.1 + b • p.2) (a' • p.1 + b' • p.2) = 0 := by
      intro y a b h1 h2 a' b'
      rw [bil_add_right, bil_rsmul_right, bil_rsmul_right, h1, h2]; ring
    have hassoc : ∀ (y : V) (a b : R), y + a • p.1 + b • p.2 = y + (a • p.1 + b • p.2) := fun y a b => by
      rw [add_assoc]
    have hww1 : ∀ k, (ww k).1 = (z k.succ).1 + (r₀ k • p.1 + r₁ k • p.2) := fun k => hassoc _ _ _
    have hww2 : ∀ k, (ww k).2 = (z k.succ).2 + (r₂ k • p.1 + r₃ k • p.2) := fun k => hassoc _ _ _
    have hwo1 : ∀ k (a' b' : R), bil Q (ww k).1 (a' • p.1 + b' • p.2) = 0 := fun k => horth (ho₀ k) (ho₁ k)
    have hwo2 : ∀ k (a' b' : R), bil Q (ww k).2 (a' • p.1 + b' • p.2) = 0 := fun k => horth (ho₂ k) (ho₃ k)
    have hwK1 : ∀ k, (ww k).1 ∈ K₁ := fun k => by rw [hww1]; exact add_mem (hz.mem₁ _) (hcorrK _ _)
    have hwK2 : ∀ k, (ww k).2 ∈ K₁ := fun k => by rw [hww2]; exact add_mem (hz.mem₂ _) (hcorrK _ _)
    have hcross : ∀ {y y' : V} {a b a' b' : R}, y ∈ K₁ → y' ∈ K₁ → algebraMap R F a ∈ s₂ →
        algebraMap R F b ∈ s₂ → bil Q (y + (a • p.1 + b • p.2)) (a' • p.1 + b' • p.2) = 0 →
        bil Q y y' ∈ s₂ → bil Q (y + (a • p.1 + b • p.2)) (y' + (a' • p.1 + b' • p.2)) ∈ s₂ := by
      intro y y' a b a' b' hy hy' ha hb h0 hyy'
      rw [bil_add_right, h0, add_zero, bil_add_left]
      exact add_mem hyy' (hcorrB a b ha hb y' hy')
    have hwdata : BlockData Q K₁ s₂ g₁ g₂ ww := by
      refine ⟨hwK1, hwK2, fun k => ?_, fun k => ?_, fun k => ?_, fun k l hkl => ?_, fun k l hkl => ?_,
        fun k l hkl => ?_⟩
      · rw [hww1, Q_add_of_orth Q (by rw [← hww1]; exact hwo1 k _ _)]
        exact sub_mem (hz.q₁ _) (hg₂₁ (hcorrQ _ _ (hr₀ k)))
      · rw [hww2, Q_add_of_orth Q (by rw [← hww2]; exact hwo2 k _ _)]
        exact sub_mem (hz.q₂ _) (hcorrQ _ _ (hr₂ k))
      · rw [hww1, hww2, bil_add_right, (by rw [← hww1]; exact hwo1 k _ _ :
          bil Q ((z k.succ).1 + (r₀ k • p.1 + r₁ k • p.2)) (r₂ k • p.1 + r₃ k • p.2) = 0), add_zero,
          bil_add_left]
        have : bil Q (z k.succ).1 (z k.succ).2 + bil Q (r₀ k • p.1 + r₁ k • p.2) (z k.succ).2 - 1 =
            (bil Q (z k.succ).1 (z k.succ).2 - 1) + bil Q (r₀ k • p.1 + r₁ k • p.2) (z k.succ).2 := by ring
        rw [this]
        exact add_mem (hz.b _) (hcorrB _ _ (hr₀ k) (hr₁ k) _ (hz.mem₂ _))
      · rw [hww1, hww1]
        exact hcross (hz.mem₁ _) (hz.mem₁ _) (hr₀ k) (hr₁ k) (by rw [← hww1]; exact hwo1 k _ _)
          (hz.c₁₁ _ _ (fun h => hkl (Fin.succ_injective _ h)))
      · rw [hww1, hww2]
        exact hcross (hz.mem₁ _) (hz.mem₂ _) (hr₀ k) (hr₁ k) (by rw [← hww1]; exact hwo1 k _ _)
          (hz.c₁₂ _ _ (fun h => hkl (Fin.succ_injective _ h)))
      · rw [hww2, hww2]
        exact hcross (hz.mem₂ _) (hz.mem₂ _) (hr₂ k) (hr₃ k) (by rw [← hww2]; exact hwo2 k _ _)
          (hz.c₂₂ _ _ (fun h => hkl (Fin.succ_injective _ h)))
    -- the unit-multiple property of the corrected pairs
    have hunitw : ∀ k, ∃ u : R, IsUnit u ∧ Q (ww k).1 = a₀ * algebraMap R F u := by
      intro k
      obtain ⟨u, hu, hue⟩ := hunit k.succ
      have hQc : Q (ww k).1 = Q (z k.succ).1 - Q (r₀ k • p.1 + r₁ k • p.2) := by
        rw [hww1, Q_add_of_orth Q (by rw [← hww1]; exact hwo1 k _ _)]
      obtain ⟨ρ, hρ, hρe⟩ := hρa _ (hcorrQ _ _ (hr₀ k))
      refine ⟨u + -ρ, isUnit_add_mem' hu ((Ideal.neg_mem_iff _).2 hρ), ?_⟩
      rw [hQc, hue, hρe]; simp only [map_add, map_neg]; ring
    -- `ζ` is orthogonal to the corrected pairs
    have hζw : ∀ k, bil Q (ww k).1 ζ.1 = 0 ∧ bil Q (ww k).2 ζ.1 = 0 := by
      intro k
      obtain ⟨h1, h2⟩ := hζ k.succ
      obtain ⟨h3, h4⟩ := hζ 0
      refine ⟨?_, ?_⟩
      · rw [hww1, bil_add_left, bil_add_left, bil_rsmul_left, bil_rsmul_left, h1, h3, h4]; ring
      · rw [hww2, bil_add_left, bil_add_left, bil_rsmul_left, bil_rsmul_left, h2, h3, h4]; ring
    -- the round for the first pair
    have hA₁ : ∃ u : R, IsUnit u ∧ repForm Q a₀ (p.1, 0) = a₀ * algebraMap R F u := by
      obtain ⟨u, hu, h⟩ := hunit 0
      exact ⟨u, hu, by rw [hQW]; exact h⟩
    have hAα₁ : ∃ α b : R, repForm Q a₀ (p.1, 0) =
        a₀ * algebraMap R F α ^ 2 + w * algebraMap R F b := by
      obtain ⟨α, b, h⟩ := hAα _ (hz.q₁ 0)
      exact ⟨α, b, by rw [hQW]; exact h⟩
    have hδ₁ : ∃ ε : R, IsUnit ε ∧ ∃ x ∈ X, bil (repForm Q a₀) (p.1, 0) (p.2, 0) ^ 2 -
        repForm Q a₀ (p.1, 0) * repForm Q a₀ (p.2, 0) = algebraMap R F ε ^ 2 + x := by
      obtain ⟨-, ε, hε, hmem⟩ := hp
      exact ⟨ε, hε, _, hmem, by rw [hbW, hQW, hQW]; ring⟩
    obtain ⟨r₁', r₂', ζ', hS1, hr₁Q, hr₂Q, hr₁₂, hr₁z, hr₂z, b', hζ'Q⟩ :=
      round_step (repForm Q a₀) h2p ha0 hw0 ha0R hw1 hw2 hf hA₁ hAα₁ hδ₁
        (by rw [hbζ]; exact (hζ 0).1) (by rw [hbζ]; exact (hζ 0).2) hζQ
    -- `S_w`: the vectors orthogonal to the corrected pairs
    have hassocW : ∀ (u : V) (x : V × F),
        (QuadraticMap.associated (repForm Q a₀)) (u, (0 : F)) x = bil Q u x.1 := fun u x => hbζ u x
    let Sw : Submodule F (V × F) := ⨅ k : Fin m,
      LinearMap.ker (QuadraticMap.associated (repForm Q a₀) ((ww k).1, (0 : F))) ⊓
        LinearMap.ker (QuadraticMap.associated (repForm Q a₀) ((ww k).2, (0 : F)))
    have hmemSw : ∀ x : V × F, x ∈ Sw ↔ ∀ k, bil Q (ww k).1 x.1 = 0 ∧ bil Q (ww k).2 x.1 = 0 := by
      intro x
      simp only [Sw, Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker, hassocW]
    have hp1Sw : (p.1, (0 : F)) ∈ Sw := (hmemSw _).2 fun k => ⟨ho₀ k, ho₂ k⟩
    have hp2Sw : (p.2, (0 : F)) ∈ Sw := (hmemSw _).2 fun k => ⟨ho₁ k, ho₃ k⟩
    have hζSw : ζ ∈ Sw := (hmemSw _).2 hζw
    obtain ⟨hr₁Sw, hr₂Sw, hζ'Sw⟩ := hS1 Sw hp1Sw hp2Sw hζSw
    have hζ'w := (hmemSw _).1 hζ'Sw
    obtain ⟨r', hr'S, hr'Q, hr'orth⟩ := ih ww hwdata hunitw ζ' hζ'w ⟨b', hζ'Q⟩
    -- `S_r`: the vectors orthogonal to the first hyperbolic pair
    have hbζ' : ∀ (x : V × F) (u : V), bil (repForm Q a₀) x (u, 0) = bil Q x.1 u := fun x u => by
      rw [NecBase.bil_repForm]; simp
    let Sr : Submodule F (V × F) :=
      LinearMap.ker (QuadraticMap.associated (repForm Q a₀) r₁') ⊓
        LinearMap.ker (QuadraticMap.associated (repForm Q a₀) r₂')
    have hmemSr : ∀ x : V × F, x ∈ Sr ↔ bil (repForm Q a₀) r₁' x = 0 ∧ bil (repForm Q a₀) r₂' x = 0 :=
      fun x => by simp [Sr, LinearMap.mem_ker, bil]
    have hwSr : ∀ k, ((ww k).1, (0 : F)) ∈ Sr ∧ ((ww k).2, (0 : F)) ∈ Sr := by
      intro k
      obtain ⟨h1, h2⟩ := (hmemSw _).1 hr₁Sw k
      obtain ⟨h3, h4⟩ := (hmemSw _).1 hr₂Sw k
      refine ⟨(hmemSr _).2 ⟨?_, ?_⟩, (hmemSr _).2 ⟨?_, ?_⟩⟩
      · rw [hbζ', bil_comm]; exact h1
      · rw [hbζ', bil_comm]; exact h3
      · rw [hbζ', bil_comm]; exact h2
      · rw [hbζ', bil_comm]; exact h4
    have hζ'Sr : ζ' ∈ Sr := (hmemSr _).2 ⟨hr₁z, hr₂z⟩
    have hr'Sr := fun k => hr'S Sr (fun k => hwSr k) hζ'Sr k
    -- membership of the corrected pairs in a subspace containing the original ones
    have hwS : ∀ S : Submodule F (V × F), (∀ k, ((z k).1, (0 : F)) ∈ S ∧ ((z k).2, (0 : F)) ∈ S) →
        ∀ k, ((ww k).1, (0 : F)) ∈ S ∧ ((ww k).2, (0 : F)) ∈ S := by
      intro S hzS k
      have hp1 := (hzS 0).1
      have hp2 := (hzS 0).2
      have e1 : ((ww k).1, (0 : F)) = ((z k.succ).1, (0 : F)) + algebraMap R F (r₀ k) • (p.1, (0 : F)) +
          algebraMap R F (r₁ k) • (p.2, (0 : F)) := by
        ext <;> simp [hww, algebraMap_smul]
      have e2 : ((ww k).2, (0 : F)) = ((z k.succ).2, (0 : F)) + algebraMap R F (r₂ k) • (p.1, (0 : F)) +
          algebraMap R F (r₃ k) • (p.2, (0 : F)) := by
        ext <;> simp [hww, algebraMap_smul]
      exact ⟨e1 ▸ add_mem (add_mem (hzS _).1 (smul_mem _ _ hp1)) (smul_mem _ _ hp2),
        e2 ▸ add_mem (add_mem (hzS _).2 (smul_mem _ _ hp1)) (smul_mem _ _ hp2)⟩
    refine ⟨Fin.cons (r₁', r₂') r', ?_, ?_, ?_⟩
    · intro S hzS hζS k
      refine Fin.cases ?_ (fun k' => ?_) k
      · obtain ⟨a1, a2, -⟩ := hS1 S (hzS 0).1 (hzS 0).2 hζS
        simpa using ⟨a1, a2⟩
      · obtain ⟨-, -, hζ'S⟩ := hS1 S (hzS 0).1 (hzS 0).2 hζS
        simpa using hr'S S (hwS S hzS) hζ'S k'
    · intro k
      refine Fin.cases ?_ (fun k' => ?_) k
      · simpa using ⟨hr₁Q, hr₂Q, hr₁₂⟩
      · simpa using hr'Q k'
    · intro k l
      cases k using Fin.cases with
      | zero =>
        cases l using Fin.cases with
        | zero => intro h; exact absurd rfl h
        | succ l' =>
          intro _
          obtain ⟨a1, a2⟩ := (hmemSr _).1 (hr'Sr l').1
          obtain ⟨a3, a4⟩ := (hmemSr _).1 (hr'Sr l').2
          simp only [Fin.cons_succ, Fin.cons_zero]
          exact ⟨a1, a3, a2, a4⟩
      | succ k' =>
        cases l using Fin.cases with
        | zero =>
          intro _
          obtain ⟨a1, a2⟩ := (hmemSr _).1 (hr'Sr k').1
          obtain ⟨a3, a4⟩ := (hmemSr _).1 (hr'Sr k').2
          simp only [Fin.cons_succ, Fin.cons_zero]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [bil_comm] <;> assumption
        | succ l' =>
          intro h
          simpa using hr'orth k' l' (fun h' => h (by rw [h']))

end Induction

section Main

open NecBlock NecBase Sat93 Arith28 Transfer28

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

set_option maxHeartbeats 3200000 in
/-- **93:28, necessity, step 1, condition (iii), for a first component with $m$ blocks** (O'Meara 1963, §93F,
pp. 269–270; O'Meara takes $m = 2$ after cancelling hyperbolic planes; compare `nec_base_rep`). See
`NecBase.nec_base_rep` for the statement; here $L_1$ is spanned by pairs $x_k^{(1)}, x_k^{(2)}$ with
$Q(x_k^{(2)}) = 0$, $B(x_k^{(1)}, x_k^{(2)}) = 1$, mutually orthogonal pairs, and every $Q(x_k^{(1)})$ a norm generator of
$L^{\mathfrak s_1}$. If $\mathfrak f_1 \subsetneq 4a_1\mathfrak w_1^{-1}$ then $FL_1 \to FK_1 \perp \langle a_1\rangle$. -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity, step 1, pp. 269–270 (condition (iii), m blocks)"]
theorem nec_base_rep_blocks (h2p : ¬ IsUnit (2 : R)) (h2 : (2 : R) ≠ 0) {L : Submodule R V} (hfg : L.FG)
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q L Ks)
    (i₀ i₁ : Fin t) (h₀ : i₀.val = 0) (h₁ : i₁.val = 1) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (hU : scale Q (Ls i₀) = 1) {m : ℕ} (x : Fin m → V × V)
    (hspan : pairSpan R x = Ls i₀) (hx2 : ∀ k, Q (x k).2 = 0) (hx12 : ∀ k, bil Q (x k).1 (x k).2 = 1)
    (hx11 : ∀ k l, k ≠ l → bil Q (x k).1 (x l).1 = 0) (hx12' : ∀ k l, k ≠ l → bil Q (x k).1 (x l).2 = 0)
    (hx22 : ∀ k l, k ≠ l → bil Q (x k).2 (x l).2 = 0)
    (hxN : ∀ k, IsNormGenerator Q (fundSub Q L Ls i₀) (Q (x k).1))
    (hlt : fIdeal Q L Ls i₀ i₁ < (4 * a i₀) • (1 / fundWeight Q L Ls i₀)) :
    SpanRepresents Q (jordanChain Ls i₀) (jordanChain Ks i₀) (a i₀) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [jordanChain_zero Ls i₀ h₀, jordanChain_zero Ks i₀ h₀]
  have hreg := isRegular_of_isJordanSplitting Q hfg hL
  obtain ⟨hT, hJT⟩ := hL.sameJordanType Q hfg hK
  have hc : ∀ i, Fin.cast hT i = i := fun i => Fin.ext (by simp)
  have hsc : ∀ i, scale Q (Ls i) = scale Q (Ks i) := fun i => by have := (hJT i).1; rwa [hc] at this
  have hK0 : scale Q (Ks i₀) = 1 := (hsc i₀) ▸ hU
  have hKi₁ : Ks i₁ ≤ L := hK.split.iSup_eq ▸ le_iSup Ks i₁
  set s₂ := scale Q (Ks i₁) with hs₂def
  have hs₂lt : s₂ < 1 := hK0 ▸ hK.scale_strictAnti (Fin.lt_def.2 (by omega))
  have hs₂R : ∀ z ∈ s₂, ∃ r ∈ maximalIdeal R, algebraMap R F r = z := fun z hz =>
    exists_max_of_lt_one (scale_fg Q (FG.of_le hfg hKi₁)) (hK.modular i₁).1 hs₂lt hz
  set g₁ := fundNormGroup Q L Ls i₀ with hg₁def
  set g₂ := fundNormGroup Q L Ls i₁ with hg₂def
  have hg₁ : g₁ = normGroup Q (subA Q 1 L) := by rw [hg₁def, ← hU]; rfl
  have hg₂ : g₂ = normGroup Q (subA Q s₂ L) := by rw [hg₂def, hs₂def, ← hsc i₁]; rfl
  have hg₂₁ : g₂ ≤ g₁ := fundNormGroup_antitone Q hL (Fin.le_def.2 (by omega))
  have hs₂sc : s₂ ≤ scale Q (subA Q s₂ L) := by
    have := scale_mono Q (le_fundSub Q hfg hK i₁)
    rwa [fundSub, ← hs₂def] at this
  have hn : ∀ i, fundNormIdeal Q L Ls i = R ∙ a i := fun i => (ha i).2.symm
  have hf : fIdeal Q L Ls i₀ i₁ = fIdealOf R (R ∙ (1 : F)) g₁ g₂ (R ∙ a i₀) (R ∙ a i₁) := by
    rw [fIdeal, hU, hn, hn, Submodule.one_eq_span]
  have ha0 : ∀ i, a i ≠ 0 := fun i =>
    (ha i).ne_zero Q (isRegular_fundSub Q hfg hreg hL i) (fundSub_ne_bot Q hfg hL i)
  have hgA : ∀ i, ∀ z ∈ fundNormGroup Q L Ls i, z ∈ R ∙ a i := fun i z hz =>
    (ha i).2 ▸ normGroup_subset_normIdeal Q _ hz
  have haS : ∀ i, a i ∈ scale Q (Ls i) := fun i => by
    rw [← scale_fundSub Q hfg hL i]
    exact normIdeal_le_scale Q _ ((ha i).2 ▸ mem_span_singleton_self (a i))
  have hu₀ : 0 ≤ dord hπ (a i₀) := by
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hU ▸ haS i₀)
    rw [← hr]; exact dord_alg_nonneg hπ (by rintro rfl; exact ha0 i₀ (by rw [← hr, map_zero]))
  have hu₁ : 1 ≤ dord hπ (a i₁) := by
    obtain ⟨r, hrm, hr⟩ := hs₂R _ (hsc i₁ ▸ haS i₁)
    rw [← hr]; exact one_le_dord_of_max hπ hrm (hr ▸ ha0 i₁)
  have key : ∀ c : R, c ∈ maximalIdeal R → ∀ α ∈ g₁, ∀ β ∈ g₂,
      SqEquivMod (fIdeal Q L Ls i₀ i₁) ((1 - algebraMap R F c) ^ 2 + α * β) 1 := by
    intro c hcm α hα β hβ
    rw [hf]
    exact sqEquivMod_sq_add_mul hπ h2 (ha0 i₀) (ha0 i₁) (ha i₀).1 (ha i₁).1 (hgA i₀) (hgA i₁) hu₀ hu₁
      (fun z hz r => mul_sq_mem_normGroup Q hz ⟨r, rfl⟩) hcm hα hβ
  have hsq₂ : ∀ z ∈ g₂, ∀ r : R, algebraMap R F r ^ 2 * z ∈ g₂ := fun z hz r =>
    mul_sq_mem_normGroup Q hz ⟨r, rfl⟩
  have h2s : ∀ z ∈ s₂, 2 * z ∈ g₂ := fun z hz => hg₂ ▸ two_mul_mem_normGroup Q (hs₂sc hz)
  have hsg : ∀ z ∈ s₂, ∀ y ∈ g₁, z ^ 2 * y ∈ g₂ := fun z hz y hy => hg₂ ▸
    sq_mul_mem_normGroup_subA Q hs₂lt.le hs₂sc hz (hg₁ ▸ hy)
  have hKR : ∀ {K : Submodule R V}, scale Q K = 1 → ∀ u ∈ K, ∀ v ∈ K, ∃ r : R, algebraMap R F r = bil Q u v :=
    fun hK1 u hu v hv => Submodule.mem_one.mp (hK1 ▸ bil_mem_scale Q hu hv)
  have hLi : Ls i₀ ≤ L := hL.split.iSup_eq ▸ le_iSup Ls i₀
  have hxL1 : ∀ k, (x k).1 ∈ Ls i₀ := fun k => hspan ▸ subset_span (Or.inl ⟨k, rfl⟩)
  have hxL2 : ∀ k, (x k).2 ∈ Ls i₀ := fun k => hspan ▸ subset_span (Or.inr ⟨k, rfl⟩)
  have hdec : ∀ v ∈ L, ∃ y ∈ Ks i₀, ∃ Y ∈ others Ks i₀, y + Y = v := fun v hv =>
    mem_sup.mp ((sup_others Q hK.split i₀).symm ▸ hv)
  choose y₁ hy₁ Y₁ hY₁ hxy₁ using fun k => hdec _ (hLi (hxL1 k))
  choose y₂ hy₂ Y₂ hY₂ hxy₂ using fun k => hdec _ (hLi (hxL2 k))
  have hsub : ∀ {Y : V}, Y ∈ others Ks i₀ → Y ∈ subA Q s₂ L := fun hY => mem_subA_of_others Q hK i₀ i₁ h₀ h₁ hY
  have horth : ∀ {y Y : V}, y ∈ Ks i₀ → Y ∈ others Ks i₀ → bil Q y Y = 0 := fun hy hY =>
    orth_others Q hK.split i₀ hy _ hY
  have hBdec : ∀ {y Y y' Y' : V}, y ∈ Ks i₀ → Y ∈ others Ks i₀ → y' ∈ Ks i₀ → Y' ∈ others Ks i₀ →
      bil Q (y + Y) (y' + Y') = bil Q y y' + bil Q Y Y' := by
    intro y Y y' Y' hy hY hy' hY'
    rw [bil_add_left, bil_add_right, bil_add_right, horth hy hY', bil_comm Q Y y', horth hy' hY]; ring
  have hQdec : ∀ {y Y : V}, y ∈ Ks i₀ → Y ∈ others Ks i₀ → Q (y + Y) = Q y + Q Y := by
    intro y Y hy hY; rw [Q_add, horth hy hY]; ring
  have hYY : ∀ {Y Y' : V}, Y ∈ others Ks i₀ → Y' ∈ others Ks i₀ → bil Q Y Y' ∈ s₂ := fun hY hY' =>
    (hsub hY).2 _ (hsub hY').1
  have hQY : ∀ {Y : V}, Y ∈ others Ks i₀ → Q Y ∈ g₂ := fun hY => hg₂ ▸ Q_mem_normGroup Q (hsub hY)
  have hfs₀ : Ls i₀ ≤ fundSub Q L Ls i₀ := le_fundSub Q hfg hL i₀
  set yy : Fin m → V × V := fun k => (y₁ k, y₂ k) with hyy
  have hyydata : BlockData Q (Ks i₀) s₂ g₁ g₂ yy := by
    refine ⟨hy₁, hy₂, fun k => ?_, fun k => ?_, fun k => ?_, fun k l hkl => ?_, fun k l hkl => ?_,
      fun k l hkl => ?_⟩
    · have h := hQdec (hy₁ k) (hY₁ k); rw [hxy₁ k] at h
      have : Q (y₁ k) = Q (x k).1 - Q (Y₁ k) := by linear_combination -h
      show Q (y₁ k) ∈ g₁; rw [this]
      exact sub_mem (Q_mem_normGroup Q (hfs₀ (hxL1 k))) (hg₂₁ (hQY (hY₁ k)))
    · have h := hQdec (hy₂ k) (hY₂ k); rw [hxy₂ k, hx2 k] at h
      have : Q (y₂ k) = -Q (Y₂ k) := by linear_combination -h
      show Q (y₂ k) ∈ g₂; rw [this]; exact neg_mem (hQY (hY₂ k))
    · have h := hBdec (hy₁ k) (hY₁ k) (hy₂ k) (hY₂ k); rw [hxy₁ k, hxy₂ k, hx12 k] at h
      show bil Q (y₁ k) (y₂ k) - 1 ∈ s₂
      have : bil Q (y₁ k) (y₂ k) - 1 = -bil Q (Y₁ k) (Y₂ k) := by linear_combination -h
      rw [this]; exact neg_mem (hYY (hY₁ k) (hY₂ k))
    · have h := hBdec (hy₁ k) (hY₁ k) (hy₁ l) (hY₁ l); rw [hxy₁ k, hxy₁ l, hx11 k l hkl] at h
      show bil Q (y₁ k) (y₁ l) ∈ s₂
      have : bil Q (y₁ k) (y₁ l) = -bil Q (Y₁ k) (Y₁ l) := by linear_combination -h
      rw [this]; exact neg_mem (hYY (hY₁ k) (hY₁ l))
    · have h := hBdec (hy₁ k) (hY₁ k) (hy₂ l) (hY₂ l); rw [hxy₁ k, hxy₂ l, hx12' k l hkl] at h
      show bil Q (y₁ k) (y₂ l) ∈ s₂
      have : bil Q (y₁ k) (y₂ l) = -bil Q (Y₁ k) (Y₂ l) := by linear_combination -h
      rw [this]; exact neg_mem (hYY (hY₁ k) (hY₂ l))
    · have h := hBdec (hy₂ k) (hY₂ k) (hy₂ l) (hY₂ l); rw [hxy₂ k, hxy₂ l, hx22 k l hkl] at h
      show bil Q (y₂ k) (y₂ l) ∈ s₂
      have : bil Q (y₂ k) (y₂ l) = -bil Q (Y₂ k) (Y₂ l) := by linear_combination -h
      rw [this]; exact neg_mem (hYY (hY₂ k) (hY₂ l))
  -- the weight generator `w` of `L^{s₁}` and the data of `hlt`
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have hfsub_sc : scale Q (fundSub Q L Ls i₀) = 1 := by rw [scale_fundSub Q hfg hL i₀, hU]
  have hwbd := weight_bounds Q (fundSub Q L Ls i₀)
  have hwle1 : fundWeight Q L Ls i₀ ≤ 1 :=
    hwbd.2.2.2.trans ((normIdeal_le_scale Q _).trans hfsub_sc.le)
  have h2w : (2 : F) ∈ fundWeight Q L Ls i₀ := by
    have h1 : (1 : F) ∈ scale Q (fundSub Q L Ls i₀) := by
      rw [hfsub_sc]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    have := hwbd.2.2.1 (Submodule.smul_mem_pointwise_smul (1 : F) (2 : F) _ h1)
    have h2' : (2 : F) ∈ weight Q (fundSub Q L Ls i₀) := by simpa using this
    exact h2'
  have hwfg : (fundWeight Q L Ls i₀).FG :=
    FG.of_le (Submodule.fg_span_singleton (a i₀)) (hwbd.2.2.2.trans (le_of_eq (ha i₀).2.symm))
  have hwne : fundWeight Q L Ls i₀ ≠ ⊥ := fun h => h2F (by simpa [h] using h2w)
  obtain ⟨w, hw0, hwdef⟩ := exists_eq_span_singleton (R := R) hwfg hwne
  have hw1 : ∃ r : R, algebraMap R F r = w :=
    Submodule.mem_one.1 (hwle1 (hwdef ▸ mem_span_singleton_self w))
  have hw2 : ∃ r : R, algebraMap R F r * w = 2 := by
    obtain ⟨r, hr⟩ := mem_span_singleton.1 (hwdef ▸ h2w)
    exact ⟨r, by rw [← hr, Algebra.smul_def]⟩
  have ha0R : ∃ r : R, algebraMap R F r = a i₀ := Submodule.mem_one.1 (hU ▸ haS i₀)
  have hlt' : fIdeal Q L Ls i₀ i₁ < R ∙ (4 * a i₀ * w⁻¹) := by
    rw [hwdef, smul_one_div_span hw0] at hlt; exact hlt
  have hle : R ∙ a i₁ ≤ R ∙ a i₀ :=
    (span_singleton_le_iff_mem _ _).2 (hgA i₀ _ (hg₂₁ (ha i₁).1))
  rcases hle.lt_or_eq with hlt₁ | heq
  swap
  · -- the case `u₁ = u₂`: condition (iii) is vacuous
    exfalso
    have hdord : dord hπ (a i₁) = dord hπ (a i₀) :=
      (FIdealAux.span_eq_iff_dord hπ (ha0 i₁) (ha0 i₀)).1 heq
    have hm := mul_fIdeal_of_dord_eq Q hπ h2p hfg hreg hL ha i₀ i₁ (by omega) (σ := 1)
      (by rw [hU, Submodule.one_eq_span]) hdord
    rw [hU, Submodule.one_mul, Submodule.one_mul] at hm
    rw [hm, hwdef, FundAux.smul_eq_span_mul, FIdealAux.span_mul_span'] at hlt'
    obtain ⟨v, hv⟩ := mem_span_singleton.1 (heq ▸ mem_span_singleton_self (a i₀) : a i₀ ∈ R ∙ a i₁)
    have hv' : a i₀ = algebraMap R F v * a i₁ := by rw [← hv, Algebra.smul_def]
    obtain ⟨tr, htr⟩ := hw2
    refine hlt'.not_ge ((span_singleton_le_iff_mem _ _).2 (mem_span_singleton.2 ⟨v * tr * tr, ?_⟩))
    rw [Algebra.smul_def, hv']
    simp only [map_mul]
    field_simp
    linear_combination (algebraMap R F v * a i₁ * (algebraMap R F tr * w + 2)) * htr
  -- the case `u₁ < u₂`
  have hρa : ∀ z ∈ g₂, ∃ ρ ∈ maximalIdeal R, z = algebraMap R F ρ * a i₀ := fun z hz =>
    mem_p_mul_of_lt hlt₁ (hgA i₁ z hz)
  have hAα : ∀ z ∈ g₁, ∃ α b : R, z = a i₀ * algebraMap R F α ^ 2 + w * algebraMap R F b := by
    intro z hz
    obtain ⟨ε, hε⟩ := exists_sub_sq_mem_weight Q h2p (ha i₀) (ha0 i₀) hz
    have hε' : z - a i₀ * algebraMap R F ε ^ 2 ∈ R ∙ w := by rw [← hwdef]; exact hε
    obtain ⟨b, hb⟩ := mem_span_singleton.1 hε'
    exact ⟨ε, b, by rw [Algebra.smul_def] at hb; linear_combination -hb⟩
  have hf' : ∀ x ∈ fIdeal Q L Ls i₀ i₁, ∃ ρ ∈ maximalIdeal R,
      x = algebraMap R F ρ * (4 * a i₀ / w) := by
    intro x hx
    obtain ⟨ρ, hρ, hxρ⟩ := mem_p_mul_of_lt hlt' hx
    exact ⟨ρ, hρ, by rw [hxρ]; ring⟩
  have hunitmul : ∀ {a₃ : F}, IsNormGenerator Q (fundSub Q L Ls i₀) a₃ → ∀ z ∈ g₂,
      ∃ u : R, IsUnit u ∧ a₃ - z = a i₀ * algebraMap R F u := by
    intro a₃ ha₃ z hz
    obtain ⟨ub, hub⟩ := span_singleton_eq_span_singleton.mp (ha₃.2.trans (ha i₀).2.symm)
    have hb : a₃ = algebraMap R F ((ub⁻¹ : Rˣ) : R) * a i₀ := by
      have : a₃ = ((ub⁻¹ : Rˣ) : R) • a i₀ := by rw [← hub, Units.smul_def, smul_smul]; simp
      rw [this, Algebra.smul_def]
    obtain ⟨ρ, hρ, hzρ⟩ := hρa z hz
    refine ⟨((ub⁻¹ : Rˣ) : R) + -ρ, isUnit_add_mem' (ub⁻¹).isUnit ((Ideal.neg_mem_iff _).2 hρ), ?_⟩
    rw [hb, hzρ]; simp only [map_add, map_neg]; ring
  have hunit_y : ∀ k, ∃ u : R, IsUnit u ∧ Q (yy k).1 = a i₀ * algebraMap R F u := by
    intro k
    have h := hQdec (hy₁ k) (hY₁ k); rw [hxy₁ k] at h
    have h' : Q (y₁ k) = Q (x k).1 - Q (Y₁ k) := by linear_combination -h
    obtain ⟨u, hu, hue⟩ := hunitmul (hxN k) (Q (Y₁ k)) (hQY (hY₁ k))
    exact ⟨u, hu, by show Q (y₁ k) = _; rw [h']; exact hue⟩
  obtain ⟨r, hrS, hrQ, hrorth⟩ := rep_blocks_ind Q h2p (K₁ := Ks i₀) (hKR hK0) hs₂R hg₂₁ hsq₂ h2s hsg key
    (ha0 i₀) hw0 ha0R hw1 hw2 hf' hAα hρa m yy hyydata hunit_y ((0 : V), (1 : F))
    (fun k => ⟨by simp [bil], by simp [bil]⟩) ⟨0, by rw [NecBase.repForm_apply]; simp⟩
  -- the frame
  have hr1 : ∀ k, bil (repForm Q (a i₀)) (r k).1 (r k).1 = 0 := fun k => by rw [bil_self]; exact (hrQ k).1
  have hr2 : ∀ k, bil (repForm Q (a i₀)) (r k).2 (r k).2 = 0 := fun k => by rw [bil_self]; exact (hrQ k).2.1
  have hr12 : ∀ k, bil (repForm Q (a i₀)) (r k).1 (r k).2 = 1 := fun k => (hrQ k).2.2
  have hr21 : ∀ k, bil (repForm Q (a i₀)) (r k).2 (r k).1 = 1 := fun k => by rw [bil_comm]; exact hr12 k
  have hro11 : ∀ k l, k ≠ l → bil (repForm Q (a i₀)) (r k).1 (r l).1 = 0 := fun k l h => (hrorth k l h).1
  have hro12 : ∀ k l, k ≠ l → bil (repForm Q (a i₀)) (r k).1 (r l).2 = 0 := fun k l h => (hrorth k l h).2.1
  have hro21 : ∀ k l, k ≠ l → bil (repForm Q (a i₀)) (r k).2 (r l).1 = 0 := fun k l h => (hrorth k l h).2.2.1
  have hro22 : ∀ k l, k ≠ l → bil (repForm Q (a i₀)) (r k).2 (r l).2 = 0 := fun k l h => (hrorth k l h).2.2.2
  let v : Fin m ⊕ Fin m → V := Sum.elim (fun k => (x k).1) (fun k => (x k).2)
  let X : Fin m ⊕ Fin m → V × F :=
    Sum.elim (fun k => (r k).2 + (Q (x k).1 / 2) • (r k).1) (fun k => (r k).1)
  have hG : ∀ i j, bil Q (X i).1 (X j).1 + a i₀ * ((X i).2 * (X j).2) = bil Q (v i) (v j) := by
    intro i j
    rw [← NecBase.bil_repForm]
    rcases i with k | k <;> rcases j with l | l
    · by_cases hkl : k = l
      · subst hkl
        simp only [X, v, Sum.elim_inl, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, hr1, hr2,
          hr12, hr21]
        rw [bil_self]
        ring
      · simp only [X, v, Sum.elim_inl, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right,
          hro11 k l hkl, hro12 k l hkl, hro21 k l hkl, hro22 k l hkl, hx11 k l hkl]
        ring
    · by_cases hkl : k = l
      · subst hkl
        simp only [X, v, Sum.elim_inl, Sum.elim_inr, bil_add_left, bil_smul_left, hr1, hr21, hx12]
        ring
      · simp only [X, v, Sum.elim_inl, Sum.elim_inr, bil_add_left, bil_smul_left, hro11 k l hkl,
          hro21 k l hkl, hx12' k l hkl]
        ring
    · by_cases hkl : k = l
      · subst hkl
        simp only [X, v, Sum.elim_inl, Sum.elim_inr, bil_add_right, bil_smul_right, hr1, hr12]
        rw [bil_comm Q (x k).2 (x k).1, hx12]; ring
      · simp only [X, v, Sum.elim_inl, Sum.elim_inr, bil_add_right, bil_smul_right, hro11 k l hkl,
          hro12 k l hkl]
        rw [bil_comm Q (x k).2 (x l).1, hx12' l k (Ne.symm hkl)]; ring
    · by_cases hkl : k = l
      · subst hkl
        simp only [X, v, Sum.elim_inr, hr1, bil_self, hx2]
      · simp only [X, v, Sum.elim_inr, hro11 k l hkl, hx22 k l hkl]
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hgsum : ∀ w' : V, bil Q (∑ i, g i • v i) w' =
        ∑ k, g (Sum.inl k) * bil Q (x k).1 w' + ∑ k, g (Sum.inr k) * bil Q (x k).2 w' := by
      intro w'
      rw [bil_sum_left]
      simp only [bil_smul_left]
      rw [Fintype.sum_sum_type]
      rfl
    have h1 : ∀ l, g (Sum.inl l) = 0 := by
      intro l
      have := hgsum (x l).2
      rw [hg] at this
      simp only [bil, map_zero, LinearMap.zero_apply] at this
      have e1 : ∀ k, bil Q (x k).1 (x l).2 = if k = l then 1 else 0 := by
        intro k; by_cases h : k = l
        · subst h; simp [hx12]
        · simp [h, hx12' k l h]
      have e2 : ∀ k, bil Q (x k).2 (x l).2 = 0 := by
        intro k; by_cases h : k = l
        · subst h; rw [bil_self, hx2]
        · exact hx22 k l h
      simp only [e1, e2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.sum_const_zero, add_zero] at this
      exact this.symm
    intro i
    rcases i with l | l
    · exact h1 l
    · have := hgsum (x l).1
      rw [hg] at this
      simp only [bil, map_zero, LinearMap.zero_apply] at this
      simp only [h1, zero_mul, Finset.sum_const_zero, zero_add] at this
      have e3 : ∀ k, bil Q (x k).2 (x l).1 = if k = l then 1 else 0 := by
        intro k; by_cases h : k = l
        · subst h; rw [bil_comm, hx12]; simp
        · rw [bil_comm]; simp [h, hx12' l k (Ne.symm h)]
      simp only [e3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
  have hsp : span F (Set.range v) = span F ((Ls i₀ : Submodule R V) : Set V) := by
    rw [← hspan, pairSpan, Submodule.span_span_of_tower, Set.Sum.elim_range]
  have hLifg : (Ls i₀).FG := FG.of_le hfg hLi
  have hMreg : IsRegular Q (Ls i₀) := (hL.modular i₀).isRegular Q hLifg
  let SK : Submodule F (V × F) := (span F (Ks i₀ : Set V)).prod ⊤
  have hyySK : ∀ k, ((yy k).1, (0 : F)) ∈ SK ∧ ((yy k).2, (0 : F)) ∈ SK := fun k =>
    ⟨⟨subset_span (hyydata.mem₁ k), trivial⟩, ⟨subset_span (hyydata.mem₂ k), trivial⟩⟩
  have hζSK : ((0 : V), (1 : F)) ∈ SK := ⟨zero_mem _, trivial⟩
  have hrSK := fun k => hrS SK hyySK hζSK k
  have hX : ∀ i, (X i).1 ∈ span F (Ks i₀ : Set V) := by
    intro i
    rcases i with k | k
    · exact (Submodule.mem_prod.1 (add_mem (hrSK k).2 (smul_mem _ _ (hrSK k).1))).1
    · exact (Submodule.mem_prod.1 (hrSK k).1).1
  exact spanRepresents_of_frame_family Q hMreg (a i₀) v hli hsp X hX hG

end Main

end QuadFormsKB.OMeara.NecBlocks
