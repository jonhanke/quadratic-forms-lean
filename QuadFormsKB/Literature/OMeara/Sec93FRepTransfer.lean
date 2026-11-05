/-
# O'Meara 93:28, proof of the necessity: transfer lemmas for `SpanRepresents`

**Setting** (as in `Sec93FAdjoin.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$,
quadratic spaces $(V, Q)$, lattices `Submodule R V`; `SpanRepresents Q M N c` (`Sec93E.lean`) says that $FM$ is
represented by $FN \perp \langle c\rangle$.

**Proves** (the representation analogues of `Sec93FTransfer.lean` and `Sec93FAdjoin.lean`)
* `Rep`, `Rep.congr`, `Rep.prod_right`, `Rep.cancel_right`: embeddings of quadratic spaces over a field, and
  cancellation of a common nonsingular orthogonal summand (a consequence of Witt's extension theorem);
* `spanRepresents_iff_rep`: `SpanRepresents Q M N c` is `Rep (subQ Q M) (subQ Q N ⊥ ⟨c⟩)`;
* `spanRepresents_iff_of_isometricLat`: isometry invariance;
* `spanRepresents_prod_iff`: adjoining a regular lattice $H$ to both lattices;
* `spanRepresents_iff_of_orthSum`: cancelling a common orthogonal summand;
* `spanRepresents_of_orthSum_complement`: complements.
-/
import QuadFormsKB.Literature.OMeara.Sec93FAdjoin
import QuadFormsKB.Literature.OMeara.Sec93DSub
import QuadFormsKB.Literature.OMeara.Sec92Space
import QuadFormsKB.Witt.Cancellation

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.RepTransfer

open QuadFormsKB.OMeara.D18 (subQ spanF)

section Abstract

variable {F : Type*} [Field F]
variable {U₁ U₁' U₂ U₂' H U : Type*} [AddCommGroup U₁] [Module F U₁] [AddCommGroup U₁'] [Module F U₁']
  [AddCommGroup U₂] [Module F U₂] [AddCommGroup U₂'] [Module F U₂'] [AddCommGroup H] [Module F H]
  [AddCommGroup U] [Module F U]

/-- **Embedding of quadratic spaces**: an injective linear map $U_1 \to U_2$ with $Q_2(fx) = Q_1(x)$. -/
def Rep (Q₁ : QuadraticForm F U₁) (Q₂ : QuadraticForm F U₂) : Prop :=
  ∃ f : U₁ →ₗ[F] U₂, Function.Injective f ∧ ∀ x, Q₂ (f x) = Q₁ x

/-- Representation is invariant under isometries of the source and of the target. -/
theorem Rep.congr {Q₁ : QuadraticForm F U₁} {Q₁' : QuadraticForm F U₁'} {Q₂ : QuadraticForm F U₂}
    {Q₂' : QuadraticForm F U₂'} (e₁ : Q₁'.IsometryEquiv Q₁) (e₂ : Q₂.IsometryEquiv Q₂') (h : Rep Q₁ Q₂) :
    Rep Q₁' Q₂' := by
  obtain ⟨f, hf, hQ⟩ := h
  refine ⟨e₂.toLinearEquiv.toLinearMap ∘ₗ f ∘ₗ e₁.toLinearEquiv.toLinearMap, ?_, fun x => ?_⟩
  · exact e₂.toLinearEquiv.injective.comp (hf.comp e₁.toLinearEquiv.injective)
  · show Q₂' (e₂ (f (e₁ x))) = Q₁' x
    rw [e₂.map_app, hQ, e₁.map_app]

/-- Adjoining a common summand. -/
theorem Rep.prod_right {Q₁ : QuadraticForm F U₁} {Q₂ : QuadraticForm F U₂} (Q : QuadraticForm F U)
    (h : Rep Q₁ Q₂) : Rep (Q₁.prod Q) (Q₂.prod Q) := by
  obtain ⟨f, hf, hQ⟩ := h
  refine ⟨f.prodMap LinearMap.id, hf.prodMap Function.injective_id, fun x => ?_⟩
  simp [QuadraticMap.prod_apply, hQ]

/-- **Cancellation of a common nonsingular orthogonal summand** from a representation (Witt's extension theorem):
if $Q_1 \perp Q_H$ embeds in $Q_2 \perp Q_H$, with $Q_2$ and $Q_H$ nonsingular, then $Q_1$ embeds in $Q_2$. -/
theorem Rep.cancel_right [FiniteDimensional F U₂] [FiniteDimensional F H] {Q₁ : QuadraticForm F U₁}
    {Q₂ : QuadraticForm F U₂} {QH : QuadraticForm F H} (h₂ : (polarBilin Q₂).Nondegenerate)
    (hH : (polarBilin QH).Nondegenerate) (h : Rep (Q₁.prod QH) (Q₂.prod QH)) : Rep Q₁ Q₂ := by
  obtain ⟨f, hf, hQ⟩ := h
  set P := Q₂.prod QH with hP
  have hPn : (polarBilin P).Nondegenerate := QuadraticForm.nondegenerate_polarBilin_prod h₂ hH
  let W₀ : Submodule F (U₂ × H) := LinearMap.range (LinearMap.inr F U₂ H)
  let σ : W₀ →ₗ[F] U₂ × H :=
    f ∘ₗ LinearMap.inr F U₁ H ∘ₗ LinearMap.snd F U₂ H ∘ₗ W₀.subtype
  have hW₀ : ∀ w : W₀, (w : U₂ × H).1 = 0 := fun ⟨_, ⟨a, rfl⟩⟩ => rfl
  have hσ : ∀ w : W₀, P (σ w) = P w := by
    intro w
    simp only [σ, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, LinearMap.coe_snd,
      LinearMap.inr_apply]
    rw [hP, hQ, QuadraticMap.prod_apply, QuadraticMap.prod_apply, hW₀ w]
    simp
  have hσi : Function.Injective σ := by
    intro a b hab
    have h1 : f (0, (a : U₂ × H).2) = f (0, (b : U₂ × H).2) := hab
    have h2 := hf h1
    have h3 : (a : U₂ × H).2 = (b : U₂ × H).2 := by
      have := congrArg Prod.snd h2
      simpa using this
    exact Subtype.ext (Prod.ext (by rw [hW₀ a, hW₀ b]) h3)
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate P hPn σ hσi hσ
  have hρh : ∀ y : H, ρ (0, y) = f (0, y) := fun y => hρ ⟨(0, y), ⟨y, rfl⟩⟩
  -- the embedding `u ↦ (ρ⁻¹ f (u, 0)).1`
  let g : U₁ →ₗ[F] U₂ :=
    LinearMap.fst F U₂ H ∘ₗ ρ.symm.toLinearEquiv.toLinearMap ∘ₗ f ∘ₗ LinearMap.inl F U₁ H
  have hsnd : ∀ u : U₁, (ρ.symm (f (u, 0))).2 = 0 := by
    intro u
    rw [QuadraticForm.nondegenerate_polarBilin_iff] at hH
    refine hH _ fun y => ?_
    have h1 : polar P (ρ.symm (f (u, 0))) (0, y) = polar P (f (u, 0)) (f (0, y)) := by
      have := ρ.symm.polar_map (f (u, 0)) (ρ (0, y))
      rw [ρ.symm_apply_apply, hρh y] at this
      exact this
    have h2 : polar P (f (u, 0)) (f (0, y)) = polar (Q₁.prod QH) (u, 0) (0, y) :=
      QuadraticForm.Witt.polar_map_of_map_app (f := f) hQ _ _
    have h3 : polar P (ρ.symm (f (u, 0))) (0, y) = polar QH (ρ.symm (f (u, 0))).2 y := by
      simp [hP]
    rw [← h3, h1, h2]
    simp
  refine ⟨g, ?_, fun u => ?_⟩
  · intro a b hab
    have hfab : ρ.symm (f (a, 0)) = ρ.symm (f (b, 0)) :=
      Prod.ext hab ((hsnd a).trans (hsnd b).symm)
    have := hf (ρ.symm.toLinearEquiv.injective hfab)
    exact congrArg Prod.fst this
  · have h1 : P (ρ.symm (f (u, 0))) = Q₁ u := by
      rw [ρ.symm.map_app, hQ]; simp [QuadraticMap.prod_apply]
    have h2 : P (ρ.symm (f (u, 0))) = Q₂ (ρ.symm (f (u, 0))).1 := by
      show Q₂ (ρ.symm (f (u, 0))).1 + QH (ρ.symm (f (u, 0))).2 = _
      rw [hsnd u]; simp
    exact h2.symm.trans h1

/-- Reordering the factors `(B ⊥ H) ⊥ C ≅ (B ⊥ C) ⊥ H`. -/
def swap23 (B : QuadraticForm F U₂) (QH : QuadraticForm F H) {K : Type*} [AddCommGroup K] [Module F K]
    (C : QuadraticForm F K) : ((B.prod QH).prod C).IsometryEquiv ((B.prod C).prod QH) :=
  { toFun := fun p => ((p.1.1, p.2), p.1.2)
    invFun := fun p => ((p.1.1, p.2), p.1.2)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_app' := fun p => by simp [QuadraticMap.prod_apply]; ring }

/-- Reassociating `A ⊥ (B ⊥ C) ≅ (A ⊥ B) ⊥ C`. -/
def assoc3 {K : Type*} [AddCommGroup K] [Module F K] (A : QuadraticForm F U₁) (B : QuadraticForm F U₂)
    (C : QuadraticForm F K) : (A.prod (B.prod C)).IsometryEquiv ((A.prod B).prod C) :=
  { toFun := fun p => ((p.1, p.2.1), p.2.2)
    invFun := fun p => (p.1.1, (p.1.2, p.2))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_app' := fun p => by simp [QuadraticMap.prod_apply]; ring }

/-- Adjoining a common summand on the left. -/
theorem Rep.prod_left {Q₁ : QuadraticForm F U₁} {Q₂ : QuadraticForm F U₂} (Q : QuadraticForm F U)
    (h : Rep Q₁ Q₂) : Rep (Q.prod Q₁) (Q.prod Q₂) := by
  obtain ⟨f, hf, hQ⟩ := h
  refine ⟨LinearMap.id.prodMap f, Function.injective_id.prodMap hf, fun x => ?_⟩
  simp [QuadraticMap.prod_apply, hQ]

/-- The form $c\,t^2$ on $F$ is nonsingular for $c 
e 0$ ($2 
e 0$). -/
theorem nondegenerate_smul_sq [Invertible (2 : F)] {c : F} (hc : c ≠ 0) :
    (polarBilin (c • (QuadraticMap.sq : QuadraticForm F F))).Nondegenerate := by
  rw [QuadraticForm.nondegenerate_polarBilin_iff]
  intro v hv
  have h : polar (c • (QuadraticMap.sq : QuadraticForm F F)) v 1 = 0 := hv 1
  have h2 : (2 : F) ≠ 0 := two_ne_zero' F
  rw [QuadraticMap.polar] at h
  simp only [QuadraticMap.smul_apply, QuadraticMap.sq_apply, smul_eq_mul] at h
  have h3 : c * (2 * v) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd h4 hc
  · exact (mul_eq_zero.1 h4).resolve_left h2

/-- **Cancellation inside a representation**: $A \perp H \to (B \perp H') \perp C$ iff $A \to B \perp C$, for
isometric nonsingular $H \cong H'$ and nonsingular $B$, $C$. -/
theorem rep_prod_iff [FiniteDimensional F U₂] [FiniteDimensional F H] {K : Type*} [AddCommGroup K]
    [Module F K] [FiniteDimensional F K] {H' : Type*} [AddCommGroup H'] [Module F H']
    {A : QuadraticForm F U₁} {B : QuadraticForm F U₂} {C : QuadraticForm F K} {QH : QuadraticForm F H}
    {QH' : QuadraticForm F H'} (e : QH.IsometryEquiv QH') (hB : (polarBilin B).Nondegenerate)
    (hC : (polarBilin C).Nondegenerate) (hH : (polarBilin QH).Nondegenerate) :
    Rep (A.prod QH) ((B.prod QH').prod C) ↔ Rep A (B.prod C) := by
  constructor
  · intro h
    have h1 : Rep (A.prod QH) ((B.prod QH).prod C) :=
      Rep.congr (QuadraticMap.IsometryEquiv.refl _)
        (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl B)
          e.symm) (QuadraticMap.IsometryEquiv.refl C)) h
    have h2 : Rep (A.prod QH) ((B.prod C).prod QH) := Rep.congr (QuadraticMap.IsometryEquiv.refl _) (swap23 B QH C) h1
    exact Rep.cancel_right (QuadraticForm.nondegenerate_polarBilin_prod hB hC) hH h2
  · intro h
    have h1 : Rep (A.prod QH) ((B.prod C).prod QH) := Rep.prod_right QH h
    have h2 : Rep (A.prod QH) ((B.prod QH).prod C) := Rep.congr (QuadraticMap.IsometryEquiv.refl _) (swap23 B QH C).symm h1
    exact Rep.congr (QuadraticMap.IsometryEquiv.refl _)
      (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl B) e)
        (QuadraticMap.IsometryEquiv.refl C)) h2

end Abstract

section Lattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable {W : Type*} [AddCommGroup W] [Module F W] [Module R W] [IsScalarTower R F W]
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V') (QW : QuadraticForm F W)

/-- $\operatorname{polar} Q\, x\, y = 2B(x, y)$. -/
theorem polar_eq_two_bil (x y : V) : polar Q x y = 2 * bil Q x y := by
  rw [QuadraticMap.polar, Q_add]; ring

/-- **The space $FL$ of a regular lattice is nonsingular.** -/
theorem nondegenerate_subQ {L : Submodule R V} (hreg : IsRegular Q L) :
    (polarBilin (subQ Q L)).Nondegenerate := by
  rw [QuadraticForm.nondegenerate_polarBilin_iff]
  intro v hv
  have h2 : (2 : F) ≠ 0 := two_ne_zero' F
  have hbil : ∀ w ∈ spanF F L, bil Q (v : V) w = 0 := by
    intro w hw
    have := hv ⟨w, hw⟩
    have h' : polar Q (v : V) w = 0 := this
    rw [polar_eq_two_bil] at h'
    exact (mul_eq_zero.1 h').resolve_left h2
  obtain ⟨d, hd0, hdL⟩ := exists_smul_mem_of_mem_span (F := F) v.2
  have hd : d • (v : V) = 0 := hreg _ hdL fun y hy => by
    rw [bil_rsmul_left, hbil y (subset_span hy), mul_zero]
  have : (v : V) = 0 := by rw [eq_inv_smul_smul (F := F) hd0 (v : V), hd, smul_zero]
  exact Subtype.ext this

/-- **`SpanRepresents` is an embedding of quadratic spaces**: $FM \to FN \perp \langle c\rangle$ iff
`subQ Q M` embeds in `subQ Q N ⊥ c t²`. -/
theorem spanRepresents_iff_rep (M N : Submodule R V) (c : F) :
    SpanRepresents Q M N c ↔
      Rep (subQ Q M) ((subQ Q N).prod (c • (QuadraticMap.sq : QuadraticForm F F))) := by
  constructor
  · rintro ⟨f, hf, hQ⟩
    refine ⟨f, hf, fun x => ?_⟩
    have := hQ x
    simp only [QuadraticMap.prod_apply, QuadraticMap.smul_apply, QuadraticMap.sq_apply, smul_eq_mul]
    show Q ((f x).1 : V) + c * ((f x).2 * (f x).2) = Q (x : V)
    linear_combination this
  · rintro ⟨f, hf, hQ⟩
    refine ⟨f, hf, fun x => ?_⟩
    have := hQ x
    show Q ((f x).1 : V) + c * (f x).2 ^ 2 = Q (x : V)
    change Q ((f x).1 : V) + c * ((f x).2 * (f x).2) = Q (x : V) at this
    linear_combination this

theorem span_prod_eq (M : Submodule R V) (H : Submodule R W) :
    span F ((M.prod H : Submodule R (V × W)) : Set (V × W)) =
      (span F (M : Set V)).prod (span F (H : Set W)) := by
  apply le_antisymm
  · exact span_le.2 fun x hx => ⟨subset_span hx.1, subset_span hx.2⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have h1 : ((a, (0 : W))) ∈ span F ((M.prod H : Submodule R (V × W)) : Set (V × W)) := by
      refine span_induction (p := fun a _ => ((a, (0 : W))) ∈
        span F ((M.prod H : Submodule R (V × W)) : Set (V × W))) ?_ ?_ ?_ ?_ ha
      · intro m hm; exact subset_span ⟨hm, H.zero_mem⟩
      · exact zero_mem _
      · intro x y _ _ hx hy; simpa using add_mem hx hy
      · intro c x _ hx; simpa using smul_mem _ c hx
    have h2 : (((0 : V), b)) ∈ span F ((M.prod H : Submodule R (V × W)) : Set (V × W)) := by
      refine span_induction (p := fun b _ => (((0 : V), b)) ∈
        span F ((M.prod H : Submodule R (V × W)) : Set (V × W))) ?_ ?_ ?_ ?_ hb
      · intro m hm; exact subset_span ⟨M.zero_mem, hm⟩
      · exact zero_mem _
      · intro x y _ _ hx hy; simpa using add_mem hx hy
      · intro c x _ hx; simpa using smul_mem _ c hx
    simpa using add_mem h1 h2

/-- $F(M \perp H) = FM \perp FH$ as quadratic spaces. -/
def prodSubEquiv (M : Submodule R V) (H : Submodule R W) :
    ((subQ Q M).prod (subQ QW H)).IsometryEquiv (subQ (Q.prod QW) (M.prod H)) :=
  have hmem : ∀ q : V × W, q ∈ spanF F (M.prod H) ↔ q.1 ∈ spanF F M ∧ q.2 ∈ spanF F H := fun q => by
    rw [spanF, span_prod_eq]; exact Submodule.mem_prod
  { toFun := fun p => ⟨(p.1.1, p.2.1), (hmem _).2 ⟨p.1.2, p.2.2⟩⟩
    invFun := fun q => (⟨q.1.1, ((hmem q.1).1 q.2).1⟩, ⟨q.1.2, ((hmem q.1).1 q.2).2⟩)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_app' := fun p => by simp [subQ, QuadraticMap.prod_apply] }

/-- **An orthogonal sum of lattices gives an orthogonal sum of spaces**: if $L = J \perp K$ and $J$ is regular then
$FL = FJ \perp FK$. -/
def orthSubEquiv {L J K : Submodule R V} (h : IsOrthSum Q L J K) (hJ : IsRegular Q J) :
    ((subQ Q J).prod (subQ Q K)).IsometryEquiv (subQ Q L) := by
  have hJL : J ≤ L := h.sup_eq ▸ le_sup_left
  have hKL : K ≤ L := h.sup_eq ▸ le_sup_right
  have hbil : ∀ a ∈ spanF F J, ∀ b ∈ spanF F K, bil Q a b = 0 := by
    intro a ha b hb
    have h1 : ∀ x ∈ J, bil Q x b = 0 := fun x hx =>
      bil_zero_of_mem_span_F Q (fun z hz => h.orth x hx z hz) hb
    rw [bil_comm]
    exact bil_zero_of_mem_span_F Q (x := b) (fun z hz => by rw [bil_comm]; exact h1 z hz) ha
  let f : (spanF F J × spanF F K) →ₗ[F] spanF F L :=
    (Submodule.inclusion (span_mono hJL)).coprod (Submodule.inclusion (span_mono hKL))
  have hf : ∀ p, ((f p : spanF F L) : V) = (p.1 : V) + (p.2 : V) := fun p => by simp [f]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    rw [LinearMap.mem_ker] at hab
    have h0 : (a : V) + (b : V) = 0 := by
      have := hf (a, b)
      rw [hab] at this
      simpa using this.symm
    have ha0 : (a : V) = -(b : V) := eq_neg_of_add_eq_zero_left h0
    have hrad : ∀ w ∈ spanF F J, bil Q (a : V) w = 0 := by
      intro w hw
      rw [ha0, bil_neg_left, bil_comm, hbil w hw b b.2, neg_zero]
    have hrad' : ∀ w ∈ J, bil Q (a : V) w = 0 := fun w hw => hrad w (subset_span hw)
    have ha1 : (a : V) = 0 := by
      have := (nondegenerate_subQ Q hJ)
      rw [QuadraticForm.nondegenerate_polarBilin_iff] at this
      have := this a fun w => by
        show polar Q (a : V) (w : V) = 0
        rw [polar_eq_two_bil, bil_zero_of_mem_span_F Q (x := (a : V)) hrad' w.2, mul_zero]
      simpa using congrArg Subtype.val this
    have hb0 : (b : V) = 0 := by rw [ha1] at h0; simpa using h0
    have : a = 0 := Subtype.ext ha1
    have : b = 0 := Subtype.ext hb0
    simp_all
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ spanF F J ⊔ spanF F K := by
      have : span F ((J ⊔ K : Submodule R V) : Set V) ≤ spanF F J ⊔ spanF F K := by
        refine span_le.2 fun y hy => ?_
        obtain ⟨j, hj, k, hk, rfl⟩ := mem_sup.1 hy
        exact add_mem (mem_sup_left (subset_span hj)) (mem_sup_right (subset_span hk))
      rw [h.sup_eq] at this
      exact this hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.1 hx'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (by rw [hf])⟩
  exact
    { LinearEquiv.ofBijective f ⟨hinj, hsurj⟩ with
      map_app' := fun p => by
        show Q ((f p : spanF F L) : V) = Q (p.1 : V) + Q (p.2 : V)
        rw [hf, Q_add, hbil p.1 p.1.2 p.2 p.2.2]; ring }

/-- An isometry of the spans of two lattices, as an isometry of the quadratic spaces `subQ`. -/
def spanIsoEquiv {M : Submodule R V} {M' : Submodule R V'}
    (h : IsometricLat (R := F) Q Q' (span F (M : Set V)) (span F (M' : Set V'))) :
    (subQ Q M).IsometryEquiv (subQ Q' M') := by
  obtain ⟨f, hf⟩ := Classical.indefiniteDescription _ h
  exact { f with map_app' := hf }

/-- **Isometry invariance of `SpanRepresents`** (O'Meara 1963, §93F, proof of 93:28, p. 270: "an
isometry preserves ..."): the spaces $V$, $V'$ may differ. -/
@[kb "omeara1963" "§93F, proof of 93:28, pp. 270–272 (isometry invariance of FM → FN ⊥ ⟨c⟩)"]
theorem spanRepresents_iff_of_isometricLat {M N : Submodule R V} {M' N' : Submodule R V'} (hM : M.FG)
    (hN : N.FG) (hMM : IsometricLat Q Q' M M') (hNN : IsometricLat Q Q' N N') (c : F) :
    SpanRepresents Q M N c ↔ SpanRepresents Q' M' N' c := by
  have eM := spanIsoEquiv Q Q' (IsometricLat.span Q Q' hMM hM)
  have eN := spanIsoEquiv Q Q' (IsometricLat.span Q Q' hNN hN)
  have eNC := QuadraticMap.IsometryEquiv.prod eN
    (QuadraticMap.IsometryEquiv.refl (c • (QuadraticMap.sq : QuadraticForm F F)))
  rw [spanRepresents_iff_rep, spanRepresents_iff_rep]
  exact ⟨Rep.congr eM.symm eNC, Rep.congr eM eNC.symm⟩

/-- **Adjoining a regular lattice to both lattices** (O'Meara 1963, §93F, proof of 93:28, p. 270, "making
suitable hyperbolic adjunctions" and p. 271, "adjoining $V$"): for $M, N \subseteq V$ and a regular $H \subseteq W$,
$F(M \perp H) \to F(N \perp H) \perp \langle c\rangle$ iff $FM \to FN \perp \langle c\rangle$ (Witt cancellation of
$FH$). Here $N$ is regular and $c \ne 0$, so that $FN \perp \langle c\rangle$ is nonsingular. -/
@[kb "omeara1963" "§93F, proof of 93:28, pp. 270–272 (adjunction in FM → FN ⊥ ⟨c⟩; Witt cancellation §42F)"]
theorem spanRepresents_prod_iff [FiniteDimensional F V] [FiniteDimensional F W] {M N : Submodule R V}
    {H : Submodule R W} (hN : IsRegular Q N) (hH : IsRegular QW H) {c : F} (hc : c ≠ 0) :
    SpanRepresents (Q.prod QW) (M.prod H) (N.prod H) c ↔ SpanRepresents Q M N c := by
  rw [spanRepresents_iff_rep, spanRepresents_iff_rep]
  have eM := prodSubEquiv Q QW M H
  have eN := prodSubEquiv Q QW N H
  have eNC := QuadraticMap.IsometryEquiv.prod eN
    (QuadraticMap.IsometryEquiv.refl (c • (QuadraticMap.sq : QuadraticForm F F)))
  rw [← rep_prod_iff (A := subQ Q M) (B := subQ Q N)
    (C := c • (QuadraticMap.sq : QuadraticForm F F)) (QuadraticMap.IsometryEquiv.refl (subQ QW H))
    (nondegenerate_subQ Q hN) (nondegenerate_smul_sq hc) (nondegenerate_subQ QW hH)]
  exact ⟨Rep.congr eM eNC.symm, Rep.congr eM.symm eNC⟩

/-- **Cancelling a common orthogonal summand** (O'Meara 1963, §93F, proof of 93:28, p. 271): if
$M_1 = M \perp H$ and $N_1 = N \perp H'$ in the same space with $H \cong H'$ regular and $M$, $N$ regular, then
$FM_1 \to FN_1 \perp \langle c\rangle$ iff $FM \to FN \perp \langle c\rangle$. -/
@[kb "omeara1963" "§93F, proof of 93:28, pp. 270–272 (cancelling a common summand in FM → FN ⊥ ⟨c⟩)"]
theorem spanRepresents_iff_of_orthSum [FiniteDimensional F V] {M₁ M H N₁ N H' : Submodule R V}
    (hM : IsOrthSum Q M₁ M H) (hN : IsOrthSum Q N₁ N H') (hMreg : IsRegular Q M) (hNreg : IsRegular Q N)
    (hHreg : IsRegular Q H) (hHfg : H.FG) (hHH' : IsometricLat Q Q H H') {c : F} (hc : c ≠ 0) :
    SpanRepresents Q M₁ N₁ c ↔ SpanRepresents Q M N c := by
  rw [spanRepresents_iff_rep, spanRepresents_iff_rep]
  have eM := orthSubEquiv Q hM hMreg
  have eN := orthSubEquiv Q hN hNreg
  have eH := spanIsoEquiv Q Q (IsometricLat.span Q Q hHH' hHfg)
  have eNC := QuadraticMap.IsometryEquiv.prod eN
    (QuadraticMap.IsometryEquiv.refl (c • (QuadraticMap.sq : QuadraticForm F F)))
  rw [← rep_prod_iff (A := subQ Q M) (B := subQ Q N)
    (C := c • (QuadraticMap.sq : QuadraticForm F F)) eH
    (nondegenerate_subQ Q hNreg) (nondegenerate_smul_sq hc) (nondegenerate_subQ Q hHreg)]
  exact ⟨fun h => Rep.congr eM eNC.symm h, fun h => Rep.congr eM.symm eNC h⟩

/-- **Complements** (O'Meara 1963, §93F, proof of 93:28, p. 271, "since $FL_t$ is hyperbolic ... by Witt's
theorem"): let $L = A \perp B = A' \perp B'$ in the same space, all four summands regular and $c \ne 0$. If
$FB \to FB' \perp \langle c\rangle$ then $FA' \to FA \perp \langle c\rangle$.

(Witt-ring reasoning: $[A] + [B] = [A'] + [B']$ and $[B] \le [B'] + [c]$ give $[A'] \le [A] + [c]$.
The conclusion is **not** $FA \to FA' \perp \langle c\rangle$: with $L = \langle a\rangle \perp H =
\langle a'\rangle \perp \langle a, -a'\rangle$, $B = H$ the hypothesis says that $\langle a, -a', c\rangle$ is
isotropic, which says that $\langle a, c\rangle$ represents $a'$, not that $\langle a', c\rangle$ represents $a$.
Neither the hyperbolicity of $FB$ nor the equality of ranks is needed.) -/
@[kb "omeara1963" "§93F, proof of 93:28, pp. 270–272 (complements: FB → FB' ⊥ ⟨c⟩ gives FA' → FA ⊥ ⟨c⟩; Witt)"]
theorem spanRepresents_of_orthSum_complement [FiniteDimensional F V] {L A B A' B' : Submodule R V}
    (hA : IsOrthSum Q L A B) (hA' : IsOrthSum Q L A' B') (hAreg : IsRegular Q A) (hA'reg : IsRegular Q A')
    (hBreg : IsRegular Q B) {c : F} (hc : c ≠ 0) (h : SpanRepresents Q B B' c) :
    SpanRepresents Q A' A c := by
  rw [spanRepresents_iff_rep] at h ⊢
  have eL := orthSubEquiv Q hA hAreg
  have eL' := orthSubEquiv Q hA' hA'reg
  have hC := nondegenerate_smul_sq (F := F) hc
  have h1 := Rep.prod_left (subQ Q A') h
  -- `A' ⊥ (B' ⊥ c) ≅ (A ⊥ c) ⊥ B`
  have e1 : (((subQ Q A').prod ((subQ Q B').prod (c • (QuadraticMap.sq : QuadraticForm F F))))).IsometryEquiv
      (((subQ Q A).prod (c • (QuadraticMap.sq : QuadraticForm F F))).prod (subQ Q B)) :=
    ((assoc3 _ _ _).trans (QuadraticMap.IsometryEquiv.prod eL'
      (QuadraticMap.IsometryEquiv.refl _))).trans
      (((QuadraticMap.IsometryEquiv.prod eL (QuadraticMap.IsometryEquiv.refl _)).symm).trans
        (swap23 _ _ _))
  have h2 := Rep.congr (QuadraticMap.IsometryEquiv.refl _) e1 h1
  exact Rep.cancel_right (QuadraticForm.nondegenerate_polarBilin_prod (nondegenerate_subQ Q hAreg) hC)
    (nondegenerate_subQ Q hBreg) h2

end Lattice

end QuadFormsKB.OMeara.RepTransfer
