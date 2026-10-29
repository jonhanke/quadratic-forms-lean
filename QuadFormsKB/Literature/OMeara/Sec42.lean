import QuadFormsKB.Literature.OMeara.Sec41

/-!
# O'Meara §42: orthogonal splittings, radicals, isotropy, involutions (42:2–42:14a)

**Setting** (as in `Sec41.lean`): $F$ a field with $2 \ne 0$ (`[Invertible (2 : F)]`), $(V, Q)$ a quadratic space
over $F$, $B$ = `bil Q` with $B(x,x) = Q(x)$. The radical of a subspace $S$, $\operatorname{rad} S = \{x \in S :
B(x, S) = 0\}$, is `splitComp (R := F) Q S S` (`Sec82.lean`); $V$ is *regular* when $\operatorname{rad} V = 0$,
equivalently `(QuadraticMap.associated Q).Nondegenerate`. A *representation* is a linear map $\sigma$ with
$Q'(\sigma x) = Q(x)$; $O(V)$ = `orth Q`.

**Proves** (O'Meara 1973 printing, Chapter IV, §42, pp. 91–96):
* `rad_eq_iSup` (**42:2**): if $V = V_1 + \dots + V_r$ with the $V_i$ pairwise orthogonal then
  $\operatorname{rad} V = \operatorname{rad} V_1 + \dots + \operatorname{rad} V_r$;
* `rad_eq_bot_iff_forall` (**42:2a**): such a $V$ is regular iff every $V_i$ is;
* `iSupIndep_of_rad_eq_bot` (**42:2b**): if $V$ is regular the sum is direct, $V = V_1 \perp \dots \perp V_r$;
* `gram_dualBasis` (**42:5**): the matrix of $V$ in the dual base is the inverse of the matrix in the base;
* `injective_of_rep` (**42:7**): a representation of a regular space is injective (an isometry);
* `isHyperbolicPlane_tfae` (**42:9**): for a binary space, hyperbolic plane $\iff$ isotropic and regular $\iff$
  $dV = -1$;
* `mem_range_iff_isotropic_prod` (**42:11**): for regular $V$, $\alpha \in Q(V)$ iff $\langle -\alpha\rangle \perp V$
  is isotropic;
* `exists_hyperbolic_partners` (**42:13**): a base $x_1, \dots, x_r$ of a totally isotropic subspace of a regular space
  has partners $y_i$ with $Q(y_i) = 0$, $B(y_i, y_j) = 0$, $B(x_i, y_j) = \delta_{ij}$, so that the planes
  $H_i = Fx_i + Fy_i$ are hyperbolic and pairwise orthogonal;
* `involution_iff_splitting` (**42:14**) and `splitting_eq_fixed` (**42:14a**): $\sigma \in O(V)$ is an involution iff
  $V = U \perp W$ with $\sigma = -1_U \perp 1_W$, and then $W$ is the fixed space and $U$ the reversed space.

**Conventions.** Indices are 0-based. A family of subspaces is indexed by any type `ι` (finite where needed). In
42:9, $dV = -1$ is stated as "some base has discriminant $-1$", which is O'Meara's meaning of $dV = -1$ in
$F/F^{\times 2}$ (p. 87). In 42:11, $\langle -\alpha\rangle \perp V$ is the form $(t, x) \mapsto -\alpha t^2 + Q(x)$
on $F \times V$ (Mathlib `QuadraticMap.prod`).
-/

open QuadraticMap Submodule Module LinearMap
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec42

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

theorem iv_two_ne : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero

theorem iv_mem_rad_iff (S : Submodule F V) (x : V) :
    x ∈ splitComp (R := F) Q S S ↔ x ∈ S ∧ ∀ z ∈ S, bil Q x z = 0 := Iff.rfl

/-- Pairwise orthogonality of a family of subspaces: $B(V_i, V_j) = 0$ for $i \ne j$. -/
def PairwiseOrth {ι : Type*} (Vs : ι → Submodule F V) : Prop :=
  ∀ i j, i ≠ j → ∀ x ∈ Vs i, ∀ y ∈ Vs j, bil Q x y = 0

theorem bil_eq_zero_of_mem_iSup_ne {ι : Type*} {Vs : ι → Submodule F V} (h : PairwiseOrth Q Vs) {i : ι}
    {x : V} (hx : x ∈ Vs i) {y : V} (hy : y ∈ ⨆ j, ⨆ (_ : j ≠ i), Vs j) : bil Q x y = 0 := by
  refine Submodule.iSup_induction _ (motive := fun y => bil Q x y = 0) hy (fun j y hy => ?_) (by simp [bil])
    (fun a b ha hb => by rw [bil_add_right, ha, hb, add_zero])
  refine Submodule.iSup_induction _ (motive := fun y => bil Q x y = 0) hy (fun hji y hy => ?_) (by simp [bil])
    (fun a b ha hb => by rw [bil_add_right, ha, hb, add_zero])
  exact h i j (Ne.symm hji) x hx y hy

/-- **O'Meara 42:2** (p. 91). Let $V = V_1 + \dots + V_r$ be a sum of pairwise orthogonal subspaces
($B(V_i, V_j) = 0$ for $i \ne j$). Then $\operatorname{rad} V = \operatorname{rad} V_1 + \dots + \operatorname{rad} V_r$. -/
@[kb "omeara1963" "§42B, 42:2, p. 91"]
theorem rad_eq_iSup {ι : Type*} {Vs : ι → Submodule F V} (h : PairwiseOrth Q Vs) (htop : ⨆ i, Vs i = ⊤) :
    splitComp (R := F) Q ⊤ ⊤ = ⨆ i, splitComp (R := F) Q (Vs i) (Vs i) := by
  classical
  apply le_antisymm
  · intro x hx
    have hxV : x ∈ ⨆ i, Vs i := htop ▸ Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hxV
    refine Submodule.sum_mem _ fun i _ => ?_
    refine Submodule.mem_iSup_of_mem i ⟨hf i, fun z hz => ?_⟩
    have h0 := hx.2 z Submodule.mem_top
    rw [Finsupp.sum, bil_sum_left] at h0
    rw [← h0, Finset.sum_eq_single i]
    · intro j _ hji; exact h j i hji _ (hf j) z hz
    · intro hi; rw [Finsupp.notMem_support_iff.1 hi]; simp [bil]
  · intro x hx
    refine ⟨Submodule.mem_top, fun z _ => ?_⟩
    have hz : z ∈ ⨆ i, Vs i := htop ▸ Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun x => bil Q x z = 0) hx (fun i x hx => ?_) (by simp [bil])
      (fun a b ha hb => by rw [bil_add_left, ha, hb, add_zero])
    refine Submodule.iSup_induction _ (motive := fun z => bil Q x z = 0) hz (fun j z hz => ?_) (by simp [bil])
      (fun a b ha hb => by rw [bil_add_right, ha, hb, add_zero])
    by_cases hij : i = j
    · subst hij; exact hx.2 z hz
    · exact h i j hij x hx.1 z hz

/-- **O'Meara 42:2a** (p. 91). With $V = V_1 + \dots + V_r$ as in 42:2, $V$ is regular
($\operatorname{rad} V = 0$) if and only if every $V_i$ is regular. -/
@[kb "omeara1963" "§42B, 42:2a, p. 91"]
theorem rad_eq_bot_iff_forall {ι : Type*} {Vs : ι → Submodule F V} (h : PairwiseOrth Q Vs)
    (htop : ⨆ i, Vs i = ⊤) :
    splitComp (R := F) Q ⊤ ⊤ = ⊥ ↔ ∀ i, splitComp (R := F) Q (Vs i) (Vs i) = ⊥ := by
  rw [rad_eq_iSup Q h htop, iSup_eq_bot]

/-- **O'Meara 42:2b** (p. 91). With $V = V_1 + \dots + V_r$ as in 42:2, if $V$ is regular then the sum is direct
(the $V_i$ are independent), so $V = V_1 \perp \dots \perp V_r$. -/
@[kb "omeara1963" "§42B, 42:2b, p. 91"]
theorem iSupIndep_of_rad_eq_bot {ι : Type*} {Vs : ι → Submodule F V} (h : PairwiseOrth Q Vs)
    (htop : ⨆ i, Vs i = ⊤) (hreg : splitComp (R := F) Q ⊤ ⊤ = ⊥) : iSupIndep Vs := by
  have hr := (rad_eq_bot_iff_forall Q h htop).1 hreg
  intro i
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxi, hxo⟩
  have : x ∈ splitComp (R := F) Q (Vs i) (Vs i) := ⟨hxi, fun z hz => by
    rw [bil_comm]; exact bil_eq_zero_of_mem_iSup_ne Q h hz hxo⟩
  rw [hr i] at this
  exact this

/-- **O'Meara 42:7** (p. 93). A representation $\sigma : V \to W$ ($Q'(\sigma x) = Q(x)$) of a regular quadratic space
$V$ is injective, hence an isometry of $V$ into $W$. -/
@[kb "omeara1963" "§42C, 42:7, p. 93"]
theorem injective_of_rep {W : Type*} [AddCommGroup W] [Module F W] (Q' : QuadraticForm F W)
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (σ : V →ₗ[F] W) (hσ : ∀ x, Q' (σ x) = Q x) :
    Function.Injective σ := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hB := (rep_iff_compl₁₂ Q Q' σ).1 hσ
  refine (Submodule.mem_bot F).2 (hQ.1 x fun y => ?_)
  have := congrArg (fun B : LinearMap.BilinForm F V => B x y) hB
  simp only [LinearMap.compl₁₂_apply, LinearMap.mem_ker.1 hx, map_zero, LinearMap.zero_apply] at this
  exact this.symm

/-- $\sigma \in O(V)$ preserves $B$. -/
theorem iv_bil_orth {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (x y : V) : bil Q (σ x) (σ y) = bil Q x y := by
  have hB := (rep_iff_compl₁₂ Q Q (σ : V →ₗ[F] V)).1 hσ
  exact congrArg (fun B : LinearMap.BilinForm F V => B x y) hB

/-- **O'Meara 42:14** (p. 96). An isometry $\sigma \in O(V)$ is an involution ($\sigma^2 = 1$) if and only if there is
a splitting $V = U \perp W$ ($U$, $W$ complementary and orthogonal) with $\sigma = -1_U \perp 1_W$, i.e.
$\sigma u = -u$ on $U$ and $\sigma w = w$ on $W$. -/
@[kb "omeara1963" "§42E, 42:14, p. 96"]
theorem involution_iff_splitting {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) :
    (∀ x, σ (σ x) = x) ↔
      ∃ U W : Submodule F V, IsCompl U W ∧ (∀ u ∈ U, ∀ w ∈ W, bil Q u w = 0) ∧
        (∀ u ∈ U, σ u = -u) ∧ (∀ w ∈ W, σ w = w) := by
  constructor
  · intro h2
    let P : V →ₗ[F] V := (σ : V →ₗ[F] V) + LinearMap.id
    let M : V →ₗ[F] V := (σ : V →ₗ[F] V) - LinearMap.id
    refine ⟨LinearMap.ker P, LinearMap.ker M, ?_, ?_, ?_, ?_⟩
    · constructor
      · rw [disjoint_iff, eq_bot_iff]
        rintro x ⟨hP, hM⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, P, M, LinearMap.add_apply, LinearMap.sub_apply,
          LinearEquiv.coe_coe, LinearMap.id_apply] at hP hM
        have : (2 : F) • x = 0 := by
          rw [two_smul]
          calc x + x = (σ x + x) - (σ x - x) := by abel
            _ = 0 := by rw [hP, hM, sub_zero]
        exact (Submodule.mem_bot F).2 ((smul_eq_zero.1 this).resolve_left iv_two_ne)
      · rw [codisjoint_iff, eq_top_iff]
        intro x _
        have hx : x = (⅟2 : F) • (x - σ x) + (⅟2 : F) • (x + σ x) := by
          rw [← smul_add]; rw [show x - σ x + (x + σ x) = (2 : F) • x by rw [two_smul]; abel, smul_smul,
            invOf_mul_self, one_smul]
        rw [hx]
        refine Submodule.add_mem_sup ?_ ?_
        · show σ ((⅟2 : F) • (x - σ x)) + (⅟2 : F) • (x - σ x) = 0
          rw [map_smul, map_sub, h2, ← smul_add, show σ x - x + (x - σ x) = 0 by abel, smul_zero]
        · show σ ((⅟2 : F) • (x + σ x)) - (⅟2 : F) • (x + σ x) = 0
          rw [map_smul, map_add, h2, ← smul_sub, show σ x + x - (x + σ x) = 0 by abel, smul_zero]
    · intro u hu w hw
      simp only [LinearMap.mem_ker, P, M, LinearMap.add_apply, LinearMap.sub_apply, LinearEquiv.coe_coe,
        LinearMap.id_apply] at hu hw
      have hu' : σ u = -u := eq_neg_of_add_eq_zero_left hu
      have hw' : σ w = w := sub_eq_zero.1 hw
      have := iv_bil_orth Q hσ u w
      rw [hu', hw', bil_neg_left] at this
      have h2b : (2 : F) * bil Q u w = 0 := by linear_combination -this
      exact (mul_eq_zero.1 h2b).resolve_left iv_two_ne
    · intro u hu
      simp only [LinearMap.mem_ker, P, LinearMap.add_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at hu
      exact eq_neg_of_add_eq_zero_left hu
    · intro w hw
      simp only [LinearMap.mem_ker, M, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at hw
      exact sub_eq_zero.1 hw
  · rintro ⟨U, W, hc, -, hU, hW⟩ x
    have hx : x ∈ U ⊔ W := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, map_add, hU u hu, hW w hw, map_neg, hU u hu, hW w hw, neg_neg]

/-- **O'Meara 42:14a** (p. 96). In a splitting $V = U \perp W$ with $\sigma = -1_U \perp 1_W$ as in 42:14, $W$ is the set
of vectors fixed by $\sigma$ and $U$ the set of vectors reversed by $\sigma$. -/
@[kb "omeara1963" "§42E, 42:14a, p. 96"]
theorem splitting_eq_fixed {σ : V ≃ₗ[F] V} {U W : Submodule F V} (hc : IsCompl U W)
    (hU : ∀ u ∈ U, σ u = -u) (hW : ∀ w ∈ W, σ w = w) :
    (∀ x, x ∈ W ↔ σ x = x) ∧ (∀ x, x ∈ U ↔ σ x = -x) := by
  have key : ∀ x, ∃ u ∈ U, ∃ w ∈ W, u + w = x := fun x =>
    Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top : x ∈ U ⊔ W)
  have h2 : ∀ v : V, (2 : F) • v = 0 → v = 0 := fun v hv =>
    (smul_eq_zero.1 hv).resolve_left iv_two_ne
  refine ⟨fun x => ⟨hW x, fun hx => ?_⟩, fun x => ⟨hU x, fun hx => ?_⟩⟩
  · obtain ⟨u, hu, w, hw, rfl⟩ := key x
    rw [map_add, hU u hu, hW w hw] at hx
    have : u = 0 := h2 u (by
      rw [two_smul]
      calc u + u = (u + w) - (-u + w) := by abel
        _ = 0 := by rw [hx, sub_self])
    rw [this, zero_add]; exact hw
  · obtain ⟨u, hu, w, hw, rfl⟩ := key x
    rw [map_add, hU u hu, hW w hw] at hx
    have : w = 0 := h2 w (by
      rw [two_smul]
      calc w + w = (-u + w) + (u + w) := by abel
        _ = 0 := by rw [hx]; abel)
    rw [this, add_zero]; exact hu

end Sec42

end QuadFormsKB.OMeara
