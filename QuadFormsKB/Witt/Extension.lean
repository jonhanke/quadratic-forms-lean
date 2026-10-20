/-
# Witt's extension theorem, in every characteristic

Let $K$ be any field, $V$ a finite-dimensional $K$-vector space and $Q$ a quadratic form on $V$
(Mathlib's `QuadraticForm K V`), with polar form $b(x, y) = Q(x + y) - Q(x) - Q(y)$ and
$\operatorname{rad} b = \{v : b(v, \cdot) = 0\}$ (`LinearMap.ker (QuadraticMap.polarBilin Q)`).

**Main result** (`QuadraticForm.exists_isometryEquiv_extend`, Elman–Karpenko–Merkurjev Thm 8.3).
Assume the **quadratic radical** `QuadraticMap.radical Q` $= \{v \in \operatorname{rad} b :
Q(v) = 0\}$ is zero (i.e. $Q$ is anisotropic on $\operatorname{rad} b$; EKM §7). Let
$W \subseteq V$ be a subspace and $\sigma : W \to V$ a linear map with $Q(\sigma w) = Q(w)$ for all
$w \in W$ which respects the polar radical: $\sigma(w) \in \operatorname{rad} b \iff
w \in \operatorname{rad} b$. Then $\sigma$ extends to an isometry $\rho$ of $(V, Q)$.

*No injectivity hypothesis is needed:* $\sigma(w) = 0$ forces $w \in \operatorname{rad} b$ and
$Q(w) = 0$, so $w = 0$.

**Special cases.**
* `QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate` (**nonsingular** forms, every
  characteristic): if $b$ is nondegenerate, every injective isometric embedding $W \to V$ extends.
* `QuadraticForm.exists_isometryEquiv_extend_of_associated` (**characteristic $\neq 2$**): if the
  associated symmetric bilinear form $\tfrac12 b$ (`QuadraticMap.associated`) is nondegenerate,
  every injective isometric embedding extends. (Lam Ch. I §4, Scharlau Ch. 1 Thm 5.3,
  O'Meara 42:17 [locators unverified].)
* `QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate'`: EKM's `QuadraticMap.Nondegenerate`
  (Mathlib's formalization of EKM §7: quadratic radical $0$ and $\dim \operatorname{rad} b \le 1$).

**Why the hypotheses.** For degenerate forms the theorem fails: if $v \in \operatorname{rad} b$,
$v \ne 0$, and $Q(v) = 0$, then $\sigma : Kv \to V$, $v \mapsto u$ for any isotropic
$u \notin \operatorname{rad} b$ is an isometric embedding, but isometries of $V$ preserve
$\operatorname{rad} b$. The same example in characteristic $2$ with $Q(v) = Q(u) \ne 0$ (e.g.
$V = \langle 1 \rangle \perp \mathbb{H}$, $v$ spanning $\langle 1 \rangle$, $u = e + f$ in
$\mathbb{H}$) shows why the radical condition on $\sigma$ is needed even when the quadratic radical
is $0$.

**Transitivity** (`QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate`,
`QuadraticForm.exists_isometryEquiv_apply_eq_of_isotropic`): $O(V)$ acts transitively on
$\{v : Q(v) = a\}$ for every $a \neq 0$ (nonsingular $Q$), and on the nonzero isotropic vectors
(quadratic radical $0$).

**Proof** (our own; it is close to the reflection proof of O'Meara 42:16–42:17 and Scharlau
Ch. 1 §5, with Eichler transformations replacing the char-$\ne 2$ trick). By induction on a basis
of $W$ one reduces to *one step*: $\sigma$ is the identity on a hyperplane $W_0$ of $W$ and sends
$x \mapsto y$. Put $z = x - y$; then $b(z, W_0) = 0$ and $b(z, x) = Q(z)$.
1. If $Q(z) \neq 0$, the reflection $\tau_z$ fixes $W_0$ and sends $x \mapsto y$.
2. If $Q(z) = 0$ and $x \notin W_0 + Kz + \operatorname{rad} b$, pick $u \perp W_0 + Kz$ with
   $b(u, x) = 1$; the Eichler transformation $E_{z,u}$ fixes $W_0$ and sends $x \mapsto x - z = y$.
3. Otherwise $x = w_0 + c z + r$ with $w_0 \in W_0$, $r \in \operatorname{rad} b$. If
   $z \in W_0 + \operatorname{rad} b$ then $z \in \operatorname{rad} b$ (radical condition), so
   $z = 0$ (quadratic radical $0$). If not, the radical condition gives $c \neq 0, 1$, and $z$ has a
   hyperbolic partner $z' \perp W_0$; scaling the pair $(z, z')$ by $(c - 1)/c$ fixes $W_0$ and
   sends $x \mapsto y$.

**Related work.** Tau Ceti (the Lean formalization project) contains a Witt theorem; this is an independent rewrite, nothing is imported or copied.

Sources: EKM Thm 8.3 (extension, all characteristics), §7 (radicals); Lam Ch. I §4; Scharlau
Ch. 1 Thm 5.3; O'Meara 42:16–42:17.
-/
import QuadFormsKB.Witt.Basic

open Module QuadraticMap

namespace QuadraticForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

namespace Witt

/-- **The induction step of Witt's theorem.** Assume the quadratic radical of $Q$ is $0$. Let
$W_0 \subseteq V$ and $x, y \in V$ with $Q(x) = Q(y)$, $b(x, w) = b(y, w)$ for $w \in W_0$, and
$x - w \in \operatorname{rad} b \iff y - w \in \operatorname{rad} b$ for $w \in W_0$. Then some
isometry $\rho$ of $V$ fixes $W_0$ pointwise and sends $x \mapsto y$. -/
theorem exists_step [FiniteDimensional K V] (hQ : Q.radical = ⊥) (W₀ : Submodule K V) {x y : V}
    (hQxy : Q x = Q y) (hb : ∀ w ∈ W₀, polar Q x w = polar Q y w)
    (hR : ∀ w ∈ W₀,
      (x - w ∈ LinearMap.ker (polarBilin Q) ↔ y - w ∈ LinearMap.ker (polarBilin Q))) :
    ∃ ρ : Q.IsometryEquiv Q, (∀ w ∈ W₀, ρ w = w) ∧ ρ x = y := by
  set R := LinearMap.ker (polarBilin Q) with hRdef
  set z := x - y with hzdef
  have hyz : y = x - z := by rw [hzdef, sub_sub_cancel]
  have hzW : ∀ w ∈ W₀, polar Q z w = 0 := fun w hw => by
    rw [hzdef, polar_sub_left, hb w hw, sub_self]
  have hQz : Q z = 2 * Q x - polar Q x y := by
    rw [hzdef, sub_eq_add_neg, map_add_eq, QuadraticMap.map_neg, polar_neg_right, ← hQxy]; ring
  have hzx : polar Q z x = Q z := by
    rw [hQz, hzdef, polar_sub_left, polar_self_eq, polar_comm Q y x]
  have hRpolar : ∀ r ∈ R, ∀ w, polar Q w r = 0 := fun r hr w => by
    rw [polar_comm]; exact (mem_ker_polarBilin Q).mp hr w
  -- Case 1: `Q z ≠ 0`, reflect.
  by_cases hz : Q z ≠ 0
  · refine ⟨isometryEquivOfMapApp Q hQ _ (reflection_map_app Q hz), fun w hw => ?_, ?_⟩
    · simp [reflection_apply, hzW w hw]
    · simp only [isometryEquivOfMapApp_apply, reflection_apply, hzx, inv_mul_cancel₀ hz, one_smul]
      exact hyz.symm
  push Not at hz
  -- Case 2: `x ∉ W₀ + K z + rad b`, use an Eichler transformation.
  by_cases hxU : x ∉ (W₀ ⊔ K ∙ z) ⊔ R
  · obtain ⟨u, hu, hux⟩ := exists_polar_ne_zero Q hxU
    obtain ⟨u', hu'w, hu'x⟩ : ∃ u', (∀ w ∈ W₀ ⊔ K ∙ z, polar Q u' w = 0) ∧ polar Q u' x = 1 :=
      ⟨(polar Q u x)⁻¹ • u, fun w hw => by rw [polar_smul_left, hu w hw, smul_zero], by
        rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hux]⟩
    have hzu' : polar Q z u' = 0 := by
      rw [polar_comm]
      exact hu'w z (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))
    refine ⟨isometryEquivOfMapApp Q hQ _ (eichler_map_app Q hz hzu'), fun w hw => ?_, ?_⟩
    · simp [eichler_apply, hzW w hw, hu'w w (Submodule.mem_sup_left hw)]
    · simp only [isometryEquivOfMapApp_apply, eichler_apply, hzx, hz, hu'x, zero_smul, add_zero,
        mul_zero, one_smul]
      exact hyz.symm
  push Not at hxU
  obtain ⟨a, ha, r, hr, hxar⟩ := Submodule.mem_sup.mp hxU
  obtain ⟨w₀, hw₀, zc, hzc, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzc
  -- Case 3a: `z ∈ W₀ + rad b`; then `z = 0`.
  by_cases hzR : z ∈ W₀ ⊔ R
  · obtain ⟨w₁, hw₁, r₁, hr₁, hzwr⟩ := Submodule.mem_sup.mp hzR
    have h1 : x - (w₀ + c • w₁) ∈ R := by
      have : x - (w₀ + c • w₁) = c • r₁ + r := by
        rw [← hxar, ← hzwr]; simp only [smul_add]; abel
      rw [this]; exact R.add_mem (R.smul_mem c hr₁) hr
    have h2 := (hR _ (W₀.add_mem hw₀ (W₀.smul_mem c hw₁))).mp h1
    have hzR' : z ∈ R := by
      have : z = (x - (w₀ + c • w₁)) - (y - (w₀ + c • w₁)) := by rw [hzdef]; abel
      rw [this]; exact R.sub_mem h1 h2
    have hz0 : z = 0 := by
      rw [← Submodule.mem_bot K, ← hQ]; exact ⟨hz, hzR'⟩
    refine ⟨QuadraticMap.IsometryEquiv.refl Q, fun w _ => rfl, ?_⟩
    rw [hyz, hz0, sub_zero]; rfl
  -- Case 3b: `z ∉ W₀ + rad b`; scale a hyperbolic pair `(z, z')`.
  have hzRnot : ∀ s ∈ R, z ≠ s := fun s hs h => hzR (h ▸ Submodule.mem_sup_right hs)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : x - w₀ ∈ R := by
      have : x - w₀ = r := by rw [← hxar]; simp only [zero_smul, add_zero]; abel
      rw [this]; exact hr
    have h2 := (hR w₀ hw₀).mp h1
    exact hzRnot _ (R.sub_mem h1 h2) (by rw [hzdef]; abel)
  have hc1 : c ≠ 1 := by
    rintro rfl
    have h2 : y - w₀ ∈ R := by
      have : y - w₀ = r := by rw [hyz, ← hxar]; simp only [one_smul]; abel
      rw [this]; exact hr
    have h1 := (hR w₀ hw₀).mpr h2
    exact hzRnot _ (R.sub_mem h1 hr) (by rw [← hxar]; simp only [one_smul]; abel)
  obtain ⟨u, hu, huz⟩ := exists_polar_ne_zero Q hzR
  obtain ⟨u', hu'w, hu'z⟩ : ∃ u', (∀ w ∈ W₀, polar Q u' w = 0) ∧ polar Q u' z = 1 :=
    ⟨(polar Q u z)⁻¹ • u, fun w hw => by rw [polar_smul_left, hu w hw, smul_zero], by
      rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ huz]⟩
  obtain ⟨z', hQz', hzz', hz'w⟩ : ∃ z', Q z' = 0 ∧ polar Q z z' = 1 ∧
      ∀ w ∈ W₀, polar Q z' w = 0 :=
    ⟨u' - Q u' • z, (hyperbolic_partner Q hz hu'z).1, (hyperbolic_partner Q hz hu'z).2,
      fun w hw => by
        rw [polar_sub_left, polar_smul_left, hu'w w hw, hzW w hw, smul_zero, sub_zero]⟩
  set l := (c - 1) / c with hl
  have hl0 : l ≠ 0 := div_ne_zero (sub_ne_zero.mpr hc1) hc0
  refine ⟨isometryEquivOfMapApp Q hQ _ (hypScale_map_app Q hl0 hz hQz' hzz'), fun w hw => ?_, ?_⟩
  · simp [hypScale_apply, hzW w hw, hz'w w hw]
  · have hz'x : polar Q z' x = c := by
      rw [← hxar, polar_add_right, polar_add_right, polar_smul_right, hz'w w₀ hw₀,
        hRpolar r hr, polar_comm Q z' z, hzz']; simp
    have hcoef : (l - 1) * c = -1 := by rw [hl]; field_simp; ring
    simp only [isometryEquivOfMapApp_apply, hypScale_apply, hz'x, hzx, hz, mul_zero, zero_smul,
      add_zero, hcoef, neg_one_smul]
    rw [hyz, sub_eq_add_neg]

/-- **Witt extension for families** (the form used in the induction). Assume the quadratic radical
of $Q$ is $0$. Let $v, w : \{0, \dots, k-1\} \to V$ have the same values and polar values,
$Q(v_i) = Q(w_i)$ and $b(v_i, v_j) = b(w_i, w_j)$, and satisfy the radical condition
$\sum_i c_i v_i \in \operatorname{rad} b \iff \sum_i c_i w_i \in \operatorname{rad} b$ for all
$c \in K^k$. Then some isometry $\rho$ of $V$ has $\rho(v_i) = w_i$ for all $i$.
(No linear independence is assumed.) -/
theorem exists_isometryEquiv_of_family [FiniteDimensional K V] (hQ : Q.radical = ⊥) :
    ∀ {k : ℕ} (v w : Fin k → V), (∀ i, Q (v i) = Q (w i)) →
      (∀ i j, polar Q (v i) (v j) = polar Q (w i) (w j)) →
      (∀ c : Fin k → K, (∑ i, c i • v i ∈ LinearMap.ker (polarBilin Q) ↔
        ∑ i, c i • w i ∈ LinearMap.ker (polarBilin Q))) →
      ∃ ρ : Q.IsometryEquiv Q, ∀ i, ρ (v i) = w i
  | 0, _, _, _, _, _ => ⟨QuadraticMap.IsometryEquiv.refl Q, fun i => i.elim0⟩
  | k + 1, v, w, hvw, hb, hR => by
    obtain ⟨τ, hτ⟩ := exists_isometryEquiv_of_family hQ (Fin.tail v) (Fin.tail w)
      (fun i => hvw _) (fun i j => hb _ _) (fun c => by
        simpa [Fin.sum_univ_succ, Fin.tail] using hR (Fin.cons 0 c))
    have hτv : ∀ i : Fin k, τ.symm (w i.succ) = v i.succ := fun i => by
      rw [QuadraticMap.IsometryEquiv.symm_apply_eq]; exact (hτ i).symm
    set y := τ.symm (w 0) with hy
    have h1 : Q (v 0) = Q y := by rw [hy, τ.symm.map_app, hvw]
    have h2 : ∀ u ∈ Submodule.span K (Set.range (Fin.tail v)), polar Q (v 0) u = polar Q y u := by
      intro u hu
      have : Set.EqOn (polarBilin Q (v 0)) (polarBilin Q y) (Set.range (Fin.tail v)) := by
        rintro _ ⟨i, rfl⟩
        simp only [polarBilin_apply_apply, Fin.tail]
        rw [hb, hy, ← hτv i, QuadraticMap.IsometryEquiv.polar_map]
      simpa using LinearMap.eqOn_span' this hu
    have h3 : ∀ u ∈ Submodule.span K (Set.range (Fin.tail v)),
        (v 0 - u ∈ LinearMap.ker (polarBilin Q) ↔ y - u ∈ LinearMap.ker (polarBilin Q)) := by
      intro u hu
      obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
      have h := hR (Fin.cons 1 (-d))
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, one_smul, Pi.neg_apply,
        neg_smul, Finset.sum_neg_distrib, ← sub_eq_add_neg] at h
      have hyw : y - ∑ i, d i • v i.succ = τ.symm (w 0 - ∑ i, d i • w i.succ) := by
        simp only [map_sub, map_sum, map_smul, hτv, hy]
      simp only [Fin.tail]
      rw [h, hyw, τ.symm.mem_ker_polarBilin_iff]
    obtain ⟨ρ, hρW, hρx⟩ := exists_step Q hQ _ h1 h2 h3
    refine ⟨ρ.trans τ, fun i => Fin.cases ?_ (fun i => ?_) i⟩
    · change τ (ρ (v 0)) = w 0
      rw [hρx, hy, QuadraticMap.IsometryEquiv.apply_symm_apply]
    · change τ (ρ (v i.succ)) = w i.succ
      rw [hρW (v i.succ) (Submodule.subset_span ⟨i, rfl⟩)]
      exact hτ i

end Witt

open _root_.QuadraticForm.Witt

/-- **Witt's extension theorem** (Elman–Karpenko–Merkurjev Thm 8.3; every field, including
characteristic $2$).

Let $K$ be a field, $V$ a finite-dimensional $K$-vector space and $Q$ a quadratic form on $V$ with
polar form $b(x, y) = Q(x + y) - Q(x) - Q(y)$. **Hypothesis on $Q$:** the quadratic radical
$\{v \in \operatorname{rad} b : Q(v) = 0\}$ (`QuadraticMap.radical Q`, EKM §7) is $0$.

Let $W \subseteq V$ be a subspace and $\sigma : W \to V$ a $K$-linear map such that
* $Q(\sigma w) = Q(w)$ for all $w \in W$ (an isometric embedding; injectivity follows), and
* $\sigma(w) \in \operatorname{rad} b \iff w \in \operatorname{rad} b$ for all $w \in W$, i.e.
  $\sigma(W \cap \operatorname{rad} b) = \sigma(W) \cap \operatorname{rad} b$ (automatic if $b$ is
  nondegenerate, in particular in characteristic $\neq 2$).

Then there is an isometry $\rho : (V, Q) \to (V, Q)$ with $\rho(w) = \sigma(w)$ for all $w \in W$.

Both hypotheses are necessary: isometries of $V$ preserve $\operatorname{rad} b$, and see the
module docstring for a counterexample when the quadratic radical is nonzero. -/
@[kb "ekm2008" "Thm 8.3"]
theorem exists_isometryEquiv_extend [FiniteDimensional K V] (hQ : Q.radical = ⊥)
    {W : Submodule K V} (σ : W →ₗ[K] V) (hσ : ∀ w, Q (σ w) = Q w)
    (hσR : ∀ w : W, σ w ∈ LinearMap.ker (polarBilin Q) ↔ (w : V) ∈ LinearMap.ker (polarBilin Q)) :
    ∃ ρ : Q.IsometryEquiv Q, ∀ w : W, ρ w = σ w := by
  set bW := Module.finBasis K W
  have hpol : ∀ a b : W, polar Q (σ a) (σ b) = polar Q a b := fun a b => by
    simp only [polar, ← map_add, hσ, Submodule.coe_add]
  obtain ⟨ρ, hρ⟩ := exists_isometryEquiv_of_family Q hQ (fun i => (bW i : V)) (fun i => σ (bW i))
    (fun i => (hσ _).symm) (fun i j => (hpol _ _).symm) (fun c => by
      have h1 : ∑ i, c i • (bW i : V) = ((∑ i, c i • bW i : W) : V) := by simp
      have h2 : ∑ i, c i • σ (bW i) = σ (∑ i, c i • bW i) := by simp
      rw [h1, h2, hσR])
  refine ⟨ρ, fun w => ?_⟩
  have : ρ.toLinearEquiv.toLinearMap ∘ₗ W.subtype = σ := bW.ext fun i => hρ i
  exact congr($this w)

/-- `QuadraticMap.radical Q = ⊥` when the polar form is nondegenerate. -/
theorem radical_eq_bot_of_nondegenerate (hQ : (polarBilin Q).Nondegenerate) : Q.radical = ⊥ :=
  eq_bot_iff.mpr fun v hv => (Submodule.mem_bot K).mpr <|
    hQ.1 v fun w => by simpa using congr($(hv.2) w)

/-- For nondegenerate polar form, `rad b = 0`. -/
theorem ker_polarBilin_eq_bot (hQ : (polarBilin Q).Nondegenerate) :
    LinearMap.ker (polarBilin Q) = ⊥ :=
  LinearMap.separatingLeft_iff_ker_eq_bot.mp hQ.1

/-- **Witt's extension theorem for nonsingular forms** (every characteristic; EKM Thm 8.3,
O'Meara 42:17 in characteristic $\ne 2$).

If the polar form $b(x, y) = Q(x + y) - Q(x) - Q(y)$ of $Q$ is nondegenerate
(`(QuadraticMap.polarBilin Q).Nondegenerate`; in characteristic $2$ this forces $\dim V$ even) and
$\sigma : W \to V$ is an **injective** linear map on a subspace $W$ with $Q(\sigma w) = Q(w)$, then
$\sigma$ extends to an isometry of $(V, Q)$. -/
@[kb "ekm2008" "Thm 8.3 (nonsingular case)"]
theorem exists_isometryEquiv_extend_of_nondegenerate [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {W : Submodule K V} (σ : W →ₗ[K] V)
    (hσi : Function.Injective σ) (hσ : ∀ w, Q (σ w) = Q w) :
    ∃ ρ : Q.IsometryEquiv Q, ∀ w : W, ρ w = σ w := by
  refine exists_isometryEquiv_extend Q (radical_eq_bot_of_nondegenerate Q hQ) σ hσ fun w => ?_
  rw [ker_polarBilin_eq_bot Q hQ, Submodule.mem_bot, Submodule.mem_bot,
    ZeroMemClass.coe_eq_zero, ← map_zero σ, hσi.eq_iff]

/-- **Witt's extension theorem in characteristic $\neq 2$** (Lam Ch. I §4 [locators unverified];
Scharlau Ch. 1 Thm 5.3; O'Meara 42:17).

If $2$ is invertible in $K$ and the associated symmetric bilinear form
$B(x, y) = \tfrac12\big(Q(x + y) - Q(x) - Q(y)\big)$ (`QuadraticMap.associated Q`) is
nondegenerate, then every injective linear map $\sigma : W \to V$ on a subspace $W$ with
$Q(\sigma w) = Q(w)$ extends to an isometry of $(V, Q)$. -/
@[kb "scharlau1985" "Ch. 1, Thm 5.3"]
theorem exists_isometryEquiv_extend_of_associated [FiniteDimensional K V] [Invertible (2 : K)]
    (hQ : (associated Q).Nondegenerate) {W : Submodule K V} (σ : W →ₗ[K] V)
    (hσi : Function.Injective σ) (hσ : ∀ w, Q (σ w) = Q w) :
    ∃ ρ : Q.IsometryEquiv Q, ∀ w : W, ρ w = σ w :=
  exists_isometryEquiv_extend_of_nondegenerate Q
    ((nondegenerate_polar_iff).mpr ((nondegenerate_associated_iff).mp hQ)) σ hσi hσ

/-- **Witt's extension theorem for EKM-nondegenerate forms** (EKM Thm 8.3), stated with
Mathlib's `QuadraticMap.Nondegenerate` (EKM §7: quadratic radical $0$ and
$\dim \operatorname{rad} b \le 1$). Only the first condition is used. -/
@[kb "ekm2008" "Thm 8.3"]
theorem exists_isometryEquiv_extend_of_nondegenerate' [FiniteDimensional K V]
    (hQ : QuadraticMap.Nondegenerate (Q := Q)) {W : Submodule K V} (σ : W →ₗ[K] V)
    (hσ : ∀ w, Q (σ w) = Q w)
    (hσR : ∀ w : W, σ w ∈ LinearMap.ker (polarBilin Q) ↔ (w : V) ∈ LinearMap.ker (polarBilin Q)) :
    ∃ ρ : Q.IsometryEquiv Q, ∀ w : W, ρ w = σ w :=
  exists_isometryEquiv_extend Q hQ.radical_eq_bot σ hσ hσR

/-! ### Transitivity -/

/-- **Transitivity on vectors with the same value** (general form). If the quadratic radical of
$Q$ is $0$, $Q(v) = Q(w)$, and $v \in \operatorname{rad} b \iff w \in \operatorname{rad} b$, then
some isometry $\rho$ of $V$ has $\rho(v) = w$. -/
@[kb "ekm2008" "Thm 8.3"]
theorem exists_isometryEquiv_apply_eq [FiniteDimensional K V] (hQ : Q.radical = ⊥) {v w : V}
    (h : Q v = Q w)
    (hR : v ∈ LinearMap.ker (polarBilin Q) ↔ w ∈ LinearMap.ker (polarBilin Q)) :
    ∃ ρ : Q.IsometryEquiv Q, ρ v = w := by
  obtain ⟨ρ, -, hρ⟩ := exists_step Q hQ ⊥ h (fun u hu => by simp [(Submodule.mem_bot K).mp hu])
    (fun u hu => by simpa [(Submodule.mem_bot K).mp hu] using hR)
  exact ⟨ρ, hρ⟩

/-- **$O(V)$ is transitive on each level set $\{v : Q(v) = a\}$, $a \neq 0$** (nonsingular forms,
every characteristic): if $b$ is nondegenerate and $Q(v) = Q(w) = a \neq 0$, some isometry
$\rho$ of $V$ has $\rho(v) = w$. (In characteristic $\ne 2$: Lam Ch. I §4; O'Meara 42:17.) -/
@[kb "ekm2008" "Thm 8.3 (nonsingular case)"]
theorem exists_isometryEquiv_apply_eq_of_nondegenerate [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {a : K} (ha : a ≠ 0) {v w : V} (hv : Q v = a)
    (hw : Q w = a) : ∃ ρ : Q.IsometryEquiv Q, ρ v = w := by
  refine exists_isometryEquiv_apply_eq Q (radical_eq_bot_of_nondegenerate Q hQ)
    (hv.trans hw.symm) ?_
  rw [ker_polarBilin_eq_bot Q hQ, Submodule.mem_bot, Submodule.mem_bot]
  constructor <;> rintro rfl <;> simp_all

/-- **$O(V)$ is transitive on nonzero isotropic vectors**: if the quadratic radical of $Q$ is $0$
(e.g. $b$ nondegenerate, or EKM-nondegenerate) and $v, w \neq 0$ with $Q(v) = Q(w) = 0$, then some
isometry $\rho$ of $V$ has $\rho(v) = w$. -/
@[kb "ekm2008" "Thm 8.3"]
theorem exists_isometryEquiv_apply_eq_of_isotropic [FiniteDimensional K V] (hQ : Q.radical = ⊥)
    {v w : V} (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv : Q v = 0) (hw : Q w = 0) :
    ∃ ρ : Q.IsometryEquiv Q, ρ v = w := by
  refine exists_isometryEquiv_apply_eq Q hQ (hv.trans hw.symm) ?_
  have hn : ∀ u, u ≠ 0 → Q u = 0 → u ∉ LinearMap.ker (polarBilin Q) := fun u hu0 hu hu' =>
    hu0 <| by rw [← Submodule.mem_bot K, ← hQ]; exact ⟨hu, hu'⟩
  exact iff_of_false (hn v hv0 hv) (hn w hw0 hw)

end QuadraticForm
