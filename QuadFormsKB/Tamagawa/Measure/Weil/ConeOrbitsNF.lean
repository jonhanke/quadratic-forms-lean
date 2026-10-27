import QuadFormsKB.Tamagawa.Measure.Weil.SphereOrbitsNF

/-!
# Orbits of $\mathrm{SO}(V)(F)$ on the punctured rational cone
**Generic part (any field $R$ with $2\ne0$).** $H\in M_n(R)$ symmetric with $\det H\ne0$, $n\ge3$,
$q(x) = x^{\mathsf T}Hx$, $B(x, y) = x^{\mathsf T}Hy$, as in `ReflectionSection`.

* **`exists_bH_ne_zero`**: a nonzero $y$ pairs nontrivially with some $z$ (nondegeneracy).
* **`exists_anisotropic_orth_isotropic`**: for a nonzero isotropic $y$ there is an anisotropic $v\perp y$
  (this uses $n\ge3$: with an isotropic $z$, $B(y,z)\ne0$, the complement $W = \{y, z\}^\perp$ is nonzero and $B$ is
  nondegenerate on it, so $q$ does not vanish on $W\subseteq y^\perp$).
* **`exists_SO_mulVec_eq_isotropic`**: if $q(x) = q(y) = 0$, $x,y\ne0$, then $y = gx$ with $g^{\mathsf T}Hg = H$,
  $\det g = 1$. Case $B(x,y)\ne0$: $y = \tau_{x-y}x$ and $\tau_v$ fixes $y$ for an anisotropic $v\perp y$, so
  $g = \tau_v\tau_{x-y}$; case $B(x,y)=0$: pass through an isotropic $z$ with $B(x,z)\ne0\ne B(y,z)$.

**Number field part.** $F$ a number field, $Q_0$ a form over $\mathcal O_F$ in $n$ variables, $Q = Q_0\otimes F$.
`RatCone Q₀` is the punctured rational cone $\{\eta\in F^n : Q(\eta)=0,\ \eta\ne0\}$, a `GammaSOAdele Q₀`-set
(`instMulActionRatCone`) with the diagonal embedding equivariant (`diagVec_smul_ratCone`), and
**`exists_smul_eq_ratCone`** (Witt's theorem for $\mathrm{SO}(V)(F)$ on the punctured cone, $n\ge3$) says the action is
transitive. `tsum_ite_eq_tsum_ratCone` converts indicator sums over the cone into sums over `RatCone Q₀`.
-/

open MeasureTheory Set Matrix
open scoped ENNReal Matrix

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

section Generic

variable {R : Type*} [Field R] {n : ℕ} {H : Matrix (Fin n) (Fin n) R}

/-- **Nondegeneracy:** if $\det H\ne0$ and $y\ne0$, then $B(y, z)\ne0$ for some $z$. -/
theorem exists_bH_ne_zero (hdet : H.det ≠ 0) {y : Fin n → R} (hy : y ≠ 0) : ∃ z, bH H y z ≠ 0 := by
  by_contra h
  push Not at h
  apply hy
  apply Matrix.eq_zero_of_vecMul_eq_zero hdet
  ext i
  have := h (Pi.single i 1)
  simpa [bH, Matrix.vecMul, dotProduct, mulVec, Pi.single_apply] using this

/-- **An anisotropic vector orthogonal to a nonzero isotropic vector** ($n\ge3$, $\det H\ne0$, $2\ne0$):
if $q(y)=0$, $y\ne0$, then some $v$ with $B(v, y)=0$ has $q(v)\ne0$. -/
theorem exists_anisotropic_orth_isotropic (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (hdet : H.det ≠ 0) (hn : 3 ≤ n)
    {y : Fin n → R} (hy0 : y ≠ 0) (hy : qH H y = 0) : ∃ v, qH H v ≠ 0 ∧ bH H v y = 0 := by
  by_contra hcon
  push Not at hcon
  -- every vector orthogonal to `y` is isotropic
  have hiso : ∀ v, bH H v y = 0 → qH H v = 0 := fun v hv => by
    by_contra hne; exact hcon v hne hv
  -- polarization on `y^⊥`
  have hpol : ∀ v w, bH H v y = 0 → bH H w y = 0 → bH H v w = 0 := by
    intro v w hv hw
    have hvw : bH H (v + w) y = 0 := by rw [bH_add_left, hv, hw, add_zero]
    have := qH_add hH v w
    rw [hiso _ hvw, hiso v hv, hiso w hw] at this
    have h' : 2 * bH H v w = 0 := by linear_combination -this
    exact (mul_eq_zero.1 h').resolve_left h2
  obtain ⟨z, hz⟩ := exists_bH_ne_zero hdet hy0
  set b := bH H y z with hb
  set z' : Fin n → R := z - (qH H z / (2 * b)) • y with hz'
  have hyz' : bH H y z' = b := by
    rw [hz', bH_sub_right, bH_smul_right, ← qH_eq_bH, hy]; ring
  have hz'y : bH H z' y = b := by rw [bH_comm hH, hyz']
  have hqz' : qH H z' = 0 := by
    rw [hz', qH_sub hH, bH_smul_right, qH_eq_bH H ((qH H z / (2 * b)) • y), bH_smul_left, bH_smul_right,
      ← qH_eq_bH, hy, bH_comm hH z y, ← hb]
    field_simp
    ring
  -- decomposition
  have hdec : ∀ t : Fin n → R, ∃ w, bH H w y = 0 ∧ bH H w z' = 0 ∧
      t = w + (bH H t z' / b) • y + (bH H t y / b) • z' := by
    intro t
    refine ⟨t - (bH H t z' / b) • y - (bH H t y / b) • z', ?_, ?_, by abel⟩
    · rw [bH_sub_left, bH_sub_left, bH_smul_left, bH_smul_left, ← qH_eq_bH, hy, hz'y]
      field_simp; ring
    · rw [bH_sub_left, bH_sub_left, bH_smul_left, bH_smul_left, ← qH_eq_bH, hqz', hyz']
      field_simp; ring
  -- every `t` lies in the span of `y` and `z'`
  have hspan : Submodule.span R (Set.range (![y, z'] : Fin 2 → Fin n → R)) = ⊤ := by
    rw [eq_top_iff]
    intro t _
    obtain ⟨w, hwy, hwz, ht⟩ := hdec t
    have hw0 : w = 0 := by
      by_contra hw
      obtain ⟨t', ht'⟩ := exists_bH_ne_zero hdet hw
      obtain ⟨w', hw'y, hw'z, htt'⟩ := hdec t'
      apply ht'
      have : bH H w t' = bH H w w' + (bH H t' z' / b) * bH H w y + (bH H t' y / b) * bH H w z' := by
        conv_lhs => rw [htt']
        rw [bH_add_right, bH_add_right, bH_smul_right, bH_smul_right]
      rw [this, hpol w w' hwy hw'y, hwy, hwz]; ring
    rw [ht, hw0, zero_add]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have := finrank_range_le_card (R := R) (![y, z'] : Fin 2 → Fin n → R)
  rw [Set.finrank, hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at this
  omega

/-- The case $B(x,y)\ne0$: $g = \tau_v\tau_{x-y}$ with $v\perp y$ anisotropic. -/
theorem exists_SO_mulVec_eq_isotropic_of_bH_ne_zero (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (hdet : H.det ≠ 0)
    (hn : 3 ≤ n) {x y : Fin n → R} (hy0 : y ≠ 0) (hx : qH H x = 0) (hy : qH H y = 0) (hb : bH H x y ≠ 0) :
    ∃ g : Matrix (Fin n) (Fin n) R, gᵀ * H * g = H ∧ g.det = 1 ∧ g *ᵥ x = y := by
  have hu : qH H (x - y) = -(2 * bH H x y) := by rw [qH_sub hH, hx, hy]; ring
  have hu0 : qH H (x - y) ≠ 0 := by rw [hu]; exact neg_ne_zero.2 (mul_ne_zero h2 hb)
  have hux : refl H (x - y) *ᵥ x = y := by
    rw [refl_mulVec hH]
    have : bH H (x - y) x = -bH H x y := by
      rw [bH_sub_left, ← qH_eq_bH, hx, bH_comm hH y x]; ring
    rw [this, hu, show 2 * -bH H x y / -(2 * bH H x y) = 1 by field_simp, one_smul]
    abel
  obtain ⟨v, hv0, hvy⟩ := exists_anisotropic_orth_isotropic hH h2 hdet hn hy0 hy
  refine ⟨refl H v * refl H (x - y), ?_, ?_, ?_⟩
  · rw [transpose_mul, show (refl H (x - y))ᵀ * (refl H v)ᵀ * H * (refl H v * refl H (x - y)) =
        (refl H (x - y))ᵀ * ((refl H v)ᵀ * H * refl H v) * refl H (x - y) by simp only [Matrix.mul_assoc],
      transpose_refl_mul_mul_refl hH hv0, transpose_refl_mul_mul_refl hH hu0]
  · rw [det_mul, det_refl hv0, det_refl hu0]; ring
  · rw [← mulVec_mulVec, hux, refl_of_orth hH hvy]

/-- **Witt's theorem for $\mathrm{SO}$ on nonzero isotropic vectors** ($n\ge3$): if $q(x)=q(y)=0$ and $x,y\ne0$,
then $y = gx$ with $g^{\mathsf T}Hg = H$ and $\det g = 1$. -/
@[kb "omeara1963" "§42F, 42:17, p. 98 (Witt's theorem); isotropic vectors"]
theorem exists_SO_mulVec_eq_isotropic (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (hdet : H.det ≠ 0) (hn : 3 ≤ n)
    {x y : Fin n → R} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : qH H x = 0) (hy : qH H y = 0) :
    ∃ g : Matrix (Fin n) (Fin n) R, gᵀ * H * g = H ∧ g.det = 1 ∧ g *ᵥ x = y := by
  by_cases hb : bH H x y ≠ 0
  · exact exists_SO_mulVec_eq_isotropic_of_bH_ne_zero hH h2 hdet hn hy0 hx hy hb
  push Not at hb
  obtain ⟨t₁, ht₁⟩ := exists_bH_ne_zero hdet hx0
  obtain ⟨t₂, ht₂⟩ := exists_bH_ne_zero hdet hy0
  obtain ⟨t, htx, hty⟩ : ∃ t, bH H x t ≠ 0 ∧ bH H y t ≠ 0 := by
    by_cases h1 : bH H y t₁ ≠ 0
    · exact ⟨t₁, ht₁, h1⟩
    by_cases h2' : bH H x t₂ ≠ 0
    · exact ⟨t₂, h2', ht₂⟩
    push Not at h1 h2'
    exact ⟨t₁ + t₂, by rw [bH_add_right, h2', add_zero]; exact ht₁,
      by rw [bH_add_right, h1, zero_add]; exact ht₂⟩
  set l : R := -qH H t / (2 * bH H x t) with hl
  set z : Fin n → R := t + l • x with hz
  have hxz : bH H x z = bH H x t := by
    rw [hz, bH_add_right, bH_smul_right, ← qH_eq_bH, hx]; ring
  have hyz : bH H y z = bH H y t := by
    rw [hz, bH_add_right, bH_smul_right, bH_comm hH y x, hb]; ring
  have hqz : qH H z = 0 := by
    have key : qH H (l • x) = 0 := by
      rw [qH_eq_bH, bH_smul_left, bH_smul_right, ← qH_eq_bH, hx]; ring
    rw [hz, qH_add hH, key, bH_smul_right, bH_comm hH t x, hl]
    field_simp
    ring
  have hz0 : z ≠ 0 := fun h => htx (by rw [← hxz, h]; simp [bH])
  have hxz' : bH H x z ≠ 0 := by rw [hxz]; exact htx
  have hzy : bH H z y ≠ 0 := by rw [bH_comm hH, hyz]; exact hty
  obtain ⟨g₁, h₁o, h₁d, h₁⟩ := exists_SO_mulVec_eq_isotropic_of_bH_ne_zero hH h2 hdet hn hz0 hx hqz hxz'
  obtain ⟨g₂, h₂o, h₂d, h₂⟩ := exists_SO_mulVec_eq_isotropic_of_bH_ne_zero hH h2 hdet hn hy0 hqz hy hzy
  refine ⟨g₂ * g₁, ?_, ?_, ?_⟩
  · rw [transpose_mul, show g₁ᵀ * g₂ᵀ * H * (g₂ * g₁) = g₁ᵀ * (g₂ᵀ * H * g₂) * g₁ by
      simp only [Matrix.mul_assoc], h₂o, h₁o]
  · rw [det_mul, h₁d, h₂d]; ring
  · rw [← mulVec_mulVec, h₁, h₂]

end Generic

/-! ### The punctured rational cone as an $\mathrm{SO}(V)(F)$-set -/

section NumberField

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **The punctured rational cone** $C(F)\setminus0 = \{\eta\in F^n : Q(\eta) = 0,\ \eta\ne0\}$. -/
def RatCone : Type := {η : Fin n → F // qF Q₀ η = 0 ∧ η ≠ 0}

instance : Countable (RatCone Q₀) :=
  inferInstanceAs (Countable {η : Fin n → F // qF Q₀ η = 0 ∧ η ≠ 0})

/-- A matrix of $\mathrm{SO}(V)(F)$ is invertible, so it sends nonzero vectors to nonzero vectors. -/
theorem ratMat_mulVec_ne_zero (γ : soSub QF F) {ξ : Fin n → F} (hξ : ξ ≠ 0) : ratMat Q₀ γ *ᵥ ξ ≠ 0 := by
  intro h
  apply hξ
  have hdet : (ratMat Q₀ γ).det ≠ 0 := by
    have := (Matrix.isUnits_det_units ((γ : orthGroup QF F) : GL (Fin n) F)).ne_zero
    exact this
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet h

/-- **$\Gamma = \mathrm{SO}(V)(F)$ acts on the punctured cone** by matrices:
$\gamma\cdot\eta = (\text{matrix of }\gamma)\,\eta$. -/
instance instMulActionRatCone : MulAction (GammaSOAdele Q₀) (RatCone Q₀) where
  smul γ η := ⟨ratMat Q₀ ((gammaEquiv Q₀).symm γ) *ᵥ η.1,
    by rw [qF_ratMat_mulVec]; exact η.2.1, ratMat_mulVec_ne_zero Q₀ _ η.2.2⟩
  one_smul η := Subtype.ext (by
    show ratMat Q₀ ((gammaEquiv Q₀).symm 1) *ᵥ η.1 = η.1
    rw [map_one]
    show ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ η.1 = η.1
    rw [Units.val_one, Matrix.one_mulVec])
  mul_smul γ δ η := Subtype.ext (by
    show ratMat Q₀ ((gammaEquiv Q₀).symm (γ * δ)) *ᵥ η.1 =
      ratMat Q₀ ((gammaEquiv Q₀).symm γ) *ᵥ (ratMat Q₀ ((gammaEquiv Q₀).symm δ) *ᵥ η.1)
    rw [map_mul, Matrix.mulVec_mulVec]; rfl)

/-- The underlying vector of $\gamma\cdot\eta$ is the matrix of $\gamma$ applied to $\eta$. -/
theorem ratCone_smul_val (γ : GammaSOAdele Q₀) (η : RatCone Q₀) :
    (γ • η).1 = ratMat Q₀ ((gammaEquiv Q₀).symm γ) *ᵥ η.1 := rfl

/-- **The diagonal embedding is equivariant**: $j(\gamma\eta) = \gamma\cdot j(\eta)$. -/
theorem diagVec_smul_ratCone (γ : GammaSOAdele Q₀) (η : RatCone Q₀) :
    diagVec F (Fin n) (γ • η).1 = (γ : SOAdele Q₀) • diagVec F (Fin n) η.1 := by
  rw [ratCone_smul_val, coe_eq_diagSOAdele_symm, diagSOAdele_smul_diagVec]

/-- **Witt's theorem for $\mathrm{SO}(V)(F)$ on the punctured cone** (O'Meara 42:17 for $\mathrm{SO}$, isotropic
vectors): for $Q$ nondegenerate and $n\ge3$, $\mathrm{SO}(V)(F)$ is transitive on
$\{\eta\in F^n : Q(\eta)=0,\ \eta\ne0\}$. -/
@[kb "omeara1963" "§42F, 42:17, p. 98 (Witt's theorem for SO(V)); isotropic vectors"]
theorem exists_smul_eq_ratCone (hQ : Q₀.Nondegenerate) (hn : 3 ≤ n) (η η' : RatCone Q₀) :
    ∃ γ : GammaSOAdele Q₀, γ • η = η' := by
  set H := (QF).hessian
  have hH : Hᵀ = H := hessian_transpose Q₀
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hdet : H.det ≠ 0 := by
    rw [show H = Q₀.hessian.map (algebraMap (𝓞 F) F) from QuadFormsKB.Siegel.Kneser.hessian_map _ _,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hQ ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective (𝓞 F) F) _ h)
  have hq : ∀ ξ : RatCone Q₀, qH H ξ.1 = 0 := fun ξ => by rw [qH_hessian, ξ.2.1, mul_zero]
  obtain ⟨g, hgo, hgd, hg⟩ := exists_SO_mulVec_eq_isotropic hH h2 hdet hn η.2.2 η'.2.2 (hq η) (hq η')
  have hu : IsUnit g.det := by rw [hgd]; exact isUnit_one
  let gGL : GL (Fin n) F := Matrix.nonsingInvUnit g hu
  have hgGL : gGL.val = g := rfl
  have hmemO : gGL ∈ orthGroup QF F := by
    rw [mem_orthGroup, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, hgGL]; exact hgo
  let γ₀ : soSub QF F := ⟨⟨gGL, hmemO⟩, by rw [mem_soSub]; exact hgd⟩
  refine ⟨gammaEquiv Q₀ γ₀, Subtype.ext ?_⟩
  rw [ratCone_smul_val, MulEquiv.symm_apply_apply]
  exact hg

open Classical in
/-- The indicator sum over the punctured cone $\{Q = 0,\ \eta\ne0\}$ is the sum over `RatCone Q₀`. -/
theorem tsum_ite_eq_tsum_ratCone (f : (Fin n → F) → ℝ≥0∞) :
    ∑' η : Fin n → F, (if qF Q₀ η = 0 ∧ η ≠ 0 then f η else 0) = ∑' η : RatCone Q₀, f η.1 := by
  rw [show (fun η => if qF Q₀ η = 0 ∧ η ≠ 0 then f η else 0) =
      {η | qF Q₀ η = 0 ∧ η ≠ 0}.indicator f from funext fun η => by simp [Set.indicator_apply]]
  exact (tsum_subtype {η | qF Q₀ η = 0 ∧ η ≠ 0} f).symm

end NumberField

end

end QuadFormsKB.Tamagawa.Measure.Weil
