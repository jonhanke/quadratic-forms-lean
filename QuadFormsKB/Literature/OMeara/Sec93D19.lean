/-
# O'Meara §93D, Proposition 93:19: changing $A(\alpha, \beta)$ by an element of the norm group

**Setting** as in `Sec93D18Q.lean`: $R$ a Henselian discrete valuation ring with finite residue field, fraction field
$F$ of characteristic $0$ satisfying the Hilbert-symbol axioms `PadicClass.LocalHilbertField`, $F$ dyadic.
$A(\alpha, \beta)$ ($\alpha, \beta \in \mathfrak o$, $-1 + \alpha\beta \in \mathfrak u$) is the unimodular binary
matrix $\begin{pmatrix}\alpha & 1 \\ 1 & \beta\end{pmatrix}$ (93.r34).

**Page image read** (O'Meara 1973 printing, p. 262): "93:19. Let $L$ be a modular lattice in a quadratic space over a
dyadic local field with $\mathfrak sL \subseteq \mathfrak p$ and $\dim L \ge 3$. Consider any $\lambda \in \mathfrak
gL$. Then $\langle A(\alpha, \beta)\rangle \perp L \cong \langle A(\alpha + \lambda, \beta)\rangle \perp K$ with
$\mathfrak gL \subseteq \mathfrak gK$. Proof. Put $\mathfrak sL = \xi\mathfrak o$ with $\xi \in \dot F$. Then by
Examples 93:13 and 93:18 (v) we have $\langle A(\alpha,\beta)\rangle \perp \langle\xi A(0,0)\rangle \perp L \cong
\langle A(\alpha,\beta)\rangle \perp \langle\xi A(\xi^{-1}\lambda, 0)\rangle \perp L \cong \langle A(\alpha + \lambda,
\beta)\rangle \perp \langle\xi A(\ldots)\rangle \perp L \cong \langle A(\alpha + \lambda, \beta)\rangle \perp
\langle\xi A(0,0)\rangle \perp K$. We have $\mathfrak gL \subseteq 2\xi\mathfrak o + \mathfrak gK = \mathfrak gK$ and,
by Theorem 93:14, $\langle A(\alpha,\beta)\rangle \perp L \cong \langle A(\alpha + \lambda, \beta)\rangle \perp K$."
(Both inclusion signs are O'Meara's double-barred $\subseteq$.)

**Proves**
* `hypForm`: the plane $\xi A(0,0)$ as the form $2\xi st$ on $F^2$;
* `span_pair_isModular`: two vectors with matrix $\xi U$, $\det U$ a unit, span a $\xi\mathfrak o$-modular plane;
* `exists_pair_of_isometricLat`: an isometry carries a binary lattice $\mathfrak ox + \mathfrak oy$ to one with a
  base of the same matrix;
* `omeara93_19` (**93:19**), with the conclusion inside the given lattice: $\langle A(\alpha,\beta)\rangle \perp L =
  (\mathfrak ox' + \mathfrak oy') \perp K$ with $\mathfrak ox' + \mathfrak oy' \cong A(\alpha + \lambda, \beta)$ and
  $\mathfrak gL \subseteq \mathfrak gK$.

The proof is O'Meara's: the adjunction of $\xi A(0,0)$ is the lattice $M \times H$ in $V \times F^2$ with the form
$Q \perp 2\xi st$ (`QuadraticMap.prod`, as in `Sec93Adj.lean`); 93:13 is `exists_isOrthSum_matA`, the middle
isometry is an explicit change of base, 93:18 (v) is `omeara93_18_v` for the form $\xi^{-1}Q$, and 93:14 is
`adj_cancel_plane`. The isometry $\langle A(\alpha,\beta)\rangle \perp L \cong \langle A(\alpha+\lambda,\beta)\rangle
\perp K$ is then transported back into $V$ (`adj_transport`).
-/
import QuadFormsKB.Literature.OMeara.Sec93D18Five
import QuadFormsKB.Literature.OMeara.Sec92Class

open QuadraticMap Submodule Module IsLocalRing QuadFormsKB.PadicClass
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.D18

section Helpers

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- The hyperbolic plane $\xi A(0,0)$: the quadratic form $Q(s, t) = 2\xi st$ on $F^2$. -/
def hypForm (ξ : F) : QuadraticForm F (F × F) :=
  (2 * ξ) • QuadraticMap.linMulLin (LinearMap.fst F F F) (LinearMap.snd F F F)

theorem hypForm_apply (ξ : F) (w : F × F) : hypForm ξ w = 2 * ξ * (w.1 * w.2) := by
  simp [hypForm, QuadraticMap.linMulLin_apply]

theorem bil_hypForm (ξ : F) : bil (hypForm ξ) ((1 : F), (0 : F)) ((0 : F), (1 : F)) = ξ := by
  apply adj_eq_bil_of
  simp only [hypForm_apply, Prod.mk_add_mk]
  ring

/-- **Two vectors with matrix $\xi U$, $\det U \in \mathfrak u$, span a $\xi\mathfrak o$-modular plane.** -/
theorem span_pair_isModular {x y : V} {ξ : F} (hξ : ξ ≠ 0) {p q e : R} (hdet : IsUnit (p * q - e * e))
    (hQx : Q x = ξ * algebraMap R F p) (hQy : Q y = ξ * algebraMap R F q)
    (hxy : bil Q x y = ξ * algebraMap R F e) :
    IsModular Q (R ∙ ξ) (span R {x, y}) ∧ finrank R (span R {x, y}) = 2 := by
  let v : Fin 2 → V := ![x, y]
  let U : Matrix (Fin 2) (Fin 2) R := !![p, e; e, q]
  have hG : gram Q v = ξ • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, hQx, hQy, hxy, bil_comm Q y x]
  have hU : IsUnit U.det := by rw [Matrix.det_fin_two_of]; exact hdet
  obtain ⟨hmod, hrk⟩ := isModular_span_of_gram Q hξ hU hG
  have hv : Set.range v = {x, y} := by ext w; simp [v, eq_comm, or_comm]
  rw [hv] at hmod hrk
  exact ⟨hmod, by simpa using hrk⟩

/-- **An isometry carries a binary lattice $\mathfrak ox + \mathfrak oy$ to a lattice $\mathfrak ox' + \mathfrak oy'$
with the same matrix.** -/
theorem exists_pair_of_isometricLat {J : Submodule R V} {J' : Submodule R V'} (h : IsometricLat Q Q' J J')
    {x y : V} (hJ : J = span R {x, y}) :
    ∃ x' y' : V', J' = span R {x', y'} ∧ Q' x' = Q x ∧ Q' y' = Q y ∧ bil Q' x' y' = bil Q x y := by
  obtain ⟨f, hf⟩ := h
  have hxJ : x ∈ J := hJ ▸ subset_span (by simp)
  have hyJ : y ∈ J := hJ ▸ subset_span (by simp)
  refine ⟨f ⟨x, hxJ⟩, f ⟨y, hyJ⟩, ?_, hf _, hf _, bil_eq_of_isometricLat Q Q' f hf _ _⟩
  apply le_antisymm
  · intro w hw
    obtain ⟨p, hp⟩ := f.surjective ⟨w, hw⟩
    have hpv : (f p : V') = w := congrArg Subtype.val hp
    rw [← hpv]
    have hpJ : (p : V) ∈ span R {x, y} := hJ ▸ p.2
    obtain ⟨a, b, hab⟩ := mem_span_pair.mp hpJ
    have : p = a • (⟨x, hxJ⟩ : J) + b • (⟨y, hyJ⟩ : J) := Subtype.ext (by simpa using hab.symm)
    rw [this, map_add, map_smul, map_smul]
    exact add_mem (smul_mem _ _ (subset_span (by simp))) (smul_mem _ _ (subset_span (by simp)))
  · rw [span_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact (f _).2
    · exact (f _).2

/-- Modularity is invariant under isometries of lattices. -/
theorem isModular_of_isometricLat {a : Submodule R F} {L : Submodule R V} {K : Submodule R V'}
    (h : IsometricLat Q Q' L K) (hL : IsModular Q a L) : IsModular Q' a K := by
  obtain ⟨f, hf⟩ := h
  have hK : imgLat f L = K := imgLat_top f
  refine ⟨hL.1, ?_, ?_⟩
  · rw [← hK, scale_imgLat Q Q' f hf le_rfl, hL.2.1]
  · rw [← hK, volume_imgLat Q Q' f hf le_rfl, finrank_imgLat f le_rfl, hL.2.2]

/-- $(\operatorname{span}\{a, b\}) \times 0 = \operatorname{span}\{(a, 0), (b, 0)\}$. -/
theorem span_pair_prod_bot (a b : V) :
    (span R {a, b}).prod (⊥ : Submodule R V') = span R {((a, (0 : V')) : V × V'), (b, (0 : V'))} := by
  ext ⟨v, w⟩
  simp only [mem_prod, mem_bot, mem_span_pair]
  constructor
  · rintro ⟨⟨c, d, h⟩, rfl⟩
    exact ⟨c, d, by rw [← h]; ext <;> simp⟩
  · rintro ⟨c, d, h⟩
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp at h1 h2
    exact ⟨⟨c, d, h1⟩, h2.symm⟩

/-- $0 \times \operatorname{span}\{a, b\} = \operatorname{span}\{(0, a), (0, b)\}$. -/
theorem bot_prod_span_pair (a b : V') :
    (⊥ : Submodule R V).prod (span R {a, b}) = span R {(((0 : V), a) : V × V'), ((0 : V), b)} := by
  ext ⟨v, w⟩
  simp only [mem_prod, mem_bot, mem_span_pair]
  constructor
  · rintro ⟨rfl, ⟨c, d, h⟩⟩
    exact ⟨c, d, by rw [← h]; ext <;> simp⟩
  · rintro ⟨c, d, h⟩
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp at h1 h2
    exact ⟨h1.symm, ⟨c, d, h2⟩⟩

/-- From $M = J \perp L$: $M \times T = (J \times 0) \perp (L \times T)$. -/
theorem isOrthSum_prod_mix {M J L : Submodule R V} (h : IsOrthSum Q M J L) (T : Submodule R V') :
    IsOrthSum (Q.prod Q') (M.prod T) (J.prod ⊥) (L.prod T) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, -⟩
    obtain rfl : b = 0 := (mem_bot R).mp hb
    rw [adj_bil_prod, h.orth a ha c hc]
    simp [bil]
  · rw [Submodule.disjoint_def]
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨hc, -⟩
    obtain rfl : b = 0 := (mem_bot R).mp hb
    have : a = 0 := Submodule.disjoint_def.mp h.disjoint a ha hc
    simp [this]
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro ⟨a, b⟩ ⟨ha, hb⟩
        exact ⟨h.sup_eq ▸ mem_sup_left ha, (mem_bot R).mp hb ▸ zero_mem _⟩
      · rintro ⟨a, b⟩ ⟨ha, hb⟩
        exact ⟨h.sup_eq ▸ mem_sup_right ha, hb⟩
    · rintro ⟨m, t⟩ ⟨hm, ht⟩
      rw [← h.sup_eq] at hm
      obtain ⟨j, hj, l, hl, rfl⟩ := mem_sup.mp hm
      have : ((j + l, t) : V × V') = (j, 0) + (l, t) := by ext <;> simp
      rw [this]
      exact add_mem (mem_sup_left ⟨hj, zero_mem _⟩) (mem_sup_right ⟨hl, ht⟩)

end Helpers

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Proposition 93:19** (O'Meara 1963, §93D, p. 262). Let $M = J \perp L$ be a lattice over a dyadic local field,
where $J = \mathfrak ox + \mathfrak oy \cong A(\alpha, \beta)$ ($Q(x) = \alpha$, $B(x, y) = 1$, $Q(y) = \beta$ with
$\alpha, \beta \in \mathfrak o$, $-1 + \alpha\beta \in \mathfrak u$) and $L$ is an $\mathfrak a$-modular lattice with
$\mathfrak sL = \mathfrak a \subseteq \mathfrak p$ and $\dim L \ge 3$. For every $\lambda \in \mathfrak gL$,
$M = (\mathfrak ox' + \mathfrak oy') \perp K$ with $Q(x') = \alpha + \lambda$, $B(x', y') = 1$, $Q(y') = \beta$ (so
$\mathfrak ox' + \mathfrak oy' \cong A(\alpha + \lambda, \beta)$) and $\mathfrak gL \subseteq \mathfrak gK$.

*Form of the statement.* O'Meara's "$\langle A(\alpha,\beta)\rangle \perp L \cong \langle A(\alpha + \lambda,
\beta)\rangle \perp K$" is stated inside the lattice $M = \langle A(\alpha,\beta)\rangle \perp L$ itself (an isometry
onto $M$ carries a splitting $A(\alpha+\lambda,\beta) \perp K$ to such a splitting of $M$, and conversely); $\lambda$ is
`γ`; "$\mathfrak sL \subseteq \mathfrak p$" is `a ≤ 𝔭` with $\mathfrak p$ the maximal ideal as an $R$-submodule of $F$.
The local field is abstract, as in `omeara93_18_iii`. -/
@[kb "omeara1963" "§93D, 93:19, p. 262"]
theorem omeara93_19 (hK : LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {M J L : Submodule R V}
    (hM : IsOrthSum Q M J L) {x y : V} (hJ : J = span R {x, y}) {α β : R}
    (hQx : Q x = algebraMap R F α) (hxy : bil Q x y = 1) (hQy : Q y = algebraMap R F β)
    (hαβ : IsUnit (-1 + α * β)) (hLfg : L.FG) {a : Submodule R F} (hL : IsModular Q a L)
    (ha : a ≤ Submodule.map (Algebra.linearMap R F) (maximalIdeal R)) (hrk : 3 ≤ finrank R L)
    {γ : F} (hγ : γ ∈ normGroup Q L) :
    ∃ x' y' : V, ∃ K : Submodule R V, Q x' = algebraMap R F α + γ ∧ bil Q x' y' = 1 ∧
      Q y' = algebraMap R F β ∧ IsOrthSum Q M (span R {x', y'}) K ∧ normGroup Q L ≤ normGroup Q K := by
  -- `𝔰L = ξ𝔬` with `ξ = ξ₀ ∈ 𝔭`
  obtain ⟨ξ, hξ0, rfl⟩ := exists_eq_span_singleton (R := R) (hL.2.1 ▸ scale_fg Q hLfg) hL.1
  obtain ⟨ξ₀, hξ₀m, hξ₀⟩ := Submodule.mem_map.mp (ha (mem_span_singleton_self ξ))
  rw [Algebra.linearMap_apply] at hξ₀
  subst hξ₀
  have hsc : scale Q L = R ∙ algebraMap R F ξ₀ := hL.2.1
  -- `λ = Q(z) + 2c = ξ₀ℓ`
  obtain ⟨z, hzL, c, hc, rfl⟩ := hγ
  have hγs : Q z + 2 * c ∈ R ∙ algebraMap R F ξ₀ := by
    rw [← hsc]
    exact add_mem (normIdeal_le_scale Q L (Q_mem_normIdeal Q hzL)) (by rw [two_mul]; exact add_mem hc hc)
  obtain ⟨ℓ, hℓ⟩ := mem_span_singleton.mp hγs
  rw [Algebra.smul_def] at hℓ
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : R, μ₀ = ξ₀ * ℓ := ⟨_, rfl⟩
  have hmuF : algebraMap R F μ₀ = Q z + 2 * c := by rw [hμ₀, map_mul, ← hℓ]; ring
  have hμ₀F : algebraMap R F μ₀ = algebraMap R F ξ₀ * algebraMap R F ℓ := by rw [hμ₀, map_mul]
  have hmum : μ₀ ∈ maximalIdeal R := by rw [hμ₀]; exact Ideal.mul_mem_right _ _ hξ₀m
  -- `w = (1 - αβ)⁻¹`
  have h1ab : IsUnit (1 - α * β) := by
    have := hαβ.neg
    rwa [show -(-1 + α * β) = 1 - α * β by ring] at this
  obtain ⟨w, hw⟩ := h1ab.exists_left_inv
  have hwF : algebraMap R F w * (1 - algebraMap R F α * algebraMap R F β) = 1 := by
    have := congrArg (algebraMap R F) hw
    simpa only [map_mul, map_sub, map_one] using this
  -- the space `V × F²` with `Q ⊥ ξA(0,0)`
  set ξ : F := algebraMap R F ξ₀ with hξ
  set H : Submodule R (F × F) := span R {((1 : F), (0 : F)), ((0 : F), (1 : F))} with hHd
  set Q₂ : QuadraticForm F (V × (F × F)) := Q.prod (hypForm ξ) with hQ₂
  have hQ₂a : ∀ v t, Q₂ (v, t) = Q v + hypForm ξ t := fun v t => rfl
  have hb₂ : ∀ v v' t t', bil Q₂ (v, t) (v', t') = bil Q v v' + bil (hypForm ξ) t t' := fun v v' t t' =>
    adj_bil_prod Q (hypForm ξ) v v' t t'
  set E₁ : V × (F × F) := (0, ((1 : F), (0 : F))) with hE₁
  set E₂ : V × (F × F) := (0, ((0 : F), (1 : F))) with hE₂
  set X : V × (F × F) := (x, 0) with hX
  set Y : V × (F × F) := (y, 0) with hY
  have hQE₁ : Q₂ E₁ = 0 := by rw [hE₁, hQ₂a, hypForm_apply]; simp
  have hQE₂ : Q₂ E₂ = 0 := by rw [hE₂, hQ₂a, hypForm_apply]; simp
  have hE₁E₂ : bil Q₂ E₁ E₂ = ξ := by rw [hE₁, hE₂, hb₂, bil_hypForm]; simp [bil]
  have hQX : Q₂ X = algebraMap R F α := by rw [hX, hQ₂a, hQx]; simp
  have hQY : Q₂ Y = algebraMap R F β := by rw [hY, hQ₂a, hQy]; simp
  have hXY : bil Q₂ X Y = 1 := by rw [hX, hY, hb₂, hxy]; simp [bil]
  have hYX : bil Q₂ Y X = 1 := by rw [bil_comm]; exact hXY
  have hXX : bil Q₂ X X = algebraMap R F α := by rw [bil_self, hQX]
  have hYY : bil Q₂ Y Y = algebraMap R F β := by rw [bil_self, hQY]
  -- the splittings `M × H = (M × 0) ⊥ (0 × H) = (J × 0) ⊥ (L × H)` and `L × H = (0 × H) ⊥ (L × 0)`
  have hMH := adj_isOrthSum_prod_split Q (hypForm ξ) M H
  have hPs := adj_isOrthSum_symm Q₂ (adj_isOrthSum_prod_split Q (hypForm ξ) L H)
  have hH0 : (⊥ : Submodule R V).prod H = span R {E₁, E₂} := bot_prod_span_pair _ _
  have hJ0 : J.prod (⊥ : Submodule R (F × F)) = span R {X, Y} := by rw [hJ]; exact span_pair_prod_bot _ _
  have hmix := isOrthSum_prod_mix Q (hypForm ξ) hM H
  -- 93:13: `(0 × H) ⊥ (L × 0) = H₁ ⊥ L₁` with `H₁ ≅ ξA(ξ⁻¹λ, 0)` and `L₁ ≅ L`
  have hLiso : IsometricLat Q Q₂ L (L.prod ⊥) := adj_isometricLat_prod_bot Q (hypForm ξ) L
  have hsc0 : scale Q₂ (L.prod ⊥) = R ∙ ξ :=
    le_antisymm (hsc ▸ adj_scale_le Q₂ Q (adj_isometricLat_symm Q Q₂ hLiso)) (hsc ▸ adj_scale_le Q Q₂ hLiso)
  have hsub := adj_le_subA Q₂ hsc0.le
  have hz₀ : ((z, 0) : V × (F × F)) ∈ L.prod ⊥ := ⟨hzL, zero_mem _⟩
  have hc₀ : c ∈ scale Q₂ (subA Q₂ (R ∙ ξ) (L.prod ⊥)) := scale_mono Q₂ hsub (hsc0 ▸ hsc ▸ hc)
  obtain ⟨x₁, y₁, α', hα', hQx₁, hx₁y₁, hQy₁, hs1, hiso1⟩ :=
    exists_isOrthSum_matA Q₂ hPs hξ0 (α := 0) hH0 (by rw [hQE₁, map_zero, mul_zero]) hE₁E₂ hQE₂
      (hsub hz₀) hc₀
  have hQz : Q₂ (z, 0) = Q z := by rw [hQ₂a]; simp
  have hQx₁' : Q₂ x₁ = algebraMap R F μ₀ := by
    rw [hQx₁, hα', map_zero, zero_add, hQz, hmuF]; field_simp
  have hy₁x₁ : bil Q₂ y₁ x₁ = ξ := by rw [bil_comm]; exact hx₁y₁
  have hx₁x₁ : bil Q₂ x₁ x₁ = algebraMap R F μ₀ := by rw [bil_self, hQx₁']
  have hy₁y₁ : bil Q₂ y₁ y₁ = 0 := by rw [bil_self, hQy₁]
  obtain ⟨hA, -⟩ := adj_isOrthSum_assoc_left Q₂ hmix hs1
  have hXJ : X ∈ J.prod ⊥ := hJ0 ▸ subset_span (by simp)
  have hYJ : Y ∈ J.prod ⊥ := hJ0 ▸ subset_span (by simp)
  have hx₁H : x₁ ∈ span R {x₁, y₁} := subset_span (by simp)
  have hy₁H : y₁ ∈ span R {x₁, y₁} := subset_span (by simp)
  have hx₁P : x₁ ∈ L.prod H := hs1.sup_eq ▸ mem_sup_left hx₁H
  have hy₁P : y₁ ∈ L.prod H := hs1.sup_eq ▸ mem_sup_left hy₁H
  have o1 : bil Q₂ X x₁ = 0 := hmix.orth X hXJ x₁ hx₁P
  have o2 : bil Q₂ X y₁ = 0 := hmix.orth X hXJ y₁ hy₁P
  have o3 : bil Q₂ Y x₁ = 0 := hmix.orth Y hYJ x₁ hx₁P
  have o4 : bil Q₂ Y y₁ = 0 := hmix.orth Y hYJ y₁ hy₁P
  have o1' : bil Q₂ x₁ X = 0 := by rw [bil_comm]; exact o1
  have o2' : bil Q₂ y₁ X = 0 := by rw [bil_comm]; exact o2
  have o3' : bil Q₂ x₁ Y = 0 := by rw [bil_comm]; exact o3
  have o4' : bil Q₂ y₁ Y = 0 := by rw [bil_comm]; exact o4
  -- the change of base `J ⊥ H₁ = J' ⊥ H₂`, `J' = 𝔬x' + 𝔬Y ≅ A(α + λ, β)`
  obtain ⟨x', hx'd⟩ : ∃ x' : V × (F × F), x' = X + x₁ := ⟨_, rfl⟩
  obtain ⟨u, hud⟩ : ∃ u : V × (F × F), u = x₁ + (β * (μ₀ * w)) • X + (-(μ₀ * w)) • Y := ⟨_, rfl⟩
  obtain ⟨v, hvd⟩ : ∃ v : V × (F × F), v = y₁ + (β * (ξ₀ * w)) • X + (-(ξ₀ * w)) • Y := ⟨_, rfl⟩
  have hQx' : Q₂ x' = algebraMap R F α + (Q z + 2 * c) := by
    rw [hx'd, Q_add, o1, hQX, hQx₁', hmuF]; ring
  have hx'Y : bil Q₂ x' Y = 1 := by rw [hx'd, bil_add_left, hXY, o3']; ring
  have v1 : bil Q₂ u x' = 0 := by
    rw [hud, hx'd]
    simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, hXX, hYY, hx₁x₁, hy₁y₁, hQX, hQY, hXY, hYX,
      o1, o2, o3, o4, o1', o2', o3', o4', hQx₁', map_neg, map_mul]
    linear_combination (-(algebraMap R F μ₀)) * hwF
  have v2 : bil Q₂ u Y = 0 := by
    rw [hud]
    simp only [bil_add_left, bil_rsmul_left, hYY, hQY, hXY, o3', map_neg, map_mul]
    ring
  have v3 : bil Q₂ v x' = 0 := by
    rw [hvd, hx'd]
    simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, hXX, hYY, hx₁x₁, hy₁y₁, hQX, hQY, hXY, hYX,
      o1, o2, o3, o4, o1', o2', o3', o4', hy₁x₁, map_neg, map_mul]
    linear_combination (-(algebraMap R F ξ₀)) * hwF
  have v4 : bil Q₂ v Y = 0 := by
    rw [hvd]
    simp only [bil_add_left, bil_rsmul_left, hYY, hQY, hXY, o4', map_neg, map_mul]
    ring
  have hQu : Q₂ u = ξ * algebraMap R F (ℓ * (1 - μ₀ * w * β)) := by
    rw [← bil_self, hud]
    simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, hXX, hYY, hx₁x₁, hy₁y₁, hQX, hQY, hXY, hYX,
      o1, o2, o3, o4, o1', o2', o3', o4', hQx₁', map_neg, map_mul, map_sub, map_one, hξ]
    linear_combination (1 - algebraMap R F μ₀ * algebraMap R F w * algebraMap R F β) * hμ₀F +
      (-(algebraMap R F μ₀ ^ 2 * algebraMap R F w * algebraMap R F β)) * hwF
  have huv : bil Q₂ u v = ξ * algebraMap R F (1 - μ₀ * w * β) := by
    rw [hud, hvd]
    simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, hXX, hYY, hx₁x₁, hy₁y₁, hQX, hQY, hXY, hYX,
      o1, o2, o3, o4, o1', o2', o3', o4', hx₁y₁, hQy₁, map_neg, map_mul, map_sub, map_one, hξ]
    linear_combination (-(algebraMap R F μ₀ * algebraMap R F ξ₀ * algebraMap R F w * algebraMap R F β)) * hwF
  have hQv : Q₂ v = ξ * algebraMap R F (-(ξ₀ * w * β)) := by
    rw [← bil_self, hvd]
    simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, hXX, hYY, hx₁x₁, hy₁y₁, hQX, hQY, hXY, hYX,
      o1, o2, o3, o4, o1', o2', o3', o4', hQy₁, map_neg, map_mul, hξ]
    linear_combination (-(algebraMap R F ξ₀ ^ 2 * algebraMap R F w * algebraMap R F β)) * hwF
  -- `J'` is unimodular, `H₂` is `ξ`-modular
  have hwmb : w * μ₀ * β ∈ maximalIdeal R := Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmum)
  have hdetJ : IsUnit ((α + μ₀) * β - 1 * 1) := by
    have : (α + μ₀) * β - 1 * 1 = -((1 - α * β) * (1 + -(w * μ₀ * β))) := by
      linear_combination (-(μ₀ * β)) * hw
    rw [this]
    exact (h1ab.mul (isUnit_one_add_aux (neg_mem hwmb))).neg
  have hJ'mod := span_pair_isModular Q₂ (one_ne_zero : (1 : F) ≠ 0) hdetJ
    (by rw [hQx', one_mul, map_add, hmuF]) (by rw [hQY, one_mul]) (by rw [hx'Y, map_one, one_mul])
  have hdetH : IsUnit (ℓ * (1 - μ₀ * w * β) * -(ξ₀ * w * β) - (1 - μ₀ * w * β) * (1 - μ₀ * w * β)) := by
    have : ℓ * (1 - μ₀ * w * β) * -(ξ₀ * w * β) - (1 - μ₀ * w * β) * (1 - μ₀ * w * β) =
        -(1 + -(w * μ₀ * β)) := by
      linear_combination ((1 - μ₀ * w * β) * w * β) * hμ₀
    rw [this]
    exact (isUnit_one_add_aux (neg_mem hwmb)).neg
  have hH₂mod := span_pair_isModular Q₂ hξ0 hdetH hQu hQv huv
  set J' := span R {x', Y} with hJ'd
  set H₂ := span R {u, v} with hH₂d
  -- `J × 0 ⊔ H₁ = J' ⊥ H₂`
  have hJ'reg : IsRegular Q₂ J' := IsModular.isRegular Q₂ hJ'mod.1 (fg_span (Set.toFinite _))
  have orthAB : ∀ p ∈ J', ∀ q ∈ H₂, bil Q₂ p q = 0 := by
    intro p hp q hq
    rw [bil_comm]
    refine Uni93.bil_zero_on_span Q₂ (S := {x', Y}) ?_ p hp
    intro r hr
    rw [bil_comm]
    refine Uni93.bil_zero_on_span Q₂ (S := {u, v}) ?_ q hq
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr hs
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> rw [bil_comm]
    · exact v1
    · exact v3
    · exact v2
    · exact v4
  have hx'mem : x' ∈ J' := subset_span (by simp)
  have hYmem : Y ∈ J' := subset_span (by simp)
  have humem : u ∈ H₂ := subset_span (by simp)
  have hvmem : v ∈ H₂ := subset_span (by simp)
  have hc₁ : β * (μ₀ * w) ∈ maximalIdeal R := Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hmum)
  obtain ⟨e, he⟩ := (isUnit_one_add_aux (neg_mem hc₁)).exists_left_inv
  have hXmem : X ∈ J' ⊔ H₂ := by
    have key : X = e • (x' - u - (μ₀ * w) • Y) := by
      have h1 : x' - u - (μ₀ * w) • Y = (1 + -(β * (μ₀ * w))) • X := by rw [hx'd, hud]; module
      rw [h1, smul_smul, he, one_smul]
    rw [key]
    exact smul_mem _ _ (sub_mem (sub_mem (mem_sup_left hx'mem) (mem_sup_right humem))
      (smul_mem _ _ (mem_sup_left hYmem)))
  have hClaimA : IsOrthSum Q₂ (J.prod ⊥ ⊔ span R {x₁, y₁}) J' H₂ := by
    refine ⟨orthAB, ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro p hp hq
      exact hJ'reg p hp fun j hj => by rw [bil_comm]; exact orthAB j hj p hq
    · apply le_antisymm
      · refine sup_le ?_ ?_
        · rw [hJ'd, span_le]
          intro r hr
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
          rcases hr with rfl | rfl
          · rw [hx'd]; exact add_mem (mem_sup_left hXJ) (mem_sup_right hx₁H)
          · exact mem_sup_left hYJ
        · rw [hH₂d, span_le]
          intro r hr
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
          rcases hr with rfl | rfl
          · rw [hud]
            exact add_mem (add_mem (mem_sup_right hx₁H) (smul_mem _ _ (mem_sup_left hXJ)))
              (smul_mem _ _ (mem_sup_left hYJ))
          · rw [hvd]
            exact add_mem (add_mem (mem_sup_right hy₁H) (smul_mem _ _ (mem_sup_left hXJ)))
              (smul_mem _ _ (mem_sup_left hYJ))
      · refine sup_le ?_ ?_
        · rw [hJ0, span_le]
          intro r hr
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
          rcases hr with rfl | rfl
          · exact hXmem
          · exact mem_sup_left hYmem
        · rw [span_le]
          intro r hr
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
          rcases hr with h | h <;> rw [h]
          · have : x₁ = x' - X := by rw [hx'd]; abel
            rw [this]; exact sub_mem (mem_sup_left hx'mem) hXmem
          · have : y₁ = v + (-(β * (ξ₀ * w))) • X + (ξ₀ * w) • Y := by rw [hvd]; module
            rw [this]
            exact add_mem (add_mem (mem_sup_right hvmem) (smul_mem _ _ hXmem))
              (smul_mem _ _ (mem_sup_left hYmem))
  -- `N = H₂ ⊥ L₁` is `ξ`-modular of rank `≥ 5`
  set L₁ := splitComp Q₂ (L.prod H) (span R {x₁, y₁}) with hL₁d
  have hL₁iso : IsometricLat Q Q₂ L L₁ := adj_isometricLat_trans Q Q₂ Q₂ hLiso hiso1
  have hL₁mod : IsModular Q₂ (R ∙ ξ) L₁ := isModular_of_isometricLat Q Q₂ hL₁iso hL
  have hL₁fg : L₁.FG := by
    obtain ⟨f, -⟩ := hL₁iso
    have : Module.Finite R L := Module.Finite.iff_fg.mpr hLfg
    exact Module.Finite.iff_fg.mp (Module.Finite.equiv f)
  have hL₁rk : finrank R L₁ = finrank R L := by
    obtain ⟨f, -⟩ := hL₁iso
    exact f.finrank_eq.symm
  have hH₂le : H₂ ≤ J.prod ⊥ ⊔ span R {x₁, y₁} := hClaimA.sup_eq ▸ le_sup_right
  have horthN : ∀ p ∈ H₂, ∀ q ∈ L₁, bil Q₂ p q = 0 := fun p hp q hq => hA.orth p (hH₂le hp) q hq
  obtain ⟨hNmod, hNrk⟩ := isModular_sup Q₂ hH₂mod.1 hL₁mod (fg_span (Set.toFinite _)) hL₁fg horthN
  have hNfg : (H₂ ⊔ L₁).FG := (fg_span (Set.toFinite _)).sup hL₁fg
  -- 93:18 (v) for `ξ⁻¹Q₂`: a hyperbolic plane `H₃ ≅ ξA(0,0)` splits `N`
  have hNU : IsUnimodular (ξ⁻¹ • Q₂) (H₂ ⊔ L₁) := isUnimodular_smul_of_isModular Q₂ hξ0 hNfg hNmod
  have hb₃ : ∀ p q, bil (ξ⁻¹ • Q₂) p q = ξ⁻¹ * bil Q₂ p q := bil_smul_form Q₂ ξ⁻¹
  have hQ₃ : ∀ p, (ξ⁻¹ • Q₂) p = ξ⁻¹ * Q₂ p := fun p => rfl
  obtain ⟨x₃, hx₃, y₃, hy₃, h31, h32, h33⟩ := omeara93_18_v (ξ⁻¹ • Q₂) hK h2p hNfg hNU
    (by rw [hNrk, hH₂mod.2, hL₁rk]; omega)
  have hξi : ξ⁻¹ ≠ 0 := inv_ne_zero hξ0
  have hQx₃ : Q₂ x₃ = 0 := by rw [hQ₃] at h31; exact (mul_eq_zero.mp h31).resolve_left hξi
  have hQy₃ : Q₂ y₃ = 0 := by rw [hQ₃] at h32; exact (mul_eq_zero.mp h32).resolve_left hξi
  have hx₃y₃ : bil Q₂ x₃ y₃ = ξ := by
    rw [hb₃] at h33; field_simp at h33; linear_combination h33
  have hH₃mod := span_pair_isModular Q₂ hξ0 (p := (0 : R)) (q := (0 : R)) (e := (1 : R)) (by simp)
    (by rw [hQx₃, map_zero, mul_zero]) (by rw [hQy₃, map_zero, mul_zero]) (by rw [hx₃y₃, map_one, mul_one])
  have hH₃N : span R {x₃, y₃} ≤ H₂ ⊔ L₁ := by
    rw [span_le]
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact hx₃
    · exact hy₃
  obtain ⟨K, hNK⟩ := splits_of_isModular_of_scale_eq Q₂ hH₃N hH₃mod.1 (fg_span (Set.toFinite _)) hNmod.2.1
  have hrkN := isOrthSum_finrank Q₂ hNK hNfg
  have hK0 : K ≠ ⊥ := by
    rintro rfl
    simp at hrkN
    rw [hNrk, hH₂mod.2, hL₁rk, hH₃mod.2] at hrkN
    omega
  have hNK₃ : IsOrthSum (ξ⁻¹ • Q₂) (H₂ ⊔ L₁) (span R {x₃, y₃}) K :=
    ⟨fun p hp q hq => by rw [hb₃, hNK.orth p hp q hq, mul_zero], hNK.disjoint, hNK.sup_eq⟩
  have hH₃U : IsUnimodular (ξ⁻¹ • Q₂) (span R {x₃, y₃}) :=
    isUnimodular_smul_of_isModular Q₂ hξ0 (fg_span (Set.toFinite _)) hH₃mod.1
  have hKU := u93_isUnimodular_of_orth (ξ⁻¹ • Q₂) hNfg hNU hH₃U hNK₃ hK0
  have hKsc : scale Q₂ K = R ∙ ξ := by
    have e1 : Q₂ = ξ • (ξ⁻¹ • Q₂) := by rw [smul_smul, mul_inv_cancel₀ hξ0, one_smul]
    rw [e1, scale_smul_form, hKU.2.1, mul_one]
  -- `𝔤L ⊆ 2ξ𝔬 + 𝔤K = 𝔤K`
  have hH₃K : normGroup Q₂ (span R {x₃, y₃}) ≤ normGroup Q₂ K := by
    rintro _ ⟨p, hp, c', hc', rfl⟩
    obtain ⟨s, t, rfl⟩ := mem_span_pair.mp hp
    rw [hH₃mod.1.2.1] at hc'
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hc'
    have : Q₂ (s • x₃ + t • y₃) + 2 * (r • ξ) = 2 * (algebraMap R F (s * t + r) * ξ) := by
      rw [Q_add, Q_rsmul, Q_rsmul, bil_rsmul_left, bil_rsmul_right, hQx₃, hQy₃, hx₃y₃, Algebra.smul_def]
      simp only [map_add, map_mul]
      ring
    rw [this]
    refine two_mul_mem_normGroup Q₂ ?_
    rw [hKsc, ← Algebra.smul_def]
    exact smul_mem _ _ (mem_span_singleton_self ξ)
  have hgL : normGroup Q L ≤ normGroup Q₂ K := by
    rw [adj_normGroup_eq Q Q₂ hL₁iso]
    calc normGroup Q₂ L₁ ≤ normGroup Q₂ (H₂ ⊔ L₁) := normGroup_mono Q₂ le_sup_right
      _ = normGroup Q₂ (span R {x₃, y₃}) ⊔ normGroup Q₂ K := by
          rw [← hNK.sup_eq, normGroup_sup_of_orth Q₂ hNK.orth]
      _ ≤ normGroup Q₂ K := sup_le hH₃K le_rfl
  -- 93:14: cancel `ξA(0,0)` from `(0 × H) ⊥ (M × 0) = H₃ ⊥ (K ⊥ J')`
  obtain ⟨hMJN, -⟩ := adj_isOrthSum_assoc_right Q₂ hA hClaimA
  obtain ⟨h4, h5⟩ := adj_isOrthSum_assoc_right Q₂ (adj_isOrthSum_symm Q₂ hMJN) hNK
  have hcan := adj_cancel_plane Q₂ hξ0 (adj_isOrthSum_symm Q₂ hMH) h4 hH0 rfl hQE₁ hQE₂ hE₁E₂ hQx₃ hQy₃
    hx₃y₃
  -- transport `K ⊥ J'` back to `M`
  have he : IsometricLat Q₂ Q (K ⊔ J') M := adj_isometricLat_symm Q Q₂
    (adj_isometricLat_trans Q Q₂ Q₂ (adj_isometricLat_prod_bot Q (hypForm ξ) M) hcan)
  obtain ⟨A', B', hAB, hKA, hJB⟩ := adj_transport Q₂ Q he h5
  obtain ⟨x'', y'', hB', hQ1, hQ2, hb⟩ := exists_pair_of_isometricLat Q₂ Q hJB hJ'd
  refine ⟨x'', y'', A', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQ1, hQx']
  · rw [hb, hx'Y]
  · rw [hQ2, hQY]
  · rw [← hB']; exact adj_isOrthSum_symm Q hAB
  · exact hgL.trans (adj_normGroup_eq Q₂ Q hKA).le

end Main

end QuadFormsKB.OMeara.D18
