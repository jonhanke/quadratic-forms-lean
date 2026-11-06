/-
# O'Meara §93D: unimodular lattices over dyadic fields (93:17, 93:18 (ii), 93:20)

Work in progress.
-/
import QuadFormsKB.Literature.OMeara.Sec93Adj
import QuadFormsKB.Literature.OMeara.Sec93EFund
import QuadFormsKB.Literature.OMeara.Sec93Gap3
import QuadFormsKB.Literature.OMeara.Sec93Unimodular
import QuadFormsKB.Literature.OMeara.Sec93Weight
import QuadFormsKB.Literature.OMeara.Sec92SpinorUnits

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace Uni93

section Hyperbolic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [IsFractionRing R F] [Invertible (2 : F)] in
/-- **Hensel for $X^2 + X + c$**: for $c$ in the maximal ideal of a Henselian local ring there is a root $s$ of
$s^2 + s + c = 0$ in the maximal ideal. -/
theorem exists_root_sq_add {c : R} (hc : c ∈ maximalIdeal R) :
    ∃ s ∈ maximalIdeal R, s ^ 2 + s + c = 0 := by
  open Polynomial in
  let f : R[X] := X ^ 2 + X + C c
  have hf : f.Monic := by
    simp only [f]
    monicity!
  have h0 : f.eval 0 ∈ maximalIdeal R := by simpa [f] using hc
  have h1 : IsUnit (f.derivative.eval 0) := by
    simp [f, derivative_X_pow]
  obtain ⟨r, hr, hr0⟩ := HenselianLocalRing.is_henselian f hf 0 h0 h1
  refine ⟨r, by simpa using hr0, ?_⟩
  simpa [f] using hr

theorem two_mem_maximalIdeal (h2p : ¬ IsUnit (2 : R)) : (2 : R) ∈ maximalIdeal R :=
  (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h2p)

/-- **A hyperbolic pair from an "even" pair** (the Hensel step behind O'Meara's 93:11 and 93:18 (ii)): if
$B(x, y) = 1$, $Q(x) = 2\alpha'$, $Q(y) = 2\beta'$ with $\alpha', \beta' \in \mathfrak o$ and $\alpha' \in \mathfrak p$,
then $\mathfrak ox + \mathfrak oy$ contains $x', y'$ with $Q(x') = Q(y') = 0$ and $B(x', y') = 1$. (Solve
$\beta' t^2 + t + \alpha' = 0$ by Hensel and take $x' = x + ty$.) -/
theorem exists_hyperbolic_of_even_pair (h2p : ¬ IsUnit (2 : R)) {x y : V} {α' β' : R}
    (hQx : Q x = 2 * algebraMap R F α') (hQy : Q y = 2 * algebraMap R F β') (hxy : bil Q x y = 1)
    (hα : α' ∈ maximalIdeal R) :
    ∃ x' ∈ span R {x, y}, ∃ y' ∈ span R {x, y}, Q x' = 0 ∧ Q y' = 0 ∧ bil Q x' y' = 1 := by
  obtain ⟨s, hs, hs0⟩ := exists_root_sq_add (c := α' * β') (Ideal.mul_mem_right _ _ hα)
  obtain ⟨u, hu⟩ := (isUnit_one_add_aux hs).exists_right_inv
  set t : R := -(α' * u) with ht_def
  have ht : β' * t ^ 2 + t + α' = 0 := by
    rw [ht_def]
    linear_combination (α' * u ^ 2) * hs0 - (α' * (1 + u * s)) * hu
  have htF : algebraMap R F β' * algebraMap R F t ^ 2 + algebraMap R F t + algebraMap R F α' = 0 := by
    have := congrArg (algebraMap R F) ht
    simpa [map_add, map_mul, map_pow] using this
  set x₁ : V := x + t • y with hx₁
  have hQx₁ : Q x₁ = 0 := by
    rw [hx₁, Q_add, Q_rsmul, bil_rsmul_right, hxy, hQx, hQy]
    linear_combination 2 * htF
  have hD : bil Q x₁ y = algebraMap R F (1 + 2 * t * β') := by
    rw [hx₁, bil_add_left, bil_rsmul_left, hxy, bil_self, hQy]
    simp only [map_add, map_mul, map_one, map_ofNat]
    ring
  have hDu : IsUnit (1 + 2 * t * β') := by
    refine isUnit_one_add_aux ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (two_mem_maximalIdeal h2p))
  obtain ⟨w, hw⟩ := hDu.exists_left_inv
  have hwF : algebraMap R F w * algebraMap R F (1 + 2 * t * β') = 1 := by
    rw [← map_mul, hw, map_one]
  set y' : V := w • y - (w ^ 2 * β') • x₁ with hy'
  have hmem1 : x₁ ∈ span R {x, y} :=
    add_mem (subset_span (by simp)) (smul_mem _ _ (subset_span (by simp)))
  refine ⟨x₁, hmem1, y', sub_mem (smul_mem _ _ (subset_span (by simp))) (smul_mem _ _ hmem1), hQx₁, ?_, ?_⟩
  · rw [hy', sub_eq_add_neg, Q_add, ← neg_smul, Q_rsmul, Q_rsmul, bil_rsmul_left, bil_rsmul_right,
      bil_comm Q y x₁, hD, hQx₁, hQy]
    simp only [map_neg, map_mul, map_pow]
    linear_combination (-(2 * algebraMap R F w ^ 2 * algebraMap R F β')) * hwF
  · rw [hy', sub_eq_add_neg, bil_add_right, ← neg_smul, bil_rsmul_right, bil_rsmul_right, hD, bil_self, hQx₁]
    simp only [map_neg, map_mul, map_pow]
    linear_combination hwF

/-- A unimodular lattice is non-zero. -/
theorem ne_bot_of_isUnimodular {L : Submodule R V} (hU : IsUnimodular Q L) : L ≠ ⊥ := by
  rintro rfl
  have := hU.2.1
  rw [scale_bot] at this
  have h1 : (1 : F) ∈ (1 : Submodule R F) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  rw [← this] at h1
  exact one_ne_zero ((Submodule.mem_bot R).mp h1)

/-- **Core of O'Meara's 93:18 (ii)**. Let $L$ be unimodular with $\mathfrak wL \subseteq 2\mathfrak o$, let
$x, y \in L$ with $B(x,y) = 1$, $Q(y) \in 2\mathfrak o$, and let $z \in L$ be orthogonal to $x$ and $y$ with
$Q(z)\mathfrak o = \mathfrak nL$, such that $t^2 Q(z) = 2\varepsilon$ for some $t \in \mathfrak o$ and unit $\varepsilon$.
Then $L$ contains $x', y'$ with $Q(x') = Q(y') = 0$ and $B(x', y') = 1$. -/
theorem core_hyperbolic (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hw : ∀ w ∈ weight Q L, ∃ c : R, w = 2 * algebraMap R F c)
    {x y z : V} (hx : x ∈ L) (hy : y ∈ L) (hz : z ∈ L) (hxy : bil Q x y = 1) {ζ : R}
    (hQy : Q y = 2 * algebraMap R F ζ) (hzx : bil Q z x = 0) (hzy : bil Q z y = 0)
    (hzn : R ∙ Q z = normIdeal Q L)
    (hm : ∃ t ε : R, IsUnit ε ∧ algebraMap R F t ^ 2 * Q z = 2 * algebraMap R F ε) :
    ∃ x' ∈ L, ∃ y' ∈ L, Q x' = 0 ∧ Q y' = 0 ∧ bil Q x' y' = 1 := by
  have hne := ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha : IsNormGenerator Q L (Q z) := ⟨Q_mem_normGroup Q hz, hzn⟩
  have ha0 := ha.ne_zero Q hreg hne
  obtain ⟨r, hr⟩ := a10_mem_one Q hU hz hz
  rw [bil_self] at hr
  obtain ⟨ξ, hξ⟩ := exists_sub_sq_mem_weight Q h2p ha ha0 (Q_mem_normGroup Q hx)
  obtain ⟨c, hc⟩ := hw _ hξ
  set η' : R := c + ξ ^ 2 * r with hη'
  have hxz : bil Q x z = 0 := by rw [bil_comm]; exact hzx
  have hyz : bil Q y z = 0 := by rw [bil_comm]; exact hzy
  set x' : V := x + (-ξ) • z with hx'
  have hx'L : x' ∈ L := L.add_mem hx (L.smul_mem _ hz)
  have hQx' : Q x' = 2 * algebraMap R F η' := by
    rw [hx', Q_add, Q_rsmul, bil_rsmul_right, hxz, ← hr]
    have : Q x = Q z * algebraMap R F ξ ^ 2 + 2 * algebraMap R F c := by linear_combination hc
    rw [this, hη']
    simp only [map_add, map_mul, map_pow, map_neg, ← hr]
    ring
  have hx'y : bil Q x' y = 1 := by
    rw [hx', bil_add_left, bil_rsmul_left, hxy, hzy]
    simp
  have hx'z : bil Q x' z = -(algebraMap R F ξ * algebraMap R F r) := by
    rw [hx', bil_add_left, bil_rsmul_left, hxz, bil_self, hr]
    simp
  have hyx' : bil Q y x' = 1 := by rw [bil_comm]; exact hx'y
  have hzx' : bil Q z x' = -(algebraMap R F ξ * algebraMap R F r) := by rw [bil_comm]; exact hx'z
  -- the unit `δ = (1 - 4 η' ζ)⁻¹`
  have hD : IsUnit (1 + -(2 * (2 * η' * ζ))) := by
    refine isUnit_one_add_aux (neg_mem ?_)
    exact Ideal.mul_mem_right _ _ (two_mem_maximalIdeal h2p)
  obtain ⟨δ, hδ⟩ := hD.exists_left_inv
  have hδF : algebraMap R F δ * (1 - 4 * algebraMap R F η' * algebraMap R F ζ) = 1 := by
    have := congrArg (algebraMap R F) hδ
    simp only [map_mul, map_add, map_one, map_neg, map_ofNat] at this
    linear_combination this
  set c₁ : R := 2 * ζ * ξ * r * δ with hc₁
  set c₂ : R := -(ξ * r * δ) with hc₂
  set z₀ : V := z + (-c₁) • x' + (-c₂) • y with hz₀
  have hz₀L : z₀ ∈ L := L.add_mem (L.add_mem hz (L.smul_mem _ hx'L)) (L.smul_mem _ hy)
  have hz₀x' : bil Q z₀ x' = 0 := by
    rw [hz₀, bil_add_left, bil_add_left, bil_rsmul_left, bil_rsmul_left, hzx', bil_self, hQx', hyx']
    simp only [hc₁, hc₂, map_neg, map_mul, map_ofNat]
    linear_combination (algebraMap R F ξ * algebraMap R F r) * hδF
  have hz₀y : bil Q z₀ y = 0 := by
    rw [hz₀, bil_add_left, bil_add_left, bil_rsmul_left, bil_rsmul_left, hzy, bil_self, hQy, hx'y]
    simp only [hc₁, hc₂, map_neg, map_mul, map_ofNat]
    ring
  have hQz₀ : Q z₀ = algebraMap R F r + 2 * algebraMap R F ζ * algebraMap R F ξ ^ 2 *
      algebraMap R F r ^ 2 * algebraMap R F δ := by
    rw [hz₀]
    simp only [Q_add, Q_rsmul, bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, hzx', hzy, hx'y,
      hQx', hQy, ← hr, hc₁, hc₂, map_neg, map_mul, map_ofNat]
    linear_combination (-(2 * algebraMap R F ζ * algebraMap R F ξ ^ 2 * algebraMap R F r ^ 2 *
      algebraMap R F δ)) * hδF
  obtain ⟨t, ε, hε, hte⟩ := hm
  set z₂ : V := t • z₀ with hz₂
  have hz₂L : z₂ ∈ L := L.smul_mem t hz₀L
  set ε' : R := ε * (1 + 2 * (ζ * ξ ^ 2 * r * δ)) with hε'
  have hε'u : IsUnit ε' :=
    hε.mul (isUnit_one_add_aux (Ideal.mul_mem_right _ _ (two_mem_maximalIdeal h2p)))
  have hQz₂ : Q z₂ = 2 * algebraMap R F ε' := by
    rw [hz₂, Q_rsmul, hQz₀, hε']
    rw [← hr] at hte
    simp only [map_mul, map_add, map_one, map_ofNat, map_pow]
    linear_combination (1 + 2 * (algebraMap R F ζ * algebraMap R F ξ ^ 2 * algebraMap R F r *
      algebraMap R F δ)) * hte
  have hz₂x' : bil Q z₂ x' = 0 := by rw [hz₂, bil_rsmul_left, hz₀x', mul_zero]
  have hz₂y : bil Q z₂ y = 0 := by rw [hz₂, bil_rsmul_left, hz₀y, mul_zero]
  obtain ⟨e2, he2⟩ := hε'u.exists_right_inv
  obtain ⟨s, hs⟩ := exists_sq_mod h2p (-(η' * e2))
  have hα'' : η' + s ^ 2 * ε' ∈ maximalIdeal R := by
    have : η' + s ^ 2 * ε' = -(ε' * (-(η' * e2) - s ^ 2)) := by
      linear_combination (-η') * he2
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hs)
  set x'' : V := x' + s • z₂ with hx''
  have hx''L : x'' ∈ L := L.add_mem hx'L (L.smul_mem s hz₂L)
  have hx'z₂ : bil Q x' z₂ = 0 := by rw [bil_comm]; exact hz₂x'
  have hQx'' : Q x'' = 2 * algebraMap R F (η' + s ^ 2 * ε') := by
    rw [hx'', Q_add, Q_rsmul, bil_rsmul_right, hx'z₂, hQx', hQz₂]
    simp only [map_add, map_mul, map_pow]
    ring
  have hx''y : bil Q x'' y = 1 := by
    rw [hx'', bil_add_left, bil_rsmul_left, hx'y, hz₂y]
    simp
  obtain ⟨x₃, hx₃, y₃, hy₃, h1, h2, h3⟩ :=
    exists_hyperbolic_of_even_pair Q h2p hQx'' hQy hx''y hα''
  have hsp : span R {x'', y} ≤ L := by
    rw [span_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hx''L
    · exact hy
  exact ⟨x₃, hsp hx₃, y₃, hsp hy₃, h1, h2, h3⟩

end Hyperbolic

section Splitting

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- Orthogonality to a set gives orthogonality to its span. -/
theorem bil_zero_on_span {S : Set V} {z : V} (h : ∀ w ∈ S, bil Q z w = 0) :
    ∀ j ∈ span R S, bil Q z j = 0 := by
  intro j hj
  refine span_induction (p := fun j _ => bil Q z j = 0) h (by simp [bil])
    (fun a b _ _ ha hb => by rw [bil_add_right, ha, hb, add_zero])
    (fun r a _ ha => by rw [bil_rsmul_right, ha, mul_zero]) hj

/-- $K \subseteq L \Rightarrow \mathfrak nK \subseteq \mathfrak nL$. -/
theorem normIdeal_mono' {K L : Submodule R V} (h : K ≤ L) : normIdeal Q K ≤ normIdeal Q L :=
  span_mono (Set.image_mono h)

/-- Two vectors $x, y$ with $B(x,y)$ a unit and $Q(x)$ a non-unit span a binary unimodular lattice. -/
theorem span_pair_unimodular {x y : V} {qx qy e : R} (hqx : ¬ IsUnit qx) (he : IsUnit e)
    (hQx : Q x = algebraMap R F qx) (hQy : Q y = algebraMap R F qy) (hxy : bil Q x y = algebraMap R F e) :
    IsUnimodular Q (span R {x, y}) ∧ finrank R (span R {x, y}) = 2 := by
  let v : Fin 2 → V := ![x, y]
  let U : Matrix (Fin 2) (Fin 2) R := !![qx, e; e, qy]
  have hG : gram Q v = (1 : F) • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, hQx, hQy, hxy, bil_comm Q y x]
  have hU : IsUnit U.det := by
    rw [Matrix.det_fin_two_of]
    exact u93_isUnit_sub_of_nonunit (fun h => hqx (isUnit_of_mul_isUnit_left h)) (he.mul he)
  obtain ⟨hmod, hrk⟩ := isModular_span_of_gram Q (one_ne_zero : (1 : F) ≠ 0) hU hG
  have hv : Set.range v = {x, y} := by ext w; simp [v, eq_comm, or_comm]
  rw [hv, ← Submodule.one_eq_span] at hmod
  rw [hv] at hrk
  exact ⟨hmod, by simpa using hrk⟩

/-- Two orthogonal vectors with unit values span a binary unimodular lattice. -/
theorem span_pair_diag {x y : V} {q₁ q₂ : R} (h1 : IsUnit q₁) (h2 : IsUnit q₂)
    (hQx : Q x = algebraMap R F q₁) (hQy : Q y = algebraMap R F q₂) (hxy : bil Q x y = 0) :
    IsUnimodular Q (span R {x, y}) ∧ finrank R (span R {x, y}) = 2 := by
  let v : Fin 2 → V := ![x, y]
  let U : Matrix (Fin 2) (Fin 2) R := !![q₁, 0; 0, q₂]
  have hG : gram Q v = (1 : F) • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, hQx, hQy, hxy, bil_comm Q y x]
  have hU : IsUnit U.det := by
    rw [Matrix.det_fin_two_of]
    simpa using h1.mul h2
  obtain ⟨hmod, hrk⟩ := isModular_span_of_gram Q (one_ne_zero : (1 : F) ≠ 0) hU hG
  have hv : Set.range v = {x, y} := by ext w; simp [v, eq_comm, or_comm]
  rw [hv, ← Submodule.one_eq_span] at hmod
  rw [hv] at hrk
  exact ⟨hmod, by simpa using hrk⟩

/-- **Splitting data for 93:18 (ii)** (O'Meara 1963, p. 260, "take a splitting $L = J \perp K$ with $J$ binary and
$\mathfrak nK = \mathfrak nL$"): a finitely generated unimodular lattice of rank $\ge 3$ contains a binary
unimodular sublattice $J$ with a vector $x \in J$ whose value is a norm generator of $J$, and a vector $z \in L$
orthogonal to $J$ with $Q(z)\mathfrak o = \mathfrak nL$. -/
theorem exists_split_data {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L) (hrk : 3 ≤ finrank R L) :
    ∃ J : Submodule R V, J ≤ L ∧ J.FG ∧ IsUnimodular Q J ∧ finrank R J = 2 ∧
      ∃ x ∈ J, IsNormGenerator Q J (Q x) ∧
        ∃ z ∈ L, (∀ j ∈ J, bil Q z j = 0) ∧ R ∙ Q z = normIdeal Q L := by
  have hsc : scale Q L = 1 := hU.2.1
  have hne := ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  by_cases hn : normIdeal Q L = 1
  · -- all norms are units: split off two unit vectors
    obtain ⟨w₁, hw₁, r₁, hr₁, hQ₁, K₁, hK₁, hK₁'⟩ := u93_exists_split_unit Q hfg hU hn
    obtain ⟨hJ₁, hrk₁⟩ := u93_isUnimodular_span_singleton Q hr₁ hQ₁
    have hrkL := isOrthSum_finrank Q hK₁ hfg
    have hK₁0 : K₁ ≠ ⊥ := by
      rintro rfl
      simp at hrkL; omega
    have hnK₁ := hK₁'.resolve_left hK₁0
    have hK₁le : K₁ ≤ L := hK₁.sup_eq ▸ le_sup_right
    have hK₁fg : K₁.FG := FG.of_le hfg hK₁le
    have hK₁U := u93_isUnimodular_of_orth Q hfg hU hJ₁ hK₁ hK₁0
    obtain ⟨w₂, hw₂, r₂, hr₂, hQ₂, K₂, hK₂, hK₂'⟩ := u93_exists_split_unit Q hK₁fg hK₁U hnK₁
    obtain ⟨hJ₂, hrk₂⟩ := u93_isUnimodular_span_singleton Q hr₂ hQ₂
    have hrkK := isOrthSum_finrank Q hK₂ hK₁fg
    have hK₂0 : K₂ ≠ ⊥ := by
      rintro rfl
      simp at hrkK; omega
    have hnK₂ := hK₂'.resolve_left hK₂0
    have hK₂le : K₂ ≤ K₁ := hK₂.sup_eq ▸ le_sup_right
    have hK₂fg : K₂.FG := FG.of_le hK₁fg hK₂le
    obtain ⟨z, hzK₂, hz⟩ := exists_normIdeal_eq Q hK₂fg
    have hw₂K₁ : w₂ ∈ K₁ := hK₂.sup_eq ▸ mem_sup_left (mem_span_singleton_self w₂)
    have hw₁w₂ : bil Q w₁ w₂ = 0 := hK₁.orth w₁ (mem_span_singleton_self w₁) w₂ hw₂K₁
    obtain ⟨hJ, hJrk⟩ := span_pair_diag Q hr₁ hr₂ hQ₁ hQ₂ hw₁w₂
    have hw₁J : w₁ ∈ span R {w₁, w₂} := subset_span (by simp)
    have hw₂J : w₂ ∈ span R {w₁, w₂} := subset_span (by simp)
    have hJL : span R {w₁, w₂} ≤ L := by
      rw [span_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hw₁
      · exact hK₁le hw₂K₁
    refine ⟨span R {w₁, w₂}, hJL, fg_span (Set.toFinite _), hJ, hJrk, w₁, hw₁J, ⟨Q_mem_normGroup Q hw₁J, ?_⟩,
      z, hK₁le (hK₂le hzK₂), ?_, ?_⟩
    · apply le_antisymm
      · rw [span_singleton_le_iff_mem]; exact Q_mem_normIdeal Q hw₁J
      · refine (normIdeal_le_scale Q _).trans ?_
        rw [hJ.2.1, hQ₁, u93_span_unit hr₁]
    · refine bil_zero_on_span Q (S := {w₁, w₂}) ?_
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · rw [bil_comm]; exact hK₁.orth _ (mem_span_singleton_self _) z (hK₂le hzK₂)
      · rw [bil_comm]; exact hK₂.orth _ (mem_span_singleton_self _) z hzK₂
    · rw [← hz, hn, hnK₂]
  · -- the norm is not the unit ideal
    obtain ⟨z₀, hz₀L, hz₀n⟩ := exists_normIdeal_eq Q hfg
    obtain ⟨q₀, hq₀⟩ := a10_mem_one Q hU hz₀L hz₀L
    rw [bil_self] at hq₀
    have hq₀n : ¬ IsUnit q₀ := by
      intro hq
      apply hn
      refine le_antisymm ((normIdeal_le_scale Q L).trans hsc.le) ?_
      rw [hz₀n, ← hq₀, u93_span_unit hq]
    have ha : IsNormGenerator Q L (Q z₀) := ⟨Q_mem_normGroup Q hz₀L, hz₀n.symm⟩
    have ha0 := ha.ne_zero Q hreg hne
    have hmax := a10_isMaxVec Q hz₀L ha ha0
    have hL1 : IsModular Q (R ∙ (1 : F)) L := by rw [← Submodule.one_eq_span]; exact hU
    obtain ⟨z', hz'L, hz'⟩ := exists_bil_unit_of_isMaxVec Q hfg hL1 hmax
    obtain ⟨e, he, hbe⟩ := u93_unit_of_span_eq_one (hz'.trans (Submodule.one_eq_span).symm)
    obtain ⟨q', hq'⟩ := a10_mem_one Q hU hz'L hz'L
    rw [bil_self] at hq'
    obtain ⟨hN, hNrk⟩ := span_pair_unimodular Q hq₀n he hq₀.symm hq'.symm hbe
    have hNL : span R {z₀, z'} ≤ L := by
      rw [span_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hz₀L
      · exact hz'L
    obtain ⟨M, hM⟩ := splits_of_isModular_of_scale_eq Q hNL hN (fg_span (Set.toFinite _)) hsc
    have hrkL := isOrthSum_finrank Q hM hfg
    have hM0 : M ≠ ⊥ := by
      rintro rfl
      simp at hrkL; omega
    have hMle : M ≤ L := hM.sup_eq ▸ le_sup_right
    have hMfg : M.FG := FG.of_le hfg hMle
    have hMU := u93_isUnimodular_of_orth Q hfg hU hN hM hM0
    have hMreg : IsRegular Q M := IsModular.isRegular Q hMU hMfg
    obtain ⟨zM, hzML, hzMn⟩ := exists_normIdeal_eq Q hMfg
    obtain ⟨qM, hqM⟩ := a10_mem_one Q hMU hzML hzML
    rw [bil_self] at hqM
    have hqMn : ¬ IsUnit qM := by
      intro hq
      apply hn
      refine le_antisymm ((normIdeal_le_scale Q L).trans hsc.le) ?_
      calc (1 : Submodule R F) = R ∙ Q zM := by rw [← hqM, u93_span_unit hq]
        _ ≤ normIdeal Q M := by rw [span_singleton_le_iff_mem]; exact Q_mem_normIdeal Q hzML
        _ ≤ normIdeal Q L := normIdeal_mono' Q hMle
    have haM : IsNormGenerator Q M (Q zM) := ⟨Q_mem_normGroup Q hzML, hzMn.symm⟩
    have haM0 := haM.ne_zero Q hMreg hM0
    have hmaxM := a10_isMaxVec Q hzML haM haM0
    have hM1 : IsModular Q (R ∙ (1 : F)) M := by rw [← Submodule.one_eq_span]; exact hMU
    obtain ⟨z', hz'M, hz'M'⟩ := exists_bil_unit_of_isMaxVec Q hMfg hM1 hmaxM
    obtain ⟨e', he', hbe'⟩ := u93_unit_of_span_eq_one (hz'M'.trans (Submodule.one_eq_span).symm)
    obtain ⟨q'', hq''⟩ := a10_mem_one Q hMU hz'M hz'M
    rw [bil_self] at hq''
    obtain ⟨hJ, hJrk⟩ := span_pair_unimodular Q hqMn he' hqM.symm hq''.symm hbe'
    have hJM : span R {zM, z'} ≤ M := by
      rw [span_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hzML
      · exact hz'M
    have hzMJ : zM ∈ span R {zM, z'} := subset_span (by simp)
    refine ⟨span R {zM, z'}, hJM.trans hMle, fg_span (Set.toFinite _), hJ, hJrk, zM, hzMJ,
      ⟨Q_mem_normGroup Q hzMJ, ?_⟩, z₀, hz₀L, ?_, hz₀n.symm⟩
    · apply le_antisymm
      · rw [span_singleton_le_iff_mem]; exact Q_mem_normIdeal Q hzMJ
      · exact (normIdeal_mono' Q hJM).trans hzMn.le
    · intro j hj
      exact hM.orth z₀ (subset_span (by simp)) j (hJM hj)

/-- An element of $R$ of even order is a square times a unit: $c\varepsilon = t^2$. -/
theorem exists_sq_of_even_order {π : R} (hπ : Irreducible π) {c : R} (hc : c ≠ 0)
    (hev : Even (dord hπ (algebraMap R F c))) : ∃ t ε : R, IsUnit ε ∧ c * ε = t ^ 2 := by
  obtain ⟨n, u, hcu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
  have hd : dord hπ (algebraMap R F c) = n := by
    refine dord_eq hπ u.isUnit (x := algebraMap R F c) (k := (n : ℤ)) ?_
    rw [hcu]; simp [map_mul, map_pow, zpow_natCast]
  rw [hd] at hev
  obtain ⟨k, hk⟩ := hev
  have hnk : n = k.toNat + k.toNat := by omega
  refine ⟨π ^ k.toNat, ↑u⁻¹, (u⁻¹).isUnit, ?_⟩
  rw [hcu, hnk]
  calc (↑u * π ^ (k.toNat + k.toNat)) * (↑u⁻¹ : R) = π ^ (k.toNat + k.toNat) * (↑u * ↑u⁻¹) := by ring
    _ = (π ^ k.toNat) ^ 2 := by rw [Units.mul_inv]; ring

/-- **Proposition 93:18 (ii)** (O'Meara 1963, §93D, p. 260): let $L$ be a unimodular lattice of dimension
$\ge 3$ over a dyadic local field, $a$ a norm generator and $b$ a weight generator of $L$ with
$\operatorname{ord} a + \operatorname{ord} b$ even. Then $L$ contains $x, y$ with $Q(x) = Q(y) = 0$, $B(x,y) = 1$,
i.e. $L = \mathfrak ox + \mathfrak oy \perp K$ with $\mathfrak ox + \mathfrak oy \cong A(0,0)$ (see
`exists_hyperbolic_splitting_of_even`). (Remark of 93:18 (i): in this case $b\mathfrak o = 2\mathfrak o$, which is
`weight_gen_eq_of_even`.) The proof differs from the book's: instead of 93:11 it uses the Hensel step
`exists_hyperbolic_of_even_pair`. -/
@[kb "omeara1963" "§93D, 93:18 (ii), p. 260"]
theorem exists_hyperbolic_pair_of_even (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V}
    (hfg : L.FG) (hU : IsUnimodular Q L) (hrk : 3 ≤ finrank R L) {a b : F} (ha : IsNormGenerator Q L a)
    (hb : IsWeightGenerator Q L b) (hev : Even (dord hπ a + dord hπ b)) :
    ∃ x ∈ L, ∃ y ∈ L, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1 := by
  have hne := ne_bot_of_isUnimodular Q hU
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have ha0 := ha.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  have hbeq := weight_gen_eq_of_even Q h2p hπ hreg hne ha hb hev
  rw [hU.2.1] at hbeq
  have hw : ∀ w ∈ weight Q L, ∃ c : R, w = 2 * algebraMap R F c := by
    intro w hwm
    rw [← hb, hbeq] at hwm
    obtain ⟨c, hc, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hwm
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    exact ⟨r, by simp [smul_eq_mul]⟩
  obtain ⟨J, hJL, hJfg, hJU, hJrk, x, hxJ, hxn, z, hzL, hzJ, hzn⟩ := exists_split_data Q hfg hU hrk
  have hxL := hJL hxJ
  obtain ⟨α, hα⟩ := a10_mem_one Q hU hxL hxL
  rw [bil_self] at hα
  obtain ⟨β, hβw, -, bs, hbs0, hbsG⟩ := exists_hasMatrixA Q h2p hJfg hJU hJrk hxJ hα.symm hxn
  obtain ⟨ζ, hζ⟩ := hw _ (weight_mono Q hJL hβw)
  have hxy : bil Q x (bs 1 : V) = 1 := by
    have := congrFun (congrFun hbsG 0) 1
    simpa [gram, matA, hbs0] using this
  have hQy : Q (bs 1 : V) = 2 * algebraMap R F ζ := by
    have := congrFun (congrFun hbsG 1) 1
    simp only [gram, Matrix.of_apply, bil_self, matA] at this
    rw [this]; simpa using hζ
  have hyJ : (bs 1 : V) ∈ J := (bs 1).2
  -- the parity condition `t² Q(z) = 2ε`
  have hz1 : IsNormGenerator Q L (Q z) := ⟨Q_mem_normGroup Q hzL, hzn⟩
  have hz0 := hz1.ne_zero Q hreg hne
  have hspan2 : R ∙ b = R ∙ (2 : F) := by
    rw [hbeq, Submodule.one_eq_span, Submodule.smul_span, Set.smul_set_singleton, smul_eq_mul, mul_one]
  have hdb : dord hπ b = dord hπ (2 : F) := dord_eq_of_span_eq hπ hb0 (two_ne_zero' F) hspan2
  have hdz : dord hπ (Q z) = dord hπ a := dord_eq_of_span_eq hπ hz0 ha0 (hzn.trans ha.2.symm)
  have h2b : (2 : F) ∈ R ∙ b := hspan2 ▸ mem_span_singleton_self _
  have h2mem : (2 : F) ∈ R ∙ Q z := by
    rw [hzn, ← ha.2]; exact weight_gen_le_norm_gen Q ha hb h2b
  obtain ⟨c, hc⟩ := mem_span_singleton.mp h2mem
  rw [Algebra.smul_def] at hc
  have hcF : algebraMap R F c ≠ 0 := fun h => by
    rw [h, zero_mul] at hc; exact two_ne_zero' F hc.symm
  have hc0 : c ≠ 0 := fun h => hcF (by rw [h, map_zero])
  have hdc : dord hπ (algebraMap R F c) = dord hπ b - dord hπ a := by
    have := dord_mul hπ hcF hz0
    rw [hc] at this
    omega
  obtain ⟨t, ε, hε, hcε⟩ := exists_sq_of_even_order (F := F) hπ hc0 (by
    rw [hdc]; obtain ⟨r, hr⟩ := hev; exact ⟨r - dord hπ a, by omega⟩)
  have hm : ∃ t ε : R, IsUnit ε ∧ algebraMap R F t ^ 2 * Q z = 2 * algebraMap R F ε := by
    refine ⟨t, ε, hε, ?_⟩
    rw [← map_pow, ← hcε, map_mul, mul_assoc, mul_comm (algebraMap R F ε), ← mul_assoc, hc]
  exact core_hyperbolic Q h2p hfg hU hw hxL (hJL hyJ) hzL hxy hQy (hzJ x hxJ) (hzJ _ hyJ) hzn hm
    |>.imp fun x' hx' => hx'

/-- **93:18 (ii), splitting form**: under the hypotheses of `exists_hyperbolic_pair_of_even`,
$L = (\mathfrak ox + \mathfrak oy) \perp K$ with $Q(x) = Q(y) = 0$, $B(x,y) = 1$ (so
$L \cong \langle A(0,0)\rangle \perp K$). -/
@[kb "omeara1963" "§93D, 93:18 (ii), p. 260 (splitting form)"]
theorem exists_hyperbolic_splitting_of_even (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L) (hrk : 3 ≤ finrank R L) {a b : F}
    (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b) (hev : Even (dord hπ a + dord hπ b)) :
    ∃ x y : V, ∃ K : Submodule R V, Q x = 0 ∧ Q y = 0 ∧ bil Q x y = 1 ∧ IsOrthSum Q L (span R {x, y}) K := by
  obtain ⟨x, hx, y, hy, h1, h2, h3⟩ := exists_hyperbolic_pair_of_even Q h2p hπ hfg hU hrk ha hb hev
  have hsub : ∀ w ∈ L, w ∈ subA Q 1 L := fun w hw =>
    ⟨hw, fun l hl => hU.2.1 ▸ bil_mem_scale Q hw hl⟩
  obtain ⟨K, hK⟩ := exists_isOrthSum_span_hyp Q (hsub x hx) (hsub y hy) h1 h2 h3
  exact ⟨x, y, K, h1, h2, h3, hK⟩

end Splitting

section Spinor

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- If $u \in L$, $Q(u) \ne 0$ and $2B(L, u) \subseteq Q(u)\mathfrak o$, then $\tau_u \in O(L)$ (no maximality of
$u$ is needed for this direction of §91B). -/
theorem symmetry_mem_orthLat_of_dvd {L : Submodule R V} {u : V} (hu : Q u ≠ 0) (huL : u ∈ L)
    (h : ∀ l ∈ L, 2 * bil Q l u ∈ R ∙ Q u) : symmetry Q u hu ∈ orthLat Q L := by
  refine symmetry_mem_orthLat_of_le Q hu fun x hx => ?_
  obtain ⟨r, hr⟩ := mem_span_singleton.mp (h x hx)
  rw [symmetry_apply]
  have : (2 * bil Q x u / Q u) • u = r • u := by
    rw [← algebraMap_smul F r u]
    congr 1
    rw [← hr, Algebra.smul_def]
    field_simp
  rw [this]
  exact L.sub_mem hx (L.smul_mem r huL)

/-- **93:20, even-parity case** (O'Meara 1963, §93D, p. 262). This is the case of 93:20 in which
$\operatorname{ord} a + \operatorname{ord} b$ is even for a norm generator $a$ and a weight generator $b$ of the
unimodular lattice $L$ (rank $\ge 3$); the odd-parity case, where O'Meara uses the normal forms of 93:18 (iii), (iv),
(v), is **not** proved here, so this is *not* the full 93:20. Conclusion: every unit $\varepsilon$ of $\mathfrak o$ is
the spinor norm of some $\sigma \in O^+(L)$ (in the factorization sense of `HasSpinorNorm`). *Proof:* by 93:18 (ii)
$L$ contains a hyperbolic pair $x, y$; then $Q(x + y) = 2$, $Q(x + \varepsilon y) = 2\varepsilon$ and
$\sigma = \tau_{x+y}\tau_{x+\varepsilon y} \in O^+(L)$ has spinor norm $4\varepsilon \equiv \varepsilon$.
Added hypothesis compared with O'Meara: `Even (dord hπ a + dord hπ b)` and `FiniteDimensional F V`
(as in `exists_hasSpinorNorm_of_isModular`). -/
@[kb "omeara1963" "§93D, 93:20, p. 262 (case ord a + ord b even)"]
theorem exists_hasSpinorNorm_unit_of_even [FiniteDimensional F V] (h2p : ¬ IsUnit (2 : R)) {π : R}
    (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L) (hrk : 3 ≤ finrank R L)
    {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b)
    (hev : Even (dord hπ a + dord hπ b)) {ε : R} (hε : IsUnit ε) :
    ∃ σ ∈ orthLatPlus Q L, HasSpinorNorm Q σ (algebraMap R F ε) := by
  obtain ⟨x, hx, y, hy, hQx, hQy, hxy⟩ := exists_hyperbolic_pair_of_even Q h2p hπ hfg hU hrk ha hb hev
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  -- for a unit `c`, `x + c y` has value `2c` and its symmetry is a unit of `L`
  have key : ∀ c : R, IsUnit c → ∃ (v : V) (hv : Q v ≠ 0), v ∈ L ∧ Q v = 2 * algebraMap R F c ∧
      symmetry Q v hv ∈ orthLat Q L := by
    intro c hc
    have hQv : Q (x + c • y) = 2 * algebraMap R F c := by
      rw [Q_add, Q_rsmul, bil_rsmul_right, hQx, hQy, hxy]; ring
    have hcF : algebraMap R F c ≠ 0 := fun h => hc.ne_zero ((IsFractionRing.injective R F) (by simpa using h))
    have hv0 : Q (x + c • y) ≠ 0 := by rw [hQv]; exact mul_ne_zero h2F hcF
    have hvL : x + c • y ∈ L := L.add_mem hx (L.smul_mem c hy)
    refine ⟨x + c • y, hv0, hvL, hQv, symmetry_mem_orthLat_of_dvd Q hv0 hvL fun l hl => ?_⟩
    obtain ⟨r, hr⟩ := a10_mem_one Q hU hl hvL
    obtain ⟨ci, hci⟩ := hc.exists_left_inv
    refine mem_span_singleton.mpr ⟨r * ci, ?_⟩
    rw [Algebra.smul_def, hQv, ← hr, map_mul]
    have : algebraMap R F ci * algebraMap R F c = 1 := by rw [← map_mul, hci, map_one]
    linear_combination (2 * algebraMap R F r) * this
  obtain ⟨v₁, h1, hv₁L, hQ₁, hs₁⟩ := key 1 isUnit_one
  obtain ⟨v₂, h2, hv₂L, hQ₂, hs₂⟩ := key ε hε
  refine ⟨symmetry Q v₁ h1 * symmetry Q v₂ h2, ⟨(orthLat Q L).mul_mem hs₁ hs₂,
    symmetry_mul_mem_orthPlus Q h1 h2⟩, ?_⟩
  obtain ⟨l, hl, hσ, s, hs0, hprod⟩ := hasSpinorNorm_symmetry_mul Q h1 h2
  refine ⟨l, hl, hσ, s * 2, mul_ne_zero hs0 h2F, ?_⟩
  rw [hprod, hQ₁, hQ₂]
  simp only [map_one]
  ring

end Spinor

section Iso

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **93:16 without the ambient-space hypothesis**: the proof of `isometricLat_of_normGroup_eq` only uses that
$L$ and $K$ are finitely generated and span the same $F$-subspace of $V$. Unimodular lattices $L, K \subseteq V$
with $FL = FK$ and $\mathfrak gL = \mathfrak gK$ are isometric. -/
theorem isometricLat_of_normGroup_eq_of_span {L K : Submodule R V} (hLfg : L.FG) (hKfg : K.FG)
    (hspan : span F (K : Set V) = span F (L : Set V))
    (hL : IsUnimodular Q L) (hK : IsUnimodular Q K) (hg : normGroup Q L = normGroup Q K) :
    IsometricLat Q Q L K := by
  have hL' : IsModular Q (R ∙ (1 : F)) L := by rw [← Submodule.one_eq_span]; exact hL
  have hK' : IsModular Q (R ∙ (1 : F)) K := by rw [← Submodule.one_eq_span]; exact hK
  have sdL : AdjSelfDual Q (1 : F) L := adj_selfDual_of_isModular Q hLfg hL'
  have sdK : AdjSelfDual Q (1 : F) K := adj_selfDual_of_isModular Q hKfg hK'
  set Q2 : QuadraticForm F (V × V) := Q.prod (-Q) with hQ2
  set Q3 : QuadraticForm F (V × (V × V)) := Q.prod Q2 with hQ3
  set S : Set F := (normGroup Q L : Set F) with hS
  set r : ℕ := finrank F (span F (L : Set V)) with hr
  have hY : AdjPlaneSum Q2 (1 : F) S r (K.prod L) := by
    have := adj_planeSum_prod Q one_ne_zero hKfg hLfg sdK sdL hspan S (fun k hk l hl =>
      sub_mem (hg ▸ Q_mem_normGroup Q hk) (Q_mem_normGroup Q hl))
    rwa [hspan] at this
  have hY' : AdjPlaneSum Q2 (1 : F) S r (L.prod L) :=
    adj_planeSum_prod Q one_ne_zero hLfg hLfg sdL sdL rfl S (fun k hk l hl =>
      sub_mem (Q_mem_normGroup Q hk) (Q_mem_normGroup Q hl))
  have hone : (R ∙ (1 : F)) = 1 := (Submodule.one_eq_span).symm
  have hD1 : IsOrthSum Q3 (L.prod (K.prod L)) ((⊥ : Submodule R V).prod (K.prod L)) (L.prod ⊥) :=
    adj_isOrthSum_symm Q3 (adj_isOrthSum_prod_split Q Q2 L (K.prod L))
  have hH1 : AdjPlaneSum Q3 (1 : F) S r ((⊥ : Submodule R V).prod (K.prod L)) :=
    adj_planeSum_of_isometric Q2 Q3 r (adj_isometricLat_bot_prod Q Q2 (K.prod L)) hY
  have hS1 : ∀ s ∈ S, s ∈ normGroup Q3 (subA Q3 (R ∙ (1 : F)) (L.prod ⊥)) := fun s hs =>
    adj_normGroup_subA_prod_bot_le Q Q2 (R ∙ (1 : F)) L
      (normGroup_mono Q (adj_le_subA Q (by rw [hL'.2.1])) hs)
  obtain ⟨H1, K1, hH1K1, hpl1, hLK1⟩ :=
    adj_planeSum_iter Q3 one_ne_zero S r hH1 hD1 (adj_isometricLat_refl Q3 _) hS1
  have hD2 : IsOrthSum Q3 (L.prod (K.prod L)) (L.prod ((⊥ : Submodule R V).prod L))
      ((⊥ : Submodule R V).prod (K.prod ⊥)) :=
    adj_isOrthSum_prod_right Q Q2 L (adj_isOrthSum_symm Q2 (adj_isOrthSum_prod_split Q (-Q) K L))
  have hH2 : AdjPlaneSum Q3 (1 : F) S r (L.prod ((⊥ : Submodule R V).prod L)) :=
    adj_planeSum_of_isometric (Q.prod (-Q)) Q3 r
      (adj_isometricLat_prod Q (-Q) Q Q2 (adj_isometricLat_refl Q L)
        (adj_isometricLat_bot_prod Q (-Q) L)) hY'
  have hS2 : ∀ s ∈ S, s ∈ normGroup Q3 (subA Q3 (R ∙ (1 : F)) ((⊥ : Submodule R V).prod (K.prod ⊥))) :=
    fun s hs => adj_normGroup_subA_bot_prod_le Q Q2 (R ∙ (1 : F)) (K.prod ⊥)
      (adj_normGroup_subA_prod_bot_le Q (-Q) (R ∙ (1 : F)) K
        (normGroup_mono Q (adj_le_subA Q (by rw [hK'.2.1])) (hg ▸ hs)))
  obtain ⟨H2, K2, hH2K2, hpl2, hKK2⟩ :=
    adj_planeSum_iter Q3 one_ne_zero S r hH2 hD2 (adj_isometricLat_refl Q3 _) hS2
  have hmid := adj_planeSum_cancel Q3 one_ne_zero r (adj_isometricLat_refl Q3 _) hH1K1 hH2K2 hpl1 hpl2
  have hKe : IsometricLat Q Q3 K ((⊥ : Submodule R V).prod (K.prod ⊥)) :=
    adj_isometricLat_trans Q Q2 Q3 (adj_isometricLat_prod_bot Q (-Q) K)
      (adj_isometricLat_bot_prod Q Q2 (K.prod ⊥))
  exact adj_isometricLat_trans Q Q3 Q (adj_isometricLat_prod_bot Q Q2 L)
    (adj_isometricLat_trans Q3 Q3 Q
      (adj_isometricLat_trans Q3 Q3 Q3 hLK1
        (adj_isometricLat_trans Q3 Q3 Q3 hmid (adj_isometricLat_symm Q3 Q3 hKK2)))
      (adj_isometricLat_symm Q Q3 hKe))

/-- An isometry of lattices preserves the bilinear form. -/
theorem bil_eq_of_isometry {L K : Submodule R V} (f : L ≃ₗ[R] K) (hf : ∀ x : L, Q (f x : V) = Q (x : V))
    (u w : L) : bil Q (f u : V) (f w : V) = bil Q (u : V) (w : V) := by
  have h1 := hf (u + w)
  rw [map_add, Submodule.coe_add, Submodule.coe_add, Q_add, Q_add, hf u, hf w] at h1
  have h2 : (2 : F) * bil Q (f u : V) (f w : V) = 2 * bil Q (u : V) (w : V) := by linear_combination h1
  exact mul_left_cancel₀ (two_ne_zero' F) h2

/-- **Change of base and the discriminant**: two bases of a lattice have discriminants differing by the square of a
unit. -/
theorem exists_unit_det_gram {L : Submodule R V} {n : ℕ} (b b' : Basis (Fin n) R L) :
    ∃ u : R, IsUnit u ∧ (gram Q fun i => (b' i : V)).det =
      algebraMap R F u ^ 2 * (gram Q fun i => (b i : V)).det := by
  classical
  let T : Matrix (Fin n) (Fin n) R := fun i j => b.repr (b' i) j
  have hT : (fun i => (b' i : V)) = fun i => ∑ j, T i j • (b j : V) := by
    funext i
    have := congrArg Subtype.val (b.sum_repr (b' i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hTt : T = (b.toMatrix b').transpose := by
    ext i j; simp [T, Basis.toMatrix_apply, Matrix.transpose_apply]
  have hdetT : IsUnit T.det := by
    have h := b.isUnit_det b'
    rwa [Basis.det_apply, ← Matrix.det_transpose, ← hTt] at h
  refine ⟨T.det, hdetT, ?_⟩
  rw [hT, gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (T.map (algebraMap R F)).det = algebraMap R F T.det from (RingHom.map_det _ _).symm]
  ring

end Iso

end Uni93

end QuadFormsKB.OMeara
