/-
# O'Meara 93:28, sufficiency over a 2-adic field: binary blocks

**Setting** (as in `Sec93E.lean`): $R$ a discrete valuation ring with finite residue field and fraction field $F$,
$2 \in F^\times$, $2$ not a unit of $R$ (dyadic).

**Proves** (O'Meara 1963, §93G, proof of 93:29, sufficiency, p. 278: "$K_1 \cong \langle A(2^{u_1}, 2\alpha)\rangle
\perp \langle A(2, 2\beta)\rangle$ with $\alpha, \beta \in \mathfrak o$")
* `exists_sq_residue`: every element of $R$ is a square modulo $\mathfrak p$ (the residue field is finite of
  characteristic $2$, hence perfect);
* `exists_bil_one_of_primitive`: in a unimodular lattice, a vector with a unit coordinate pairs to $1$ with some
  vector of the lattice;
* `exists_pair_small`: a unimodular lattice of rank $\ge 2$ contains $x, y$ with $B(x, y) = 1$ and
  $Q(y) \in \mathfrak p$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCoreSplit
import QuadFormsKB.Literature.OMeara.Sec93GBasic
import QuadFormsKB.Literature.OMeara.Sec93GNec

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreTwo

section Residue

variable {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]

/-- **The residue field of a dyadic ring is perfect**: if $2 \in \mathfrak p$, every $q \in R$ is congruent to a
square modulo $\mathfrak p$ (squaring is injective on the finite field $R/\mathfrak p$ of characteristic $2$). -/
theorem exists_sq_residue (h2 : (2 : R) ∈ maximalIdeal R) (q : R) : ∃ c : R, q - c ^ 2 ∈ maximalIdeal R := by
  have h2k : (2 : ResidueField R) = 0 := by
    rw [← map_ofNat (residue R) 2]; exact (residue_eq_zero_iff 2).2 h2
  have hinj : Function.Injective (fun x : ResidueField R => x ^ 2) := by
    intro x y hxy
    simp only at hxy
    have : (x - y) ^ 2 = 0 := by
      have e : (x - y) ^ 2 = x ^ 2 + y ^ 2 - 2 * x * y := by ring
      rw [e, h2k, hxy]; ring_nf; rw [show y ^ 2 * 2 = y ^ 2 * (2 : ResidueField R) from rfl, h2k, mul_zero]
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  obtain ⟨c', hc'⟩ := (Finite.injective_iff_surjective.mp hinj) (residue R q)
  obtain ⟨c, rfl⟩ := residue_surjective c'
  refine ⟨c, (residue_eq_zero_iff _).1 ?_⟩
  simp only at hc'
  rw [map_sub, map_pow, hc', sub_self]

end Residue

section Pair

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

omit [FiniteDimensional F V] in
/-- In a unimodular lattice all values $B(x, y)$ are integral. -/
theorem bil_integral {L : Submodule R V} (hU : IsUnimodular Q L) {x y : V} (hx : x ∈ L) (hy : y ∈ L) :
    ∃ r : R, bil Q x y = algebraMap R F r := by
  have h := bil_mem_scale Q hx hy
  rw [hU.2.1] at h
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp h
  exact ⟨r, hr.symm⟩

/-- **A primitive vector of a unimodular lattice pairs to $1$** (O'Meara 1963, 82:14b): if $L$ is unimodular with
base $b$ and $y \in L$ has a coordinate outside $\mathfrak p$, then $B(x, y) = 1$ for some $x \in L$. -/
theorem exists_bil_one_of_primitive {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L) {ι : Type*}
    [Fintype ι] (b : Basis ι R L) (y : L) (hy : ∃ i, b.equivFun y i ∉ maximalIdeal R) :
    ∃ x ∈ L, bil Q x (y : V) = 1 := by
  by_contra hno
  push_neg at hno
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : maximalIdeal R = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hinj := IsFractionRing.injective R F
  have hπF : algebraMap R F π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  -- every value `B(y, z)` lies in `𝔭`
  have key : ∀ z ∈ L, ∃ r : R, bil Q (y : V) z = algebraMap R F (π * r) := by
    intro z hz
    obtain ⟨s, hs⟩ := bil_integral Q hU y.2 hz
    by_cases hsm : s ∈ maximalIdeal R
    · rw [hmax] at hsm
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hsm
      exact ⟨r, by rw [hs, ← hr, mul_comm]⟩
    · exfalso
      have hsu : IsUnit s := by
        by_contra hnu; exact hsm ((IsLocalRing.mem_maximalIdeal s).mpr hnu)
      obtain ⟨u, rfl⟩ := hsu
      have hx : (algebraMap R F (↑u⁻¹ : R)) • z ∈ L := by
        rw [algebraMap_smul]; exact L.smul_mem _ hz
      refine hno _ hx ?_
      rw [bil_smul_left, bil_comm, hs, ← map_mul, Units.inv_mul, map_one]
  -- hence `π⁻¹ y ∈ L^# = L`
  have hreg : IsRegular Q L := IsModular.isRegular Q hU hfg
  have hne : L ≠ ⊥ := by
    rintro rfl
    obtain ⟨i, hi⟩ := hy
    have : y = 0 := Subsingleton.elim _ _
    rw [this, map_zero] at hi
    exact hi (zero_mem _)
  have hdual : dual Q L = L := (isUnimodular_iff_dual_eq Q hfg hne hreg).mp hU
  set w : V := (algebraMap R F π)⁻¹ • (y : V) with hw
  have hwL : w ∈ L := by
    rw [← hdual]
    refine ⟨Submodule.smul_mem _ _ (subset_span y.2), fun z hz => ?_⟩
    obtain ⟨r, hr⟩ := key z hz
    rw [hw, bil_smul_left, hr, map_mul, ← mul_assoc, inv_mul_cancel₀ hπF, one_mul]
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  have hyw : y = π • (⟨w, hwL⟩ : L) := by
    apply Subtype.ext
    simp only [SetLike.val_smul]
    rw [← algebraMap_smul F π w, hw, smul_smul, mul_inv_cancel₀ hπF, one_smul]
  obtain ⟨i, hi⟩ := hy
  apply hi
  rw [hyw, map_smul, Pi.smul_apply, smul_eq_mul, hmax]
  exact Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩

/-- **A binary block with small second norm** (O'Meara 1963, §93G, p. 278; §93D, 93:15): a unimodular lattice $L$
of rank $\ge 2$ over a dyadic ring with finite residue field contains $x, y$ with $B(x, y) = 1$ and
$Q(y) \in \mathfrak p$. With $Q(e_i) \equiv c_i^2 \bmod \mathfrak p$ take $y = c_2e_1 - c_1e_2$ (or $y = e_1$ when
$c_1, c_2 \in \mathfrak p$): $Q(y) \equiv 2c_1^2c_2^2 \equiv 0$, and $y$ is primitive. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (K₁ ≅ A(2^u, 2α) ⊥ A(2, 2β)); §93D, 93:15"]
theorem exists_pair_small [Finite (ResidueField R)] (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hU : IsUnimodular Q L) (hrk : 2 ≤ finrank R L) :
    ∃ x ∈ L, ∃ y ∈ L, bil Q x y = 1 ∧ ∃ q ∈ maximalIdeal R, Q y = algebraMap R F q := by
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hfg
  have h2m : (2 : R) ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h2p
  set i₀ : Fin (finrank R L) := ⟨0, by omega⟩
  set i₁ : Fin (finrank R L) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by simp [i₀, i₁, Fin.ext_iff] at h
  set e₁ : V := (b i₀ : V)
  set e₂ : V := (b i₁ : V)
  obtain ⟨q₁, hq₁⟩ := bil_integral Q hU (b i₀).2 (b i₀).2
  obtain ⟨q₂, hq₂⟩ := bil_integral Q hU (b i₁).2 (b i₁).2
  obtain ⟨β, hβ⟩ := bil_integral Q hU (b i₀).2 (b i₁).2
  rw [bil_self] at hq₁ hq₂
  obtain ⟨c₁, hc₁⟩ := exists_sq_residue h2m q₁
  obtain ⟨c₂, hc₂⟩ := exists_sq_residue h2m q₂
  -- the vector `y` with its coordinates
  obtain ⟨v, hv, hQv⟩ : ∃ v : Fin (finrank R L) → R, (∃ i, v i ∉ maximalIdeal R) ∧
      ∃ q ∈ maximalIdeal R, Q (∑ i, v i • (b i : V)) = algebraMap R F q := by
    by_cases hc : c₁ ∈ maximalIdeal R ∧ c₂ ∈ maximalIdeal R
    · refine ⟨Pi.single i₀ 1, ⟨i₀, by simp⟩, q₁, ?_, ?_⟩
      · have : q₁ = (q₁ - c₁ ^ 2) + c₁ * c₁ := by ring
        rw [this]; exact add_mem hc₁ (Ideal.mul_mem_left _ _ hc.1)
      · rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
        simp [hq₁]
    · refine ⟨Pi.single i₀ c₂ - Pi.single i₁ c₁, ?_, c₂ ^ 2 * q₁ + c₁ ^ 2 * q₂ - 2 * c₁ * c₂ * β, ?_, ?_⟩
      · by_cases h1 : c₁ ∈ maximalIdeal R
        · refine ⟨i₀, ?_⟩
          simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, if_neg h01, sub_zero]
          exact fun h2 => hc ⟨h1, h2⟩
        · refine ⟨i₁, ?_⟩
          simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, if_neg h01.symm, zero_sub]
          exact fun h => h1 (by simpa using neg_mem h)
      · have : c₂ ^ 2 * q₁ + c₁ ^ 2 * q₂ - 2 * c₁ * c₂ * β =
            c₂ ^ 2 * (q₁ - c₁ ^ 2) + c₁ ^ 2 * (q₂ - c₂ ^ 2) + 2 * (c₁ ^ 2 * c₂ ^ 2 - c₁ * c₂ * β) := by ring
        rw [this]
        exact add_mem (add_mem (Ideal.mul_mem_left _ _ hc₁) (Ideal.mul_mem_left _ _ hc₂))
          (Ideal.mul_mem_right _ _ h2m)
      · have hsum : ∑ i, (Pi.single i₀ c₂ - Pi.single i₁ c₁ : Fin (finrank R L) → R) i • (b i : V) =
            c₂ • e₁ - c₁ • e₂ := by
          simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
          rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
            Finset.sum_eq_single i₁ (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
          simp [e₁, e₂]
        rw [hsum, sub_eq_add_neg, ← neg_smul, ← algebraMap_smul F c₂ e₁, ← algebraMap_smul F (-c₁) e₂, Q_add,
          QuadraticMap.map_smul, QuadraticMap.map_smul, bil_smul_left, bil_smul_right]
        simp only [smul_eq_mul, e₁, e₂, hq₁, hq₂, hβ, map_neg, map_sub, map_add, map_mul, map_pow, map_ofNat]
        ring
  -- the pairing
  set y : L := ∑ i, v i • b i with hy
  have hyV : (y : V) = ∑ i, v i • (b i : V) := by simp only [hy, Submodule.coe_sum, Submodule.coe_smul]
  have hcoord : b.equivFun y = v := by rw [hy, ← Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx, hxy⟩ := exists_bil_one_of_primitive Q hfg hU b y (by rw [hcoord]; exact hv)
  obtain ⟨q, hq, hQ⟩ := hQv
  exact ⟨x, hx, y, y.2, hxy, q, hq, hyV ▸ hQ⟩

end Pair

section Shift

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open D18 Sat93 CoreSplit

/-- A fractional ideal $\mathfrak a = \xi\mathfrak o$ with $\mathfrak a \subsetneq \mathfrak o$ lies in $\mathfrak p$. -/
theorem le_maximal_of_lt_one {a : Submodule R F} (hfg : a.FG) (h0 : a ≠ ⊥) (hlt : a < 1) :
    a ≤ Submodule.map (Algebra.linearMap R F) (maximalIdeal R) := by
  obtain ⟨ξ, -, rfl⟩ := exists_eq_span_singleton (R := R) hfg h0
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hlt.le (mem_span_singleton_self ξ))
  have hrm : r ∈ maximalIdeal R := by
    by_contra hnm
    have hu : IsUnit r := by
      by_contra hnu; exact hnm ((IsLocalRing.mem_maximalIdeal r).mpr hnu)
    apply hlt.ne
    apply le_antisymm hlt.le
    rw [Submodule.one_eq_span, span_le, Set.singleton_subset_iff]
    obtain ⟨u, rfl⟩ := hu
    refine mem_span_singleton.mpr ⟨↑u⁻¹, ?_⟩
    rw [← hr, Algebra.smul_def, ← map_mul, Units.inv_mul, map_one]
  intro z hz
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hz
  refine ⟨c * r, Ideal.mul_mem_left _ _ hrm, ?_⟩
  rw [← hr, Algebra.linearMap_apply, map_mul, Algebra.smul_def]

/-- **93:19 inside a Jordan splitting** (O'Meara 1963, §93D, 93:19, p. 262, as used in §93F, steps 4–7, and §93G,
p. 278: "$K_1 \perp K_2 \cong \langle A(\cdot, 0)\rangle \perp \cdots \perp K_2'$"): let $K = K_1 \perp \cdots \perp K_t$
be a Jordan splitting with $K_1$ unimodular, $K_1 = J \perp C$ with $J = \mathfrak ox + \mathfrak oy$,
$Q(x) = \alpha \in \mathfrak p$, $B(x, y) = 1$, $Q(y) = \beta$, $\dim K_2 \ge 3$ and $\gamma_0 \in \mathfrak gK_2$
with $(\alpha + \gamma_0)\beta - 1$ a unit. Then $K$ has a Jordan splitting $K = K_1' \perp \cdots \perp K_t'$ with the
same scales and ranks, $K_1' = J' \perp C$, $J' = \mathfrak ox' + \mathfrak oy'$, $Q(x') = \alpha + \gamma_0$,
$B(x', y') = 1$, $Q(y') = \beta$ ($0$-based: `Ks 0`, `Ks 1` are $K_1$, $K_2$). -/
@[kb "omeara1963" "§93D, 93:19, p. 262, inside a Jordan splitting (as used in §93F, pp. 274–276, §93G, p. 278)"]
theorem exists_shift_first (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {K : Submodule R V}
    (hKfg : K.FG) {t : ℕ} {Ks : Fin (t + 2) → Submodule R V} (hK : IsJordanSplitting Q K Ks)
    (hs0 : scale Q (Ks 0) = 1) {x y : V} {C : Submodule R V} (hJC : IsOrthSum Q (Ks 0) (span R {x, y}) C)
    {α β : R} (hQx : Q x = algebraMap R F α) (hxy : bil Q x y = 1) (hQy : Q y = algebraMap R F β)
    (hα : α ∈ maximalIdeal R) (hrk1 : 3 ≤ finrank R (Ks 1)) {γ₀ : R}
    (hγ : algebraMap R F γ₀ ∈ normGroup Q (Ks 1)) (hdet : IsUnit ((α + γ₀) * β - 1 * 1)) :
    ∃ Ks' : Fin (t + 2) → Submodule R V, IsJordanSplitting Q K Ks' ∧
      (∀ i, scale Q (Ks' i) = scale Q (Ks i) ∧ finrank R (Ks' i) = finrank R (Ks i)) ∧
      ∃ x' y' : V, Q x' = algebraMap R F (α + γ₀) ∧ bil Q x' y' = 1 ∧ Q y' = algebraMap R F β ∧
        IsOrthSum Q (Ks' 0) (span R {x', y'}) C := by
  set J : Submodule R V := span R {x, y} with hJdef
  have hle : ∀ j, Ks j ≤ K := fun j => hK.split.iSup_eq ▸ le_iSup Ks j
  have hK0fg : (Ks 0).FG := FG.of_le hKfg (hle 0)
  have hK1fg : (Ks 1).FG := FG.of_le hKfg (hle 1)
  have hJK0 : J ≤ Ks 0 := hJC.sup_eq ▸ le_sup_left
  have hCK0 : C ≤ Ks 0 := hJC.sup_eq ▸ le_sup_right
  have h01 : (0 : Fin (t + 2)) ≠ 1 := by simp [Fin.ext_iff]
  -- `J` is unimodular
  have hαβ : IsUnit (α * β - 1 * 1) := by
    have : α * β - 1 * 1 = -(1 - α * β) := by ring
    rw [this, IsUnit.neg_iff]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hα))
  have hJmod := span_pair_isModular Q one_ne_zero hαβ (by rw [hQx, one_mul]) (by rw [hQy, one_mul])
    (by rw [hxy, map_one, mul_one])
  rw [← Submodule.one_eq_span] at hJmod
  -- `M = J ⊥ K₂` and 93:19
  have horthJ1 : ∀ u ∈ J, ∀ v ∈ Ks 1, bil Q u v = 0 := fun u hu v hv =>
    hK.split.orth 0 1 h01 u (hJK0 hu) v hv
  have hJfg : J.FG := FG.of_le hK0fg hJK0
  have hJreg : IsRegular Q J := hJmod.1.isRegular Q hJfg
  have hM : IsOrthSum Q (J ⊔ Ks 1) J (Ks 1) := ⟨horthJ1, disjoint_of_orth Q hJreg horthJ1, rfl⟩
  have hs1lt : scale Q (Ks 1) < 1 := hs0 ▸ hK.scale_strictAnti (show (0 : Fin (t + 2)) < 1 by simp [Fin.lt_def])
  have ha := le_maximal_of_lt_one (scale_fg Q hK1fg) (hK.modular 1).1 hs1lt
  have hαβ' : IsUnit (-1 + α * β) := by
    have : -1 + α * β = α * β - 1 * 1 := by ring
    rw [this]; exact hαβ
  obtain ⟨x', y', K'', hQx', hx'y', hQy', hM', -⟩ :=
    omeara93_19 Q hHil h2p hM rfl hQx hxy hQy hαβ' hK1fg (hK.modular 1) ha hrk1 hγ
  -- `J' = 𝔬x' + 𝔬y'` is unimodular of rank 2
  have hJ'mod := span_pair_isModular Q one_ne_zero hdet (by rw [hQx', one_mul, map_add])
    (by rw [hQy', one_mul]) (by rw [hx'y', map_one, mul_one])
  rw [← Submodule.one_eq_span] at hJ'mod
  set J' : Submodule R V := span R {x', y'} with hJ'def
  have hCfg : C.FG := FG.of_le hK0fg hCK0
  have hJ0 : J ≠ ⊥ := by
    intro h
    have := hJmod.2
    rw [← hJdef, h, finrank_bot] at this
    exact absurd this (by norm_num)
  -- the new first component `A = J' ⊥ C`
  have hJ'M : J' ≤ J ⊔ Ks 1 := hM'.sup_eq ▸ le_sup_left
  have hK''M : K'' ≤ J ⊔ Ks 1 := hM'.sup_eq ▸ le_sup_right
  have horthCM : ∀ u ∈ C, ∀ v ∈ J ⊔ Ks 1, bil Q u v = 0 := by
    intro u hu v hv
    obtain ⟨a, ha', b, hb, rfl⟩ := mem_sup.mp hv
    rw [bil_add_right, bil_comm Q u a, hJC.orth a ha' u hu, hK.split.orth 0 1 h01 u (hCK0 hu) b hb, add_zero]
  set A : Submodule R V := J' ⊔ C with hAdef
  have horthJ'C : ∀ u ∈ J', ∀ v ∈ C, bil Q u v = 0 := fun u hu v hv => by
    rw [bil_comm]; exact horthCM v hv u (hJ'M hu)
  have hJ'fg : J'.FG := Submodule.fg_span (Set.toFinite _)
  have hAmod : IsModular Q 1 A ∧ finrank R A = finrank R J' + finrank R C := by
    by_cases hC0 : C = ⊥
    · rw [hAdef, hC0, sup_bot_eq, finrank_bot, add_zero]
      exact ⟨hJ'mod.1, rfl⟩
    · have hCmod : IsModular Q 1 C :=
        ((Dedekind.isModular_iff_of_isOrthSum Q hJC hJfg hCfg hJ0 hC0).mp (hs0 ▸ hK.modular 0)).2
      exact isModular_sup Q hJ'mod.1 hCmod hJ'fg hCfg horthJ'C
  -- the rest `C' = K'' ⊔ T`
  set T : Submodule R V := ⨆ j : Fin t, Ks j.succ.succ with hTdef
  have horthT : ∀ i : Fin (t + 2), i = 0 ∨ i = 1 → ∀ u ∈ Ks i, ∀ v ∈ T, bil Q u v = 0 := by
    intro i hi u hu v hv
    refine iSup_induction (fun j : Fin t => Ks j.succ.succ) (motive := fun v => bil Q u v = 0) hv ?_
      (by simp [bil]) (fun a b ha hb => by rw [bil_add_right, ha, hb, add_zero])
    intro j w hw
    refine hK.split.orth i j.succ.succ ?_ u hu w hw
    rcases hi with rfl | rfl <;> simp [Fin.ext_iff]
  set C' : Submodule R V := K'' ⊔ T with hC'def
  have horthAC' : ∀ u ∈ A, ∀ v ∈ C', bil Q u v = 0 := by
    intro u hu v hv
    obtain ⟨a, ha', c, hc, rfl⟩ := mem_sup.mp hu
    obtain ⟨k, hk, w, hw, rfl⟩ := mem_sup.mp hv
    have hJ'T : ∀ a ∈ J', bil Q a w = 0 := by
      intro a ha'
      obtain ⟨j, hj, k1, hk1, hjk⟩ := mem_sup.mp (hJ'M ha')
      rw [← hjk, bil_add_left, horthT 0 (Or.inl rfl) j (hJK0 hj) w hw, horthT 1 (Or.inr rfl) k1 hk1 w hw,
        add_zero]
    rw [bil_add_left, bil_add_right, bil_add_right, hM'.orth a ha' k hk, hJ'T a ha', horthCM c hc k (hK''M hk),
      horthT 0 (Or.inl rfl) c (hCK0 hc) w hw]
    ring
  have hAreg : IsRegular Q A := hAmod.1.isRegular Q (hJ'fg.sup hCfg)
  have hsupK : A ⊔ C' = K := by
    have h1 : J' ⊔ K'' = J ⊔ Ks 1 := hM'.sup_eq
    have h2 : (⨆ i, Ks i) = Ks 0 ⊔ (Ks 1 ⊔ T) := by
      rw [SuffStep.iSup_eq_zero_sup, SuffStep.tailLat, SuffStep.iSup_eq_zero_sup (fun k : Fin (t + 1) => Ks k.succ),
        SuffStep.tailLat]
      rfl
    rw [← hK.split.iSup_eq, h2, ← hJC.sup_eq, hAdef, hC'def]
    calc J' ⊔ C ⊔ (K'' ⊔ T) = (J' ⊔ K'') ⊔ C ⊔ T := by ac_rfl
      _ = (J ⊔ Ks 1) ⊔ C ⊔ T := by rw [h1]
      _ = J ⊔ C ⊔ (Ks 1 ⊔ T) := by ac_rfl
  have hAC' : IsOrthSum Q K A C' := ⟨horthAC', disjoint_of_orth Q hAreg horthAC', hsupK⟩
  have hrk0 : finrank R A = finrank R (Ks 0) := by
    rw [hAmod.2, hJ'mod.2, isOrthSum_finrank Q hJC hK0fg, hJmod.2]
  obtain ⟨Cs, -, hJs, hCs⟩ := exists_jordan_cons_of_compl Q hKfg hK hAC' (hs0 ▸ hAmod.1) hrk0
  refine ⟨Fin.cons A Cs, hJs, fun i => ?_, x', y', by rw [hQx', map_add], hx'y', hQy', ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]; exact ⟨hAmod.1.2.1.trans hs0.symm, hrk0⟩
    · simp only [Fin.cons_succ]; exact hCs i
  · simp only [Fin.cons_zero]
    exact ⟨horthJ'C, disjoint_of_orth Q (hJ'mod.1.isRegular Q hJ'fg) horthJ'C, rfl⟩

end Shift

section Blocks

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open D18 Sat93 CoreSplit NecBlock Merge28

omit [HenselianLocalRing R] [Finite (ResidueField R)] [CharZero F] in
include F in
/-- A finitely generated lattice of rank $0$ is zero. -/
theorem eq_bot_of_finrank_eq_zero {L : Submodule R V} (hfg : L.FG) (h : finrank R L = 0) : L = ⊥ := by
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hfg
  rw [← span_basis_eq b, span_eq_bot]
  rintro _ ⟨p, rfl⟩
  exact (Fin.cast h p).elim0

omit [HenselianLocalRing R] [Finite (ResidueField R)] [CharZero F] in
/-- Adding an orthogonal hyperbolic pair to a block base. -/
theorem isBlockBase_cons {B : Submodule R V} {m : ℕ} {x : Fin m → V × V} (hx : IsBlockBase Q B x) {e f : V}
    (hf : Q f = 0) (hef : bil Q e f = 1) (horth : ∀ u ∈ span R {e, f}, ∀ v ∈ B, bil Q u v = 0) :
    IsBlockBase Q (span R {e, f} ⊔ B) (Fin.cons (e, f) x : Fin (m + 1) → V × V) := by
  obtain ⟨hsp, hQ0, h1, hee, hef', hff⟩ := hx
  have heS : e ∈ span R {e, f} := subset_span (by simp)
  have hfS : f ∈ span R {e, f} := subset_span (by simp)
  have h1B : ∀ k, (x k).1 ∈ B := fun k => hsp ▸ subset_span (Or.inl ⟨k, rfl⟩)
  have h2B : ∀ k, (x k).2 ∈ B := fun k => hsp ▸ subset_span (Or.inr ⟨k, rfl⟩)
  have o : ∀ u ∈ span R {e, f}, ∀ k, bil Q u (x k).1 = 0 ∧ bil Q u (x k).2 = 0 ∧ bil Q (x k).1 u = 0 ∧
      bil Q (x k).2 u = 0 := fun u hu k =>
    ⟨horth u hu _ (h1B k), horth u hu _ (h2B k), by rw [bil_comm]; exact horth u hu _ (h1B k),
      by rw [bil_comm]; exact horth u hu _ (h2B k)⟩
  refine ⟨by rw [pairSpan_cons, hsp], fun k => ?_, fun k => ?_, fun k l hkl => ?_, fun k l hkl => ?_,
    fun k l hkl => ?_⟩
  · refine Fin.cases ?_ (fun k => ?_) k <;> simp [hf, hQ0]
  · refine Fin.cases ?_ (fun k => ?_) k <;> simp [hef, h1]
  · refine Fin.cases (fun hkl => ?_) (fun k hkl => ?_) k hkl <;>
      refine Fin.cases (fun hkl' => ?_) (fun l hkl' => ?_) l hkl
    · exact absurd rfl hkl'
    · simpa using (o e heS l).1
    · simpa using (o e heS k).2.2.1
    · simpa using hee k l (fun h => hkl' (by rw [h]))
  · refine Fin.cases (fun hkl => ?_) (fun k hkl => ?_) k hkl <;>
      refine Fin.cases (fun hkl' => ?_) (fun l hkl' => ?_) l hkl
    · exact absurd rfl hkl'
    · simpa using (o e heS l).2.1
    · simpa using (o f hfS k).2.2.1
    · simpa using hef' k l (fun h => hkl' (by rw [h]))
  · refine Fin.cases (fun hkl => ?_) (fun k hkl => ?_) k hkl <;>
      refine Fin.cases (fun hkl' => ?_) (fun l hkl' => ?_) l hkl
    · exact absurd rfl hkl'
    · simpa using (o f hfS l).2.1
    · simpa using (o f hfS k).2.2.2
    · simpa using hff k l (fun h => hkl' (by rw [h]))

/-- **The first Jordan component made hyperbolic, block by block** (O'Meara 1963, §93F, step 4, p. 274, and §93G,
p. 278, "hence by Proposition 93:19 $K_1 \perp K_2 \cong \langle A(2^{u_1}, 0)\rangle \perp \langle A(2, 0)\rangle
\perp K_2'$"): let $K = K_1 \perp \cdots \perp K_t$ be a Jordan splitting ($t \ge 2$) with $K_1$ unimodular of even
rank and $\dim K_2 \ge 3$, and suppose that for every Jordan splitting $K'$ of $K$ with the same scales and ranks,
$\mathfrak p \subseteq \mathfrak gK_2'$. Then $K$ has such a Jordan splitting whose first component has a block base
$A(c_1, 0) \perp \cdots \perp A(c_m, 0)$ (`IsBlockBase`). Each step splits off $\mathfrak oy + \mathfrak ox$ with
$B(y, x) = 1$, $Q(x) \in \mathfrak p$ (`exists_pair_small`) and moves $Q(x)$ to $0$ by 93:19
(`exists_shift_first`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 4, p. 274; §93G, p. 278 (93:19 applied block by block)"]
theorem exists_blocks_first (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R)) {K : Submodule R V}
    (hKfg : K.FG) {t : ℕ} {Ks : Fin (t + 2) → Submodule R V} (hK : IsJordanSplitting Q K Ks)
    (hs0 : scale Q (Ks 0) = 1) (hev : Even (finrank R (Ks 0))) (hrk1 : 3 ≤ finrank R (Ks 1))
    (hg : ∀ Ks' : Fin (t + 2) → Submodule R V, IsJordanSplitting Q K Ks' →
      (∀ i, scale Q (Ks' i) = scale Q (Ks i) ∧ finrank R (Ks' i) = finrank R (Ks i)) →
      ∀ μ ∈ maximalIdeal R, algebraMap R F μ ∈ normGroup Q (Ks' 1)) :
    ∃ Ks' : Fin (t + 2) → Submodule R V, IsJordanSplitting Q K Ks' ∧
      (∀ i, scale Q (Ks' i) = scale Q (Ks i) ∧ finrank R (Ks' i) = finrank R (Ks i)) ∧
      ∃ m, ∃ x : Fin m → V × V, IsBlockBase Q (Ks' 0) x := by
  -- the invariant: `Ks' 0 = B ⊥ C`, `B` with a block base, `C` unimodular of rank `k`
  suffices H : ∀ k, ∀ Ks' : Fin (t + 2) → Submodule R V, IsJordanSplitting Q K Ks' →
      (∀ i, scale Q (Ks' i) = scale Q (Ks i) ∧ finrank R (Ks' i) = finrank R (Ks i)) →
      ∀ B C : Submodule R V, IsOrthSum Q (Ks' 0) B C → (∃ m, ∃ x : Fin m → V × V, IsBlockBase Q B x) →
      (C = ⊥ ∨ IsUnimodular Q C) → finrank R C = k → Even k →
      ∃ Ks'' : Fin (t + 2) → Submodule R V, IsJordanSplitting Q K Ks'' ∧
        (∀ i, scale Q (Ks'' i) = scale Q (Ks i) ∧ finrank R (Ks'' i) = finrank R (Ks i)) ∧
        ∃ m, ∃ x : Fin m → V × V, IsBlockBase Q (Ks'' 0) x by
    have hb0 : IsBlockBase Q (⊥ : Submodule R V) (Fin.elim0 : Fin 0 → V × V) :=
      ⟨by simp [pairSpan], fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
        fun k => k.elim0⟩
    have hsplit : IsOrthSum Q (Ks 0) ⊥ (Ks 0) :=
      ⟨fun x hx y _ => by rw [(mem_bot R).mp hx]; simp [bil], disjoint_bot_left, bot_sup_eq (Ks 0)⟩
    exact H _ Ks hK (fun i => ⟨rfl, rfl⟩) ⊥ (Ks 0) hsplit ⟨0, _, hb0⟩
      (Or.inr (by have := hK.modular 0; rwa [hs0] at this)) rfl hev
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Ks' hK' hsame B C hBC ⟨m, x, hx⟩ hC hk hev'
  have hle : ∀ j, Ks' j ≤ K := fun j => hK'.split.iSup_eq ▸ le_iSup Ks' j
  have hK0fg : (Ks' 0).FG := FG.of_le hKfg (hle 0)
  have hCK0 : C ≤ Ks' 0 := hBC.sup_eq ▸ le_sup_right
  have hBK0 : B ≤ Ks' 0 := hBC.sup_eq ▸ le_sup_left
  have hCfg : C.FG := FG.of_le hK0fg hCK0
  have hs0' : scale Q (Ks' 0) = 1 := (hsame 0).1.trans hs0
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `C = 0`, so `Ks' 0 = B`
    have hC0 : C = ⊥ := eq_bot_of_finrank_eq_zero (F := F) hCfg (hk.trans hk0)
    refine ⟨Ks', hK', hsame, m, x, ?_⟩
    have : Ks' 0 = B := by rw [← hBC.sup_eq, hC0, sup_bot_eq]
    rw [this]; exact hx
  · have hCU : IsUnimodular Q C := by
      rcases hC with h | h
      · exfalso; rw [h, finrank_bot] at hk; omega
      · exact h
    have hk2 : 2 ≤ k := by obtain ⟨j, hj⟩ := hev'; omega
    obtain ⟨u, hu, s, hs, hus, α, hα, hQs⟩ := exists_pair_small Q h2p hCfg hCU (hk ▸ hk2)
    -- `J = 𝔬s + 𝔬u` splits `C`
    obtain ⟨β, hβ⟩ := bil_integral Q hCU hu hu
    rw [bil_self] at hβ
    have hsu : bil Q s u = 1 := by rw [bil_comm]; exact hus
    have hαβ : IsUnit (α * β - 1 * 1) := by
      have : α * β - 1 * 1 = -(1 - α * β) := by ring
      rw [this, IsUnit.neg_iff]
      exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
        ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hα))
    have hJmod := span_pair_isModular Q one_ne_zero hαβ (by rw [hQs, one_mul]) (by rw [hβ, one_mul])
      (by rw [hsu, map_one, mul_one])
    rw [← Submodule.one_eq_span] at hJmod
    have hJC : span R {s, u} ≤ C := span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact hs
      · exact hu)
    obtain ⟨C', hC'⟩ := splits_of_isModular_of_scale_eq Q hJC hJmod.1 (Submodule.fg_span (Set.toFinite _))
      hCU.2.1
    -- `Ks' 0 = J ⊥ (B ⊔ C')`
    have hC'C : C' ≤ C := hC'.sup_eq ▸ le_sup_right
    have horthJB : ∀ a ∈ span R {s, u}, ∀ b ∈ B, bil Q a b = 0 := fun a ha b hb => by
      rw [bil_comm]; exact hBC.orth b hb a (hJC ha)
    have horthJ : ∀ a ∈ span R {s, u}, ∀ v ∈ B ⊔ C', bil Q a v = 0 := by
      intro a ha v hv
      obtain ⟨b, hb, c, hc, rfl⟩ := mem_sup.mp hv
      rw [bil_add_right, horthJB a ha b hb, hC'.orth a ha c hc, add_zero]
    have hJreg : IsRegular Q (span R {s, u}) :=
      hJmod.1.isRegular Q (Submodule.fg_span (Set.toFinite _))
    have hsplit : IsOrthSum Q (Ks' 0) (span R {s, u}) (B ⊔ C') := by
      refine ⟨horthJ, disjoint_of_orth Q hJreg horthJ, ?_⟩
      rw [← hBC.sup_eq, ← hC'.sup_eq]; ac_rfl
    obtain ⟨Ks'', hK'', hsame'', x', y', hQx', hx'y', hQy', hsplit''⟩ :=
      exists_shift_first Q hHil h2p hKfg hK' hs0' hsplit hQs hsu hβ hα
        ((hsame 1).2 ▸ hrk1) (γ₀ := -α) (hg Ks' hK' hsame (-α) (neg_mem hα))
        (by simp)
    rw [add_neg_cancel, map_zero] at hQx'
    -- the new block `(y', x')`
    have hyx : bil Q y' x' = 1 := by rw [bil_comm]; exact hx'y'
    have hpair : span R {y', x'} = span R {x', y'} := by rw [Set.pair_comm]
    have horthB : ∀ a ∈ span R {y', x'}, ∀ b ∈ B, bil Q a b = 0 := by
      intro a ha b hb
      rw [hpair] at ha
      exact hsplit''.orth a ha b (mem_sup_left hb)
    have hx' := isBlockBase_cons Q hx hQx' hyx horthB
    -- `Ks'' 0 = (𝔬y' + 𝔬x' ⊥ B) ⊥ C'`
    have hJ'C' : ∀ a ∈ span R {y', x'}, ∀ c ∈ C', bil Q a c = 0 := by
      intro a ha c hc
      rw [hpair] at ha
      exact hsplit''.orth a ha c (mem_sup_right hc)
    have hBC' : ∀ b ∈ B, ∀ c ∈ C', bil Q b c = 0 := fun b hb c hc => hBC.orth b hb c (hC'C hc)
    have horthB' : ∀ c ∈ C', ∀ a ∈ span R {y', x'} ⊔ B, bil Q c a = 0 := by
      intro c hc a ha
      obtain ⟨p, hp, b, hb, rfl⟩ := mem_sup.mp ha
      rw [bil_add_right, bil_comm Q c p, hJ'C' p hp c hc, bil_comm Q c b, hBC' b hb c hc, add_zero]
    have hJfg : (span R {s, u}).FG := Submodule.fg_span (Set.toFinite _)
    have hC'fg : C'.FG := FG.of_le hCfg hC'C
    have hC'U : C' = ⊥ ∨ IsUnimodular Q C' := by
      by_cases h0 : C' = ⊥
      · exact Or.inl h0
      · have hJ0 : span R {s, u} ≠ ⊥ := by
          intro h; have := hJmod.2; rw [h, finrank_bot] at this; exact absurd this (by norm_num)
        exact Or.inr ((Dedekind.isModular_iff_of_isOrthSum Q hC' hJfg hC'fg hJ0 h0).mp hCU).2
    have hC'reg : IsRegular Q C' := by
      rcases hC'U with h | h
      · rw [h]; intro z hz _; exact (mem_bot R).mp hz
      · exact IsModular.isRegular Q h hC'fg
    have hnew : IsOrthSum Q (Ks'' 0) (span R {y', x'} ⊔ B) C' := by
      refine ⟨fun a ha c hc => by rw [bil_comm]; exact horthB' c hc a ha,
        (disjoint_of_orth Q hC'reg horthB').symm, ?_⟩
      rw [hpair, ← hsplit''.sup_eq]; ac_rfl
    have hrkC : finrank R C = 2 + finrank R C' := by rw [isOrthSum_finrank Q hC' hCfg, hJmod.2]
    obtain ⟨Ks₃, hK₃, hsame₃, hres⟩ := ih (k - 2) (by omega) Ks'' hK''
      (fun i => ⟨(hsame'' i).1.trans (hsame i).1, (hsame'' i).2.trans (hsame i).2⟩)
      _ C' hnew ⟨m + 1, _, hx'⟩ hC'U (by omega) (by obtain ⟨j, hj⟩ := hev'; exact ⟨j - 1, by omega⟩)
    exact ⟨Ks₃, hK₃, hsame₃, hres⟩

end Blocks

section Lagrangian

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open NecBlock Merge28 CoreHyp

/-- **A block base spans a hyperbolic space**: if $B$ has a block base $(e_k, f_k)$ (matrix
$A(c_1, 0) \perp \cdots \perp A(c_m, 0)$), the span of the $f_k$ is a totally isotropic subspace of $FB$ of
dimension $m = \frac12\operatorname{rank} B$. -/
theorem exists_lagrangian_of_blockBase {B : Submodule R V} {m : ℕ} {x : Fin m → V × V} (hx : IsBlockBase Q B x) :
    ∃ T : Submodule F V, (∀ v ∈ T, Q v = 0) ∧ (∀ v ∈ T, v ∈ span F (B : Set V)) ∧
      finrank R B ≤ 2 * finrank F T := by
  obtain ⟨hsp, hQ0, -, -, -, hff⟩ := id hx
  set f : Fin m → V := fun k => (x k).2 with hfdef
  refine ⟨span F (Set.range f), ?_, ?_, ?_⟩
  · have hbil : ∀ u ∈ span F (Set.range f), ∀ w ∈ span F (Set.range f), bil Q u w = 0 := by
      intro u hu w hw
      induction hu using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨k, rfl⟩ := ha
        induction hw using Submodule.span_induction with
        | mem b hb =>
          obtain ⟨l, rfl⟩ := hb
          by_cases hkl : k = l
          · subst hkl; rw [bil_self]; exact hQ0 k
          · exact hff k l hkl
        | zero => simp [bil]
        | add a b _ _ ha hb => rw [bil_add_right, ha, hb, add_zero]
        | smul c a _ ha => rw [bil_smul_right, ha, mul_zero]
      | zero => simp [bil]
      | add a b _ _ ha hb => rw [bil_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [bil_smul_left, ha, mul_zero]
    intro v hv
    rw [← bil_self]; exact hbil v hv v hv
  · intro v hv
    refine span_le.mpr ?_ hv
    rintro _ ⟨k, rfl⟩
    exact subset_span (hsp ▸ subset_span (Or.inr ⟨k, rfl⟩) : (x k).2 ∈ B)
  · have hli : LinearIndependent F (hypVec Q x) :=
      linearIndependent_of_det_gram_ne_zero (R := F) Q (det_gram_hypVec_ne_zero Q hx)
    have hlf : LinearIndependent F f := hli.comp Sum.inr Sum.inr_injective
    rw [finrank_of_blockBase Q hx, finrank_span_eq_card hlf, Fintype.card_fin]

end Lagrangian

section TwoAdic

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

open D18 Sat93 CoreSplit NecBlock Merge28 Suff28 CoreHyp

omit [HenselianLocalRing R] [Finite (ResidueField R)] [CharZero F] in
/-- A modular lattice is not zero. -/
theorem ne_bot_of_isModular {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    (Q : QuadraticForm F V) {a : Submodule R F} {L : Submodule R V} (h : IsModular Q a L) : L ≠ ⊥ := by
  rintro rfl
  apply h.1
  rw [← h.2.1, scale, span_eq_bot]
  rintro _ ⟨x, hx, y, -, rfl⟩
  rw [(mem_bot R).mp hx]; simp [bil]

/-- **The core of 93:28 over a 2-adic field when $\mathfrak n_2 = 2\mathfrak o$** (O'Meara 1963, §93G, proof of 93:29,
sufficiency, p. 278: "First consider the case $\mathfrak n_2 = 2\mathfrak o$ ... hence by Proposition 93:19
$K_1 \perp K_2 \cong \langle A(2^{u_1}, 0)\rangle \perp \langle A(2, 0)\rangle \perp K_2'$"): in the situation of
`CoreCases.SuffCoreHypRest`, over a field where $2$ is prime, if $2 \in \mathfrak n_2 = a_2\mathfrak o$ ($0$-based:
`a 1`), then $K$ has a saturated Jordan splitting whose first space is hyperbolic. Over a 2-adic field every
Jordan splitting is saturated and $\mathfrak gK_2' = \mathfrak nK_2' = \mathfrak n_2 = 2\mathfrak o \supseteq
\mathfrak p$ for every Jordan splitting, so `exists_blocks_first` applies. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (the case n₂ = 2o)"]
theorem core_twoAdic_two (hHil : PadicClass.LocalHilbertField F) (h2 : IsTwoAdic R) {V : Type v}
    [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (h2p : ¬ IsUnit (2 : R)) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
    (a : Fin (m + 2) → F) (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks) (hd : ∀ k, 3 ≤ finrank R (Ls k))
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
      finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : scale Q (Ls 0) = 1) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hn : (2 : F) ∈ R ∙ a 1) :
    ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
      ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
        finrank R (Ks' 0) ≤ 2 * finrank F T := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hKreg : IsRegular Q K := isRegular_of_lattice_max Q hQ ‹K.IsLattice F›
  obtain ⟨⟨h0, hTy⟩, -, haK⟩ := hS
  have hc : ∀ k : Fin (m + 2), Fin.cast h0 k = k := fun k => Fin.ext (by simp)
  have hrk : ∀ k, finrank R (Ls k) = finrank R (Ks k) := fun k => by have := (hTy k).1; rwa [hc] at this
  have hscK : ∀ k, scale Q (Ls k) = scale Q (Ks k) := fun k => by have := (hTy k).2.1; rwa [hc] at this
  have hs0 : scale Q (Ks 0) = 1 := (hscK 0).symm.trans hsc
  -- `dim K₁` is even: `L₁` lies in a lattice with a block base of the same rank (93:3)
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLs.1.split.iSup_eq ▸ le_iSup Ls 0)
  have hev : Even (finrank R (Ks 0)) := by
    obtain ⟨T, hTiso, hTL, hTdim⟩ := hT 0
    obtain ⟨B, -, -, -, -, -, hrB, mB, xB, hxB⟩ := exists_unimodular_blocks Q hL0fg
      ((hLs.1.modular 0).isRegular Q hL0fg) hsc hTiso hTL hTdim
    rw [← hrk 0, ← hrB, finrank_of_blockBase Q hxB]
    exact ⟨mB, by ring⟩
  have hrk1 : 3 ≤ finrank R (Ks 1) := hrk 1 ▸ hd 1
  -- `𝔭 ⊆ 𝔤K₂'` for every Jordan splitting with the same scales
  have hmax : maximalIdeal R = Ideal.span {(2 : R)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer 2).mp h2
  have hg : ∀ Ks' : Fin (m + 2) → Submodule R V, IsJordanSplitting Q K Ks' →
      (∀ i, scale Q (Ks' i) = scale Q (Ks i) ∧ finrank R (Ks' i) = finrank R (Ks i)) →
      ∀ μ ∈ maximalIdeal R, algebraMap R F μ ∈ normGroup Q (Ks' 1) := by
    intro Ks' hK' hsame μ hμ
    have hle : Ks' 1 ≤ K := hK'.split.iSup_eq ▸ le_iSup Ks' 1
    have h1fg : (Ks' 1).FG := FG.of_le hKfg hle
    have hset := normGroup_eq_normIdeal_twoAdic Q h2 h1fg ((hK'.modular 1).isRegular Q h1fg)
      (ne_bot_of_isModular Q (hK'.modular 1))
    have hn' : normIdeal Q (Ks' 1) = R ∙ a 1 := by
      rw [← fundNormIdeal_eq_normIdeal_twoAdic Q h2 hKfg hK' 1, (haK 1).2]
      simp only [fundNormIdeal, fundSub, (hsame 1).1]
    rw [hmax] at hμ
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hμ
    have : algebraMap R F (r * 2) ∈ normIdeal Q (Ks' 1) := by
      rw [hn', map_mul, map_ofNat, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hn
    rw [← SetLike.mem_coe, hset]; exact this
  obtain ⟨Ks', hK', hsame, mb, xb, hxb⟩ :=
    exists_blocks_first Q hHil h2p hKfg hKs.1 hs0 hev hrk1 hg
  refine ⟨Ks', ⟨hK', fun i => ?_⟩, exists_lagrangian_of_blockBase Q hxb⟩
  have hle : Ks' i ≤ K := hK'.split.iSup_eq ▸ le_iSup Ks' i
  have hifg : (Ks' i).FG := FG.of_le hKfg hle
  apply SetLike.coe_injective
  rw [normGroup_eq_normIdeal_twoAdic Q h2 hifg ((hK'.modular i).isRegular Q hifg)
      (ne_bot_of_isModular Q (hK'.modular i)),
    fundNormGroup_eq_normIdeal_twoAdic Q h2 hKfg hKreg hK' i]

end TwoAdic

section TwoAdicCases

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

open Nec93

/-- **The decided case over a 2-adic field** (O'Meara 1963, §93G, proof of 93:29, p. 279, "Finally let
$\mathfrak n_2 \subseteq 8\mathfrak o$ ... $\mathfrak n_2 \subseteq 8\mathfrak o \subsetneq 4\mathfrak n_1$"): if the
first component is unimodular and $\mathfrak f_1 \subseteq 8\mathfrak o$, then $\mathfrak f_1 \subseteq 4\mathfrak p$
and condition (iii) of 93:28 is required ($\mathfrak f_1 \subsetneq 4a_1\mathfrak w_1^{-1}$). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 279 (n₂ ⊆ 8o: condition (iii) applies)"]
theorem decided_of_le_eight (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (i j : Fin t) (hij : (j : ℕ) = i + 1)
    (hs : scale Q (Ls i) = 1) {a : F} (ha : R ∙ a = normIdeal Q (Ls i)) (h8 : fIdeal Q L Ls i j ≤ R ∙ (8 : F)) :
    (∀ x ∈ fIdeal Q L Ls i j, ∃ μ ∈ maximalIdeal R, x = 4 * algebraMap R F μ) ∧
      fIdeal Q L Ls i j < (4 * a) • (1 / fundWeight Q L Ls i) := by
  have hπ := twoAdic_irreducible h2
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have h2m : (2 : R) ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := mem_span_singleton.mp (h8 hx)
    refine ⟨2 * r, Ideal.mul_mem_right _ _ h2m, ?_⟩
    rw [Algebra.smul_def, map_mul, map_ofNat]; ring
  obtain ⟨u, σ, τ, k, hu, hσ0, hτ0, hσ, hτ, hk, p1, p2, q1, q2, hst, hcase⟩ :=
    exists_data Q h2 hfg hreg hL hij
  have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
  -- `ord σ = 0`
  have hσ1 : R ∙ σ = R ∙ ((2 : F) ^ (0 : ℤ)) := by rw [← hσ, hs, zpow_zero, ← Submodule.one_eq_span]
  have hdσ : dord hπ σ = 0 := by
    have h1 : σ ∈ R ∙ ((2 : F) ^ (0 : ℤ)) := hσ1 ▸ mem_span_singleton_self σ
    have h2' : (2 : F) ^ (0 : ℤ) ∈ R ∙ σ := hσ1 ▸ mem_span_singleton_self _
    rw [mem_span_two_zpow_iff h2 hσ0] at h1
    rw [mem_span_iff hπ (z2 0) hσ0, dord_two_zpow h2] at h2'
    omega
  have hA : R ∙ (4 * a) = R ∙ ((2 : F) ^ (u i + 2)) := by
    rw [← FIdealAux.smul_span_singleton, ha, ← hu i, FIdealAux.smul_span_singleton, four_mul_two_zpow]
  have hw : fundWeight Q L Ls i = R ∙ (2 * σ) := by
    rw [fundWeight_eq_two_smul_scale_twoAdic Q h2 hfg hreg hL i, hσ, FIdealAux.smul_span_singleton]
  have hσ2 : (2 : F) * σ ≠ 0 := mul_ne_zero h2F hσ0
  have hrhs : (4 * a) • (1 / fundWeight Q L Ls i) = R ∙ ((2 : F) ^ (u i + 2) * (2 * σ)⁻¹) := by
    rw [hw, one_div_span hσ2, FundAux.smul_eq_span_mul, hA, FIdealAux.span_mul_span']
  rw [hrhs]
  have hg0 : (2 : F) ^ (u i + 2) * (2 * σ)⁻¹ ≠ 0 := mul_ne_zero (z2 _) (inv_ne_zero hσ2)
  have hdg : dord hπ ((2 : F) ^ (u i + 2) * (2 * σ)⁻¹) = u i + 2 - (1 + dord hπ σ) := by
    rw [dord_mul hπ (z2 _) (inv_ne_zero hσ2), B63.dord_inv' hπ hσ2, dord_mul hπ h2F hσ0,
      dord_two_zpow h2, twoAdic_dord_two h2]
    ring
  have key : ∀ z ∈ fIdeal Q L Ls i j, z ≠ 0 →
      dord hπ ((2 : F) ^ (u i + 2) * (2 * σ)⁻¹) + 1 ≤ dord hπ z := by
    intro z hz hz0
    have h8' : z ∈ R ∙ ((2 : F) ^ (3 : ℤ)) := by
      have : (8 : F) = (2 : F) ^ (3 : ℤ) := by norm_num
      rw [← this]; exact h8 hz
    rw [mem_span_two_zpow_iff h2 hz0] at h8'
    rw [hdg]
    omega
  refine lt_of_le_of_ne ?_ ?_
  · intro z hz
    by_cases hz0 : z = 0
    · rw [hz0]; exact zero_mem _
    rw [mem_span_iff hπ hz0 hg0]
    have := key z hz hz0
    omega
  · intro heq
    have hmem : (2 : F) ^ (u i + 2) * (2 * σ)⁻¹ ∈ fIdeal Q L Ls i j := by
      rw [heq]; exact mem_span_singleton_self _
    have := key _ hmem hg0
    omega

/-- **The three cases over a 2-adic field** (O'Meara 1963, §93G, proof of 93:29, pp. 278–279): for a Jordan splitting
with unimodular first component and norm generators $a_1$, $a_2$ ($0$-based `a 0`, `a 1`) of the first two components,
either $\mathfrak n_2 = a_2\mathfrak o \ni 2$, or $\mathfrak n_1 = \mathfrak o$ and $\mathfrak n_2 = 4\mathfrak o$, or
$\mathfrak f_1 \subseteq 8\mathfrak o$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, pp. 278–279 (the cases n₂ = 2o, n₂ = 4o, n₂ ⊆ 8o)"]
theorem twoAdic_cases (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ}
    {Ls : Fin (t + 2) → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hs : scale Q (Ls 0) = 1) {a : Fin (t + 2) → F}
    (ha : ∀ i, R ∙ a i = normIdeal Q (Ls i)) :
    (2 : F) ∈ R ∙ a 1 ∨ (R ∙ a 0 = 1 ∧ R ∙ a 1 = R ∙ (4 : F)) ∨ fIdeal Q L Ls 0 1 ≤ R ∙ (8 : F) := by
  have hπ := twoAdic_irreducible h2
  obtain ⟨u, σ, τ, k, hu, hσ0, hτ0, hσ, hτ, hk, p1, p2, q1, q2, hst, hcase⟩ :=
    exists_data Q h2 hfg hreg hL (i := 0) (j := 1) (by simp)
  have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
  have hσ1 : R ∙ σ = R ∙ ((2 : F) ^ (0 : ℤ)) := by rw [← hσ, hs, zpow_zero, ← Submodule.one_eq_span]
  have hdσ : dord hπ σ = 0 := by
    have h1 : σ ∈ R ∙ ((2 : F) ^ (0 : ℤ)) := hσ1 ▸ mem_span_singleton_self σ
    have h2' : (2 : F) ^ (0 : ℤ) ∈ R ∙ σ := hσ1 ▸ mem_span_singleton_self _
    rw [mem_span_two_zpow_iff h2 hσ0] at h1
    rw [mem_span_iff hπ (z2 0) hσ0, dord_two_zpow h2] at h2'
    omega
  have hf : fIdeal Q L Ls 0 1 = R ∙ ((2 : F) ^ k) := by rw [← hk, hs, one_mul, one_mul]
  have ha0 : R ∙ a 0 = R ∙ ((2 : F) ^ u 0) := (ha 0).trans (hu 0).symm
  have ha1 : R ∙ a 1 = R ∙ ((2 : F) ^ u 1) := (ha 1).trans (hu 1).symm
  by_cases hk3 : 3 ≤ k
  · right; right
    rw [hf, Submodule.span_singleton_le_iff_mem, show (8 : F) = (2 : F) ^ (3 : ℤ) by norm_num,
      mem_span_two_zpow_iff h2 (z2 _), dord_two_zpow h2]
    exact hk3
  · have hcases : u 1 = 1 ∨ (u 0 = 0 ∧ u 1 = 2) := by
      rcases hcase with ⟨_, hk'⟩ | ⟨he, hk'⟩
      · omega
      · obtain ⟨m, hm⟩ := he; omega
    rcases hcases with h1 | ⟨h0, h1⟩
    · left
      rw [ha1, h1, zpow_one]; exact mem_span_singleton_self _
    · right; left
      refine ⟨by rw [ha0, h0, zpow_zero, ← Submodule.one_eq_span], ?_⟩
      rw [ha1, h1]; norm_num

end TwoAdicCases

end QuadFormsKB.OMeara.CoreTwo
