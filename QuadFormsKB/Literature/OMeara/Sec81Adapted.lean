/-
# O'Meara §81B: adapted bases (81:2, Theorem 81:3), rank, almost free lattices

**Setting** (as in `Sec81.lean`): $R$ a Dedekind domain with fraction field $F$, $V$ a vector space over $F$; lattices
in $V$ are finitely generated $R$-submodules; fractional ideals are non-zero finitely generated $R$-submodules of $F$;
$\mathfrak a_x$ is `coeff F L x`.

**Index convention.** O'Meara's base $x_1, \dots, x_n$ is `x 0, …, x (n-1)`, and his condition
$y_i \in Fx_1 + \cdots + Fx_i$ reads `y i ∈ span F (x '' Set.Iic i)`.

**Proves** (O'Meara 1963, §81B, pp. 210–213):
* `exists_coeff_max`, `eq_coeff_smul_sup_inf` (**81:2**), stated for a lattice $L$ in $U \oplus Fx_0$
  (O'Meara: $L$ on $V$ and $U$ a hyperplane, the case `U ⊔ span F {x₀} = ⊤`);
* `exists_adapted_flag` (**Theorem 81:3**, for a lattice $L$ in $V$ and a base of $FL$) and
  `exists_adapted_basis_flag` (81:3 as stated: $L$ on $V$ and a base of $V$); `exists_adapted` (§81B, p. 212: every
  lattice has an adapted base);
* `finrank_eq_finrank_span` (§81B, p. 212: $\operatorname{rank} L = \dim FL$) and `free_of_principal` (p. 213:
  every lattice is free when the class number is $1$).
-/
import QuadFormsKB.Literature.OMeara.Sec81

open Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- A functional on `V` equal to `1` at `x₀ ∉ U` and vanishing on `U`. -/
theorem exists_functional_aux {U : Submodule F V} {x₀ : V} (hx₀ : x₀ ∉ U) :
    ∃ f : V →ₗ[F] F, f x₀ = 1 ∧ ∀ u ∈ U, f u = 0 := by
  obtain ⟨g, hg, hgU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx₀ inferInstance
  refine ⟨(g x₀)⁻¹ • g, by simp [hg], fun u hu => ?_⟩
  have : g u ∈ U.map g := Submodule.mem_map_of_mem hu
  rw [hgU] at this
  have h0 : g u = 0 := by simpa using this
  simp [h0]

/-- For `m ∈ U ⊔ F x₀`, the vector `m - f m • x₀` lies in `U`. -/
theorem sub_smul_mem_aux {U : Submodule F V} {x₀ : V} {f : V →ₗ[F] F} (h1 : f x₀ = 1)
    (h0 : ∀ u ∈ U, f u = 0) {m : V} (hm : m ∈ U ⊔ span F {x₀}) : m - f m • x₀ ∈ U := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have : f (u + c • x₀) = c := by simp [h1, h0 u hu]
  rw [this]
  simpa using hu

/-- **Proposition 81:2, first part** (O'Meara 1963, p. 210). Let $U$ be a subspace of $V$, $x_0 \notin U$, and $L$ a
lattice in $U \oplus Fx_0$ (O'Meara: $L$ on $V$ and $U$ a hyperplane). Among the vectors of $x_0 + U$ there is one
whose coefficient in $L$ is absolutely largest, i.e. contains the coefficient of every vector of $x_0 + U$. -/
@[kb "omeara1963" "§81B, 81:2, p. 210 (an absolutely largest coefficient on x₀ + U)"]
theorem exists_coeff_max {L : Submodule R V} (hL : L.FG) {U : Submodule F V} {x₀ : V} (hx₀ : x₀ ∉ U)
    (hLU : ∀ x ∈ L, x ∈ U ⊔ span F {x₀}) :
    ∃ u₀ ∈ U, ∀ u ∈ U, coeff F L (x₀ + u) ≤ coeff F L (x₀ + u₀) := by
  obtain ⟨f, hf1, hf0⟩ := exists_functional_aux hx₀
  set 𝔞 : Submodule R F := L.map (f.restrictScalars R) with h𝔞
  have h𝔞fg : 𝔞.FG := hL.map _
  have hle : ∀ u ∈ U, coeff F L (x₀ + u) ≤ 𝔞 := by
    intro u hu α hα
    rw [mem_coeff] at hα
    refine ⟨_, hα, ?_⟩
    simp [hf1, hf0 u hu]
  by_cases hbot : 𝔞 = ⊥
  · exact ⟨0, U.zero_mem, fun u hu => (hle u hu).trans (hbot ▸ bot_le)⟩
  · have hinv := mul_one_div_cancel_of_fg h𝔞fg hbot
    have h1 : (1 : F) ∈ 𝔞 * (1 / 𝔞) := by
      rw [hinv]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    have key : ∀ z ∈ 𝔞 * (1 / 𝔞), ∃ m ∈ U ⊔ span F {x₀}, f m = z ∧ ∀ α ∈ 𝔞, α • m ∈ L := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        obtain ⟨l, hl, rfl⟩ := ha
        refine ⟨b • l, Submodule.smul_mem _ _ (hLU l hl), ?_, ?_⟩
        · simp [mul_comm]
        · intro α hα
          obtain ⟨r, hr⟩ := Submodule.mem_one.mp ((Submodule.mem_div_iff_forall_mul_mem.mp hb) α hα)
          rw [smul_comm, smul_smul, ← hr, algebraMap_smul]
          exact L.smul_mem r hl
      · rintro x y ⟨m, hm, rfl, hmL⟩ ⟨m', hm', rfl, hmL'⟩
        exact ⟨m + m', Submodule.add_mem _ hm hm', by simp, fun α hα => by
          rw [smul_add]; exact L.add_mem (hmL α hα) (hmL' α hα)⟩
    obtain ⟨m, hm, hfm, hmL⟩ := key 1 h1
    have hU := sub_smul_mem_aux hf1 hf0 hm
    rw [hfm, one_smul] at hU
    refine ⟨m - x₀, hU, fun u hu => (hle u hu).trans ?_⟩
    intro α hα
    rw [mem_coeff, add_sub_cancel]
    exact hmL α hα

/-- **Proposition 81:2, second part** (O'Meara 1963, pp. 210–211). In the situation of `exists_coeff_max`, let
$x_0 + u_0$ ($u_0 \in U$) have the absolutely largest coefficient $\mathfrak a$ on $x_0 + U$. Then
$L = \mathfrak a(x_0 + u_0) + (L \cap U)$. -/
@[kb "omeara1963" "§81B, 81:2, pp. 210–211 (L = a(x₀ + u₀) + (L ∩ U))"]
theorem eq_coeff_smul_sup_inf {L : Submodule R V} {U : Submodule F V} {x₀ : V}
    (hLU : ∀ x ∈ L, x ∈ U ⊔ span F {x₀}) {u₀ : V} (hu₀ : u₀ ∈ U)
    (hmax : ∀ u ∈ U, coeff F L (x₀ + u) ≤ coeff F L (x₀ + u₀)) :
    L = coeff F L (x₀ + u₀) • span R {x₀ + u₀} ⊔ (L ⊓ U.restrictScalars R) := by
  have hc : ∀ c : F, c ∈ coeff F L (x₀ + u₀) → c • (x₀ + u₀) ∈ L := fun c hc => hc
  apply le_antisymm
  · intro l hl
    obtain ⟨u, hu, w, hw, hlw⟩ := Submodule.mem_sup.mp (hLU l hl)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    by_cases hc0 : c = 0
    · subst hc0
      refine Submodule.mem_sup_right ⟨hl, ?_⟩
      rw [← hlw]; simpa using hu
    · have hcm : c ∈ coeff F L (x₀ + u₀) := by
        have h1 : c ∈ coeff F L (x₀ + c⁻¹ • u) := by
          rw [mem_coeff, smul_add, smul_smul, mul_inv_cancel₀ hc0, one_smul, add_comm, hlw]
          exact hl
        exact hmax _ (U.smul_mem _ hu) h1
      have hmem : c • (x₀ + u₀) ∈ L := hc c hcm
      have hs : c • (x₀ + u₀) ∈ coeff F L (x₀ + u₀) • span R {x₀ + u₀} :=
        Submodule.smul_mem_smul hcm (Submodule.mem_span_singleton_self _)
      refine Submodule.mem_sup.mpr ⟨c • (x₀ + u₀), hs, l - c • (x₀ + u₀), ⟨L.sub_mem hl hmem, ?_⟩, by abel⟩
      have : l - c • (x₀ + u₀) = u - c • u₀ := by
        rw [← hlw, smul_add]; abel
      show l - c • (x₀ + u₀) ∈ U
      rw [this]
      exact U.sub_mem hu (U.smul_mem _ hu₀)
  · refine sup_le ?_ inf_le_left
    rw [Submodule.smul_le]
    intro α hα n hn
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hn
    rw [smul_comm]
    exact L.smul_mem r (hc α hα)

/-- A submodule of a finitely generated submodule over a Noetherian ring is finitely generated. -/
theorem fg_of_le_aux {N M : Submodule R V} (hM : M.FG) (h : N ≤ M) : N.FG := by
  have : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  have : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  exact Module.Finite.iff_fg.mp (Module.Finite.of_injective (Submodule.inclusion h)
    (Submodule.inclusion_injective h))

/-- The supremum over `Fin (n + 1)` splits off the last index. -/
theorem iSup_snoc_aux {n : ℕ} (A : Fin (n + 1) → Submodule R V) :
    ⨆ i, A i = (⨆ i : Fin n, A (Fin.castSucc i)) ⊔ A (Fin.last n) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact le_sup_right
    · exact le_sup_of_le_left (le_iSup (fun i : Fin n => A (Fin.castSucc i)) j)
  · exact sup_le (iSup_le fun j => le_iSup A _) (le_iSup A _)

/-- **Theorem 81:3** (O'Meara 1963, pp. 211–212), for a lattice $L$ in $V$ and a base $x_1, \dots, x_n$ of $FL$.
There are independent $y_1, \dots, y_n$ with $y_i \in Fx_1 + \cdots + Fx_i$ and fractional ideals
$\mathfrak a_1, \dots, \mathfrak a_n$ such that $L = \mathfrak a_1y_1 + \cdots + \mathfrak a_ny_n$ (so $y$ is a base of
$FL$ adapted to $L$). -/
@[kb "omeara1963" "§81B, 81:3, pp. 211–212"]
theorem exists_adapted_flag {L : Submodule R V} (hL : L.FG) {n : ℕ} (x : Fin n → V)
    (hx : LinearIndependent F x) (hxL : span F (Set.range x) = span F (L : Set V)) :
    ∃ y : Fin n → V, LinearIndependent F y ∧ (∀ i, y i ∈ span F (x '' Set.Iic i)) ∧
      ∃ a : Fin n → Submodule R F, (∀ i, (a i).FG ∧ a i ≠ ⊥) ∧ L = ⨆ i, a i • span R {y i} := by
  induction n generalizing L with
  | zero =>
    have hL0 : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      have : l ∈ span F (L : Set V) := subset_span hl
      rw [← hxL] at this
      simpa using this
    refine ⟨x, hx, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    simp [hL0]
  | succ n ih =>
    set x' : Fin n → V := fun i => x (Fin.castSucc i) with hx'
    set x₀ := x (Fin.last n) with hx₀def
    set U : Submodule F V := span F (Set.range x') with hU
    have hxsnoc : x = Fin.snoc (α := fun _ => V) x' x₀ := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [x', x₀]
    have hx2 : LinearIndependent F (Fin.snoc (α := fun _ => V) x' x₀) := by
      rw [← hxsnoc]; exact hx
    obtain ⟨hx'i, hx₀U⟩ := linearIndependent_finSnoc.mp hx2
    have hU_le : U ≤ span F (Set.range x) :=
      span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Fin.castSucc i, rfl⟩)
    have hx₀_mem : x₀ ∈ span F (Set.range x) := subset_span ⟨_, rfl⟩
    have hLU : ∀ l ∈ L, l ∈ U ⊔ span F {x₀} := by
      intro l hl
      have : l ∈ span F (Set.range x) := by rw [hxL]; exact subset_span hl
      refine (span_le.mpr ?_ : span F (Set.range x) ≤ U ⊔ span F {x₀}) this
      rintro _ ⟨i, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact mem_sup_right (mem_span_singleton_self _)
      · exact mem_sup_left (subset_span ⟨j, rfl⟩)
    have hL'fg : (L ⊓ U.restrictScalars R).FG := fg_of_le_aux hL inf_le_left
    have hspan' : span F (Set.range x') = span F ((L ⊓ U.restrictScalars R : Submodule R V) : Set V) := by
      apply le_antisymm
      · intro u hu
        have hu' : u ∈ span F (L : Set V) := by rw [← hxL]; exact hU_le hu
        obtain ⟨d, hd0, hd⟩ := exists_smul_mem_of_mem_span (F := F) hu'
        have hdu : d • u ∈ (L ⊓ U.restrictScalars R : Submodule R V) :=
          ⟨hd, (U.smul_of_tower_mem d hu : d • u ∈ U)⟩
        have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd0
        have : u = (algebraMap R F d)⁻¹ • (d • u) := by
          rw [← algebraMap_smul F d u, smul_smul, inv_mul_cancel₀ hd', one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (subset_span hdu)
      · exact span_le.mpr fun v hv => hv.2
    obtain ⟨y', hy'i, hy'f, a', ha', hL'eq⟩ := ih (L := L ⊓ U.restrictScalars R) hL'fg x' hx'i hspan'
    obtain ⟨u₀, hu₀, hmax⟩ := exists_coeff_max hL hx₀U hLU
    have hdecomp := eq_coeff_smul_sup_inf hLU hu₀ hmax
    have hzU : x₀ + u₀ ∉ U := fun h => hx₀U (by simpa using U.sub_mem h hu₀)
    have hz0 : x₀ + u₀ ≠ 0 := fun h => hzU (h ▸ U.zero_mem)
    have hzL : x₀ + u₀ ∈ span F (L : Set V) := by
      rw [← hxL]; exact add_mem hx₀_mem (hU_le hu₀)
    have hyU : ∀ i, y' i ∈ U := fun i =>
      (span_mono (by rintro _ ⟨k, _, rfl⟩; exact ⟨k, rfl⟩) : span F (x' '' Set.Iic i) ≤ U) (hy'f i)
    refine ⟨Fin.snoc (α := fun _ => V) y' (x₀ + u₀), ?_, ?_,
      Fin.snoc (α := fun _ => Submodule R F) a' (coeff F L (x₀ + u₀)), ?_, ?_⟩
    · refine linearIndependent_finSnoc.mpr ⟨hy'i, fun h => hzU ?_⟩
      exact (span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hyU i) : span F (Set.range y') ≤ U) h
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
        refine add_mem (subset_span ⟨Fin.last n, Set.mem_Iic.mpr le_rfl, rfl⟩) ?_
        exact (span_mono (by
          rintro _ ⟨k, rfl⟩; exact ⟨Fin.castSucc k, Set.mem_Iic.mpr (Fin.le_last _), rfl⟩) :
          span F (Set.range x') ≤ span F (x '' Set.Iic (Fin.last n))) hu₀
      · rw [Fin.snoc_castSucc]
        exact (span_mono (by
          rintro _ ⟨k, hk, rfl⟩
          exact ⟨Fin.castSucc k, Fin.castSucc_le_castSucc_iff.mpr hk, rfl⟩) :
          span F (x' '' Set.Iic j) ≤ span F (x '' Set.Iic (Fin.castSucc j))) (hy'f j)
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact ⟨coeff_fg hL hz0, coeff_ne_bot hzL⟩
      · rw [Fin.snoc_castSucc]; exact ha' j
    · refine hdecomp.trans ?_
      rw [iSup_snoc_aux]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← hL'eq, sup_comm]

/-- **Theorem 81:3** as stated by O'Meara (1963, pp. 211–212). Let $L$ be a lattice on $V$ and $x_1, \dots, x_n$ a
base for $V$. Then there is a base $y_1, \dots, y_n$ with $y_i \in Fx_1 + \cdots + Fx_i$, and there are fractional
ideals $\mathfrak a_1, \dots, \mathfrak a_n$, such that $L = \mathfrak a_1y_1 + \cdots + \mathfrak a_ny_n$. -/
@[kb "omeara1963" "§81B, 81:3, pp. 211–212"]
theorem exists_adapted_basis_flag {L : Submodule R V} (hL : L.IsLattice F) {n : ℕ} (x : Basis (Fin n) F V) :
    ∃ y : Basis (Fin n) F V, (∀ i, y i ∈ span F (x '' Set.Iic i)) ∧
      ∃ a : Fin n → Submodule R F, (∀ i, (a i).FG ∧ a i ≠ ⊥) ∧ L = ⨆ i, a i • span R {y i} := by
  classical
  have : FiniteDimensional F V := Module.Finite.of_basis x
  obtain ⟨y, hy, hyf, a, ha, hL'⟩ :=
    exists_adapted_flag hL.fg x x.linearIndependent (by rw [x.span_eq, hL.span_eq_top])
  have hcard : Fintype.card (Fin n) = finrank F V := (finrank_eq_card_basis x).symm
  have hspan : span F (Set.range y) = ⊤ := hy.span_eq_top_of_card_eq_finrank' hcard
  refine ⟨Basis.mk hy hspan.ge, ?_, a, ha, ?_⟩
  · intro i; simpa using hyf i
  · simpa using hL'

/-- **Adapted bases exist** (O'Meara 1963, §81B, p. 212: "Theorem 81:3 asserts that there is a base for $FL$ that is
adapted to $L$"): every lattice $L$ in $V$ is $\mathfrak a_1y_1 + \cdots + \mathfrak a_ry_r$ for a base $y$ of $FL$
and fractional ideals $\mathfrak a_i$. -/
@[kb "omeara1963" "§81B, p. 212 (a base of FL adapted to L)"]
theorem exists_adapted [FiniteDimensional F V] {L : Submodule R V} (hL : L.FG) :
    ∃ r : ℕ, ∃ y : Fin r → V, LinearIndependent F y ∧ span F (Set.range y) = span F (L : Set V) ∧
      ∃ a : Fin r → Submodule R F, (∀ i, (a i).FG ∧ a i ≠ ⊥) ∧ L = ⨆ i, a i • span R {y i} := by
  classical
  set W : Submodule F V := span F (L : Set V) with hW
  let b := Module.finBasis F W
  let x : Fin (finrank F W) → V := fun i => (b i : V)
  have hx : LinearIndependent F x := b.linearIndependent.map' W.subtype (ker_subtype W)
  have hxL : span F (Set.range x) = W := by
    have h1 : Submodule.map W.subtype (span F (Set.range b)) = span F (W.subtype '' Set.range b) :=
      Submodule.map_span _ _
    rw [b.span_eq, Submodule.map_top, Submodule.range_subtype] at h1
    refine Eq.trans ?_ h1.symm
    congr 1
    rw [← Set.range_comp]; rfl
  obtain ⟨y, hy, hyf, a, ha, hLeq⟩ := exists_adapted_flag hL x hx hxL
  refine ⟨_, y, hy, ?_, a, ha, hLeq⟩
  apply le_antisymm
  · refine span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [← hxL]
    exact span_mono (Set.image_subset_range _ _) (hyf i)
  · have hLle : L ≤ (span F (Set.range y)).restrictScalars R := by
      rw [hLeq]
      refine iSup_le fun i => ?_
      rw [Submodule.smul_le]
      intro α hα m hm
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hm
      show α • r • y i ∈ span F (Set.range y)
      rw [← algebraMap_smul F r (y i), smul_smul]
      exact Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
    exact span_le.mpr fun l hl => hLle hl

/-- **$\operatorname{rank} L = \dim FL$** (O'Meara 1963, §81B, p. 212): the rank of a lattice $L$ in $V$ (the number
of elements of a maximal independent subset of $L$, here `Module.finrank R L`) is the dimension of the space $FL$. -/
@[kb "omeara1963" "§81B, p. 212 (rank L = dim FL)"]
theorem finrank_eq_finrank_span (L : Submodule R V) :
    finrank R L = finrank F (span F (L : Set V)) := by
  set W : Submodule F V := span F (L : Set V) with hW
  let g : L →ₗ[R] W :=
    { toFun := fun l => ⟨l, subset_span l.2⟩
      map_add' := fun a b => rfl
      map_smul' := fun r a => Subtype.ext (by simp) }
  have hloc : IsLocalizedModule (nonZeroDivisors R) g := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      rw [Module.End.isUnit_iff]
      have hs : algebraMap R F s ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.ne_zero s.2)
      constructor
      · intro w w' h
        have h' : (algebraMap R F s) • w = (algebraMap R F s) • w' := by
          simpa [algebraMap_smul] using h
        exact smul_right_injective W hs h'
      · intro w
        refine ⟨(algebraMap R F s)⁻¹ • w, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul F (s : R), smul_smul, mul_inv_cancel₀ hs, one_smul]
    · intro w
      obtain ⟨d, hd0, hd⟩ := exists_smul_mem_of_mem_span (F := F) (S := L) w.2
      refine ⟨(⟨_, hd⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd0⟩), ?_⟩
      rfl
    · intro l l' h
      have : l = l' := Subtype.ext (congrArg (fun w : W => (w : V)) h)
      exact ⟨1, by rw [this]⟩
  have h1 : finrank R W = finrank R L := IsLocalizedModule.finrank_eq (nonZeroDivisors R) g le_rfl
  have h2 : finrank F W = finrank R W := IsLocalization.finrank_eq F (nonZeroDivisors R) le_rfl
  rw [h2, h1]

/-- **Every lattice is free when the class number is $1$** (O'Meara 1963, §81B, p. 213): if every fractional ideal is
principal, every lattice in $V$ has a base. -/
@[kb "omeara1963" "§81B, p. 213 (free lattices when the class number is 1)"]
theorem free_of_principal [FiniteDimensional F V] (hP : ∀ a : Submodule R F, a.FG → ∃ α : F, a = span R {α})
    {L : Submodule R V} (hL : L.FG) : Module.Free R L := by
  obtain ⟨r, y, hy, hspan, a, ha, hLeq⟩ := exists_adapted (F := F) hL
  choose α hα using fun i => hP (a i) (ha i).1
  have hα0 : ∀ i, α i ≠ 0 := by
    intro i h
    apply (ha i).2
    rw [hα i, h]; simp
  let w : Fin r → V := fun i => α i • y i
  have hw : LinearIndependent R w := by
    have := hy.units_smul (fun i => Units.mk0 (α i) (hα0 i))
    exact LinearIndependent.restrict_scalars' (R := R) (K := F) this
  have hLw : L = span R (Set.range w) := by
    apply le_antisymm
    · rw [hLeq]
      refine iSup_le fun i => ?_
      rw [Submodule.smul_le]
      intro β hβ m hm
      rw [hα i] at hβ
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hβ
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hm
      have : (s • α i) • t • y i = (s * t) • w i := by
        simp only [w]
        rw [Algebra.smul_def, ← algebraMap_smul F t (y i), smul_smul, ← algebraMap_smul F (s * t),
          smul_smul, map_mul]
        congr 1
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
    · refine span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [hLeq]
      exact Submodule.mem_iSup_of_mem i
        (Submodule.smul_mem_smul (by rw [hα i]; exact Submodule.mem_span_singleton_self _)
          (Submodule.mem_span_singleton_self _))
  rw [hLw]
  exact Module.Free.of_basis (Basis.span hw)

end QuadFormsKB.OMeara
