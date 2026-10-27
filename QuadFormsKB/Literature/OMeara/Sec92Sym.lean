/-
# O'Meara §92: units of a lattice are products of symmetries (Theorem 92:4)

**Setting** (as in `Sec92.lean`): $R$ a discrete valuation ring with fraction field $F$, $2$ a unit of $R$
(non-dyadic), a quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.

**Proves** `exists_symmetry_list` (**Theorem 92:4**, p. 248): if $L$ is a lattice on a regular $n$-dimensional quadratic
space over a non-dyadic local field, every element of $O(L)$ is a product of at most $2n - 1$ symmetries in $O(L)$.
-/
import QuadFormsKB.Literature.OMeara.Sec92Rep

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section NonDyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

open Classical in
/-- The symmetry $\tau_u$ if $Q(u) \ne 0$, and $1$ otherwise (a total version of `symmetry`, used to write products
of symmetries as products over lists). -/
def symmetryOrOne (u : V) : V ≃ₗ[F] V :=
  if hu : Q u = 0 then 1 else symmetry Q u hu

/-- A vector $u$ of $L$ with $Q(u) \ne 0$ and $\tau_u L \subseteq L$ (helper for 92:4). -/
def IsSymVec (L : Submodule R V) (u : V) : Prop :=
  u ∈ L ∧ ∃ hu : Q u ≠ 0, ∀ x ∈ L, symmetry Q u hu x ∈ L

theorem sym4_symmetryOrOne_of_ne {u : V} (hu : Q u ≠ 0) : symmetryOrOne Q u = symmetry Q u hu := by
  simp [symmetryOrOne, hu]

theorem sym4_symmetryOrOne_fix (u x : V) (h : bil Q x u = 0) : symmetryOrOne Q u x = x := by
  unfold symmetryOrOne
  split_ifs with hu
  · simp
  · rw [symmetry_apply]; simp [h]

theorem sym4_prod_fix (l : List V) (x : V) (h : ∀ u ∈ l, bil Q x u = 0) :
    (l.map (symmetryOrOne Q)).prod x = x := by
  induction l with
  | nil => simp
  | cons u l ih =>
    rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih (fun v hv => h v (by simp [hv])),
      sym4_symmetryOrOne_fix Q u x (h u (by simp))]

theorem sym4_prod_mem {L : Submodule R V} (l : List V) (hl : ∀ u ∈ l, IsSymVec Q L u) :
    (l.map (symmetryOrOne Q)).prod ∈ orthLat Q L := by
  induction l with
  | nil => simp
  | cons u l ih =>
    rw [List.map_cons, List.prod_cons]
    obtain ⟨hu, hQ, hτ⟩ := hl u (by simp)
    rw [sym4_symmetryOrOne_of_ne Q hQ]
    exact (orthLat Q L).mul_mem (symmetry_mem_orthLat_of_le Q hQ hτ)
      (ih fun v hv => hl v (by simp [hv]))

theorem sym4_bil_neg_right (x y : V) : bil Q x (-y) = -bil Q x y := by
  rw [bil_comm, bil_neg_left, bil_comm]

theorem sym4_bil_orth {σ : V ≃ₗ[F] V} (hσ : σ ∈ orth Q) (x y : V) :
    bil Q (σ x) (σ y) = bil Q x y := by
  have h1 := Q_add Q (σ x) (σ y)
  have h2 := Q_add Q x y
  rw [← map_add σ x y] at h1
  have a : Q (σ (x + y)) = Q (x + y) := hσ (x + y)
  have b : Q (σ x) = Q x := hσ x
  have c : Q (σ y) = Q y := hσ y
  have : (2 : F) * bil Q (σ x) (σ y) = 2 * bil Q x y := by
    linear_combination (-1) * h1 + h2 + a - b - c
  exact mul_left_cancel₀ two_ne_zero this

theorem sym4_symmetry_self {u : V} (hu : Q u ≠ 0) : symmetry Q u hu u = -u := by
  rw [symmetry_apply, bil_self]
  have : 2 * Q u / Q u = 2 := by field_simp
  rw [this, two_smul]; abel

theorem sym4_symmetry_apply_of_two_bil {u v : V} (hu : Q u ≠ 0) (h : 2 * bil Q v u = Q u) :
    symmetry Q u hu v = v - u := by
  rw [symmetry_apply, h, div_self hu, one_smul]

/-- A vector $y \in L$ with $\mathfrak sL = Q(y)\mathfrak o$ gives a symmetry preserving $L$. -/
theorem sym4_isSymVec_of_good (h2 : IsUnit (2 : R)) {L : Submodule R V} {y : V} (hy : y ∈ L)
    (hQ : Q y ≠ 0) (hs : scale Q L = R ∙ Q y) : IsSymVec Q L y := by
  refine ⟨hy, hQ, fun x hx => ?_⟩
  have h2' : 2 * bil Q y x ∈ R ∙ Q y := by
    have := two_mul_mem_normIdeal Q (bil_mem_scale Q hy hx)
    rwa [normIdeal_eq_scale Q h2, hs] at this
  obtain ⟨r, hr⟩ := mem_span_singleton.mp h2'
  rw [symmetry_apply]
  have : (2 * bil Q x y / Q y) • y = r • y := by
    rw [← algebraMap_smul F r y]
    congr 1
    rw [bil_comm, ← hr, Algebra.smul_def]; field_simp
  rw [this]
  exact L.sub_mem hx (L.smul_mem r hy)

/-- One or two symmetries of $L$ carry $y$ (with $\mathfrak sL = Q(y)\mathfrak o$) to $\sigma y$ for $\sigma \in O(L)$. -/
theorem sym4_exists_list_two (h2 : IsUnit (2 : R)) {L : Submodule R V} {y : V} (hy : y ∈ L)
    (hQ : Q y ≠ 0) (hs : scale Q L = R ∙ Q y) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthLat Q L) :
    ∃ l : List V, l.length ≤ 2 ∧ (∀ u ∈ l, IsSymVec Q L u) ∧
      (l.map (symmetryOrOne Q)).prod y = σ y := by
  have hσy : σ y ∈ L := by
    have : σ y ∈ latMap σ L := Submodule.mem_map_of_mem hy
    rwa [hσ.2] at this
  have hQw : Q (σ y) = Q y := hσ.1 y
  generalize σ y = w at hσy hQw ⊢
  have hnorm : ∀ v ∈ L, Q v ∈ R ∙ Q y := fun v hv => by
    have := Q_mem_normIdeal Q hv
    rwa [normIdeal_eq_scale Q h2, hs] at this
  have hqa : Q (y - w) = 2 * Q y - 2 * bil Q y w := by
    have := Q_add Q y (-w)
    rw [← sub_eq_add_neg, sym4_bil_neg_right, QuadraticMap.map_neg] at this
    rw [this, hQw]; ring
  have hqb : Q (y + w) = 2 * Q y + 2 * bil Q y w := by
    rw [Q_add, hQw]; ring
  have h4 : IsUnit (4 : R) := by
    have : (4 : R) = 2 * 2 := by norm_num
    rw [this]; exact h2.mul h2
  obtain ⟨u4, hu4⟩ := h4
  have hQy : Q y ∈ (R ∙ Q (y - w)) ⊔ (R ∙ Q (y + w)) := by
    have hsum : Q (y - w) + Q (y + w) = 4 * Q y := by rw [hqa, hqb]; ring
    have hmem : 4 * Q y ∈ (R ∙ Q (y - w)) ⊔ (R ∙ Q (y + w)) :=
      hsum ▸ add_mem_sup (mem_span_singleton_self _) (mem_span_singleton_self _)
    have : Q y = (↑u4⁻¹ : R) • (4 * Q y) := by
      rw [Algebra.smul_def, ← mul_assoc, ← map_ofNat (algebraMap R F) 4, ← hu4, ← map_mul,
        Units.inv_mul, map_one, one_mul]
    rw [this]; exact Submodule.smul_mem _ _ hmem
  rcases span_pair_eq (R := R) (Q (y - w)) (Q (y + w)) with h | h
  · rw [h] at hQy
    have hsa : scale Q L = R ∙ Q (y - w) := by
      rw [hs]; apply le_antisymm
      · exact (span_singleton_le_iff_mem _ _).mpr hQy
      · exact (span_singleton_le_iff_mem _ _).mpr (hnorm _ (L.sub_mem hy hσy))
    have hQa : Q (y - w) ≠ 0 := by
      intro h0
      rw [h0] at hQy
      obtain ⟨r, hr⟩ := mem_span_singleton.mp hQy
      rw [smul_zero] at hr; exact hQ hr.symm
    refine ⟨[y - w], by simp, ?_, ?_⟩
    · intro u hu'
      rw [List.mem_singleton] at hu'
      rw [hu']
      exact sym4_isSymVec_of_good Q h2 (L.sub_mem hy hσy) hQa hsa
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [sym4_symmetryOrOne_of_ne Q hQa, sym4_symmetry_apply_of_two_bil Q hQa ?_]
      · abel
      · rw [bil_sub_right, bil_self, hqa]; ring
  · rw [h] at hQy
    have hsb : scale Q L = R ∙ Q (y + w) := by
      rw [hs]; apply le_antisymm
      · exact (span_singleton_le_iff_mem _ _).mpr hQy
      · exact (span_singleton_le_iff_mem _ _).mpr (hnorm _ (L.add_mem hy hσy))
    have hQb : Q (y + w) ≠ 0 := by
      intro h0
      rw [h0] at hQy
      obtain ⟨r, hr⟩ := mem_span_singleton.mp hQy
      rw [smul_zero] at hr; exact hQ hr.symm
    refine ⟨[y + w, y], by simp, ?_, ?_⟩
    · intro u hu'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
      rcases hu' with h' | h'
      · rw [h']
        exact sym4_isSymVec_of_good Q h2 (L.add_mem hy hσy) hQb hsb
      · rw [h']
        exact sym4_isSymVec_of_good Q h2 hy hQ hs
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [sym4_symmetryOrOne_of_ne Q hQb, sym4_symmetryOrOne_of_ne Q hQ, LinearEquiv.mul_apply,
        sym4_symmetry_self Q hQ, map_neg, sym4_symmetry_apply_of_two_bil Q hQb ?_]
      · abel
      · rw [bil_add_right, bil_self, hqb]; ring

theorem sym4_isModular_span_singleton {y : V} (hy : Q y ≠ 0) :
    IsModular Q (R ∙ Q y) (R ∙ y) ∧ finrank R (R ∙ y) = 1 := by
  let v : Fin 1 → V := fun _ => y
  have hG : gram Q v = Q y • (1 : Matrix (Fin 1) (Fin 1) R).map (algebraMap R F) := by
    ext i j; fin_cases i; fin_cases j; simp [v, gram]
  obtain ⟨hmod, hrk⟩ := isModular_span_of_gram Q hy (by simp) hG
  have hJ : span R (Set.range v) = R ∙ y := by simp [v, Set.range_const]
  rw [hJ] at hmod hrk
  exact ⟨hmod, by simpa using hrk⟩

/-- Splitting off a vector $y$ with $\mathfrak sL = Q(y)\mathfrak o$. -/
theorem sym4_exists_split (h2 : IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L)
    (hne : L ≠ ⊥) :
    ∃ (y : V) (K : Submodule R V), y ∈ L ∧ Q y ≠ 0 ∧ scale Q L = R ∙ Q y ∧
      IsOrthSum Q L (R ∙ y) K ∧ finrank R L = 1 + finrank R K := by
  obtain ⟨y, hyL, hn⟩ := exists_normIdeal_eq Q hfg
  have hs : scale Q L = R ∙ Q y := by rw [← normIdeal_eq_scale Q h2 L]; exact hn
  have hQ : Q y ≠ 0 := by
    intro h0; exact scale_ne_bot Q hreg hne (by rw [hs, h0]; simp)
  obtain ⟨hJ, hJrk⟩ := sym4_isModular_span_singleton (R := R) Q hQ
  have hJL : R ∙ y ≤ L := (span_singleton_le_iff_mem _ _).mpr hyL
  obtain ⟨K, hK⟩ := splits_of_isModular_of_scale_eq Q hJL hJ (fg_span_singleton y) hs
  refine ⟨y, K, hyL, hQ, hs, hK, ?_⟩
  rw [isOrthSum_finrank Q hK hfg, hJrk]

theorem sym4_mem_comp_iff {L K : Submodule R V} {y : V} (hQ : Q y ≠ 0) (hK : IsOrthSum Q L (R ∙ y) K)
    {x : V} : x ∈ K ↔ x ∈ L ∧ bil Q x y = 0 := by
  constructor
  · intro hx
    refine ⟨hK.sup_eq ▸ mem_sup_right hx, ?_⟩
    rw [bil_comm]; exact hK.orth y (mem_span_singleton_self y) x hx
  · rintro ⟨hxL, hxy⟩
    rw [← hK.sup_eq] at hxL
    obtain ⟨z, hz, k, hk, rfl⟩ := mem_sup.mp hxL
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hz
    have hky : bil Q k y = 0 := by
      rw [bil_comm]; exact hK.orth y (mem_span_singleton_self y) k hk
    rw [bil_add_left, hky, add_zero, bil_rsmul_left, bil_self] at hxy
    have hr : algebraMap R F r = 0 := (mul_eq_zero.mp hxy).resolve_right hQ
    have : r • y = 0 := by rw [← algebraMap_smul F r y, hr, zero_smul]
    rw [this, zero_add]; exact hk

theorem sym4_map_mem_comp {L K : Submodule R V} {y : V} (hQ : Q y ≠ 0) (hK : IsOrthSum Q L (R ∙ y) K)
    {g : V ≃ₗ[F] V} (hg : g ∈ orthLat Q L) (hgy : g y = y) {x : V} (hx : x ∈ K) : g x ∈ K := by
  rw [sym4_mem_comp_iff Q hQ hK] at hx ⊢
  refine ⟨?_, ?_⟩
  · have : g x ∈ latMap g L := Submodule.mem_map_of_mem hx.1
    rwa [hg.2] at this
  · have := sym4_bil_orth Q hg.1 x y
    rw [hgy] at this
    rw [this]; exact hx.2

/-- Passing to the complement $K$ of $y$ in $L = Ry \perp K$ for a unit fixing $y$. -/
theorem sym4_reduce {L K : Submodule R V} {y : V} (hQ : Q y ≠ 0) (hK : IsOrthSum Q L (R ∙ y) K)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthLat Q L) (hy : σ y = y)
    (hfix : ∀ x, (∀ z ∈ L, bil Q x z = 0) → σ x = x) :
    σ ∈ orthLat Q K ∧ ∀ x, (∀ z ∈ K, bil Q x z = 0) → σ x = x := by
  have hy' : (σ⁻¹) y = y := (LinearEquiv.symm_apply_eq σ).mpr hy.symm
  refine ⟨⟨hσ.1, ?_⟩, ?_⟩
  · ext x
    simp only [latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact sym4_map_mem_comp Q hQ hK hσ hy hz
    · intro hx
      exact ⟨(σ⁻¹) x, sym4_map_mem_comp Q hQ hK ((orthLat Q L).inv_mem hσ) hy' hx,
        (LinearEquiv.apply_symm_apply σ x)⟩
  · intro x hx
    set c := bil Q x y / Q y with hc
    have hcy : c * Q y = bil Q x y := by rw [hc]; field_simp
    have h0 : σ (x - c • y) = x - c • y := by
      apply hfix
      intro z hz
      rw [← hK.sup_eq] at hz
      obtain ⟨w, hw, k, hk, rfl⟩ := mem_sup.mp hz
      obtain ⟨r, rfl⟩ := mem_span_singleton.mp hw
      have hyk : bil Q y k = 0 := hK.orth y (mem_span_singleton_self y) k hk
      rw [bil_add_right, bil_rsmul_right, bil_sub_left, bil_sub_left, bil_smul_left, bil_smul_left,
        hyk, hx k hk, bil_self, hcy]
      simp
    calc σ x = σ ((x - c • y) + c • y) := by rw [sub_add_cancel]
      _ = x := by rw [map_add, map_smul, h0, hy, sub_add_cancel]

/-- Peeling off a list of symmetries carrying $y$ to $\sigma y$. -/
theorem sym4_peel {L K : Submodule R V} {y : V} (hQ : Q y ≠ 0) (hK : IsOrthSum Q L (R ∙ y) K)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthLat Q L) (hfix : ∀ x, (∀ z ∈ L, bil Q x z = 0) → σ x = x)
    (l : List V) (hl : ∀ u ∈ l, IsSymVec Q L u)
    (hy : (l.map (symmetryOrOne Q)).prod y = σ y) :
    ∃ σ' : V ≃ₗ[F] V, σ' ∈ orthLat Q K ∧ (∀ x, (∀ z ∈ K, bil Q x z = 0) → σ' x = x) ∧
      σ = (l.map (symmetryOrOne Q)).prod * σ' := by
  set ρ := (l.map (symmetryOrOne Q)).prod with hρ
  have hρL : ρ ∈ orthLat Q L := sym4_prod_mem Q l hl
  have hσ'L : ρ⁻¹ * σ ∈ orthLat Q L := (orthLat Q L).mul_mem ((orthLat Q L).inv_mem hρL) hσ
  have hσ'y : (ρ⁻¹ * σ) y = y := by
    rw [LinearEquiv.mul_apply, ← hy]
    exact (LinearEquiv.symm_apply_eq ρ).mpr rfl
  have hfix' : ∀ x, (∀ z ∈ L, bil Q x z = 0) → (ρ⁻¹ * σ) x = x := by
    intro x hx
    have h1 : ρ x = x := sym4_prod_fix Q l x (fun u hu => hx u (hl u hu).1)
    rw [LinearEquiv.mul_apply, hfix x hx]
    exact (LinearEquiv.symm_apply_eq ρ).mpr h1.symm
  obtain ⟨h1, h2⟩ := sym4_reduce Q hQ hK hσ'L hσ'y hfix'
  exact ⟨ρ⁻¹ * σ, h1, h2, (mul_inv_cancel_left ρ σ).symm⟩

theorem sym4_isSymVec_of_comp {L K : Submodule R V} {y : V} (hK : IsOrthSum Q L (R ∙ y) K) {u : V}
    (hu : IsSymVec Q K u) : IsSymVec Q L u := by
  obtain ⟨huK, hQ, hτ⟩ := hu
  have hKL : K ≤ L := hK.sup_eq ▸ le_sup_right
  refine ⟨hKL huK, hQ, fun x hx => ?_⟩
  rw [← hK.sup_eq] at hx
  obtain ⟨z, hz, k, hk, rfl⟩ := mem_sup.mp hx
  rw [map_add]
  have h1 : symmetry Q u hQ z = z := by
    rw [symmetry_apply]; simp [hK.orth z hz u huK]
  rw [h1]
  have := add_mem (mem_sup_left hz : z ∈ R ∙ y ⊔ K) (mem_sup_right (hτ k hk) : _ ∈ R ∙ y ⊔ K)
  rwa [hK.sup_eq] at this

/-- The generalized statement of 92:4, by induction on the rank. -/
theorem sym4_aux (h2 : IsUnit (2 : R)) (m : ℕ) :
    ∀ {L : Submodule R V}, L.FG → IsRegular Q L → finrank R L = m + 1 →
    ∀ {σ : V ≃ₗ[F] V}, σ ∈ orthLat Q L → (∀ x, (∀ z ∈ L, bil Q x z = 0) → σ x = x) →
    ∃ l : List V, l.length ≤ 2 * (m + 1) - 1 ∧ (∀ u ∈ l, IsSymVec Q L u) ∧
      σ = (l.map (symmetryOrOne Q)).prod := by
  induction m with
  | zero =>
    intro L hfg hreg hrk σ hσ hfix
    have hne : L ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hrk; omega
    obtain ⟨y, K, hyL, hQ, hs, hK, hrkK⟩ := sym4_exists_split Q h2 hfg hreg hne
    have hKL : K ≤ L := hK.sup_eq ▸ le_sup_right
    have hKfg : K.FG := FG.of_le hfg hKL
    have := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
    have : Module.Finite R K := Module.Finite.iff_fg.mpr hKfg
    have hK0 : K = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hLy : L = R ∙ y := by rw [← hK.sup_eq, hK0, sup_bot_eq]
    have hσy : σ y ∈ L := by
      have : σ y ∈ latMap σ L := Submodule.mem_map_of_mem hyL
      rwa [hσ.2] at this
    rw [hLy] at hσy
    obtain ⟨r, hr⟩ := mem_span_singleton.mp hσy
    have hq : Q (σ y) = Q y := hσ.1 y
    rw [← hr, Q_rsmul] at hq
    have hfac : (algebraMap R F r - 1) * (algebraMap R F r + 1) * Q y = 0 := by
      linear_combination hq
    have hc : algebraMap R F r = 1 ∨ algebraMap R F r = -1 := by
      rcases mul_eq_zero.mp hfac with h | h
      · rcases mul_eq_zero.mp h with h | h
        · left; linear_combination h
        · right; linear_combination h
      · exact absurd h hQ
    obtain ⟨l, hl1, hl, hρ⟩ : ∃ l : List V, l.length ≤ 1 ∧ (∀ u ∈ l, IsSymVec Q L u) ∧
        (l.map (symmetryOrOne Q)).prod y = σ y := by
      rcases hc with h | h
      · refine ⟨[], by simp, by simp, ?_⟩
        rw [← hr, ← algebraMap_smul F r y, h, one_smul]; simp
      · refine ⟨[y], by simp, ?_, ?_⟩
        · intro u hu
          rw [List.mem_singleton] at hu
          rw [hu]; exact sym4_isSymVec_of_good Q h2 hyL hQ hs
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [sym4_symmetryOrOne_of_ne Q hQ, sym4_symmetry_self Q hQ, ← hr,
            ← algebraMap_smul F r y, h, neg_one_smul]
    obtain ⟨σ', hσ'K, hfixK, hσeq⟩ := sym4_peel Q hQ hK hσ hfix l hl hρ
    have hσ'1 : σ' = 1 := by
      ext x
      exact hfixK x (fun z hz => by rw [hK0, Submodule.mem_bot] at hz; simp [hz, bil])
    refine ⟨l, by omega, hl, ?_⟩
    rw [hσeq, hσ'1, mul_one]
  | succ m ih =>
    intro L hfg hreg hrk σ hσ hfix
    have hne : L ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hrk; omega
    obtain ⟨y, K, hyL, hQ, hs, hK, hrkK⟩ := sym4_exists_split Q h2 hfg hreg hne
    have hKL : K ≤ L := hK.sup_eq ▸ le_sup_right
    have hKfg : K.FG := FG.of_le hfg hKL
    obtain ⟨l, hl2, hl, hρ⟩ := sym4_exists_list_two Q h2 hyL hQ hs hσ
    obtain ⟨σ', hσ'K, hfixK, hσeq⟩ := sym4_peel Q hQ hK hσ hfix l hl hρ
    have hKreg := IsOrthSum.isRegular_right Q hK hreg
    obtain ⟨l', hl'1, hl', hσ'eq⟩ := ih hKfg hKreg (by omega) hσ'K hfixK
    refine ⟨l ++ l', ?_, ?_, ?_⟩
    · rw [List.length_append]; omega
    · intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hl u h
      · exact sym4_isSymVec_of_comp Q hK (hl' u h)
    · rw [List.map_append, List.prod_append, ← hσ'eq]; exact hσeq

/-- **Theorem 92:4** (O'Meara 1963, p. 248): let $L$ be a lattice on a regular $n$-ary quadratic space $V$ over a
non-dyadic local field, $n \ge 1$. Then every element of $O(L)$ is a product of at most $2n - 1$ symmetries in $O(L)$:
$\sigma = \tau_{u_1} \cdots \tau_{u_k}$ with $k \le 2n - 1$, each $Q(u_j) \ne 0$ and each $\tau_{u_j} \in O(L)$.
(Only the discrete valuation ring and $2 \in \mathfrak u$ are used.) -/
@[kb "omeara1963" "§92, 92:4, p. 248"]
theorem exists_symmetry_list (h2 : IsUnit (2 : R)) [FiniteDimensional F V]
    (hV : (QuadraticMap.associated Q).Nondegenerate) (hn : 1 ≤ finrank F V) {L : Submodule R V}
    (hL : L.IsLattice F) {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthLat Q L) :
    ∃ l : List V, l.length ≤ 2 * finrank F V - 1 ∧
      (∀ u ∈ l, ∃ hu : Q u ≠ 0, symmetry Q u hu ∈ orthLat Q L) ∧ σ = (l.map (symmetryOrOne Q)).prod := by
  have hfg := hL.fg
  have hbil : ∀ x, (∀ z ∈ L, bil Q x z = 0) → x = 0 := by
    intro x hx
    have hBV : ∀ y : V, bil Q x y = 0 := by
      intro y
      have hy : y ∈ span F (L : Set V) := hL.span_eq_top ▸ mem_top
      refine span_induction (p := fun y _ => bil Q x y = 0) ?_ (by simp [bil]) ?_ ?_ hy
      · intro y hy; exact hx y hy
      · intro a b _ _ ha hb; rw [bil_add_right, ha, hb, add_zero]
      · intro c a _ ha; rw [bil_smul_right, ha, mul_zero]
    exact hV.1 x hBV
  have hreg : IsRegular Q L := fun x _ hx => hbil x hx
  have hrank : finrank R L = finrank F V :=
    Module.finrank_eq_of_rank_eq
      ((Submodule.IsLattice.rank' F L).trans (Module.finrank_eq_rank F V).symm)
  obtain ⟨m, hm⟩ : ∃ m, finrank R L = m + 1 := ⟨finrank R L - 1, by omega⟩
  obtain ⟨l, hl, hu, hσl⟩ := sym4_aux Q h2 m hfg hreg hm hσ
    (fun x hx => by rw [hbil x hx, map_zero])
  refine ⟨l, by omega, fun u hu' => ?_, hσl⟩
  obtain ⟨-, hQ, hτ⟩ := hu u hu'
  exact ⟨hQ, symmetry_mem_orthLat_of_le Q hQ hτ⟩

end NonDyadic

end QuadFormsKB.OMeara
