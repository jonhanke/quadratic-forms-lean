/-
# O'Meara §65B, §65D: Propositions 65:13, 65:14, 65:21, 65:22 (the idèle-class index of the norms)

**Setting** as in `Sec65Index.lean`. $P_F N_{E/F}J_E$ is the subgroup `IdeleGroup.principalSubgroup (𝓞 F) F ⊔
(ideleNorm).range` of $J_F$ (the group is commutative, so the product of two subgroups is their join); a group index
`≠ 0` means "finite".

**Proves**
* **Proposition 65:13** `index_principal_sup_range_ideleNorm`: if $\theta$ is a unit at all spots of $S$ and $J_E =
  P_E J_E^S$, then $(J_F : P_F N_{E/F}J_E) = 2\,(P_F^S \cap N_{E/F}J_E^S : N_{E/F}P_E^S) < \infty$.
-/
import QuadFormsKB.Literature.OMeara.Sec65Index
import QuadFormsKB.Literature.OMeara.Sec65D
import QuadFormsKB.Literature.OMeara.Sec65Rest

open NumberField IsDedekindDomain InfinitePlace

open scoped NumberField.LiesOver

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

local notation "JF" => IdeleGroup (𝓞 F) F
local notation "PF" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "NE" => ideleNorm (F := F) (E := E)

variable {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
include hθ hs

omit [Algebra.IsQuadraticExtension F E] hθ hs in
/-- In a commutative group, if $K \le M$ then $M \cap (H \sqcup K) = (M \cap H) \sqcup K$ (modular law). -/
lemma inf_sup_of_le {G : Type*} [CommGroup G] {H K M : Subgroup G} (hKM : K ≤ M) :
    M ⊓ (H ⊔ K) = (M ⊓ H) ⊔ K := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_sup]
  constructor
  · rintro ⟨hx, y, hy, z, hz, rfl⟩
    refine ⟨y, ⟨?_, hy⟩, z, hz, rfl⟩
    have : y = (y * z) * z⁻¹ := by group
    rw [this]
    exact M.mul_mem hx (M.inv_mem (hKM hz))
  · rintro ⟨y, ⟨hyM, hy⟩, z, hz, rfl⟩
    exact ⟨M.mul_mem hyM (hKM hz), y, hy, z, hz, rfl⟩

/-- **Proposition 65:13** (O'Meara 1963, p. 181): suppose $S$ satisfies the conventions of §65A, $\theta$ is a unit at
all spots in $S$, and $J_E = P_E J_E^S$. Then
$(J_F : P_FN_{E/F}J_E) = 2\,(P_F^S \cap N_{E/F}J_E^S : N_{E/F}P_E^S) < \infty$. -/
@[kb "omeara1963" "§65B, 65:13, p. 181"]
theorem index_principal_sup_range_ideleNorm {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    (hθS : ∀ v ∈ S, v.valuation F θ = 1)
    (hE : ∀ i : IdeleGroup (𝓞 E) E, ∃ p ∈ IdeleGroup.principalSubgroup (𝓞 E) E,
      ∃ j ∈ sIdeles (spotsAbove (E := E) S), i = p * j) :
    (PF ⊔ (NE).range).index =
        2 * ((principalSIdeles (spotsAbove (E := E) S)).map NE).relIndex
          (principalSIdeles S ⊓ (sIdeles (spotsAbove (E := E) S)).map NE) ∧
      (PF ⊔ (NE).range).index ≠ 0 := by
  set JS := sIdeles (F := F) S
  set PS := principalSIdeles (F := F) S
  set NJS := (sIdeles (spotsAbove (E := E) S)).map NE
  set NP := (principalSIdeles (spotsAbove (E := E) S)).map NE
  have hNJS : NJS ≤ JS := map_sIdeles_le S
  have hNP_PS : NP ≤ PS := map_principalSIdeles_le S
  have hNP_NJS : NP ≤ NJS := Subgroup.map_mono inf_le_left
  have hPS_JS : PS ≤ JS := inf_le_left
  -- `P_F N J_E = P_F N J_E^S`
  have hPNJ : PF ⊔ (NE).range = PF ⊔ NJS := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left (Subgroup.map_le_range _ _) _)
    rintro _ ⟨i, rfl⟩
    obtain ⟨p, hp, j, hj, rfl⟩ := hE i
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (map_principalSubgroup_le ⟨p, hp, rfl⟩))
      (Subgroup.mem_sup_right ⟨j, hj, rfl⟩)
  -- `J_F = P_F J^S`
  have hJ : JS ⊔ (PF ⊔ NJS) = ⊤ := by
    refine eq_top_iff.2 fun i _ => ?_
    obtain ⟨p, hp, j, hj, rfl⟩ := hS.ideles i
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left hp)) (Subgroup.mem_sup_left hj)
  -- `(J_F : P N J_E) = (J^S : P^S N J^S_E)`
  have h1 : (PF ⊔ NJS).index = (PS ⊔ NJS).relIndex JS := by
    have := Subgroup.relIndex_sup_right (H := JS) (K := PF ⊔ NJS)
    rw [hJ, Subgroup.relIndex_top_right] at this
    rw [this, ← Subgroup.inf_relIndex_right, inf_comm, inf_sup_of_le hNJS]
    have hPS : JS ⊓ PF = PS := rfl
    rw [hPS]
  -- `(J^S : N J^S_E) = 2^b` (65:8)
  have h8 := relIndex_map_sIdeles E hθ hs hS hθS
  have h2 : NJS.relIndex (PS ⊔ NJS) * (PS ⊔ NJS).relIndex JS = NJS.relIndex JS :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right (sup_le hPS_JS hNJS)
  have h3 : NJS.relIndex (PS ⊔ NJS) = (PS ⊓ NJS).relIndex PS := by
    rw [sup_comm, Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, inf_comm]
  -- `(P^S : N P^S_E) = 2^{b-1}` (65:10)
  obtain ⟨hb, h10⟩ := relIndex_normSUnits E hθ hs hS hθS
  rw [← relIndex_map_principalSIdeles E hS.cofinite] at h10
  have h4 : NP.relIndex (PS ⊓ NJS) * (PS ⊓ NJS).relIndex PS = NP.relIndex PS :=
    Subgroup.relIndex_mul_relIndex _ _ _ (le_inf hNP_PS hNP_NJS) inf_le_left
  rw [h10] at h4
  rw [h3, h8] at h2
  rw [hPNJ, h1]
  set X := (PS ⊔ NJS).relIndex JS
  set y := (PS ⊓ NJS).relIndex PS
  set z := NP.relIndex (PS ⊓ NJS)
  have hy : y ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h4; exact (pow_ne_zero _ two_ne_zero) h4.symm
  have hz : z ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h4; exact (pow_ne_zero _ two_ne_zero) h4.symm
  have key : y * X = y * (2 * z) := by
    have : 2 ^ (splitB θ S).ncard = 2 * 2 ^ ((splitB θ S).ncard - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hb]
    rw [h2, this, ← h4]; ring
  have hX : X = 2 * z := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hy) key
  exact ⟨hX, by rw [hX]; exact mul_ne_zero two_ne_zero hz⟩

/-- **Proposition 65:14** (O'Meara 1963, p. 182): $2 \le (J_F : P_FN_{E/F}J_E) < \infty$. (Take $S$ as in 65:13,
`exists_sConventions_strong`.) -/
@[kb "omeara1963" "§65B, 65:14, p. 182"]
theorem two_le_index_principal_sup_range_ideleNorm :
    2 ≤ (PF ⊔ (NE).range).index ∧ (PF ⊔ (NE).range).index ≠ 0 := by
  have hθ0 : θ ≠ 0 := by rintro rfl; exact hθ ⟨0, by simp⟩
  obtain ⟨S, hS, hθS, hE⟩ := exists_sConventions_strong E {θ} (by simpa using hθ0)
  obtain ⟨h13, hfin⟩ := index_principal_sup_range_ideleNorm E hθ hs hS (hθS θ (by simp)) hE
  refine ⟨?_, hfin⟩
  rw [h13]
  have : ((principalSIdeles (spotsAbove (E := E) S)).map NE).relIndex
      (principalSIdeles S ⊓ (sIdeles (spotsAbove (E := E) S)).map NE) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h13; exact hfin h13
  omega

/-! ### Proposition 65:21: the tower -/

omit hθ hs in
/-- The subgroup used to show that O'Meara's tower in the proof of 65:21 is strictly increasing: the idèles $x$ with
$x = (\alpha)\,y$, $\alpha \in \dot F$, $y$ a square at every spot of $\Omega - S$ and a unit at every spot of
$S - V$. -/
def towerBound (S V : Set (HeightOneSpectrum (𝓞 F))) : Subgroup JF where
  carrier := {x | ∃ α : Fˣ, (∀ v ∉ S, IsSquare (ideleAt (x * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹) v)) ∧
    (∀ w : InfinitePlace F, IsSquare (ideleAtInf (x * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹) w)) ∧
    ∀ v ∈ S, v ∉ V → Valued.v (ideleAt (x * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹) v) = 1}
  mul_mem' := by
    rintro x y ⟨α, h1, h2, h3⟩ ⟨β, k1, k2, k3⟩
    have he : x * y * (IdeleGroup.unitEmbedding (𝓞 F) F (α * β))⁻¹ =
        (x * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹) * (y * (IdeleGroup.unitEmbedding (𝓞 F) F β)⁻¹) := by
      rw [map_mul, mul_inv]; ac_rfl
    refine ⟨α * β, fun v hv => ?_, fun w => ?_, fun v hv hV => ?_⟩
    · rw [he, ideleAt_mul]; exact (h1 v hv).mul (k1 v hv)
    · rw [he, ideleAtInf_mul]; exact (h2 w).mul (k2 w)
    · rw [he, ideleAt_mul, map_mul, h3 v hv hV, k3 v hv hV, one_mul]
  one_mem' := ⟨1, fun v _ => by simp, fun w => by simp, fun v _ _ => by simp⟩
  inv_mem' := by
    rintro x ⟨α, h1, h2, h3⟩
    have he : x⁻¹ * (IdeleGroup.unitEmbedding (𝓞 F) F α⁻¹)⁻¹ =
        (x * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv, mul_comm]
    refine ⟨α⁻¹, fun v hv => ?_, fun w => ?_, fun v hv hV => ?_⟩
    · rw [he, ideleAt_inv]; exact (h1 v hv).inv
    · rw [he, ideleAtInf_inv]; exact (h2 w).inv
    · rw [he, ideleAt_inv, map_inv₀, h3 v hv hV, inv_one]

omit hθ hs in
lemma principal_le_towerBound (S V : Set (HeightOneSpectrum (𝓞 F))) : PF ≤ towerBound S V := by
  rintro _ ⟨α, rfl⟩
  exact ⟨α, fun v _ => by simp, fun w => by simp, fun v _ _ => by simp⟩

omit hθ hs in
lemma sqSIdeles_le_towerBound (S V : Set (HeightOneSpectrum (𝓞 F))) : sqSIdeles S ≤ towerBound S V := by
  rintro x ⟨hxS, h1, h2⟩
  refine ⟨1, fun v hv => by simpa using h1 v hv, fun w => by simpa using h2 w, fun v hv _ => ?_⟩
  simpa using hxS v hv

omit hθ hs in
lemma ideleSupportedAt_le_towerBound {S V : Set (HeightOneSpectrum (𝓞 F))} (hVS : V ⊆ S)
    {u : HeightOneSpectrum (𝓞 F)} (hu : u ∈ V) : ideleSupportedAt u ≤ towerBound S V := by
  intro x hx
  rw [mem_ideleSupportedAt_iff] at hx
  refine ⟨1, fun v hv => ?_, fun w => ?_, fun v _ hvV => ?_⟩
  · have : v ≠ u := fun h => hv (h ▸ hVS hu)
    simp [hx.1 v this]
  · simp [hx.2 w]
  · have : v ≠ u := fun h => hvV (h ▸ hu)
    simp [hx.1 v this]

/-- **The square idèles are norms** (O'Meara 1963, p. 185, from Example 65:4): if every spot of $S$ is non-dyadic
and $\theta$ is a unit on $S$, then $J^{S,2} \subseteq N_{E/F}J_E^S \subseteq N_{E/F}J_E$. -/
lemma sqSIdeles_le_range {S : Set (HeightOneSpectrum (𝓞 F))} (h2S : ∀ v ∈ S, (2 : 𝓞 F) ∉ v.asIdeal)
    (hθS : ∀ v ∈ S, v.valuation F θ = 1) : sqSIdeles S ≤ (NE).range := by
  rintro i ⟨hiS, h1, h2⟩
  have := (mem_map_sIdeles_iff_of_unit E hθ hs S h2S hθS i).2 ⟨hiS, fun v hv w hn w' => ?_, fun v w hn w' => ?_⟩
  · obtain ⟨j, -, rfl⟩ := this; exact ⟨j, rfl⟩
  · obtain ⟨y, hy⟩ := h1 v hv
    refine ⟨algebraMap _ _ y, ?_⟩
    rw [localNormFin_apply, Algebra.norm_algebraMap, finrank_eq_of_liesOver hθ hs v w'.1 w.1, hn, hy, sq]
  · obtain ⟨y, hy⟩ := h2 v
    refine ⟨algebraMap _ _ y, ?_⟩
    have hn' : Module.finrank v.Completion w'.1.Completion = 2 := by
      rw [finrank_eq_two_iff_not_isSquare_inf hθ hs v w'.1, ← finrank_eq_two_iff_not_isSquare_inf hθ hs v w.1]
      exact hn
    rw [localNormInf_apply, Algebra.norm_algebraMap, hn', hy, sq]

/-- If $\theta$ is a square at the finite spot $\mathfrak p$, then $I_\mathfrak p \subseteq N_{E/F}J_E$ (O'Meara 1963,
p. 185, by Example 65:2). -/
lemma ideleSupportedAt_le_range_of_isSquare (v : HeightOneSpectrum (𝓞 F))
    (hv : IsSquare (algebraMap F (v.adicCompletion F) θ)) : ideleSupportedAt v ≤ (NE).range := by
  have h := relIndex_ideleSupportedAt_inf_range E hθ hs v
  rw [if_pos hv, Subgroup.relIndex_eq_one] at h
  exact fun x hx => (h hx).1

omit [Algebra.IsQuadraticExtension F E] hθ hs in
/-- **The tower is strictly increasing** (O'Meara 1963, pp. 185–186, step 2 of the proof of 65:21): with
$\mathfrak p_1, \dots, \mathfrak p_s$ as in 65:18, $I_{\mathfrak p_j} \not\subseteq$ the group generated by $P_F$,
$J^{S,2}$ and the $I_{\mathfrak p_k}$, $k \in U$, when $j \notin U$ (a prime element at $\mathfrak p_j$ would be
$(\alpha)\mathfrak t$ with $\alpha$ a square by 65:18a, but $\alpha$ is a prime element at $\mathfrak p_j$). -/
lemma not_ideleSupportedAt_le_towerBound (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hS' : SConventions (F := F) (↑T)ᶜ)
    {e : Fin (T.card + Fintype.card (InfinitePlace F)) → HN.SUnit (F := F) T} (he : IsGenModSq T e)
    {p : Fin (T.card + Fintype.card (InfinitePlace F)) → HeightOneSpectrum (𝓞 F)} (hpinj : Function.Injective p)
    (hpT : ∀ i, p i ∉ T) (hp : ∀ i j, SqAt (p i) ((e j : Fˣ) : F) ↔ j ≠ i)
    (U : Finset (Fin (T.card + Fintype.card (InfinitePlace F)))) {j : Fin (T.card + Fintype.card (InfinitePlace F))}
    (hj : j ∉ U) : ¬ ideleSupportedAt (p j) ≤ towerBound (↑T)ᶜ (p '' ↑U) := by
  intro hle
  obtain ⟨π, hπ⟩ := (p j).valuation_exists_uniformizer F
  have hπ0 : algebraMap F ((p j).adicCompletion F) π ≠ 0 := by
    intro h0
    have := valued_alg (p j) π
    rw [h0, map_zero, hπ] at this
    exact WithZero.exp_ne_zero this.symm
  set u : ((p j).adicCompletion F)ˣ := Units.mk0 _ hπ0
  set x := IdeleGroup.ofAdicCompletion (𝓞 F) F (p j) u
  obtain ⟨α, h1, h2, h3⟩ := hle ⟨u, rfl⟩
  have hcomp : ∀ v, ideleAt (x * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹) v =
      ideleAt x v * (algebraMap F (v.adicCompletion F) (α : F))⁻¹ := fun v => by
    rw [ideleAt_mul, ideleAt_inv, ideleAt_unitEmbedding]
  have hcompI : ∀ w, ideleAtInf (x * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹) w =
      (algebraMap F w.Completion (α : F))⁻¹ := fun w => by
    rw [ideleAtInf_mul, ideleAtInf_inv, ideleAtInf_unitEmbedding, ideleAtInf_ofAdic, one_mul]
  have hα0 : (α : F) ≠ 0 := α.ne_zero
  have hsq : ∀ v ∈ T, SqAt v (α : F) := by
    intro v hv
    have hvj : v ≠ p j := fun h => hpT j (h ▸ hv)
    have := h1 v (by simpa using hv)
    rw [hcomp, ideleAt_ofAdic_ne _ _ hvj, one_mul] at this
    simpa using this.inv
  have hinf : ∀ w : InfinitePlace F, IsSquare (algebraMap F w.Completion (α : F)) := by
    intro w
    have := h2 w
    rw [hcompI] at this
    simpa using this.inv
  have hunit : ∀ v, v ∉ T → v ∉ Set.range p → v.valuation F (α : F) = 1 := by
    intro v hvT hvp
    have hvj : v ≠ p j := fun h => hvp ⟨j, h.symm⟩
    have hvU : v ∉ p '' ↑U := fun ⟨k, _, hk⟩ => hvp ⟨k, hk⟩
    have := h3 v (by simpa using hvT) hvU
    rw [hcomp, ideleAt_ofAdic_ne _ _ hvj, one_mul, map_inv₀, inv_eq_one, valued_alg] at this
    exact this
  have hαsq := isSquare_of_dual_spots T hS' he hpT hp hα0 hsq hinf hunit
  -- but `α` is a prime element at `𝔭_j`
  have hjU : p j ∉ p '' ↑U := fun ⟨k, hk, hkj⟩ => hj (hpinj hkj ▸ hk)
  have hv := h3 (p j) (by simpa using hpT j) hjU
  rw [hcomp, ideleAt_ofAdic_self, Units.val_mk0, map_mul, map_inv₀, valued_alg, valued_alg, hπ,
    mul_inv_eq_one₀] at hv
  · obtain ⟨c, hc⟩ := hαsq
    have hc0 : c ≠ 0 := by rintro rfl; exact hα0 (by simpa using hc)
    rw [hc, map_mul] at hv
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (p j).valuation F c = WithZero.exp k :=
      ⟨WithZero.log _, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hc0)).symm⟩
    rw [hk, ← WithZero.exp_add, WithZero.exp_inj] at hv
    omega
  · rw [← valued_alg]; exact (map_ne_zero _).2 ((map_ne_zero _).2 hα0)

/-- **The bound $(J_F : P_FN_{E/F}J_E) \le 2$** (O'Meara 1963, pp. 185–186, the proof of 65:21): with $S$ as in §65A
and $\theta$ a unit on $S$, the tower $P_FJ^{S,2} = \Phi_1 \subsetneq \Phi_2 \subsetneq \dots \subsetneq \Phi_s
\subseteq P_FN_{E/F}J_E$, $\Phi_j = I_{\mathfrak p_j}\Phi_{j-1}$, and $(J_F : P_FJ^{S,2}) = 2^s$ (65:12). -/
theorem index_principal_sup_range_ideleNorm_le_two :
    (PF ⊔ (NE).range).index ≤ 2 := by
  classical
  have hθ0 : θ ≠ 0 := by rintro rfl; exact hθ ⟨0, by simp⟩
  obtain ⟨S, hS, hθS', -⟩ := exists_sConventions_strong E {θ} (by simpa using hθ0)
  have hθS : ∀ v ∈ S, v.valuation F θ = 1 := hθS' θ (by simp)
  set T := hS.cofinite.toFinset with hT
  have hST : ((T : Set (HeightOneSpectrum (𝓞 F)))ᶜ) = S := by ext v; simp [hT]
  have hS' : SConventions (F := F) (↑T)ᶜ := hST ▸ hS
  -- `θ` as an `S`-unit, extended to generators `e` with dual spots `p`
  have hθu : Units.mk0 θ hθ0 ∈ HN.SUnit (F := F) T := by
    rw [HN.mem_sUnit_iff]
    intro w hw
    have hwS : w ∈ S := by simpa [hT] using hw
    rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, Units.val_mk0, hθS w hwS]
    rfl
  obtain ⟨e, he, i₀, hi₀⟩ := exists_isGenModSq_mem T (ε := ⟨_, hθu⟩) hθ
  obtain ⟨p, hpinj, hpT2, hp⟩ := exists_dual_spots T he
  have hpT : ∀ i, p i ∉ T := fun i => (hpT2 i).1
  have he₀ : ((e i₀ : Fˣ) : F) = θ := by rw [hi₀]; rfl
  have hpS : ∀ i, p i ∈ S := fun i => by rw [← hST]; exact hpT i
  -- the tower
  let Φ : Finset (Fin (T.card + Fintype.card (InfinitePlace F))) → Subgroup JF := fun U =>
    (PF ⊔ sqSIdeles S) ⊔ ⨆ j ∈ U, ideleSupportedAt (p j)
  have hΦ0 : Φ ∅ = PF ⊔ sqSIdeles S := by simp [Φ]
  have hΦmono : ∀ {U V}, U ⊆ V → Φ U ≤ Φ V := fun hUV =>
    sup_le_sup_left (biSup_mono fun j hj => hUV hj) _
  have hΦtb : ∀ U, Φ U ≤ towerBound S (p '' ↑U) := fun U =>
    sup_le (sup_le (principal_le_towerBound _ _) (sqSIdeles_le_towerBound _ _))
      (iSup₂_le fun j hj => ideleSupportedAt_le_towerBound (by rintro _ ⟨k, -, rfl⟩; exact hpS k)
        ⟨j, hj, rfl⟩)
  have hΦle : ∀ U ⊆ Finset.univ.erase i₀, Φ U ≤ PF ⊔ (NE).range := fun U hU =>
    sup_le (sup_le le_sup_left (le_trans (sqSIdeles_le_range E hθ hs hS.nondyadic hθS) le_sup_right))
      (iSup₂_le fun j hj => by
        have hji : j ≠ i₀ := Finset.ne_of_mem_erase (hU hj)
        have hsqj : SqAt (p j) θ := by rw [← he₀]; exact (hp j i₀).2 (Ne.symm hji)
        exact le_trans (ideleSupportedAt_le_range_of_isSquare E hθ hs (p j) hsqj) le_sup_right)
  -- `(J_F : Φ ∅) = 2^s`
  have hidx0 : (Φ ∅).index = 2 ^ (T.card + Fintype.card (InfinitePlace F)) := by
    rw [hΦ0, index_principal_sup_sqSIdeles hS, ncard_outsideS hS.cofinite]
  have hne0 : ∀ K, Φ ∅ ≤ K → (Φ ∅).relIndex K ≠ 0 := fun K hK h0 => by
    have := Subgroup.relIndex_dvd_index_of_le hK
    rw [h0, hidx0, zero_dvd_iff] at this
    exact pow_ne_zero _ two_ne_zero this
  -- each step at least doubles the index
  have hrel : ∀ U ⊆ Finset.univ.erase i₀, 2 ^ U.card ≤ (Φ ∅).relIndex (Φ U) := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro _; simp [Subgroup.relIndex_self]
    | insert j U hjU ih =>
      intro hsub
      have hU : U ⊆ Finset.univ.erase i₀ := (Finset.subset_insert j U).trans hsub
      have hmono : Φ U ≤ Φ (insert j U) := hΦmono (Finset.subset_insert j U)
      have hIj : ideleSupportedAt (p j) ≤ Φ (insert j U) :=
        le_sup_of_le_right (le_iSup₂_of_le j (Finset.mem_insert_self j U) le_rfl)
      have hstrict : ¬ Φ (insert j U) ≤ Φ U := fun h =>
        not_ideleSupportedAt_le_towerBound T hS' he hpinj hpT hp U hjU
          (hST.symm ▸ (hIj.trans (h.trans (hΦtb U))))
      have hmul := Subgroup.relIndex_mul_relIndex (Φ ∅) (Φ U) (Φ (insert j U))
        (hΦmono (Finset.empty_subset U)) hmono
      have hne : (Φ U).relIndex (Φ (insert j U)) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hmul
        exact hne0 _ (hΦmono (Finset.empty_subset _)) hmul.symm
      have hne1 : (Φ U).relIndex (Φ (insert j U)) ≠ 1 := fun h1 =>
        hstrict (Subgroup.relIndex_eq_one.1 h1)
      rw [Finset.card_insert_of_notMem hjU, pow_succ, ← hmul]
      exact Nat.mul_le_mul (ih hU) (by omega)
  -- conclude
  set U₀ := Finset.univ.erase i₀
  have hcard : U₀.card + 1 = T.card + Fintype.card (InfinitePlace F) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.sub_add_cancel (Fin.pos_iff_nonempty.2 ⟨i₀⟩)]
  have ha := hrel U₀ subset_rfl
  have e1 := Subgroup.relIndex_mul_relIndex (Φ ∅) (Φ U₀) (PF ⊔ (NE).range)
    (hΦmono (Finset.empty_subset _)) (hΦle U₀ subset_rfl)
  have e2 := Subgroup.relIndex_mul_relIndex (Φ ∅) (PF ⊔ (NE).range) ⊤
    ((hΦmono (Finset.empty_subset _)).trans (hΦle U₀ subset_rfl)) le_top
  rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, hidx0, ← e1] at e2
  set a := (Φ ∅).relIndex (Φ U₀)
  set b := (Φ U₀).relIndex (PF ⊔ (NE).range)
  set X := (PF ⊔ (NE).range).index
  have hb : b ≠ 0 := by
    intro h0; rw [h0, mul_zero, zero_mul] at e2; exact (pow_ne_zero _ two_ne_zero) e2.symm
  have h2a : 2 ^ (T.card + Fintype.card (InfinitePlace F)) ≤ 2 * a := by
    rw [← hcard, pow_succ, mul_comm]; exact Nat.mul_le_mul_left 2 ha
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, zero_mul, zero_mul] at e2; exact absurd e2.symm (pow_ne_zero _ two_ne_zero)
    · exact h
  have : a * (b * X) ≤ a * 2 := by rw [← mul_assoc, e2, mul_comm a 2]; exact h2a
  have hbX : b * X ≤ 2 := Nat.le_of_mul_le_mul_left this hapos
  exact le_trans (Nat.le_mul_of_pos_left X (Nat.pos_of_ne_zero hb)) hbX

/-- **Proposition 65:21** (O'Meara 1963, p. 185): $(J_F : P_FN_{E/F}J_E) = 2$. (By 65:14 it is $\ge 2$; the bound
$\le 2$ is `index_principal_sup_range_ideleNorm_le_two`.) -/
@[kb "omeara1963" "§65D, 65:21, p. 185 ((J_F : P_F N_{E/F} J_E) = 2)"]
theorem index_principal_sup_range_ideleNorm_eq_two : (PF ⊔ (NE).range).index = 2 :=
  le_antisymm (index_principal_sup_range_ideleNorm_le_two E hθ hs)
    (two_le_index_principal_sup_range_ideleNorm E hθ hs).1

/-- **Proposition 65:22** (O'Meara 1963, p. 186): suppose $S$ satisfies the conventions of §65A, $\theta$ is a unit at
all spots in $S$, and $J_E = P_E J_E^S$. Then $P_F^S \cap N_{E/F}J_E^S = N_{E/F}P_E^S$ (from 65:13 and 65:21). -/
@[kb "omeara1963" "§65D, 65:22, p. 186 (P_F^S ∩ N_{E/F} J_E^S = N_{E/F} P_E^S)"]
theorem principalSIdeles_inf_map_sIdeles {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    (hθS : ∀ v ∈ S, v.valuation F θ = 1)
    (hE : ∀ i : IdeleGroup (𝓞 E) E, ∃ p ∈ IdeleGroup.principalSubgroup (𝓞 E) E,
      ∃ j ∈ sIdeles (spotsAbove (E := E) S), i = p * j) :
    principalSIdeles S ⊓ (sIdeles (spotsAbove (E := E) S)).map NE =
      (principalSIdeles (spotsAbove (E := E) S)).map NE := by
  obtain ⟨h13, -⟩ := index_principal_sup_range_ideleNorm E hθ hs hS hθS hE
  rw [index_principal_sup_range_ideleNorm_eq_two E hθ hs] at h13
  have h1 : ((principalSIdeles (spotsAbove (E := E) S)).map NE).relIndex
      (principalSIdeles S ⊓ (sIdeles (spotsAbove (E := E) S)).map NE) = 1 := by omega
  rw [Subgroup.relIndex_eq_one] at h1
  exact le_antisymm h1 (le_inf (map_principalSIdeles_le S) (Subgroup.map_mono inf_le_left))

end QuadFormsKB.OMeara
