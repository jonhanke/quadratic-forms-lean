/-
# O'Meara §82I: the lattice $L^{\mathfrak a}$ over a Dedekind domain

**Setting.** $R$ is a Dedekind domain with fraction field $F$, $2 \in F^\times$, and $(V, Q)$ a finite-dimensional
quadratic space over $F$ with O'Meara's bilinear form $B$ = `bil Q`. For a regular lattice $L$ and a fractional ideal
$\mathfrak a$, $L^{\mathfrak a} = \{x \in L : B(x, L) \subseteq \mathfrak a\}$ is `subA Q a L` (`Sec82.lean`), and
$L^\#$ is `dual Q L` (`Sec82Dual.lean`).

**Proves** (O'Meara 1963, §82I, p. 237):
* `subA_eq_smul_dual_inf` ($L^{\mathfrak a} = \mathfrak aL^\# \cap L$) and `span_subA` ($FL^{\mathfrak a} = FL$);
* `bil_subA_mem` ($B(L^{\mathfrak a}, L) \subseteq \mathfrak a$), `Dedekind.scale_subA_le`
  ($\mathfrak sL^{\mathfrak a} \subseteq \mathfrak a$), `subA_eq_self_iff` ($L^{\mathfrak a} = L$ if and only if
  $\mathfrak sL \subseteq \mathfrak a$);
* `IsOrthSum.subA` ($(J \perp K)^{\mathfrak a} = J^{\mathfrak a} \perp K^{\mathfrak a}$);
* `smul_subA_le_subA`, `subA_mono` ($\mathfrak a\mathfrak b^{-1}L^{\mathfrak b} \subseteq L^{\mathfrak a} \subseteq
  L^{\mathfrak b}$ if $\mathfrak a \subseteq \mathfrak b$);
* `subA_of_isModular_of_le`, `subA_of_isModular_of_ge` ($L^{\mathfrak a}$ for a $\mathfrak b$-modular $L$).
-/
import QuadFormsKB.Literature.OMeara.Sec82Dual

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Ring

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **$B(L^{\mathfrak a}, L) \subseteq \mathfrak a$** (O'Meara 1963, §82I, p. 237). -/
@[kb "omeara1963" "§82I, p. 237 (B(L^a, L) ⊆ a)"]
theorem bil_subA_mem {a : Submodule R F} {L : Submodule R V} {x y : V} (hx : x ∈ subA Q a L) (hy : y ∈ L) :
    bil Q x y ∈ a :=
  hx.2 y hy

/-- **$\mathfrak sL^{\mathfrak a} \subseteq \mathfrak a$** (O'Meara 1963, §82I, p. 237); any commutative ring. -/
@[kb "omeara1963" "§82I, p. 237 (sL^a ⊆ a)"]
theorem Dedekind.scale_subA_le (a : Submodule R F) (L : Submodule R V) : scale Q (subA Q a L) ≤ a := by
  rw [scale, span_le]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact hx.2 y hy.1

/-- **$L^{\mathfrak a} = L$ if and only if $\mathfrak sL \subseteq \mathfrak a$** (O'Meara 1963, §82I, p. 237). -/
@[kb "omeara1963" "§82I, p. 237 (L^a = L iff sL ⊆ a)"]
theorem subA_eq_self_iff {a : Submodule R F} {L : Submodule R V} : subA Q a L = L ↔ scale Q L ≤ a := by
  constructor
  · intro h
    rw [scale, span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hx' : x ∈ subA Q a L := by rw [h]; exact hx
    exact hx'.2 y hy
  · intro h
    exact le_antisymm (fun _ hx => hx.1) fun _ hx => ⟨hx, fun _ hy => h (bil_mem_scale Q hx hy)⟩

/-- **$(J \perp K)^{\mathfrak a} = J^{\mathfrak a} \perp K^{\mathfrak a}$** (O'Meara 1963, §82I, p. 237). -/
@[kb "omeara1963" "§82I, p. 237 (L^a = J^a ⊥ K^a for L = J ⊥ K)"]
theorem IsOrthSum.subA {a : Submodule R F} {L J K : Submodule R V} (h : IsOrthSum Q L J K) :
    IsOrthSum Q (subA Q a L) (subA Q a J) (subA Q a K) := by
  have hJL : J ≤ L := h.sup_eq ▸ le_sup_left
  have hKL : K ≤ L := h.sup_eq ▸ le_sup_right
  have hKJ : ∀ k ∈ K, ∀ j ∈ J, bil Q k j = 0 := fun k hk j hj => by rw [bil_comm]; exact h.orth j hj k hk
  refine ⟨fun x hx y hy => h.orth x hx.1 y hy.1, ?_, ?_⟩
  · exact h.disjoint.mono (fun _ hx => hx.1) (fun _ hx => hx.1)
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · intro x hx
        refine ⟨hJL hx.1, fun y hy => ?_⟩
        rw [← h.sup_eq, mem_sup] at hy
        obtain ⟨j, hj, k, hk, rfl⟩ := hy
        rw [bil_add_right, h.orth x hx.1 k hk, add_zero]
        exact hx.2 j hj
      · intro x hx
        refine ⟨hKL hx.1, fun y hy => ?_⟩
        rw [← h.sup_eq, mem_sup] at hy
        obtain ⟨j, hj, k, hk, rfl⟩ := hy
        rw [bil_add_right, hKJ x hx.1 j hj, zero_add]
        exact hx.2 k hk
    · intro x hx
      have hx1 := hx.1
      rw [← h.sup_eq, mem_sup] at hx1
      obtain ⟨j, hj, k, hk, rfl⟩ := hx1
      refine add_mem (mem_sup_left ⟨hj, fun y hy => ?_⟩) (mem_sup_right ⟨hk, fun y hy => ?_⟩)
      · have := hx.2 y (hJL hy)
        rwa [bil_add_left, hKJ k hk y hy, add_zero] at this
      · have := hx.2 y (hKL hy)
        rwa [bil_add_left, h.orth j hj y hy, zero_add] at this

/-- **$L^{\mathfrak a} \subseteq L^{\mathfrak b}$ if $\mathfrak a \subseteq \mathfrak b$** (O'Meara 1963, §82I,
p. 237). -/
@[kb "omeara1963" "§82I, p. 237 (L^a ⊆ L^b if a ⊆ b)"]
theorem subA_mono {a b : Submodule R F} (hab : a ≤ b) (L : Submodule R V) : subA Q a L ≤ subA Q b L :=
  fun _ hx => ⟨hx.1, fun y hy => hab (hx.2 y hy)⟩

end Ring

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- Helper: $\mathfrak c L \subseteq L$ when $\mathfrak c \subseteq \mathfrak o$. -/
theorem smul_le_of_le_one {c : Submodule R F} (hc : c ≤ 1) (L : Submodule R V) : c • L ≤ L := by
  rw [Submodule.smul_le]
  intro r hr n hn
  obtain ⟨s, rfl⟩ := Submodule.mem_one.1 (hc hr)
  rw [algebraMap_smul]
  exact L.smul_mem s hn

/-- Helper: $B(\mathfrak aL^\#, L) \subseteq \mathfrak a$. -/
theorem bil_smul_dual_mem {a : Submodule R F} {L : Submodule R V} {z : V} (hz : z ∈ a • dual Q L) {y : V}
    (hy : y ∈ L) : bil Q z y ∈ a := by
  refine Submodule.smul_induction_on hz (fun r hr n hn => ?_) (fun x x' hx hx' => ?_)
  · rw [bil_smul_left]
    simpa using mul_mem_mul hr (hn.2 y hy)
  · rw [bil_add_left]; exact a.add_mem hx hx'

/-- **$L^{\mathfrak a} = \mathfrak aL^\# \cap L$** (O'Meara 1963, §82I, p. 237) for a lattice $L$ (O'Meara: regular) and a
fractional ideal $\mathfrak a$. -/
@[kb "omeara1963" "§82I, p. 237 (L^a = aL# ∩ L)"]
theorem subA_eq_smul_dual_inf {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) (L : Submodule R V) :
    subA Q a L = a • dual Q L ⊓ L := by
  ext x
  constructor
  · rintro ⟨hxL, hx⟩
    refine ⟨?_, hxL⟩
    have h1 := mul_one_div_cancel_of_fg ha ha0
    have h1' : (1 : F) ∈ a * (1 / a) := by
      rw [h1]; exact Submodule.one_le.1 le_rfl
    have key : ∀ t ∈ a * (1 / a), t • x ∈ a • dual Q L := by
      intro t ht
      refine Submodule.mul_induction_on ht (fun m hm n hn => ?_) (fun u v hu hv => ?_)
      · rw [mul_smul]
        refine smul_mem_smul hm ⟨?_, fun y hy => ?_⟩
        · exact Submodule.smul_mem _ _ (subset_span hxL)
        · rw [bil_smul_left]
          have := mul_mem_mul hn (hx y hy)
          rwa [mul_comm (1 / a) a, mul_one_div_cancel_of_fg ha ha0] at this
      · rw [add_smul]; exact add_mem hu hv
    simpa using key 1 h1'
  · rintro ⟨hz, hxL⟩
    exact ⟨hxL, fun y hy => bil_smul_dual_mem Q hz hy⟩

/-- **$FL^{\mathfrak a} = FL$** (O'Meara 1963, §82I, p. 237) for a regular lattice $L$ and a fractional ideal
$\mathfrak a$. -/
@[kb "omeara1963" "§82I, p. 237 (FL^a = FL)"]
theorem span_subA {a : Submodule R F} (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.FG) :
    span F (subA Q a L : Set V) = span F (L : Set V) := by
  apply le_antisymm (span_mono fun _ hx => hx.1)
  -- a nonzero `d : R` with `d • scale ⊆ a`
  obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha0
  obtain ⟨⟨n, m⟩, hnm⟩ := IsLocalization.surj (S := F) (nonZeroDivisors R) α
  have hm0 : algebraMap R F (m : R) ≠ 0 := by
    have : (m : R) ≠ 0 := nonZeroDivisors.coe_ne_zero m
    exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 this
  have hnmem : algebraMap R F n ∈ a := by
    rw [← hnm]; exact a.smul_mem (m : R) hα |> fun h => by simpa [Algebra.smul_def, mul_comm] using h
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at hnm
    exact hα0 ((mul_eq_zero.1 hnm).resolve_right hm0)
  obtain ⟨b, hb0', hb⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) (scale_fg Q hL)
  have hd : ∀ s ∈ scale Q L, algebraMap R F (n * b) * s ∈ a := by
    intro s hs
    obtain ⟨r, hr⟩ := hb s hs
    have : algebraMap R F (n * b) * s = algebraMap R F r * algebraMap R F n := by
      have hr' : algebraMap R F r = algebraMap R F b * s := by rw [hr, Algebra.smul_def]
      rw [map_mul, hr']; ring
    rw [this]
    simpa [Algebra.smul_def] using a.smul_mem r hnmem
  have hdb : algebraMap R F (n * b) ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 (mul_ne_zero hn0 ?_)
    exact nonZeroDivisors.ne_zero hb0'
  rw [span_le]
  intro x hx
  have hmem : algebraMap R F (n * b) • x ∈ subA Q a L := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [algebraMap_smul]; exact L.smul_mem _ hx
    · rw [bil_smul_left]; exact hd _ (bil_mem_scale Q hx hy)
  have : x = (algebraMap R F (n * b))⁻¹ • (algebraMap R F (n * b) • x) := by
    rw [smul_smul, inv_mul_cancel₀ hdb, one_smul]
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (subset_span hmem)

/-- **$\mathfrak a\mathfrak b^{-1}L^{\mathfrak b} \subseteq L^{\mathfrak a}$ if $\mathfrak a \subseteq \mathfrak b$**
(O'Meara 1963, §82I, p. 237; the inclusion is garbled in the OCR text and restored from the definitions). -/
@[kb "omeara1963" "§82I, p. 237 (ab⁻¹L^b ⊆ L^a if a ⊆ b)"]
theorem smul_subA_le_subA {a b : Submodule R F} (hb : b.FG) (hb0 : b ≠ ⊥) (hab : a ≤ b) (L : Submodule R V) :
    (a * (1 / b)) • subA Q b L ≤ subA Q a L := by
  have h1 := mul_one_div_cancel_of_fg hb hb0
  have hle : a * (1 / b) ≤ 1 := le_of_le_of_eq (Submodule.mul_le.2 fun m hm n hn => Submodule.mul_mem_mul (hab hm) hn) h1
  rw [Submodule.smul_le]
  intro t ht x hx
  refine ⟨smul_le_of_le_one hle L (smul_mem_smul ht hx.1), fun y hy => ?_⟩
  rw [bil_smul_left]
  have := mul_mem_mul ht (hx.2 y hy)
  have e : a * (1 / b) * b = a := by rw [mul_assoc, mul_comm (1 / b) b, h1, mul_one]
  rwa [e] at this


/-- **$L^{\mathfrak a}$ of a modular lattice, first case** (O'Meara 1963, §82I, p. 237): if $L$ is
$\mathfrak b$-modular and $\mathfrak b \subseteq \mathfrak a$ then $L^{\mathfrak a} = L$. -/
@[kb "omeara1963" "§82I, p. 237 (L^a = L for b-modular L, b ⊆ a)"]
theorem subA_of_isModular_of_le {a b : Submodule R F} {L : Submodule R V} (hL : IsModular Q b L)
    (hba : b ≤ a) : subA Q a L = L :=
  (subA_eq_self_iff Q).2 (hL.2.1 ▸ hba)

/-- **$L^{\mathfrak a}$ of a modular lattice, second case** (O'Meara 1963, §82I, p. 237): if $L$ is
$\mathfrak b$-modular and $\mathfrak b \supseteq \mathfrak a$ ($\mathfrak a$ a fractional ideal) then
$L^{\mathfrak a} = \mathfrak a\mathfrak b^{-1}L$, since $L^{\mathfrak a} = \mathfrak aL^\# \cap L =
\mathfrak a\mathfrak b^{-1}L \cap L$. -/
@[kb "omeara1963" "§82I, p. 237 (L^a = ab⁻¹L for b-modular L, b ⊇ a)"]
theorem subA_of_isModular_of_ge {a b : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V}
    (hL : IsModular Q b L) (hLfg : L.FG) (hab : a ≤ b) : subA Q a L = (a * (1 / b)) • L := by
  have hbfg : b.FG := hL.2.1 ▸ scale_fg Q hLfg
  have hreg := isRegular_of_isModular Q hL hLfg
  have h1 := mul_one_div_cancel_of_fg hbfg hL.1
  have hle : a * (1 / b) ≤ 1 := le_of_le_of_eq (Submodule.mul_le.2 fun m hm n hn => Submodule.mul_mem_mul (hab hm) hn) h1
  rw [subA_eq_smul_dual_inf Q ha ha0 L, dual_eq_of_isModular Q hL hLfg, ← Submodule.smul_assoc]
  exact inf_eq_left.2 (smul_le_of_le_one hle L)

end Dedekind

end QuadFormsKB.OMeara
