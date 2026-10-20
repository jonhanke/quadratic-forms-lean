/-
# Stabilizers of lattices are commensurable

**Layer:** lattices in $(F^n, Q)$ over a number field (`Lattices/`), and the finite adelic orthogonal group
$O(V)(\mathbb A_f)$ = `OAf Q` acting on them (`Lattices/ClassSet.lean`).

**Proves** `commensurable_locStab`: for any two lattices $L, M \subseteq F^n$ the adelic stabilizers $O(\hat L)$ and
$O(\hat M)$ are commensurable, i.e. $O(\hat L) \cap O(\hat M)$ has finite index in both. This is the discrete content of
"compact open subgroups of $O(V)(\mathbb A_f)$ are commensurable", which `idxVol` and `dcMass_mul_idxVol` need.

*Proof.* Choose $d \ne 0$ in $\mathcal O_F$ with $dL \subseteq M$ and $dM \subseteq L$ (`exists_sandwich`). For
$k \in O(\hat L)$ the lattice $kM$ satisfies the same two inclusions (`sandwich_latSMul`, prime by prime), so the orbit
$O(\hat L)\cdot M$ lies in the set of lattices $M'$ with $dL \subseteq M'$, $dM' \subseteq L$. That set is finite
(`finite_sandwich`): all such $M'$ lie between $kL'$ and $L' = d^{-1}L$ for an integer $k \ne 0$, and they are
determined by their images in $L'/kL' \cong (\mathbb Z/k)^r$. The index of $O(\hat L) \cap O(\hat M)$ in $O(\hat L)$ is the
size of the orbit (`MulAction.index_stabilizer`).
-/
import QuadFormsKB.Tamagawa.MassFormula

open NumberField IsDedekindDomain Matrix MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- **Two lattices are mutually sandwiched:** for lattices $L, M$ there is $d \ne 0$ in $\mathcal O_F$ with
$dL \subseteq M$ and $dM \subseteq L$. -/
theorem exists_sandwich {L M : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) (hM : M.IsLattice F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ (∀ x ∈ L, d • x ∈ M) ∧ (∀ x ∈ M, d • x ∈ L) := by
  obtain ⟨d₁, hd₁, h₁, h₁'⟩ := exists_global_bounds hL
  obtain ⟨d₂, hd₂, h₂, h₂'⟩ := exists_global_bounds hM
  refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_comm, mul_smul]; exact h₂ _ (h₁' x hx)
  · rw [mul_smul]; exact h₁ _ (h₂' x hx)

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Scaling inclusions localize: if $dL \subseteq M$ then $d L_\mathfrak p \subseteq M_\mathfrak p$. -/
theorem smul_mem_loc_of {L M : Submodule (𝓞 F) (Fin n → F)} {d : 𝓞 F} (h : ∀ x ∈ L, d • x ∈ M)
    {y : Fin n → Fv} (hy : y ∈ loc v L) : algebraMap (𝓞 F) 𝔬 d • y ∈ loc v M := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← locVec_smul_int]
    exact locVec_mem_loc v (h x hx)
  | zero => rw [smul_zero]; exact (loc v M).zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact (loc v M).add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact (loc v M).smul_mem c hy

theorem smul_mem_locAct {g : GL (Fin n) Fv} {M : Submodule 𝔬 (Fin n → Fv)} {c : 𝔬} {y : Fin n → Fv}
    (hy : c • y ∈ M) : c • (g.val *ᵥ y) ∈ locAct v g M := by
  refine ⟨c • y, hy, ?_⟩
  simp only [LinearMap.coe_restrictScalars, mulVecLin_apply]
  rw [show (c • y : Fin n → Fv) = (c : Fv) • y from rfl, mulVec_smul]
  rfl

variable {v}

variable (Q : QuadForm F n)

/-- **The sandwich is preserved by $O(\hat L)$:** if $dL \subseteq M$ and $dM \subseteq L$, then for every
$k \in O(\hat L)$ also $dL \subseteq kM$ and $d(kM) \subseteq L$. -/
theorem sandwich_latSMul {L M : Lat F n} {d : 𝓞 F} (h1 : ∀ x ∈ L.1, d • x ∈ M.1) (h2 : ∀ x ∈ M.1, d • x ∈ L.1)
    {k : OAf Q} (hk : k ∈ locStab Q L) :
    (∀ x ∈ L.1, d • x ∈ (latSMul Q k M).1) ∧ (∀ x ∈ (latSMul Q k M).1, d • x ∈ L.1) := by
  constructor
  · intro x hx
    rw [mem_iff_forall_loc (latSMul Q k M).2]
    intro w
    rw [loc_latSMul, locVec_smul_int]
    have hxw : locVec w x ∈ locAct w ((k w : orthGroup Q _) : GL (Fin n) _) (loc w L.1) := by
      rw [hk w]; exact locVec_mem_loc w hx
    obtain ⟨y, hy, hyx⟩ := hxw
    simp only [LinearMap.coe_restrictScalars, mulVecLin_apply] at hyx
    rw [← hyx]
    exact smul_mem_locAct w (smul_mem_loc_of w h1 hy)
  · intro x hx
    rw [mem_iff_forall_loc L.2]
    intro w
    have hxw : locVec w x ∈ loc w (latSMul Q k M).1 := locVec_mem_loc w hx
    rw [loc_latSMul] at hxw
    obtain ⟨y, hy, hyx⟩ := hxw
    simp only [LinearMap.coe_restrictScalars, mulVecLin_apply] at hyx
    rw [locVec_smul_int, ← hyx, ← hk w]
    exact smul_mem_locAct w (smul_mem_loc_of w h2 hy)

/-- **Finitely many sandwiched lattices:** for a lattice $L$ and $d \ne 0$, only finitely many lattices $M'$ satisfy
$dL \subseteq M'$ and $dM' \subseteq L$. -/
theorem finite_sandwich (L : Lat F n) {d : 𝓞 F} (hd : d ≠ 0) :
    {M' : Lat F n | (∀ x ∈ L.1, d • x ∈ M'.1) ∧ (∀ x ∈ M'.1, d • x ∈ L.1)}.Finite := by
  classical
  -- the lattice L' = d⁻¹ L
  let L' : Submodule (𝓞 F) (Fin n → F) :=
    { carrier := {x | d • x ∈ L.1}
      add_mem' := fun {a b} ha hb => by
        show d • (a + b) ∈ L.1
        rw [smul_add]; exact L.1.add_mem ha hb
      zero_mem' := by show d • (0 : Fin n → F) ∈ L.1; rw [smul_zero]; exact L.1.zero_mem
      smul_mem' := fun c x hx => by
        show d • (c • x) ∈ L.1
        rw [smul_comm]; exact L.1.smul_mem c hx }
  have hmemL' : ∀ x, x ∈ L' ↔ d • x ∈ L.1 := fun _ => Iff.rfl
  obtain ⟨d₁, hd₁, h₁, h₁'⟩ := exists_global_bounds L.2
  have hL' : L'.IsLattice F := by
    refine isLattice_of_global_bounds (d := d₁ * d) (mul_ne_zero hd₁ hd) (fun x hx => ?_) (fun x hx => ?_)
    · rw [hmemL', smul_smul, show d * (d₁ * d) = (d * d) * d₁ by ring, mul_smul]
      exact L.1.smul_mem _ (h₁ x hx)
    · rw [mul_smul]
      exact h₁' _ ((hmemL' x).mp hx)
  -- an integer k with d² ∣ k
  obtain ⟨k, hk0, e, he⟩ := exists_int_dvd (mul_ne_zero hd hd)
  set S := {M' : Lat F n | (∀ x ∈ L.1, d • x ∈ M'.1) ∧ (∀ x ∈ M'.1, d • x ∈ L.1)}
  have hsub : ∀ M' ∈ S, ∀ x ∈ M'.1, x ∈ L' := fun M' hM' x hx => hM'.2 x hx
  have hk : ∀ M' ∈ S, ∀ x ∈ L', k • x ∈ M'.1 := by
    intro M' hM' x hx
    rw [← Int.cast_smul_eq_zsmul (𝓞 F), he, mul_comm, mul_smul, mul_smul]
    exact M'.1.smul_mem _ (hM'.1 _ ((hmemL' x).mp hx))
  -- the reduction map to (ℤ/k)^r
  set b := frame hL'
  set K := k.natAbs
  let φ : zLat L' → (Fin (zrank F n) → ZMod K) := fun x i => (b.repr x i : ZMod K)
  let Ψ : S → Set (Fin (zrank F n) → ZMod K) := fun M' =>
    φ '' {x : zLat L' | (x : Fin n → F) ∈ (M' : Lat F n).1}
  have hle : ∀ M₁ M₂ : S, Ψ M₁ = Ψ M₂ → (M₁ : Lat F n).1 ≤ (M₂ : Lat F n).1 := by
    intro M₁ M₂ hΨ x hx
    set xz : zLat L' := ⟨x, hsub _ M₁.2 x hx⟩
    have : φ xz ∈ Ψ M₂ := hΨ ▸ ⟨xz, hx, rfl⟩
    obtain ⟨yz, hy, hφ⟩ := this
    have hdiv : ∀ i, k ∣ b.repr (xz - yz) i := by
      intro i
      have := congrFun hφ i
      simp only [φ] at this
      rw [map_sub, Finsupp.sub_apply]
      rw [← Int.natAbs_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, this, sub_self]
    choose c hc using hdiv
    set z : zLat L' := ∑ i, c i • b i
    have hxyz : xz - yz = k • z := by
      apply b.repr.injective
      ext i
      rw [map_zsmul, Finsupp.smul_apply, hc i, congrFun (b.repr_sum_self c) i, smul_eq_mul]
    have hx' : x = (yz : Fin n → F) + k • (z : Fin n → F) := by
      have := congrArg Subtype.val hxyz
      simp only [Submodule.coe_sub, Submodule.coe_smul] at this
      rw [← this]; simp [xz]
    rw [hx']
    exact (M₂ : Lat F n).1.add_mem hy (hk _ M₂.2 _ z.2)
  have hΨ : Function.Injective Ψ := fun M₁ M₂ h =>
    Subtype.ext (Lattices.Lat.ext (le_antisymm (hle M₁ M₂ h) (hle M₂ M₁ h.symm)))
  have : NeZero K := ⟨Int.natAbs_ne_zero.mpr hk0⟩
  have : Finite S := Finite.of_injective Ψ hΨ
  exact Set.toFinite S

/-- **$[O(\hat L) : O(\hat L) \cap O(\hat M)] < \infty$** for any lattices $L, M \subseteq F^n$. -/
theorem relIndex_locStab_ne_zero (L M : Lat F n) : (locStab Q M).relIndex (locStab Q L) ≠ 0 := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  set K := locStab Q L
  have hstab : (locStab Q M).subgroupOf K = stabilizer K M := by
    ext k
    rw [Subgroup.mem_subgroupOf, mem_stabilizer_iff, ← stabilizer_eq_locStab Q M, mem_stabilizer_iff]
    rfl
  rw [Subgroup.relIndex, hstab, index_stabilizer]
  obtain ⟨d, hd, h1, h2⟩ := exists_sandwich L.2 M.2
  have hsub : orbit K M ⊆ {M' : Lat F n | (∀ x ∈ L.1, d • x ∈ M'.1) ∧ (∀ x ∈ M'.1, d • x ∈ L.1)} := by
    rintro _ ⟨k, rfl⟩
    exact sandwich_latSMul Q h1 h2 k.2
  have hfin := (finite_sandwich L hd).subset hsub
  exact ((Set.ncard_pos hfin).mpr ⟨M, mem_orbit_self M⟩).ne'

/-- **Lattice stabilizers are commensurable:** $O(\hat M)$ and $O(\hat L)$ are commensurable subgroups of
$O(V)(\mathbb A_f)$ for any lattices $L, M \subseteq F^n$ (O'Meara §81 [unverified]; Weil 1982, §2.1
[unverified]). -/
@[kb "weil1982" "§2.1 (compact open subgroups) [unverified]"]
theorem commensurable_locStab (L M : Lat F n) : (locStab Q M).Commensurable (locStab Q L) :=
  ⟨⟨relIndex_locStab_ne_zero Q L M⟩, ⟨relIndex_locStab_ne_zero Q M L⟩⟩

end QuadFormsKB.Tamagawa
