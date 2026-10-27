/-
# Local spinor norms of unimodular lattices at non-dyadic primes

**Layer:** $V = F^n$ with $Q = Q_0 \otimes F$ for a form $Q_0$ over $\mathcal O_F$, a finite prime $\mathfrak p$ of $F$ with
completion $F_\mathfrak p \supseteq \mathfrak o_\mathfrak p$, and the standard local lattice $\mathfrak o_\mathfrak p^n$ (`std`). Symmetries and the
spinor norm are from `Lattices/SpinorKernel.lean` and `Lattices/SpinorNorm.lean`.

**Defines**
* `locStabV Q L v` $= O(L_\mathfrak p) = \{g \in O(V_\mathfrak p) : gL_\mathfrak p = L_\mathfrak p\}$;
* `IsUnitSqClass v c`: the square class $c$ contains a unit of $\mathfrak o_\mathfrak p$;
* `LocalSpinorUnits Q L v`: every $\sigma \in O(V_\mathfrak p)$ whose spinor norm is a unit class lies in
  $O'(V_\mathfrak p)\,O(L_\mathfrak p)$. Equivalently, $(\theta, \det)(O(L_\mathfrak p)) \supseteq
  \mathfrak o_\mathfrak p^\times F_\mathfrak p^{\times 2}/F_\mathfrak p^{\times 2} \times \{\pm 1\}$
  ("$\theta(O(L_\mathfrak p)) \supseteq \mathfrak o_\mathfrak p^\times F_\mathfrak p^{\times2}$ with an improper element").

**Proves**
* `exists_eval_eq_unit_dvr`: over a complete non-dyadic DVR $R$ with finite residue field, a unimodular form in
  $n \ge 2$ variables represents every unit (diagonalize, `DVR.exists_diag_of_unimodular`, then
  `Nbr.exists_binary_one_dvr`);
* `symm_mem_stdStab`: a symmetry $\tau_x$ in $x \in \mathfrak o_\mathfrak p^n$ with $Q(x) \in \mathfrak o_\mathfrak p^\times$ stabilizes
  $\mathfrak o_\mathfrak p^n$ (since $B(x, y)/Q(x) \in \mathfrak o_\mathfrak p$);
* `localSpinorUnits_of_unimodular`: **if $\mathfrak p \nmid 2\det H$ and $n \ge 2$, then $L_\mathfrak p = \mathfrak o_\mathfrak p^n$ has
  `LocalSpinorUnits`**, in particular $\theta(O(L_\mathfrak p)) \supseteq \mathfrak o_\mathfrak p^\times F_\mathfrak p^{\times 2}$
  (`spinorNorm_stdStab_unit`) (cf. O'Meara 1963, 92:5, p. 249: $\theta(O^+(L)) = \mathfrak u F^{\times 2}$ for modular $L$ of rank $\ge 2$; Kneser 1956, Satz 3 [unverified]). Purely local.
-/
import QuadFormsKB.Lattices.SpinorNorm
import QuadFormsKB.Lattices.UnimodularDVR
import QuadFormsKB.LocalDensity.NFLocalGeneral

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### Unimodular forms over a complete non-dyadic DVR represent all units -/

section DVR

open QuadFormsKB.LocalDensity

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- **A unimodular form in $n \ge 2$ variables over a complete non-dyadic DVR with finite residue field represents
every unit** (O'Meara 1963, 92:1b, p. 247). -/
@[kb "omeara1963" "§92, 92:1b, p. 247 (a unimodular lattice represents every unit)"]
theorem exists_eval_eq_unit_dvr {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (Q₀ : QuadForm R n)
    (hdet : ¬ π ∣ Q₀.hessian.det) (hn : 2 ≤ n) {u : R} (hu : IsUnit u) : ∃ x, Q₀.eval x = u := by
  obtain ⟨a, ha, ⟨U, -, hU⟩, -⟩ := DVR.exists_diag_of_unimodular Q₀ π hπ h2 hdet
  have haU : ∀ i, IsUnit (a i) := fun i => DVR.isUnit_of_not_dvd _ hπ _ (ha i)
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨s, t, hst⟩ := Nbr.exists_binary_one_dvr hπ h2 ((haU i0).mul hu.unit⁻¹.isUnit)
    ((haU i1).mul hu.unit⁻¹.isUnit)
  let z : Fin n → R := Pi.single i0 s + Pi.single i1 t
  refine ⟨U *ᵥ z, ?_⟩
  rw [← hU, Siegel.Kneser.eval_diag]
  have hz : ∀ i, a i * z i ^ 2 = (if i = i0 then a i0 * s ^ 2 else 0) + (if i = i1 then a i1 * t ^ 2 else 0) := by
    intro i
    by_cases h0 : i = i0
    · subst h0; simp [z, h01]
    · by_cases h1 : i = i1
      · subst h1; simp [z, h0]
      · simp [z, h0, h1]
  rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have := congrArg (· * u) hst
  simp only [one_mul] at this
  rw [← this]
  have hu' : (↑hu.unit⁻¹ : R) * u = 1 := hu.val_inv_mul
  linear_combination (-(a i0 * s ^ 2 + a i1 * t ^ 2)) * hu'

end DVR

/-! ### Symmetries of the standard local lattice -/

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable (Q₀ : QuadForm (𝓞 F) n)

local notation "Q" => Q₀.map (algebraMap (𝓞 F) F)

theorem hessian_entry_le_one (i j : Fin n) :
    Valued.v (((Q).hessian.map (algebraMap F Fv)) i j) ≤ 1 := by
  rw [QuadForm.hessian_map, Matrix.map_apply, Matrix.map_apply, ← IsScalarTower.algebraMap_apply]
  exact valued_int_le_one v _

theorem qbil_le_one {x y : Fin n → Fv} (hx : x ∈ std v) (hy : y ∈ std v) :
    Valued.v (qbil (Q) Fv x y) ≤ 1 := by
  have hHy : (Q).hessian.map (algebraMap F Fv) *ᵥ y ∈ std v :=
    mulVec_mem_std v (hessian_entry_le_one v Q₀) hy
  rw [qbil, dotProduct]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul]
  have h1 := hx i
  have h2 := hHy i
  rw [neg_zero, exp_zero] at h1 h2
  exact mul_le_one' h1 h2

/-- **A symmetry in a unit vector stabilizes $\mathfrak o_\mathfrak p^n$:** if $x \in \mathfrak o_\mathfrak p^n$ and
$Q(x) \in \mathfrak o_\mathfrak p^\times$, then $\tau_x\,\mathfrak o_\mathfrak p^n = \mathfrak o_\mathfrak p^n$. -/
@[kb "omeara1963" "§91B, p. 241 (τ_u ∈ O(L) if and only if 2B(u,L) ⊆ Q(u)𝔬)"]
theorem symm_mem_stdStab {x : Fin n → Fv} (hx : x ∈ std v) (hQx : Valued.v ((Q).evalIn Fv x) = 1) :
    symm (Q) Fv x ∈ stdStab (Q) v := by
  have hx0 : (Q).evalIn Fv x ≠ 0 := fun h => by rw [h, map_zero] at hQx; exact zero_ne_one hQx
  have hmaps : ∀ y ∈ std v, ((symm (Q) Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y ∈ std v := by
    intro y hy
    rw [symm_mulVec_bil (Q) Fv hx0]
    have hc : Valued.v (qbil (Q) Fv x y / (Q).evalIn Fv x) ≤ 1 := by
      rw [map_div₀, hQx, div_one]; exact qbil_le_one v Q₀ hx hy
    have hcx : (qbil (Q) Fv x y / (Q).evalIn Fv x) • x ∈ std v :=
      (std v).smul_mem (⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩ : 𝔬) hx
    exact (std v).sub_mem hy hcx
  change locAct v (symm (Q) Fv x : GL (Fin n) Fv) (std v) = std v
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hmaps y hy
  · intro y hy
    refine ⟨((symm (Q) Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y, hmaps y hy, ?_⟩
    show ((symm (Q) Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ
      (((symm (Q) Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, symm_mul_self]
    simp

/-- **Unit vectors of $\mathfrak o_\mathfrak p^n$:** if $\mathfrak p \nmid 2\det H$ and $n \ge 2$, every unit $u$ of
$\mathfrak o_\mathfrak p$ is $Q(x)$ for some $x \in \mathfrak o_\mathfrak p^n$. -/
theorem exists_std_evalIn_eq_unit (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hdet : Q₀.hessian.det ∉ v.asIdeal) (hn : 2 ≤ n)
    {u : Fv} (hu : Valued.v u = 1) : ∃ x ∈ std v, (Q).evalIn Fv x = u := by
  let u' : 𝔬 := ⟨u, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le⟩
  have hu' : IsUnit u' := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact hu
  obtain ⟨x, hx⟩ := exists_eval_eq_unit_dvr (LocalDensity.NF.irreducible_π v)
    (LocalDensity.NF.π_not_dvd_two v h2) (LocalDensity.NF.Qp v Q₀) (LocalDensity.NF.π_not_dvd_det v Q₀ hdet) hn hu'
  refine ⟨fun i => (x i : Fv), fun i => ?_, ?_⟩
  · rw [neg_zero, exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (x i).2
  · rw [Tamagawa.evalIn_coe_o v Q₀ x, hx]

end Local

/-! ### The local condition `LocalSpinorUnits` -/

section LocalCondition

variable (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **$O(L_\mathfrak p)$**, the stabilizer of the localization $L_\mathfrak p$ in $O(V_\mathfrak p)$. -/
def locStabV (L : Lat F n) : Subgroup (orthGroup Q Fv) where
  carrier := {g | locAct v (g : GL (Fin n) Fv) (loc v L.1) = loc v L.1}
  mul_mem' {a b} ha hb := by
    change locAct v (((a * b : orthGroup Q _)) : GL (Fin n) _) _ = _
    rw [Subgroup.coe_mul, locAct_mul, show locAct v (b : GL (Fin n) Fv) (loc v L.1) = loc v L.1 from hb]
    exact ha
  one_mem' := locAct_one _
  inv_mem' {a} ha := by
    change locAct v (((a⁻¹ : orthGroup Q _)) : GL (Fin n) _) _ = _
    rw [Subgroup.coe_inv, locAct_eq_iff, inv_inv]
    exact (show locAct v (a : GL (Fin n) Fv) (loc v L.1) = loc v L.1 from ha).symm

theorem locStabV_eq_stdStab (L : Lat F n) (hL : loc v L.1 = std v) {g : orthGroup Q Fv} :
    g ∈ locStabV Q v L ↔ g ∈ stdStab Q v := by
  change locAct v _ (loc v L.1) = loc v L.1 ↔ locAct v _ (std v) = std v
  rw [hL]

/-- **A unit square class:** $c = u\,F_\mathfrak p^{\times 2}$ for a unit $u \in \mathfrak o_\mathfrak p^\times$. -/
def IsUnitSqClass (c : SqClass Fv) : Prop := ∃ u : Fv, Valued.v u = 1 ∧ c = sqClassOf u

/-- **Local spinor norms contain the units** (at $\mathfrak p$, for the lattice $L$): every $\sigma \in O(V_\mathfrak p)$ whose
spinor norm is a unit class lies in $O'(V_\mathfrak p)\,O(L_\mathfrak p)$. This is the local condition of the classical
criterion "genus = spinor genus" (O'Meara 1963, 102:9, p. 304, and 92:5, p. 249). It holds at every $\mathfrak p \nmid 2\det H$
for $n \ge 2$ (`localSpinorUnits_of_unimodular`); at the finitely many other primes it is a hypothesis. -/
@[kb "omeara1963" "§102B, 102:9, p. 304 (hypothesis θ(O⁺(L_𝔭)) ⊇ 𝔲_𝔭); §92, 92:5, p. 249"]
def LocalSpinorUnits (L : Lat F n) : Prop :=
  ∀ σ : orthGroup Q Fv, IsUnitSqClass v (spinorNorm Q Fv σ) →
    ∃ k ∈ spinorKernel Q Fv, k⁻¹ * σ ∈ locStabV Q v L

end LocalCondition

/-! ### `LocalSpinorUnits` from improper elements of $O(L_\mathfrak p)$ -/

section Improper

variable (Q : QuadForm F n) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **`LocalSpinorUnits` from improper automorphs with prescribed unit spinor norms** (any prime, dyadic or not): if
for every unit $u\in\mathfrak o_\mathfrak p^\times$ there is $g\in O(L_\mathfrak p)$ with $\det g = -1$ and
$\theta(g) = u\,F_\mathfrak p^{\times2}$, then every $\sigma\in O(V_\mathfrak p)$ with unit spinor norm lies in
$O'(V_\mathfrak p)\,O(L_\mathfrak p)$. *Proof:* pick $g$ (or $g\,g_1$, $\theta(g_1) = 1$) in $O(L_\mathfrak p)$ with the
determinant and spinor norm of $\sigma$; then $\sigma g^{-1}\in O'(V_\mathfrak p)$. Purely local. -/
@[kb "omeara1963" "§92, 92:5, p. 249; §102B, 102:9, p. 304"]
theorem localSpinorUnits_of_improper (hQ : Q.Nondegenerate) (L : Lat F n)
    (himp : ∀ u : Fv, Valued.v u = 1 →
      ∃ g ∈ locStabV Q v L, detHom Q Fv g = -1 ∧ spinorNorm Q Fv g = sqClassOf u) :
    LocalSpinorUnits Q v L := by
  intro σ ⟨u, hu, hσ⟩
  obtain ⟨g₁, hg₁, hd₁, hθ₁⟩ := himp u hu
  obtain ⟨g₂, hg₂, hd₂, hθ₂⟩ := himp 1 (by simp)
  -- `det σ = ±1`
  obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q Fv hQ σ
  have hdσ := detHom_symmProd Q Fv xs hxs
  -- choose `g ∈ O(L_p)` with the same spinor norm and determinant as `σ`
  obtain ⟨g, hg, hdg, hθg⟩ : ∃ g ∈ locStabV Q v L, detHom Q Fv g = detHom Q Fv (symmProd Q Fv xs) ∧
      spinorNorm Q Fv g = sqClassOf u := by
    rcases Nat.even_or_odd xs.length with he | ho
    · refine ⟨g₁ * g₂, (locStabV Q v L).mul_mem hg₁ hg₂, ?_, ?_⟩
      · ext; rw [map_mul, hd₁, hd₂, hdσ, he.neg_one_pow]; simp
      · rw [← spinorNormHom_apply Q Fv hQ, map_mul, spinorNormHom_apply, spinorNormHom_apply, hθ₁, hθ₂,
          sqClassOf_one, mul_one]
    · exact ⟨g₁, hg₁, by ext; rw [hd₁, hdσ, ho.neg_one_pow]; simp, hθ₁⟩
  refine ⟨symmProd Q Fv xs * g⁻¹, ?_, ?_⟩
  · rw [spinorKernel_eq_ker Q Fv hQ]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hθg, ← hσ,
        mul_inv_cancel]
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hdg, mul_inv_cancel]
  · simpa using hg

end Improper

section Unimodular

variable (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n)

local notation "Fv" => v.adicCompletion F
local notation "Q" => Q₀.map (algebraMap (𝓞 F) F)

theorem nondegenerate_map_of_det_not_mem (hdet : Q₀.hessian.det ∉ v.asIdeal) : (Q).Nondegenerate := by
  intro h
  apply hdet
  rw [QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  have : Q₀.hessian.det = 0 := (FaithfulSMul.algebraMap_injective (𝓞 F) F) (by rw [h, map_zero])
  rw [this]; exact v.asIdeal.zero_mem

/-- **$\theta(O(\mathfrak o_\mathfrak p^n)) \supseteq \mathfrak o_\mathfrak p^\times F_\mathfrak p^{\times 2}$ at non-dyadic unimodular primes**,
$n \ge 2$, realized by symmetries of $\mathfrak o_\mathfrak p^n$ (determinant $-1$) (cf. O'Meara 1963, 92:5, p. 249, which gives $\theta(O^+(L)) = \mathfrak u F^{\times 2}$; the
containment for $O(L)$ follows). -/
@[kb "omeara1963" "§92, 92:5, p. 249; cassels1978 Ch. 10, Lemma 4.1, p. 183; Ch. 11, Lemma 3.3, p. 208"]
theorem spinorNorm_stdStab_unit (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hdet : Q₀.hessian.det ∉ v.asIdeal) (hn : 2 ≤ n)
    {u : Fv} (hu : Valued.v u = 1) :
    ∃ g ∈ stdStab (Q) v, detHom (Q) Fv g = -1 ∧ spinorNorm (Q) Fv g = sqClassOf u := by
  obtain ⟨x, hx, hQx⟩ := exists_std_evalIn_eq_unit v Q₀ h2 hdet hn hu
  have hQ := nondegenerate_map_of_det_not_mem v Q₀ hdet
  have hx0 : (Q).evalIn Fv x ≠ 0 := by rw [hQx]; intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  refine ⟨symm (Q) Fv x, symm_mem_stdStab v Q₀ hx (by rw [hQx, hu]), ?_, ?_⟩
  · ext; rw [detHom_val, symm_det (Q) Fv hx0]; simp
  · rw [spinorNorm_symm (Q) Fv hQ hx0, hQx]

/-- **`LocalSpinorUnits` at non-dyadic unimodular primes:** if $\mathfrak p \nmid 2\det H$, $n \ge 2$ and
$L_\mathfrak p = \mathfrak o_\mathfrak p^n$, then every $\sigma \in O(V_\mathfrak p)$ with unit spinor norm is in
$O'(V_\mathfrak p)O(L_\mathfrak p)$ (a consequence of O'Meara 1963, 92:5, p. 249). Purely local. -/
@[kb "omeara1963" "§92, 92:5, p. 249; §102B, 102:9, p. 304; §102B, 102:10 (ii), p. 304; cassels1978 Ch. 10, Lemma 4.1, p. 183; Ch. 11, Lemma 3.3, p. 208"]
theorem localSpinorUnits_of_unimodular (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hdet : Q₀.hessian.det ∉ v.asIdeal)
    (hn : 2 ≤ n) (L : Lat F n) (hL : loc v L.1 = std v) : LocalSpinorUnits (Q) v L := by
  refine localSpinorUnits_of_improper (Q) v (nondegenerate_map_of_det_not_mem v Q₀ hdet) L fun u hu => ?_
  obtain ⟨g, hg, hd, hθ⟩ := spinorNorm_stdStab_unit v Q₀ h2 hdet hn hu
  exact ⟨g, (locStabV_eq_stdStab (Q) v L hL).mpr hg, hd, hθ⟩

end Unimodular

end QuadFormsKB.Lattices
