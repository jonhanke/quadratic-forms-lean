/-
# The strong approximation theorem for rotations, step 1 ($n \ge 4$) of O'Meara 104:4

**Layer:** $V = F^n$ with $Q$ = `Q : QuadForm F n` over a number field $F$, its completions $V_\mathfrak p$, the spinor
kernels $O'(V) \le O(V)(F)$ and $O'(V_\mathfrak p)$ (`Lattices/SpinorKernel.lean`), the local stabilizers
$O(\mathfrak o_\mathfrak p^n)$ (`stdStab`) and the finite adelic group (`Lattices/ClassSet.lean`).

**Defines** the two approximation properties of O'Meara 1973, §104 (pp. 311–319 = PDF pp. 319–327), phrased with
neighbourhoods at finitely many primes (no adelic topology):
* `RotApprox Q` (**104:4**, strong approximation for rotations): for a finite set $T$ of primes, rotations
  $\varphi_\mathfrak p \in O'(V_\mathfrak p)$ and neighbourhoods $U_\mathfrak p$ of $\varphi_\mathfrak p$ ($\mathfrak p \in T$) there is
  $\sigma \in O'(V)$ with $\sigma \in U_\mathfrak p$ for $\mathfrak p \in T$ and $\sigma \in O(\mathfrak o_\mathfrak p^n)$ for $\mathfrak p \notin T$;
* `VecApprox Q` (**104:3**, strong approximation for vectors of a given norm $a = Q(u)$): for local vectors $z_\mathfrak p$
  with $Q(z_\mathfrak p) = a$ and neighbourhoods $Z_\mathfrak p$ ($\mathfrak p \in T$) there is $z \in V$ with $Q(z) = a$,
  $z \in Z_\mathfrak p$ on $T$ and $z \in \mathfrak o_\mathfrak p^n$ off $T$ (given that $u \in \mathfrak o_\mathfrak p^n$ off $T$).

**Proves**
* `approx_of_rotApprox` (**104:5** direction used here): `RotApprox Q` gives the field `approx` of the input
  `StrongApproximationSpin` for $Q$: every $h \in O'(V_{\mathbb A_f})$ lies in $O'(V)\,O(\hat L)$;
* `pair_approx` (104:4 step 1a): approximation of short commutators $\tau_u\tau_w$ ($Q(u) = Q(w)$) from `VecApprox Q`;
* `list_approx`: products of short commutators;
* `rotApprox_of_vecApprox`: **`VecApprox Q` and isotropy of every $V_\mathfrak p$ give `RotApprox Q`**, using
  $O'(V_\mathfrak p) = \langle \tau_u\tau_w : Q(u) = Q(w)\rangle$ for isotropic $V_\mathfrak p$ (`Lattices/SAEqualPairs.lean`).

*Simplification (recorded in `docs/updates-and-errata.md`).* O'Meara's step 1c reduces an arbitrary
$\varphi_\mathfrak p \in O'(V_\mathfrak p)$ to the commutator subgroup $\Omega(V_\mathfrak p)$ using 55:? and global elements from 95:1
and 101:9. When every $V_\mathfrak p$ is isotropic (always for $n \ge 5$), the spinor-word definition of $O'$ gives
$O'(V_\mathfrak p) = \langle \tau_u\tau_w : Q(u) = Q(w)\rangle$ directly and step 1c is a list-padding argument.
-/
import QuadFormsKB.Lattices.SAApprox
import QuadFormsKB.Lattices.StrongApproximation

open NumberField IsDedekindDomain Matrix WithZero Topology Filter
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- The matrix of an isometry. -/
abbrev omat {K : Type*} [Field K] [Algebra F K] {Q : QuadForm F n} (g : orthGroup Q K) :
    Matrix (Fin n) (Fin n) K :=
  ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem omat_mul {K : Type*} [Field K] [Algebra F K] {Q : QuadForm F n} (g h : orthGroup Q K) :
    omat (g * h) = omat g * omat h := rfl

theorem omat_one {K : Type*} [Field K] [Algebra F K] {Q : QuadForm F n} : omat (1 : orthGroup Q K) = 1 := rfl

variable (Q : QuadForm F n)

/-! ### The approximation properties -/

/-- **Strong approximation for rotations** (O'Meara 1973, 104:4, p. 315), with neighbourhoods: for every finite set
$T$ of finite primes, every family $\varphi_\mathfrak p \in O'(V_\mathfrak p)$ and every family of neighbourhoods $U_\mathfrak p$ of
(the matrices of) $\varphi_\mathfrak p$, $\mathfrak p \in T$, there is $\sigma \in O'(V)$ with $\sigma \in U_\mathfrak p$ for $\mathfrak p \in T$
and $\sigma\,\mathfrak o_\mathfrak p^n = \mathfrak o_\mathfrak p^n$ for $\mathfrak p \notin T$. -/
def RotApprox : Prop :=
  ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (φ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F)),
    (∀ v ∈ T, φ v ∈ spinorKernel Q (v.adicCompletion F)) →
    ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)),
      (∀ v ∈ T, U v ∈ 𝓝 (omat (φ v))) →
      ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, omat (orthMap Q (v.adicCompletion F) σ) ∈ U v) ∧
        ∀ v ∉ T, orthMap Q (v.adicCompletion F) σ ∈ stdStab Q v

/-- **Strong approximation for vectors of a given norm** (O'Meara 1973, 104:3, p. 311), with neighbourhoods: let
$u \in V$ with $a = Q(u) \ne 0$, $T$ a finite set of primes with $u \in \mathfrak o_\mathfrak p^n$ for $\mathfrak p \notin T$, and
$z_\mathfrak p \in V_\mathfrak p$ with $Q(z_\mathfrak p) = a$ and neighbourhoods $Z_\mathfrak p \ni z_\mathfrak p$ ($\mathfrak p \in T$). Then some $z \in V$
has $Q(z) = a$, $z \in Z_\mathfrak p$ for $\mathfrak p \in T$ and $z \in \mathfrak o_\mathfrak p^n$ for $\mathfrak p \notin T$.
(O'Meara's local hypothesis "$z_\mathfrak p \in L_\mathfrak p$ with $Q(z_\mathfrak p) = a$ for $\mathfrak p \notin T$" is met here by $u$.) -/
def VecApprox : Prop :=
  ∀ u : Fin n → F, Q.evalIn F u ≠ 0 → ∀ T : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∉ T, locVec v u ∈ std v) →
    ∀ z : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F,
      (∀ v ∈ T, Q.evalIn (v.adicCompletion F) (z v) = algebraMap F (v.adicCompletion F) (Q.evalIn F u)) →
    ∀ Z : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F), (∀ v ∈ T, Z v ∈ 𝓝 (z v)) →
      ∃ y : Fin n → F, Q.evalIn F y = Q.evalIn F u ∧ (∀ v ∈ T, locVec v y ∈ Z v) ∧ ∀ v ∉ T, locVec v y ∈ std v

/-! ### The bridge to `StrongApproximationSpin` (104:5) -/

/-- **Strong approximation for rotations gives $O'(V_{\mathbb A_f}) \subseteq O'(V)\,O(\hat L)$** (the field `approx` of
`StrongApproximationSpin`; O'Meara 1973, proof of 104:5, p. 319). Take $T$ = the primes where $h_\mathfrak p \notin
O(\mathfrak o_\mathfrak p^n)$ or $L_\mathfrak p \ne \mathfrak o_\mathfrak p^n$ and approximate $h_\mathfrak p$ so closely that
$\sigma L_\mathfrak p = h_\mathfrak p L_\mathfrak p$ (`exists_mem_nhds_locAct_eq`). -/
theorem approx_of_rotApprox (hR : RotApprox Q) (L : Lat F n) (h : OAf Q) (hh : h ∈ spinorKernelAf Q) :
    ∃ γ : orthGroup Q F, γ ∈ spinorKernel Q F ∧ (diagF Q γ)⁻¹ * h ∈ locStab Q L := by
  classical
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, h v ∈ stdStab Q v ∧ loc v L.1 = std v :=
    h.2.and (loc_eventually_std L.2)
  set T : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.mp hev).toFinset
  have hT : ∀ v, v ∉ T → h v ∈ stdStab Q v ∧ loc v L.1 = std v := by
    intro v hv
    by_contra hc
    exact hv ((Filter.eventually_cofinite.mp hev).mem_toFinset.mpr hc)
  choose U hU hUσ using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_mem_nhds_locAct_eq v ((h v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F))
      (loc_isLattice v L.2)
  obtain ⟨σ, hσ, hσT, hσT'⟩ := hR T (fun v => h v) (fun v _ => hh v) U (fun v _ => hU v)
  refine ⟨σ, hσ, fun v => ?_⟩
  change locAct v ((((diagF Q σ)⁻¹ * h) v : orthGroup Q (v.adicCompletion F)) : GL (Fin n) _) (loc v L.1) = loc v L.1
  have e : ((diagF Q σ)⁻¹ * h) v = (orthMap Q (v.adicCompletion F) σ)⁻¹ * h v := rfl
  rw [e, Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
  by_cases hv : v ∈ T
  · rw [← hUσ v _ (hσT v hv), locAct_inv_locAct]
  · obtain ⟨hhv, hL⟩ := hT v hv
    have h1 : locAct v ((h v : orthGroup Q _) : GL (Fin n) _) (std v) = std v := hhv
    have h2 : locAct v ((orthMap Q (v.adicCompletion F) σ : orthGroup Q _) : GL (Fin n) _) (std v) = std v :=
      hσT' v hv
    rw [hL, h1]; exact (locAct_eq_iff.mp h2).symm

/-! ### Symmetries in unit vectors are integral -/

section Integral

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $Q$ has $\mathfrak p$-integral Hessian. -/
def HessInt : Prop := ∀ i j, Valued.v ((Q.hessian.map (algebraMap F Fv)) i j) ≤ 1

theorem eventually_hessInt : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, HessInt Q v := by
  have : ∀ i j : Fin n, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v ((Q.hessian.map (algebraMap F (v.adicCompletion F))) i j) ≤ 1 := fun i j => by
    filter_upwards [eventually_valuation_le_one (Q.hessian i j)] with v hv
    rw [Matrix.map_apply, valued_algebraMap]; exact hv
  simp only [HessInt, Filter.eventually_all]
  exact this

theorem qbil_le_one' (hH : HessInt Q v) {x y : Fin n → Fv} (hx : x ∈ std v) (hy : y ∈ std v) :
    Valued.v (qbil Q Fv x y) ≤ 1 := by
  have hHy : Q.hessian.map (algebraMap F Fv) *ᵥ y ∈ std v := mulVec_mem_std v hH hy
  rw [qbil, dotProduct]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul]
  have h1 := hx i
  have h2 := hHy i
  rw [neg_zero, exp_zero] at h1 h2
  exact mul_le_one' h1 h2

/-- **A symmetry in a unit vector stabilizes $\mathfrak o_\mathfrak p^n$** (for $Q$ with $\mathfrak p$-integral Hessian;
O'Meara 1973, §91B [unverified]). -/
theorem symm_mem_stdStab' (hH : HessInt Q v) {x : Fin n → Fv} (hx : x ∈ std v)
    (hQx : Valued.v (Q.evalIn Fv x) = 1) : symm Q Fv x ∈ stdStab Q v := by
  have hx0 : Q.evalIn Fv x ≠ 0 := fun h => by rw [h, map_zero] at hQx; exact zero_ne_one hQx
  have hmaps : ∀ y ∈ std v, ((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y ∈ std v := by
    intro y hy
    rw [symm_mulVec_bil Q Fv hx0]
    have hc : Valued.v (qbil Q Fv x y / Q.evalIn Fv x) ≤ 1 := by
      rw [map_div₀, hQx, div_one]; exact qbil_le_one' Q v hH hx hy
    have hcx : (qbil Q Fv x y / Q.evalIn Fv x) • x ∈ std v :=
      (std v).smul_mem (⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩ : 𝔬) hx
    exact (std v).sub_mem hy hcx
  change locAct v (symm Q Fv x : GL (Fin n) Fv) (std v) = std v
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hmaps y hy
  · intro y hy
    refine ⟨((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y, hmaps y hy, ?_⟩
    show ((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ
      (((symm Q Fv x : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, symm_mul_self]
    simp

end Integral

/-- The integrality conditions at a prime: $u \in \mathfrak o_\mathfrak p^n$, $Q(u) \in \mathfrak o_\mathfrak p^\times$, $H$ integral. -/
def GoodAt (Q : QuadForm F n) (u : Fin n → F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  locVec v u ∈ std v ∧ Valued.v (Q.evalIn (v.adicCompletion F) (locVec v u)) = 1 ∧ HessInt Q v

theorem eventually_goodAt {u : Fin n → F} (hu : Q.evalIn F u ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, GoodAt Q u v := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, locVec v u ∈ std v := by
    have : ∀ i, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F (u i) ≤ 1 :=
      fun i => eventually_valuation_le_one (u i)
    filter_upwards [Filter.eventually_all.mpr this] with v hv i
    rw [locVec_apply, valued_algebraMap, neg_zero, exp_zero]; exact hv i
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v (Q.evalIn (v.adicCompletion F) (locVec v u)) = 1 := by
    filter_upwards [eventually_valuation_le_one (Q.evalIn F u),
      eventually_valuation_le_one (Q.evalIn F u)⁻¹] with v hv hv'
    rw [evalIn_locVec, valued_algebraMap]
    rw [map_inv₀] at hv'
    have hne : v.valuation F (Q.evalIn F u) ≠ 0 := by simpa using hu
    refine le_antisymm hv ?_
    by_contra hlt
    push Not at hlt
    exact absurd hv' (not_le.mpr (one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hne, hlt⟩))
  filter_upwards [h1, h2, eventually_hessInt Q] with v a b c
  exact ⟨a, b, c⟩

/-- In a good prime both symmetries of a short commutator $\tau_u\tau_z$ are integral. -/
theorem pair_mem_stdStab {u z : Fin n → F} {v : HeightOneSpectrum (𝓞 F)} (hg : GoodAt Q u v)
    (hz : locVec v z ∈ std v) (hzu : Q.evalIn F z = Q.evalIn F u) :
    orthMap Q (v.adicCompletion F) (symm Q F u * symm Q F z) ∈ stdStab Q v := by
  obtain ⟨h1, h2, h3⟩ := hg
  rw [map_mul, orthMap_symm_locVec, orthMap_symm_locVec]
  refine Subgroup.mul_mem _ (symm_mem_stdStab' Q v h3 h1 h2) (symm_mem_stdStab' Q v h3 hz ?_)
  rw [evalIn_locVec] at h2 ⊢
  rw [show Q.eval z = Q.eval u from hzu]; exact h2

/-! ### Step 1a: short commutators -/

section Pair

variable {Q}

/-- **Local data for step 1a.** Given $Q(u) = Q(w) \ne 0$ in $V_\mathfrak p$ and a neighbourhood $U$ of $\tau_u\tau_w$, there are
an anisotropic $c$, neighbourhoods $A \ni u$, $C \ni c$ and an open $B$ with: $Q \ne 0$ on $A$; $\tau_{c'}a \in B$ for
$a \in A$, $c' \in C$; and $\tau_a\tau_b \in U$ for $a \in A$, $b \in B$. -/
theorem pair_local (v : HeightOneSpectrum (𝓞 F)) {u w : Fin n → v.adicCompletion F}
    (hu : Q.evalIn _ u ≠ 0) (huw : Q.evalIn _ u = Q.evalIn _ w)
    {U : Set (Matrix (Fin n) (Fin n) (v.adicCompletion F))} (hU : U ∈ 𝓝 (omat (symm Q _ u * symm Q _ w))) :
    ∃ c : Fin n → v.adicCompletion F, ∃ A ∈ 𝓝 u, ∃ C ∈ 𝓝 c, ∃ B : Set (Fin n → v.adicCompletion F),
      IsOpen B ∧ (∀ a ∈ A, Q.evalIn _ a ≠ 0) ∧ (∀ a ∈ A, ∀ c' ∈ C, omat (symm Q _ c') *ᵥ a ∈ B) ∧
      ∀ a ∈ A, ∀ b ∈ B, omat (symm Q _ a * symm Q _ b) ∈ U := by
  obtain ⟨c, w', hc, hw'symm, hw'Q, hcu⟩ := exists_symm_apply_eq (Q := Q) hu huw
  have hw'0 : Q.evalIn _ w' ≠ 0 := by rw [hw'Q, ← huw]; exact hu
  have h1 := (continuousAt_symm v Q hu).comp
    (continuousAt_fst (p := ((u, w') : (Fin n → v.adicCompletion F) × (Fin n → v.adicCompletion F))))
  have h2 := (continuousAt_symm v Q hw'0).comp
    (continuousAt_snd (p := ((u, w') : (Fin n → v.adicCompletion F) × (Fin n → v.adicCompletion F))))
  have hcont : ContinuousAt (fun p : (Fin n → v.adicCompletion F) × (Fin n → v.adicCompletion F) =>
      omat (symm Q _ p.1) * omat (symm Q _ p.2)) (u, w') :=
    continuousAt_matmul_of v
      (M := fun p : (Fin n → v.adicCompletion F) × (Fin n → v.adicCompletion F) => omat (symm Q _ p.1))
      (N := fun p : (Fin n → v.adicCompletion F) × (Fin n → v.adicCompletion F) => omat (symm Q _ p.2)) h1 h2
  have hmem : U ∈ 𝓝 (omat (symm Q _ u) * omat (symm Q _ w')) := by rw [hw'symm]; exact hU
  obtain ⟨A₁, B, hA₁, huA₁, hB, hwB, hAB⟩ := mem_nhds_prod_iff'.mp (hcont.preimage_mem_nhds hmem)
  have h3 := (continuousAt_symm v Q hc).comp
    (continuousAt_snd (p := ((u, c) : (Fin n → v.adicCompletion F) × (Fin n → v.adicCompletion F))))
  have hcont' : ContinuousAt (fun p : (Fin n → v.adicCompletion F) × (Fin n → v.adicCompletion F) =>
      omat (symm Q _ p.2) *ᵥ p.1) (u, c) :=
    continuousAt_mulVec_of v
      (M := fun p : (Fin n → v.adicCompletion F) × (Fin n → v.adicCompletion F) => omat (symm Q _ p.2))
      (y := fun p : (Fin n → v.adicCompletion F) × (Fin n → v.adicCompletion F) => p.1) h3 continuousAt_fst
  have hmem' : B ∈ 𝓝 (omat (symm Q _ c) *ᵥ u) := by rw [hcu]; exact hB.mem_nhds hwB
  obtain ⟨A₂, hA₂, C, hC, hAC⟩ := mem_nhds_prod_iff.mp (hcont'.preimage_mem_nhds hmem')
  have hA₃ : {a | Q.evalIn (v.adicCompletion F) a ≠ 0} ∈ 𝓝 u :=
    (continuous_evalIn v Q).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hu)
  refine ⟨c, A₁ ∩ A₂ ∩ {a | Q.evalIn (v.adicCompletion F) a ≠ 0}, ?_, C, hC, B, hB, ?_, ?_, ?_⟩
  · exact inter_mem (inter_mem (hA₁.mem_nhds huA₁) hA₂) hA₃
  · intro a ha
    exact ha.2
  · intro a ha c' hc'
    have := hAC (Set.mk_mem_prod ha.1.2 hc')
    simp only [Set.mem_preimage] at this
    exact this
  · intro a ha b hb
    have := hAB (Set.mk_mem_prod ha.1.1 hb)
    simp only [Set.mem_preimage] at this
    rw [omat_mul]; exact this


/-- $\{y : \tau_x\tau_y \in N\}$ is a neighbourhood of an anisotropic $x$ when $N$ is a neighbourhood of $1$. -/
theorem symm_mul_mem_nhds (v : HeightOneSpectrum (𝓞 F)) {x : Fin n → v.adicCompletion F}
    (hx : Q.evalIn _ x ≠ 0) {N : Set (Matrix (Fin n) (Fin n) (v.adicCompletion F))} (hN : N ∈ 𝓝 1) :
    {y | omat (symm Q _ x * symm Q _ y) ∈ N} ∈ 𝓝 x := by
  have hcont : ContinuousAt (fun y => omat (symm Q (v.adicCompletion F) x) * omat (symm Q _ y)) x :=
    continuousAt_matmul_of v (M := fun _ => omat (symm Q (v.adicCompletion F) x))
      (N := fun y => omat (symm Q (v.adicCompletion F) y)) continuousAt_const (continuousAt_symm v Q hx)
  have h1 : omat (symm Q (v.adicCompletion F) x) * omat (symm Q _ x) = 1 := by
    rw [← omat_mul, symm_mul_self]; rfl
  have := hcont.preimage_mem_nhds (by rw [h1]; exact hN)
  exact Filter.mem_of_superset this fun y hy => by
    simp only [Set.mem_preimage] at hy
    show omat (symm Q _ x * symm Q _ y) ∈ N
    rw [omat_mul]; exact hy

/-- **Step 1a of O'Meara 104:4** (p. 315): approximation of short commutators $\tau_{u_\mathfrak p}\tau_{w_\mathfrak p}$
($Q(u_\mathfrak p) = Q(w_\mathfrak p) \ne 0$) by $\sigma = \tau_{u}\tau_{z} \in O'(V)$ integral off $T$: approximate $u_\mathfrak p$ by
$u \in V$, and $w_\mathfrak p = \pm\tau_{c_\mathfrak p}u_\mathfrak p$ by $\tau_c u$; then choose $z$ with $Q(z) = Q(u)$ by `VecApprox`,
close to $\tau_c u$ on $T$, close to $u$ at the primes $T_1$ where $u$ is not a unit vector, and integral elsewhere. -/
theorem pair_approx (hV : VecApprox Q) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (u w : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (hu : ∀ v ∈ T, Q.evalIn _ (u v) ≠ 0) (huw : ∀ v ∈ T, Q.evalIn _ (u v) = Q.evalIn _ (w v))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hU : ∀ v ∈ T, U v ∈ 𝓝 (omat (symm Q _ (u v) * symm Q _ (w v)))) :
    ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, omat (orthMap Q (v.adicCompletion F) σ) ∈ U v) ∧
      ∀ v ∉ T, orthMap Q (v.adicCompletion F) σ ∈ stdStab Q v := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨1, Subgroup.one_mem _, by simp, fun v _ => by rw [map_one]; exact Subgroup.one_mem _⟩
  choose! c A hA C hC B hBo hAQ hAC hAB using
    fun v (hv : v ∈ T) => pair_local (Q := Q) v (hu v hv) (huw v hv) (hU v hv)
  obtain ⟨u₀, hu₀, -⟩ := exists_vec_approx T u A hA
  obtain ⟨c₀, hc₀, -⟩ := exists_vec_approx T c C hC
  have hQu₀ : Q.evalIn F u₀ ≠ 0 := by
    have h := hAQ v₀ hv₀ _ (hu₀ v₀ hv₀)
    rw [evalIn_locVec] at h
    exact fun h0 => h (by rw [show Q.eval u₀ = 0 from h0, map_zero])
  set w₀ : Fin n → F := omat (symm Q F c₀) *ᵥ u₀ with hw₀
  have hw₀loc : ∀ v : HeightOneSpectrum (𝓞 F),
      locVec v w₀ = omat (symm Q (v.adicCompletion F) (locVec v c₀)) *ᵥ locVec v u₀ := by
    intro v
    rw [hw₀, locVec_mulVec, ← orthMap_val, orthMap_symm_locVec]
  have hw₀B : ∀ v ∈ T, locVec v w₀ ∈ B v := fun v hv => by
    rw [hw₀loc]; exact hAC v hv _ (hu₀ v hv) _ (hc₀ v hv)
  have hQw₀ : Q.evalIn F w₀ = Q.evalIn F u₀ := evalIn_mulVec_of_mem Q (symm Q F c₀).2 u₀
  have hgood := eventually_goodAt Q hQu₀
  set T₁ := (Filter.eventually_cofinite.mp hgood).toFinset
  have hT₁ : ∀ v, v ∉ T₁ → GoodAt Q u₀ v := by
    intro v hv; by_contra hc'; exact hv ((Filter.eventually_cofinite.mp hgood).mem_toFinset.mpr hc')
  choose N hN hNσ using fun v : HeightOneSpectrum (𝓞 F) => exists_mem_nhds_stdStab v Q
  have hloc0 : ∀ v : HeightOneSpectrum (𝓞 F), Q.evalIn (v.adicCompletion F) (locVec v u₀) ≠ 0 := by
    intro v; rw [evalIn_locVec]; exact (map_ne_zero _).mpr hQu₀
  obtain ⟨y, hyQ, hyZ, hystd⟩ := hV u₀ hQu₀ (T ∪ T₁)
    (fun v hv => (hT₁ v (fun h => hv (Finset.mem_union_right _ h))).1)
    (fun v => if v ∈ T then locVec v w₀ else locVec v u₀)
    (by
      intro v _
      split_ifs
      · rw [evalIn_locVec]; exact congrArg _ hQw₀
      · rw [evalIn_locVec])
    (fun v => if v ∈ T then B v else {y | omat (symm Q _ (locVec v u₀) * symm Q _ y) ∈ N v})
    (by
      intro v _
      split_ifs with hv
      · exact (hBo v hv).mem_nhds (hw₀B v hv)
      · exact symm_mul_mem_nhds v (hloc0 v) (hN v))
  refine ⟨symm Q F u₀ * symm Q F y,
    eqPairSet_subset_spinorKernel Q F (pair_mem_eqPairSet Q F hQu₀ hyQ.symm), ?_, ?_⟩
  · intro v hv
    have hyB := hyZ v (Finset.mem_union_left _ hv)
    simp only [hv, ite_true] at hyB
    rw [map_mul, orthMap_symm_locVec, orthMap_symm_locVec]
    exact hAB v hv _ (hu₀ v hv) _ hyB
  · intro v hv
    by_cases h1 : v ∈ T₁
    · have hyN := hyZ v (Finset.mem_union_right _ h1)
      simp only [hv, ite_false] at hyN
      apply hNσ v
      rw [map_mul, orthMap_symm_locVec, orthMap_symm_locVec]
      exact hyN
    · exact pair_mem_stdStab Q (hT₁ v h1) (hystd v (by simp [hv, h1])) hyQ

end Pair

/-! ### Steps 1b and 1c: products of short commutators -/

theorem inv_mem_eqPairSet {K : Type*} [Field K] [Algebra F K] [CharZero K] {g : orthGroup Q K}
    (hg : g ∈ eqPairSet Q K) : g⁻¹ ∈ eqPairSet Q K := by
  obtain ⟨u, w, hu, huw, rfl⟩ := hg
  refine ⟨w, u, by rwa [← huw], huw.symm, ?_⟩
  rw [_root_.mul_inv_rev, symm_inv, symm_inv]

/-- Every element of the group generated by equal-value pairs is a product of equal-value pairs. -/
theorem exists_list_of_mem_eqPairGroup {K : Type*} [Field K] [Algebra F K] [CharZero K] {g : orthGroup Q K}
    (hg : g ∈ eqPairGroup Q K) : ∃ l : List (orthGroup Q K), (∀ x ∈ l, x ∈ eqPairSet Q K) ∧ l.prod = g := by
  have hg' : g ∈ (Subgroup.closure (eqPairSet Q K)).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid] at hg'
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hg'
  refine ⟨l, fun x hx => ?_, hprod⟩
  rcases hl x hx with h | h
  · exact h
  · have := inv_mem_eqPairSet Q (Set.mem_inv.mp h)
    rwa [inv_inv] at this

/-- **Step 1b of O'Meara 104:4** (p. 316): products of at most $N$ short commutators at each $\mathfrak p \in T$ are
approximated by $\sigma \in O'(V)$ integral off $T$ (induction on $N$, `pair_approx` for the first factor). -/
theorem list_approx (hV : VecApprox Q) (u₀ : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F)
    (hu₀ : ∀ v, Q.evalIn _ (u₀ v) ≠ 0) :
    ∀ (N : ℕ) (T : Finset (HeightOneSpectrum (𝓞 F)))
      (l : ∀ v : HeightOneSpectrum (𝓞 F), List (orthGroup Q (v.adicCompletion F))),
      (∀ v ∈ T, (l v).length ≤ N ∧ ∀ g ∈ l v, g ∈ eqPairSet Q _) →
      ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)),
        (∀ v ∈ T, U v ∈ 𝓝 (omat (l v).prod)) →
        ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, omat (orthMap Q (v.adicCompletion F) σ) ∈ U v) ∧
          ∀ v ∉ T, orthMap Q (v.adicCompletion F) σ ∈ stdStab Q v := by
  classical
  intro N
  induction N with
  | zero =>
    intro T l hl U hU
    refine ⟨1, Subgroup.one_mem _, fun v hv => ?_, fun v _ => by rw [map_one]; exact Subgroup.one_mem _⟩
    have h0 : l v = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hl v hv).1)
    have := mem_of_mem_nhds (hU v hv)
    rw [h0, List.prod_nil] at this
    rw [map_one]; exact this
  | succ N ih =>
    intro T l hl U hU
    -- the first factor as a pair
    have hpair : ∀ v ∈ T, ∃ a b : Fin n → v.adicCompletion F, Q.evalIn _ a ≠ 0 ∧ Q.evalIn _ a = Q.evalIn _ b ∧
        (l v).headD 1 = symm Q _ a * symm Q _ b := by
      intro v hv
      rcases hlv : l v with _ | ⟨g, t⟩
      · exact ⟨u₀ v, u₀ v, hu₀ v, rfl, by rw [symm_mul_self]; rfl⟩
      · obtain ⟨a, b, ha, hab, hg⟩ := (hl v hv).2 g (by rw [hlv]; exact List.mem_cons_self)
        exact ⟨a, b, ha, hab, hg⟩
    choose! a b ha hab hhead using hpair
    have hprod : ∀ v : HeightOneSpectrum (𝓞 F), (l v).prod = (l v).headD 1 * (l v).tail.prod := by
      intro v
      rcases l v with _ | ⟨g, t⟩
      · simp
      · simp
    -- split the neighbourhood
    have hsplit : ∀ v ∈ T, ∃ U₁ ∈ 𝓝 (omat (symm Q (v.adicCompletion F) (a v) * symm Q _ (b v))),
        ∃ U₂ ∈ 𝓝 (omat (l v).tail.prod), ∀ x ∈ U₁, ∀ y ∈ U₂, x * y ∈ U v := by
      intro v hv
      have hmem : U v ∈ 𝓝 (omat (symm Q (v.adicCompletion F) (a v) * symm Q _ (b v)) * omat (l v).tail.prod) := by
        rw [← hhead v hv, ← omat_mul, ← hprod]; exact hU v hv
      have hc := (continuous_matmul_joint v).continuousAt
        (x := (omat (symm Q (v.adicCompletion F) (a v) * symm Q _ (b v)), omat (l v).tail.prod))
      obtain ⟨U₁, hU₁, U₂, hU₂, h12⟩ := mem_nhds_prod_iff.mp (hc.preimage_mem_nhds hmem)
      refine ⟨U₁, hU₁, U₂, hU₂, fun x hx y hy => ?_⟩
      have := h12 (Set.mk_mem_prod hx hy)
      simp only [Set.mem_preimage] at this
      exact this
    choose! U₁ hU₁ U₂ hU₂ h12 using hsplit
    obtain ⟨σ₁, hσ₁, hσ₁T, hσ₁T'⟩ := pair_approx hV T a b ha hab U₁ hU₁
    obtain ⟨σ₂, hσ₂, hσ₂T, hσ₂T'⟩ := ih T (fun v => (l v).tail)
      (fun v hv => ⟨by rw [List.length_tail]; have := (hl v hv).1; omega,
        fun g hg => (hl v hv).2 g (List.mem_of_mem_tail hg)⟩) U₂ hU₂
    refine ⟨σ₁ * σ₂, Subgroup.mul_mem _ hσ₁ hσ₂, fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul, omat_mul]; exact h12 v hv _ (hσ₁T v hv) _ (hσ₂T v hv)
    · rw [map_mul]; exact Subgroup.mul_mem _ (hσ₁T' v hv) (hσ₂T' v hv)

/-- **Steps 1a–1b of O'Meara 104:4:** elements of the group generated by short commutators at finitely many primes
are approximated by $\sigma \in O'(V)$ integral off $T$ (pad the factorizations to a common length). -/
theorem eqPair_approx (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (hV : VecApprox Q)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (φ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F))
    (hφ : ∀ v ∈ T, φ v ∈ eqPairGroup Q (v.adicCompletion F))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hU : ∀ v ∈ T, U v ∈ 𝓝 (omat (φ v))) :
    ∃ σ ∈ spinorKernel Q F, (∀ v ∈ T, omat (orthMap Q (v.adicCompletion F) σ) ∈ U v) ∧
      ∀ v ∉ T, orthMap Q (v.adicCompletion F) σ ∈ stdStab Q v := by
  classical
  have hu₀ : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin n → v.adicCompletion F, Q.evalIn _ x ≠ 0 := by
    intro v
    obtain ⟨e, -, he⟩ := exists_orthogonal_basis Q (v.adicCompletion F) hQ
    exact ⟨e ⟨0, hn⟩, he _⟩
  choose u₀ hu₀ using hu₀
  choose! l hl hlprod using fun v (hv : v ∈ T) => exists_list_of_mem_eqPairGroup Q (hφ v hv)
  exact list_approx Q hV u₀ hu₀ (T.sup fun v => (l v).length) T l
    (fun v hv => ⟨Finset.le_sup (f := fun v => (l v).length) hv, hl v hv⟩) U
    (fun v hv => by rw [hlprod v hv]; exact hU v hv)

/-- **Step 1 of O'Meara 104:4 when every $V_\mathfrak p$ is isotropic:** `VecApprox Q` implies `RotApprox Q`
(step 1c: $O'(V_\mathfrak p)$ is generated by short commutators, `spinorKernel_eq_eqPairGroup`). For $n \ge 5$ every
$V_\mathfrak p$ is isotropic. -/
theorem rotApprox_of_vecApprox (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (hV : VecApprox Q)
    (hiso : ∀ v : HeightOneSpectrum (𝓞 F), Q.IsotropicIn (v.adicCompletion F)) : RotApprox Q := by
  intro T φ hφ U hU
  exact eqPair_approx Q hQ hn hV T φ (fun v hv => by
    rw [← spinorKernel_eq_eqPairGroup Q _ hQ (hiso v)]; exact hφ v hv) U hU

/-- **Step 1c of O'Meara 104:4 in general** (p. 316): given a *correction* — for every finite $T$ and
$\varphi_\mathfrak p \in O'(V_\mathfrak p)$ an element $g \in O'(V)$ with $g\varphi_\mathfrak p \in \Omega(V_\mathfrak p)$ on $T$ and
$g \in \Omega(V_\mathfrak p)$ at every prime outside $T$ (O'Meara uses 95:1 and 101:9) — `VecApprox Q` implies `RotApprox Q`:
approximate $g\varphi_\mathfrak p$ on $T$ and $g$ at the primes where $g$ is not integral by $\sigma \in O'(V)$ (`eqPair_approx`),
and take $g^{-1}\sigma$. -/
theorem rotApprox_of_vecApprox_of_correction (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (hV : VecApprox Q)
    (hcorr : ∀ (T : Finset (HeightOneSpectrum (𝓞 F)))
      (φ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F)),
      (∀ v ∈ T, φ v ∈ spinorKernel Q (v.adicCompletion F)) →
      ∃ g ∈ spinorKernel Q F, (∀ v ∈ T, orthMap Q (v.adicCompletion F) g * φ v ∈
          commutator (↥(orthGroup Q (v.adicCompletion F)))) ∧
        ∀ v ∉ T, orthMap Q (v.adicCompletion F) g ∈
          commutator (↥(orthGroup Q (v.adicCompletion F)))) :
    RotApprox Q := by
  classical
  intro T φ hφ U hU
  obtain ⟨g, hgO, hgT, hgall⟩ := hcorr T φ hφ
  have hgev := (diagF Q g).2
  set T₂ := (Filter.eventually_cofinite.mp hgev).toFinset
  have hT₂ : ∀ v, v ∉ T₂ → orthMap Q (v.adicCompletion F) g ∈ stdStab Q v := by
    intro v hv; by_contra hc; exact hv ((Filter.eventually_cofinite.mp hgev).mem_toFinset.mpr hc)
  choose N hN hNσ using fun v : HeightOneSpectrum (𝓞 F) => exists_mem_nhds_stdStab v Q
  set gv : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F) :=
    fun v => orthMap Q (v.adicCompletion F) g
  have hE : ∀ v : HeightOneSpectrum (𝓞 F), eqPairGroup Q (v.adicCompletion F) =
      commutator (↥(orthGroup Q (v.adicCompletion F))) := fun v => eqPairGroup_eq_commutator Q _ hQ
  have hleft : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : orthGroup Q (v.adicCompletion F))
      {S : Set (Matrix (Fin n) (Fin n) (v.adicCompletion F))}, S ∈ 𝓝 (omat h) →
      {M | omat (gv v)⁻¹ * M ∈ S} ∈ 𝓝 (omat (gv v * h)) := by
    intro v h S hS
    have hc : ContinuousAt (fun M : Matrix (Fin n) (Fin n) (v.adicCompletion F) => omat (gv v)⁻¹ * M)
        (omat (gv v * h)) :=
      continuousAt_matmul_of v (M := fun _ => omat (gv v)⁻¹) (N := fun M => M) continuousAt_const
        continuousAt_id
    refine hc.preimage_mem_nhds ?_
    rw [← omat_mul, inv_mul_cancel_left]; exact hS
  obtain ⟨σ, hσ, hσT, hσT'⟩ := eqPair_approx Q hQ hn hV (T ∪ T₂)
    (fun v => if v ∈ T then gv v * φ v else gv v)
    (by
      intro v hv
      rw [hE]
      split_ifs with h
      · exact hgT v h
      · exact hgall v h)
    (fun v => if v ∈ T then {M | omat (gv v)⁻¹ * M ∈ U v} else {M | omat (gv v)⁻¹ * M ∈ N v})
    (by
      intro v _
      split_ifs with h
      · exact hleft v (φ v) (hU v h)
      · have := hleft v 1 (S := N v) (by rw [omat_one]; exact hN v)
        rwa [mul_one] at this)
  refine ⟨g⁻¹ * σ, Subgroup.mul_mem _ (Subgroup.inv_mem _ hgO) hσ, fun v hv => ?_, fun v hv => ?_⟩
  · have h := hσT v (Finset.mem_union_left _ hv)
    simp only [hv, ite_true, Set.mem_ofPred_eq] at h
    rw [map_mul, map_inv, omat_mul]; exact h
  · rw [map_mul, map_inv]
    by_cases h2 : v ∈ T₂
    · have h := hσT v (Finset.mem_union_right _ h2)
      simp only [hv, ite_false, Set.mem_ofPred_eq] at h
      exact hNσ v _ h
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hT₂ v h2)) (hσT' v (by simp [hv, h2]))
end QuadFormsKB.Lattices
