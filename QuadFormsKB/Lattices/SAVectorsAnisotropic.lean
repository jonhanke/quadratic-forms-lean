/-
# Strong approximation for vectors of a given norm, general case (O'Meara 104:3)

**Layer:** $V = F^n$ with `Q : QuadForm F n` nondegenerate over a number field $F$, $n \ge 4$, indefinite (isotropic at
some infinite place $q_0$); local completions, lattices on the complement $v_0^\perp$ (`Lattices/SAPerpCoords.lean`).

**Proves** `vecApprox_of_indefinite`: **`VecApprox Q` for every nondegenerate indefinite $Q$ in $n \ge 4$ variables**
(O'Meara 1973, 104:3, printed pp. 311–315 = PDF pp. 319–323), hence the named input `VecStrongApproximation F`
(`vecStrongApproximation`) and, with `strongApproximationSpin_of_vecInput`, the input `StrongApproximationSpin F`
(`strongApproximationSpin`).

*Proof (O'Meara's steps 1–5).* After enlarging $T$ (bad primes) the target is a vector $z$ with $Q(z) = a$ close to
$z_\mathfrak p$ on $T$ and integral elsewhere.
1. $w$ with $Q(w) = a$ close to the $z_\mathfrak p$ (`exists_quadric_approx`), $\lambda \approx 1$ on $T$ with
   $v_0 = \lambda w$ integral off $T$ (strong approximation in $F$).
2. $U = v_0^\perp$ in coordinates $R(y) = Q(My)$; the lattice $K$ on $U$ (`exists_lat_comap`) small on $T$ and
   $\mathfrak o^n \cap U$ elsewhere; Lemma 104:1 (`exists_scale_represents`) gives $\mu$, a unit on
   $T_1 = \{\mathfrak p \notin T : \lambda \notin \mathfrak o_\mathfrak p^\times\}$.
3. Very strong approximation (`exists_very_strong_approx`) gives $\beta$ with $c = a(1 - \lambda^2\beta^2)$ represented by
   every $K_\mathfrak p$ after division by $\mu^2$ (local lemmas `LocRep.exists_perp_std`, `exists_beta_local`) and by $U$
   at the infinite places (signs, `isSquare_one_sub_of_lt`).
4. By Hasse–Minkowski and Lemma 104:1, $c = R(t)$ with $t \in K$; $z = \beta v_0 + Mt$.
-/
import QuadFormsKB.Lattices.SAVecAux

open NumberField IsDedekindDomain Matrix Topology WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {m : ℕ}

section GoodPrime

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

variable {Q : QuadForm F (m + 1)} {Q₀ : QuadForm (𝓞 F) (m + 1)} {k : 𝓞 F}
  (hQ₀ : Q₀.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F k) • Q)

include hQ₀ in
/-- $B(x, y)$ is integral on $\mathfrak o_\mathfrak p^n$ at a good prime. -/
theorem valued_qbil_le_one (hk : k ∉ v.asIdeal) {x y : Fin (m + 1) → Fv} (hx : x ∈ std v) (hy : y ∈ std v) :
    Valued.v (qbil Q Fv x y) ≤ 1 := by
  rw [qbil_eq_polar]
  refine (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_sub _ _ _).trans (max_le ?_ ?_)) ?_)
  · exact valued_evalIn_le_one v hQ₀ hk (Submodule.add_mem _ hx hy)
  · exact valued_evalIn_le_one v hQ₀ hk hx
  · exact valued_evalIn_le_one v hQ₀ hk hy

include hQ₀ in
/-- **Local representation by the lattice on $v_0^\perp$ at a good prime** (O'Meara 104:3 step 3): with
$L = \{y : My \in \mathfrak o_\mathfrak p^{m+1}\}$, every unit is $R(y)$, $y \in L$; every integral $c$ is, if $Q(v_0)$ is a unit. -/
@[kb "omeara1963" "§104, proof of 104:3, step 3, p. 313"]
theorem exists_rep_perp_lattice (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hk : k ∉ v.asIdeal)
    (hdet : Q₀.hessian.det ∉ v.asIdeal) (hm : 3 ≤ m) {v₀ : Fin (m + 1) → F}
    {Mb : Matrix (Fin (m + 1)) (Fin m) F} {Nb : Matrix (Fin m) (Fin (m + 1)) F}
    (hMN : ∀ x : Fin (m + 1) → Fv, qbil Q Fv (locVec v v₀) x = 0 →
      Mb.map (algebraMap F Fv) *ᵥ (Nb.map (algebraMap F Fv) *ᵥ x) = x)
    (hv₀ : locVec v v₀ ∈ std v) (hv₀0 : locVec v v₀ ≠ 0)
    {L : Submodule (v.adicCompletionIntegers F) (Fin m → Fv)}
    (hL : ∀ y, y ∈ L ↔ Mb.map (algebraMap F Fv) *ᵥ y ∈ std v) {c : Fv}
    (hc : Valued.v c = 1 ∨ (Valued.v c ≤ 1 ∧ Valued.v (Q.evalIn Fv (locVec v v₀)) = 1)) :
    ∃ y ∈ L, (pullbackForm Q Mb).evalIn Fv y = c := by
  obtain ⟨x, hx, hperp, hxc⟩ : ∃ x ∈ std v, qbil Q Fv (locVec v v₀) x = 0 ∧ Q.evalIn Fv x = c := by
    rcases hc with h | h
    · obtain ⟨c', hc'0, hc'std, hc'prim⟩ := exists_primitive hv₀0
      obtain ⟨x, hx, hp, hq⟩ := LocRep.exists_perp_std v hQ₀ h2 hk hdet (by omega) hc'std
        (Or.inl ⟨hc'prim, h⟩)
      refine ⟨x, hx, ?_, hq⟩
      rw [qbil_smul_left] at hp
      exact (mul_eq_zero.mp hp).resolve_left hc'0
    · exact LocRep.exists_perp_std v hQ₀ h2 hk hdet (by omega) hv₀ (Or.inr h)
  refine ⟨Nb.map (algebraMap F Fv) *ᵥ x, (hL _).mpr (by rw [hMN x hperp]; exact hx), ?_⟩
  rw [evalIn_pullback, hMN x hperp, hxc]

include hQ₀ in
/-- **A symmetry of the lattice on $v_0^\perp$** at a good prime: $\tau_e$ for $e \in L$ with $R(e) = 1$. -/
theorem symm_stab_perp_lattice (hk : k ∉ v.asIdeal) {Mb : Matrix (Fin (m + 1)) (Fin m) F}
    {L : Submodule (v.adicCompletionIntegers F) (Fin m → Fv)}
    (hL : ∀ y, y ∈ L ↔ Mb.map (algebraMap F Fv) *ᵥ y ∈ std v) {e : Fin m → Fv} (he : e ∈ L)
    (he1 : (pullbackForm Q Mb).evalIn Fv e = 1) :
    locAct v ((symm (pullbackForm Q Mb) Fv e : orthGroup _ _) : GL (Fin m) Fv) L = L := by
  set R := pullbackForm Q Mb
  have hR0 : R.evalIn Fv e ≠ 0 := by rw [he1]; exact one_ne_zero
  have hle : ∀ M : Submodule (v.adicCompletionIntegers F) (Fin m → Fv), M = L →
      locAct v ((symm R Fv e : orthGroup _ _) : GL (Fin m) Fv) M ≤ L := by
    rintro M rfl y hy
    obtain ⟨y', hy', rfl⟩ := hy
    change ((symm R Fv e : GL (Fin m) Fv) : Matrix (Fin m) (Fin m) Fv) *ᵥ y' ∈ M
    rw [symm_mulVec_bil R Fv hR0, he1, div_one, qbil_pullback]
    refine Submodule.sub_mem _ hy' (smul_mem_of_valued_le ?_ he)
    exact valued_qbil_le_one v hQ₀ hk ((hL e).mp he) ((hL y').mp hy')
  refine le_antisymm (hle L rfl) ?_
  intro y hy
  refine ⟨((symm R Fv e : GL (Fin m) Fv) : Matrix (Fin m) (Fin m) Fv) *ᵥ y, hle L rfl ⟨y, hy, rfl⟩, ?_⟩
  change ((symm R Fv e : GL (Fin m) Fv) : Matrix (Fin m) (Fin m) Fv) *ᵥ
    (((symm R Fv e : GL (Fin m) Fv) : Matrix (Fin m) (Fin m) Fv) *ᵥ y) = y
  rw [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, symm_mul_self]
  simp

end GoodPrime

/-! ### Small helpers -/

theorem locVec_mulVec_rect {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Mb : Matrix (Fin n) (Fin m) F) (t : Fin m → F) :
    locVec v (Mb *ᵥ t) = Mb.map (algebraMap F (v.adicCompletion F)) *ᵥ locVec v t := by
  funext i
  simp only [locVec_eq, mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem representsIn_of_mul_isSquare {n : ℕ} (R : QuadForm F n) (K : Type*) [Field K] [Algebra F K] [CharZero K]
    {y : Fin n → K} (hy : R.evalIn K y ≠ 0) {c : F} (h : IsSquare (algebraMap F K c * R.evalIn K y)) :
    R.RepresentsIn K c := by
  obtain ⟨s, hs⟩ := h
  refine ⟨(s / R.evalIn K y) • y, ?_⟩
  rw [evalIn_smul_sq, div_pow, sq s, ← hs]
  field_simp

theorem smul_mem_ball' {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {c : v.adicCompletion F} {j k : ℤ}
    (hc : Valued.v c ≤ exp (-j)) {x : Fin n → v.adicCompletion F} (hx : x ∈ ball v k) : c • x ∈ ball v (j + k) := by
  intro i
  rw [Pi.smul_apply, smul_eq_mul, map_mul, neg_add, exp_add]
  exact mul_le_mul' hc (hx i)

theorem eventually_valuation_eq_one {x : F} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x = 1 := by
  filter_upwards [eventually_valuation_le_one (F := F) x, eventually_valuation_le_one (F := F) x⁻¹] with v h1 h2
  rw [map_inv₀] at h2
  have h0 : v.valuation F x ≠ 0 := by simpa using hx
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)

theorem valued_eq_one_of_mul_self {v : HeightOneSpectrum (𝓞 F)} {s : v.adicCompletion F}
    (h : Valued.v (s * s) = 1) : Valued.v s = 1 := by
  have hs : s ≠ 0 := by rintro rfl; rw [mul_zero, map_zero] at h; exact zero_ne_one h
  obtain ⟨k, hk⟩ := exists_valued_eq_exp v hs
  rw [map_mul, hk, ← exp_add, ← exp_zero, exp_inj] at h
  rw [hk, ← exp_zero, exp_inj]; omega

/-! ### The core of 104:3 -/

set_option maxHeartbeats 1600000 in
/-- **The core of O'Meara 104:3** (after the reductions): $T \ne \emptyset$ contains every bad prime. -/
@[kb "omeara1963" "§104, proof of 104:3, step 4, pp. 314–315"]
theorem vecApprox_core (Q : QuadForm F (m + 1)) (hQ : Q.Nondegenerate) (hm : 3 ≤ m) (q₀ : InfinitePlace F)
    (hq₀ : Q.IsotropicIn q₀.Completion) {Q₀ : QuadForm (𝓞 F) (m + 1)} {k : 𝓞 F}
    (hQ₀ : Q₀.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F k) • Q)
    {u : Fin (m + 1) → F} (hu : Q.evalIn F u ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T.Nonempty)
    (hgood : ∀ v ∉ T, (2 : 𝓞 F) ∉ v.asIdeal ∧ k ∉ v.asIdeal ∧ Q₀.hessian.det ∉ v.asIdeal ∧
      Valued.v (algebraMap F (v.adicCompletion F) (Q.evalIn F u)) = 1)
    (z : ∀ v : HeightOneSpectrum (𝓞 F), Fin (m + 1) → v.adicCompletion F)
    (hz : ∀ v ∈ T, Q.evalIn _ (z v) = algebraMap F _ (Q.evalIn F u)) (r : HeightOneSpectrum (𝓞 F) → ℤ) :
    ∃ y : Fin (m + 1) → F, Q.evalIn F y = Q.evalIn F u ∧ (∀ v ∈ T, locVec v y - z v ∈ ball v (r v)) ∧
      ∀ v ∉ T, locVec v y ∈ std v := by
  classical
  set a := Q.evalIn F u
  -- Step 1: `w` with `Q(w) = a` close to the `z_p`
  obtain ⟨w, hwa, hwz⟩ := exists_quadric_approx Q hQ (by omega) hu T z hz
    (fun v => {y | y - z v ∈ ball v (r v)}) (fun v _ => ball_add_mem_nhds v (z v) (r v))
  choose sw hsw0 hsw using fun v : HeightOneSpectrum (𝓞 F) => exists_mem_ball_neg v (locVec v w)
  set ρ : HeightOneSpectrum (𝓞 F) → ℤ := fun v => |r v| + |sw v| + 1
  have hwint : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, locVec v w ∈ std v := by
    have := Filter.eventually_all.mpr fun i : Fin (m + 1) => eventually_valuation_le_one (F := F) (w i)
    filter_upwards [this] with v hv i
    rw [locVec_apply', valued_algebraMap, neg_zero, exp_zero]; exact hv i
  set Pw := (Filter.eventually_cofinite.mp hwint).toFinset
  have hPw : ∀ v, v ∉ Pw → locVec v w ∈ std v := by
    intro v hv; by_contra hc; exact hv ((Filter.eventually_cofinite.mp hwint).mem_toFinset.mpr hc)
  -- Step 2: `λ`
  obtain ⟨lam, hlamT, hlamout⟩ := exists_scalar_approx (T ∪ Pw)
    (fun v => if v ∈ T then 1 else 0)
    (fun v => if v ∈ T then {x | Valued.v (x - 1) ≤ exp (-ρ v)} else {x | Valued.v (x - 0) ≤ exp (-sw v)})
    (fun v _ => by
      split_ifs
      · exact valued_le_mem_nhds v 1 (ρ v)
      · exact valued_le_mem_nhds v 0 (sw v))
  have hlam1 : ∀ v ∈ T, Valued.v (algebraMap F (v.adicCompletion F) lam - 1) ≤ exp (-ρ v) := by
    intro v hv
    have := hlamT v (Finset.mem_union_left _ hv)
    simpa [hv] using this
  have hlamlt : ∀ v ∈ T, Valued.v (algebraMap F (v.adicCompletion F) lam - 1) < 1 := fun v hv =>
    (hlam1 v hv).trans_lt (by
      rw [← exp_zero, exp_lt_exp]; have := abs_nonneg (r v); have := abs_nonneg (sw v); simp only [ρ]; linarith)
  have hlamU : ∀ v ∈ T, Valued.v (algebraMap F (v.adicCompletion F) lam) = 1 := by
    intro v hv
    have : Valued.v (algebraMap F (v.adicCompletion F) lam - 1) < Valued.v (1 : v.adicCompletion F) := by
      rw [map_one]; exact hlamlt v hv
    rw [Valuation.map_eq_of_sub_lt _ this, map_one]
  have hlam0 : lam ≠ 0 := by
    obtain ⟨v, hv⟩ := hT
    intro h0; have := hlamU v hv; rw [h0, map_zero, map_zero] at this; exact zero_ne_one this
  have hlamint : ∀ v ∉ T, Valued.v (algebraMap F (v.adicCompletion F) lam) ≤ 1 := by
    intro v hv
    by_cases hP : v ∈ Pw
    · have := hlamT v (Finset.mem_union_right _ hP)
      simp only [hv, ite_false, Set.mem_ofPred_eq, sub_zero] at this
      exact this.trans (by rw [← exp_zero, exp_le_exp]; linarith [hsw0 v])
    · exact hlamout v (by simp [hv, hP])
  set v₀ := lam • w
  have hv₀std : ∀ v ∉ T, locVec v v₀ ∈ std v := by
    intro v hv
    rw [locVec_smul']
    by_cases hP : v ∈ Pw
    · have := hlamT v (Finset.mem_union_right _ hP)
      simp only [hv, ite_false, Set.mem_ofPred_eq, sub_zero] at this
      have h := smul_mem_ball' this (hsw v)
      rwa [add_neg_cancel] at h
    · exact smul_mem_of_valued_le (hlamint v hv) (hPw v hP)
  have hQv₀ : Q.evalIn F v₀ = lam ^ 2 * a := by simp only [v₀]; rw [evalIn_smul_sq, hwa]
  have hQv₀0 : Q.evalIn F v₀ ≠ 0 := by rw [hQv₀]; exact mul_ne_zero (pow_ne_zero 2 hlam0) hu
  have hv₀0 : ∀ v, locVec v v₀ ≠ 0 := by
    intro v h0
    have := evalIn_locVec Q v v₀
    rw [h0] at this
    simp only [QuadForm.evalIn, Pi.zero_apply, mul_zero, zero_mul, ite_self, Finset.sum_const_zero] at this
    exact hQv₀0 ((map_eq_zero _).mp this.symm)
  -- Step 3: coordinates on `v₀^⊥`, the lattice `K'`, and `μ` from Lemma 104:1
  obtain ⟨Mb, Nb, hNM, hN01, hperp, hMN, hRnd⟩ := exists_perp_coords Q hQ hQv₀0
  set R := pullbackForm Q Mb
  obtain ⟨K', hK'⟩ := exists_lat_comap Mb Nb hNM hN01 T (fun v => if v ∈ T then r v else 0)
    (fun v hv => by simp [hv])
  have hK'T : ∀ v ∈ T, ∀ y, y ∈ loc v K'.1 ↔ Mb.map (algebraMap F (v.adicCompletion F)) *ᵥ y ∈ ball v (r v) := by
    intro v hv y; rw [hK' v y]; simp [hv]
  have hK'out : ∀ v ∉ T, ∀ y, y ∈ loc v K'.1 ↔ Mb.map (algebraMap F (v.adicCompletion F)) *ᵥ y ∈ std v := by
    intro v hv y; rw [hK' v y]; simp [hv]
  set T₁ := (Filter.eventually_cofinite.mp (eventually_valuation_eq_one hlam0)).toFinset.filter (· ∉ T)
  have hT₁ : ∀ v, v ∈ T₁ ↔ v ∉ T ∧ v.valuation F lam ≠ 1 := by
    intro v; simp [T₁, and_comm]
  have himp : ∀ v ∈ T₁, ∃ e : Fin m → v.adicCompletion F, R.evalIn _ e ≠ 0 ∧
      locAct v ((symm R (v.adicCompletion F) e : orthGroup R _) : GL (Fin m) _) (loc v K'.1) = loc v K'.1 := by
    intro v hv
    have hvT := ((hT₁ v).mp hv).1
    obtain ⟨h2, hk, hdet, -⟩ := hgood v hvT
    obtain ⟨e, he, he1⟩ := exists_rep_perp_lattice v hQ₀ h2 hk hdet hm (hMN _) (hv₀std v hvT) (hv₀0 v)
      (hK'out v hvT) (c := 1) (Or.inl (map_one _))
    exact ⟨e, by rw [he1]; exact one_ne_zero, symm_stab_perp_lattice v hQ₀ hk (hK'out v hvT) he he1⟩
  obtain ⟨μ, hμ0, hμT₁, hμrep⟩ := exists_scale_represents R hRnd K' T₁ himp
  -- Step 4: the local choice of `β` on `T`
  have ha0 : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) a ≠ 0 :=
    fun v => (map_ne_zero _).mpr hu
  have hTdata : ∀ v ∈ T, ∃ y₀ : Fin m → v.adicCompletion F, ∃ β₀ : v.adicCompletion F, ∃ B ∈ 𝓝 β₀,
      Mb.map (algebraMap F (v.adicCompletion F)) *ᵥ y₀ ∈ ball v (r v) ∧ R.evalIn _ y₀ ≠ 0 ∧
      ∀ β ∈ B, Valued.v (algebraMap F _ lam * β - 1) ≤ exp (-ρ v) ∧
        algebraMap F _ a * (1 - algebraMap F _ lam ^ 2 * β ^ 2) ≠ 0 ∧
        IsSquare (algebraMap F _ a * (1 - algebraMap F _ lam ^ 2 * β ^ 2) /
          (algebraMap F _ (μ ^ 2) * R.evalIn _ y₀)) ∧
        Valued.v (algebraMap F _ a * (1 - algebraMap F _ lam ^ 2 * β ^ 2) /
          (algebraMap F _ (μ ^ 2) * R.evalIn _ y₀)) = 1 := by
    intro v hv
    obtain ⟨e, -, he⟩ := exists_orthogonal_basis R (v.adicCompletion F) hRnd
    set y₁ := e ⟨0, by omega⟩
    have hy₁ : R.evalIn _ y₁ ≠ 0 := he _
    obtain ⟨s1, -, hs1⟩ := exists_mem_ball_neg v (Mb.map (algebraMap F (v.adicCompletion F)) *ᵥ y₁)
    have hμv : algebraMap F (v.adicCompletion F) (μ ^ 2) ≠ 0 := (map_ne_zero _).mpr (pow_ne_zero 2 hμ0)
    set C := algebraMap F (v.adicCompletion F) (μ ^ 2) * R.evalIn _ y₁ / algebraMap F _ a
    have hC : C ≠ 0 := div_ne_zero (mul_ne_zero hμv hy₁) (ha0 v)
    obtain ⟨cC, hcC⟩ := exists_valued_eq_exp v hC
    have h4 : (4 : v.adicCompletion F) ≠ 0 := by
      have := (algebraMap F (v.adicCompletion F)).injective.ne (by norm_num : (4 : F) ≠ 0)
      rwa [map_ofNat, map_zero] at this
    obtain ⟨k4, hk4⟩ := exists_valued_eq_exp v h4
    set N : ℤ := |cC| + |ρ v| + |k4| + |s1| + |r v| + 1
    set y₀ := ϖk v N • y₁
    have hR0 : R.evalIn _ y₀ = ϖk v N ^ 2 * R.evalIn _ y₁ := evalIn_smul_sq _ _ _ _
    refine ?_
    have hdC : algebraMap F (v.adicCompletion F) (μ ^ 2) * R.evalIn _ y₀ / algebraMap F _ a = ϖk v N ^ 2 * C := by
      rw [hR0]; simp only [C]; ring
    have hvd : Valued.v (algebraMap F (v.adicCompletion F) (μ ^ 2) * R.evalIn _ y₀ / algebraMap F _ a) =
        exp (-(2 * N) + cC) := by
      rw [hdC, map_mul, map_pow, valued_ϖk, hcC, sq, ← exp_add, ← exp_add]; congr 1; ring
    obtain ⟨β₀, B, hB, hBp⟩ := exists_beta_local v (hlamlt v hv) (ha0 v)
      (show algebraMap F _ (μ ^ 2) * R.evalIn _ y₀ ≠ 0 from
        mul_ne_zero hμv (by rw [hR0]; exact mul_ne_zero (pow_ne_zero 2 (ϖk_ne_zero v N)) hy₁)) (ρ v)
      (by rw [hvd, exp_le_exp]; have := abs_nonneg cC; have := le_abs_self cC; have := le_abs_self (ρ v);
          have := abs_nonneg k4; have := abs_nonneg s1; have := abs_nonneg (r v); simp only [N]; linarith)
      (by rw [hvd, hk4, exp_lt_exp]; have := le_abs_self cC; have := neg_abs_le k4; have := abs_nonneg (ρ v);
          have := abs_nonneg k4; have := abs_nonneg cC;
          have := abs_nonneg s1; have := abs_nonneg (r v); simp only [N]; linarith)
    refine ⟨y₀, β₀, B, hB, ?_, by rw [hR0]; exact mul_ne_zero (pow_ne_zero 2 (ϖk_ne_zero v N)) hy₁, hBp⟩
    rw [mulVec_smul]
    have := ball_anti v (n := m + 1) (show r v ≤ N + -s1 by
      have := le_abs_self (r v); have := abs_nonneg cC; have := abs_nonneg (ρ v); have := abs_nonneg k4;
      have := le_abs_self s1; simp only [N]; linarith) (smul_mem_ball' (le_of_eq (valued_ϖk v N)) hs1)
    exact this
  choose! y₀ β₀ B hB hy₀K hy₀R hBp using hTdata
  -- `T₂`: where `μ` is not a unit (outside `T ∪ T₁`)
  set T₂ := (Filter.eventually_cofinite.mp (eventually_valuation_eq_one hμ0)).toFinset.filter
    (fun v => v ∉ T ∧ v ∉ T₁)
  have hT₂ : ∀ v, v ∈ T₂ ↔ (v ∉ T ∧ v ∉ T₁) ∧ v.valuation F μ ≠ 1 := by
    intro v; simp [T₂, and_comm]
  have hμv0 : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) μ ≠ 0 :=
    fun v => (map_ne_zero _).mpr hμ0
  choose kμ hkμ using fun v : HeightOneSpectrum (𝓞 F) => exists_valued_eq_exp v (hμv0 v)
  set j : HeightOneSpectrum (𝓞 F) → ℤ := fun v => 2 * |kμ v| + 1
  -- Step 5: very strong approximation for `β`
  set bb : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun v =>
    if v ∈ T then β₀ v else if v ∈ T₁ then 0 else (algebraMap F _ lam)⁻¹
  set OO : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F) := fun v =>
    if v ∈ T then B v else if v ∈ T₁ then {x | Valued.v (x - 0) ≤ exp (-(0 : ℤ))}
      else {x | Valued.v (x - (algebraMap F _ lam)⁻¹) ≤ exp (-j v)}
  have hOO : ∀ v ∈ T ∪ T₁ ∪ T₂, OO v ∈ 𝓝 (bb v) := by
    intro v hv
    simp only [OO, bb]
    split_ifs with h1 h2
    · exact hB v h1
    · exact valued_le_mem_nhds v 0 0
    · exact valued_le_mem_nhds v _ (j v)
  set S : Finset (InfinitePlace F) := Finset.univ.filter fun w => w ≠ q₀ ∧
    ∃ y : Fin m → w.Completion, R.evalIn _ y ≠ 0 ∧ IsSquare (R.evalIn _ y * algebraMap F _ a)
  have hq₀S : q₀ ∉ S := by intro h; exact (Finset.mem_filter.mp h).2.1 rfl
  set Λ : ℝ := ∑ w : InfinitePlace F, w lam
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  have hwlam : ∀ w : InfinitePlace F, 0 < w lam := fun w => AbsoluteValue.pos _ hlam0
  set δ : ℝ := 1 / (2 * (Λ + 1))
  have hδ : 0 < δ := by positivity
  set Rb : ℝ := ∑ w : InfinitePlace F, 2 / w lam
  obtain ⟨β, hβT, hβout, hβS, hβL⟩ := exists_very_strong_approx (T ∪ T₁ ∪ T₂) bb OO hOO q₀ S hq₀S hδ Rb
  have hsmall : ∀ w ∈ S, w (lam ^ 2 * β ^ 2) < 1 / 2 := by
    intro w hw
    have h1 : w lam ≤ Λ := Finset.single_le_sum (f := fun w => w lam) (fun w _ => AbsoluteValue.nonneg _ _)
      (Finset.mem_univ w)
    have h2 := hβS w hw
    have h3 : w lam * w β < 1 / 2 := by
      calc w lam * w β ≤ Λ * w β := mul_le_mul_of_nonneg_right h1 (AbsoluteValue.nonneg _ _)
        _ ≤ Λ * δ := mul_le_mul_of_nonneg_left h2.le hΛ
        _ < 1 / 2 := by simp only [δ]; rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    rw [map_mul, map_pow, map_pow, ← mul_pow]
    have h0 : 0 ≤ w lam * w β := mul_nonneg (AbsoluteValue.nonneg _ _) (AbsoluteValue.nonneg _ _)
    nlinarith
  have hlarge : ∀ w ∉ S, w ((lam * β)⁻¹ ^ 2) < 1 / 2 := by
    intro w hw
    have h1 : 2 / w lam ≤ Rb := Finset.single_le_sum (f := fun w => 2 / w lam)
      (fun w _ => div_nonneg (by norm_num) (AbsoluteValue.nonneg _ _)) (Finset.mem_univ w)
    have h2 := hβL w hw
    have h3 : 2 < w lam * w β := by
      have : 2 / w lam < w β := h1.trans_lt h2
      rw [div_lt_iff₀ (hwlam w)] at this; linarith
    rw [map_pow, map_inv₀, map_mul]
    rw [inv_pow, inv_lt_comm₀ (by positivity) (by norm_num)]
    nlinarith
  -- local properties of `β` and `λ`, `μ`
  have hTT : ∀ v ∈ T, v ∈ T ∪ T₁ ∪ T₂ := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hβB : ∀ v ∈ T, algebraMap F (v.adicCompletion F) β ∈ B v := by
    intro v hv; have := hβT v (hTT v hv); simpa [OO, hv] using this
  have hT₁T : ∀ v ∈ T₁, v ∉ T := fun v hv => ((hT₁ v).mp hv).1
  have hβT₁ : ∀ v ∈ T₁, Valued.v (algebraMap F (v.adicCompletion F) β) ≤ 1 := by
    intro v hv
    have := hβT v (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
    simpa [OO, hT₁T v hv, hv] using this
  have hβT₂ : ∀ v ∈ T₂, Valued.v (algebraMap F (v.adicCompletion F) β - (algebraMap F _ lam)⁻¹) ≤ exp (-j v) := by
    intro v hv
    have h := (hT₂ v).mp hv
    have := hβT v (Finset.mem_union_right _ hv)
    simpa [OO, h.1.1, h.1.2] using this
  have hlamval : ∀ v, v ∉ T → v ∉ T₁ → Valued.v (algebraMap F (v.adicCompletion F) lam) = 1 := by
    intro v hv hv1
    rw [valued_algebraMap]
    by_contra h; exact hv1 ((hT₁ v).mpr ⟨hv, h⟩)
  have hμval : ∀ v, v ∉ T → v ∉ T₁ → v ∉ T₂ → Valued.v (algebraMap F (v.adicCompletion F) μ) = 1 := by
    intro v hv hv1 hv2
    rw [valued_algebraMap]
    by_contra h; exact hv2 ((hT₂ v).mpr ⟨⟨hv, hv1⟩, h⟩)
  have hβint : ∀ v ∉ T, Valued.v (algebraMap F (v.adicCompletion F) β) ≤ 1 := by
    intro v hv
    by_cases h1 : v ∈ T₁
    · exact hβT₁ v h1
    by_cases h2 : v ∈ T₂
    · have hl := hlamval v hv h1
      have hli : Valued.v ((algebraMap F (v.adicCompletion F) lam)⁻¹) = 1 := by rw [map_inv₀, hl, inv_one]
      have e : algebraMap F (v.adicCompletion F) β =
          (algebraMap F _ β - (algebraMap F _ lam)⁻¹) + (algebraMap F _ lam)⁻¹ := by ring
      rw [e]
      refine (Valuation.map_add _ _ _).trans (max_le ((hβT₂ v h2).trans ?_) hli.le)
      rw [← exp_zero, exp_le_exp]; simp only [j]; have := abs_nonneg (kμ v); linarith
    · exact hβout v (by simp [hv, h1, h2])
  -- Step 6: `c = a (1 - λ²β²)`
  set c : F := a * (1 - lam ^ 2 * β ^ 2)
  have hcv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) c =
      algebraMap F _ a * (1 - algebraMap F _ lam ^ 2 * (algebraMap F _ β) ^ 2) := by
    intro v; simp [c, map_mul, map_sub, map_pow]
  have hc0 : c ≠ 0 := by
    obtain ⟨v, hv⟩ := hT
    intro h0
    have := (hBp v hv _ (hβB v hv)).2.1
    rw [← hcv, h0, map_zero] at this; exact this rfl
  -- local representations by `K'`
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ y ∈ loc v K'.1,
      R.evalIn (v.adicCompletion F) y = algebraMap F _ (c / μ ^ 2) := by
    intro v
    have hcμ : algebraMap F (v.adicCompletion F) (c / μ ^ 2) =
        algebraMap F _ c / (algebraMap F _ μ) ^ 2 := by rw [map_div₀, map_pow]
    by_cases hvT : v ∈ T
    · obtain ⟨-, -, ⟨s, hs⟩, hval⟩ := hBp v hvT _ (hβB v hvT)
      rw [hs] at hval
      have hs1 := valued_eq_one_of_mul_self hval
      refine ⟨s • y₀ v, (hK'T v hvT _).mpr ?_, ?_⟩
      · rw [mulVec_smul]; exact smul_mem_of_valued_le hs1.le (hy₀K v hvT)
      · rw [evalIn_smul_sq, sq, ← hs, hcμ, hcv, map_pow]
        have := hy₀R v hvT
        field_simp
    obtain ⟨h2, hk, hdet, hav⟩ := hgood v hvT
    have hqv0 : Valued.v (Q.evalIn (v.adicCompletion F) (locVec v v₀)) =
        Valued.v (algebraMap F (v.adicCompletion F) lam) ^ 2 := by
      rw [evalIn_locVec, show Q.eval v₀ = Q.evalIn F v₀ from rfl, hQv₀, map_mul, map_pow, map_mul, map_pow, hav,
        mul_one]
    by_cases hv1 : v ∈ T₁
    · refine exists_rep_perp_lattice v hQ₀ h2 hk hdet hm (hMN _) (hv₀std v hvT) (hv₀0 v) (hK'out v hvT)
        (Or.inl ?_)
      have hlt : Valued.v (algebraMap F (v.adicCompletion F) lam) < 1 :=
        lt_of_le_of_ne (hlamint v hvT) (by rw [valued_algebraMap]; exact ((hT₁ v).mp hv1).2)
      have hx : Valued.v (algebraMap F (v.adicCompletion F) lam ^ 2 * (algebraMap F _ β) ^ 2) < 1 := by
        rw [map_mul, map_pow, map_pow]
        calc Valued.v (algebraMap F (v.adicCompletion F) lam) ^ 2 * Valued.v (algebraMap F _ β) ^ 2
            ≤ Valued.v (algebraMap F (v.adicCompletion F) lam) ^ 2 * 1 :=
              mul_le_mul' le_rfl (pow_le_one₀ zero_le (hβT₁ v hv1))
          _ = Valued.v (algebraMap F (v.adicCompletion F) lam) * Valued.v (algebraMap F _ lam) := by
              rw [mul_one, sq]
          _ ≤ Valued.v (algebraMap F (v.adicCompletion F) lam) * 1 := mul_le_mul' le_rfl (hlamint v hvT)
          _ < 1 := by rw [mul_one]; exact hlt
      rw [hcμ, hcv, map_div₀, map_mul, Valuation.map_one_sub_of_lt _ hx, hav, map_pow, hμT₁ v hv1]
      simp
    · have hl1 := hlamval v hvT hv1
      refine exists_rep_perp_lattice v hQ₀ h2 hk hdet hm (hMN _) (hv₀std v hvT) (hv₀0 v) (hK'out v hvT)
        (Or.inr ⟨?_, hqv0.trans (by rw [hl1, one_pow])⟩)
      rw [hcμ, hcv, map_div₀, map_mul, hav, one_mul, map_pow]
      by_cases hv2 : v ∈ T₂
      · -- `1 - λ²β² = -λ(β - λ⁻¹)(1 + λβ)`
        have hlam0v : algebraMap F (v.adicCompletion F) lam ≠ 0 := (map_ne_zero _).mpr hlam0
        have e : 1 - algebraMap F (v.adicCompletion F) lam ^ 2 * (algebraMap F _ β) ^ 2 =
            -algebraMap F _ lam * (algebraMap F _ β - (algebraMap F _ lam)⁻¹) * (1 + algebraMap F _ lam * algebraMap F _ β) := by
          field_simp; ring
        have h1 : Valued.v (1 + algebraMap F (v.adicCompletion F) lam * algebraMap F _ β) ≤ 1 := by
          refine (Valuation.map_add _ _ _).trans (max_le (by rw [map_one]) ?_)
          rw [map_mul, hl1, one_mul]; exact hβint v hvT
        rw [e, map_mul, map_mul, Valuation.map_neg, hl1, one_mul, hkμ v, div_le_one₀ (pow_pos exp_pos 2)]
        calc Valued.v (algebraMap F (v.adicCompletion F) β - (algebraMap F _ lam)⁻¹) *
              Valued.v (1 + algebraMap F _ lam * algebraMap F _ β)
            ≤ exp (-j v) * 1 := mul_le_mul' (hβT₂ v hv2) h1
          _ ≤ exp (kμ v) ^ 2 := by
            rw [mul_one, sq, ← exp_add, exp_le_exp]; simp only [j]; have := neg_abs_le (kμ v); linarith
      · rw [hμval v hvT hv1 hv2, one_pow, div_one]
        refine (Valuation.map_sub _ _ _).trans (max_le (by rw [map_one]) ?_)
        rw [map_mul, map_pow, map_pow, hl1, one_pow, one_mul]
        exact pow_le_one₀ zero_le (hβint v hvT)
  -- global representation of `c` by `U` (Hasse–Minkowski)
  have hβ0 : β ≠ 0 := by
    intro h0
    have := hβL q₀ hq₀S
    have hRb : 0 ≤ Rb := Finset.sum_nonneg fun w _ => div_nonneg (by norm_num) (AbsoluteValue.nonneg _ _)
    rw [h0, map_zero] at this; linarith
  have hlb0 : lam * β ≠ 0 := mul_ne_zero hlam0 hβ0
  have hc_large : c = -(lam ^ 2 * a) * β ^ 2 * (1 - (lam * β)⁻¹ ^ 2) := by
    simp only [c]; field_simp; ring
  have hrepF : R.RepresentsIn F c := by
    rw [represents_iff_everywhere_nf R hRnd c hc0]
    intro place
    cases place with
    | finite v =>
      change R.RepresentsIn (v.adicCompletion F) c
      obtain ⟨y, -, hy⟩ := hloc v
      refine ⟨algebraMap F (v.adicCompletion F) μ • y, ?_⟩
      rw [evalIn_smul_sq, hy, map_div₀, map_pow]
      have := hμv0 v
      field_simp
    | infinite w =>
      change R.RepresentsIn w.Completion c
      have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
      have hι : ∀ x : F, (algebraMap F w.Completion x = 0 ↔ x = 0) := fun x => map_eq_zero _
      by_cases hwq : w = q₀
      · subst hwq
        obtain ⟨zq, hzq0, hzq⟩ := hq₀
        set ιv := fun i => algebraMap F w.Completion (v₀ i)
        have hQιv : Q.evalIn w.Completion ιv = algebraMap F _ (lam ^ 2 * a) := by
          rw [show ιv = fun i => algebraMap F w.Completion (v₀ i) from rfl, evalIn_map_tower Q w.Completion (K := F),
            hQv₀]
        have hvv : qbil Q w.Completion ιv ιv ≠ 0 := by
          rw [qbil_self, hQιv]; exact mul_ne_zero two_ne_zero ((map_ne_zero _).mpr (mul_ne_zero
            (pow_ne_zero 2 hlam0) hu))
        set s0 := qbil Q w.Completion ιv zq / qbil Q w.Completion ιv ιv
        set x' := zq - s0 • ιv
        have hx' : qbil Q w.Completion ιv x' = 0 := by
          simp only [x']; rw [sub_eq_add_neg, ← neg_smul, qbil_add_right, qbil_smul_right]
          simp only [s0]; field_simp; ring
        set yq := Nb.map (algebraMap F w.Completion) *ᵥ x'
        have hMyq : Mb.map (algebraMap F w.Completion) *ᵥ yq = x' := hMN _ x' hx'
        have hRyq : R.evalIn w.Completion yq = Q.evalIn w.Completion x' := by
          rw [evalIn_pullback, hMyq]
        have hdecomp : Q.evalIn w.Completion zq = Q.evalIn w.Completion x' + s0 ^ 2 * algebraMap F _ (lam ^ 2 * a) := by
          have e : zq = x' + s0 • ιv := by simp only [x']; abel
          rw [e, evalIn_add_smul, qbil_comm, hx', mul_zero, add_zero, hQιv]
        by_cases hs0 : s0 = 0
        · apply representsIn_of_isotropicIn R _ hRnd
          refine ⟨yq, fun h0 => hzq0 ?_, ?_⟩
          · have : x' = 0 := by rw [← hMyq, h0, mulVec_zero]
            simpa [x', hs0] using this
          · rw [hRyq]; rw [hdecomp, hs0] at hzq; simpa using hzq
        · have hRyq' : R.evalIn w.Completion yq = -(s0 ^ 2 * algebraMap F _ (lam ^ 2 * a)) := by
            rw [hRyq]; linear_combination hdecomp.symm.trans hzq
          have hRyq0 : R.evalIn w.Completion yq ≠ 0 := by
            rw [hRyq']; exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hs0) ((map_ne_zero _).mpr
              (mul_ne_zero (pow_ne_zero 2 hlam0) hu)))
          refine representsIn_of_mul_isSquare R _ hRyq0 ?_
          obtain ⟨X, hX⟩ := isSquare_one_sub_of_lt w (hlarge w hq₀S)
          refine ⟨s0 * algebraMap F _ (lam ^ 2 * a * β) * X, ?_⟩
          rw [hRyq', hc_large]
          simp only [map_mul, map_neg, map_pow] at hX ⊢
          rw [hX]; ring
      by_cases hwS : w ∈ S
      · obtain ⟨-, y, hy0, hsq⟩ := (Finset.mem_filter.mp hwS).2
        refine representsIn_of_mul_isSquare R _ hy0 ?_
        have h1 := isSquare_one_sub_of_lt w (hsmall w hwS)
        have e : algebraMap F w.Completion c * R.evalIn _ y =
            algebraMap F _ (1 - lam ^ 2 * β ^ 2) * (R.evalIn _ y * algebraMap F _ a) := by
          simp only [c, map_mul]; ring
        rw [e]; exact h1.mul hsq
      · have hnot : ∀ y : Fin m → w.Completion, R.evalIn _ y ≠ 0 → ¬ IsSquare (R.evalIn _ y * algebraMap F _ a) :=
          fun y hy hsq => hwS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwq, y, hy, hsq⟩)
        obtain ⟨e, -, he⟩ := exists_orthogonal_basis R w.Completion hRnd
        set y := e ⟨0, by omega⟩
        have hy0 : R.evalIn _ y ≠ 0 := he _
        have hwr : w.IsReal := by
          by_contra hc
          exact hnot y hy0 (isSquare_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.mp hc) _)
        have hneg := (isSquare_or_isSquare_neg w hwr (R.evalIn _ y * algebraMap F _ a)).resolve_left (hnot y hy0)
        refine representsIn_of_mul_isSquare R _ hy0 ?_
        have h1 := isSquare_one_sub_of_lt w (hlarge w hwS)
        have e : algebraMap F w.Completion c * R.evalIn _ y =
            algebraMap F _ (1 - (lam * β)⁻¹ ^ 2) * (-(R.evalIn _ y * algebraMap F _ a)) *
              (algebraMap F _ (lam * β)) ^ 2 := by
          rw [hc_large]; simp only [map_mul, map_neg, map_pow, map_sub, map_one, map_inv₀]; field_simp
        rw [e]; exact (h1.mul hneg).mul ⟨algebraMap F _ (lam * β), sq _⟩
  -- Step 7: `t ∈ K'` with `R(t) = c`, and `z = β v₀ + M t`
  obtain ⟨t, htK, htc⟩ := hμrep c hc0 hrepF hloc
  have hidM : Mb.map (algebraMap F F) = Mb := by ext i j; simp
  have hRt : Q.evalIn F (Mb *ᵥ t) = c := by
    rw [← htc, evalIn_pullback, hidM]
  have hperpF : qbil Q F (Mb *ᵥ t) v₀ = 0 := by
    have := hperp F t
    rw [hidM, show (fun i => algebraMap F F (v₀ i)) = v₀ by funext i; simp] at this
    rw [qbil_comm]; exact this
  refine ⟨Mb *ᵥ t + β • v₀, ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [evalIn_add_smul, hRt, hperpF, mul_zero, add_zero, hQv₀]
    simp only [c]; ring
  · have hlt : locVec v (Mb *ᵥ t) ∈ ball v (r v) := by
      rw [locVec_mulVec_rect]; exact (hK'T v hv _).mp (locVec_mem_loc v htK)
    have e : locVec v (Mb *ᵥ t + β • v₀) - z v =
        (algebraMap F (v.adicCompletion F) lam * algebraMap F _ β - 1) • locVec v w + (locVec v w - z v) +
          locVec v (Mb *ᵥ t) := by
      funext i
      simp only [v₀, locVec_eq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
      ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ (hwz v hv)) hlt
    have h1 := (hBp v hv _ (hβB v hv)).1
    have := smul_mem_ball' h1 (hsw v)
    refine ball_anti v ?_ this
    simp only [ρ]; have := le_abs_self (r v); have := abs_nonneg (sw v); have := le_abs_self (sw v); linarith
  · rw [map_add, locVec_smul', locVec_mulVec_rect]
    exact Submodule.add_mem _ ((hK'out v hv _).mp (locVec_mem_loc v htK))
      (smul_mem_of_valued_le (hβint v hv) (hv₀std v hv))

/-! ### The theorem -/

/-- **O'Meara 1973, 104:3** (strong approximation for vectors of a given norm): `VecApprox Q` for every nondegenerate
indefinite $Q$ in $n \ge 4$ variables. Reductions: $T = \emptyset$ is trivial ($y = u$); otherwise enlarge $T$ by the bad
primes (targets $u$, neighbourhoods $\mathfrak o_\mathfrak p^n$), shrink the neighbourhoods to balls, and apply
`vecApprox_core`. -/
@[kb "omeara1963" "§104, 104:3, pp. 311–315; cassels1978 Ch. 9, Thm. 1.5, p. 131; Ch. 10, Lemma 7.1, p. 187"]
theorem vecApprox_of_indefinite {n : ℕ} (Q : QuadForm F n) (hn : 4 ≤ n) (hQ : Q.Nondegenerate)
    (hind : IsIndefinite Q) : VecApprox Q := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨q₀, hq₀⟩ := hind
  intro u hu T hT z hz Z hZ
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine ⟨u, rfl, by simp [hTe], fun v _ => hT v (by simp [hTe])⟩
  obtain ⟨Q₀, k, hk0, hQ₀⟩ := exists_integral_model Q
  have hdet0 := det_model_ne_zero hk0 hQ₀ hQ
  set a := Q.evalIn F u
  have hbad : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (2 : 𝓞 F) ∉ v.asIdeal ∧ k ∉ v.asIdeal ∧
      Q₀.hessian.det ∉ v.asIdeal ∧ Valued.v (algebraMap F (v.adicCompletion F) a) = 1 := by
    filter_upwards [eventually_not_mem (two_ne_zero : (2 : 𝓞 F) ≠ 0), eventually_not_mem hk0,
      eventually_not_mem hdet0, eventually_valuation_eq_one hu] with v h1 h2 h3 h4
    exact ⟨h1, h2, h3, by rw [valued_algebraMap]; exact h4⟩
  set Bad := (Filter.eventually_cofinite.mp hbad).toFinset
  have hBad : ∀ v, v ∉ Bad → (2 : 𝓞 F) ∉ v.asIdeal ∧ k ∉ v.asIdeal ∧ Q₀.hessian.det ∉ v.asIdeal ∧
      Valued.v (algebraMap F (v.adicCompletion F) a) = 1 := by
    intro v hv; by_contra hc; exact hv ((Filter.eventually_cofinite.mp hbad).mem_toFinset.mpr hc)
  choose! r hr using fun v (hv : v ∈ T) => exists_ball_of_mem_nhds v (hZ v hv)
  set T' := T ∪ Bad
  obtain ⟨y, hya, hyT, hyout⟩ := vecApprox_core Q hQ (by omega) q₀ hq₀ hQ₀ hu T'
    (hTne.mono Finset.subset_union_left)
    (fun v hv => hBad v (fun h => hv (Finset.mem_union_right _ h)))
    (fun v => if v ∈ T then z v else locVec v u)
    (fun v _ => by
      split_ifs with h
      · exact hz v h
      · rw [evalIn_locVec])
    (fun v => if v ∈ T then r v else 0)
  refine ⟨y, hya, fun v hv => ?_, fun v hv => ?_⟩
  · have := hyT v (Finset.mem_union_left _ hv)
    simp only [hv, ite_true] at this
    exact hr v hv _ this
  · by_cases hvB : v ∈ Bad
    · have := hyT v (Finset.mem_union_right _ hvB)
      simp only [hv, ite_false] at this
      have h := Submodule.add_mem _ this (hT v hv)
      rwa [sub_add_cancel] at h
    · exact hyout v (by simp [T', hv, hvB])

/-- **The input `VecStrongApproximation F` holds** (O'Meara 104:3; `vecApprox_of_indefinite`). -/
@[kb "omeara1963" "§104, 104:3, pp. 311–315; cassels1978 Ch. 9, Thm. 1.5, p. 131; Ch. 10, Lemma 7.1, p. 187"]
theorem vecStrongApproximation : VecStrongApproximation F :=
  ⟨fun Q hn hQ hind _ => vecApprox_of_indefinite Q hn hQ hind⟩

/-- **Strong approximation for rotations, unconditional** (Kneser 1956, Eichler 1952; O'Meara 1973, 104:4–104:5): the
input `StrongApproximationSpin F` holds for every number field $F$: for nondegenerate indefinite $Q$ in $n \ge 3$
variables, $O'(V_{\mathbb A_f}) \subseteq O'(V)\,O(\hat L)$ for every lattice $L$. -/
@[kb "omeara1963" "§104, 104:4, p. 315; 104:5, p. 319; cassels1978 Ch. 10, Thm. 7.1, Cor., p. 187"]
theorem strongApproximationSpin : StrongApproximationSpin F :=
  strongApproximationSpin_of_vecInput vecStrongApproximation

/-- **Eichler's theorem, unconditional** (O'Meara 1973, 104:5): for nondegenerate indefinite $Q$ in $n \ge 3$ variables,
two lattices in the same spinor genus are isometric. -/
@[kb "omeara1963" "§104, 104:5, p. 319; cassels1978 Ch. 11, Thm. 1.4, p. 202"]
theorem eichler_spinorGenus_eq_class_uncond {n : ℕ} (Q : QuadForm F n) (hn : 3 ≤ n) (hQ : Q.Nondegenerate)
    (hind : IsIndefinite Q) {L M : Lat F n} (h : SameSpinorGenus Q L M) : IsIsometric Q L.1 M.1 :=
  eichler_spinorGenus_eq_class Q strongApproximationSpin hn hQ hind h

end QuadFormsKB.Lattices
