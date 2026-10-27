/-
# Strong approximation for vectors away from a finite prime (O'Meara 104:3 with $S = \Omega \setminus \{\infty, \mathfrak p\}$)

**Layer:** as `Lattices/SAVectorsAnisotropic.lean`, with the free place a finite prime $\mathfrak p$ at which $V_\mathfrak p$ is
isotropic (O'Meara's $q_0$ discrete); no condition at the infinite places.

**Defines** `VecApproxAway Q E`: `VecApprox` with no conditions at the primes of $E$.

**Proves** `vecApproxAway_of_isotropicAt`: for nondegenerate $Q$ in $n \ge 4$ variables isotropic at $\mathfrak p$,
`VecApproxAway Q {p}` (O'Meara 1973, 104:3 with $S$ = all finite primes except $\mathfrak p$). The proof is the one of
`vecApprox_core` with the very strong approximation theorem for the free place $\mathfrak p$
(`exists_very_strong_approx_at`) and Lemma 104:1 relative to $\{\mathfrak p\}$ (`exists_scale_represents_away`).
-/
import QuadFormsKB.Lattices.SAVectorsAnisotropic

open NumberField IsDedekindDomain Matrix Topology WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {m : ℕ}

/-- **The isotropic place of $V$ in O'Meara 104:3, step 4:** if $V_K$ is isotropic and $1 - (\lambda\beta)^{-2}$ is a square
in $K$, then $c = a(1 - \lambda^2\beta^2)$ is represented by $U_K = v_0^\perp$ ($Q(v_0) = \lambda^2 a$). -/
@[kb "omeara1963" "§104, proof of 104:3, step 4, pp. 314–315"]
theorem representsIn_of_isotropic_perp (Q : QuadForm F (m + 1)) {v₀ : Fin (m + 1) → F}
    {Mb : Matrix (Fin (m + 1)) (Fin m) F} {Nb : Matrix (Fin m) (Fin (m + 1)) F}
    (hMN : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin (m + 1) → K),
      qbil Q K (fun i => algebraMap F K (v₀ i)) x = 0 →
        Mb.map (algebraMap F K) *ᵥ (Nb.map (algebraMap F K) *ᵥ x) = x)
    (K : Type) [Field K] [Algebra F K] [CharZero K] (hiso : Q.IsotropicIn K) {lam a β : F}
    (hQv₀ : Q.evalIn F v₀ = lam ^ 2 * a) (hlam0 : lam ≠ 0) (hu : a ≠ 0) (hβ0 : β ≠ 0)
    {c : F} (hc_large : c = -(lam ^ 2 * a) * β ^ 2 * (1 - (lam * β)⁻¹ ^ 2))
    (hsq : IsSquare (algebraMap F K (1 - (lam * β)⁻¹ ^ 2))) (hRnd : (pullbackForm Q Mb).Nondegenerate) :
    (pullbackForm Q Mb).RepresentsIn K c := by
  set R := pullbackForm Q Mb
  have hRnd' : ∀ x : F, (algebraMap F K x = 0 ↔ x = 0) := fun x => map_eq_zero _
  obtain ⟨zq, hzq0, hzq⟩ := hiso
  set ιv := fun i => algebraMap F K (v₀ i)
  have hQιv : Q.evalIn K ιv = algebraMap F _ (lam ^ 2 * a) := by
    rw [show ιv = fun i => algebraMap F K (v₀ i) from rfl, evalIn_map_tower Q K (K := F), hQv₀]
  have hvv : qbil Q K ιv ιv ≠ 0 := by
    rw [qbil_self, hQιv]; exact mul_ne_zero two_ne_zero ((map_ne_zero _).mpr (mul_ne_zero
      (pow_ne_zero 2 hlam0) hu))
  set s0 := qbil Q K ιv zq / qbil Q K ιv ιv
  set x' := zq - s0 • ιv
  have hx' : qbil Q K ιv x' = 0 := by
    simp only [x']; rw [sub_eq_add_neg, ← neg_smul, qbil_add_right, qbil_smul_right]
    simp only [s0]; field_simp; ring
  set yq := Nb.map (algebraMap F K) *ᵥ x'
  have hMyq : Mb.map (algebraMap F K) *ᵥ yq = x' := hMN _ x' hx'
  have hRyq : R.evalIn K yq = Q.evalIn K x' := by
    rw [evalIn_pullback, hMyq]
  have hdecomp : Q.evalIn K zq = Q.evalIn K x' + s0 ^ 2 * algebraMap F _ (lam ^ 2 * a) := by
    have e : zq = x' + s0 • ιv := by simp only [x']; abel
    rw [e, evalIn_add_smul, qbil_comm, hx', mul_zero, add_zero, hQιv]
  by_cases hs0 : s0 = 0
  · apply representsIn_of_isotropicIn R _ hRnd
    refine ⟨yq, fun h0 => hzq0 ?_, ?_⟩
    · have : x' = 0 := by rw [← hMyq, h0, mulVec_zero]
      simpa [x', hs0] using this
    · rw [hRyq]; rw [hdecomp, hs0] at hzq; simpa using hzq
  · have hRyq' : R.evalIn K yq = -(s0 ^ 2 * algebraMap F _ (lam ^ 2 * a)) := by
      rw [hRyq]; linear_combination hdecomp.symm.trans hzq
    have hRyq0 : R.evalIn K yq ≠ 0 := by
      rw [hRyq']; exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hs0) ((map_ne_zero _).mpr
        (mul_ne_zero (pow_ne_zero 2 hlam0) hu)))
    refine representsIn_of_mul_isSquare R _ hRyq0 ?_
    obtain ⟨X, hX⟩ := hsq
    refine ⟨s0 * algebraMap F _ (lam ^ 2 * a * β) * X, ?_⟩
    rw [hRyq', hc_large]
    simp only [map_mul, map_neg, map_pow] at hX ⊢
    rw [hX]; ring

set_option maxHeartbeats 1600000 in
/-- **The core of O'Meara 104:3 with the free place a finite prime $\mathfrak p$** (after the reductions): $T \ne \emptyset$,
$\mathfrak p \notin T$, and $T \cup \{\mathfrak p\}$ contains every bad prime; no integrality is asked at $\mathfrak p$. -/
@[kb "omeara1963" "§104, proof of 104:3, step 4, pp. 314–315"]
theorem vecApprox_core_at (Q : QuadForm F (m + 1)) (hQ : Q.Nondegenerate) (hm : 3 ≤ m) (p : HeightOneSpectrum (𝓞 F))
    (hp : Q.IsotropicIn (p.adicCompletion F)) {Q₀ : QuadForm (𝓞 F) (m + 1)} {k : 𝓞 F}
    (hQ₀ : Q₀.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F k) • Q)
    {u : Fin (m + 1) → F} (hu : Q.evalIn F u ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T.Nonempty) (hpT : p ∉ T)
    (hgood : ∀ v ∉ T, v ≠ p → (2 : 𝓞 F) ∉ v.asIdeal ∧ k ∉ v.asIdeal ∧ Q₀.hessian.det ∉ v.asIdeal ∧
      Valued.v (algebraMap F (v.adicCompletion F) (Q.evalIn F u)) = 1)
    (z : ∀ v : HeightOneSpectrum (𝓞 F), Fin (m + 1) → v.adicCompletion F)
    (hz : ∀ v ∈ T, Q.evalIn _ (z v) = algebraMap F _ (Q.evalIn F u)) (r : HeightOneSpectrum (𝓞 F) → ℤ) :
    ∃ y : Fin (m + 1) → F, Q.evalIn F y = Q.evalIn F u ∧ (∀ v ∈ T, locVec v y - z v ∈ ball v (r v)) ∧
      ∀ v ∉ T, v ≠ p → locVec v y ∈ std v := by
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
  set T₁ := (Filter.eventually_cofinite.mp (eventually_valuation_eq_one hlam0)).toFinset.filter
    (fun v => v ∉ T ∧ v ≠ p)
  have hT₁ : ∀ v, v ∈ T₁ ↔ (v ∉ T ∧ v ≠ p) ∧ v.valuation F lam ≠ 1 := by
    intro v; simp [T₁, and_comm]
  have himp : ∀ v ∈ T₁, ∃ e : Fin m → v.adicCompletion F, R.evalIn _ e ≠ 0 ∧
      locAct v ((symm R (v.adicCompletion F) e : orthGroup R _) : GL (Fin m) _) (loc v K'.1) = loc v K'.1 := by
    intro v hv
    have hvT := ((hT₁ v).mp hv).1.1
    obtain ⟨h2, hk, hdet, -⟩ := hgood v hvT ((hT₁ v).mp hv).1.2
    obtain ⟨e, he, he1⟩ := exists_rep_perp_lattice v hQ₀ h2 hk hdet hm (hMN _) (hv₀std v hvT) (hv₀0 v)
      (hK'out v hvT) (c := 1) (Or.inl (map_one _))
    exact ⟨e, by rw [he1]; exact one_ne_zero, symm_stab_perp_lattice v hQ₀ hk (hK'out v hvT) he he1⟩
  obtain ⟨μ, hμ0, hμT₁, hμrep⟩ := exists_scale_represents_away R hRnd K' T₁ himp
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
    (fun v => v ∉ T ∧ v ∉ T₁ ∧ v ≠ p)
  have hT₂ : ∀ v, v ∈ T₂ ↔ (v ∉ T ∧ v ∉ T₁ ∧ v ≠ p) ∧ v.valuation F μ ≠ 1 := by
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
  set S : Finset (InfinitePlace F) := Finset.univ.filter fun w =>
    ∃ y : Fin m → w.Completion, R.evalIn _ y ≠ 0 ∧ IsSquare (R.evalIn _ y * algebraMap F _ a)
  have hpT' : p ∉ T ∪ T₁ ∪ T₂ := by
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨hpT, fun h => ((hT₁ p).mp h).1.2 rfl⟩, fun h => ((hT₂ p).mp h).1.2.2 rfl⟩
  have hlamp0 : algebraMap F (p.adicCompletion F) lam ≠ 0 := (map_ne_zero _).mpr hlam0
  obtain ⟨klp, hklp⟩ := exists_valued_eq_exp p hlamp0
  have h4p : (4 : p.adicCompletion F) ≠ 0 := by
    have := (algebraMap F (p.adicCompletion F)).injective.ne (by norm_num : (4 : F) ≠ 0)
    rwa [map_ofNat, map_zero] at this
  obtain ⟨k4p, hk4p⟩ := exists_valued_eq_exp p h4p
  set Λ : ℝ := ∑ w : InfinitePlace F, w lam
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  have hwlam : ∀ w : InfinitePlace F, 0 < w lam := fun w => AbsoluteValue.pos _ hlam0
  set δ : ℝ := 1 / (2 * (Λ + 1))
  have hδ : 0 < δ := by positivity
  set Rb : ℝ := ∑ w : InfinitePlace F, 2 / w lam
  obtain ⟨β, hβT, hβout, hβS, hβL, hβp⟩ := exists_very_strong_approx_at p (T ∪ T₁ ∪ T₂) hpT' bb OO hOO S hδ Rb
    (|k4p| + |klp| + 1)
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
  have hT₁T : ∀ v ∈ T₁, v ∉ T := fun v hv => ((hT₁ v).mp hv).1.1
  have hβT₁ : ∀ v ∈ T₁, Valued.v (algebraMap F (v.adicCompletion F) β) ≤ 1 := by
    intro v hv
    have := hβT v (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
    simpa [OO, hT₁T v hv, hv] using this
  have hβT₂ : ∀ v ∈ T₂, Valued.v (algebraMap F (v.adicCompletion F) β - (algebraMap F _ lam)⁻¹) ≤ exp (-j v) := by
    intro v hv
    have h := (hT₂ v).mp hv
    have := hβT v (Finset.mem_union_right _ hv)
    simpa [OO, h.1.1, h.1.2.1] using this
  have hlamval : ∀ v, v ∉ T → v ≠ p → v ∉ T₁ → Valued.v (algebraMap F (v.adicCompletion F) lam) = 1 := by
    intro v hv hvp hv1
    rw [valued_algebraMap]
    by_contra h; exact hv1 ((hT₁ v).mpr ⟨⟨hv, hvp⟩, h⟩)
  have hμval : ∀ v, v ∉ T → v ≠ p → v ∉ T₁ → v ∉ T₂ → Valued.v (algebraMap F (v.adicCompletion F) μ) = 1 := by
    intro v hv hvp hv1 hv2
    rw [valued_algebraMap]
    by_contra h; exact hv2 ((hT₂ v).mpr ⟨⟨hv, hv1, hvp⟩, h⟩)
  have hβint : ∀ v ∉ T, v ≠ p → Valued.v (algebraMap F (v.adicCompletion F) β) ≤ 1 := by
    intro v hv hvp
    by_cases h1 : v ∈ T₁
    · exact hβT₁ v h1
    by_cases h2 : v ∈ T₂
    · have hl := hlamval v hv hvp h1
      have hli : Valued.v ((algebraMap F (v.adicCompletion F) lam)⁻¹) = 1 := by rw [map_inv₀, hl, inv_one]
      have e : algebraMap F (v.adicCompletion F) β =
          (algebraMap F _ β - (algebraMap F _ lam)⁻¹) + (algebraMap F _ lam)⁻¹ := by ring
      rw [e]
      refine (Valuation.map_add _ _ _).trans (max_le ((hβT₂ v h2).trans ?_) hli.le)
      rw [← exp_zero, exp_le_exp]; simp only [j]; have := abs_nonneg (kμ v); linarith
    · exact hβout v (by simp [hv, h1, h2]) hvp
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
  have hloc : ∀ v ∉ ({p} : Finset (HeightOneSpectrum (𝓞 F))), ∃ y ∈ loc v K'.1,
      R.evalIn (v.adicCompletion F) y = algebraMap F _ (c / μ ^ 2) := by
    intro v hvp
    rw [Finset.mem_singleton] at hvp
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
    obtain ⟨h2, hk, hdet, hav⟩ := hgood v hvT hvp
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
    · have hl1 := hlamval v hvT hvp hv1
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
          rw [map_mul, hl1, one_mul]; exact hβint v hvT hvp
        rw [e, map_mul, map_mul, Valuation.map_neg, hl1, one_mul, hkμ v, div_le_one₀ (pow_pos exp_pos 2)]
        calc Valued.v (algebraMap F (v.adicCompletion F) β - (algebraMap F _ lam)⁻¹) *
              Valued.v (1 + algebraMap F _ lam * algebraMap F _ β)
            ≤ exp (-j v) * 1 := mul_le_mul' (hβT₂ v hv2) h1
          _ ≤ exp (kμ v) ^ 2 := by
            rw [mul_one, sq, ← exp_add, exp_le_exp]; simp only [j]; have := neg_abs_le (kμ v); linarith
      · rw [hμval v hvT hvp hv1 hv2, one_pow, div_one]
        refine (Valuation.map_sub _ _ _).trans (max_le (by rw [map_one]) ?_)
        rw [map_mul, map_pow, map_pow, hl1, one_pow, one_mul]
        exact pow_le_one₀ zero_le (hβint v hvT hvp)
  -- global representation of `c` by `U` (Hasse–Minkowski)
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hβp
    exact not_lt.mpr zero_le hβp
  have hlb0 : lam * β ≠ 0 := mul_ne_zero hlam0 hβ0
  have hc_large : c = -(lam ^ 2 * a) * β ^ 2 * (1 - (lam * β)⁻¹ ^ 2) := by
    simp only [c]; field_simp; ring
  have hrepF : R.RepresentsIn F c := by
    rw [represents_iff_everywhere_nf R hRnd c hc0]
    intro place
    cases place with
    | finite v =>
      change R.RepresentsIn (v.adicCompletion F) c
      by_cases hvp : v = p
      · subst hvp
        refine representsIn_of_isotropic_perp Q hMN (v.adicCompletion F) hp hQv₀ hlam0 hu hβ0 hc_large ?_ hRnd
        refine HN.isSquare_of_valued_sub_one_lt v _ ?_
        have e : algebraMap F (v.adicCompletion F) (1 - (lam * β)⁻¹ ^ 2) - 1 =
            -((algebraMap F (v.adicCompletion F) lam * algebraMap F _ β)⁻¹ * (algebraMap F _ lam * algebraMap F _ β)⁻¹) := by
          simp only [map_sub, map_one, map_pow, map_inv₀, map_mul]; ring
        have hb := hβp
        obtain ⟨kb, hkb⟩ := exists_valued_eq_exp v ((map_ne_zero (algebraMap F (v.adicCompletion F))).mpr hβ0)
        rw [hkb, exp_lt_exp] at hb
        rw [e, Valuation.map_neg, Valuation.map_mul, Valuation.map_inv, Valuation.map_mul, hklp, hkb, hk4p,
          ← exp_add, ← WithZero.exp_neg, ← exp_add, exp_lt_exp]
        have := neg_abs_le k4p; have := abs_nonneg klp; have := neg_abs_le klp; have := abs_nonneg k4p
        linarith
      obtain ⟨y, -, hy⟩ := hloc v (by simpa using hvp)
      refine ⟨algebraMap F (v.adicCompletion F) μ • y, ?_⟩
      rw [evalIn_smul_sq, hy, map_div₀, map_pow]
      have := hμv0 v
      field_simp
    | infinite w =>
      change R.RepresentsIn w.Completion c
      have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
      have hι : ∀ x : F, (algebraMap F w.Completion x = 0 ↔ x = 0) := fun x => map_eq_zero _
      by_cases hwS : w ∈ S
      · obtain ⟨y, hy0, hsq⟩ := (Finset.mem_filter.mp hwS).2
        refine representsIn_of_mul_isSquare R _ hy0 ?_
        have h1 := isSquare_one_sub_of_lt w (hsmall w hwS)
        have e : algebraMap F w.Completion c * R.evalIn _ y =
            algebraMap F _ (1 - lam ^ 2 * β ^ 2) * (R.evalIn _ y * algebraMap F _ a) := by
          simp only [c, map_mul]; ring
        rw [e]; exact h1.mul hsq
      · have hnot : ∀ y : Fin m → w.Completion, R.evalIn _ y ≠ 0 → ¬ IsSquare (R.evalIn _ y * algebraMap F _ a) :=
          fun y hy hsq => hwS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, hsq⟩)
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
  obtain ⟨t, htc, htK'⟩ := hμrep {p} c hc0 hrepF hloc
  have htK : ∀ v, v ≠ p → locVec v t ∈ loc v K'.1 := fun v hvp => htK' v (by simpa using hvp)
  have hidM : Mb.map (algebraMap F F) = Mb := by ext i j; simp
  have hRt : Q.evalIn F (Mb *ᵥ t) = c := by
    rw [← htc, evalIn_pullback, hidM]
  have hperpF : qbil Q F (Mb *ᵥ t) v₀ = 0 := by
    have := hperp F t
    rw [hidM, show (fun i => algebraMap F F (v₀ i)) = v₀ by funext i; simp] at this
    rw [qbil_comm]; exact this
  refine ⟨Mb *ᵥ t + β • v₀, ?_, fun v hv => ?_, fun v hv hvp => ?_⟩
  · rw [evalIn_add_smul, hRt, hperpF, mul_zero, add_zero, hQv₀]
    simp only [c]; ring
  · have hlt : locVec v (Mb *ᵥ t) ∈ ball v (r v) := by
      rw [locVec_mulVec_rect]; exact (hK'T v hv _).mp (htK v (fun h => hpT (h ▸ hv)))
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
    exact Submodule.add_mem _ ((hK'out v hv _).mp (htK v hvp))
      (smul_mem_of_valued_le (hβint v hv hvp) (hv₀std v hv))


/-! ### `VecApprox` away from a prime -/

/-- **Strong approximation for vectors of a given norm away from a prime $\mathfrak p$** (O'Meara 1973, 104:3 with
$S$ = all finite primes except $\mathfrak p$): `VecApprox Q` with no condition at $\mathfrak p$. -/
def VecApproxAt {n : ℕ} (Q : QuadForm F n) (p : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ u : Fin n → F, Q.evalIn F u ≠ 0 → ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
    (∀ v ∉ T, v ≠ p → locVec v u ∈ std v) →
    ∀ z : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F,
      (∀ v ∈ T, Q.evalIn (v.adicCompletion F) (z v) = algebraMap F (v.adicCompletion F) (Q.evalIn F u)) →
    ∀ Z : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → v.adicCompletion F), (∀ v ∈ T, Z v ∈ 𝓝 (z v)) →
      ∃ y : Fin n → F, Q.evalIn F y = Q.evalIn F u ∧ (∀ v ∈ T, v ≠ p → locVec v y ∈ Z v) ∧
        ∀ v ∉ T, v ≠ p → locVec v y ∈ std v

/-- **O'Meara 1973, 104:3 away from a prime $\mathfrak p$ at which $V$ is isotropic**: `VecApproxAt Q p` for every
nondegenerate $Q$ in $n \ge 4$ variables with $V_\mathfrak p$ isotropic (no condition at the infinite places). -/
@[kb "omeara1963" "§104, 104:3, pp. 311–315 (S = finite primes except 𝔭); cassels1978 Ch. 11, Thm. 8.1, p. 231"]
theorem vecApproxAt_of_isotropicAt (Q : QuadForm F (m + 1)) (hm : 3 ≤ m) (hQ : Q.Nondegenerate)
    (p : HeightOneSpectrum (𝓞 F)) (hp : Q.IsotropicIn (p.adicCompletion F)) : VecApproxAt Q p := by
  classical
  intro u hu T hT z hz Z hZ
  set T₀ := T.erase p
  rcases T₀.eq_empty_or_nonempty with hTe | hTne
  · refine ⟨u, rfl, fun v hv hvp => ?_, fun v hv hvp => hT v hv hvp⟩
    have : v ∈ T₀ := Finset.mem_erase.mpr ⟨hvp, hv⟩
    rw [hTe] at this; exact absurd this (Finset.notMem_empty v)
  obtain ⟨Q₀, k, hk0, hQ₀⟩ := exists_integral_model Q
  have hdet0 := det_model_ne_zero hk0 hQ₀ hQ
  set a := Q.evalIn F u
  have hbad : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (2 : 𝓞 F) ∉ v.asIdeal ∧ k ∉ v.asIdeal ∧
      Q₀.hessian.det ∉ v.asIdeal ∧ Valued.v (algebraMap F (v.adicCompletion F) a) = 1 := by
    filter_upwards [eventually_not_mem (two_ne_zero : (2 : 𝓞 F) ≠ 0), eventually_not_mem hk0,
      eventually_not_mem hdet0, eventually_valuation_eq_one hu] with v h1 h2 h3 h4
    exact ⟨h1, h2, h3, by rw [valued_algebraMap]; exact h4⟩
  set Bad := ((Filter.eventually_cofinite.mp hbad).toFinset).erase p
  have hBad : ∀ v, v ∉ Bad → v ≠ p → (2 : 𝓞 F) ∉ v.asIdeal ∧ k ∉ v.asIdeal ∧ Q₀.hessian.det ∉ v.asIdeal ∧
      Valued.v (algebraMap F (v.adicCompletion F) a) = 1 := by
    intro v hv hvp; by_contra hc
    exact hv (Finset.mem_erase.mpr ⟨hvp, (Filter.eventually_cofinite.mp hbad).mem_toFinset.mpr hc⟩)
  choose! r hr using fun v (hv : v ∈ T) => exists_ball_of_mem_nhds v (hZ v hv)
  set T' := T₀ ∪ Bad
  have hpT' : p ∉ T' := by
    simp only [T', Finset.mem_union, not_or, T₀, Bad, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      not_false_eq_true, and_self]
  obtain ⟨y, hya, hyT, hyout⟩ := vecApprox_core_at Q hQ hm p hp hQ₀ hu T'
    (hTne.mono Finset.subset_union_left) hpT'
    (fun v hv hvp => hBad v (fun h => hv (Finset.mem_union_right _ h)) hvp)
    (fun v => if v ∈ T then z v else locVec v u)
    (fun v _ => by
      split_ifs with h
      · exact hz v h
      · rw [evalIn_locVec])
    (fun v => if v ∈ T then r v else 0)
  refine ⟨y, hya, fun v hv hvp => ?_, fun v hv hvp => ?_⟩
  · have := hyT v (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvp, hv⟩))
    simp only [hv, ite_true] at this
    exact hr v hv _ this
  · by_cases hvB : v ∈ Bad
    · have := hyT v (Finset.mem_union_right _ hvB)
      simp only [hv, ite_false] at this
      have h := Submodule.add_mem _ this (hT v hv hvp)
      rwa [sub_add_cancel] at h
    · refine hyout v ?_ hvp
      simp only [T', Finset.mem_union, not_or, T₀, Finset.mem_erase]
      exact ⟨fun h => hv h.2, hvB⟩

end QuadFormsKB.Lattices
