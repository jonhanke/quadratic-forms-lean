/-
# O'Meara §106B: membership in $\mathcal G(L)$ by invariant factors

**Layer:** $V = \mathbb Q^n$ with a quadratic form `Q : QuadForm ℚ n`; lattices are $\mathbb Z$-lattices
(`Lat ℚ n`, $\mathcal O_{\mathbb Q} = \mathbb Z$); $K_p$ = `loc v K` at the finite spot $v$ of the odd prime $p$;
$\mathcal G(L)$ = `omearaG Q L` (`Sec106Defs.lean`): the unimodular $K$ with $K_p = L_p$ at every odd prime $p$.

**Proves** (O'Meara 1973, §106B, pp. 325–326, the remark before the definition of adjacency, row 106.r18)
* `omearaG_iff_pow`: for lattices $K$, $L$: $K_p = L_p$ at every odd $p$ iff $2^kL \subseteq K$ and $2^kK \subseteq L$
  for some $k \ge 0$.
* `omeara106_r18`: for unimodular $K$, $L$ on $V$: $K \in \mathcal G(L)$ iff the invariant factors of $K$ in $L$ are of
  the form $2^{r_0}\mathbb Z, \dots, 2^{r_{n-1}}\mathbb Z$, i.e. iff there is a base $y_0, \dots, y_{n-1}$ of $V$ with
  $L = \sum_i \mathbb Zy_i$ and $K = \sum_i \mathbb Z2^{r_i}y_i$ ($r_i \in \mathbb Z$). The invariant factors are those of
  any such adapted base (uniqueness in 81:11, `OMeara.invariant_factors_unique`); the form with an adapted base is the
  one used for 106.r22 (`omeara106_r22`) and comes from `exists_adapted_basis_pid`.

*Convention:* 0-based indices: O'Meara's $r_1, \dots, r_n$ are `r 0, …, r (n-1)`. His parenthetical "with $r_1 \le 0$
and $r_n \ge 0$" (for the ordered factors) is a consequence (both lattices have volume $\mathbb Z$, so $\sum r_i = 0$)
and is not part of the statement here; the factors are not ordered.
-/
import QuadFormsKB.Literature.OMeara.Sec106Facts

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- At a spot $v$ where $m \in \mathcal O_F$ is a unit, $m x \in M$ gives $x \in M_v$. -/
theorem locVec_mem_loc_of_unit_smul {F : Type*} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
    {m : 𝓞 F} (hm : m ∉ v.asIdeal) {M : Submodule (𝓞 F) (Fin n → F)} {x : Fin n → F} (h : m • x ∈ M) :
    locVec v x ∈ loc v M := by
  have h1 : locVec v (m • x) ∈ loc v M := locVec_mem_loc v h
  have hv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) m) = 1 := by
    rw [valued_algebraMap_int v m]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hm
  have hne : algebraMap (𝓞 F) (v.adicCompletion F) m ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have ht : Valued.v ((algebraMap (𝓞 F) (v.adicCompletion F) m)⁻¹) ≤ 1 := by
    rw [map_inv₀, hv]; simp
  have e : locVec v x = (toO v _ ht) • locVec v (m • x) := by
    funext i
    rw [locVec_smul_int]
    change locVec v x i = ((toO v _ ht : v.adicCompletionIntegers F) : v.adicCompletion F) *
      (((algebraMap (𝓞 F) (v.adicCompletionIntegers F) m : v.adicCompletionIntegers F) :
        v.adicCompletion F) * locVec v x i)
    rw [← mul_assoc, algebraMap_int_coe]
    change locVec v x i = (algebraMap (𝓞 F) (v.adicCompletion F) m)⁻¹ *
      (algebraMap (𝓞 F) (v.adicCompletion F) m) * locVec v x i
    rw [inv_mul_cancel₀ hne, one_mul]
  rw [e]
  exact (loc v M).smul_mem _ h1

variable {n : ℕ}

theorem two_pow_notMem {v : HeightOneSpectrum (𝓞 ℚ)} (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) (k : ℕ) :
    (2 : 𝓞 ℚ) ^ k ∉ v.asIdeal := fun h => hv (v.isPrime.mem_of_pow_mem k h)

/-- **$K_p = L_p$ at every odd $p$ iff $2^kL \subseteq K$ and $2^kK \subseteq L$ for some $k$** (lattices on
$\mathbb Q^n$). -/
theorem omearaG_iff_pow {K L : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hK : K.IsLattice ℚ) (hL : L.IsLattice ℚ) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → loc v K = loc v L) ↔
      ∃ k : ℕ, (∀ x ∈ L, (2 : 𝓞 ℚ) ^ k • x ∈ K) ∧ ∀ x ∈ K, (2 : 𝓞 ℚ) ^ k • x ∈ L := by
  constructor
  · intro hKL
    -- one direction at a time, then take the larger exponent
    have one : ∀ {A B : Submodule (𝓞 ℚ) (Fin n → ℚ)}, A.IsLattice ℚ → B.IsLattice ℚ →
        (∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → loc v A = loc v B) →
        ∃ a : ℕ, ∀ x ∈ A, (2 : 𝓞 ℚ) ^ a • x ∈ B := by
      intro A B hA hB hAB
      obtain ⟨dA, hdA0, -, hdA⟩ := exists_global_bounds hA
      obtain ⟨dB, hdB0, hdB, -⟩ := exists_global_bounds hB
      set D : 𝓞 ℚ := dB * dA with hD
      have hDx : ∀ x ∈ A, D • x ∈ B := fun x hx => by rw [hD, mul_smul]; exact hdB _ (hdA x hx)
      have hD0 : D ≠ 0 := mul_ne_zero hdB0 hdA0
      set N : ℕ := (Rat.ringOfIntegersEquiv D).natAbs with hN
      have hN0 : N ≠ 0 := by
        rw [hN, Int.natAbs_ne_zero]
        exact (map_ne_zero_iff _ Rat.ringOfIntegersEquiv.injective).mpr hD0
      obtain ⟨a, m, hm, hNm⟩ := Nat.exists_eq_two_pow_mul_odd hN0
      have hNx : ∀ x ∈ A, (N : 𝓞 ℚ) • x ∈ B := by
        intro x hx
        rcases Int.natAbs_eq (Rat.ringOfIntegersEquiv D) with h | h
        · have : (N : 𝓞 ℚ) = D := by
            apply Rat.ringOfIntegersEquiv.injective
            rw [map_natCast]; exact h.symm
          rw [this]; exact hDx x hx
        · have : (N : 𝓞 ℚ) = -D := by
            apply Rat.ringOfIntegersEquiv.injective
            rw [map_natCast, map_neg, h, neg_neg]
          rw [this, neg_smul]; exact B.neg_mem (hDx x hx)
      refine ⟨a, fun x hx => ?_⟩
      rw [mem_iff_forall_loc hB]
      intro v
      by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
      · have hmv : (m : 𝓞 ℚ) ∉ v.asIdeal := by
          intro hmv
          obtain ⟨k, hk⟩ := hm
          have e : (1 : 𝓞 ℚ) = (m : 𝓞 ℚ) - 2 * (k : 𝓞 ℚ) := by rw [hk]; push_cast; ring
          exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
            (e ▸ v.asIdeal.sub_mem hmv (Ideal.mul_mem_right _ _ h2)))
        refine locVec_mem_loc_of_unit_smul v hmv ?_
        rw [smul_smul, mul_comm, ← Nat.cast_ofNat, ← Nat.cast_pow, ← Nat.cast_mul, ← hNm]
        exact hNx x hx
      · rw [← hAB v h2]
        exact locVec_mem_loc v (A.smul_mem _ hx)
    obtain ⟨a, ha⟩ := one hK hL hKL
    obtain ⟨b, hb⟩ := one hL hK fun v hv => (hKL v hv).symm
    refine ⟨a + b, fun x hx => ?_, fun x hx => ?_⟩
    · rw [pow_add, mul_smul]; exact K.smul_mem _ (hb x hx)
    · rw [pow_add, mul_comm, mul_smul]; exact L.smul_mem _ (ha x hx)
  · rintro ⟨k, h1, h2⟩ v hv
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact locVec_mem_loc_of_unit_smul v (two_pow_notMem hv k) (h2 x hx)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact locVec_mem_loc_of_unit_smul v (two_pow_notMem hv k) (h1 x hx)

/-- $(2 : \mathbb Z)^m$ acts on $\mathbb Q^n$ as $(2 : \mathbb Q)^m$. -/
theorem two_pow_smul_eq (m : ℕ) (x : Fin n → ℚ) : ((2 : 𝓞 ℚ) ^ m) • x = ((2 : ℚ) ^ m) • x := by
  rw [← algebraMap_smul ℚ ((2 : 𝓞 ℚ) ^ m) x, map_pow, map_ofNat]

/-- The $y$-coordinates of an element of $\sum_j \mathbb Z f_jy_j$: the $i$-th is an integer multiple of $f_i$. -/
theorem repr_mem_of_mem_span (y : Module.Basis (Fin n) ℚ (Fin n → ℚ)) (f : Fin n → ℚ) {z : Fin n → ℚ}
    (hz : z ∈ Submodule.span (𝓞 ℚ) (Set.range fun i => f i • y i)) (i : Fin n) :
    ∃ c : ℤ, y.repr z i = c * f i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 ℚ)).mp hz
  refine ⟨Rat.ringOfIntegersEquiv (c i), ?_⟩
  have e : ∑ j, c j • (f j • y j) = ∑ j, (algebraMap (𝓞 ℚ) ℚ (c j) * f j) • y j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul ℚ (c j), smul_smul]
  rw [e, y.repr_sum_self, Rat.ringOfIntegersEquiv_apply_coe]

/-- If $C\varphi = 2^k$ and $2^k\varphi = C'$ with $C, C' \in \mathbb Z$, then $\varphi = \pm 2^r$. -/
theorem eq_pm_two_zpow {φ : ℚ} {k : ℕ} {C C' : ℤ} (h1 : (C : ℚ) * φ = 2 ^ k) (h2 : (2 : ℚ) ^ k * φ = C') :
    ∃ r : ℤ, φ = 2 ^ r ∨ φ = -2 ^ r := by
  have hCC : C * C' = 2 ^ (2 * k) := by
    have : (C : ℚ) * C' = 2 ^ (2 * k) := by
      rw [← h2, pow_mul', sq, ← h1]; ring
    exact_mod_cast this
  have hdvd : C'.natAbs ∣ 2 ^ (2 * k) := ⟨C.natAbs, by rw [← Int.natAbs_mul, Int.mul_comm C' C, hCC, Int.natAbs_pow]; rfl⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hφ : φ = (C' : ℚ) / 2 ^ k := by rw [← h2]; field_simp
  refine ⟨(j : ℤ) - k, ?_⟩
  have e : (2 : ℚ) ^ ((j : ℤ) - k) = 2 ^ j / 2 ^ k := by
    rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
  rw [e, hφ]
  rcases Int.natAbs_eq C' with h | h
  · left; rw [h, hj]; push_cast; ring
  · right; rw [h, hj]; push_cast; ring

variable (Q : QuadForm ℚ n)

attribute [kb "omeara1963" "§106, p. 324 (a unimodular lattice over ℤ has discriminant ±1: its volume is ℤ)"]
  volume_eq_one_of_unimodular

/-- **106.r18** (O'Meara 1973, §106B, pp. 325–326): for unimodular lattices $K$ and $L$ on $V$, $K \in \mathcal G(L)$
if and only if the invariant factors of $K$ in $L$ are of the form $2^{r_0}\mathbb Z, \dots, 2^{r_{n-1}}\mathbb Z$: there
is a base $y_0, \dots, y_{n-1}$ of $V$ and integers $r_i$ with $L = \sum_i\mathbb Zy_i$ and
$K = \sum_i\mathbb Z\,2^{r_i}y_i$. Proof: $K \in \mathcal G(L)$ iff $2^kL \subseteq K$ and $2^kK \subseteq L$ for some
$k$ (`omearaG_iff_pow`); in an adapted base (`exists_adapted_basis_pid`, 81:11 over $\mathbb Z$) with
$K = \sum\mathbb Z\varphi_iy_i$ this forces $\varphi_i = \pm2^{r_i}$, and the signs are absorbed into $y_i$. -/
@[kb "omeara1963" "§106B, pp. 325–326 (K ∈ 𝔊(L) iff the invariant factors of K in L are 2^{r₁}Z, …, 2^{rₙ}Z)"]
theorem omeara106_r18 {K L : Lat ℚ n} (hK : IsUnimodularZ Q K.1) (_hL : IsUnimodularZ Q L.1) :
    K ∈ omearaG Q L ↔ ∃ (y : Fin n → Fin n → ℚ) (r : Fin n → ℤ), LinearIndependent ℚ y ∧
      L.1 = Submodule.span (𝓞 ℚ) (Set.range y) ∧
      K.1 = Submodule.span (𝓞 ℚ) (Set.range fun i => (2 : ℚ) ^ (r i) • y i) := by
  constructor
  · rintro ⟨-, hloc⟩
    obtain ⟨k, h1, h2⟩ := (omearaG_iff_pow K.2 L.2).mp hloc
    obtain ⟨y, φ, hφ0, -, hLy, hKy⟩ := exists_adapted_basis_pid L.2 K.2
    have hL1 : L.1 = Submodule.span (𝓞 ℚ) (Set.range fun i => (1 : ℚ) • y i) := by simpa using hLy
    have hr : ∀ i, ∃ r : ℤ, φ i = 2 ^ r ∨ φ i = -2 ^ r := by
      intro i
      have hyL : y i ∈ L.1 := hLy ▸ Submodule.subset_span ⟨i, rfl⟩
      have hyK : φ i • y i ∈ K.1 := hKy ▸ Submodule.subset_span ⟨i, rfl⟩
      have a1 := h1 _ hyL
      rw [hKy, two_pow_smul_eq] at a1
      obtain ⟨C, hC⟩ := repr_mem_of_mem_span y φ a1 i
      have a2 := h2 _ hyK
      rw [hL1, two_pow_smul_eq, smul_smul] at a2
      obtain ⟨C', hC'⟩ := repr_mem_of_mem_span y _ a2 i
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
        mul_one] at hC hC'
      exact eq_pm_two_zpow hC.symm hC'
    choose r hr using hr
    let w : Fin n → ℚ := fun i => if φ i = 2 ^ (r i) then 1 else -1
    have hw : ∀ i, φ i = 2 ^ (r i) * w i := by
      intro i
      by_cases h : φ i = 2 ^ (r i)
      · simp [w, h]
      · simp only [w, h, ↓reduceIte, mul_neg, mul_one]
        exact (hr i).resolve_left h
    have hw0 : ∀ i, w i ≠ 0 := fun i => by by_cases h : φ i = 2 ^ (r i) <;> simp [w, h]
    refine ⟨fun i => w i • y i, r, ?_, ?_, ?_⟩
    · have := y.linearIndependent.units_smul fun i => Units.mk0 (w i) (hw0 i)
      convert this using 1
      funext i
      simp [Units.smul_def]
    · rw [hLy]
      apply le_antisymm
      · refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => ?_)
        by_cases h : φ i = 2 ^ (r i)
        · exact Submodule.subset_span ⟨i, by simp [w, h]⟩
        · have : y i = -(w i • y i) := by simp [w, h]
          rw [this]
          exact Submodule.neg_mem _ (Submodule.subset_span ⟨i, rfl⟩)
      · refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => ?_)
        by_cases h : φ i = 2 ^ (r i)
        · exact Submodule.subset_span ⟨i, by simp [w, h]⟩
        · have : w i • y i = -y i := by simp [w, h]
          rw [this]
          exact Submodule.neg_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [hKy]
      congr 2
      funext i
      rw [smul_smul, ← hw]
  · rintro ⟨y, r, -, hLy, hKy⟩
    refine ⟨hK, (omearaG_iff_pow K.2 L.2).mpr ⟨∑ i, (r i).natAbs, fun x hx => ?_, fun x hx => ?_⟩⟩
    · have hle : ∀ i, (r i).natAbs ≤ ∑ j, (r j).natAbs := fun i =>
        Finset.single_le_sum (f := fun j => (r j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [hLy] at hx
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        have hm : 0 ≤ ((∑ j, (r j).natAbs : ℕ) : ℤ) - r i := by
          have := hle i; have := Int.le_natAbs (a := r i); omega
        obtain ⟨m, hm'⟩ := Int.eq_ofNat_of_zero_le hm
        have e : ((2 : 𝓞 ℚ) ^ (∑ j, (r j).natAbs)) • y i = ((2 : 𝓞 ℚ) ^ m) • ((2 : ℚ) ^ (r i) • y i) := by
          rw [two_pow_smul_eq, two_pow_smul_eq, smul_smul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero,
            ← hm']
          congr 1; ring_nf
        rw [e, hKy]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      | zero => simp
      | add a b _ _ ha hb => rw [smul_add]; exact K.1.add_mem ha hb
      | smul c a _ ha => rw [smul_comm]; exact K.1.smul_mem c ha
    · rw [hKy] at hx
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        have hm : 0 ≤ ((∑ j, (r j).natAbs : ℕ) : ℤ) + r i := by
          have := Finset.single_le_sum (f := fun j => (r j).natAbs) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
          have h3 := Int.le_natAbs (a := -(r i))
          rw [Int.natAbs_neg] at h3
          omega
        obtain ⟨m, hm'⟩ := Int.eq_ofNat_of_zero_le hm
        have e : ((2 : 𝓞 ℚ) ^ (∑ j, (r j).natAbs)) • ((2 : ℚ) ^ (r i) • y i) = ((2 : 𝓞 ℚ) ^ m) • y i := by
          rw [two_pow_smul_eq, two_pow_smul_eq, smul_smul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero,
            ← hm']
        rw [e, hLy]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      | zero => simp
      | add a b _ _ ha hb => rw [smul_add]; exact L.1.add_mem ha hb
      | smul c a _ ha => rw [smul_comm]; exact L.1.smul_mem c ha

end QuadFormsKB.Lattices
