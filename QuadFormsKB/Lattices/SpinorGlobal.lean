/-
# Global spinor norms and "genus = spinor genus"

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$ (`F : Type`), $Q$ nondegenerate; local spinor norms
and the local condition `LocalSpinorUnits` (`Lattices/SpinorLocal.lean`).

**Proves**
* `exists_evalIn_eq_mul` (**global spinor norms**): if $n \ge 3$ and $Q$ is isotropic at every infinite place of $F$, then
  for every $a \in F^\times$ there are anisotropic $x, y \in F^n$ with $Q(x) = a\,Q(y)$; hence
  $\theta(\tau_x\tau_y) = a\,F^{\times 2}$ and $\theta(O^+(V)) = F^\times/F^{\times2}$ (O'Meara 1963, 101:8 [unverified]).
  *Proof:* $\langle b\rangle \perp \langle -ab\rangle$ ($Q \cong \langle b_0, \dots, b_{n-1}\rangle$) has rank $2n \ge 6$, so it
  is isotropic at every finite place (`LocalRankFive.isotropic_diag_five`) and, containing $Q$, at every infinite
  place; by Hasse–Minkowski (`hasseMinkowski_nf`) it is isotropic over $F$. If the isotropic vector has $Q(y) = 0$, then
  $Q$ is isotropic, hence universal.
* `sameSpinorGenus_of_sameGenus` (**genus = spinor genus**): if moreover $\mathcal O_F$ is a PID and
  `LocalSpinorUnits Q v L` holds at every finite $\mathfrak p$, then every lattice in the genus of $L$ is in the spinor
  genus of $L$ (O'Meara 1963, 102:9 [unverified]; Cassels 1978, Ch. 11, Thm. 3.? [unverified]).
* `genus_eq_class_of_localSpinorUnits`: with Eichler's theorem (conditional on `StrongApproximationSpin F`), for
  $n \ge 3$ every lattice in the genus of $L$ is isometric to $L$: **class number one of the genus**.
-/
import QuadFormsKB.Lattices.SpinorLocal
import QuadFormsKB.Lattices.Eichler
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNFMain
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Literature.LocalGlobal.PadicClassification

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Global values: $Q(x) = a\,Q(y)$ -/

section Global

theorem evalIn_diag_append (K : Type*) [Field K] [Algebra F K] (b c : Fin n → F) (z : Fin (n + n) → K) :
    (QuadForm.diag (Fin.append b c)).evalIn K z =
      (QuadForm.diag b).evalIn K (fun i => z (Fin.castAdd n i)) +
        (QuadForm.diag c).evalIn K (fun i => z (Fin.natAdd n i)) := by
  rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag, QuadForm.evalIn_diag, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **Every nondegenerate diagonal form of rank $\ge 5$ over $F$ is isotropic at every finite place.** -/
theorem isotropicIn_diag_finite {m : ℕ} (hm : 5 ≤ m) (c : Fin m → F) (hc : ∀ i, c i ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) : (QuadForm.diag c).IsotropicIn (v.adicCompletion F) := by
  refine FieldGen.isotropicIn_diag_of_prefix _ 5 hm c ?_
  have h5 := LocalRankFive.isotropic_diag_five v (fun i : Fin 5 => algebraMap F (v.adicCompletion F)
    (c ⟨i, lt_of_lt_of_le i.2 hm⟩)) (fun i => (map_ne_zero _).mpr (hc _))
  obtain ⟨y, hy0, hy⟩ := h5
  refine ⟨y, hy0, ?_⟩
  rw [QuadForm.evalIn_diag]
  rw [QuadForm.evalIn_diag] at hy
  simpa using hy

/-- **Global values of an indefinite form** (O'Meara 1963, 101:8 [unverified]): if $Q$ is nondegenerate in $n \ge 3$
variables and isotropic at every infinite place of $F$, then for every $a \in F^\times$ there are $x, y \in F^n$ with
$Q(y) \ne 0$ and $Q(x) = a\,Q(y)$. -/
@[kb "omeara1963" "101:8 [unverified]"]
theorem exists_evalIn_eq_mul (Q : QuadForm F n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (hinf : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion) {a : F} (ha : a ≠ 0) :
    ∃ x y : Fin n → F, Q.evalIn F y ≠ 0 ∧ Q.evalIn F x = a * Q.evalIn F y := by
  obtain ⟨b, hb, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  obtain ⟨P, hPu, hP⟩ := hiso
  have hPF : ∀ x : Fin n → F, Q.evalIn F (P *ᵥ x) = ∑ i, b i * x i ^ 2 := fun x => by
    rw [hP, QuadForm.evalIn_diag]; simp
  set c : Fin (n + n) → F := Fin.append b fun i => -a * b i with hcdef
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [c, Fin.append_left]; exact hb j
    · simp only [c, Fin.append_right]; exact mul_ne_zero (neg_ne_zero.mpr ha) (hb j)
  have hD : (QuadForm.diag c).IsotropicIn F := by
    rw [hasseMinkowski_nf _ (QuadForm.nondegenerate_diag hc)]
    intro w
    cases w with
    | infinite w =>
      obtain ⟨y, hy0, hy⟩ := (FieldGen.isotropicIn_iff_of_isometricIn _
        (FieldGen.isometricIn_of_base _ ⟨P, hPu, hP⟩)).mp (hinf w)
      refine ⟨Fin.append y 0, fun h => hy0 (funext fun i => ?_), ?_⟩
      · simpa [Fin.append_left] using congrFun h (Fin.castAdd n i)
      · rw [evalIn_diag_append]
        simp only [Fin.append_left, Fin.append_right]
        rw [hy, zero_add, QuadForm.evalIn_diag]
        simp
    | finite v => exact isotropicIn_diag_finite (by omega) c hc v
  obtain ⟨z, hz0, hz⟩ := hD
  set x' : Fin n → F := fun i => z (Fin.castAdd n i)
  set y' : Fin n → F := fun i => z (Fin.natAdd n i)
  have hxy : Q.evalIn F (P *ᵥ x') = a * Q.evalIn F (P *ᵥ y') := by
    rw [evalIn_diag_append, QuadForm.evalIn_diag, QuadForm.evalIn_diag] at hz
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at hz
    rw [hPF, hPF, Finset.mul_sum]
    have : ∑ i, -a * b i * y' i ^ 2 = -∑ i, a * (b i * y' i ^ 2) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this] at hz
    linear_combination hz
  by_cases hy : Q.evalIn F (P *ᵥ y') = 0
  · -- `Q` is isotropic, hence universal
    have hxz : Q.evalIn F (P *ᵥ x') = 0 := by rw [hxy, hy, mul_zero]
    have hiso : (QuadForm.diag b).IsotropicIn F := by
      by_cases hx0 : x' = 0
      · refine ⟨y', fun h => hz0 (funext fun i => ?_), ?_⟩
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · exact congrFun hx0 j
          · exact congrFun h j
        · rw [← hP]; exact hy
      · exact ⟨x', hx0, by rw [← hP]; exact hxz⟩
    have hn0 : 0 < n := by omega
    obtain ⟨x'', hx''⟩ := PadicClass.representsIn_of_isotropic hb hiso (a * b ⟨0, hn0⟩)
    refine ⟨P *ᵥ x'', P *ᵥ Pi.single ⟨0, hn0⟩ 1, ?_, ?_⟩
    · rw [hPF]; simp [Pi.single_apply, hb]
    · rw [hP, hx'', hPF]; simp [Pi.single_apply]
  · exact ⟨P *ᵥ x', P *ᵥ y', hy, hxy⟩

end Global

/-! ### Valuations -/

section Valuation

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **Even valuation means unit square class:** if $v(z) = e^{2k}$ then $z \in \mathfrak o_\mathfrak p^\times F_\mathfrak p^{\times 2}$. -/
theorem isUnitSqClass_of_valued_eq (z : Fv) (k : ℤ) (hv : Valued.v z = exp (2 * k)) :
    IsUnitSqClass v (sqClassOf z) := by
  have hz : z ≠ 0 := fun h => by rw [h, map_zero] at hv; exact exp_ne_zero hv.symm
  have hϖ := ϖk_ne_zero v k
  refine ⟨z * ϖk v k ^ 2, ?_, ?_⟩
  · rw [map_mul, map_pow, hv, valued_ϖk, ← WithZero.exp_nsmul, ← exp_add]
    simp only [smul_neg, nsmul_eq_mul, Nat.cast_ofNat]
    rw [show 2 * k + -(2 * k) = 0 by ring, exp_zero]
  · rw [sqClassOf_mul hz (pow_ne_zero 2 hϖ), (sqClassOf_eq_one_iff (pow_ne_zero 2 hϖ)).mpr ⟨ϖk v k, sq _⟩,
      mul_one]

variable [IsPrincipalIdealRing (𝓞 F)]

/-- A generator of the prime ideal $\mathfrak p_w$ ($\mathcal O_F$ a PID). -/
def primeGen (w : HeightOneSpectrum (𝓞 F)) : 𝓞 F := Submodule.IsPrincipal.generator w.asIdeal

theorem primeGen_ne_zero (w : HeightOneSpectrum (𝓞 F)) : primeGen w ≠ 0 := by
  intro h
  apply w.ne_bot
  rw [← Submodule.IsPrincipal.span_singleton_generator w.asIdeal]
  change Ideal.span {primeGen w} = ⊥
  rw [h, Ideal.span_singleton_eq_bot]

theorem intValuation_primeGen_self : v.intValuation (primeGen v) = exp (-1 : ℤ) :=
  v.intValuation_singleton (primeGen_ne_zero v)
    (Submodule.IsPrincipal.span_singleton_generator v.asIdeal).symm

theorem intValuation_primeGen_of_ne {w : HeightOneSpectrum (𝓞 F)} (hvw : v ≠ w) :
    v.intValuation (primeGen w) = 1 := by
  have hspan : w.asIdeal = Ideal.span {primeGen w} :=
    (Submodule.IsPrincipal.span_singleton_generator w.asIdeal).symm
  rw [HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  apply hvw
  have hle : w.asIdeal ≤ v.asIdeal := by
    rw [hspan, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  exact HeightOneSpectrum.ext ((w.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)

/-- $\prod_{w \in S}\varpi_w^{\varepsilon_w}$ has valuation $e^{-\varepsilon_v}$ at $v \in S$. -/
theorem valued_prod_primeGen_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (ε : HeightOneSpectrum (𝓞 F) → ℕ)
    (hv : v ∈ S) : Valued.v (algebraMap (𝓞 F) Fv (∏ w ∈ S, primeGen w ^ ε w)) = exp (-(ε v : ℤ)) := by
  rw [valued_algebraMap_int, map_prod, Finset.prod_eq_single_of_mem v hv]
  · rw [map_pow, intValuation_primeGen_self, ← WithZero.exp_nsmul]; congr 1; simp
  · intro w _ hwv
    rw [map_pow, intValuation_primeGen_of_ne v (Ne.symm hwv), one_pow]

/-- $\prod_{w \in S}\varpi_w^{\varepsilon_w}$ is a unit at $v \notin S$. -/
theorem valued_prod_primeGen_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (ε : HeightOneSpectrum (𝓞 F) → ℕ)
    (hv : v ∉ S) : Valued.v (algebraMap (𝓞 F) Fv (∏ w ∈ S, primeGen w ^ ε w)) = 1 := by
  rw [valued_algebraMap_int, map_prod]
  refine Finset.prod_eq_one fun w hw => ?_
  rw [map_pow, intValuation_primeGen_of_ne v (fun h => hv (h ▸ hw)), one_pow]

end Valuation

/-! ### Genus = spinor genus -/

section GenusSpinor

variable (Q : QuadForm F n)

/-- The spinor norm of the image of a rational isometry $\tau_x\tau_y$ at $\mathfrak p$. -/
theorem spinorNorm_orthMap_symm_mul (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) {x y : Fin n → F}
    (hx : Q.evalIn F x ≠ 0) (hy : Q.evalIn F y ≠ 0) :
    spinorNorm Q (v.adicCompletion F) (orthMap Q (v.adicCompletion F) (symm Q F x * symm Q F y)) =
      sqClassOf (algebraMap F (v.adicCompletion F) (Q.evalIn F x * Q.evalIn F y)) := by
  set K := v.adicCompletion F
  have hval : ∀ z : Fin n → F, Q.evalIn K (fun i => algebraMap F K (z i)) = algebraMap F K (Q.evalIn F z) :=
    fun z => by simpa using evalIn_map_tower Q K (K := F) z
  have hx' : Q.evalIn K (fun i => algebraMap F K (x i)) ≠ 0 := by rw [hval]; exact (map_ne_zero _).mpr hx
  have hy' : Q.evalIn K (fun i => algebraMap F K (y i)) ≠ 0 := by rw [hval]; exact (map_ne_zero _).mpr hy
  rw [map_mul, orthMap_symm, orthMap_symm]
  have := spinorNorm_symmProd Q K hQ [fun i => algebraMap F K (x i), fun i => algebraMap F K (y i)]
    (by intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl <;> assumption)
  simp only [symmProd, valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  rw [this, hval, hval, map_mul]

/-- **Genus = spinor genus** (O'Meara 1963, 102:9 [unverified]): let $\mathcal O_F$ be a PID, $Q$ nondegenerate in
$n \ge 3$ variables and isotropic at every infinite place, and $L$ a lattice such that `LocalSpinorUnits Q v L` holds at
every finite prime $\mathfrak p$ ($\theta(O(L_\mathfrak p)) \supseteq \mathfrak o_\mathfrak p^\times$, with an improper element).
Then every lattice in the genus of $L$ lies in the spinor genus of $L$. By `localSpinorUnits_of_unimodular` the local
condition holds automatically at every $\mathfrak p \nmid 2\det H$. Unconditional (no cited inputs). -/
@[kb "omeara1963" "102:9 [unverified]"]
theorem sameSpinorGenus_of_sameGenus [IsPrincipalIdealRing (𝓞 F)] (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (hinf : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion) (L : Lat F n)
    (hloc : ∀ v, LocalSpinorUnits Q v L) {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    SameSpinorGenus Q L M := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  -- `M = h L`
  have hMo : M ∈ MulAction.orbit (OAf Q) L := by rw [orbit_eq_genus]; exact hM
  obtain ⟨h, rfl⟩ := hMo
  -- local spinor norms `θ(h_v) = x_v`
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : v.adicCompletion F, x ≠ 0 ∧
      spinorNorm Q (v.adicCompletion F) (h v) = sqClassOf x := by
    intro v
    obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ (h v)
    exact ⟨_, valProd_ne_zero Q _ hxs, by rw [← hxe, spinorNorm_symmProd Q _ hQ xs hxs]⟩
  choose xv hxv0 hxvθ using hx
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v => log (Valued.v (xv v))
  let ε : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (m v % 2).toNat
  have hm : ∀ v, Valued.v (xv v) = exp (m v) := fun v =>
    (exp_log ((map_ne_zero _).mpr (hxv0 v))).symm
  have hε : ∀ v, ((ε v : ℕ) : ℤ) = m v % 2 := fun v => Int.toNat_of_nonneg (Int.emod_nonneg _ two_ne_zero)
  -- the finite set of primes where `h_v ∉ O(L_v)`
  have hfin : {v | h v ∉ locStabV Q v L}.Finite := by
    refine ((Filter.eventually_cofinite.mp h.2).union
      (Filter.eventually_cofinite.mp (loc_eventually_std L.2))).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hv ((locStabV_eq_stdStab Q v L hc.2).mpr hc.1)
  set S := hfin.toFinset
  -- the global element `a` and `γ` with `θ(γ) = a`
  set a₀ : 𝓞 F := ∏ w ∈ S, primeGen w ^ ε w
  set a : F := algebraMap (𝓞 F) F a₀
  have hva : ∀ v ∈ S, Valued.v (algebraMap F (v.adicCompletion F) a) = exp (-(ε v : ℤ)) := by
    intro v hv
    rw [← IsScalarTower.algebraMap_apply]
    exact valued_prod_primeGen_of_mem v ε hv
  have hva' : ∀ v ∉ S, Valued.v (algebraMap F (v.adicCompletion F) a) = 1 := by
    intro v hv
    rw [← IsScalarTower.algebraMap_apply]
    exact valued_prod_primeGen_of_not_mem v ε hv
  have ha : a ≠ 0 := by
    refine (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ?_
    exact Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  obtain ⟨x, y, hy, hxy⟩ := exists_evalIn_eq_mul Q hQ hn hinf ha
  have hx0 : Q.evalIn F x ≠ 0 := by rw [hxy]; exact mul_ne_zero ha hy
  set γ : orthGroup Q F := symm Q F x * symm Q F y
  have hθγ : ∀ v : HeightOneSpectrum (𝓞 F), spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ) =
      sqClassOf (algebraMap F (v.adicCompletion F) a) := by
    intro v
    rw [spinorNorm_orthMap_symm_mul Q hQ v hx0 hy, hxy, map_mul, map_mul]
    have hyv : algebraMap F (v.adicCompletion F) (Q.evalIn F y) ≠ 0 := (map_ne_zero _).mpr hy
    have hav : algebraMap F (v.adicCompletion F) a ≠ 0 := (map_ne_zero _).mpr ha
    rw [mul_assoc, sqClassOf_mul hav (mul_ne_zero hyv hyv),
      (sqClassOf_eq_one_iff (mul_ne_zero hyv hyv)).mpr ⟨_, rfl⟩, mul_one]
  -- local decomposition `γ_v⁻¹ h_v = k_v u_v`
  have hdec : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k ∈ spinorKernel Q (v.adicCompletion F),
      k⁻¹ * ((orthMap Q _ γ)⁻¹ * h v) ∈ locStabV Q v L := by
    intro v
    set K := v.adicCompletion F
    have hav : algebraMap F K a ≠ 0 := (map_ne_zero _).mpr ha
    by_cases hvS : v ∈ S
    · apply hloc v
      rw [← spinorNormHom_apply Q K hQ, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hθγ,
        SqClass.inv_eq, hxvθ, ← sqClassOf_mul hav (hxv0 v)]
      refine isUnitSqClass_of_valued_eq v _ (m v / 2) ?_
      rw [map_mul, hva v hvS, hm, ← exp_add, hε]
      congr 1
      omega
    · have hhv : h v ∈ locStabV Q v L := by
        by_contra hc; exact hvS (hfin.mem_toFinset.mpr hc)
      obtain ⟨k, hk, hg⟩ := hloc v (orthMap Q K γ) (by
        rw [hθγ]; exact ⟨_, hva' v hvS, rfl⟩)
      set g := k⁻¹ * orthMap Q K γ
      refine ⟨g⁻¹ * k⁻¹ * g, ?_, ?_⟩
      · have := (spinorKernel_normal Q K).conj_mem k⁻¹ ((spinorKernel Q K).inv_mem hk) g⁻¹
        simpa using this
      · have e : (g⁻¹ * k⁻¹ * g)⁻¹ * ((orthMap Q K γ)⁻¹ * h v) = g⁻¹ * h v := by
          simp only [g]; group
        rw [e]
        exact (locStabV Q v L).mul_mem ((locStabV Q v L).inv_mem hg) hhv
  choose kv hkv hukv using hdec
  -- the adelic element `u ∈ O(L̂)`
  let u : OAf Q := ⟨fun v => (kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v), by
    filter_upwards [loc_eventually_std L.2] with v hv
    exact (locStabV_eq_stdStab Q v L hv).mp (hukv v)⟩
  have hu : u ∈ locStab Q L := fun v => hukv v
  set k : OAf Q := (diagF Q γ)⁻¹ * h * u⁻¹
  have hk : k ∈ spinorKernelAf Q := by
    intro v
    have : k v = kv v := by
      change (orthMap Q _ γ)⁻¹ * h v * ((kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v))⁻¹ = kv v
      group
    rw [this]; exact hkv v
  refine (mem_latSpinorGenus Q).mpr ⟨γ, k, hk, ?_⟩
  have huL : latSMul Q u L = L :=
    MulAction.mem_stabilizer_iff.mp ((stabilizer_eq_locStab Q L).symm ▸ hu)
  have hh : h = diagF Q γ * k * u := by simp only [k]; group
  change h • L = (diagF Q γ) • (k • L)
  conv_lhs => rw [hh, mul_smul, mul_smul]
  change diagF Q γ • (k • latSMul Q u L) = _
  rw [huL]

/-- **Class number one of the genus** for indefinite forms with large local spinor norms: under the hypotheses of
`sameSpinorGenus_of_sameGenus`, every lattice in the genus of $L$ is isometric to $L$. **Conditional** on the named
input `StrongApproximationSpin F` (through Eichler's theorem). -/
@[kb "omeara1963" "102:9, 104:5 [unverified]"]
theorem isIsometric_of_sameGenus [IsPrincipalIdealRing (𝓞 F)] (hSA : StrongApproximationSpin F)
    (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (hinf : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion) (L : Lat F n)
    (hloc : ∀ v, LocalSpinorUnits Q v L) {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    IsIsometric Q L.1 M.1 := by
  have hind : IsIndefinite Q := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact ⟨w, hinf w⟩
  exact eichler_spinorGenus_eq_class Q hSA hn hQ hind (sameSpinorGenus_of_sameGenus Q hQ hn hinf L hloc hM)

/-- **The standard lattice** $\mathcal O_F^n$ as an element of `Lat F n`. -/
def stdLat : Lat F n := ⟨intVec, intVec_isLattice⟩

/-- **Genus = spinor genus for $\mathcal O_F^n$, checking only the bad primes**: for $Q = Q_0 \otimes F$ with $Q_0$ over
$\mathcal O_F$ (a PID), nondegenerate, $n \ge 3$, isotropic at every infinite place, the genus of $L = \mathcal O_F^n$ equals its
spinor genus as soon as `LocalSpinorUnits` holds at the primes $\mathfrak p \mid 2\det H$; at all other primes it holds
by `localSpinorUnits_of_unimodular`. -/
@[kb "omeara1963" "92:5, 102:9 [unverified]"]
theorem sameSpinorGenus_of_sameGenus_std [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) n)
    (hQ : (Q₀.map (algebraMap (𝓞 F) F)).Nondegenerate) (hn : 3 ≤ n)
    (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v stdLat)
    {M : Lat F n} (hM : SameGenus (Q₀.map (algebraMap (𝓞 F) F)) stdLat.1 M.1) :
    SameSpinorGenus (Q₀.map (algebraMap (𝓞 F) F)) stdLat M := by
  refine sameSpinorGenus_of_sameGenus _ hQ hn hinf stdLat (fun v => ?_) hM
  by_cases hb : (2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal
  · exact hbad v hb
  · push Not at hb
    exact localSpinorUnits_of_unimodular v Q₀ hb.1 hb.2 (by omega) stdLat (loc_intVec v)

end GenusSpinor

end QuadFormsKB.Lattices
