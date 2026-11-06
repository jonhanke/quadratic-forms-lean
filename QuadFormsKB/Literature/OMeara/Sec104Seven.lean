/-
# O'Meara §104: indefiniteness is essential in 104:5 (104:7)

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^9$ with $Q = I_9$ = `sumSqForm 9`, $L = \mathbb Z^9$ = `intVec`,
$K = E_8 \perp \mathbb Z$ = `omearaEZ 9` (`Sec106EZ.lean`, `Sec106Genus9.lean`). Indices are 0-based.

**Defines/Proves**
* `exists_spinorDecomp_of_rho`, `sameSpinorGenus_of_sameGenus_rho`: the argument of
  `sameSpinorGenus_of_sameGenus` (genus = spinor genus) without isotropy at infinity; the global rotation is supplied
  through a hypothesis `hρ` (for every nonzero $a_0 \in \mathcal O_F$, a sum-of-values relation
  $Q(x) = u\,a_0\,Q(y)$ with $u$ a unit at every finite place).
* `exists_unit_eq_mul_sq_odd`: every unit of $\mathbb Z_2$ is $c\,s^2$ with $c \in \{1,3,5,7\}$.
* `localSpinorUnits_sumSq9`: `LocalSpinorUnits` for $I_9$ and $\mathbb Z^9$ at every finite prime.
* `sameSpinorGenus_sumSq9`: the genus of $\mathbb Z^9$ is one spinor genus.
* `omeara104_7` (O'Meara 1973, §104, 104:7, p. 320): a nondegenerate non-indefinite form in $9 \ge 3$ variables
  with lattices in one spinor genus that are not isometric. Unconditional.

**Deviations.** O'Meara deduces this from 106:13; here the example of `omeara106_r3` is used directly.
The helper lemmas on $\mathbb Z_2$ are adapted from `Tamagawa/Indefinite/OneClassExample.lean` (classes $1,3,5,7$
instead of $1,3,5,-1$) and `localSpinorUnits_of_unitReps` from `Tamagawa/Indefinite/OneClass.lean`, copied here to
avoid importing the Siegel formula chain.
-/
import QuadFormsKB.Tamagawa.RatHeadline3
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.Lattices.SpinorGlobal
import QuadFormsKB.Literature.OMeara.Sec106Genus9

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.NF

/-- **`LocalSpinorUnits` from representations of all units** (copy of
`Tamagawa.Indefinite.localSpinorUnits_of_unitReps`): if every unit of $\mathfrak o_v$ is $Q_0(y)$ with
$y \in \mathfrak o_v^n$, then every $\sigma\in O(V_v)$ with unit spinor norm lies in $O'(V_v)\,O(\mathfrak o_v^n)$. -/
theorem localSpinorUnits_of_unitReps' {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)
    (v : HeightOneSpectrum (𝓞 F)) (hQ : (Q₀.map (algebraMap (𝓞 F) F)).Nondegenerate)
    (hrep : ∀ u : v.adicCompletionIntegers F, IsUnit u →
      ∃ y : Fin n → v.adicCompletionIntegers F, (LocalDensity.NF.Qp v Q₀).eval y = u) :
    LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F n) := by
  refine localSpinorUnits_of_improper (Q₀.map (algebraMap (𝓞 F) F)) v hQ _ fun u hu => ?_
  let u' : v.adicCompletionIntegers F := ⟨u, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le⟩
  have hu' : IsUnit u' := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact hu
  obtain ⟨y, hy⟩ := hrep u' hu'
  have hxstd : (fun i => (y i : v.adicCompletion F)) ∈ std v := fun i => by
    rw [neg_zero, WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (y i).2
  have hQx : (Q₀.map (algebraMap (𝓞 F) F)).evalIn (v.adicCompletion F) (fun i => (y i : v.adicCompletion F)) = u := by
    rw [Tamagawa.evalIn_coe_o v Q₀ y, hy]
  have hx0 : (Q₀.map (algebraMap (𝓞 F) F)).evalIn (v.adicCompletion F) (fun i => (y i : v.adicCompletion F)) ≠ 0 := by
    rw [hQx]; intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  have hs : symm (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F) (fun i => (y i : v.adicCompletion F)) ∈
      stdStab (Q₀.map (algebraMap (𝓞 F) F)) v :=
    symm_mem_stdStab v Q₀ hxstd (by rw [hQx, hu])
  have hL : symm (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F) (fun i => (y i : v.adicCompletion F)) ∈
      locStabV (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F n) :=
    (locStabV_eq_stdStab _ v (Tamagawa.stdLat F n) (loc_intVec v)).mpr hs
  refine ⟨_, hL, ?_, ?_⟩
  · ext; rw [detHom_val, symm_det _ _ hx0]; simp
  · rw [spinorNorm_symm _ _ hQ hx0, hQx]

section DyadicHelpers

variable {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

include h2

theorem natGenerator_eq_two' : Rat.HeightOneSpectrum.natGenerator v = 2 := by
  have h := (Tamagawa.RatHeadline3.intCast_mem_iff v 2).mp (by exact_mod_cast h2)
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  have h' : Rat.HeightOneSpectrum.natGenerator v ∣ 2 := by exact_mod_cast h
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'

theorem two_not_mem_sq' : (2 : 𝓞 ℚ) ∉ v.asIdeal ^ 2 := by
  intro h
  have hmap := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h
  rw [Ideal.map_pow, ← Rat.HeightOneSpectrum.span_natGenerator, natGenerator_eq_two' h2,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_ofNat] at hmap
  norm_num at hmap

theorem ordTwo_eq_one' : ordTwo v = 1 := by
  obtain ⟨h1, h2'⟩ := ordTwo_spec v
  have hle : ordTwo v ≤ 1 := by
    by_contra hc
    apply two_not_mem_sq' h2
    rw [← π_pow_dvd_ι_iff, map_ofNat]
    exact (pow_dvd_pow _ (by omega)).trans h1
  have hge : 1 ≤ ordTwo v := by
    by_contra hc
    apply h2'
    rw [show ordTwo v + 1 = 1 by omega, pow_one, ← map_ofNat (ι v), π_dvd_ι_iff]
    exact h2
  omega

theorem π_dvd_intCast_iff' (z : ℤ) : π v ∣ (z : 𝔬) ↔ (2 : ℤ) ∣ z := by
  rw [← map_intCast (ι v), π_dvd_ι_iff, Tamagawa.RatHeadline3.intCast_mem_iff, natGenerator_eq_two' h2]
  norm_cast

theorem π_pow_three_dvd_intCast' {z : ℤ} (hz : (8 : ℤ) ∣ z) : π v ^ 3 ∣ (z : 𝔬) := by
  obtain ⟨t, rfl⟩ := hz
  rw [← map_intCast (ι v), π_pow_dvd_ι_iff]
  have e : (((8 * t : ℤ)) : 𝓞 ℚ) = 2 ^ 3 * (t : 𝓞 ℚ) := by push_cast; norm_num
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow h2 3)

end DyadicHelpers

/-! ### The form over `𝓞 ℚ` -/

/-- $I_9$ over $\mathcal O_{\mathbb Q}$ (auxiliary). -/
def sumSqO : QuadForm (𝓞 ℚ) 9 := QuadForm.diag fun _ => 1

theorem sumSqO_map : sumSqO.map (algebraMap (𝓞 ℚ) ℚ) = sumSqForm 9 := by
  ext i j
  simp only [sumSqO, sumSqForm, QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem sumSqO_hessian_det : sumSqO.hessian.det = 2 ^ 9 := by
  have : sumSqO.hessian = Matrix.diagonal (fun _ => (1 : 𝓞 ℚ) + 1) := by
    ext i j
    simp only [sumSqO, QuadForm.hessian, QuadForm.diag, Matrix.add_apply, Matrix.transpose_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [this, Matrix.det_diagonal]
  simp
  norm_num

theorem nondegenerate_sumSqO : sumSqO.Nondegenerate := by
  rw [QuadForm.Nondegenerate, sumSqO_hessian_det]; norm_num

theorem nondegenerate_sumSqForm : (sumSqForm 9).Nondegenerate := by
  rw [← sumSqO_map]
  exact Tamagawa.nondegenerate_map sumSqO nondegenerate_sumSqO

/-! ### Unit square classes of $\mathbb Q_2$ with representatives $1,3,5,7$ -/

section Dyadic

variable {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

include h2

theorem exists_unit_eq_mul_sq_odd {u : 𝔬} (hu : IsUnit u) :
    ∃ c : ℤ, (c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) ∧ ∃ s : 𝔬, u = (c : 𝔬) * s ^ 2 := by
  obtain ⟨r, hr⟩ := redHom_surjective v 3 (Ideal.Quotient.mk _ u)
  have hr' : π v ^ 3 ∣ u - ι v r := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hr.symm)
  set z : ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) r
  have hzr : ι v r = (z : 𝔬) := by
    have : (z : 𝓞 ℚ) = r := by
      rw [← Tamagawa.RatHeadline3.intEquiv_symm_intCast]
      exact RingEquiv.symm_apply_apply _ r
    rw [← this, map_intCast]
  rw [hzr] at hr'
  have hπu : ¬ π v ∣ u := fun h => (irreducible_π v).not_isUnit (isUnit_of_dvd_unit h hu)
  have hz : ¬ (2 : ℤ) ∣ z := by
    intro hdvd
    apply hπu
    have h1 : π v ∣ u - (z : 𝔬) := (dvd_pow_self _ (by norm_num)).trans hr'
    have h2' : π v ∣ (z : 𝔬) := (π_dvd_intCast_iff' h2 z).mpr hdvd
    simpa using dvd_add h1 h2'
  obtain ⟨c, hc, h8⟩ : ∃ c : ℤ, (c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) ∧ (8 : ℤ) ∣ z - c := by
    have : z % 8 = 1 ∨ z % 8 = 3 ∨ z % 8 = 5 ∨ z % 8 = 7 := by omega
    rcases this with h | h | h | h
    · exact ⟨1, by norm_num, by omega⟩
    · exact ⟨3, by norm_num, by omega⟩
    · exact ⟨5, by norm_num, by omega⟩
    · exact ⟨7, by norm_num, by omega⟩
  have hcodd : ¬ (2 : ℤ) ∣ c := by rcases hc with rfl | rfl | rfl | rfl <;> norm_num
  have h3 : π v ^ 3 ∣ (c : 𝔬) * 1 ^ 2 - u := by
    have e : (c : 𝔬) * 1 ^ 2 - u = -((u - (z : 𝔬)) + ((z - c : ℤ) : 𝔬)) := by push_cast; ring
    rw [e, dvd_neg]
    exact dvd_add hr' (π_pow_three_dvd_intCast' h2 h8)
  have he := ordTwo_spec v
  rw [ordTwo_eq_one' h2] at he
  obtain ⟨s, hs⟩ := (DVR.exists_sq_mod_iff_exists_sq (irreducible_π v)
    (by simpa [pow_one] using he.1) (two_ne_zero' v) 1 he
    (fun h => hcodd ((π_dvd_intCast_iff' h2 c).mp h)) hπu).mp ⟨1, by simpa using h3⟩
  exact ⟨c, hc, s, hs.symm⟩

omit h2 in
theorem exists_vec_eq_sumSq (c : ℤ) (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) :
    ∃ y : Fin 9 → ℤ, ∑ i, y i ^ 2 = c := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨![1, 0, 0, 0, 0, 0, 0, 0, 0], by simp [Fin.sum_univ_succ]⟩
  · exact ⟨![1, 1, 1, 0, 0, 0, 0, 0, 0], by simp [Fin.sum_univ_succ]⟩
  · exact ⟨![1, 2, 0, 0, 0, 0, 0, 0, 0], by simp [Fin.sum_univ_succ]⟩
  · exact ⟨![1, 1, 1, 2, 0, 0, 0, 0, 0], by simp [Fin.sum_univ_succ]⟩

theorem localSpinorUnits_sumSq_two : LocalSpinorUnits (sumSqForm 9) v stdLat := by
  rw [← sumSqO_map]
  refine localSpinorUnits_of_unitReps' sumSqO v (Tamagawa.nondegenerate_map sumSqO
    nondegenerate_sumSqO) fun u hu => ?_
  obtain ⟨c, hc, s, hs⟩ := exists_unit_eq_mul_sq_odd h2 hu
  obtain ⟨y, hy⟩ := exists_vec_eq_sumSq c hc
  refine ⟨fun i => s * (y i : 𝔬), ?_⟩
  have hy' : ∑ i, (y i : 𝔬) ^ 2 = (c : 𝔬) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : 𝔬)) hy
  rw [hs, ← hy', sumSqO, Qp_diag]
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Matrix.one_apply, Finset.mul_sum,
    mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

end Dyadic

/-! ### Genus = spinor genus, with the global rotation supplied by representing $|a|$ -/

section Global

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {n : ℕ} (Q : QuadForm F n)

/-- **Spinor decomposition without isotropy at infinity.** As `exists_spinorDecomp`, but the rational rotation is
supplied through the hypothesis `hρ`: for every nonzero $a_0\in\mathcal O_F$ there are $x,y\in F^n$ and a global
unit-valued $u \neq 0$ (valuation $1$ at every finite place) with $Q(y)\ne0$ and $Q(x) = u\,a_0\,Q(y)$. -/
theorem exists_spinorDecomp_of_rho (hQ : Q.Nondegenerate)
    (hρ : ∀ a₀ : 𝓞 F, a₀ ≠ 0 → ∃ x y : Fin n → F, Q.evalIn F y ≠ 0 ∧ ∃ u : F, u ≠ 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) u) = 1) ∧
      Q.evalIn F x = u * algebraMap (𝓞 F) F a₀ * Q.evalIn F y)
    (L : Lat F n) (hloc : ∀ v, LocalSpinorUnits Q v L) (h : OAf Q) :
    ∃ γ : orthGroup Q F, ∃ k ∈ spinorKernelAf Q, ∃ u ∈ locStab Q L, h = diagF Q γ * k * u := by
  classical
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
  have hfin : {v | h v ∉ locStabV Q v L}.Finite := by
    refine ((Filter.eventually_cofinite.mp h.2).union
      (Filter.eventually_cofinite.mp (loc_eventually_std L.2))).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hv ((locStabV_eq_stdStab Q v L hc.2).mpr hc.1)
  set S := hfin.toFinset
  set a₀ : 𝓞 F := ∏ w ∈ S, primeGen w ^ ε w
  have ha₀ : a₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  have ha₀' : algebraMap (𝓞 F) F a₀ ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha₀
  obtain ⟨x, y, hy, u, hu0, hu, hxy⟩ := hρ a₀ ha₀
  set a : F := u * algebraMap (𝓞 F) F a₀ with hadef
  have hva : ∀ v ∈ S, Valued.v (algebraMap F (v.adicCompletion F) a) = exp (-(ε v : ℤ)) := by
    intro v hv
    rw [hadef, map_mul, map_mul, hu v, one_mul, ← IsScalarTower.algebraMap_apply]
    exact valued_prod_primeGen_of_mem v ε hv
  have hva' : ∀ v ∉ S, Valued.v (algebraMap F (v.adicCompletion F) a) = 1 := by
    intro v hv
    rw [hadef, map_mul, map_mul, hu v, one_mul, ← IsScalarTower.algebraMap_apply]
    exact valued_prod_primeGen_of_not_mem v ε hv
  have ha : a ≠ 0 := mul_ne_zero hu0 ha₀'
  have hx0 : Q.evalIn F x ≠ 0 := by rw [hxy]; exact mul_ne_zero ha hy
  set γ : orthGroup Q F := symm Q F x * symm Q F y
  have hθγ : ∀ v : HeightOneSpectrum (𝓞 F), spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ) =
      sqClassOf (algebraMap F (v.adicCompletion F) a) := by
    intro v
    rw [spinorNorm_orthMap_symm_mul Q hQ v hx0 hy, hxy]
    have hyv : algebraMap F (v.adicCompletion F) (Q.evalIn F y) ≠ 0 := (map_ne_zero _).mpr hy
    have hav : algebraMap F (v.adicCompletion F) a ≠ 0 := (map_ne_zero _).mpr ha
    rw [show a * Q.evalIn F y * Q.evalIn F y = a * (Q.evalIn F y * Q.evalIn F y) by ring]
    simp only [map_mul]
    rw [sqClassOf_mul hav (mul_ne_zero hyv hyv),
      (sqClassOf_eq_one_iff (mul_ne_zero hyv hyv)).mpr ⟨_, rfl⟩, mul_one]
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
  let u' : OAf Q := ⟨fun v => (kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v), by
    filter_upwards [loc_eventually_std L.2] with v hv
    exact (locStabV_eq_stdStab Q v L hv).mp (hukv v)⟩
  have hu' : u' ∈ locStab Q L := fun v => hukv v
  set k : OAf Q := (diagF Q γ)⁻¹ * h * u'⁻¹
  have hk : k ∈ spinorKernelAf Q := by
    intro v
    have : k v = kv v := by
      change (orthMap Q _ γ)⁻¹ * h v * ((kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v))⁻¹ = kv v
      group
    rw [this]; exact hkv v
  exact ⟨γ, k, hk, u', hu', by simp only [k]; group⟩

/-- **Genus = spinor genus** (variant of `sameSpinorGenus_of_sameGenus` without isotropy at infinity, with the
rational rotation supplied by `hρ`). -/
theorem sameSpinorGenus_of_sameGenus_rho (hQ : Q.Nondegenerate)
    (hρ : ∀ a₀ : 𝓞 F, a₀ ≠ 0 → ∃ x y : Fin n → F, Q.evalIn F y ≠ 0 ∧ ∃ u : F, u ≠ 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) u) = 1) ∧
      Q.evalIn F x = u * algebraMap (𝓞 F) F a₀ * Q.evalIn F y)
    (L : Lat F n) (hloc : ∀ v, LocalSpinorUnits Q v L) {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    SameSpinorGenus Q L M := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  have hMo : M ∈ MulAction.orbit (OAf Q) L := by rw [orbit_eq_genus]; exact hM
  obtain ⟨h, rfl⟩ := hMo
  obtain ⟨γ, k, hk, u, hu, hh⟩ := exists_spinorDecomp_of_rho Q hQ hρ L hloc h
  refine (mem_latSpinorGenus Q).mpr ⟨γ, k, hk, ?_⟩
  have huL : latSMul Q u L = L :=
    MulAction.mem_stabilizer_iff.mp ((stabilizer_eq_locStab Q L).symm ▸ hu)
  change h • L = (diagF Q γ) • (k • L)
  conv_lhs => rw [hh, mul_smul, mul_smul]
  change diagF Q γ • (k • latSMul Q u L) = _
  rw [huL]

end Global

/-! ### The definite space $I_9$ -/

theorem exists_sumSq_eq (r : ℚ) (hr : 0 < r) : ∃ x : Fin 9 → ℚ, (sumSqForm 9).evalIn ℚ x = r := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (r.num.toNat * r.den)
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hnum : ((r.num.toNat : ℤ) : ℚ) = r.num := by
    have : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr.le)
    rw [this]
  refine ⟨fun i => (![(a : ℚ), b, c, d, 0, 0, 0, 0, 0] i) / r.den, ?_⟩
  rw [sumSqForm, QuadForm.evalIn_diag]
  simp only [map_one, one_mul, div_pow, ← Finset.sum_div]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  have h' : ((a : ℚ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = (r.num : ℚ) * r.den := by
    rw [← hnum]; exact_mod_cast h
  have hr' : (r.num : ℚ) = r * r.den := (Rat.mul_den_eq_num r).symm
  rw [div_eq_iff (pow_ne_zero 2 hden)]
  linear_combination h' + (r.den : ℚ) * hr'

/-- $I_9$ is anisotropic at every infinite place of $\mathbb Q$ (a sum of squares in $\mathbb R$). -/
theorem not_isIndefinite_sumSq (n : ℕ) : ¬ IsIndefinite (sumSqForm n) := by
  rintro ⟨w, y, hy0, hy⟩
  have hw : w.IsReal := IsTotallyReal.isReal w
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  rw [sumSqForm, QuadForm.evalIn_diag] at hy
  simp only [map_one, one_mul] at hy
  have h0 : ∑ i, (ψ (y i)) ^ 2 = 0 := by
    have := congrArg ψ hy
    simpa [map_sum, map_pow] using this
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ψ (y i)))).mp h0
  apply hy0
  funext i
  have hi := this i (Finset.mem_univ i)
  exact ψ.injective (by simpa using hi)

theorem rho_sumSq9 (a₀ : 𝓞 ℚ) (ha₀ : a₀ ≠ 0) :
    ∃ x y : Fin 9 → ℚ, (sumSqForm 9).evalIn ℚ y ≠ 0 ∧ ∃ u : ℚ, (u = 1 ∨ u = -1) ∧
      (sumSqForm 9).evalIn ℚ x = u * algebraMap (𝓞 ℚ) ℚ a₀ * (sumSqForm 9).evalIn ℚ y := by
  have hq : algebraMap (𝓞 ℚ) ℚ a₀ ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ)).mpr ha₀
  set q := algebraMap (𝓞 ℚ) ℚ a₀
  have hy : (sumSqForm 9).evalIn ℚ (Pi.single 0 1) = 1 := by
    rw [sumSqForm, QuadForm.evalIn_diag]
    simp [Pi.single_apply]
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · obtain ⟨x, hx⟩ := exists_sumSq_eq (-q) (by linarith)
    exact ⟨x, Pi.single 0 1, by rw [hy]; exact one_ne_zero, -1, Or.inr rfl,
      by rw [hy, hx]; ring⟩
  · obtain ⟨x, hx⟩ := exists_sumSq_eq q hpos
    exact ⟨x, Pi.single 0 1, by rw [hy]; exact one_ne_zero, 1, Or.inl rfl,
      by rw [hy, hx]; ring⟩

theorem localSpinorUnits_sumSq9 (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocalSpinorUnits (sumSqForm 9) v stdLat := by
  by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
  · exact localSpinorUnits_sumSq_two h2
  · rw [← sumSqO_map]
    refine localSpinorUnits_of_unimodular v sumSqO h2 ?_ (by norm_num) stdLat (loc_intVec v)
    rw [sumSqO_hessian_det]
    exact fun h => h2 (v.isPrime.mem_of_pow_mem 9 h)

/-- **Every lattice in the genus of $\mathbb Z^9$ lies in its spinor genus** (a definite space where the class
is nevertheless smaller than the genus, see `omeara104_7`). -/
theorem sameSpinorGenus_sumSq9 {M : Lat ℚ 9} (hM : SameGenus (sumSqForm 9) (stdLat : Lat ℚ 9).1 M.1) :
    SameSpinorGenus (sumSqForm 9) stdLat M := by
  refine sameSpinorGenus_of_sameGenus_rho (sumSqForm 9) nondegenerate_sumSqForm ?_ stdLat
    localSpinorUnits_sumSq9 hM
  intro a₀ ha₀
  obtain ⟨x, y, hy, u, hu, hxy⟩ := rho_sumSq9 a₀ ha₀
  refine ⟨x, y, hy, u, by rcases hu with rfl | rfl <;> norm_num, fun v => ?_, hxy⟩
  rcases hu with rfl | rfl <;> simp

/-- **O'Meara 104:7 (indefiniteness is essential in 104:5).** There is a nondegenerate quadratic form $Q$ over
$\mathbb Q$ in $n = 9 \ge 3$ variables that is not indefinite, namely $Q = I_9$ (`sumSqForm 9`), and
lattices $L = \mathbb Z^9$ and $K = E_8 \perp \mathbb Z$ on $V = \mathbb Q^9$ with $K$ in the spinor genus of $L$
(`SameSpinorGenus`) but $K$ not isometric to $L$ (`IsIsometric`). So the conclusion $\mathrm{cls} = \mathrm{spn}$ of
104:5 fails for this definite space.

*Proof (not O'Meara's, who cites 106:13):* the lattices are in the same genus (as in `omeara106_r3`), and the genus of
$\mathbb Z^9$ is a single spinor genus, because $\theta(O(\mathbb Z_p^9)) \supseteq \mathbb Z_p^\times\mathbb Q_p^{\times2}$ at
every prime (`localSpinorUnits_sumSq9`: symmetries at odd $p$, the unit classes $1,3,5,7$ at $p = 2$) and $\mathbb Z$
is a principal ideal domain; the positive rational $a = \prod p^{\varepsilon_p}$ is a spinor norm of a global rotation
$\tau_x\tau_{e_0}$ since it is a sum of four squares (`sameSpinorGenus_of_sameGenus_rho`). Unconditional. -/
@[kb "omeara1963" "§104, 104:7, p. 320 (indefiniteness is essential in 104:5)"]
theorem omeara104_7 :
    ∃ Q : QuadForm ℚ 9, Q.Nondegenerate ∧ ¬ IsIndefinite Q ∧ ∃ L K : Lat ℚ 9,
      SameSpinorGenus Q L K ∧ ¬ IsIsometric Q L.1 K.1 := by
  let L : Lat ℚ 9 := ⟨intVec, intVec_isLattice⟩
  let K : Lat ℚ 9 := ⟨omearaEZ 9, omearaEZ_isLattice (by norm_num)⟩
  refine ⟨sumSqForm 9, nondegenerate_sumSqForm, not_isIndefinite_sumSq 9, L, K, ?_,
    not_isIsometric_intVec_omearaEZ (by norm_num)⟩
  refine sameSpinorGenus_sumSq9 ?_
  intro v
  by_cases hv : (2 : 𝓞 ℚ) ∈ v.asIdeal
  · exact genus9_isometry_at_two v hv
  · have h := (omeara106_r21 (sumSqForm 9) L K adj_D_unimodular
      (omearaEZ_adjacent (by norm_num))).2 v hv
    exact ⟨1, Subgroup.one_mem _, by rw [locAct_one]; exact h⟩

end QuadFormsKB.Lattices
