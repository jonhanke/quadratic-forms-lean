/-
# Left ideals of a maximal order: the local-global correspondence for every class number

**Layer:** $F$ a number field (any class number), $D=(a,b)_F$ with $a,b \in \mathcal O_F$, $\mathcal O \subset D$ an order, $v$ the finite places.
The PID file `QuatIdealLocalGlobal` indexes left ideals by a *generator* $n$ of the reduced norm and uses a global basis of $\mathcal O$ and generators of
$\mathfrak p_v$. This file proves the same local-global dictionary with the reduced norm an arbitrary ideal $\mathfrak n \subseteq \mathcal O_F$:
$$\{J : \operatorname{nrd}(J) = \mathfrak n\} \;\simeq\; \prod_{v \mid n}\{I \subseteq \mathcal O_v : \operatorname{nrd}(I) = \mathfrak p_v^{c_v(\mathfrak n)}\}$$
for any $0 \ne n \in \mathfrak n$, with no basis or generator chosen: local frames (`OrderLocalNF.LocFrame`) replace bases, the ideal powers
$\mathfrak p_v^e$ replace $\varpi^e$, and ideals of $\mathcal O_F$ are compared through their completions by
`map_ι_eq_span` ($\mathfrak a\,\mathfrak o_v = (\varpi_v^{c_v(\mathfrak a)})$) and Mathlib's $\mathfrak a = \bigcap_v\mathfrak p_v^{c_v(\mathfrak a)}$.

Contents of this file's first part: the ideal arithmetic (`cI`, `mem_iff_forall_cI`, `map_ι_eq_span`, `eq_of_map_eq`) and basis-free
copies (in the namespace `QuatOrder.Gen`) of the PID file's lemmas: completions of ideals, the reduced norm of a completion, CRT approximation,
`mem_pow_smul_order` (the basis-free replacement of `exists_eq_genP_pow_smul`).

Sources: Voight, *Quaternion Algebras* (2021), Thm. 9.4.9, Lemma 9.5.3, Prop. 26.3.9, §26.4.
-/
import QuadFormsKB.Tamagawa.OrderLocalNF
import QuadFormsKB.Tamagawa.QuatIdealLocalGlobal

open NumberField IsDedekindDomain Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF IsLocalization

/-! ### Ideals of $\mathcal O_F$ versus their completions -/

section IdealArith

variable {F : Type} [Field F] [NumberField F]

/-- The multiplicity $c_v(\mathfrak a)$ of the prime $\mathfrak p_v$ in the ideal $\mathfrak a$ (Mathlib's `Associates` count; it is
`FractionalIdeal.count` on the coercion). -/
abbrev cI (v : HeightOneSpectrum (𝓞 F)) (𝔞 : Ideal (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔞).factors

/-- **Ideals are determined locally:** $x \in \mathfrak a \iff x \in \mathfrak p_v^{c_v(\mathfrak a)}$ for all $v$. -/
theorem mem_iff_forall_cI {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) {x : 𝓞 F} :
    x ∈ 𝔞 ↔ ∀ v : HeightOneSpectrum (𝓞 F), x ∈ v.asIdeal ^ cI v 𝔞 := by
  have h1 := Ideal.iInf_maxPowDividing_eq (I := 𝔞) h
  constructor
  · intro hx v
    rw [← h1] at hx
    exact (Submodule.mem_iInf _).1 hx v
  · intro hx
    rw [← h1]
    exact (Submodule.mem_iInf _).2 hx

theorem le_pow_cI (v : HeightOneSpectrum (𝓞 F)) {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) : 𝔞 ≤ v.asIdeal ^ cI v 𝔞 :=
  fun _ hx => (mem_iff_forall_cI h).1 hx v

theorem not_le_pow_succ_cI (v : HeightOneSpectrum (𝓞 F)) {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) :
    ¬ 𝔞 ≤ v.asIdeal ^ (cI v 𝔞 + 1) := by
  intro hle
  have hd : v.asIdeal ^ (cI v 𝔞 + 1) ∣ 𝔞 := Ideal.dvd_iff_le.2 hle
  have h2 : (Associates.mk v.asIdeal) ^ (cI v 𝔞 + 1) ≤ Associates.mk 𝔞 := by
    rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]; exact hd
  have := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr h) v.associates_irreducible).1 h2
  change cI v 𝔞 + 1 ≤ cI v 𝔞 at this
  omega

theorem exists_mem_not_mem_pow_succ (v : HeightOneSpectrum (𝓞 F)) {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) :
    ∃ x ∈ 𝔞, x ∉ v.asIdeal ^ (cI v 𝔞 + 1) := by
  obtain ⟨x, hx, hx'⟩ := IsConcreteLE.not_le_iff_exists.1 (not_le_pow_succ_cI v h)
  exact ⟨x, hx, hx'⟩

theorem exists_span_ι_eq_nf (v : HeightOneSpectrum (𝓞 F)) {n : 𝓞 F} (hn : n ≠ 0) :
    ∃ e : ℕ, Ideal.span {ι v n} = Ideal.span {π v ^ e} :=
  IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact ι_ne_zero v hn) (irreducible_π v)

/-- **The completion of an ideal:** $\mathfrak a\,\mathfrak o_v = (\varpi_v^{c_v(\mathfrak a)})$. -/
theorem map_ι_eq_span (v : HeightOneSpectrum (𝓞 F)) {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) :
    Ideal.map (ι v) 𝔞 = Ideal.span {π v ^ cI v 𝔞} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    exact (ι_mem_span_π_pow v _ _).2 (le_pow_cI v h hx)
  · obtain ⟨x, hx, hxn⟩ := exists_mem_not_mem_pow_succ v h
    have hx0 : x ≠ 0 := fun h0 => hxn (h0 ▸ Ideal.zero_mem _)
    obtain ⟨m, hm⟩ := exists_span_ι_eq_nf v hx0
    have hmc : m ≤ cI v 𝔞 := by
      by_contra hlt
      push Not at hlt
      apply hxn
      rw [← ι_mem_span_π_pow]
      have : ι v x ∈ Ideal.span {π v ^ m} := hm ▸ Ideal.mem_span_singleton_self _
      exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hlt) this
    have hπm : π v ^ m ∈ Ideal.map (ι v) 𝔞 := by
      have : π v ^ m ∈ Ideal.span {ι v x} := hm ▸ Ideal.mem_span_singleton_self _
      exact Ideal.span_le.2 (Set.singleton_subset_iff.2 (Ideal.mem_map_of_mem _ hx)) this
    rw [Ideal.span_singleton_le_iff_mem]
    have : π v ^ cI v 𝔞 = π v ^ (cI v 𝔞 - m) * π v ^ m := by rw [← pow_add, Nat.sub_add_cancel hmc]
    rw [this]
    exact Ideal.mul_mem_left _ _ hπm


/-- **Ideals of $\mathcal O_F$ are determined by their completions.** -/
theorem eq_of_map_eq {𝔞 𝔟 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), Ideal.map (ι v) 𝔞 = Ideal.map (ι v) 𝔟) : 𝔞 = 𝔟 := by
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), cI v 𝔞 = cI v 𝔟 := fun v => by
    have := h v
    rw [map_ι_eq_span v h𝔞, map_ι_eq_span v h𝔟] at this
    exact pow_eq_of_span_eq (irreducible_π v) this
  ext x
  rw [mem_iff_forall_cI h𝔞, mem_iff_forall_cI h𝔟]
  simp only [hc]

end IdealArith

/-! ### Copies of the PID-file lemmas without `IsPrincipalIdealRing` -/

namespace Gen

section Arith

variable {F : Type} [Field F] [NumberField F]

theorem finite_setOf_mem {n : 𝓞 F} (hn : n ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | n ∈ v.asIdeal}.Finite := by
  have h := Ideal.finite_factors (I := Ideal.span {n}) (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn)
  exact h.subset fun v hv => Ideal.dvd_span_singleton.2 hv

/-- The finite set of places $v \mid n$. -/
def primeSupport {n : 𝓞 F} (hn : n ≠ 0) : Finset (HeightOneSpectrum (𝓞 F)) := (finite_setOf_mem hn).toFinset

theorem mem_primeSupport {n : 𝓞 F} (hn : n ≠ 0) {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ primeSupport hn ↔ n ∈ v.asIdeal := by
  rw [primeSupport, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]


theorem isUnit_ι_of_not_mem {v : HeightOneSpectrum (𝓞 F)} {n : 𝓞 F} (hn : n ∉ v.asIdeal) : IsUnit (ι v n) := by
  by_contra h
  have : ι v n ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := h
  rw [(irreducible_π v).maximalIdeal_eq, Ideal.mem_span_singleton, π_dvd_ι_iff] at this
  exact hn this

theorem exists_ι_sub_mem_span (v : HeightOneSpectrum (𝓞 F)) (E : ℕ) (d : v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, d - ι v r ∈ Ideal.span {π v ^ E} := by
  obtain ⟨r, hr⟩ := redHom_surjective v E (Ideal.Quotient.mk _ d)
  exact ⟨r, Ideal.Quotient.eq.1 hr.symm⟩

/-- **Simultaneous approximation (CRT + density):** given finitely many places $v \in S$, exponents $e_v$ and targets
$d_v \in \mathfrak o_v$, there is $r \in \mathcal O_F$ with $\iota_v(r) \equiv d_v \bmod \varpi_v^{e_v}$ for all $v \in S$. -/
theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ)
    (d : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, ∀ v ∈ S, d v - ι v r ∈ Ideal.span {π v ^ e v} := by
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ rv : 𝓞 F, d v - ι v rv ∈ Ideal.span {π v ^ e v} := by
    intro v
    obtain ⟨rv, hrv⟩ := redHom_surjective v (e v) (Ideal.Quotient.mk _ (d v))
    exact ⟨rv, Ideal.Quotient.eq.1 hrv.symm⟩
  choose rv hrv using hloc
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) e
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => rv v)
  refine ⟨y, fun v hv => ?_⟩
  have h1 : ι v (y - rv v) ∈ Ideal.span {π v ^ e v} := (ι_mem_span_π_pow v _ _).2 (hy v hv)
  have : d v - ι v y = (d v - ι v (rv v)) - ι v (y - rv v) := by rw [map_sub]; ring
  rw [this]
  exact Ideal.sub_mem _ (hrv v) h1


theorem exists_crt_idem (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ t : 𝓞 F, t - 1 ∈ v.asIdeal ^ e v ∧ ∀ w ∈ S, w ≠ v → t ∈ w.asIdeal ^ e w := by
  classical
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert v S) (fun w => w.asIdeal) e
    (fun w _ => w.prime) (fun w _ u _ h h' => h (HeightOneSpectrum.ext h'))
    (fun w => if w.1 = v then 1 else 0)
  refine ⟨y, by simpa using hy v (Finset.mem_insert_self v S), fun w hw hwv => ?_⟩
  simpa [hwv] using hy w (Finset.mem_insert_of_mem hw)

end Arith

section LocalIdeal

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem nrd_complHom (x : QuatF F a b) : nrd (complHom v a b x) = algebraMap F Fv (nrd x) := by
  simp only [nrd, complHom_re, complHom_imI, complHom_imJ, complHom_imK, map_add, map_sub, map_mul, map_pow]
  rfl

variable {O : Subalgebra (𝓞 F) (QuatF F a b)}

theorem mem_localIdeal_iff {J : Ideal O} {y : localOrder (v := v) a b O} :
    y ∈ localIdeal (v := v) J ↔ (y : QuatV v a b) ∈ Submodule.span 𝔬 (idealImage (v := v) J) := by rfl

theorem complHom_mem_span_idealImage {J : Ideal O} {x : O} (hx : x ∈ J) :
    complHom v a b (x : QuatF F a b) ∈ Submodule.span 𝔬 (idealImage (v := v) J) :=
  Submodule.subset_span ⟨x, hx, rfl⟩

variable (v) in
/-- The completion of an order is an order, without a PID hypothesis (local frame). -/
theorem isOrder_localOrder_gen (hO : IsOrder (𝓞 F) F O) : IsOrder 𝔬 Fv (localOrder (v := v) a b O) :=
  (Classical.choice (LocFrame.exists (v := v) hO)).isOrder_localOrder

theorem leftNrdIdeal_localIdeal (hO : IsOrder (𝓞 F) F O) (J : Ideal O) :
    leftNrdIdeal (localIdeal (v := v) J) = Ideal.map (ι v) (leftNrdIdeal J) := by
  have hOv := isOrder_localOrder_gen (v := v) hO
  apply le_antisymm
  · -- the local reduced-norm ideal is generated by one value t = nrd y
    obtain ⟨t, ⟨y, hyJ, hyt⟩, hspan⟩ := exists_span_eq_span_singleton (R := 𝔬)
      (S := {r | ∃ x ∈ localIdeal (v := v) J, algebraMap 𝔬 Fv r = nrd (x : QuatV v a b)})
      ⟨0, 0, (localIdeal (v := v) J).zero_mem, by simp [nrd]⟩
    rw [leftNrdIdeal, hspan]
    by_cases ht0 : t = 0
    · rw [ht0, Ideal.span_singleton_eq_bot.2 rfl]; exact bot_le
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 (irreducible_π v)
    set ϖ' : 𝔬 := π v
    -- approximate y by an element of J modulo ϖ'^(m+1)
    obtain ⟨N, c, g, hyc⟩ := Submodule.mem_span_set'.1 ((mem_localIdeal_iff).1 hyJ)
    have hg : ∀ k, ∃ x : O, x ∈ J ∧ complHom v a b (x : QuatF F a b) = (g k : QuatV v a b) := fun k => by
      obtain ⟨x, hx, hxg⟩ := (g k).2; exact ⟨x, hx, hxg⟩
    choose xk hxkJ hxk using hg
    have happrox := fun k => exists_ι_sub_mem_span v (m + 1) (c k)
    choose r hr using happrox
    have hr' : ∀ k, ∃ h, c k - ι v (r k) = π v ^ (m + 1) * h := fun k =>
      (Ideal.mem_span_singleton'.1 (hr k)).imp fun h hh => by rw [← hh, mul_comm]
    choose h hrh using hr'
    set x : O := ∑ k, algebraMap (𝓞 F) O (r k) * xk k
    have hxJ : x ∈ J := J.sum_mem fun k _ => J.mul_mem_left _ (hxkJ k)
    set z : QuatV v a b := ∑ k, h k • complHom v a b (xk k : QuatF F a b)
    have hzO : z ∈ localOrder (v := v) a b O :=
      Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _ (mem_localOrder_of_mem a b (xk k).2) _
    have hcx : complHom v a b (x : QuatF F a b) = ∑ k, ι v (r k) • complHom v a b (xk k : QuatF F a b) := by
      simp only [x, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, map_sum, map_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply (𝓞 F) F (QuatF F a b), AlgHom.commutes,
        ← Algebra.smul_def, ι_smul_eq]
    have hyx : (y : QuatV v a b) = complHom v a b (x : QuatF F a b) + ϖ' ^ (m + 1) • z := by
      rw [← hyc, hcx, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hxk k, smul_smul, ← hrh k, ← add_smul]
      congr 1; ring
    -- integrality of the pieces
    have hxO : complHom v a b (x : QuatF F a b) ∈ localOrder (v := v) a b O := mem_localOrder_of_mem a b x.2
    obtain ⟨nz, hnz⟩ := (isInteger_trd_nrd hOv hzO).2
    obtain ⟨tz, htz⟩ := (isInteger_trd_nrd hOv (Subalgebra.mul_mem _ hxO
      (star_mem_of_isOrder hOv hzO))).1
    obtain ⟨nx, hnx⟩ := (isInteger_trd_nrd hO x.2).2
    have hnxl : nrd (complHom v a b (x : QuatF F a b)) = algebraMap 𝔬 Fv (ι v nx) := by
      rw [nrd_complHom, ← hnx]; rfl
    have key : t = ι v nx + ϖ' ^ (m + 1) * (ϖ' ^ (m + 1) * nz + tz) := by
      apply IsFractionRing.injective 𝔬 Fv
      rw [hyt, hyx, ← algebraMap_smul Fv (ϖ' ^ (m + 1)) z, nrd_add, nrd_smul, hnxl, star_smul_quat, mul_smul_comm, trd, QuaternionAlgebra.re_smul,
        smul_eq_mul]
      have htz' : 2 * (complHom v a b (x : QuatF F a b) * star z).re = algebraMap 𝔬 Fv tz := by
        rw [htz]; rfl
      rw [← mul_assoc, mul_comm 2, mul_assoc, htz', ← hnz]
      simp only [map_add, map_mul, map_pow]; ring
    -- so nrd(ι x) generates (t)
    have hunit : IsUnit ((u : 𝔬) - ϖ' * (ϖ' ^ (m + 1) * nz + tz)) := by
      have hmem : ϖ' * (ϖ' ^ (m + 1) * nz + tz) ∈ IsLocalRing.maximalIdeal 𝔬 :=
        Ideal.mul_mem_right _ _ ((irreducible_π v).maximalIdeal_eq ▸ Ideal.mem_span_singleton_self _)
      by_contra hc
      have h1 : (u : 𝔬) - ϖ' * (ϖ' ^ (m + 1) * nz + tz) ∈ IsLocalRing.maximalIdeal 𝔬 := hc
      have h2 : (u : 𝔬) ∈ IsLocalRing.maximalIdeal 𝔬 := by
        have := Ideal.add_mem _ h1 hmem; rwa [sub_add_cancel] at this
      exact h2 u.isUnit
    have hgen : ι v nx = ϖ' ^ m * ((u : 𝔬) - ϖ' * (ϖ' ^ (m + 1) * nz + tz)) := by
      have : ι v nx = t - ϖ' ^ (m + 1) * (ϖ' ^ (m + 1) * nz + tz) := by rw [key]; ring
      rw [this, hu]; ring
    have hspan_eq : Ideal.span {t} = Ideal.span {ι v nx} := by
      rw [Ideal.span_singleton_eq_span_singleton]
      refine ⟨u⁻¹ * hunit.unit, ?_⟩
      calc t * ↑(u⁻¹ * hunit.unit) = ϖ' ^ m * ((u : 𝔬) * ↑u⁻¹) * ↑hunit.unit := by
            rw [hu, Units.val_mul]; ring
        _ = ι v nx := by rw [Units.mul_inv, mul_one, IsUnit.unit_spec, hgen]
    rw [hspan_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨x, hxJ, hnx⟩)
  · rw [Ideal.map_le_iff_le_comap]
    refine Ideal.span_le.2 ?_
    rintro r ⟨x, hx, hr⟩
    refine Ideal.mem_comap.2 (Ideal.subset_span ⟨⟨_, mem_localOrder_of_mem a b x.2⟩,
      complHom_mem_span_idealImage hx, ?_⟩)
    rw [nrd_complHom, ← hr]; rfl


end LocalIdeal

section LocalGlobal

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

theorem complHom_algebraMap (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    complHom v a b (algebraMap (𝓞 F) (QuatF F a b) r) =
      algebraMap (v.adicCompletionIntegers F) (QuatV v a b) (ι v r) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (QuatF F a b), AlgHom.commutes,
    IsScalarTower.algebraMap_apply (v.adicCompletionIntegers F) (v.adicCompletion F) (QuatV v a b),
    IsScalarTower.algebraMap_apply F (v.adicCompletion F) (QuatV v a b)]
  rfl

/-- $\iota_v(n) \in J_v$ when $n \in J$. -/
theorem algebraMap_mem_localIdeal (v : HeightOneSpectrum (𝓞 F)) {J : Ideal O} {n : 𝓞 F}
    (hn : algebraMap (𝓞 F) O n ∈ J) :
    algebraMap (v.adicCompletionIntegers F) (localOrder (v := v) a b O) (ι v n) ∈ localIdeal (v := v) J := by
  rw [mem_localIdeal_iff]
  have := complHom_mem_span_idealImage (v := v) hn
  rwa [Subalgebra.coe_algebraMap, complHom_algebraMap] at this

/-- Multiples of $\iota_v(n)$: if $\iota_v(n) \in I$ (a left ideal of $\mathcal O_v$) then $c\,z \in I$ for all $z \in \mathcal O_v$ and $c \in (\iota_v n)$. -/
theorem smul_mem_of_algebraMap_mem (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (localOrder (v := v) a b O)}
    {n : 𝓞 F} (hn : algebraMap (v.adicCompletionIntegers F) (localOrder (v := v) a b O) (ι v n) ∈ I)
    {c : v.adicCompletionIntegers F} (hc : c ∈ Ideal.span {ι v n}) (z : localOrder (v := v) a b O) : c • z ∈ I := by
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  have : (d * ι v n) • z = (d • z) * algebraMap _ (localOrder (v := v) a b O) (ι v n) := by
    rw [mul_comm, ← smul_smul, Algebra.smul_def (ι v n), Algebra.commutes]
  rw [this]; exact I.mul_mem_left _ hn

/-- **Units away from $n$:** if $n \in J$ and $v \nmid n$ then $J_v = \mathcal O_v$. -/
theorem localIdeal_eq_top (v : HeightOneSpectrum (𝓞 F)) {J : Ideal O} {n : 𝓞 F}
    (hn : algebraMap (𝓞 F) O n ∈ J) (hv : n ∉ v.asIdeal) : localIdeal (v := v) J = ⊤ := by
  obtain ⟨u, hu⟩ := isUnit_ι_of_not_mem hv
  rw [Ideal.eq_top_iff_one]
  have h1 := smul_mem_of_algebraMap_mem v (algebraMap_mem_localIdeal v hn) (c := ↑u⁻¹ * ι v n)
    (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) 1
  rwa [← hu, Units.inv_mul, one_smul] at h1


theorem exists_approx_mem (v : HeightOneSpectrum (𝓞 F)) {J : Ideal O} {x : O}
    (hx : complHom v a b (x : QuatF F a b) ∈ Submodule.span (v.adicCompletionIntegers F) (idealImage (v := v) J))
    (E : ℕ) : ∃ y ∈ J, ∃ z ∈ localOrder (v := v) a b O,
      complHom v a b ((x : QuatF F a b) - y) = (π v ^ E) • z := by
  obtain ⟨N, c, g, hyc⟩ := Submodule.mem_span_set'.1 hx
  have hg : ∀ k, ∃ y : O, y ∈ J ∧ complHom v a b (y : QuatF F a b) = (g k : QuatV v a b) := fun k => by
    obtain ⟨y, hy, hyg⟩ := (g k).2; exact ⟨y, hy, hyg⟩
  choose yk hykJ hyk using hg
  have happrox := fun k => exists_ι_sub_mem_span v E (c k)
  choose r hr using happrox
  have hr' : ∀ k, ∃ h, c k - ι v (r k) = π v ^ E * h := fun k => Ideal.mem_span_singleton'.1 (hr k) |>.imp
    fun h hh => by rw [← hh, mul_comm]
  choose h hh using hr'
  refine ⟨∑ k, algebraMap (𝓞 F) O (r k) * yk k, J.sum_mem fun k _ => J.mul_mem_left _ (hykJ k),
    ∑ k, h k • complHom v a b (yk k : QuatF F a b),
    Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _ (mem_localOrder_of_mem a b (yk k).2) _, ?_⟩
  rw [map_sub, ← hyc, Finset.smul_sum]
  simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul, map_sum, map_mul, Subalgebra.coe_algebraMap,
    complHom_algebraMap]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hyk k, ← Algebra.smul_def, smul_smul, ← hh k, sub_smul]

/-- Multiples of $n$ lie in every left ideal containing $n$. -/
theorem smul_mem_of_dvd {J : Ideal O} {n r : 𝓞 F} (hn : algebraMap (𝓞 F) O n ∈ J) (hr : n ∣ r) (q : O) :
    r • q ∈ J := by
  obtain ⟨c, rfl⟩ := hr
  rw [Algebra.smul_def, show algebraMap (𝓞 F) O (n * c) * q = (algebraMap (𝓞 F) O c * q) * algebraMap (𝓞 F) O n by
    rw [mul_comm n c, map_mul, mul_assoc, Algebra.commutes n q, ← mul_assoc]]
  exact J.mul_mem_left _ hn

/-- **The local-global principle for left ideals containing $n$:** if $n \in J_2$ and $J_{1,v} \subseteq J_{2,v}$ for all $v \mid n$, then
$J_1 \subseteq J_2$.

*Proof.* For $x \in J_1$ and $v \mid n$ approximate: $x - y_v \in \varpi_v^{e_v}\mathcal O$ with $y_v \in J_2$ (`exists_approx_mem`,
`exists_eq_genP_pow_smul`). With CRT idempotents $t_v$, $x = (1 - \sum t_v)x + \sum_v\big(t_vy_v + t_v\varpi_v^{e_v}w_v\big)$ and
$n \mid 1 - \sum t_v$, $n \mid t_v\varpi_v^{e_v}$. -/


@[simp] theorem coe_toLocal (v : HeightOneSpectrum (𝓞 F)) (x : O) :
    ((toLocal (a := a) (b := b) (O := O) v x : localOrder (v := v) a b O) : QuatV v a b) =
      complHom v a b (x : QuatF F a b) := rfl

theorem toLocal_mem_localIdeal (v : HeightOneSpectrum (𝓞 F)) {J : Ideal O} {x : O} (hx : x ∈ J) :
    toLocal v x ∈ localIdeal (v := v) J :=
  complHom_mem_span_idealImage hx

/-- **The global left ideal with prescribed completions** $\{x \in \mathcal O : \iota_v(x) \in I_v\ \forall v \in S\}$. -/

theorem mem_globalIdeal {S : Finset (HeightOneSpectrum (𝓞 F))}
    {I : ∀ v : HeightOneSpectrum (𝓞 F), Ideal (localOrder (v := v) a b O)} {x : O} :
    x ∈ globalIdeal S I ↔ ∀ v ∈ S, toLocal v x ∈ I v := by
  simp only [globalIdeal, Submodule.mem_iInf]; rfl


/-- A left ideal of $\mathcal O_v$ contains the $\mathfrak o_v$-span of its elements' images (it is an $\mathfrak o_v$-module). -/
theorem span_le_of_forall_mem (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (localOrder (v := v) a b O)}
    {T : Set (QuatV v a b)} (hT : ∀ q ∈ T, ∃ h : q ∈ localOrder (v := v) a b O, (⟨q, h⟩ : localOrder (v := v) a b O) ∈ I)
    {y : localOrder (v := v) a b O} (hy : (y : QuatV v a b) ∈ Submodule.span (v.adicCompletionIntegers F) T) :
    y ∈ I := by
  have key : ∀ q ∈ Submodule.span (v.adicCompletionIntegers F) T,
      ∃ h : q ∈ localOrder (v := v) a b O, (⟨q, h⟩ : localOrder (v := v) a b O) ∈ I := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq => exact hT q hq
    | zero => exact ⟨Subalgebra.zero_mem _, by convert I.zero_mem⟩
    | add q r _ _ hq hr =>
      obtain ⟨h1, h1'⟩ := hq; obtain ⟨h2, h2'⟩ := hr
      exact ⟨Subalgebra.add_mem _ h1 h2, by convert I.add_mem h1' h2'⟩
    | smul c q _ hq =>
      obtain ⟨h1, h1'⟩ := hq
      refine ⟨Subalgebra.smul_mem _ h1 c, ?_⟩
      have : (⟨c • q, Subalgebra.smul_mem _ h1 c⟩ : localOrder (v := v) a b O) =
          algebraMap _ (localOrder (v := v) a b O) c * ⟨q, h1⟩ := by
        apply Subtype.ext
        rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← Algebra.smul_def]
      rw [this]; exact I.mul_mem_left _ h1'
  obtain ⟨h, hI⟩ := key _ hy
  exact hI


/-- $\mathfrak p_v^e\mathcal O$ as an $\mathcal O_F$-submodule of $D$ (the span of $y\,o$, $y \in \mathfrak p_v^e$, $o \in \mathcal O$). -/
def powSmul (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) (O : Subalgebra (𝓞 F) (QuatF F a b)) : Submodule (𝓞 F) (QuatF F a b) :=
  Submodule.span (𝓞 F) {u | ∃ y ∈ v.asIdeal ^ e, ∃ o ∈ O, u = y • o}

theorem smul_mem_powSmul {v : HeightOneSpectrum (𝓞 F)} {e : ℕ} {y : 𝓞 F} (hy : y ∈ v.asIdeal ^ e) {o : QuatF F a b}
    (ho : o ∈ O) : y • o ∈ powSmul v e O :=
  Submodule.subset_span ⟨y, hy, o, ho, rfl⟩

theorem exists_add_mul_eq_one (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {s : 𝓞 F} (hs : s ∉ v.asIdeal) :
    ∃ t ∈ v.asIdeal ^ k, ∃ r : 𝓞 F, t + r * s = 1 := by
  have hsup1 : v.asIdeal ⊔ Ideal.span {s} = ⊤ := by
    by_contra hne
    have := v.isMaximal.eq_of_le hne le_sup_left
    exact hs (this ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hsup : v.asIdeal ^ k ⊔ Ideal.span {s} = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.1 (Ideal.isCoprime_iff_sup_eq.2 hsup1).pow_left
  obtain ⟨t, ht, r', hr', htr⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 F) ∈ _)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hr'
  exact ⟨t, ht, r, by rw [hr, htr]⟩

/-- **Coordinates without a global basis:** if $w \in \mathcal O$ and $\iota_v(w) \in \varpi_v^e\mathcal O_v$ then
$w \in \mathfrak p_v^e\mathcal O$ (the replacement of `exists_eq_genP_pow_smul`; uses a local frame at $v$ and the coprimality of
$\mathfrak p_v^e$ with the denominators prime to $v$). -/
theorem mem_pow_smul_order (v : HeightOneSpectrum (𝓞 F)) {e : ℕ} {w : QuatF F a b}
    (hO : IsOrder (𝓞 F) F O) (hw : w ∈ O) {z : QuatV v a b} (hz : z ∈ localOrder (v := v) a b O)
    (hwz : complHom v a b w = (π v ^ e) • z) :
    w ∈ powSmul v e O := by
  classical
  obtain ⟨L⟩ := LocFrame.exists (v := v) hO
  have hc : ∀ i, v.valuation F (L.fb.repr w i) ≤ WithZero.exp (-(e : ℤ)) := by
    intro i
    obtain ⟨t, ht⟩ := (L.mem_localOrder_iff z).1 hz i
    have h1 : algebraMap F (v.adicCompletion F) (L.fb.repr w i) =
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (π v ^ e * t) := by
      rw [← LocFrame.cb_repr_complHom, hwz, ← algebraMap_smul (v.adicCompletion F) (π v ^ e) z, map_smul,
        Finsupp.smul_apply, smul_eq_mul, ← ht, map_mul, map_pow]
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change Valued.v (algebraMap F (v.adicCompletion F) (L.fb.repr w i)) ≤ _
    rw [h1]
    have : Valued.v (((π v ^ e * t : v.adicCompletionIntegers F)) : v.adicCompletion F) =
        WithZero.exp (-(e : ℤ)) * Valued.v ((t : v.adicCompletionIntegers F) : v.adicCompletion F) := by
      rw [MulMemClass.coe_mul, map_mul, SubmonoidClass.coe_pow, map_pow, valued_π, ← WithZero.exp_nsmul]
      congr 2; simp
    change Valued.v (((π v ^ e * t : v.adicCompletionIntegers F)) : v.adicCompletion F) ≤ _
    rw [this]
    calc _ ≤ WithZero.exp (-(e : ℤ)) * 1 := mul_le_mul' le_rfl t.2
      _ = _ := mul_one _
  have hint : ∀ i, v.valuation F (L.fb.repr w i) ≤ 1 := fun i =>
    (hc i).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; simp)
  choose n d hnd using fun i => HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (L.fb.repr w i) (hint i)
  set D : 𝓞 F := ∏ i, (d i : 𝓞 F) with hD
  have hDmem : D ∉ v.asIdeal := by
    have : D ∈ v.asIdeal.primeCompl := by
      rw [hD, ← Submonoid.coe_finsetProd]
      exact (∏ i, d i).2
    exact this
  have hm : ∀ i, ∃ m : 𝓞 F, m ∈ v.asIdeal ^ e ∧
      algebraMap (𝓞 F) F m = algebraMap (𝓞 F) F D * L.fb.repr w i := by
    intro i
    have h := hnd i
    change L.fb.repr w i * algebraMap (𝓞 F) F (d i : 𝓞 F) = algebraMap (𝓞 F) F (n i) at h
    have hne : n i ∈ v.asIdeal ^ e := by
      have e1 : v.valuation F (algebraMap (𝓞 F) F (n i)) = v.intValuation (n i) :=
        HeightOneSpectrum.valuation_of_algebraMap v _
      have e2 : v.valuation F (algebraMap (𝓞 F) F (d i : 𝓞 F)) = v.intValuation (d i : 𝓞 F) :=
        HeightOneSpectrum.valuation_of_algebraMap v _
      rw [← v.intValuation_le_pow_iff_mem, ← e1, ← h, map_mul, e2]
      have h1 : v.intValuation (d i : 𝓞 F) = 1 := (v.intValuation_eq_one_iff_mem_primeCompl _).2 (d i).2
      rw [h1, mul_one]
      exact hc i
    refine ⟨(∏ j ∈ Finset.univ.erase i, (d j : 𝓞 F)) * n i, Ideal.mul_mem_left _ _ hne, ?_⟩
    rw [map_mul, ← h, hD, ← Finset.mul_prod_erase Finset.univ (fun j => (d j : 𝓞 F)) (Finset.mem_univ i), map_mul]
    ring
  choose m hmp hmF using hm
  have hDw : D • w ∈ powSmul v e O := by
    have : D • w = ∑ i, m i • L.fb i := by
      conv_lhs => rw [← L.fb.sum_repr w]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul F D, ← algebraMap_smul F (m i), smul_smul, hmF i]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => smul_mem_powSmul (hmp i) (L.mem i)
  obtain ⟨t, ht, r, htr⟩ := exists_add_mul_eq_one v e hDmem
  have : w = t • w + r • (D • w) := by
    rw [smul_smul, ← add_smul, htr, one_smul]
  rw [this]
  exact Submodule.add_mem _ (smul_mem_powSmul ht hw) (Submodule.smul_mem _ _ hDw)


theorem cI_span_eq_zero_of_not_mem {v : HeightOneSpectrum (𝓞 F)} {n : 𝓞 F} (hn : n ≠ 0) (hv : n ∉ v.asIdeal) :
    cI v (Ideal.span {n}) = 0 := by
  have h𝔫 : Ideal.span {n} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hn
  by_contra hc
  apply hv
  have h1 := le_pow_cI v h𝔫 (Ideal.mem_span_singleton_self n)
  exact Ideal.pow_le_self hc h1

/-- A multiple of `n` by an element lying in `𝔭_w^{c_w(n)}` for every `w ∣ n` lies in `(n)`. -/
theorem mem_span_of_forall_mem_pow {n : 𝓞 F} (hn : n ≠ 0) {r : 𝓞 F}
    (h : ∀ w ∈ primeSupport hn, r ∈ w.asIdeal ^ cI w (Ideal.span {n})) : n ∣ r := by
  have h𝔫 : Ideal.span {n} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hn
  rw [← Ideal.mem_span_singleton, mem_iff_forall_cI h𝔫]
  intro w
  by_cases hw : n ∈ w.asIdeal
  · exact h w ((mem_primeSupport hn).2 hw)
  · rw [cI_span_eq_zero_of_not_mem hn hw, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top

/-- **Multiples of `t_v` of elements of `𝔭_v^e O` lie in `J₂`** when `n ∈ J₂` and `t_v` vanishes to the right order at the other primes. -/
theorem smul_mem_of_mem_powSmul {n : 𝓞 F} (hn : n ≠ 0) {J₂ : Ideal O} (hn2 : algebraMap (𝓞 F) O n ∈ J₂)
    {v : HeightOneSpectrum (𝓞 F)} {t : 𝓞 F}
    (ht : ∀ w ∈ primeSupport hn, w ≠ v → t ∈ w.asIdeal ^ cI w (Ideal.span {n}))
    {u : QuatF F a b} (hu : u ∈ powSmul v (cI v (Ideal.span {n})) O) :
    ∃ hu' : u ∈ O, t • (⟨u, hu'⟩ : O) ∈ J₂ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, o, ho, rfl⟩ := hu
    refine ⟨O.smul_mem ho y, ?_⟩
    have : t • (⟨y • o, O.smul_mem ho y⟩ : O) = (t * y) • (⟨o, ho⟩ : O) := by
      apply Subtype.ext; simp only [Subalgebra.coe_smul]; exact (mul_smul t y o).symm
    rw [this]
    refine smul_mem_of_dvd hn2 (mem_span_of_forall_mem_pow hn fun w hw => ?_) _
    by_cases hwv : w = v
    · subst hwv; exact Ideal.mul_mem_left _ _ hy
    · exact Ideal.mul_mem_right _ _ (ht w hw hwv)
  | zero =>
    refine ⟨O.zero_mem, ?_⟩
    have : (⟨0, O.zero_mem⟩ : O) = 0 := rfl
    rw [this, smul_zero]; exact J₂.zero_mem
  | add u u' _ _ hu hu' =>
    obtain ⟨h1, h1'⟩ := hu; obtain ⟨h2, h2'⟩ := hu'
    refine ⟨O.add_mem h1 h2, ?_⟩
    have : t • (⟨u + u', O.add_mem h1 h2⟩ : O) = t • (⟨u, h1⟩ : O) + t • (⟨u', h2⟩ : O) := by
      rw [← smul_add]; rfl
    rw [this]; exact J₂.add_mem h1' h2'
  | smul c u _ hu =>
    obtain ⟨h1, h1'⟩ := hu
    refine ⟨O.smul_mem h1 c, ?_⟩
    have : t • (⟨c • u, O.smul_mem h1 c⟩ : O) = algebraMap (𝓞 F) O c * (t • (⟨u, h1⟩ : O)) := by
      rw [← Algebra.smul_def, smul_comm]; rfl
    rw [this]; exact J₂.mul_mem_left _ h1'

/-- **The local-global principle for left ideals containing $n$** (basis-free): if $n \in J_2$ and $J_{1,v} \subseteq J_{2,v}$ for all
$v \mid n$, then $J_1 \subseteq J_2$.

Source: Voight 2021, Thm. 9.4.9. -/
@[kb "voight2021" "Thm. 9.4.9"]
theorem le_of_localIdeal_le (hO : IsOrder (𝓞 F) F O) {n : 𝓞 F} (hn : n ≠ 0) {J₁ J₂ : Ideal O}
    (hn2 : algebraMap (𝓞 F) O n ∈ J₂)
    (h : ∀ v ∈ primeSupport hn, localIdeal (v := v) J₁ ≤ localIdeal (v := v) J₂) : J₁ ≤ J₂ := by
  classical
  intro x hx
  set S := primeSupport hn
  set 𝔫 : Ideal (𝓞 F) := Ideal.span {n} with h𝔫def
  have hloc : ∀ v ∈ S, ∃ y : O, y ∈ J₂ ∧ ((x : QuatF F a b) - y) ∈ powSmul v (cI v 𝔫) O := by
    intro v hv
    have hxv : complHom v a b (x : QuatF F a b) ∈
        Submodule.span (v.adicCompletionIntegers F) (idealImage (v := v) J₂) :=
      (mem_localIdeal_iff).1 (h v hv (show (⟨_, mem_localOrder_of_mem a b x.2⟩ : localOrder (v := v) a b O) ∈
        localIdeal (v := v) J₁ from complHom_mem_span_idealImage hx))
    obtain ⟨y, hyJ, z, hz, hxyz⟩ := exists_approx_mem v hxv (cI v 𝔫)
    exact ⟨y, hyJ, mem_pow_smul_order v hO (O.sub_mem x.2 y.2) hz hxyz⟩
  choose! y hyJ hxy using hloc
  have hcrt := fun v => exists_crt_idem S (fun u => cI u 𝔫) v
  choose t ht1 ht0 using hcrt
  have hdiv1 : n ∣ 1 - ∑ v ∈ S, t v := by
    refine mem_span_of_forall_mem_pow hn fun u hu => ?_
    have : 1 - ∑ v ∈ S, t v = -(t u - 1) - ∑ v ∈ S.erase u, t v := by
      rw [← Finset.add_sum_erase S t hu]; ring
    rw [this]
    exact Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 (ht1 u))
      (Ideal.sum_mem _ fun v hv => ht0 v u hu (Finset.ne_of_mem_erase hv).symm)
  have hterm : ∀ v ∈ S, t v • x = t v • y v + t v • (x - y v) := fun v _ => by rw [← smul_add, add_sub_cancel]
  have key : x = (1 - ∑ v ∈ S, t v) • x + ∑ v ∈ S, (t v • y v + t v • (x - y v)) := by
    rw [← Finset.sum_congr rfl hterm, sub_smul, one_smul, Finset.sum_smul, sub_add_cancel]
  rw [key]
  refine J₂.add_mem (smul_mem_of_dvd hn2 hdiv1 x) (J₂.sum_mem fun v hv => J₂.add_mem ?_ ?_)
  · rw [Algebra.smul_def]; exact J₂.mul_mem_left _ (hyJ v hv)
  · obtain ⟨hu', hmem⟩ := smul_mem_of_mem_powSmul hn hn2 (v := v) (t := t v)
      (fun w hw hwv => ht0 v w hw hwv) (hxy v hv)
    exact hmem

theorem span_ι_eq_cI (v : HeightOneSpectrum (𝓞 F)) {n : 𝓞 F} (hn : n ≠ 0) :
    Ideal.span {ι v n} = Ideal.span {π v ^ cI v (Ideal.span {n})} := by
  have h𝔫 : Ideal.span {n} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hn
  have := map_ι_eq_span v h𝔫
  rwa [Ideal.map_span, Set.image_singleton] at this

set_option maxHeartbeats 1000000 in
/-- **Existence of a global ideal with prescribed completions** (CRT, basis-free): if $\iota_v(n) \in I_v$ for $v \in S$ (the places
dividing $n$), then the completions of `globalIdeal S I` are the $I_v$ ($v \in S$). -/
@[kb "voight2021" "Thm. 9.4.9"]
theorem localIdeal_globalIdeal (hO : IsOrder (𝓞 F) F O) {n : 𝓞 F} (hn : n ≠ 0)
    (I : ∀ v : HeightOneSpectrum (𝓞 F), Ideal (localOrder (v := v) a b O))
    (hI : ∀ v ∈ primeSupport hn, algebraMap _ (localOrder (v := v) a b O) (ι v n) ∈ I v)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ primeSupport hn) :
    localIdeal (v := v) (globalIdeal (primeSupport hn) I) = I v := by
  classical
  set S := primeSupport hn
  have hnJ : algebraMap (𝓞 F) O n ∈ globalIdeal S I := mem_globalIdeal.2 fun w hw => by
    have : toLocal w (algebraMap (𝓞 F) O n) = algebraMap _ (localOrder (v := w) a b O) (ι w n) :=
      Subtype.ext (by rw [coe_toLocal, Subalgebra.coe_algebraMap, complHom_algebraMap]; rfl)
    rw [this]; exact hI w hw
  apply le_antisymm
  · intro y hy
    refine span_le_of_forall_mem v (T := idealImage (v := v) (globalIdeal S I)) ?_ hy
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_localOrder_of_mem a b x.2, mem_globalIdeal.1 hx v hv⟩
  · intro y hy
    obtain ⟨L⟩ := LocFrame.exists (v := v) hO
    set Eb := L.cb
    have hEi : ∀ (w : HeightOneSpectrum (𝓞 F)) (i : Fin 4), complHom w a b (L.fb i : QuatF F a b) ∈ localOrder (v := w) a b O :=
      fun w i => mem_localOrder_of_mem a b (L.mem i)
    have hd := (L.mem_localOrder_iff (y : QuatV v a b)).1 y.2
    choose d hd using hd
    -- approximate the coordinates at v, and make them vanish to order e_w at the other w ∈ S
    have h0 := fun i => exists_ι_sub_mem_span v (cI v (Ideal.span {n})) (d i)
    choose r0 hr0 using h0
    obtain ⟨t, ht1, ht0⟩ := exists_crt_idem S (fun u => cI u (Ideal.span {n})) v
    set r : Fin 4 → 𝓞 F := fun i => t * r0 i
    obtain ⟨x, hxdef⟩ : ∃ x : O, x = ∑ i, r i • (⟨L.fb i, L.mem i⟩ : O) := ⟨_, rfl⟩
    -- coefficients in (ι_w n) at every w ∈ S
    have hcoef_w : ∀ w ∈ S, w ≠ v → ∀ i, ι w (r i) ∈ Ideal.span {ι w n} := by
      intro w hw hwv i
      rw [span_ι_eq_cI w hn, ι_mem_span_π_pow]
      exact Ideal.mul_mem_right _ _ (ht0 w hw hwv)
    have hcoef_v : ∀ i, ι v (r i) - d i ∈ Ideal.span {ι v n} := by
      intro i
      rw [span_ι_eq_cI v hn]
      have e1 : ι v (t - 1) ∈ Ideal.span {π v ^ cI v (Ideal.span {n})} := (ι_mem_span_π_pow v _ _).2 (ht1)
      have : ι v (r i) - d i = ι v (t - 1) * ι v (r0 i) - (d i - ι v (r0 i)) := by
        simp only [r, map_mul, map_sub, map_one]; ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ e1) (hr0 i)
    have hloc_x : ∀ w, toLocal w x = ∑ i, ι w (r i) • (⟨complHom w a b (L.fb i : QuatF F a b), hEi w i⟩ :
        localOrder (v := w) a b O) := by
      intro w
      apply Subtype.ext
      rw [coe_toLocal, hxdef, AddSubmonoidClass.coe_finsetSum, map_sum, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Subalgebra.coe_smul, Subalgebra.coe_smul]
      erw [complHom_int_smul]
    have hy_sum : y = ∑ i, d i • (⟨complHom v a b (L.fb i : QuatF F a b), hEi v i⟩ : localOrder (v := v) a b O) := by
      apply Subtype.ext
      rw [← Eb.sum_repr (y : QuatV v a b), AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Subalgebra.coe_smul, ← hd i, algebraMap_smul, LocFrame.cb_apply]; rfl
    have hdiff : toLocal v x - y = ∑ i, (ι v (r i) - d i) • (⟨complHom v a b (L.fb i : QuatF F a b), hEi v i⟩ :
        localOrder (v := v) a b O) := by
      rw [hloc_x, hy_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    have hxJ : x ∈ globalIdeal S I := by
      rw [mem_globalIdeal]
      intro w hw
      by_cases hwv : w = v
      · subst hwv
        have : toLocal w x = y + (toLocal w x - y) := by abel
        rw [this, hdiff]
        exact (I w).add_mem hy ((I w).sum_mem fun i _ => smul_mem_of_algebraMap_mem w (hI w hw) (hcoef_v i) _)
      · rw [hloc_x]
        exact (I w).sum_mem fun i _ => smul_mem_of_algebraMap_mem w (hI w hw) (hcoef_w w hw hwv i) _
    have : y = toLocal v x - (toLocal v x - y) := by abel
    rw [this, hdiff]
    refine Ideal.sub_mem _ (toLocal_mem_localIdeal v hxJ) ((localIdeal (v := v) _).sum_mem fun i _ => ?_)
    exact smul_mem_of_algebraMap_mem v (algebraMap_mem_localIdeal v hnJ) (hcoef_v i) _

end LocalGlobal

section Completions

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

instance finite_quot_π_pow (b : ℕ) : Finite (𝔬 ⧸ Ideal.span {π v ^ b}) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_quot_π_pow]
    exact pow_ne_zero _ ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).2
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot)))

theorem matOrderEquiv_apply (X : Matrix (Fin 2) (Fin 2) 𝔬) :
    ((matOrderEquiv (v := v) X : matOrder 𝔬 Fv) : Matrix (Fin 2) (Fin 2) Fv) = X.map (algebraMap 𝔬 Fv) := rfl

/-- **The split local count:** at a finite place $v$ where $D_v \cong M_2(F_v)$, the completion $\mathcal O_v$ of a maximal order has
exactly $\sum_{b=0}^k(N\mathfrak p_v)^b$ left ideals of reduced norm $\mathfrak p_v^k$.

Source: Voight 2021, Lemma 26.4.1(b) (right ideals there; left ideals here, by transposition). -/
@[kb "voight2021" "Lemma 26.4.1"]
theorem card_localOrder_ideal_split {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsMaximalOrder (𝓞 F) F O)
    (hsplit : Nonempty (QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv)) (k : ℕ) :
    Nat.card {I : Ideal (localOrder (v := v) a b O) // leftNrdIdeal I = Ideal.span {π v ^ k}} =
      ∑ i ∈ Finset.range (k + 1), Ideal.absNorm v.asIdeal ^ i := by
  obtain ⟨φ, hφ⟩ := exists_algEquiv_localOrder_eq_matOrder_nf hO hsplit
  -- ψ : O_v ≃ M_2(𝔬)
  let e1 := (φ.restrictScalars 𝔬).subalgebraMap (localOrder (v := v) a b O)
  let e2 := Subalgebra.equivOfEq _ _ hφ
  let ψ : localOrder (v := v) a b O ≃+* Matrix (Fin 2) (Fin 2) 𝔬 :=
    ((e1.trans e2).trans (matOrderEquiv (v := v)).symm).toRingEquiv
  have hψ : ∀ x : localOrder (v := v) a b O, algebraMap 𝔬 Fv (ψ x).det = nrd (x : QuatV v a b) := by
    intro x
    have h1 : ((matOrderEquiv (v := v) (ψ x) : matOrder 𝔬 Fv) : Matrix (Fin 2) (Fin 2) Fv) = φ x := by
      change ((matOrderEquiv (v := v) ((matOrderEquiv (v := v)).symm (e2 (e1 x))) : matOrder 𝔬 Fv) :
        Matrix (Fin 2) (Fin 2) Fv) = φ x
      rw [AlgEquiv.apply_symm_apply]; rfl
    rw [← det_algEquiv φ, ← h1, matOrderEquiv_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [Nat.card_congr ((leftIdealEquivOfRingEquiv ψ (IsFractionRing.injective 𝔬 Fv) hψ _).trans
    (matIdealEquiv (irreducible_π v) k)), Nat.card_sigma, Fin.sum_univ_eq_sum_range
      (fun b => Nat.card (𝔬 ⧸ Ideal.span {π v ^ b})) (k + 1)]
  exact Finset.sum_congr rfl fun b _ => card_quot_π_pow v b

/-- **The ramified local count:** at a finite place $v$ where $D_v$ is a division algebra, the completion $\mathcal O_v$ of a maximal
order has exactly one left ideal of each reduced norm $\mathfrak p_v^k$.

Source: Voight 2021, Lemma 26.4.1 (ramified case). -/
@[kb "voight2021" "Lemma 26.4.1"]
theorem card_localOrder_ideal_ramified (ha : a ≠ 0) (hb : b ≠ 0) {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) (hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0) (k : ℕ) :
    Nat.card {I : Ideal (localOrder (v := v) a b O) // leftNrdIdeal I = Ideal.span {π v ^ k}} = 1 := by
  have heq := localOrder_eq_valOrder_nf ha hb hO hdiv
  have hπ0 : algebraMap 𝔬 Fv (π v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (irreducible_π v).ne_zero
  obtain ⟨y, hy⟩ := QuadFormsKB.Quat.exists_nrd_eq_finite' (a := (a : F)) (b := (b : F))
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha)
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb) v hπ0
  rw [← card_valOrder_ideal (R := 𝔬) hdiv hy k]
  have key : ∀ O₁ O₂ : Subalgebra 𝔬 (QuatV v a b), O₁ = O₂ →
      Nat.card {I : Ideal O₁ // leftNrdIdeal I = Ideal.span {π v ^ k}} =
        Nat.card {I : Ideal O₂ // leftNrdIdeal I = Ideal.span {π v ^ k}} := by
    rintro _ _ rfl; rfl
  exact key _ _ heq

/-- $D$ is ramified at the finite place $v$ (`Quat.IsRamifiedAt`) iff $D_v$ has no nonzero element of reduced norm $0$. -/
theorem isRamifiedAt_finite_iff :
    IsRamifiedAt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) (NFPlace.finite v) ↔
      ∀ x : QuatV v a b, nrd x = 0 → x = 0 := by
  change (∀ x : QuatV v a b, x ≠ 0 → IsUnit x) ↔ _
  constructor
  · intro h x hx
    by_contra h0
    exact (isUnit_iff_nrd_ne_zero x).1 (h x h0) hx
  · intro h x hx
    exact (isUnit_iff_nrd_ne_zero x).2 fun h0 => hx (h x h0)

open Classical in
/-- **The local ideal counts of a maximal order** ($\mathcal O_F$ a PID, $ab \ne 0$): for every finite place $v$ and $k \ge 0$,
$$a_v(k) = \#\{I \subseteq \mathcal O_v \text{ left ideal} : \operatorname{nrd}(I) = \mathfrak p_v^k\} =
  \begin{cases}1 & v \in \operatorname{Ram}(D),\\ \sum_{i=0}^k(N\mathfrak p_v)^i & \text{otherwise.}\end{cases}$$

Source: Voight 2021, Lemma 26.4.1 and (26.3.13). -/
@[kb "voight2021" "Lemma 26.4.1"]
theorem card_localOrder_ideal (ha : a ≠ 0) (hb : b ≠ 0) {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) (k : ℕ) :
    Nat.card {I : Ideal (localOrder (v := v) a b O) // leftNrdIdeal I = Ideal.span {π v ^ k}} =
      if IsRamifiedAt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) (NFPlace.finite v) then 1
      else ∑ i ∈ Finset.range (k + 1), Ideal.absNorm v.asIdeal ^ i := by
  split_ifs with h
  · exact card_localOrder_ideal_ramified ha hb hO (isRamifiedAt_finite_iff.1 h) k
  · rw [isRamifiedAt_finite_iff] at h
    push Not at h
    obtain ⟨x, hx0, hx⟩ := h
    have ha' : algebraMap 𝔬 Fv (ι v a) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v ha)
    have hb' : algebraMap 𝔬 Fv (ι v b) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).2 (ι_ne_zero v hb)
    have h2 := two_ne_zero_of_algebra (F := F) Fv
    exact card_localOrder_ideal_split hO ((nonempty_algEquiv_matrix_iff h2 ha' hb').2
      ((hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha' hb').2 ⟨x, hx, hx0⟩)) k

end Completions


section ByIdeal

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

theorem famExt_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))}
    {I : (v : S) → Ideal (localOrder (v := v.1) a b O)} {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ S) :
    famExt S I v = I ⟨v, h⟩ := by
  simp only [famExt, h, dite_true]

theorem algebraMap_mem_globalIdeal {S : Finset (HeightOneSpectrum (𝓞 F))}
    {I : ∀ v : HeightOneSpectrum (𝓞 F), Ideal (localOrder (v := v) a b O)} {n : 𝓞 F}
    (hI : ∀ v ∈ S, algebraMap _ (localOrder (v := v) a b O) (ι v n) ∈ I v) :
    algebraMap (𝓞 F) O n ∈ globalIdeal S I := mem_globalIdeal.2 fun w hw => by
  have : toLocal w (algebraMap (𝓞 F) O n) = algebraMap _ (localOrder (v := w) a b O) (ι w n) :=
    Subtype.ext (by rw [coe_toLocal, Subalgebra.coe_algebraMap, complHom_algebraMap]; rfl)
  rw [this]; exact hI w hw


theorem cI_eq_zero_of_mem_not_mem {v : HeightOneSpectrum (𝓞 F)} {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) {n : 𝓞 F}
    (hn𝔫 : n ∈ 𝔫) (hnv : n ∉ v.asIdeal) : cI v 𝔫 = 0 := by
  by_contra hc
  exact hnv (Ideal.pow_le_self hc (le_pow_cI v h𝔫 hn𝔫))

/-- A local ideal of reduced norm $(\varpi_v^{c_v(\mathfrak n)})$ contains $\iota_v(n)$ for $n \in \mathfrak n$. -/
theorem algebraMap_mem_of_nrd_eq (hO : IsOrder (𝓞 F) F O) (v : HeightOneSpectrum (𝓞 F)) {𝔫 : Ideal (𝓞 F)}
    (h𝔫 : 𝔫 ≠ ⊥) {n : 𝓞 F} (hn𝔫 : n ∈ 𝔫) {I : Ideal (localOrder (v := v) a b O)}
    (hI : leftNrdIdeal I = Ideal.span {π v ^ cI v 𝔫}) :
    algebraMap _ (localOrder (v := v) a b O) (ι v n) ∈ I := by
  have h1 : algebraMap _ (localOrder (v := v) a b O) (π v ^ cI v 𝔫) ∈ I :=
    algebraMap_mem_of_mem_leftNrdIdeal (R := v.adicCompletionIntegers F) (isOrder_localOrder_gen v hO) I
      (by rw [hI]; exact Ideal.mem_span_singleton_self _)
  have h2 : ι v n ∈ Ideal.span {π v ^ cI v 𝔫} := (ι_mem_span_π_pow v _ _).2 (le_pow_cI v h𝔫 hn𝔫)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h2
  rw [← hu, map_mul]
  exact I.mul_mem_left _ h1

/-- The family of local ideals of reduced norm $(\varpi_v^{c_v(\mathfrak n)})$, $v \mid n$. -/
abbrev LocalFamN (𝔫 : Ideal (𝓞 F)) {n : 𝓞 F} (hn : n ≠ 0) (O : Subalgebra (𝓞 F) (QuatF F a b)) :=
  (v : primeSupport hn) → {I : Ideal (localOrder (v := v.1) a b O) // leftNrdIdeal I = Ideal.span {π v.1 ^ cI v.1 𝔫}}

/-- The global ideal attached to a family of local ideals. -/
def globalOfFamN {𝔫 : Ideal (𝓞 F)} {n : 𝓞 F} (hn : n ≠ 0) (I : LocalFamN 𝔫 hn O) : Ideal O :=
  globalIdeal (primeSupport hn) (famExt (primeSupport hn) fun v => (I v).1)

theorem famExt_algebraMap_memN (hO : IsOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) {n : 𝓞 F} (hn : n ≠ 0)
    (hn𝔫 : n ∈ 𝔫) (I : LocalFamN 𝔫 hn O) :
    ∀ v ∈ primeSupport hn, algebraMap _ (localOrder (v := v) a b O) (ι v n) ∈
      famExt (primeSupport hn) (fun v => (I v).1) v := fun v hv => by
  rw [famExt_of_mem hv]; exact algebraMap_mem_of_nrd_eq hO v h𝔫 hn𝔫 (I ⟨v, hv⟩).2

theorem localIdeal_globalOfFamN (hO : IsOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) {n : 𝓞 F} (hn : n ≠ 0)
    (hn𝔫 : n ∈ 𝔫) (I : LocalFamN 𝔫 hn O) (v : primeSupport hn) :
    localIdeal (v := v.1) (globalOfFamN hn I) = (I v).1 := by
  rw [globalOfFamN, localIdeal_globalIdeal hO hn _ (famExt_algebraMap_memN hO h𝔫 hn hn𝔫 I) v.1 v.2,
    famExt_of_mem v.2]

theorem leftNrdIdeal_top_localOrder (v : HeightOneSpectrum (𝓞 F)) :
    leftNrdIdeal (⊤ : Ideal (localOrder (v := v) a b O)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨1, Submodule.mem_top, by simp [nrd]⟩

/-- **The reduced norm of $\mathrm{globalOfFamN}$ is $\mathfrak n$.** -/
theorem leftNrdIdeal_globalOfFamN (hO : IsOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) {n : 𝓞 F} (hn : n ≠ 0)
    (hn𝔫 : n ∈ 𝔫) (I : LocalFamN 𝔫 hn O) : leftNrdIdeal (globalOfFamN hn I) = 𝔫 := by
  have hnJ : algebraMap (𝓞 F) O n ∈ globalOfFamN hn I :=
    algebraMap_mem_globalIdeal (famExt_algebraMap_memN hO h𝔫 hn hn𝔫 I)
  have hne : leftNrdIdeal (globalOfFamN hn I) ≠ ⊥ := by
    intro hbot
    have hmem : n ^ 2 ∈ leftNrdIdeal (globalOfFamN hn I) := Ideal.subset_span ⟨_, hnJ, by
      rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply (𝓞 F) F (QuatF F a b), nrd_algebraMap,
        map_pow]⟩
    rw [hbot] at hmem
    exact hn (pow_eq_zero_iff (by norm_num) |>.1 ((Ideal.mem_bot).1 hmem))
  refine eq_of_map_eq hne h𝔫 fun v => ?_
  rw [← leftNrdIdeal_localIdeal hO, map_ι_eq_span v h𝔫]
  by_cases hv : v ∈ primeSupport hn
  · have := localIdeal_globalOfFamN hO h𝔫 hn hn𝔫 I ⟨v, hv⟩
    rw [globalOfFamN] at this ⊢
    simp only at this
    rw [this]
    exact (I ⟨v, hv⟩).2
  · have hnv : n ∉ v.asIdeal := fun h => hv ((mem_primeSupport hn).2 h)
    rw [localIdeal_eq_top v hnJ hnv, leftNrdIdeal_top_localOrder, cI_eq_zero_of_mem_not_mem h𝔫 hn𝔫 hnv, pow_zero,
      Ideal.span_singleton_one]

/-- The family of completions of a left ideal of reduced norm $\mathfrak n$. -/
def famOfIdealN (hO : IsOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) {n : 𝓞 F} (hn : n ≠ 0)
    (J : {J : Ideal O // leftNrdIdeal J = 𝔫}) : LocalFamN 𝔫 hn O := fun v =>
  ⟨localIdeal (v := v.1) J.1, by rw [leftNrdIdeal_localIdeal hO, J.2, map_ι_eq_span v.1 h𝔫]⟩

theorem globalOfFamN_famOfIdealN (hO : IsOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) {n : 𝓞 F} (hn : n ≠ 0)
    (hn𝔫 : n ∈ 𝔫) (J : {J : Ideal O // leftNrdIdeal J = 𝔫}) :
    globalOfFamN hn (famOfIdealN hO h𝔫 hn J) = J.1 := by
  have hnJ : algebraMap (𝓞 F) O n ∈ J.1 :=
    algebraMap_mem_of_mem_leftNrdIdeal hO J.1 (by rw [J.2]; exact hn𝔫)
  have hnJ' := algebraMap_mem_globalIdeal (famExt_algebraMap_memN hO h𝔫 hn hn𝔫 (famOfIdealN hO h𝔫 hn J))
  have hleq : ∀ v ∈ primeSupport hn, localIdeal (v := v) (globalOfFamN hn (famOfIdealN hO h𝔫 hn J)) =
      localIdeal (v := v) J.1 := fun v hv => localIdeal_globalOfFamN hO h𝔫 hn hn𝔫 _ ⟨v, hv⟩
  exact le_antisymm (le_of_localIdeal_le hO hn hnJ fun v hv => (hleq v hv).le)
    (le_of_localIdeal_le hO hn hnJ' fun v hv => (hleq v hv).ge)

/-- **The local-global correspondence for left ideals of given reduced norm $\mathfrak n$** (any class number; $0 \ne n \in \mathfrak n$):
$$\{J \subseteq \mathcal O : \operatorname{nrd}(J) = \mathfrak n\} \;\simeq\; \prod_{v \mid n}\{I \subseteq \mathcal O_v : \operatorname{nrd}(I) = \mathfrak p_v^{c_v(\mathfrak n)}\}.$$

Source: Voight 2021, Thm. 9.4.9, Lemma 9.5.3, §26.4 (first display) and Prop. 26.3.9. -/
@[kb "voight2021" "Thm. 9.4.9"]
def idealLocalEquivN (hO : IsOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) {n : 𝓞 F} (hn : n ≠ 0) (hn𝔫 : n ∈ 𝔫) :
    {J : Ideal O // leftNrdIdeal J = 𝔫} ≃ LocalFamN 𝔫 hn O where
  toFun := famOfIdealN hO h𝔫 hn
  invFun I := ⟨globalOfFamN hn I, leftNrdIdeal_globalOfFamN hO h𝔫 hn hn𝔫 I⟩
  left_inv J := Subtype.ext (globalOfFamN_famOfIdealN hO h𝔫 hn hn𝔫 J)
  right_inv I := funext fun v => Subtype.ext (localIdeal_globalOfFamN hO h𝔫 hn hn𝔫 I v)

open Classical in
/-- **The number of left ideals of a maximal order with reduced norm $\mathfrak n$** (any class number, $ab \ne 0$, $\mathfrak n \ne 0$,
$0 \ne n \in \mathfrak n$): $\#\{J : \operatorname{nrd}(J) = \mathfrak n\} = \prod_{v \mid n}a_v(c_v(\mathfrak n))$, $a_v(k) = 1$ at the ramified places,
$\sum_{i \le k}(N\mathfrak p_v)^i$ elsewhere.

Source: Voight 2021, Prop. 26.3.9, (26.3.12), Lemma 26.4.1, Cor. 26.4.7; Thm. 9.4.9. -/
@[kb "voight2021" "Prop. 26.3.9; Lemma 26.4.1"]
theorem card_ideal_nrd_eq_N (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥)
    {n : 𝓞 F} (hn : n ≠ 0) (hn𝔫 : n ∈ 𝔫) :
    Nat.card {J : Ideal O // leftNrdIdeal J = 𝔫} =
      ∏ v ∈ primeSupport hn,
        (if IsRamifiedAt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) (NFPlace.finite v) then 1
          else ∑ i ∈ Finset.range (cI v 𝔫 + 1), Ideal.absNorm v.asIdeal ^ i) := by
  rw [Nat.card_congr (idealLocalEquivN hO.1 h𝔫 hn hn𝔫), Nat.card_pi, ← Finset.prod_coe_sort (primeSupport hn)]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact card_localOrder_ideal ha hb hO (cI v.1 𝔫)

end ByIdeal

end Gen

end QuadFormsKB.QuatOrder
