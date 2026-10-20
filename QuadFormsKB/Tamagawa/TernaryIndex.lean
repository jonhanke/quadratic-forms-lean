/-
# $[SO(\hat{\mathcal O}^0) : K'] = 2^{\#\mathrm{Ram}_f}$ and the $SO$-mass of $\mathcal O^0$

**Layer:** as in `TernaryMass.lean`.

**Proves**
* the parity homomorphism $x \mapsto \operatorname{ord}_v\operatorname{nrd}(x) \bmod 2$ on $D_v^\times$ (`parD`), constant on the fibres of $c_v$;
* `TZFrame.relIndex_Kp_K0`: $[K_0 : K'] = 2^{\#\mathrm{Ram}_f(D)}$ ($K_0 = SO(\hat{\mathcal O}^0)$, $K' = \prod_vc_v(\mathcal O_v^\times)$): the map
  $K_0 \to \prod_{v\in\mathrm{Ram}_f}\mathbb Z/2$, $k \mapsto (\operatorname{ord}_v\operatorname{nrd}x_v)_v$ ($k_v = c_v(x_v)$) is onto with kernel $K'$;
* **`TZFrame.dcMass_SO_eq`**: $\mathrm{dcMass}(SO(V)(F), SO(\hat{\mathcal O}^0)) = 2^{-\#\mathrm{Ram}_f(D)}\sum_{[J]\ne0}[\Gamma_J:\mathcal O_F^\times]^{-1}$;
* **`TZFrame.tauSO_eq`**: $\tau(SO(\mathcal O^0)) = \mu_{\mathrm{Tam}}(K_{SO})\cdot2^{-\#\mathrm{Ram}_f}\sum_{[J]\ne0}[\Gamma_J:\mathcal O_F^\times]^{-1}$.

Source: Voight 2021, §§23.4, 26.5 (two-sided ideals and normalizers of local maximal orders); Weil 1982, §3.7(a).
-/
import QuadFormsKB.Tamagawa.TernaryMass

open NumberField IsDedekindDomain Matrix Quaternion WithZero MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O)

/-! ### The parity of the reduced norm -/

section Parity

variable (v : HeightOneSpectrum (𝓞 F))

/-- **The parity of $\operatorname{ord}_v\operatorname{nrd}x$**, as a homomorphism $D_v^\times \to \mathbb Z/2$ (multiplicatively). -/
def parD : (QuatV v a b)ˣ →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd ((WithZero.log (Valued.v (nrd (x : QuatV v a b))) : ℤ) : ZMod 2)
  map_one' := by rw [Units.val_one, nrd_one, map_one]; simp
  map_mul' x y := by
    rw [Units.val_mul, nrd_mul, map_mul, WithZero.log_mul ((map_ne_zero _).2 (nrd_units_ne_zero x))
      ((map_ne_zero _).2 (nrd_units_ne_zero y)), Int.cast_add, ofAdd_add]

theorem parD_apply (x : (QuatV v a b)ˣ) :
    parD v x = Multiplicative.ofAdd ((WithZero.log (Valued.v (nrd (x : QuatV v a b))) : ℤ) : ZMod 2) := rfl

theorem parD_qScalar {r : v.adicCompletion F} (hr : r ≠ 0) : parD (a := a) (b := b) v (qScalar r hr) = 1 := by
  rw [parD_apply, coe_qScalar]
  have : nrd (algebraMap (v.adicCompletion F) (QuatV v a b) r) = r ^ 2 := by
    simp [nrd, QuaternionAlgebra.algebraMap_eq]; try ring
  rw [this, map_pow]
  obtain ⟨k, hk⟩ := exists_valued_eq_exp v hr
  rw [hk, ← WithZero.exp_nsmul, WithZero.log_exp]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, Int.cast_mul, Int.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, ofAdd_zero]

theorem parD_eq_of_cvv_eq (ha : a ≠ 0) {x y : (QuatV v a b)ˣ} (h : fr.cvv v x = fr.cvv v y) : parD v x = parD v y := by
  have ha' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v ha)
  obtain ⟨r, hr⟩ := (cvHom_eq_iff (two_ne_zero_Fv v) ha' (fr.PGv v) x y).1 (congrArg Subtype.val h)
  have hr0 : r ≠ 0 := by rintro rfl; exact x.ne_zero (by rw [hr, map_zero, zero_mul])
  have hxy : x = qScalar r hr0 * y := Units.ext (by rw [Units.val_mul, coe_qScalar]; exact hr)
  rw [hxy, map_mul, parD_qScalar, one_mul]

theorem parD_eq_one_of_mem_unitsOv (hO : IsOrder (𝓞 F) F O) {u : (QuatV v a b)ˣ} (hu : u ∈ unitsOv (O := O) v) :
    parD v u = 1 := by
  have hOv := isOrder_localOrder (v := v) hO
  obtain ⟨t, ht⟩ := (isInteger_trd_nrd hOv hu.1).2
  obtain ⟨t', ht'⟩ := (isInteger_trd_nrd hOv hu.2).2
  have h1 : Valued.v (nrd (u : QuatV v a b)) ≤ 1 := by
    rw [← ht]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 t.2
  have h2 : Valued.v (nrd ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)) ≤ 1 := by
    rw [← ht']; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 t'.2
  have hmul : nrd (u : QuatV v a b) * nrd ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) = 1 := by
    rw [← nrd_mul, Units.mul_inv, nrd_one]
  have h3 : Valued.v (nrd (u : QuatV v a b)) = 1 := by
    refine le_antisymm h1 ?_
    by_contra hlt
    push Not at hlt
    have hprod := congrArg Valued.v hmul
    rw [map_mul, map_one] at hprod
    have hlt2 : Valued.v (nrd (u : QuatV v a b)) * Valued.v (nrd ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [hprod] at hlt2
    exact lt_irrefl _ hlt2
  rw [parD_apply, h3]
  simp

end Parity

/-! ### Split and ramified places via $\mathrm{Ram}_f$ -/

section Places

variable (v : HeightOneSpectrum (𝓞 F))

theorem hdiv_of_mem_ramFin (ha : a ≠ 0) (hb : b ≠ 0) (hv : v ∈ ramFin ha hb) :
    ∀ x : QuatV v a b, nrd x = 0 → x = 0 := by
  have h := (mem_ramFin ha hb).1 hv
  intro x hx
  by_contra h0
  exact (isUnit_iff_nrd_ne_zero x).1 (h x h0) hx

theorem split_of_not_mem_ramFin (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) (hv : v ∉ ramFin ha hb) :
    ∃ φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F),
      (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
        (v.adicCompletionIntegers F)) = matOrder (v.adicCompletionIntegers F) (v.adicCompletion F) := by
  rcases localOrder_ramified_or_split (v := v) ha hb hO with ⟨hd, -⟩ | h
  · exfalso; apply hv
    rw [mem_ramFin]
    intro x hx
    exact (isUnit_iff_nrd_ne_zero x).2 fun h0 => hx (hd x h0)
  · exact h

theorem TZFrame.exists_cvv_eq (ha : a ≠ 0) (hb : b ≠ 0) (g : orthGroup fr.QF (v.adicCompletion F))
    (hg : g ∈ soSub fr.QF (v.adicCompletion F)) : ∃ y : (QuatV v a b)ˣ, fr.cvv v y = g := by
  have hmem := (mem_orthGroup fr.QF).1 g.2
  rw [fr.hessian_QF_map v] at hmem
  have ha' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v ha)
  have hb' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v hb)
  obtain ⟨α, hα⟩ := exists_cvHom_eq (two_ne_zero_Fv v) ha' hb' (fr.PGv v) _ hmem hg
  exact ⟨α, Subtype.ext hα⟩

end Places

/-! ### The index $[K_0 : K']$ -/

section Index

/-- **The parity map** $K_0 \to \prod_{v \in \mathrm{Ram}_f}\mathbb Z/2$, $k \mapsto (\operatorname{ord}_v\operatorname{nrd}x_v \bmod 2)_v$ for
$k_v = c_v(x_v)$. -/
def TZFrame.chi (ha : a ≠ 0) (hb : b ≠ 0) : fr.K0 →* ((ramFin ha hb) → Multiplicative (ZMod 2)) where
  toFun k := fun w => parD w.1 (Classical.choose (fr.exists_cvv_eq w.1 ha hb ((((k : fr.K0) : soAf fr.QF) :
    OAf fr.QF) w.1) ((((k : fr.K0) : soAf fr.QF)).2 w.1)))
  map_one' := by
    funext w
    have h := Classical.choose_spec (fr.exists_cvv_eq w.1 ha hb ((((1 : fr.K0) : soAf fr.QF) : OAf fr.QF) w.1)
      ((((1 : fr.K0) : soAf fr.QF)).2 w.1))
    simp only [OneMemClass.coe_one, RestrictedProduct.one_apply] at h
    rw [Pi.one_apply, parD_eq_of_cvv_eq fr w.1 ha (h.trans (map_one _).symm), map_one]
  map_mul' k l := by
    funext w
    have hk := Classical.choose_spec (fr.exists_cvv_eq w.1 ha hb ((((k : fr.K0) : soAf fr.QF) : OAf fr.QF) w.1)
      ((((k : fr.K0) : soAf fr.QF)).2 w.1))
    have hl := Classical.choose_spec (fr.exists_cvv_eq w.1 ha hb ((((l : fr.K0) : soAf fr.QF) : OAf fr.QF) w.1)
      ((((l : fr.K0) : soAf fr.QF)).2 w.1))
    have hkl := Classical.choose_spec (fr.exists_cvv_eq w.1 ha hb ((((k * l : fr.K0) : soAf fr.QF) : OAf fr.QF) w.1)
      ((((k * l : fr.K0) : soAf fr.QF)).2 w.1))
    rw [Pi.mul_apply, ← map_mul]
    apply parD_eq_of_cvv_eq fr w.1 ha
    rw [hkl, map_mul, hk, hl]
    simp only [Subgroup.coe_mul, RestrictedProduct.mul_apply]

theorem TZFrame.chi_apply (ha : a ≠ 0) (hb : b ≠ 0) (k : fr.K0) (w : ramFin ha hb) {y : (QuatV w.1 a b)ˣ}
    (hy : fr.cvv w.1 y = (((k : fr.K0) : soAf fr.QF) : OAf fr.QF) w.1) : fr.chi ha hb k w = parD w.1 y := by
  have h := Classical.choose_spec (fr.exists_cvv_eq w.1 ha hb ((((k : fr.K0) : soAf fr.QF) : OAf fr.QF) w.1)
      ((((k : fr.K0) : soAf fr.QF)).2 w.1))
  exact parD_eq_of_cvv_eq fr w.1 ha (h.trans hy.symm)

theorem ofAdd_eq_one_iff_even (k : ℤ) : Multiplicative.ofAdd ((k : ℤ) : ZMod 2) = 1 ↔ Even k := by
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
  norm_num

/-- **The kernel of the parity map is $K'$.** -/
theorem TZFrame.ker_chi (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) :
    (fr.chi ha hb).ker = fr.Kp.subgroupOf fr.K0 := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro h v
    by_cases hv : v ∈ ramFin ha hb
    · obtain ⟨y, hy⟩ := fr.exists_cvv_eq v ha hb ((((k : fr.K0) : soAf fr.QF) : OAf fr.QF) v)
        ((((k : fr.K0) : soAf fr.QF)).2 v)
      have h1 := congrFun h ⟨v, hv⟩
      rw [fr.chi_apply ha hb k ⟨v, hv⟩ hy, Pi.one_apply, parD_apply] at h1
      have hdiv := hdiv_of_mem_ramFin v ha hb hv
      have heq := localOrder_eq_valOrder ha hb hO hdiv
      obtain ⟨m, hm⟩ := exists_valued_eq_exp v (nrd_units_ne_zero y)
      rw [hm, WithZero.log_exp, ofAdd_eq_one_iff_even] at h1
      rw [← hy]
      exact (fr.cvv_mem_Kv_iff_even v hdiv heq ha y m hm).2 h1
    · obtain ⟨φ, hφ⟩ := split_of_not_mem_ramFin v ha hb hO hv
      obtain ⟨y, hy⟩ := fr.exists_cvv_eq v ha hb ((((k : fr.K0) : soAf fr.QF) : OAf fr.QF) v)
        ((((k : fr.K0) : soAf fr.QF)).2 v)
      have hk0 : (((k : fr.K0) : soAf fr.QF) : OAf fr.QF) ∈ locStab fr.QF (stdLat F 3) :=
        Subgroup.mem_subgroupOf.1 k.2
      have hst := (mem_locStab_intVec fr.QF _).1 hk0 v
      rw [← hy] at hst ⊢
      exact fr.mem_Kv_of_mem_stdStab_split v φ hφ ha y hst
  · intro h
    funext w
    obtain ⟨u, hu, huk⟩ := h w.1
    rw [fr.chi_apply ha hb k w huk, Pi.one_apply]
    exact parD_eq_one_of_mem_unitsOv w.1 hO.1 hu

/-- **The parity map is onto.** -/
theorem TZFrame.chi_surjective (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) :
    Function.Surjective (fr.chi ha hb) := by
  classical
  -- the elements t_w = c_w(Pw_w) at one ramified place
  have ht : ∀ w : ramFin ha hb, ∃ k : fr.K0, fr.chi ha hb k = Pi.mulSingle w (Multiplicative.ofAdd 1) := by
    intro w
    obtain ⟨Pw, hPw⟩ := exists_nrd_odd w.1 ha hb
    have hdiv := hdiv_of_mem_ramFin w.1 ha hb w.2
    have heq := localOrder_eq_valOrder ha hb hO hdiv
    obtain ⟨t, htdef⟩ : ∃ t : OAf fr.QF, t = RestrictedProduct.mulSingle _ w.1 (fr.cvv w.1 Pw) := ⟨_, rfl⟩
    have hts : t ∈ soAf fr.QF := by
      intro v
      by_cases hv : v = w.1
      · subst hv; rw [htdef, RestrictedProduct.mulSingle_eq_same]; exact fr.cvv_mem_soSub _ Pw
      · rw [htdef, RestrictedProduct.mulSingle_eq_of_ne _ _ hv]; exact (soSub fr.QF _).one_mem
    have htK : t ∈ locStab fr.QF (stdLat F 3) := by
      refine (mem_locStab_intVec fr.QF t).2 fun v => ?_
      by_cases hv : v = w.1
      · subst hv; rw [htdef, RestrictedProduct.mulSingle_eq_same]
        exact fr.cvv_mem_stdStab_ramified _ hdiv heq Pw
      · rw [htdef, RestrictedProduct.mulSingle_eq_of_ne _ _ hv]; exact (stdStab fr.QF v).one_mem
    refine ⟨⟨⟨t, hts⟩, Subgroup.mem_subgroupOf.2 htK⟩, ?_⟩
    funext w'
    by_cases hw : w' = w
    · subst hw
      rw [fr.chi_apply ha hb _ w' (y := Pw) (by show _ = t w'.1; rw [htdef]; exact (RestrictedProduct.mulSingle_eq_same (stdStab fr.QF) w'.1 _).symm), Pi.mulSingle_eq_same, parD_apply, hPw, WithZero.log_exp]
      rfl
    · have hw1 : w'.1 ≠ w.1 := fun h => hw (Subtype.ext h)
      rw [fr.chi_apply ha hb _ w' (y := 1) (by show _ = t w'.1; rw [htdef, map_one]; exact (RestrictedProduct.mulSingle_eq_of_ne (stdStab fr.QF) _ hw1).symm),
        Pi.mulSingle_eq_of_ne hw, map_one]
  intro f
  have hf : f = ∏ w, Pi.mulSingle w (f w) := (Finset.univ_prod_mulSingle f).symm
  have hmem : ∀ w, Pi.mulSingle w (f w) ∈ (fr.chi ha hb).range := by
    intro w
    have h2 : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by
      intro z
      obtain ⟨z, rfl⟩ := Multiplicative.ofAdd.surjective z
      fin_cases z
      · left; rfl
      · right; rfl
    rcases h2 (f w) with h | h
    · rw [h, Pi.mulSingle_one]; exact Subgroup.one_mem _
    · rw [h]; obtain ⟨k, hk⟩ := ht w; exact ⟨k, hk⟩
  have : f ∈ (fr.chi ha hb).range := by
    rw [hf]; exact Subgroup.prod_mem _ fun w _ => hmem w
  exact this

/-- **$[K_0 : K'] = 2^{\#\mathrm{Ram}_f(D)}$.** -/
theorem TZFrame.relIndex_Kp_K0 (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) :
    fr.Kp.relIndex fr.K0 = 2 ^ (ramFin ha hb).card := by
  rw [Subgroup.relIndex, ← fr.ker_chi ha hb hO, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (fr.chi_surjective ha hb hO), Subgroup.card_top, Nat.card_fun]
  simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

end Index

/-! ### The $SO$-mass of $\mathcal O^0$ and $\tau(SO(\mathcal O^0))$ -/

section Mass

variable [IsTotallyReal F]

/-- **The $SO$-mass of the ternary lattice $\mathcal O^0$** ($F$ totally real, $h_F = 1$, $D$ totally definite, $\mathcal O \supseteq
\mathcal O_F\langle1,i,j,k\rangle$ maximal):
$$\mathrm{dcMass}(SO(V)(F), SO(\hat{\mathcal O}^0)) = 2^{-\#\mathrm{Ram}_f(D)}\sum_{[J]\ne0}\frac{1}{[\Gamma_J:\mathcal O_F^\times]}.$$
(With `mass_SO_eq_two_mul_mass` this is $\mathrm{Mass}(\mathcal O^0) = 2^{-\#\mathrm{Ram}_f(D)-1}$ times Eichler's mass.) -/
@[kb "voight2021" "§26.5 (types and normalizers); Weil 1982, §3.7(a)"]
theorem TZFrame.dcMass_SO_eq (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) :
    dcMass fr.Gam fr.K0 = ((2 : ℝ) ^ (ramFin ha hb).card)⁻¹ * ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥},
      (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ := by
  classical
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  have : Finite (Quotient (idealSetoid O)) := finite_classes ha hb hO hdiv
  have : Finite {c : Quotient (idealSetoid O) // c.out ≠ ⊥} := Subtype.finite
  obtain ⟨Ψ, hw⟩ := fr.exists_orbitEquiv ha hb hdef hO
  have hfinKp : Finite (orbitRel.Quotient fr.Gam (soAf fr.QF ⧸ fr.Kp)) := Finite.of_equiv _ Ψ
  have hstabKp : ∀ x : soAf fr.QF ⧸ fr.Kp, Finite (stabilizer fr.Gam x) := by
    intro x
    set c := Ψ.symm (Quotient.mk'' x)
    have hc : Ψ c = Quotient.mk'' x := Ψ.apply_symm_apply _
    have hmem : (Ψ c).out ∈ orbit fr.Gam x := out_mem_orbit (Ψ c) x hc.symm
    have hcard := card_stabilizer_of_mem_orbit hmem
    rw [hw c] at hcard
    have : (centralUnitsIn (R := 𝓞 F) c.1.out).FiniteIndex := finiteIndex_centralUnitsIn (O := O) hdef hO.1 hstd c.2
    apply Nat.finite_of_card_ne_zero
    rw [← hcard]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hle : fr.Kp ≤ fr.K0 := fun x hx => Subgroup.mem_subgroupOf.2 (fr.KA_le_locStab (Subgroup.mem_subgroupOf.1 hx))
  have hrel := fr.relIndex_Kp_K0 ha hb hO
  have hrel0 : fr.Kp.relIndex fr.K0 ≠ 0 := by rw [hrel]; positivity
  have hK : fr.K0.Commensurable fr.Kp :=
    ⟨⟨by rw [Subgroup.relIndex_eq_one.2 hle]; exact one_ne_zero⟩, ⟨hrel0⟩⟩
  have : Finite (orbitRel.Quotient fr.Gam (soAf fr.QF ⧸ fr.K0)) := finite_orbits_of_commensurable _ _ _ hK
  have hstab0 := finite_stabilizer_of_commensurable fr.Gam fr.Kp fr.K0 hK hstabKp
  have h := dcMass_of_le fr.Gam hle hrel0 hstab0
  rw [fr.dcMass_Kp_eq ha hb hdef hO, hrel] at h
  rw [h]
  push_cast
  have h2 : (0 : ℝ) < 2 ^ (ramFin ha hb).card := by positivity
  field_simp

omit [IsPrincipalIdealRing (𝓞 F)] [IsTotallyReal F] in
theorem dcMass_SO_congr {Q Q' : QuadForm F 3} (h : Q = Q') :
    dcMass ((ratPoints Q).subgroupOf (soAf Q)) ((locStab Q (stdLat F 3)).subgroupOf (soAf Q)) =
      dcMass ((ratPoints Q').subgroupOf (soAf Q')) ((locStab Q' (stdLat F 3)).subgroupOf (soAf Q')) := by
  subst h; rfl

/-- **$\tau(SO(\mathcal O^0))$ in terms of Eichler's mass:** for a ternary $Q_0$ over $\mathcal O_F$ with $Q_0 \otimes F = Q_{\mathcal O^0}$,
$$\tau(SO(Q_0)) = \mu_{\mathrm{Tam}}(K_{SO})\cdot2^{-\#\mathrm{Ram}_f(D)}\sum_{[J]\ne0}\frac{1}{[\Gamma_J:\mathcal O_F^\times]}.$$ -/
theorem TZFrame.tauSO_eq (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) (Q₀ : QuadForm (𝓞 F) 3) (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    tauSO Q₀ = tamagawaK Q₀ * (((2 : ℝ) ^ (ramFin ha hb).card)⁻¹ *
      ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥}, (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹) := by
  unfold tauSO
  congr 1
  exact (dcMass_SO_congr hQ).trans (fr.dcMass_SO_eq ha hb hdef hO hstd)

end Mass

end QuadFormsKB.QuatOrder
