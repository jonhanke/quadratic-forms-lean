/-
# The Picard group of an order: the exact sequence at $\mathrm{Pic}(R)$ (Neukirch I (12.9)–(12.11))

**Setting** as in `OrderPicSetup.lean`: $\mathcal O = \mathcal O_E$, $R\subseteq\mathcal O$ a subalgebra over $\mathcal O_F$,
$\mathfrak m\ne0$ an ideal of $\mathcal O$ with $\mathfrak m\subseteq R$; fractional ideals live in $E$.

**Defines**
* `phi0`: $(\mathcal O/\mathfrak m)^\times\to\{\text{invertible fractional ideals of }R\}$, $a \bmod \mathfrak m\mapsto aR+\mathfrak m$;
* `phi`: its composite with the class map, $(\mathcal O/\mathfrak m)^\times\to\mathrm{Cl}(R)$ (Mathlib's `ClassGroup R`, invertible
  fractional ideals modulo principal ones, i.e. $\mathrm{Pic}(R)$);
* `psi`: $\mathrm{Cl}(R)\to\mathrm{Cl}(\mathcal O)$, $[I]\mapsto[I\mathcal O]$.

**Proves** (unconditional)
* `exists_unit_pair`: if $II' = R$ then there are $u\in I$, $v\in I'$ with $uv\in R$ a unit modulo $\mathfrak m$
  (the Chinese remainder theorem in the finite ring $R/(\mathfrak m\cap R)$);
* `range_phi_eq_ker_psi`: $\operatorname{im}\varphi = \ker\psi$.

Source: Neukirch, *Algebraic Number Theory*, Ch. I, §12, proof of (12.9)–(12.11), pp. 78–79.
-/
import QuadFormsKB.Literature.Hanke2011Structure.OrderPicIdeals

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure.OrderCN

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {R : Subalgebra (𝓞 F) (𝓞 E)} {𝔪 : Ideal (𝓞 E)}

local notation "ι" => algebraMap (𝓞 E) E

/-- A representative in $\mathcal O$ of a class modulo $\mathfrak m$. -/
def rep (x : 𝓞 E ⧸ 𝔪) : 𝓞 E := Classical.choose (Ideal.Quotient.mk_surjective x)

theorem mk_rep (x : 𝓞 E ⧸ 𝔪) : Ideal.Quotient.mk 𝔪 (rep x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

theorem sub_mem_of_mk_eq {a b : 𝓞 E} (h : Ideal.Quotient.mk 𝔪 a = Ideal.Quotient.mk 𝔪 b) : a - b ∈ 𝔪 :=
  Ideal.Quotient.eq.mp h

theorem rep_mul_sub_one (u : (𝓞 E ⧸ 𝔪)ˣ) : rep (u : 𝓞 E ⧸ 𝔪) * rep ((u⁻¹ : (𝓞 E ⧸ 𝔪)ˣ) : 𝓞 E ⧸ 𝔪) - 1 ∈ 𝔪 :=
  sub_mem_of_mk_eq (by rw [map_mul, mk_rep, mk_rep, map_one, Units.mul_inv])

variable [IsFractionRing R E]

theorem idealA_rep_mul (hR : ∀ x ∈ 𝔪, x ∈ R) (u : (𝓞 E ⧸ 𝔪)ˣ) :
    idealA R 𝔪 (rep (u : 𝓞 E ⧸ 𝔪)) * idealA R 𝔪 (rep ((u⁻¹ : (𝓞 E ⧸ 𝔪)ˣ) : 𝓞 E ⧸ 𝔪)) = 1 := by
  rw [idealA_mul hR _ _ (c := rep (u : 𝓞 E ⧸ 𝔪)) (by rw [mul_comm]; exact rep_mul_sub_one u),
    idealA_congr hR (rep_mul_sub_one u), idealA_one hR]

variable (R 𝔪) in
/-- **$a\bmod\mathfrak m\mapsto aR+\mathfrak m$**, $(\mathcal O/\mathfrak m)^\times\to$ invertible fractional ideals of $R$. -/
def phi0 (hR : ∀ x ∈ 𝔪, x ∈ R) : (𝓞 E ⧸ 𝔪)ˣ →* (FractionalIdeal R⁰ E)ˣ where
  toFun u := ⟨idealA R 𝔪 (rep (u : 𝓞 E ⧸ 𝔪)), idealA R 𝔪 (rep ((u⁻¹ : (𝓞 E ⧸ 𝔪)ˣ) : 𝓞 E ⧸ 𝔪)),
    idealA_rep_mul hR u, by simpa using idealA_rep_mul hR u⁻¹⟩
  map_one' := Units.ext <| by
    show idealA R 𝔪 _ = 1
    rw [idealA_congr hR (a' := 1) (sub_mem_of_mk_eq (by simp [mk_rep])), idealA_one hR]
  map_mul' u v := Units.ext <| by
    show idealA R 𝔪 _ = idealA R 𝔪 _ * idealA R 𝔪 _
    rw [idealA_mul hR _ _ (rep_mul_sub_one v)]
    exact idealA_congr hR (sub_mem_of_mk_eq (by rw [mk_rep, map_mul, mk_rep, mk_rep, Units.val_mul]))

theorem coe_phi0 (hR : ∀ x ∈ 𝔪, x ∈ R) (u : (𝓞 E ⧸ 𝔪)ˣ) :
    (phi0 R 𝔪 hR u : FractionalIdeal R⁰ E) = idealA R 𝔪 (rep (u : 𝓞 E ⧸ 𝔪)) := rfl

variable (R 𝔪) in
/-- **$\varphi$**: $(\mathcal O/\mathfrak m)^\times\to\mathrm{Cl}(R)$, $a\mapsto[aR+\mathfrak m]$. -/
def phi (hR : ∀ x ∈ 𝔪, x ∈ R) : (𝓞 E ⧸ 𝔪)ˣ →* ClassGroup R :=
  (ClassGroup.mk E).comp (phi0 R 𝔪 hR)

/-! ### $\psi$: extension of classes to $\mathcal O$ -/

/-- $\mathcal O\cdot(R\text{-span of }x) = \mathcal O x$. -/
theorem extendedHom_spanSingleton' (x : E) :
    FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) (FractionalIdeal.spanSingleton R⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ x := by
  rw [← FractionalIdeal.coeToSubmodule_inj, coe_extendedHom, FractionalIdeal.coe_spanSingleton]
  show Submodule.span (𝓞 E) ((Submodule.span R {x} : Submodule R E) : Set E) = _
  exact Submodule.span_span_of_tower _ _ _

theorem extU_principal_le :
    (toPrincipalIdeal R E).range ≤ ((ClassGroup.mk E).comp (extU R)).ker := by
  rintro _ ⟨x, rfl⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff]
  have : ((extU R (toPrincipalIdeal R E x) : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) =
      Submodule.span (𝓞 E) {(x : E)} := by
    show ((FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E)
      (toPrincipalIdeal R E x : FractionalIdeal R⁰ E) : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) = _
    rw [coe_toPrincipalIdeal, extendedHom_spanSingleton', FractionalIdeal.coe_spanSingleton]
  rw [this]
  exact ⟨⟨_, rfl⟩⟩

variable (R) in
/-- **$\psi$**: $\mathrm{Cl}(R)\to\mathrm{Cl}(\mathcal O)$, $[I]\mapsto[I\mathcal O]$. -/
def psi : ClassGroup R →* ClassGroup (𝓞 E) :=
  (QuotientGroup.lift (toPrincipalIdeal R E).range ((ClassGroup.mk E).comp (extU R)) extU_principal_le).comp
    (ClassGroup.equiv (R := R) E).toMonoidHom

theorem psi_mk (I : (FractionalIdeal R⁰ E)ˣ) : psi R (ClassGroup.mk E I) = ClassGroup.mk E (extU R I) := by
  simp only [psi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ClassGroup.equiv_mk,
    FractionalIdeal.canonicalEquiv_self]
  erw [QuotientGroup.lift_mk']

theorem coe_extU (I : (FractionalIdeal R⁰ E)ˣ) :
    (extU R I : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) (I : FractionalIdeal R⁰ E) := rfl

theorem psi_phi (hR : ∀ x ∈ 𝔪, x ∈ R) (u : (𝓞 E ⧸ 𝔪)ˣ) : psi R (phi R 𝔪 hR u) = 1 := by
  rw [phi, MonoidHom.comp_apply, psi_mk]
  have : extU R (phi0 R 𝔪 hR u) = 1 := Units.ext <| by
    rw [coe_extU, coe_phi0, Units.val_one]
    exact extendedHom_idealA hR _ (rep_mul_sub_one u)
  rw [this, map_one]

/-! ### A pair $u\in I$, $v\in I^{-1}$ with $uv$ a unit modulo $\mathfrak m$ -/

/-- An element of a commutative ring lying in no maximal ideal is a unit. -/
theorem isUnit_of_forall_notMem {A : Type*} [CommRing A] {x : A}
    (h : ∀ P : Ideal A, P.IsMaximal → x ∉ P) : IsUnit x := by
  by_contra hx
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {x}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  exact h M hM (hle (Ideal.mem_span_singleton_self x))

/-- **If $II' = R$, some $u\in I$, $v\in I'$ have $uv = w\in R$ with $w$ a unit modulo $\mathfrak m$** ($ww'-1\in\mathfrak m$ for
some $w'\in R$). For every maximal ideal $P$ of the finite ring $A = R/(\mathfrak m\cap R)$ some product $u_Pv_P\notin P$ (the
products span $R\ni1$); with $e_P\in R$ lying in every other maximal ideal but not in $P$, the element
$uv = (\sum_P e_Pu_P)(\sum_Q e_Qv_Q)$ is $\equiv e_P^2u_Pv_P\not\equiv0$ modulo each $P$, hence a unit of $A$. -/
theorem exists_unit_pair (hm : 𝔪 ≠ ⊥) {I I' : FractionalIdeal R⁰ E} (h : I * I' = 1) :
    ∃ u ∈ I, ∃ v ∈ I', ∃ w w' : R, u * v = algebraMap R E w ∧ ((w * w' : R) : 𝓞 E) - 1 ∈ 𝔪 := by
  classical
  have : Finite (𝓞 E ⧸ 𝔪) := finite_quot hm
  have : Finite (R ⧸ idealIn R 𝔪) :=
    Finite.of_injective _ (Ideal.quotientMap_injective (I := 𝔪) (f := R.val.toRingHom))
  let q : R →+* R ⧸ idealIn R 𝔪 := Ideal.Quotient.mk (idealIn R 𝔪)
  have hprod : ∀ u ∈ I, ∀ v ∈ I', ∃ r : R, algebraMap R E r = u * v := fun u hu v hv =>
    (FractionalIdeal.mem_one_iff R⁰).mp (h ▸ FractionalIdeal.mul_mem_mul hu hv)
  have : Finite (Ideal (R ⧸ idealIn R 𝔪)) :=
    Finite.of_injective (fun P : Ideal (R ⧸ idealIn R 𝔪) => (P : Set (R ⧸ idealIn R 𝔪))) SetLike.coe_injective
  let s : Finset (Ideal (R ⧸ idealIn R 𝔪)) := (Set.toFinite {P | P.IsMaximal}).toFinset
  have hs : ∀ P, P ∈ s ↔ P.IsMaximal := fun P => by simp [s]
  have hpair : ∀ P ∈ s, ∃ u ∈ I, ∃ v ∈ I', ∃ r : R, algebraMap R E r = u * v ∧ q r ∉ P := by
    intro P hP
    have hPm := (hs P).mp hP
    by_contra hcon
    push Not at hcon
    have h1 : (1 : E) ∈ I.1 * I'.1 := by
      have h1' : (1 : E) ∈ (I * I').1 := by
        rw [h]; exact (FractionalIdeal.mem_one_iff R⁰).mpr ⟨1, map_one _⟩
      exact (FractionalIdeal.coe_mul I I') ▸ h1'
    have key : ∃ r : R, algebraMap R E r = 1 ∧ q r ∈ P := by
      refine Submodule.mul_induction_on (C := fun z => ∃ r : R, algebraMap R E r = z ∧ q r ∈ P) h1
        (fun u hu v hv => ?_) (fun x y hx hy => ?_)
      · obtain ⟨r, hr⟩ := hprod u hu v hv
        exact ⟨r, hr, hcon u hu v hv r hr⟩
      · obtain ⟨r, rfl, hr⟩ := hx
        obtain ⟨r', rfl, hr'⟩ := hy
        exact ⟨r + r', map_add _ _ _, by rw [map_add]; exact P.add_mem hr hr'⟩
    obtain ⟨r, hr, hrP⟩ := key
    have : r = 1 := algebraMap_R_E_injective R (by rw [hr, map_one])
    rw [this, map_one] at hrP
    exact hPm.ne_top ((Ideal.eq_top_iff_one P).mpr hrP)
  choose! uf huf vf hvf rf hrf hrfP using hpair
  have hsep : ∀ P ∈ s, ∃ e : R, q e ∉ P ∧ ∀ Q ∈ s, Q ≠ P → q e ∈ Q := by
    intro P hP
    have hPm := (hs P).mp hP
    have hnle : ¬ (s.erase P).inf id ≤ P := by
      rw [hPm.isPrime.inf_le']
      rintro ⟨Q, hQ, hQP⟩
      exact (Finset.mem_erase.mp hQ).1 (((hs Q).mp (Finset.mem_erase.mp hQ).2).eq_of_le hPm.ne_top hQP)
    obtain ⟨a, ha, haP⟩ := Set.not_subset.mp hnle
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨e, haP, fun Q hQ hQP =>
      (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hQP, hQ⟩) : (s.erase P).inf id ≤ id Q) ha⟩
  choose! ef hef hefQ using hsep
  have hcross : ∀ P ∈ s, ∀ Q ∈ s, ∃ r : R, algebraMap R E r = uf P * vf Q := fun P hP Q hQ =>
    hprod _ (huf P hP) _ (hvf Q hQ)
  choose! rr hrr using hcross
  let w : R := ∑ P ∈ s, ∑ Q ∈ s, ef P * ef Q * rr P Q
  have hw : (∑ P ∈ s, algebraMap R E (ef P) * uf P) * (∑ Q ∈ s, algebraMap R E (ef Q) * vf Q) =
      algebraMap R E w := by
    rw [Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [map_mul, map_mul, hrr P hP Q hQ]
    ring
  have hunit : IsUnit (q w) := by
    refine isUnit_of_forall_notMem fun P0 hP0m => ?_
    have hP0 : P0 ∈ s := (hs P0).mpr hP0m
    have hrr0 : rr P0 P0 = rf P0 := algebraMap_R_E_injective R (by rw [hrr P0 hP0 P0 hP0, hrf P0 hP0])
    have hterm : q (ef P0 * ef P0 * rr P0 P0) ∉ P0 := by
      rw [hrr0, map_mul, map_mul]
      exact hP0m.isPrime.mul_notMem (hP0m.isPrime.mul_notMem (hef P0 hP0) (hef P0 hP0)) (hrfP P0 hP0)
    have hrest : q w - q (ef P0 * ef P0 * rr P0 P0) ∈ P0 := by
      have e1 : w = (∑ Q ∈ s, ef P0 * ef Q * rr P0 Q) +
          ∑ P ∈ s.erase P0, ∑ Q ∈ s, ef P * ef Q * rr P Q := (Finset.add_sum_erase s _ hP0).symm
      have e2 : ∑ Q ∈ s, ef P0 * ef Q * rr P0 Q = ef P0 * ef P0 * rr P0 P0 +
          ∑ Q ∈ s.erase P0, ef P0 * ef Q * rr P0 Q := (Finset.add_sum_erase s _ hP0).symm
      rw [e1, e2, map_add, map_add, add_assoc, add_sub_cancel_left, map_sum, map_sum]
      refine P0.add_mem (Ideal.sum_mem _ fun Q hQ => ?_) (Ideal.sum_mem _ fun P hP => ?_)
      · obtain ⟨hQP, hQs⟩ := Finset.mem_erase.mp hQ
        rw [map_mul, map_mul]
        exact P0.mul_mem_right _ (P0.mul_mem_left _ (hefQ Q hQs P0 hP0 (Ne.symm hQP)))
      · obtain ⟨hPP, hPs⟩ := Finset.mem_erase.mp hP
        rw [map_sum]
        refine Ideal.sum_mem _ fun Q _ => ?_
        rw [map_mul, map_mul]
        exact P0.mul_mem_right _ (P0.mul_mem_right _ (hefQ P hPs P0 hP0 (Ne.symm hPP)))
    intro hwP
    exact hterm (by simpa using P0.sub_mem hwP hrest)
  obtain ⟨y, hy⟩ := hunit.exists_right_inv
  obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨_, I.1.sum_mem fun P hP => fmul_mem I (ef P) (huf P hP), _,
    I'.1.sum_mem fun P hP => fmul_mem I' (ef P) (hvf P hP), w, w', hw, ?_⟩
  have : w * w' - 1 ∈ idealIn R 𝔪 := Ideal.Quotient.eq.mp (by rw [map_mul, map_one]; exact hy)
  simpa using this

/-! ### $\operatorname{im}\varphi = \ker\psi$ -/

theorem range_phi_le_ker_psi (hR : ∀ x ∈ 𝔪, x ∈ R) : (phi R 𝔪 hR).range ≤ (psi R).ker := by
  rintro _ ⟨u, rfl⟩
  exact psi_phi hR u

theorem ker_psi_le_range_phi (hm : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) : (psi R).ker ≤ (phi R 𝔪 hR).range := by
  intro c
  refine ClassGroup.induction (R := R) E (fun I hI => ?_) c
  rw [MonoidHom.mem_ker, psi_mk, ClassGroup.mk_eq_one_iff] at hI
  obtain ⟨x, hx⟩ := hI.principal
  have hxI : (extU R I : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ x := by
    rw [← FractionalIdeal.coeToSubmodule_inj, hx, FractionalIdeal.coe_spanSingleton]
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact (extU R I).ne_zero (by rw [hxI, map_zero])
  let xu : Eˣ := Units.mk0 x⁻¹ (inv_ne_zero hx0)
  let I₁ := I * toPrincipalIdeal R E xu
  have hI₁ : extU R I₁ = 1 := Units.ext <| by
    rw [map_mul, Units.val_mul, hxI, coe_extU, coe_toPrincipalIdeal, extendedHom_spanSingleton',
      Units.val_one, FractionalIdeal.spanSingleton_mul_spanSingleton]
    simp [xu, hx0]
  have hmk : ClassGroup.mk E I₁ = ClassGroup.mk E I := by
    have : ClassGroup.mk E (toPrincipalIdeal R E xu) = 1 := by
      rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
      exact ⟨⟨_, rfl⟩⟩
    rw [map_mul, this, mul_one]
  have hI₁' : FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) (I₁ : FractionalIdeal R⁰ E) = 1 :=
    congrArg Units.val hI₁
  have hI₁inv : FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) ((I₁⁻¹ : (FractionalIdeal R⁰ E)ˣ) :
      FractionalIdeal R⁰ E) = 1 := by
    have := congrArg Units.val (show extU R I₁⁻¹ = 1 by rw [map_inv, hI₁, inv_one])
    exact this
  obtain ⟨u, hu, v, hv, w, w', huv, hww'⟩ := exists_unit_pair hm (Units.mul_inv I₁)
  obtain ⟨u0, rfl⟩ := (le_of_extendedHom_eq_one hR hI₁').1 u hu
  obtain ⟨v0, rfl⟩ := (le_of_extendedHom_eq_one hR hI₁inv).1 v hv
  have huv0 : u0 * v0 = (w : 𝓞 E) := IsFractionRing.injective (𝓞 E) E (by rw [map_mul, huv, algebraMap_R_E])
  have hU : Ideal.Quotient.mk 𝔪 u0 * Ideal.Quotient.mk 𝔪 (v0 * w') = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔪)]
    refine Ideal.Quotient.eq.mpr ?_
    rw [← mul_assoc, huv0]
    simpa using hww'
  refine ⟨Units.mkOfMulEqOne _ _ hU, ?_⟩
  rw [← hmk, phi, MonoidHom.comp_apply]
  congr 1
  refine Units.ext ?_
  rw [coe_phi0, idealA_congr hR (a' := u0) (sub_mem_of_mk_eq (by rw [mk_rep]; rfl))]
  exact (idealA_eq_of_unit hR (Units.mul_inv I₁) hI₁' hu hv huv hww').symm

/-- **Exactness at $\mathrm{Cl}(R)$**: $\operatorname{im}\bigl((\mathcal O/\mathfrak m)^\times\to\mathrm{Cl}(R)\bigr) =
\ker\bigl(\mathrm{Cl}(R)\to\mathrm{Cl}(\mathcal O)\bigr)$ (Neukirch I (12.9)–(12.11)). -/
@[kb "neukirch1999" "Ch. I, (12.9)-(12.11), pp. 78-79 (exactness at Pic(R))"]
theorem range_phi_eq_ker_psi (hm : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) : (phi R 𝔪 hR).range = (psi R).ker :=
  le_antisymm (range_phi_le_ker_psi hR) (ker_psi_le_range_phi hm hR)

end

end QuadFormsKB.Hanke2011Structure.OrderCN

#print axioms QuadFormsKB.Hanke2011Structure.OrderCN.range_phi_eq_ker_psi
