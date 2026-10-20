/-
# The $SO$-mass of $\mathcal O^0$ is $2^{-\#\mathrm{Ram}_f}$ times Eichler's mass

**Layer:** $F$ totally real with $\mathcal O_F$ a PID, $D = (a,b)_F$ totally definite, $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ a
maximal order with a trace-zero frame `fr` (`TernaryFrame.lean`), $Q = Q_{\mathcal O^0}$ the ternary norm form of $\mathcal O^0$ over $F$.
Inside $G = SO(V)(\mathbb A_f)$ (`soAf`) we have $\Gamma = SO(V)(F)$, $K_0 = SO(\hat{\mathcal O}^0)$ and
$K' = \prod_vc_v(\mathcal O_v^\times)$ (`TZFrame.KA`).

**Proves**
* `TZFrame.dcMass_KA_eq`: $\mathrm{dcMass}(\Gamma, K') = \sum_{[J]\ne0}[\Gamma_J:\mathcal O_F^\times]^{-1}$ (Eichler's mass): the double cosets
  $\Gamma\backslash G/K'$ are the left ideal classes ($J \mapsto (c_v(x_v)^{-1})_v$ for $J_v = \mathcal O_vx_v$), and the stabilizer of the
  coset of $J$ is $\Gamma_J/\mathcal O_F^\times$;
* `TZFrame.relIndex_KA`: $[K_0 : K'] = 2^{\#\mathrm{Ram}_f(D)}$;
* **`TZFrame.dcMass_SO_eq`**: $\mathrm{dcMass}(SO(V)(F), SO(\hat{\mathcal O}^0)) = 2^{-\#\mathrm{Ram}_f(D)}\sum_{[J]\ne0}[\Gamma_J:\mathcal O_F^\times]^{-1}$.

Source: Voight 2021, §§17.4–17.7, 25.3, 26.5 (classes, types, normalizers); Weil 1982, §3.7(a) ($SO_3 = D^\times/F^\times$) and
§2.4, p. 23 and Lemma 2.4.2, p. 26 (masses as volumes).
-/
import QuadFormsKB.Tamagawa.TernaryGlue

open NumberField IsDedekindDomain Matrix Quaternion WithZero MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O)

/-! ### The subgroup $K'$ and the rational points -/

/-- **$K' = \prod_v c_v(\mathcal O_v^\times)$** inside $O(V)(\mathbb A_f)$. -/
def TZFrame.KA : Subgroup (OAf fr.QF) where
  carrier := {g | ∀ v, g v ∈ fr.Kv v}
  mul_mem' {g h} hg hh v := (fr.Kv v).mul_mem (hg v) (hh v)
  one_mem' v := (fr.Kv v).one_mem
  inv_mem' {g} hg v := (fr.Kv v).inv_mem (hg v)

theorem TZFrame.mem_KA {g : OAf fr.QF} : g ∈ fr.KA ↔ ∀ v, g v ∈ fr.Kv v := Iff.rfl

theorem TZFrame.KA_le_soAf : fr.KA ≤ soAf fr.QF := fun g hg v => fr.Kv_le_soSub v (hg v)

theorem TZFrame.KA_le_locStab : fr.KA ≤ locStab fr.QF (stdLat F 3) := fun g hg =>
  (mem_locStab_intVec fr.QF g).2 fun v => fr.Kv_le_stdStab v (hg v)

theorem TZFrame.diagF_apply (γ : orthGroup fr.QF F) (v : HeightOneSpectrum (𝓞 F)) :
    (diagF fr.QF γ) v = orthMap fr.QF (v.adicCompletion F) γ := rfl

theorem TZFrame.diagF_cv0_apply (β : (QuatF F a b)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (diagF fr.QF (fr.cv0 β)) v = fr.cvv v (complUnits v β) := by
  rw [fr.diagF_apply, fr.orthMap_cv0]

theorem TZFrame.diagF_cv0_mem_soAf (β : (QuatF F a b)ˣ) : diagF fr.QF (fr.cv0 β) ∈ soAf fr.QF := fun v => by
  rw [fr.diagF_cv0_apply]; exact fr.cvv_mem_soSub v _

/-- **The rational points of $SO$ are the conjugations** $c(\beta)$, $\beta \in D^\times$. -/
theorem TZFrame.exists_cv0_of_mem (ha : a ≠ 0) (hb : b ≠ 0) {γ : OAf fr.QF} (hγ : γ ∈ ratPoints fr.QF)
    (hγs : γ ∈ soAf fr.QF) : ∃ β : (QuatF F a b)ˣ, γ = diagF fr.QF (fr.cv0 β) := by
  obtain ⟨γ₀, rfl⟩ := hγ
  obtain ⟨v₀⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
  have hdet : (γ₀ : GL (Fin 3) F).val.det = 1 := by
    have := hγs v₀
    rw [det_diagF] at this
    exact (algebraMap F (v₀.adicCompletion F)).injective (by rw [this, map_one])
  have hmem := (mem_orthGroup fr.QF).1 γ₀.2
  rw [fr.hessian_QF_map_self] at hmem
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb
  obtain ⟨β, hβ⟩ := exists_cvHom_eq two_ne_zero ha' hb' fr.PG (γ₀ : GL (Fin 3) F) hmem hdet
  refine ⟨β, ?_⟩
  congr 1
  exact Subtype.ext hβ.symm

/-! ### Local generators of a left ideal -/

/-- **$g$ is attached to $J$:** at every $v$, $J_v = \mathcal O_vx_v$ and $g_v = c_v(x_v)^{-1}$. -/
def TZFrame.IsGen (J : Ideal O) (g : OAf fr.QF) : Prop :=
  ∀ v, ∃ x : (QuatV v a b)ˣ, idealSet (localIdeal (v := v) J) =
    rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) (x : QuatV v a b) ∧ g v = (fr.cvv v x)⁻¹

theorem TZFrame.isGen_mem_soAf {J : Ideal O} {g : OAf fr.QF} (h : fr.IsGen J g) : g ∈ soAf fr.QF := fun v => by
  obtain ⟨x, -, hx⟩ := h v
  rw [hx]; exact (soSub fr.QF _).inv_mem (fr.cvv_mem_soSub v x)

theorem rTrans_localOrder_one (v : HeightOneSpectrum (𝓞 F)) :
    idealSet (⊤ : Ideal (localOrder (v := v) a b O)) =
      rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) ((1 : (QuatV v a b)ˣ) : QuatV v a b) := by
  rw [Units.val_one, rTrans_one, idealSet_top_local]

/-- **Every nonzero left ideal has attached elements** ($\mathcal O$ maximal). -/
theorem TZFrame.exists_isGen (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) : ∃ g : OAf fr.QF, fr.IsGen J g := by
  classical
  obtain ⟨ν, hν⟩ := (IsPrincipalIdealRing.principal (leftNrdIdeal J)).principal
  have hν' : leftNrdIdeal J = Ideal.span {ν} := by rw [hν]
  have hν0 : ν ≠ 0 := by rintro rfl; apply hJ; simp [hν']
  have hνJ : algebraMap (𝓞 F) O ν ∈ J :=
    algebraMap_mem_of_mem_leftNrdIdeal hO.1 J (by rw [hν']; exact Ideal.mem_span_singleton_self _)
  have hgen : ∀ v, ∃ x : (QuatV v a b)ˣ, idealSet (localIdeal (v := v) J) =
      rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) (x : QuatV v a b) ∧
      (ν ∉ v.asIdeal → x = 1) := by
    intro v
    by_cases hv : ν ∈ v.asIdeal
    · obtain ⟨α, t, -, hα, ht, hassoc⟩ := exists_local_generator ha hb hO hν0 hν' v
      have ht0 : t ≠ 0 := by
        rintro rfl; exact ι_ne_zero v hν0 (hassoc.eq_zero_iff.2 rfl)
      have hα0 : nrd α ≠ 0 := by
        rw [← ht]; exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ht0
      exact ⟨((isUnit_iff_nrd_ne_zero α).2 hα0).unit, hα, fun h => absurd hv h⟩
    · refine ⟨1, ?_, fun _ => rfl⟩
      rw [localIdeal_eq_top v hνJ hv, rTrans_localOrder_one]
  choose x hx hx1 using hgen
  refine ⟨⟨fun v => (fr.cvv v (x v))⁻¹, ?_⟩, fun v => ⟨x v, hx v, rfl⟩⟩
  have hfin := finite_setOf_mem hν0
  filter_upwards [hfin.compl_mem_cofinite] with v hv
  rw [hx1 v hv, map_one, inv_one]
  exact (stdStab fr.QF v).one_mem

theorem rTrans_localOrder_unit (v : HeightOneSpectrum (𝓞 F)) {u : (QuatV v a b)ˣ} (hu : u ∈ unitsOv (O := O) v) :
    rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) (u : QuatV v a b) =
      (localOrder (v := v) a b O : Set (QuatV v a b)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩; exact Subalgebra.mul_mem _ hz hu.1
  · intro hy
    refine ⟨y * ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b), Subalgebra.mul_mem _ hy hu.2, ?_⟩
    simp only [mul_assoc, Units.inv_mul, mul_one]

theorem TZFrame.cvv_inv_mul_inv (v : HeightOneSpectrum (𝓞 F)) (x y z : (QuatV v a b)ˣ) :
    ((fr.cvv v x)⁻¹)⁻¹ * (fr.cvv v y)⁻¹ * (fr.cvv v z)⁻¹ = fr.cvv v (x * y⁻¹ * z⁻¹) := by
  simp only [map_mul, map_inv, inv_inv]

/-- **From a double coset to a class:** if $(c(\beta)g)^{-1}g' \in K'$ for $g, g'$ attached to $J, J'$, then $J' = J\,c\beta^{-1}$ for
some $c \in F^\times$. -/
theorem TZFrame.exists_scalar_of_mem_KA (ha : a ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J J' : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) (hJ' : leftNrdIdeal J' ≠ ⊥) {g g' : OAf fr.QF} (hg : fr.IsGen J g)
    (hg' : fr.IsGen J' g') (β : (QuatF F a b)ˣ) (hβ : (diagF fr.QF (fr.cv0 β) * g)⁻¹ * g' ∈ fr.KA) :
    ∃ c : F, c ≠ 0 ∧ idealSet J' = rTrans (idealSet J) (algebraMap F (QuatF F a b) c * ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)) := by
  have hn := fun (I : Ideal O) (hI : leftNrdIdeal I ≠ ⊥) => (IsPrincipalIdealRing.principal (leftNrdIdeal I)).principal
  obtain ⟨n, hn⟩ := hn J hJ
  obtain ⟨n', hn'⟩ := (IsPrincipalIdealRing.principal (leftNrdIdeal J')).principal
  have hnJ0 : n ≠ 0 := by rintro rfl; apply hJ; rw [hn]; simp
  have hnJ0' : n' ≠ 0 := by rintro rfl; apply hJ'; rw [hn']; simp
  have hnJ : algebraMap (𝓞 F) O n ∈ J :=
    algebraMap_mem_of_mem_leftNrdIdeal hO.1 J (by rw [hn]; exact Ideal.mem_span_singleton_self _)
  have hnJ' : algebraMap (𝓞 F) O n' ∈ J' :=
    algebraMap_mem_of_mem_leftNrdIdeal hO.1 J' (by rw [hn']; exact Ideal.mem_span_singleton_self _)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : v.adicCompletion F, r ≠ 0 ∧
      idealSet (localIdeal (v := v) J') = rTrans (idealSet (localIdeal (v := v) J))
        (algebraMap (v.adicCompletion F) (QuatV v a b) r * complHom v a b ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)) := by
    intro v
    obtain ⟨x, hx, hgx⟩ := hg v
    obtain ⟨x', hx', hgx'⟩ := hg' v
    obtain ⟨u, hu, hku⟩ := hβ v
    have hval : ((diagF fr.QF (fr.cv0 β) * g)⁻¹ * g') v = fr.cvv v (x * (complUnits v β)⁻¹ * x'⁻¹) := by
      rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, RestrictedProduct.mul_apply,
        fr.diagF_cv0_apply, hgx, hgx']
      simp only [_root_.mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc]
    rw [hval] at hku
    have ha' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v a) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v ha)
    obtain ⟨r, hr⟩ := (cvHom_eq_iff (two_ne_zero_Fv v) ha' (fr.PGv v) u (x * (complUnits v β)⁻¹ * x'⁻¹)).1
      (congrArg (fun k : orthGroup fr.QF (v.adicCompletion F) => (k : GL (Fin 3) (v.adicCompletion F))) hku)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [hr, map_zero, zero_mul])
    -- x' = r u⁻¹ x β⁻¹ (as quaternions), up to the central r
    refine ⟨r, hr0, ?_⟩
    rw [hx', hx, rTrans_rTrans]
    have hx'eq : (x' : QuatV v a b) = ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) *
        ((x : QuatV v a b) * (algebraMap (v.adicCompletion F) (QuatV v a b) r *
          complHom v a b ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b))) := by
      have hinvβ : (((complUnits v β)⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) =
          complHom v a b ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) := by
        rw [← map_inv, coe_complUnits]
      have e2 : (u : QuatV v a b) * (x' : QuatV v a b) = algebraMap (v.adicCompletion F) (QuatV v a b) r *
          ((x : QuatV v a b) * complHom v a b ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)) := by
        rw [hr, Units.val_mul, Units.val_mul, hinvβ]
        simp only [mul_assoc, Units.inv_mul, mul_one]
      calc (x' : QuatV v a b) = ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) * ((u : QuatV v a b) * x') := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = _ := by
            rw [e2, ← mul_assoc (algebraMap _ _ r), Algebra.commutes r (x : QuatV v a b), mul_assoc]
    rw [hx'eq, ← rTrans_rTrans, rTrans_localOrder_unit v ((unitsOv v).inv_mem hu)]
  exact exists_scalar_of_local hO.1 hnJ0 hnJ0' hnJ hnJ' β⁻¹ hloc

/-- **Classes = double cosets, the orbit relation** ($\mathcal O$ maximal): for $g, g'$ attached to $J, J'$,
$J' \sim J$ iff $g' \in \Gamma gK'$, i.e. $(c(eta)g)^{-1}g' \in K'$ for some $eta \in D^	imes$. -/
theorem TZFrame.idealRel_iff (ha : a ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J J' : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) (hJ' : leftNrdIdeal J' ≠ ⊥) {g g' : OAf fr.QF} (hg : fr.IsGen J g)
    (hg' : fr.IsGen J' g') :
    IdealRel J J' ↔ ∃ β : (QuatF F a b)ˣ, (diagF fr.QF (fr.cv0 β) * g)⁻¹ * g' ∈ fr.KA := by
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨β⁻¹, fun v => ?_⟩
    obtain ⟨x, hx, hgx⟩ := hg v
    obtain ⟨x', hx', hgx'⟩ := hg' v
    have hloc := idealSet_localIdeal_rTrans v hβ
    rw [hx, rTrans_rTrans, hx'] at hloc
    obtain ⟨u, hu, hxu⟩ := exists_unit_of_rTrans_eq (O := O) v (x := x * complUnits v β) (x' := x')
      (by rw [hloc]; rfl)
    have hval : ((diagF fr.QF (fr.cv0 β⁻¹) * g)⁻¹ * g') v = fr.cvv v u⁻¹ := by
      rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, RestrictedProduct.mul_apply,
        fr.diagF_cv0_apply, hgx, hgx']
      have e : u⁻¹ = x * complUnits v β * x'⁻¹ := by rw [hxu]; group
      rw [e]
      simp only [_root_.mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc]
    rw [hval]
    exact ⟨u⁻¹, (unitsOv v).inv_mem hu, rfl⟩
  · rintro ⟨β, hβ⟩
    obtain ⟨c, hc0, hc⟩ := fr.exists_scalar_of_mem_KA ha hO hJ hJ' hg hg' β hβ
    have hcu : IsUnit (algebraMap F (QuatF F a b) c * ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)) :=
      (IsUnit.map _ (isUnit_iff_ne_zero.2 hc0)).mul (β⁻¹).isUnit
    exact ⟨hcu.unit, by rw [hc]; rfl⟩

/-! ### The double coset space and its stabilizers -/

/-- $\Gamma = SO(V)(F)$ inside $G = SO(V)(\mathbb A_f)$. -/
abbrev TZFrame.Gam : Subgroup (soAf fr.QF) := (ratPoints fr.QF).subgroupOf (soAf fr.QF)

/-- $K' = \prod_vc_v(\mathcal O_v^\times)$ inside $G$. -/
abbrev TZFrame.Kp : Subgroup (soAf fr.QF) := fr.KA.subgroupOf (soAf fr.QF)

/-- $K_0 = SO(\hat{\mathcal O}^0)$ inside $G$. -/
abbrev TZFrame.K0 : Subgroup (soAf fr.QF) := (locStab fr.QF (stdLat F 3)).subgroupOf (soAf fr.QF)

/-- $\beta \mapsto c(\beta)$ as a homomorphism $D^\times \to \Gamma$. -/
def TZFrame.rhoD : (QuatF F a b)ˣ →* fr.Gam where
  toFun β := ⟨⟨diagF fr.QF (fr.cv0 β), fr.diagF_cv0_mem_soAf β⟩, Subgroup.mem_subgroupOf.2 ⟨fr.cv0 β, rfl⟩⟩
  map_one' := by ext1; ext1; simp
  map_mul' x y := by ext1; ext1; simp

@[simp] theorem TZFrame.coe_rhoD (β : (QuatF F a b)ˣ) :
    (((fr.rhoD β : fr.Gam) : soAf fr.QF) : OAf fr.QF) = diagF fr.QF (fr.cv0 β) := rfl

theorem TZFrame.mem_stabilizer_iff {g : OAf fr.QF} (hg : g ∈ soAf fr.QF) (γ : fr.Gam) :
    γ ∈ stabilizer fr.Gam (QuotientGroup.mk (⟨g, hg⟩ : soAf fr.QF) : soAf fr.QF ⧸ fr.Kp) ↔
      ((γ : soAf fr.QF) * ⟨g, hg⟩)⁻¹ * ⟨g, hg⟩ ∈ fr.Kp := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk ((γ : soAf fr.QF) * ⟨g, hg⟩) : soAf fr.QF ⧸ fr.Kp) = QuotientGroup.mk ⟨g, hg⟩ ↔ _
  rw [QuotientGroup.eq]

theorem TZFrame.diagF_injective : Function.Injective (diagF fr.QF) := by
  intro x y h
  obtain ⟨v₀⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
  have h1 := congrArg (fun g : OAf fr.QF => ((g v₀ : orthGroup fr.QF _) : GL (Fin 3) (v₀.adicCompletion F))) h
  simp only [fr.diagF_apply] at h1
  apply Subtype.ext; apply Units.ext
  ext i j
  have := congrArg (fun M : GL (Fin 3) (v₀.adicCompletion F) => M.val i j) h1
  simpa [orthMap_val] using this

/-- A scalar $r \in F^\times$ in $\Gamma_J$ is a unit of $\mathcal O_F$. -/
theorem TZFrame.isUnit_of_scalar_mem_rStab (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} {g : OAf fr.QF}
    (hg : fr.IsGen J g) {r : F} (hr : r ≠ 0) (hrJ : rTrans (idealSet J) (algebraMap F (QuatF F a b) r) = idealSet J) :
    ∃ w : (𝓞 F)ˣ, algebraMap (𝓞 F) F w = r := by
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) r) = 1 := by
    intro v
    obtain ⟨x, hx, -⟩ := hg v
    have h1 := idealSet_localIdeal_rTrans v hrJ.symm
    rw [hx, rTrans_rTrans] at h1
    have hr' : algebraMap F (v.adicCompletion F) r ≠ 0 := (map_ne_zero _).2 hr
    set ru : (QuatV v a b)ˣ := qScalar (algebraMap F (v.adicCompletion F) r) hr'
    have hcr : complHom v a b (algebraMap F (QuatF F a b) r) = (ru : QuatV v a b) := by
      rw [AlgHom.commutes]; rfl
    rw [hcr] at h1
    obtain ⟨u, hu, hxu⟩ := exists_unit_of_rTrans_eq (O := O) v (x := x * ru) (x' := x) (by rw [Units.val_mul]; exact h1)
    have hcommU : x * ru = ru * x := Units.ext (Algebra.commutes _ _).symm
    have e2 : u * ru = 1 := by
      have : u * ru * x = 1 * x := by rw [one_mul, mul_assoc, ← hcommU, ← hxu]
      exact mul_right_cancel this
    have huinv : u = ru⁻¹ := eq_inv_of_mul_eq_one_left e2
    have h2 := valued_eq_one_of_scalar_unit (O := O) v hO.1 (inv_ne_zero hr') (by
      have : algebraMap (v.adicCompletion F) (QuatV v a b) (algebraMap F _ r)⁻¹ = (u : QuatV v a b) := by
        rw [huinv, qScalar_inv, coe_qScalar]
      rw [this]; exact hu.1) (by
      rw [inv_inv]
      have : algebraMap (v.adicCompletion F) (QuatV v a b) (algebraMap F _ r) =
          ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) := by rw [huinv, inv_inv, coe_qScalar]
      rw [this]; exact hu.2)
    rw [map_inv₀, inv_eq_one] at h2
    exact h2
  have hint : ∀ {s : F}, (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) s) ≤ 1) →
      ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = s := by
    intro s hs
    have := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F s (fun v => by
      rw [← valued_algebraMap]; exact hs v)
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht⟩
  obtain ⟨t, ht⟩ := hint fun v => (hloc v).le
  obtain ⟨t', ht'⟩ := hint (s := r⁻¹) fun v => by rw [map_inv₀ (algebraMap F _), map_inv₀, hloc v, inv_one]
  have htt : t * t' = 1 := IsFractionRing.injective (𝓞 F) F (by rw [map_mul, ht, ht', mul_inv_cancel₀ hr, map_one])
  exact ⟨⟨t, t', htt, by rw [mul_comm]; exact htt⟩, ht⟩

theorem TZFrame.cv0_scalar_mul (ha : a ≠ 0) (c : F) (β : (QuatF F a b)ˣ) (δ : (QuatF F a b)ˣ)
    (hδ : (δ : QuatF F a b) = algebraMap F (QuatF F a b) c * β) : fr.cv0 δ = fr.cv0 β := by
  ext1
  exact (cvHom_eq_iff two_ne_zero (b := algebraMap (𝓞 F) F b)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha) fr.PG δ β).2 ⟨c, hδ⟩

set_option maxHeartbeats 1000000 in
/-- **The stabilizer of the coset of $J$ is $\Gamma_J/\mathcal O_F^\times$:** for $g$ attached to $J$,
$|\Gamma \cap gK'g^{-1}| = [\Gamma_J : \mathcal O_F^\times]$. -/
theorem TZFrame.card_stabilizer (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) {g : OAf fr.QF} (hg : fr.IsGen J g) :
    Nat.card (stabilizer fr.Gam (QuotientGroup.mk (⟨g, fr.isGen_mem_soAf hg⟩ : soAf fr.QF) : soAf fr.QF ⧸ fr.Kp)) =
      (centralUnitsIn (R := 𝓞 F) J).index := by
  have hgs := fr.isGen_mem_soAf hg
  set x0 : soAf fr.QF ⧸ fr.Kp := QuotientGroup.mk (⟨g, hgs⟩ : soAf fr.QF)
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  have hmem : ∀ β : rStab J, fr.rhoD (β : (QuatF F a b)ˣ) ∈ stabilizer fr.Gam x0 := by
    intro β
    rw [fr.mem_stabilizer_iff hgs, Subgroup.mem_subgroupOf]
    intro v
    obtain ⟨x, hx, hgx⟩ := hg v
    have hβJ : idealSet J = rTrans (idealSet J) ((β : (QuatF F a b)ˣ) : QuatF F a b) := (mem_rStab.1 β.2).symm
    have h1 := idealSet_localIdeal_rTrans v hβJ
    rw [hx, rTrans_rTrans] at h1
    obtain ⟨u, hu, hxu⟩ := exists_unit_of_rTrans_eq (O := O) v (x := x) (x' := x * complUnits v β)
      (by rw [Units.val_mul, coe_complUnits]; exact h1.symm)
    have hval : (((((fr.rhoD (β : (QuatF F a b)ˣ) : fr.Gam) : soAf fr.QF) * ⟨g, hgs⟩)⁻¹ * ⟨g, hgs⟩ :
        soAf fr.QF) : OAf fr.QF) v = fr.cvv v u⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, fr.coe_rhoD]
      rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, RestrictedProduct.mul_apply,
        fr.diagF_cv0_apply, hgx]
      rw [show u⁻¹ = x * (complUnits v (β : (QuatF F a b)ˣ))⁻¹ * x⁻¹ by
        rw [show u = x * complUnits v (β : (QuatF F a b)ˣ) * x⁻¹ by rw [hxu]; group]; group]
      simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [hval]
    exact ⟨u⁻¹, (unitsOv v).inv_mem hu, rfl⟩
  let f : rStab J →* stabilizer fr.Gam x0 :=
    (fr.rhoD.comp (rStab J).subtype).codRestrict _ hmem
  have hf : ∀ β : rStab J, ((f β : stabilizer fr.Gam x0) : fr.Gam) = fr.rhoD (β : (QuatF F a b)ˣ) := fun _ => rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨γ, hγ⟩
    have hγr : (((γ : soAf fr.QF) : OAf fr.QF)) ∈ ratPoints fr.QF := Subgroup.mem_subgroupOf.1 γ.2
    obtain ⟨β₀, hβ₀⟩ := fr.exists_cv0_of_mem ha hb hγr (γ : soAf fr.QF).2
    have hst := (fr.mem_stabilizer_iff hgs γ).1 hγ
    rw [Subgroup.mem_subgroupOf] at hst
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hβ₀] at hst
    obtain ⟨c, hc0, hc⟩ := fr.exists_scalar_of_mem_KA ha hO hJ hJ hg hg β₀ hst
    have hδu : IsUnit (algebraMap F (QuatF F a b) c * ((β₀⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)) :=
      (IsUnit.map _ (isUnit_iff_ne_zero.2 hc0)).mul (β₀⁻¹).isUnit
    set δ := hδu.unit
    have hδ : δ ∈ rStab J := mem_rStab.2 hc.symm
    refine ⟨(⟨δ, hδ⟩ : rStab J)⁻¹, ?_⟩
    have key : fr.rhoD (((⟨δ, hδ⟩ : rStab J)⁻¹ : rStab J) : (QuatF F a b)ˣ) = γ := by
      apply Subtype.ext; apply Subtype.ext
      show diagF fr.QF (fr.cv0 δ⁻¹) = ((γ : soAf fr.QF) : OAf fr.QF)
      rw [hβ₀]
      simp only [map_inv, fr.cv0_scalar_mul ha c (β₀⁻¹) δ rfl, inv_inv]
    exact Subtype.ext key
  have hker : f.ker = centralUnitsIn (R := 𝓞 F) J := by
    ext β
    rw [MonoidHom.mem_ker, centralUnitsIn, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : diagF fr.QF (fr.cv0 (β : (QuatF F a b)ˣ)) = 1 := by
        have := congrArg (fun z : stabilizer fr.Gam x0 => (((z : fr.Gam) : soAf fr.QF) : OAf fr.QF)) h1
        simpa [hf] using this
      have h3 : fr.cv0 (β : (QuatF F a b)ˣ) = 1 := fr.diagF_injective (by rw [h2, map_one])
      have h4 : cvHom fr.PG (β : (QuatF F a b)ˣ) = 1 := congrArg Subtype.val h3
      obtain ⟨r, hr⟩ := (cvHom_eq_one_iff two_ne_zero ha' fr.PG _).1 h4
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact (β : (QuatF F a b)ˣ).ne_zero (by rw [hr]; simp)
      have hrJ : rTrans (idealSet J) (algebraMap F (QuatF F a b) r) = idealSet J := by
        have := mem_rStab.1 β.2; rwa [hr] at this
      obtain ⟨w, hw⟩ := fr.isUnit_of_scalar_mem_rStab hO hg hr0 hrJ
      refine ⟨w, Units.ext ?_⟩
      rw [hr, ← hw]; rfl
    · rintro ⟨w, hw⟩
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      rw [hf]
      simp only [fr.coe_rhoD, OneMemClass.coe_one]
      have : fr.cv0 (β : (QuatF F a b)ˣ) = 1 := by
        ext1
        refine (cvHom_eq_one_iff two_ne_zero ha' fr.PG _).2 ⟨algebraMap (𝓞 F) F w, ?_⟩
        rw [← hw]; rfl
      rw [this, map_one]
  rw [Subgroup.index, ← hker]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv).symm

/-! ### Every double coset comes from a left ideal -/

theorem TZFrame.cvv_scalar (v : HeightOneSpectrum (𝓞 F)) (ha : a ≠ 0) {r : v.adicCompletion F} (hr : r ≠ 0) :
    fr.cvv v (qScalar r hr) = 1 := by
  have ha' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v ha)
  ext1
  exact (cvHom_eq_one_iff (two_ne_zero_Fv v) ha' (fr.PGv v) _).2 ⟨r, rfl⟩

/-- Every quaternion becomes integral after multiplying by a power of $\varpi_v$. -/
theorem exists_pow_smul_mem_localOrder (hO : IsOrder (𝓞 F) F O) (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O))
    (v : HeightOneSpectrum (𝓞 F)) (z : QuatV v a b) :
    ∃ N : ℕ, algebraMap (v.adicCompletion F) (QuatV v a b)
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v (genP v)) ^ N) * z ∈ localOrder (v := v) a b O := by
  classical
  set ϖ := algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v (genP v))
  set B := complBasis (v := v) e hO
  have hN := fun i => exists_pow_mul_isInteger (v := v) (B.repr z i)
  choose N hN using hN
  set M := Finset.univ.sup N
  refine ⟨M, (mem_localOrder_iff e hO _).2 fun i => ?_⟩
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hle : N i ≤ M := Finset.le_sup (f := N) (Finset.mem_univ i)
  rw [show ϖ ^ M = ϖ ^ (M - N i) * ϖ ^ N i by rw [← pow_add]; congr 1; omega, mul_assoc]
  obtain ⟨c, hc⟩ := hN i
  refine ⟨ι v (genP v) ^ (M - N i) * c, ?_⟩
  rw [map_mul, map_pow, hc]

/-- **Every element of $SO(V)(\mathbb A_f)$ is attached to a left ideal** ($\mathcal O$ maximal, $D$ definite at no finite place
needed): for $h \in G$ there is $J \ne 0$ with $J_v = \mathcal O_vx_v$, $h_v = c_v(x_v)^{-1}$. -/
theorem TZFrame.exists_isGen_of_mem (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0) {h : OAf fr.QF} (hh : h ∈ soAf fr.QF) :
    ∃ J : Ideal O, leftNrdIdeal J ≠ ⊥ ∧ fr.IsGen J h := by
  classical
  -- step 1: local preimages, units where possible
  have hpre : ∀ v, ∃ y : (QuatV v a b)ˣ, fr.cvv v y = h v ∧ (h v ∈ fr.Kv v → y ∈ unitsOv (O := O) v) := by
    intro v
    by_cases hK : h v ∈ fr.Kv v
    · obtain ⟨u, hu, e⟩ := hK
      exact ⟨u, e, fun _ => hu⟩
    · have hmem := (mem_orthGroup fr.QF).1 (h v).2
      rw [fr.hessian_QF_map v] at hmem
      have ha' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v a) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v ha)
      have hb' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v b) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v hb)
      obtain ⟨α, hα⟩ := exists_cvHom_eq (two_ne_zero_Fv v) ha' hb' (fr.PGv v) _ hmem (hh v)
      exact ⟨α, Subtype.ext hα, fun h' => absurd h' hK⟩
  choose y hy hyK using hpre
  -- step 2: the bad set is finite
  have hT : {v | h v ∉ fr.Kv v}.Finite := by
    have h1 : {v | h v ∉ stdStab fr.QF v}.Finite := h.2
    have h2 : (↑(ramFin ha hb) : Set (HeightOneSpectrum (𝓞 F))).Finite := Finset.finite_toSet _
    refine (h1.union h2).subset fun v hv => ?_
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hcon
    apply hv
    rcases localOrder_ramified_or_split (v := v) ha hb hO with ⟨hd, -⟩ | ⟨φ, hφ⟩
    · exfalso; apply hcon.2
      rw [mem_ramFin]
      intro x hx
      exact (isUnit_iff_nrd_ne_zero x).2 fun h0 => hx (hd x h0)
    · rw [← hy v]
      exact fr.mem_Kv_of_mem_stdStab_split v φ hφ ha (y v) (by rw [hy v]; exact hcon.1)
  set T := hT.toFinset
  -- step 3: integral local generators x_v = ϖ^N y_v⁻¹
  have hint : ∀ v, ∃ N : ℕ, algebraMap (v.adicCompletion F) (QuatV v a b)
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v (genP v)) ^ N) *
        (((y v)⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O ∧ (v ∉ T → N = 0) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨N, hN⟩ := exists_pow_smul_mem_localOrder hO.1 fr.e v (((y v)⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)
      exact ⟨N, hN, fun h' => absurd hv h'⟩
    · refine ⟨0, ?_, fun _ => rfl⟩
      have hvK : h v ∈ fr.Kv v := by
        by_contra hc; exact hv (hT.mem_toFinset.2 hc)
      rw [pow_zero, map_one, one_mul]
      exact (hyK v hvK).2
  choose N hNmem hN0 using hint
  have hϖ0 : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v (genP v)) ^ N v ≠ 0 := fun v =>
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 irreducible_ι_genP.ne_zero)
  set x : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV v a b)ˣ := fun v =>
    qScalar (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v (genP v)) ^ N v) (hϖ0 v) * (y v)⁻¹
  have hxO : ∀ v, ((x v : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O := fun v => hNmem v
  have hxh : ∀ v, h v = (fr.cvv v (x v))⁻¹ := by
    intro v
    simp only [x, map_mul, fr.cvv_scalar v ha (hϖ0 v), one_mul, map_inv, inv_inv, hy v]
  -- step 4: the local ideals
  set I : ∀ v : HeightOneSpectrum (𝓞 F), Ideal (localOrder (v := v) a b O) := fun v =>
    Ideal.span {(⟨(x v : QuatV v a b), hxO v⟩ : localOrder (v := v) a b O)}
  have hI : ∀ v, idealSet (I v) = rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) (x v : QuatV v a b) :=
    fun v => idealSet_span_singleton _
  -- step 5: the global element n = ∏_{v ∈ T} ϖ_v^{e_v}
  have hexp : ∀ v, ∃ e : ℕ, 1 ≤ e ∧ exp (-(e : ℤ)) ≤ Valued.v (nrd ((x v : (QuatV v a b)ˣ) : QuatV v a b)) := by
    intro v
    obtain ⟨k, hk⟩ := exists_valued_eq_exp v (nrd_units_ne_zero (x v))
    refine ⟨(-k).toNat + 1, by omega, ?_⟩
    rw [hk, WithZero.exp_le_exp]; omega
  choose e he1 he using hexp
  set n : 𝓞 F := ∏ v ∈ T, genP v ^ e v
  have hn0 : n ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ genP_ne_zero
  have hmemT : ∀ w, n ∈ w.asIdeal ↔ w ∈ T := by
    intro w
    haveI := w.isPrime
    rw [Ideal.IsPrime.prod_mem_iff]
    constructor
    · rintro ⟨v, hv, hmem⟩
      have := w.isPrime.mem_of_pow_mem _ hmem
      by_cases hvw : v = w
      · rwa [← hvw]
      · exact absurd this (genP_not_mem hvw)
    · intro hw
      refine ⟨w, hw, ?_⟩
      have h1 : genP w ∈ w.asIdeal := by rw [span_genP]; exact Ideal.mem_span_singleton_self _
      exact Ideal.pow_mem_of_mem _ h1 _ (by have := he1 w; omega)
  have hsupp : primeSupport hn0 = T := by
    ext w; rw [mem_primeSupport, hmemT]
  have hvaln : ∀ v ∈ T, Valued.v ((ι v n : v.adicCompletionIntegers F) : v.adicCompletion F) = exp (-(e v : ℤ)) := by
    intro v hv
    rw [valued_ι, map_prod, ← Finset.mul_prod_erase T _ hv, map_pow, intValuation_genP, Finset.prod_eq_one, mul_one,
      ← WithZero.exp_nsmul]
    · simp
    · intro w hw
      rw [map_pow, HeightOneSpectrum.intValuation_eq_one_iff.2 (genP_not_mem (Finset.ne_of_mem_erase hw)), one_pow]
  -- step 6: ι_v(n) ∈ I_v at v ∈ T
  have hnI : ∀ v ∈ primeSupport hn0, algebraMap (v.adicCompletionIntegers F) (localOrder (v := v) a b O) (ι v n) ∈ I v := by
    intro v hv
    rw [hsupp] at hv
    have hnrd0 := nrd_units_ne_zero (x v)
    set t : v.adicCompletion F := ((ι v n : v.adicCompletionIntegers F) : v.adicCompletion F) /
      nrd ((x v : (QuatV v a b)ˣ) : QuatV v a b)
    have ht : Valued.v t ≤ 1 := by
      rw [map_div₀, hvaln v hv, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hnrd0))]
      exact he v
    set t' : v.adicCompletionIntegers F := ⟨t, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ht⟩
    have hstar : star ((x v : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O :=
      star_mem_of_isOrder (isOrder_localOrder (v := v) hO.1) (hxO v)
    have heq : algebraMap (v.adicCompletionIntegers F) (localOrder (v := v) a b O) (ι v n) =
        (algebraMap (v.adicCompletionIntegers F) (localOrder (v := v) a b O) t' * ⟨_, hstar⟩) *
          ⟨(x v : QuatV v a b), hxO v⟩ := by
      apply Subtype.ext
      simp only [Subalgebra.coe_algebraMap, Subalgebra.coe_mul]
      rw [mul_assoc, star_mul_eq_nrd]
      change algebraMap (v.adicCompletion F) (QuatV v a b) ((ι v n : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap (v.adicCompletion F) (QuatV v a b) t * algebraMap (v.adicCompletion F) (QuatV v a b) (nrd _)
      rw [← map_mul]
      congr 1
      simp only [t]; field_simp
    rw [heq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  -- step 7: the global ideal
  set J := globalIdeal (primeSupport hn0) I
  have hnJ : algebraMap (𝓞 F) O n ∈ J := algebraMap_mem_globalIdeal hnI
  refine ⟨J, ?_, fun v => ⟨x v, ?_, hxh v⟩⟩
  · refine leftNrdIdeal_ne_bot hO.1 hdiv fun hbot => hn0 ?_
    rw [hbot] at hnJ
    have h0 : algebraMap (𝓞 F) O n = 0 := hnJ
    have := congrArg Subtype.val h0
    simp only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1
      ((map_eq_zero_iff _ (algebraMap F (QuatF F a b)).injective).1 (by
        rw [← IsScalarTower.algebraMap_apply]; exact this))
  · by_cases hv : v ∈ primeSupport hn0
    · rw [localIdeal_globalIdeal hO.1 hn0 I hnI v hv, hI]
    · have hvn : n ∉ v.asIdeal := fun h' => hv ((mem_primeSupport hn0).2 h')
      have hvT : v ∉ T := by rw [← hsupp]; exact hv
      rw [localIdeal_eq_top v hnJ hvn, idealSet_top_local]
      have hvK : h v ∈ fr.Kv v := by
        by_contra hc; exact hvT (hT.mem_toFinset.2 hc)
      have hxu : x v ∈ unitsOv (O := O) v := by
        have h1 : x v = (y v)⁻¹ := Units.ext (by
          simp only [x, hN0 v hvT, pow_zero, Units.val_mul, coe_qScalar, map_one, one_mul])
        rw [h1]; exact (unitsOv v).inv_mem (hyK v hvK)
      exact (rTrans_localOrder_unit v hxu).symm

/-! ### $\mathrm{dcMass}(\Gamma, K')$ is Eichler's mass -/

theorem TZFrame.mem_orbit_iff (ha : a ≠ 0) (hb : b ≠ 0) {g g' : OAf fr.QF} (hg : g ∈ soAf fr.QF)
    (hg' : g' ∈ soAf fr.QF) :
    (QuotientGroup.mk (⟨g', hg'⟩ : soAf fr.QF) : soAf fr.QF ⧸ fr.Kp) ∈
        orbit fr.Gam (QuotientGroup.mk (⟨g, hg⟩ : soAf fr.QF) : soAf fr.QF ⧸ fr.Kp) ↔
      ∃ β : (QuatF F a b)ˣ, (diagF fr.QF (fr.cv0 β) * g)⁻¹ * g' ∈ fr.KA := by
  constructor
  · rintro ⟨γ, hγ⟩
    have hγ' : (QuotientGroup.mk ((γ : soAf fr.QF) * ⟨g, hg⟩) : soAf fr.QF ⧸ fr.Kp) = QuotientGroup.mk ⟨g', hg'⟩ := hγ
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hγ'
    obtain ⟨β, hβ⟩ := fr.exists_cv0_of_mem ha hb (Subgroup.mem_subgroupOf.1 γ.2) (γ : soAf fr.QF).2
    refine ⟨β, ?_⟩
    simpa [hβ] using hγ'
  · rintro ⟨β, hβ⟩
    refine ⟨fr.rhoD β, ?_⟩
    change (QuotientGroup.mk (((fr.rhoD β : fr.Gam) : soAf fr.QF) * ⟨g, hg⟩) : soAf fr.QF ⧸ fr.Kp) =
      QuotientGroup.mk ⟨g', hg'⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hβ

variable [IsTotallyReal F]

/-- **Double cosets $\Gamma\backslash G/K'$ = nonzero left ideal classes**, with stabilizers of order $[\Gamma_J:\mathcal O_F^\times]$. -/
theorem TZFrame.exists_orbitEquiv (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O) :
    ∃ Ψ : {c : Quotient (idealSetoid O) // c.out ≠ ⊥} ≃ orbitRel.Quotient fr.Gam (soAf fr.QF ⧸ fr.Kp),
      ∀ c, Nat.card (stabilizer fr.Gam (Ψ c).out) = (centralUnitsIn (R := 𝓞 F) c.1.out).index := by
  classical
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  have : Finite (Quotient (idealSetoid O)) := finite_classes ha hb hO hdiv
  set C := {c : Quotient (idealSetoid O) // c.out ≠ ⊥}
  have hJc : ∀ c : C, leftNrdIdeal c.1.out ≠ ⊥ := fun c => leftNrdIdeal_ne_bot hO.1 hdiv c.2
  choose g hg using fun c : C => fr.exists_isGen ha hb hO (hJc c)
  have hgs : ∀ c, g c ∈ soAf fr.QF := fun c => fr.isGen_mem_soAf (hg c)
  let Ψ : C → orbitRel.Quotient fr.Gam (soAf fr.QF ⧸ fr.Kp) := fun c =>
    Quotient.mk'' (QuotientGroup.mk (⟨g c, hgs c⟩ : soAf fr.QF))
  have hΨinj : Function.Injective Ψ := by
    intro c c' h
    have h1 := Quotient.exact' h
    rw [orbitRel_apply, fr.mem_orbit_iff ha hb] at h1
    have h2 := (fr.idealRel_iff ha hO (hJc c') (hJc c) (hg c') (hg c)).2 h1
    apply Subtype.ext
    rw [← Quotient.out_eq c.1, ← Quotient.out_eq c'.1]
    exact Quotient.sound h2.symm
  have hΨsurj : Function.Surjective Ψ := by
    intro ω
    induction ω using Quotient.inductionOn' with | h y => ?_
    induction y using QuotientGroup.induction_on with | H h => ?_
    obtain ⟨J, hJ, hJh⟩ := fr.exists_isGen_of_mem ha hb hO hdiv h.2
    have hJ0 : J ≠ ⊥ := by
      rintro rfl
      apply hJ
      refine Ideal.span_eq_bot.2 fun r ⟨x, hx, hr⟩ => ?_
      have h0 : nrd (x : QuatF F a b) = 0 := by rw [show x = 0 from hx]; simp [nrd]
      rw [h0] at hr
      exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 hr
    have hrel : IdealRel (Quotient.mk (idealSetoid O) J).out J := by
      have := Quotient.exact (Quotient.out_eq (Quotient.mk (idealSetoid O) J))
      exact this
    have hout : (Quotient.mk (idealSetoid O) J).out ≠ ⊥ := fun h0 => hJ0 (eq_bot_of_idealRel_bot (h0 ▸ hrel))
    set c : C := ⟨Quotient.mk (idealSetoid O) J, hout⟩
    refine ⟨c, Quotient.sound' ?_⟩
    rw [orbitRel_apply]
    have := (fr.idealRel_iff ha hO (hJc c) hJ (hg c) hJh).1 hrel
    have hh : h = ⟨(h : OAf fr.QF), h.2⟩ := rfl
    rw [hh]
    exact MulAction.mem_orbit_symm.1 ((fr.mem_orbit_iff ha hb (hgs c) h.2).2 this)
  have hw : ∀ c : C, Nat.card (stabilizer fr.Gam (Ψ c).out) = (centralUnitsIn (R := 𝓞 F) c.1.out).index := by
    intro c
    rw [card_stabilizer_of_mem_orbit (out_mem_orbit (Ψ c) _ rfl)]
    exact fr.card_stabilizer ha hb hO (hJc c) (hg c)
  exact ⟨Equiv.ofBijective Ψ (show Function.Bijective Ψ from ⟨hΨinj, hΨsurj⟩), hw⟩

/-- **The double coset mass of $K'$ is Eichler's mass** ($\mathcal O$ maximal, $D$ totally definite):
$$\mathrm{dcMass}(SO(V)(F), K') = \sum_{[J]\ne0}\frac{1}{[\Gamma_J:\mathcal O_F^\times]}.$$ -/
theorem TZFrame.dcMass_Kp_eq (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O) :
    dcMass fr.Gam fr.Kp = ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥},
      (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ := by
  classical
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  have : Finite (Quotient (idealSetoid O)) := finite_classes ha hb hO hdiv
  obtain ⟨Ψ, hw⟩ := fr.exists_orbitEquiv ha hb hdef hO
  have : Finite {c : Quotient (idealSetoid O) // c.out ≠ ⊥} := Subtype.finite
  let _ : Fintype {c : Quotient (idealSetoid O) // c.out ≠ ⊥} := Fintype.ofFinite _
  unfold dcMass orbitMass
  rw [← finsum_comp_equiv Ψ]
  simp only [hw]
  rw [tsum_fintype (L := .unconditional _), finsum_eq_sum_of_fintype]

end QuadFormsKB.QuatOrder
