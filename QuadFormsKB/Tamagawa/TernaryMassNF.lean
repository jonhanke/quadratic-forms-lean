/-
# Double cosets of the trace-zero lattice and left ideal classes modulo $\mathrm{Cl}(F)$

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$, $\mathcal O$ a maximal order, $L = \mathcal O^0$ (`pureLat`),
$Q = \langle -a,-b,ab\rangle$, $G = SO(Q)(\mathbb A_f)$, $\Gamma = SO(Q)(F)$, $K' = \prod_vc_v(\mathcal O_v^\times)$ (`TernaryIndexNF`).

To a nonzero left ideal $J$ we attach $g \in G$ with $J_v = \mathcal O_vx_v$, $g_v = c_v(x_v)^{-1}$ (`IsGenNF`, `exists_isGenNF`). Then
**$g' \in \Gamma gK'$ iff $\mathfrak bJ' \sim \mathfrak aJ$ for nonzero integral ideals $\mathfrak a, \mathfrak b$** (`orbit_iff_clsRel`): the gluing lemma
of `TernaryGlueNF` in one direction, the local description of $\mathfrak aJ$ in the other. Every element of $G$ is attached to some
$J$ (`exists_isGenNF_of_mem`). So $\Gamma\backslash G/K'$ is the set of left ideal classes modulo the action of $\mathrm{Cl}(F)$.

Source: Voight 2021, §§17.4–17.7, 26.5; Weil 1982, §3.7(a). Port of `TernaryMass` with ideals in place of scalars.
-/
import QuadFormsKB.Tamagawa.TernaryGlueNF

open NumberField IsDedekindDomain Matrix Quaternion WithZero MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-! ### The rational points -/

theorem diagF_apply_QP (γ : orthGroup (QP a b) F) (v : HeightOneSpectrum (𝓞 F)) :
    (diagF (QP a b) γ) v = orthMap (QP a b) (v.adicCompletion F) γ := rfl

theorem diagF_cv0NF_apply (β : (QuatF F a b)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (diagF (QP a b) (cv0NF β)) v = cvvNF v (complUnits v β) := by
  change orthMap (QP a b) _ (cv0NF β) = _
  rw [orthMap_cv0NF]

theorem diagF_cv0NF_mem_soAf (β : (QuatF F a b)ˣ) : diagF (QP a b) (cv0NF β) ∈ soAf (QP a b) := fun v => by
  rw [diagF_cv0NF_apply]; exact cvvNF_mem_soSub v _

/-- **The rational points of $SO(Q)$ are the conjugations** $c(\beta)$, $\beta \in D^\times$. -/
theorem exists_cv0NF_of_mem (ha : a ≠ 0) (hb : b ≠ 0) {γ : OAf (QP a b)} (hγ : γ ∈ ratPoints (QP a b))
    (hγs : γ ∈ soAf (QP a b)) : ∃ β : (QuatF F a b)ˣ, γ = diagF (QP a b) (cv0NF β) := by
  obtain ⟨γ₀, rfl⟩ := hγ
  obtain ⟨v₀⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
  have hdet : (γ₀ : GL (Fin 3) F).val.det = 1 := by
    have := hγs v₀
    rw [det_diagF] at this
    exact (algebraMap F (v₀.adicCompletion F)).injective (by rw [this, map_one])
  have hmem := (mem_orthGroup (QP a b)).1 γ₀.2
  rw [hessian_QP_map_self] at hmem
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb
  obtain ⟨β, hβ⟩ := exists_cvHom_eq two_ne_zero ha' hb' 1 (γ₀ : GL (Fin 3) F) hmem hdet
  refine ⟨β, ?_⟩
  congr 1
  exact Subtype.ext hβ.symm

theorem cv0NF_scalar_mul (ha : a ≠ 0) (c : F) (β δ : (QuatF F a b)ˣ)
    (hδ : (δ : QuatF F a b) = algebraMap F (QuatF F a b) c * β) : cv0NF δ = cv0NF β := by
  ext1
  exact (cvHom_eq_iff two_ne_zero (b := algebraMap (𝓞 F) F b)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha) 1 δ β).2 ⟨c, hδ⟩

theorem diagF_injective_QP : Function.Injective (diagF (QP a b)) := by
  intro x y h
  obtain ⟨v₀⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
  have h1 := congrArg (fun g : OAf (QP a b) => ((g v₀ : orthGroup (QP a b) _) : GL (Fin 3) (v₀.adicCompletion F))) h
  simp only [diagF_apply_QP] at h1
  apply Subtype.ext; apply Units.ext
  ext i j
  have := congrArg (fun M : GL (Fin 3) (v₀.adicCompletion F) => M.val i j) h1
  simpa [orthMap_val] using this

/-! ### Attached adelic elements -/

/-- **$g$ is attached to $J$:** at every $v$, $J_v = \mathcal O_vx_v$ and $g_v = c_v(x_v)^{-1}$. -/
def IsGenNF (J : Ideal O) (g : OAf (QP a b)) : Prop :=
  ∀ v, ∃ x : (QuatV v a b)ˣ, idealSet (localIdeal (v := v) J) =
    rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) (x : QuatV v a b) ∧ g v = (cvvNF v x)⁻¹

theorem isGenNF_mem_soAf {J : Ideal O} {g : OAf (QP a b)} (h : IsGenNF J g) : g ∈ soAf (QP a b) := fun v => by
  obtain ⟨x, -, hx⟩ := h v
  rw [hx]; exact (soSub (QP a b) _).inv_mem (cvvNF_mem_soSub v x)

theorem rTrans_localOrder_one_nf (v : HeightOneSpectrum (𝓞 F)) :
    idealSet (⊤ : Ideal (localOrder (v := v) a b O)) =
      rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) ((1 : (QuatV v a b)ˣ) : QuatV v a b) := by
  rw [Units.val_one, rTrans_one, idealSet_top_local_nf]

/-- **Every nonzero left ideal has attached elements** ($\mathcal O$ maximal). -/
theorem exists_isGenNF (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) : ∃ g : OAf (QP a b), IsGenNF J g := by
  classical
  obtain ⟨ν, hνJ', hν0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hνJ : algebraMap (𝓞 F) O ν ∈ J := algebraMap_mem_of_mem_leftNrdIdeal hO.1 J hνJ'
  have hgen : ∀ v, ∃ x : (QuatV v a b)ˣ, idealSet (localIdeal (v := v) J) =
      rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) (x : QuatV v a b) ∧
      (ν ∉ v.asIdeal → x = 1) := by
    intro v
    by_cases hv : ν ∈ v.asIdeal
    · obtain ⟨α, t, -, hα, ht, hspan⟩ := Gen.exists_local_generator ha hb hO hJ v
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at hspan
        exact pow_ne_zero _ (irreducible_π v).ne_zero hspan
      have hα0 : nrd α ≠ 0 := by
        rw [← ht]; exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ht0
      exact ⟨((isUnit_iff_nrd_ne_zero α).2 hα0).unit, hα, fun h => absurd hv h⟩
    · refine ⟨1, ?_, fun _ => rfl⟩
      rw [Gen.localIdeal_eq_top v hνJ hv, rTrans_localOrder_one_nf]
  choose x hx hx1 using hgen
  refine ⟨⟨fun v => (cvvNF v (x v))⁻¹, ?_⟩, fun v => ⟨x v, hx v, rfl⟩⟩
  have hfin := Gen.finite_setOf_mem hν0
  filter_upwards [hfin.compl_mem_cofinite] with v hv
  rw [hx1 v hv, map_one, inv_one]
  exact (stdStab (QP a b) v).one_mem

theorem exists_nonzero_mem (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) :
    ∃ n : 𝓞 F, n ≠ 0 ∧ algebraMap (𝓞 F) O n ∈ J := by
  obtain ⟨ν, hνJ', hν0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  exact ⟨ν, hν0, algebraMap_mem_of_mem_leftNrdIdeal hO J hνJ'⟩

theorem cvvNF_inv_mul_inv (v : HeightOneSpectrum (𝓞 F)) (x y z : (QuatV v a b)ˣ) :
    ((cvvNF v x)⁻¹)⁻¹ * (cvvNF v y)⁻¹ * (cvvNF v z)⁻¹ = cvvNF v (x * y⁻¹ * z⁻¹) := by
  simp only [map_mul, map_inv, inv_inv]

/-- **From a double coset to the class relation:** if $(c(\beta)g)^{-1}g' \in K'$ for $g, g'$ attached to $J, J'$, then
$\mathfrak bJ' = \mathfrak aJ\beta^{-1}$ for nonzero integral ideals $\mathfrak a, \mathfrak b$. -/
theorem exists_scale_of_mem_KANF (ha : a ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J J' : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) (hJ' : leftNrdIdeal J' ≠ ⊥) {g g' : OAf (QP a b)} (hg : IsGenNF J g)
    (hg' : IsGenNF J' g') (β : (QuatF F a b)ˣ) (hβ : (diagF (QP a b) (cv0NF β) * g)⁻¹ * g' ∈ KANF O) :
    ∃ 𝔞 𝔟 : Ideal (𝓞 F), 𝔞 ≠ ⊥ ∧ 𝔟 ≠ ⊥ ∧ idealSet (Gen.scaleIdeal 𝔟 J') =
      rTrans (idealSet (Gen.scaleIdeal 𝔞 J)) ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) := by
  obtain ⟨n, hn0, hnJ⟩ := exists_nonzero_mem hO.1 hJ
  obtain ⟨n', hn0', hnJ'⟩ := exists_nonzero_mem hO.1 hJ'
  refine exists_scale_of_local hO.1 hn0 hn0' hnJ hnJ' β⁻¹ fun v => ?_
  obtain ⟨x, hx, hgx⟩ := hg v
  obtain ⟨x', hx', hgx'⟩ := hg' v
  obtain ⟨u, hu, hku⟩ := hβ v
  have hval : ((diagF (QP a b) (cv0NF β) * g)⁻¹ * g') v = cvvNF v (x * (complUnits v β)⁻¹ * x'⁻¹) := by
    rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, RestrictedProduct.mul_apply,
      diagF_cv0NF_apply, hgx, hgx']
    simp only [_root_.mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc]
  rw [hval] at hku
  have ha' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v ha)
  obtain ⟨r, hr⟩ := (cvHom_eq_iff (two_ne_zero_Fv v) ha' 1 u (x * (complUnits v β)⁻¹ * x'⁻¹)).1
    (congrArg (fun k : orthGroup (QP a b) (v.adicCompletion F) => (k : GL (Fin 3) (v.adicCompletion F))) hku)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hr, map_zero, zero_mul])
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
  rw [hx'eq, ← rTrans_rTrans, rTrans_localOrder_unit_nf v ((unitsOv v).inv_mem hu)]

theorem units_central_solve {G : Type*} [Group G] {x x' u d qA qB : G} (hA : ∀ y, qA * y = y * qA)
    (hB : ∀ y, qB * y = y * qB) (h : x' * qB = u * (x * qA * d)) : x * d * x'⁻¹ = qA⁻¹ * qB * u⁻¹ := by
  have h1 : x * qA * d = u⁻¹ * (x' * qB) := by rw [h]; group
  have h2 : x * d = qA⁻¹ * (u⁻¹ * (x' * qB)) := by
    rw [← h1, show x * qA * d = qA * (x * d) by rw [← hA x, mul_assoc]]; group
  calc x * d * x'⁻¹ = qA⁻¹ * (u⁻¹ * (x' * qB)) * x'⁻¹ := by rw [h2]
    _ = qA⁻¹ * u⁻¹ * (x' * (qB * x'⁻¹)) := by group
    _ = qA⁻¹ * u⁻¹ * (x' * (x'⁻¹ * qB)) := by rw [hB]
    _ = qA⁻¹ * (u⁻¹ * qB) := by group
    _ = qA⁻¹ * (qB * u⁻¹) := by rw [hB]
    _ = _ := by group

/-- **From the class relation to a double coset:** if $\mathfrak bJ' = \mathfrak aJ\delta$ then $(c(\delta^{-1})g)^{-1}g' \in K'$ for
$g, g'$ attached to $J, J'$. -/
theorem mem_KANF_of_scale (ha : a ≠ 0) {J J' : Ideal O} {g g' : OAf (QP a b)}
    (hg : IsGenNF J g) (hg' : IsGenNF J' g') {𝔞 𝔟 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) (δ : (QuatF F a b)ˣ)
    (h : idealSet (Gen.scaleIdeal 𝔟 J') = rTrans (idealSet (Gen.scaleIdeal 𝔞 J)) (δ : QuatF F a b)) :
    (diagF (QP a b) (cv0NF δ⁻¹) * g)⁻¹ * g' ∈ KANF O := by
  intro v
  obtain ⟨x, hx, hgx⟩ := hg v
  obtain ⟨x', hx', hgx'⟩ := hg' v
  have hloc := idealSet_localIdeal_rTrans_nf v h
  rw [localIdeal_scaleIdeal (O := O) v (map_ι_eq_span v h𝔟) J',
    localIdeal_scaleIdeal (O := O) v (map_ι_eq_span v h𝔞) J, hx, hx', rTrans_rTrans, rTrans_rTrans,
    rTrans_rTrans] at hloc
  set P := ((π v : v.adicCompletionIntegers F) : v.adicCompletion F)
  have hP0 : P ≠ 0 := by
    intro h0; have := valued_π v; rw [show ((π v : v.adicCompletionIntegers F) : v.adicCompletion F) = P from rfl,
      h0, map_zero] at this; exact WithZero.exp_ne_zero this.symm
  have hpow : ∀ e : ℕ, (((π v ^ e : v.adicCompletionIntegers F)) : v.adicCompletion F) = P ^ e := fun e => by
    push_cast; rfl
  rw [hpow, hpow] at hloc
  set A := P ^ cI v 𝔞
  set B := P ^ cI v 𝔟
  have hA0 : A ≠ 0 := pow_ne_zero _ hP0
  have hB0 : B ≠ 0 := pow_ne_zero _ hP0
  -- the two generators as units
  set X' : (QuatV v a b)ˣ := x' * qScalar B hB0
  set X : (QuatV v a b)ˣ := x * qScalar A hA0 * complUnits v δ
  have eX : ((X : (QuatV v a b)ˣ) : QuatV v a b) =
      (x : QuatV v a b) * (algebraMap (v.adicCompletion F) (QuatV v a b) A * complHom v a b (δ : QuatF F a b)) := by
    simp only [X, Units.val_mul, coe_qScalar, coe_complUnits, mul_assoc]
  have eX' : ((X' : (QuatV v a b)ˣ) : QuatV v a b) =
      (x' : QuatV v a b) * algebraMap (v.adicCompletion F) (QuatV v a b) B := by
    simp only [X', Units.val_mul, coe_qScalar]
  obtain ⟨u, hu, hXu⟩ := exists_unit_of_rTrans_eq_nf (O := O) v (x := X) (x' := X') (by
    rw [eX, eX']; exact hloc)
  have hval : ((diagF (QP a b) (cv0NF δ⁻¹) * g)⁻¹ * g') v = cvvNF v (x * complUnits v δ * x'⁻¹) := by
    rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, RestrictedProduct.mul_apply,
      diagF_cv0NF_apply, hgx, hgx', map_inv]
    simp only [_root_.mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc]
  rw [hval]
  refine (cvvNF_mem_KvNF_iff (O := O) v ha _).2 ?_
  refine ⟨B / A, u⁻¹, (unitsOv v).inv_mem hu, ?_⟩
  have hq : ∀ (c : v.adicCompletion F) (hc : c ≠ 0) (y : (QuatV v a b)ˣ), qScalar c hc * y = y * qScalar c hc :=
    fun c hc y => Units.ext (Algebra.commutes _ _)
  have key := units_central_solve (hq A hA0) (hq B hB0) hXu
  rw [key, Units.val_mul, Units.val_mul, qScalar_inv, coe_qScalar, coe_qScalar, ← map_mul]
  congr 2
  rw [div_eq_mul_inv, mul_comm]

set_option maxHeartbeats 1600000 in
/-- **Every element of $SO(Q)(\mathbb A_f)$ is attached to a nonzero left ideal** ($\mathcal O$ maximal, $D$ a division algebra). -/
theorem exists_isGenNF_of_mem (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0) {h : OAf (QP a b)} (hh : h ∈ soAf (QP a b)) :
    ∃ J : Ideal O, leftNrdIdeal J ≠ ⊥ ∧ IsGenNF J h := by
  classical
  -- step 1: local preimages, units where possible
  have hpre : ∀ v, ∃ y : (QuatV v a b)ˣ, cvvNF v y = h v ∧ (h v ∈ KvNF v O → y ∈ unitsOv (O := O) v) := by
    intro v
    by_cases hK : h v ∈ KvNF v O
    · obtain ⟨u, hu, e⟩ := hK
      exact ⟨u, e, fun _ => hu⟩
    · obtain ⟨α, hα⟩ := exists_cvvNF_eq v ha hb (h v) (hh v)
      exact ⟨α, hα, fun h' => absurd h' hK⟩
  choose y hy hyK using hpre
  -- step 2: the bad set is finite
  have hT : {v | h v ∉ KvNF v O}.Finite := finite_not_mem_KvNF ha hb hO hh
  set T := hT.toFinset
  have hvT : ∀ v, v ∉ T → h v ∈ KvNF v O := fun v hv => by
    by_contra hc; exact hv (hT.mem_toFinset.2 hc)
  -- step 3: integral local generators `x_v = ϖ^N y_v⁻¹`
  have hint : ∀ v, ∃ N : ℕ, algebraMap (v.adicCompletion F) (QuatV v a b)
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (π v) ^ N) *
        (((y v)⁻¹ : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O ∧ (v ∉ T → N = 0) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨N, hN⟩ := exists_pi_pow_mul_mem_localOrder (O := O) v hO.1 (((y v)⁻¹ : (QuatV v a b)ˣ) : QuatV v a b)
      exact ⟨N, hN, fun h' => absurd hv h'⟩
    · refine ⟨0, ?_, fun _ => rfl⟩
      rw [pow_zero, map_one, one_mul]
      exact (hyK v (hvT v hv)).2
  choose N hNmem hN0 using hint
  have hϖ0 : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (π v) ^ N v ≠ 0 := fun v =>
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (irreducible_π v).ne_zero)
  set x : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV v a b)ˣ := fun v =>
    qScalar (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (π v) ^ N v) (hϖ0 v) * (y v)⁻¹
  have hxO : ∀ v, ((x v : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O := fun v => hNmem v
  have hxh : ∀ v, h v = (cvvNF v (x v))⁻¹ := by
    intro v
    simp only [x, map_mul, cvvNF_scalar v ha (hϖ0 v), one_mul, map_inv, inv_inv, hy v]
  have hxu : ∀ v, v ∉ T → x v ∈ unitsOv (O := O) v := by
    intro v hv
    have h1 : x v = (y v)⁻¹ := Units.ext (by
      simp only [x, hN0 v hv, pow_zero, Units.val_mul, coe_qScalar, map_one, one_mul])
    rw [h1]; exact (unitsOv v).inv_mem (hyK v (hvT v hv))
  -- step 4: the local ideals
  set I : ∀ v : HeightOneSpectrum (𝓞 F), Ideal (localOrder (v := v) a b O) := fun v =>
    Ideal.span {(⟨(x v : QuatV v a b), hxO v⟩ : localOrder (v := v) a b O)}
  have hI : ∀ v, idealSet (I v) = rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) (x v : QuatV v a b) :=
    fun v => idealSet_span_singleton _
  -- step 5: a global `n` divisible enough at the places of `T`
  have hexp : ∀ v, ∃ e : ℕ, 1 ≤ e ∧ exp (-(e : ℤ)) ≤ Valued.v (nrd ((x v : (QuatV v a b)ˣ) : QuatV v a b)) := by
    intro v
    obtain ⟨k, hk⟩ := exists_valued_eq_exp v (nrd_units_ne_zero (x v))
    refine ⟨(-k).toNat + 1, by omega, ?_⟩
    rw [hk, WithZero.exp_le_exp]; omega
  choose e he1 he using hexp
  have hprod : (∏ w ∈ T, w.asIdeal ^ e w) ≠ ⊥ := prod_pow_ne_bot T e
  obtain ⟨n, hnmem, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprod
  have hnv : ∀ v ∈ T, n ∈ v.asIdeal ^ e v := fun v hv =>
    Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) hnmem
  have hTsub : ∀ v ∈ T, v ∈ Gen.primeSupport hn0 := fun v hv =>
    (Gen.mem_primeSupport hn0).2 (Ideal.pow_le_self (by have := he1 v; omega) (hnv v hv))
  -- step 6: `ι_v(n) ∈ I_v` at the places of the support
  have hnI : ∀ v ∈ Gen.primeSupport hn0,
      algebraMap (v.adicCompletionIntegers F) (localOrder (v := v) a b O) (ι v n) ∈ I v := by
    intro v _
    by_cases hvT : v ∈ T
    · have hnrd0 := nrd_units_ne_zero (x v)
      have hvaln : Valued.v ((ι v n : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ exp (-(e v : ℤ)) := by
        have h1 := (ι_mem_span_π_pow v (e v) n).2 (hnv v hvT)
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
        rw [← hc, Subring.coe_mul, map_mul, Subring.coe_pow, map_pow, valued_π]
        calc Valued.v ((c : v.adicCompletionIntegers F) : v.adicCompletion F) * exp (-1 : ℤ) ^ e v
            ≤ 1 * exp (-1 : ℤ) ^ e v := mul_le_mul_left c.2 _
          _ = exp (-(e v : ℤ)) := by rw [one_mul, ← WithZero.exp_nsmul]; simp
      set t : v.adicCompletion F := ((ι v n : v.adicCompletionIntegers F) : v.adicCompletion F) /
        nrd ((x v : (QuatV v a b)ˣ) : QuatV v a b)
      have ht : Valued.v t ≤ 1 := by
        rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hnrd0))]
        exact hvaln.trans (he v)
      set t' : v.adicCompletionIntegers F := ⟨t, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ht⟩
      have hstar : star ((x v : (QuatV v a b)ˣ) : QuatV v a b) ∈ localOrder (v := v) a b O :=
        star_mem_of_isOrder (Gen.isOrder_localOrder_gen v hO.1) (hxO v)
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
    · have hu := hxu v hvT
      have htop : I v = ⊤ := by
        rw [Ideal.eq_top_iff_one]
        have h1 : (⟨(((x v)⁻¹ : (QuatV v a b)ˣ) : QuatV v a b), hu.2⟩ : localOrder (v := v) a b O) *
            ⟨_, hxO v⟩ = 1 := Subtype.ext (by
          rw [Subalgebra.coe_mul, Units.inv_mul, OneMemClass.coe_one])
        rw [← h1]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      rw [htop]; exact Submodule.mem_top
  -- step 7: the global ideal
  set J := globalIdeal (Gen.primeSupport hn0) I
  have hnJ : algebraMap (𝓞 F) O n ∈ J := Gen.algebraMap_mem_globalIdeal hnI
  refine ⟨J, ?_, fun v => ⟨x v, ?_, hxh v⟩⟩
  · refine Gen.leftNrdIdeal_ne_bot hO.1 hdiv fun hbot => hn0 ?_
    rw [hbot] at hnJ
    have h0 : algebraMap (𝓞 F) O n = 0 := hnJ
    have := congrArg Subtype.val h0
    simp only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1
      ((map_eq_zero_iff _ (algebraMap F (QuatF F a b)).injective).1 (by
        rw [← IsScalarTower.algebraMap_apply]; exact this))
  · by_cases hv : v ∈ Gen.primeSupport hn0
    · rw [Gen.localIdeal_globalIdeal hO.1 hn0 I hnI v hv, hI]
    · have hvn : n ∉ v.asIdeal := fun h' => hv ((Gen.mem_primeSupport hn0).2 h')
      have hvT : v ∉ T := fun h' => hv (hTsub v h')
      rw [Gen.localIdeal_eq_top v hnJ hvn, idealSet_top_local_nf]
      exact (rTrans_localOrder_unit_nf v (hxu v hvT)).symm

end QuadFormsKB.QuatOrder
