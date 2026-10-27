/-
# The index of a left ideal in a maximal order: $[\mathcal O : J] = \operatorname{nrd}(J)^2$

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, $D = (a,b)_F$ ($ab \ne 0$), $\mathcal O$ a maximal $\mathcal O_F$-order with $\mathcal O_F$-basis
$e_0,\dots,e_3$.

Let $J$ be a left ideal with $\operatorname{nrd}(J) \ne 0$, generated over $\mathcal O_F$ by $f_0,\dots,f_3$ with $f_j = \sum_iB_{ij}e_i$ and
$\det B \ne 0$. Then (`span_det_eq_sq`)
$$(\det B) = \operatorname{nrd}(J)^2 \quad\text{as ideals of } \mathcal O_F,$$
i.e. the $\mathcal O_F$-index $[\mathcal O : J]$ is $\operatorname{nrd}(J)^2$. *Proof, at each finite place $v$:* $J_v = \mathcal O_v\alpha$ (local principality,
`exists_localIdeal_eq_rTrans`) with $(\operatorname{nrd}\alpha) = \operatorname{nrd}(J)\mathfrak o_v$ (`leftNrdIdeal_eq_of_idealSet_eq_rTrans`, the
`leftNrdIdeal_localIdeal`); the families $(f_j)$ and $(e_i\alpha)$ generate the same $\mathfrak o_v$-module $J_v$, so in the $F_v$-basis $E = \iota_v(e)$ of
$D_v$ their coordinate matrices satisfy $B = RU$, $R = BW$ with $U, W$ integral; hence $\det U \in \mathfrak o_v^\times$ and
$\det B \sim \det R = \det(x\mapsto x\alpha) = \operatorname{nrd}(\alpha)^2$ (`det_mulRight`). Divisibility is local (`dvd_of_forall_ι_dvd`).

Source: Voight, *Quaternion Algebras* (2021), Lemma 16.4.? / Prop. 16.4.3 and (16.4.10) ($[\mathcal O : J]_{\mathcal O_F} = \operatorname{nrd}(J)^2$ for
invertible $J$; there via $\operatorname{disc}$ and local principality); locators checked in the author's PDF.
-/
import QuadFormsKB.Tamagawa.QuatLocalPrincipal

open NumberField IsDedekindDomain Quaternion IsLocalization

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF

/-! ### The reduced norm of a principal left ideal -/

section NrdPrincipal

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {a b : K}

/-- **$\operatorname{nrd}(\mathcal O\alpha) = (\operatorname{nrd}\alpha)$** for an $R$-order (reduced norms integral). -/
theorem leftNrdIdeal_eq_of_idealSet_eq_rTrans {O : Subalgebra R ℍ[K,a,b]} (hinj : Function.Injective (algebraMap R K))
    (hOint : ∀ y ∈ O, IsInteger R (nrd y)) {I : Ideal O} {α : ℍ[K,a,b]}
    (hI : idealSet I = rTrans (O : Set ℍ[K,a,b]) α) {t : R} (ht : algebraMap R K t = nrd α) :
    leftNrdIdeal I = Ideal.span {t} := by
  apply le_antisymm
  · rw [leftNrdIdeal, Ideal.span_le]
    rintro r ⟨x, hx, hr⟩
    have hx' : (x : ℍ[K,a,b]) ∈ rTrans (O : Set ℍ[K,a,b]) α := hI ▸ coe_mem_idealSet.2 hx
    obtain ⟨y, hy, hyx⟩ := hx'
    obtain ⟨s, hs⟩ := hOint y hy
    have : r = s * t := hinj (by rw [hr, ← hyx, nrd_mul, map_mul, hs, ht])
    rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hα : α ∈ idealSet I := by rw [hI]; exact ⟨1, O.one_mem, one_mul α⟩
    obtain ⟨hαO, hαI⟩ := hα
    exact Ideal.subset_span ⟨⟨α, hαO⟩, hαI, ht⟩

end NrdPrincipal

/-! ### Local principality at the completions -/

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **Left ideals of $\mathcal O_v$ with nonzero reduced norm are principal** ($\mathcal O$ maximal). -/
theorem exists_localIdeal_eq_rTrans (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (I : Ideal (localOrder (v := v) a b O)) (hI : leftNrdIdeal I ≠ ⊥) :
    ∃ α : QuatV v a b, nrd α ≠ 0 ∧ idealSet I = rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) α := by
  rcases localOrder_ramified_or_split (v := v) ha hb hO with ⟨hdiv, heq⟩ | ⟨φ, hφ⟩
  · exact exists_eq_rTrans_of_valOrder hdiv _ heq I hI
  · exact exists_eq_rTrans_of_map_eq_matOrder φ _ hφ I hI

end Local

/-! ### The index–norm relation -/

section Index

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The local step:** at every finite place, $\iota_v(\det B)$ and $\iota_v(\nu)^2$ are associated, $(\nu) = \operatorname{nrd}(J)$. -/
theorem associated_ι_det (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) {J : Ideal O} {ν : 𝓞 F} (hν0 : ν ≠ 0)
    (hν : leftNrdIdeal J = Ideal.span {ν}) (f : Fin 4 → QuatF F a b)
    (hspan : ∀ x ∈ idealSet J, ∃ c : Fin 4 → 𝓞 F, x = ∑ j, algebraMap (𝓞 F) F (c j) • f j)
    (hfJ : ∀ j, f j ∈ idealSet J)
    (B : Matrix (Fin 4) (Fin 4) (𝓞 F)) (hB : ∀ j, f j = ∑ i, algebraMap (𝓞 F) F (B i j) • (e i : QuatF F a b))
    (hdet : B.det ≠ 0) :
    Associated (ι v B.det) (ι v ν ^ 2) := by
  set I := localIdeal (v := v) J
  have hOv := isOrder_localOrder (v := v) hO.1
  have hIν : leftNrdIdeal I = Ideal.span {ι v ν} := by
    rw [leftNrdIdeal_localIdeal hO.1, hν, Ideal.map_span, Set.image_singleton]
  have hI0 : leftNrdIdeal I ≠ ⊥ := by
    rw [hIν, Ne, Ideal.span_singleton_eq_bot]; exact ι_ne_zero v hν0
  obtain ⟨α, hα0, hIα⟩ := exists_localIdeal_eq_rTrans ha hb hO I hI0
  -- α ∈ O_v and nrd α = t
  have hαO : α ∈ localOrder (v := v) a b O := by
    have : α ∈ idealSet I := by rw [hIα]; exact ⟨1, Subalgebra.one_mem _, one_mul α⟩
    exact idealSet_subset I this
  obtain ⟨t, ht⟩ := (isInteger_trd_nrd hOv hαO).2
  have hIt : leftNrdIdeal I = Ideal.span {t} :=
    leftNrdIdeal_eq_of_idealSet_eq_rTrans (IsFractionRing.injective _ _)
      (fun y hy => (isInteger_trd_nrd hOv hy).2) hIα ht
  have hassoc1 : Associated (ι v ν) t := Ideal.span_singleton_eq_span_singleton.1 (hIν.symm.trans hIt)
  -- the basis E of D_v
  set E := complBasis (v := v) e hO.1
  have hE : ∀ i, E i = complHom v a b (e i : QuatF F a b) := fun i => by
    rw [complBasis_apply]; rfl
  set Fj : Fin 4 → QuatV v a b := fun j => complHom v a b (f j)
  have hFj : ∀ j, Fj j = ∑ i, algebraMap 𝔬 Fv (ι v (B i j)) • E i := by
    intro j
    simp only [Fj, hB j, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hE i, ← algebraMap_smul Fv (algebraMap (𝓞 F) F (B i j))]; rfl
  -- coordinates
  have hrepr : ∀ (c : Fin 4 → Fv) (k : Fin 4), E.repr (∑ i, c i • E i) k = c k := by
    intro c k
    rw [map_sum]; simp [Finsupp.single_apply]
  set cR : Matrix (Fin 4) (Fin 4) Fv := Matrix.of fun k i => E.repr (E i * α) k
  have hcR : cR.det = nrd α ^ 2 := by
    have : cR = LinearMap.toMatrix E E (LinearMap.mulRight Fv α) := by
      refine Matrix.ext fun k i => ?_; rw [LinearMap.toMatrix_apply]; rfl
    rw [this, LinearMap.det_toMatrix, det_mulRight]
  set Bv : Matrix (Fin 4) (Fin 4) Fv := (B.map (ι v)).map (algebraMap 𝔬 Fv)
  have hBv : ∀ k j, E.repr (Fj j) k = Bv k j := fun k j => by rw [hFj, hrepr]; rfl
  -- (1) F_j = Σ_i u_ij (E_i α)
  have hU : ∀ j, ∃ u : Fin 4 → 𝔬, Fj j = ∑ i, algebraMap 𝔬 Fv (u i) • (E i * α) := by
    intro j
    have hmem : Fj j ∈ idealSet I := by
      have hfO : f j ∈ O := idealSet_subset J (hfJ j)
      refine ⟨mem_localOrder_of_mem a b hfO, ?_⟩
      rw [mem_localIdeal_iff]
      obtain ⟨hfO', hfJ'⟩ := hfJ j
      exact complHom_mem_span_idealImage hfJ'
    rw [hIα] at hmem
    obtain ⟨y, hy, hyF⟩ := hmem
    have hyc := (mem_localOrder_iff e hO.1 y).1 hy
    choose u hu using hyc
    refine ⟨u, ?_⟩
    rw [← hyF]
    show y * α = _
    conv_lhs => rw [← E.sum_repr y]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu i, smul_mul_assoc]
  choose u hu using hU
  -- (2) E_i α = Σ_j w_ji F_j
  have hspanv : Submodule.span 𝔬 (idealImage (v := v) J) ≤ Submodule.span 𝔬 (Set.range Fj) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := hspan x (coe_mem_idealSet.2 hx)
    simp only
    rw [hc, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [complHom_smul_int]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hW : ∀ i, ∃ w : Fin 4 → 𝔬, E i * α = ∑ j, w j • Fj j := by
    intro i
    have hmem : E i * α ∈ idealSet I := by
      rw [hIα]
      refine ⟨E i, ?_, rfl⟩
      rw [hE]; exact mem_localOrder_of_mem a b (e i).2
    obtain ⟨_, hmemI⟩ := hmem
    have := hspanv ((mem_localIdeal_iff).1 hmemI)
    exact (Submodule.mem_span_range_iff_exists_fun 𝔬).1 this |>.imp fun w hw => hw.symm
  choose w hw using hW
  -- matrix identities
  set Uv : Matrix (Fin 4) (Fin 4) Fv := Matrix.of fun i j => algebraMap 𝔬 Fv (u j i)
  set Wv : Matrix (Fin 4) (Fin 4) Fv := Matrix.of fun j i => algebraMap 𝔬 Fv (w i j)
  have h1 : Bv = cR * Uv := by
    refine Matrix.ext fun k j => ?_
    rw [← hBv, hu j, map_sum]
    simp only [Matrix.mul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, cR, Uv, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : cR = Bv * Wv := by
    refine Matrix.ext fun k i => ?_
    simp only [cR, Matrix.of_apply]
    rw [hw i, map_sum]
    simp only [Matrix.mul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Wv, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul Fv (w i j), map_smul, Finsupp.smul_apply, smul_eq_mul, hBv, mul_comm]
  have hBdet : Bv.det = algebraMap 𝔬 Fv (ι v B.det) := by
    simp only [Bv]
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hBdet0 : Bv.det ≠ 0 := by
    rw [hBdet]; exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v hdet)
  have hUdet : Uv.det = algebraMap 𝔬 Fv (Matrix.of fun i j => u j i).det := by
    rw [RingHom.map_det]; rfl
  have hWdet : Wv.det = algebraMap 𝔬 Fv (Matrix.of fun j i => w i j).det := by
    rw [RingHom.map_det]; rfl
  have hWU : Wv.det * Uv.det = 1 := by
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h2, Matrix.det_mul] at this
    have h' : Bv.det * (Wv.det * Uv.det) = Bv.det * 1 := by rw [mul_one, ← mul_assoc]; exact this.symm
    exact mul_left_cancel₀ hBdet0 h'
  have hunit : IsUnit (Matrix.of fun i j => u j i).det := by
    rw [hUdet, hWdet, ← map_mul] at hWU
    have h1' : (Matrix.of fun j i => w i j).det * (Matrix.of fun i j => u j i).det = 1 :=
      IsFractionRing.injective 𝔬 Fv (by rw [hWU, map_one])
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h1')
  -- ι(det B) = t² · det U
  have hkey : ι v B.det = t ^ 2 * (Matrix.of fun i j => u j i).det := by
    apply IsFractionRing.injective 𝔬 Fv
    rw [← hBdet, h1, Matrix.det_mul, hcR, hUdet, map_mul, map_pow, ht]
  have hassoc2 : Associated (ι v B.det) (t ^ 2) := by
    rw [hkey]; exact (associated_mul_isUnit_left_iff hunit).2 (Associated.refl _)
  exact hassoc2.trans (hassoc1.pow_pow (n := 2)).symm

/-- **The index–norm relation** $(\det B) = \operatorname{nrd}(J)^2$ (Voight 2021, (16.4.10) for invertible lattices of a maximal order). -/
@[kb "voight2021" "Lemma 16.4.11; (16.4.10)"]
theorem span_det_eq_sq (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥)
    (f : Fin 4 → QuatF F a b)
    (hspan : ∀ x ∈ idealSet J, ∃ c : Fin 4 → 𝓞 F, x = ∑ j, algebraMap (𝓞 F) F (c j) • f j)
    (hfJ : ∀ j, f j ∈ idealSet J)
    (B : Matrix (Fin 4) (Fin 4) (𝓞 F)) (hB : ∀ j, f j = ∑ i, algebraMap (𝓞 F) F (B i j) • (e i : QuatF F a b))
    (hdet : B.det ≠ 0) :
    Ideal.span {B.det} = leftNrdIdeal J ^ 2 := by
  obtain ⟨ν, hν⟩ := (IsPrincipalIdealRing.principal (leftNrdIdeal J)).principal
  have hν' : leftNrdIdeal J = Ideal.span {ν} := hν
  have hν0 : ν ≠ 0 := by rintro rfl; exact hJ (by rw [hν', Ideal.span_singleton_eq_bot.2 rfl])
  have hloc := fun v => associated_ι_det v ha hb hO e hν0 hν' f hspan hfJ B hB hdet
  have d1 : ν ^ 2 ∣ B.det := dvd_of_forall_ι_dvd (pow_ne_zero 2 hν0) fun v => by
    rw [map_pow]; exact (hloc v).symm.dvd
  have d2 : B.det ∣ ν ^ 2 := dvd_of_forall_ι_dvd hdet fun v => by
    rw [map_pow]; exact (hloc v).dvd
  rw [hν', Ideal.span_singleton_pow]
  exact Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd d2 d1)

end Index

end QuadFormsKB.QuatOrder
