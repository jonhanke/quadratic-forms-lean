/-
# The inverse of a left ideal: $(\mathcal O : J) = \nu^{-1}\bar J$

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, $D = (a,b)_F$ ($ab \ne 0$), $\mathcal O$ a maximal $\mathcal O_F$-order, $J$ a left ideal with
$\operatorname{nrd}(J) = (\nu) \ne 0$.

* Local–global principles for elements (`mem_of_forall_toLocal_mem`, `mem_order_of_forall_complHom_mem`): $z \in J$ (resp. $z \in \mathcal O$)
  as soon as $\iota_v(z) \in J_v$ (resp. $\mathcal O_v$) at every finite place, from `le_of_localIdeal_le`.
* `exists_local_generator`: $J_v = \mathcal O_v\alpha$ with $\operatorname{nrd}\alpha \sim \nu$ in $\mathfrak o_v$.
* `mul_star_mem`: $\nu^{-1}y\bar x \in \mathcal O$ for $x, y \in J$ (locally $y\bar x = p\alpha\bar\alpha\bar q = \operatorname{nrd}(\alpha)p\bar q$).
* `smul_star_mem_of_mem_colon`: $\beta \in (\mathcal O : J) \Rightarrow \nu\bar\beta \in J$ (locally $\beta \in \alpha^{-1}\mathcal O_v$).

Hence $(\mathcal O : J) = \nu^{-1}\bar J$ (`mem_colon_iff`), and the Epstein sum of the class unfolds over $J$ itself:
$E_J(s) = N(\nu)^{2s}\,E'_J(s)$, $E'_J(s) = \sum_{x\in\mathcal O_F^\times\backslash(J\setminus0)}|N(\operatorname{nrd}x)|^{-s}$ (`epsteinSum_eq`).

Source: Voight, *Quaternion Algebras* (2021), §16.5–16.6 (invertible lattices: $J^{-1} = \bar J/\operatorname{nrd}(J)$, Prop. 16.6.15, and
$J\bar J = \operatorname{nrd}(J)\mathcal O_L(J)$, Lemma 16.3.7, Prop. 16.4.3); Thm. 9.4.9 (local–global for lattices). Locators checked in the author's PDF.
-/
import QuadFormsKB.Tamagawa.QuatIdealIndex

open NumberField IsDedekindDomain Quaternion IsLocalization

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF

section LocalGlobalElt

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-- **Membership in $J$ is local:** if $n \ne 0$, $n \in J$ and $\iota_v(z) \in J_v$ at every $v$, then $z \in J$. -/
theorem mem_of_forall_toLocal_mem (hO : IsOrder (𝓞 F) F O) {J : Ideal O} {n : 𝓞 F} (hn : n ≠ 0)
    (hnJ : algebraMap (𝓞 F) O n ∈ J) {z : O} (hz : ∀ v, toLocal v z ∈ localIdeal (v := v) J) : z ∈ J := by
  refine le_of_localIdeal_le hO hn (J₁ := Ideal.span {z}) hnJ (fun v _ => ?_) (Ideal.subset_span rfl)
  intro y hy
  refine span_le_of_forall_mem v (T := idealImage (v := v) (Ideal.span {z})) ?_ ((mem_localIdeal_iff).1 hy)
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
  refine ⟨mem_localOrder_of_mem a b (o • z).2, ?_⟩
  have : (⟨complHom v a b ((o • z : O) : QuatF F a b), mem_localOrder_of_mem a b (o • z).2⟩ :
      localOrder (v := v) a b O) = toLocal v o * toLocal v z := by
    apply Subtype.ext
    simp only [smul_eq_mul, Subalgebra.coe_mul, map_mul]; rfl
  rw [this]
  exact Ideal.mul_mem_left _ _ (hz v)

/-- Every quaternion has a nonzero multiple in an order. -/
theorem exists_smul_mem_order (hO : IsOrder (𝓞 F) F O) (z : QuatF F a b) :
    ∃ n : 𝓞 F, n ≠ 0 ∧ algebraMap (𝓞 F) F n • z ∈ O := by
  have hz : z ∈ Submodule.span F (O : Set (QuatF F a b)) := hO.span ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [map_one, one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact O.zero_mem⟩
  | add y w _ _ hy hw =>
    obtain ⟨n, hn, hny⟩ := hy; obtain ⟨m, hm, hmw⟩ := hw
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add, map_mul]
    refine O.add_mem ?_ ?_
    · rw [mul_comm, mul_smul, algebraMap_smul F m]
      exact O.smul_mem hny m
    · rw [mul_smul, algebraMap_smul F n]
      exact O.smul_mem hmw n
  | smul c y _ hy =>
    obtain ⟨n, hn, hny⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    refine ⟨q * n, mul_ne_zero hq0 hn, ?_⟩
    have hqF : algebraMap (𝓞 F) F q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hq0
    have : algebraMap (𝓞 F) F (q * n) • ((algebraMap (𝓞 F) F p / algebraMap (𝓞 F) F q) • y) =
        p • (algebraMap (𝓞 F) F n • y) := by
      rw [smul_smul, ← algebraMap_smul F p (algebraMap (𝓞 F) F n • y), smul_smul, map_mul]
      congr 1; field_simp
    rw [this]; exact O.smul_mem hny p

/-- **Membership in $\mathcal O$ is local:** if $\iota_v(z) \in \mathcal O_v$ at every finite place then $z \in \mathcal O$. -/
theorem mem_order_of_forall_complHom_mem (hO : IsOrder (𝓞 F) F O) {z : QuatF F a b}
    (hz : ∀ v, complHom v a b z ∈ localOrder (v := v) a b O) : z ∈ O := by
  obtain ⟨n, hn, hnz⟩ := exists_smul_mem_order hO z
  set J₂ : Ideal O := Ideal.span {algebraMap (𝓞 F) O n}
  have hnJ : algebraMap (𝓞 F) O n ∈ J₂ := Ideal.subset_span rfl
  have hw : (⟨_, hnz⟩ : O) ∈ J₂ := by
    refine mem_of_forall_toLocal_mem hO hn hnJ fun v => ?_
    have h1 : toLocal v (⟨_, hnz⟩ : O) = ⟨complHom v a b z, hz v⟩ * toLocal v (algebraMap (𝓞 F) O n) := by
      apply Subtype.ext
      simp only [toLocal, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subalgebra.coe_mul,
        Subalgebra.coe_algebraMap]
      rw [← map_mul, ← Algebra.commutes, ← Algebra.smul_def]
      congr 1
    rw [h1]
    exact Ideal.mul_mem_left _ _ (complHom_mem_span_idealImage hnJ)
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hw
  have ho' : (o : QuatF F a b) * algebraMap (𝓞 F) (QuatF F a b) n = algebraMap (𝓞 F) F n • z :=
    congrArg Subtype.val ho
  have hnF : algebraMap (𝓞 F) F n ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hn
  have : z = (o : QuatF F a b) := by
    rw [← Algebra.commutes, ← Algebra.smul_def, ← algebraMap_smul F] at ho'
    exact (smul_right_injective _ hnF ho').symm
  rw [this]; exact o.2

end LocalGlobalElt

section Inverse

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

theorem complHom_star (v : HeightOneSpectrum (𝓞 F)) (x : QuatF F a b) :
    complHom v a b (star x) = star (complHom v a b x) := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp only [complHom_re, complHom_imI, complHom_imJ, complHom_imK, QuaternionAlgebra.re_star,
      QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, map_neg,
      zero_mul, add_zero]

theorem complHom_mem_idealSet_localIdeal (v : HeightOneSpectrum (𝓞 F)) {J : Ideal O} {x : QuatF F a b}
    (hx : x ∈ idealSet J) : complHom v a b x ∈ idealSet (localIdeal (v := v) J) := by
  obtain ⟨hxO, hxJ⟩ := hx
  exact ⟨mem_localOrder_of_mem a b hxO, complHom_mem_span_idealImage hxJ⟩

/-- **Local generators:** $J_v = \mathcal O_v\alpha$ with $\alpha \in \mathcal O_v$ and $\operatorname{nrd}\alpha = t \sim \nu$. -/
theorem exists_local_generator (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} {ν : 𝓞 F}
    (hν0 : ν ≠ 0) (hν : leftNrdIdeal J = Ideal.span {ν}) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (α : QuatV v a b) (t : v.adicCompletionIntegers F), α ∈ localOrder (v := v) a b O ∧
      idealSet (localIdeal (v := v) J) = rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) α ∧
      algebraMap _ (v.adicCompletion F) t = nrd α ∧ Associated (ι v ν) t := by
  set I := localIdeal (v := v) J
  have hOv := isOrder_localOrder (v := v) hO.1
  have hIν : leftNrdIdeal I = Ideal.span {ι v ν} := by
    rw [leftNrdIdeal_localIdeal hO.1, hν, Ideal.map_span, Set.image_singleton]
  have hI0 : leftNrdIdeal I ≠ ⊥ := by
    rw [hIν, Ne, Ideal.span_singleton_eq_bot]; exact ι_ne_zero v hν0
  obtain ⟨α, -, hIα⟩ := exists_localIdeal_eq_rTrans ha hb hO I hI0
  have hαO : α ∈ localOrder (v := v) a b O := by
    have : α ∈ idealSet I := by rw [hIα]; exact ⟨1, Subalgebra.one_mem _, one_mul α⟩
    exact idealSet_subset I this
  obtain ⟨t, ht⟩ := (isInteger_trd_nrd hOv hαO).2
  have hIt : leftNrdIdeal I = Ideal.span {t} :=
    leftNrdIdeal_eq_of_idealSet_eq_rTrans (IsFractionRing.injective _ _)
      (fun y hy => (isInteger_trd_nrd hOv hy).2) hIα ht
  exact ⟨α, t, hαO, hIα, ht, Ideal.span_singleton_eq_span_singleton.1 (hIν.symm.trans hIt)⟩

/-- **$J\bar J \subseteq \nu\mathcal O$:** $\nu^{-1}y\bar x \in \mathcal O$ for $x, y \in J$. -/
theorem mul_star_mem (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} {ν : 𝓞 F}
    (hν0 : ν ≠ 0) (hν : leftNrdIdeal J = Ideal.span {ν}) {x y : QuatF F a b} (hx : x ∈ idealSet J)
    (hy : y ∈ idealSet J) : (algebraMap (𝓞 F) F ν)⁻¹ • (y * star x) ∈ O := by
  refine mem_order_of_forall_complHom_mem hO.1 fun v => ?_
  obtain ⟨α, t, hαO, hIα, ht, hassoc⟩ := exists_local_generator ha hb hO hν0 hν v
  have hx' := complHom_mem_idealSet_localIdeal v hx
  have hy' := complHom_mem_idealSet_localIdeal v hy
  rw [hIα] at hx' hy'
  obtain ⟨q, hq, hqx⟩ := hx'
  obtain ⟨p, hp, hpy⟩ := hy'
  obtain ⟨u, hu⟩ := hassoc.symm
  -- t * u = ι ν
  have hOv := isOrder_localOrder (v := v) hO.1
  have hνt : algebraMap _ (v.adicCompletion F) (ι v ν) = algebraMap _ (v.adicCompletion F) t *
      algebraMap _ (v.adicCompletion F) (u : v.adicCompletionIntegers F) := by rw [← map_mul, hu]
  have hνF : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F ν) = algebraMap _ (v.adicCompletion F) (ι v ν) := rfl
  have ht0 : algebraMap _ (v.adicCompletion F) t ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hνt
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v hν0) (by rw [← hνF] at hνt ⊢; exact hνt)
  rw [map_smul, map_mul, complHom_star, ← hqx, ← hpy]
  simp only
  rw [star_mul, mul_assoc, ← mul_assoc α, mul_star_eq_nrd, ← ht]
  rw [← algebraMap_smul (v.adicCompletion F), map_inv₀, hνF, hνt]
  have hu' : algebraMap _ (v.adicCompletion F) ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) *
      algebraMap _ (v.adicCompletion F) (u : v.adicCompletionIntegers F) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e : (algebraMap _ (v.adicCompletion F) t * algebraMap _ (v.adicCompletion F) (u : v.adicCompletionIntegers F))⁻¹ •
      (p * (((algebraMap _ (v.adicCompletion F) t : v.adicCompletion F) : QuatV v a b) * star q)) =
      ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) • (p * star q) := by
    rw [← algebraMap_smul (v.adicCompletion F) (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F))]
    rw [QuaternionAlgebra.coe_mul_eq_smul, mul_smul_comm, smul_smul]
    congr 1
    have hu0 : algebraMap _ (v.adicCompletion F) (u : v.adicCompletionIntegers F) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 u.ne_zero
    rw [eq_inv_of_mul_eq_one_left hu']
    field_simp
  rw [e]
  exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hp (star_mem_of_isOrder hOv hq)) _

/-- **$(\mathcal O : J) \subseteq \nu^{-1}\bar J$:** for $\beta \in (\mathcal O : J)$, $\nu\bar\beta \in J$. -/
theorem smul_star_mem_of_mem_colon (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    {ν : 𝓞 F} (hν0 : ν ≠ 0) (hν : leftNrdIdeal J = Ideal.span {ν}) {β : QuatF F a b} (hβ : β ∈ colon J) :
    algebraMap (𝓞 F) F ν • star β ∈ idealSet J := by
  have hOv := fun v => isOrder_localOrder (v := v) hO.1
  -- the local statement: ι(νβ̄) = c • (γ̄ α) with c ∈ 𝔬, γ ∈ O_v
  have hloc : ∀ v, ∃ y ∈ localOrder (v := v) a b O, ∃ α : QuatV v a b,
      idealSet (localIdeal (v := v) J) = rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) α ∧
      complHom v a b (algebraMap (𝓞 F) F ν • star β) = y * α := by
    intro v
    obtain ⟨α, t, hαO, hIα, ht, hassoc⟩ := exists_local_generator ha hb hO hν0 hν v
    -- γ = α ι(β) ∈ O_v
    have hαJ : α ∈ Submodule.span (v.adicCompletionIntegers F) (idealImage (v := v) J) := by
      have : α ∈ idealSet (localIdeal (v := v) J) := by rw [hIα]; exact ⟨1, Subalgebra.one_mem _, one_mul α⟩
      obtain ⟨_, h⟩ := this; exact (mem_localIdeal_iff).1 h
    have hgen : ∀ z ∈ Submodule.span (v.adicCompletionIntegers F) (idealImage (v := v) J),
        z * complHom v a b β ∈ localOrder (v := v) a b O := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        rw [← map_mul]
        exact mem_localOrder_of_mem a b (hβ _ (coe_mem_idealSet.2 hx))
      | zero => rw [zero_mul]; exact Subalgebra.zero_mem _
      | add z w _ _ hz hw => rw [add_mul]; exact Subalgebra.add_mem _ hz hw
      | smul c z _ hz => rw [smul_mul_assoc]; exact Subalgebra.smul_mem _ hz c
    have hγ := hgen α hαJ
    set γ := α * complHom v a b β
    obtain ⟨u, hu⟩ := hassoc
    -- ι ν * u = t
    have hνF : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F ν) =
        algebraMap _ (v.adicCompletion F) (ι v ν) := rfl
    have ht0 : nrd α ≠ 0 := by
      rw [← ht, ← hu, map_mul]
      exact mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v hν0))
        ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 u.ne_zero)
    -- ι(β) = nrd(α)⁻¹ • (ᾱ γ)
    have hβv : complHom v a b β = (nrd α)⁻¹ • (star α * γ) := by
      rw [← mul_assoc, star_mul_eq_nrd, QuaternionAlgebra.coe_mul_eq_smul, smul_smul, inv_mul_cancel₀ ht0,
        one_smul]
    refine ⟨((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) • star γ,
      Subalgebra.smul_mem _ (star_mem_of_isOrder (hOv v) hγ) _, α, hIα, ?_⟩
    rw [map_smul, complHom_star, hβv, star_smul_quat, star_mul, star_star, ← algebraMap_smul (v.adicCompletion F),
      hνF, smul_smul, smul_mul_assoc]
    rw [← algebraMap_smul (v.adicCompletion F) ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)]
    congr 1
    rw [← ht, ← hu, map_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v hν0)), one_mul]
    exact (eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm
  have hzO : algebraMap (𝓞 F) F ν • star β ∈ O := by
    refine mem_order_of_forall_complHom_mem hO.1 fun v => ?_
    obtain ⟨y, hy, α, hIα, hz⟩ := hloc v
    rw [hz]
    have : y * α ∈ idealSet (localIdeal (v := v) J) := by rw [hIα]; exact ⟨y, hy, rfl⟩
    exact idealSet_subset _ this
  refine ⟨hzO, ?_⟩
  have hνJ : algebraMap (𝓞 F) O ν ∈ J := algebraMap_mem_of_mem_leftNrdIdeal hO.1 J (by rw [hν]; exact Ideal.mem_span_singleton_self ν)
  refine mem_of_forall_toLocal_mem hO.1 hν0 hνJ fun v => ?_
  obtain ⟨y, hy, α, hIα, hz⟩ := hloc v
  have : complHom v a b (algebraMap (𝓞 F) F ν • star β) ∈ idealSet (localIdeal (v := v) J) := by
    rw [hIα, hz]; exact ⟨y, hy, rfl⟩
  obtain ⟨_, h⟩ := this
  exact h

/-- **$(\mathcal O : J) = \nu^{-1}\bar J$** ($\mathcal O$ maximal, $\operatorname{nrd}(J) = (\nu) \ne 0$; Voight 2021, Prop. 16.6.15). -/
@[kb "voight2021" "Prop. 16.6.15; Lemma 16.3.7"]
theorem mem_colon_iff (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    {ν : 𝓞 F} (hν0 : ν ≠ 0) (hν : leftNrdIdeal J = Ideal.span {ν}) {β : QuatF F a b} :
    β ∈ colon J ↔ ∃ x ∈ idealSet J, β = (algebraMap (𝓞 F) F ν)⁻¹ • star x := by
  have hνF : algebraMap (𝓞 F) F ν ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hν0
  constructor
  · intro hβ
    refine ⟨_, smul_star_mem_of_mem_colon ha hb hO hν0 hν hβ, ?_⟩
    rw [star_smul_quat, star_star, smul_smul, inv_mul_cancel₀ hνF, one_smul]
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [mul_smul_comm]
    exact mul_star_mem ha hb hO hν0 hν hx hy

end Inverse

/-! ### The Epstein sum over $J$ -/

section EpsteinJ

open scoped ENNReal

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]
  {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-- $|N_{F/\mathbb Q}(w)| = 1$ for a unit $w$ of $\mathcal O_F$. -/
theorem abs_norm_unit (w : (𝓞 F)ˣ) : |(Algebra.norm ℚ (algebraMap (𝓞 F) F (w : 𝓞 F)) : ℝ)| = 1 := by
  have h := w.isUnit.map (Algebra.norm ℤ : 𝓞 F →* ℤ)
  rw [Int.isUnit_iff_abs_eq] at h
  have h2 : ((Algebra.norm ℤ (w : 𝓞 F) : ℤ) : ℚ) = Algebra.norm ℚ ((w : 𝓞 F) : F) := Algebra.coe_norm_int _
  have h3 : |((Algebra.norm ℤ (w : 𝓞 F) : ℤ) : ℝ)| = 1 := by exact_mod_cast h
  rw [show (Algebra.norm ℚ (algebraMap (𝓞 F) F (w : 𝓞 F)) : ℝ) = ((Algebra.norm ℚ ((w : 𝓞 F) : F) : ℚ) : ℝ) from rfl,
    ← h2]
  exact_mod_cast h3

/-- The norm $|N(\operatorname{nrd}x)|$ is invariant under the central units. -/
theorem abs_norm_nrd_central (u : centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b))
    (x : QuatF F a b) :
    |(Algebra.norm ℚ (nrd (((u : (QuatF F a b)ˣ) : QuatF F a b) * x)) : ℝ)| = |(Algebra.norm ℚ (nrd x) : ℝ)| := by
  obtain ⟨w, hw⟩ := u.2
  have hu : ((u : (QuatF F a b)ˣ) : QuatF F a b) = ((algebraMap (𝓞 F) F (w : 𝓞 F) : F) : QuatF F a b) := by
    rw [← hw]; rfl
  rw [hu, nrd_mul, show nrd ((algebraMap (𝓞 F) F (w : 𝓞 F) : F) : QuatF F a b) = (algebraMap (𝓞 F) F (w : 𝓞 F)) ^ 2 by
    simp [nrd], map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow, abs_norm_unit, one_pow, one_mul]

/-- **The Epstein sum of the ideal $J$ itself**: $E'_J(s) = \sum_{x\in\mathcal O_F^\times\backslash(J\cap D^\times)}|N(\operatorname{nrd}x)|^{-s}$. -/
def epsteinSumIdeal (J : Ideal O) (s : ℝ) : ℝ≥0∞ :=
  ∑' q : MulAction.orbitRel.Quotient (centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b))
      (IdealUnits J),
    ENNReal.ofReal (|(Algebra.norm ℚ (nrd ((q.out.1 : (QuatF F a b)ˣ) : QuatF F a b)) : ℝ)| ^ (-s))

theorem exists_coe_of_mem_centralUnits {u : (QuatF F a b)ˣ}
    (hu : u ∈ centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b)) :
    ∃ c : F, c ≠ 0 ∧ (u : QuatF F a b) = (c : QuatF F a b) := by
  obtain ⟨w, rfl⟩ := hu
  exact ⟨algebraMap (𝓞 F) F (w : 𝓞 F), (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 w.ne_zero, rfl⟩

theorem isUnit_smul_star {c : F} (hc : c ≠ 0) (x : (QuatF F a b)ˣ) : IsUnit (c • star (x : QuatF F a b)) := by
  rw [isUnit_iff_nrd_ne_zero, nrd_smul, nrd_star]
  exact mul_ne_zero (pow_ne_zero 2 hc) (nrd_units_ne_zero x)

variable (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} {ν : 𝓞 F} (hν0 : ν ≠ 0)
  (hν : leftNrdIdeal J = Ideal.span {ν})

include ha hb hO hν0 hν in
/-- **$\beta \mapsto \nu\bar\beta$** identifies the units of $(\mathcal O : J)$ with the units of $J$. -/
def colonEquiv : ColonUnits J ≃ IdealUnits J where
  toFun β := ⟨(isUnit_smul_star ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hν0) β.1).unit,
    smul_star_mem_of_mem_colon ha hb hO hν0 hν β.2⟩
  invFun x := ⟨(isUnit_smul_star (inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hν0))
      x.1).unit, (mem_colon_iff ha hb hO hν0 hν).2 ⟨_, x.2, rfl⟩⟩
  left_inv β := by
    have hνF : algebraMap (𝓞 F) F ν ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hν0
    refine Subtype.ext (Units.ext ?_)
    simp only [IsUnit.unit_spec]
    rw [star_smul_quat, star_star, smul_smul, inv_mul_cancel₀ hνF, one_smul]
  right_inv x := by
    have hνF : algebraMap (𝓞 F) F ν ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hν0
    refine Subtype.ext (Units.ext ?_)
    simp only [IsUnit.unit_spec]
    rw [star_smul_quat, star_star, smul_smul, mul_inv_cancel₀ hνF, one_smul]

theorem colonEquiv_val (β : ColonUnits J) :
    (((colonEquiv ha hb hO hν0 hν β).1 : (QuatF F a b)ˣ) : QuatF F a b) =
      algebraMap (𝓞 F) F ν • star ((β.1 : (QuatF F a b)ˣ) : QuatF F a b) := rfl

theorem colonEquiv_symm_val (x : IdealUnits J) :
    ((((colonEquiv ha hb hO hν0 hν).symm x).1 : (QuatF F a b)ˣ) : QuatF F a b) =
      (algebraMap (𝓞 F) F ν)⁻¹ • star ((x.1 : (QuatF F a b)ˣ) : QuatF F a b) := rfl

theorem star_coe_mul_comm (c : F) (y : QuatF F a b) : star ((c : QuatF F a b) * y) = (c : QuatF F a b) * star y := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp <;> ring

/-- **The orbits correspond**: $\Gamma$-orbits of $\mathcal O_F^\times$ on $Y_J$ and on the units of $J$. -/
def colonOrbitEquiv :
    MulAction.orbitRel.Quotient (centralUnitsIn (R := 𝓞 F) J) (ColonUnits J) ≃
      MulAction.orbitRel.Quotient (centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b))
        (IdealUnits J) :=
  Quotient.congr (colonEquiv ha hb hO hν0 hν) fun β β' => by
    have hνF : algebraMap (𝓞 F) F ν ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hν0
    constructor
    · rintro ⟨g, hg⟩
      have hgc : ((g : rStab J) : (QuatF F a b)ˣ) ∈ centralUnits (𝓞 F) (algebraMap (𝓞 F) F a)
          (algebraMap (𝓞 F) F b) := Subgroup.mem_subgroupOf.1 g.2
      obtain ⟨c, -, hc⟩ := exists_coe_of_mem_centralUnits hgc
      have hg' : ((β.1 : (QuatF F a b)ˣ) : QuatF F a b) = (c : QuatF F a b) * ((β'.1 : (QuatF F a b)ˣ) : QuatF F a b) := by
        have hg2 : g • β' = β := hg
        rw [← hg2]
        show (((g : rStab J) : (QuatF F a b)ˣ) : QuatF F a b) * ((β'.1 : (QuatF F a b)ˣ) : QuatF F a b) = _
        rw [hc]
      refine ⟨⟨_, hgc⟩, Subtype.ext (Units.ext ?_)⟩
      rw [smul_idealUnits_val, Units.val_mul, colonEquiv_val, colonEquiv_val, hg', hc, star_coe_mul_comm,
        mul_smul_comm]
    · rintro ⟨u, hu⟩
      have hu2 : u • colonEquiv ha hb hO hν0 hν β' = colonEquiv ha hb hO hν0 hν β := hu
      obtain ⟨c, -, hc⟩ := exists_coe_of_mem_centralUnits u.2
      have hmem : (⟨u, centralUnits_le_rStab J u.2⟩ : rStab J) ∈ centralUnitsIn (R := 𝓞 F) J := by
        unfold centralUnitsIn; exact Subgroup.mem_subgroupOf.2 u.2
      refine ⟨⟨⟨u, centralUnits_le_rStab J u.2⟩, hmem⟩, Subtype.ext (Units.ext ?_)⟩
      have h1 := congrArg (fun z : IdealUnits J =>
        ((((colonEquiv ha hb hO hν0 hν).symm z).1 : (QuatF F a b)ˣ) : QuatF F a b)) hu2
      simp only [Equiv.symm_apply_apply] at h1
      rw [← h1]
      show ((u : (QuatF F a b)ˣ) : QuatF F a b) * ((β'.1 : (QuatF F a b)ˣ) : QuatF F a b) = _
      rw [colonEquiv_symm_val, smul_idealUnits_val, Units.val_mul, colonEquiv_val, hc, star_coe_mul_comm,
        star_smul_quat, star_star, mul_smul_comm, smul_smul, inv_mul_cancel₀ hνF, one_smul]

theorem colonOrbitEquiv_mk (β : ColonUnits J) :
    colonOrbitEquiv ha hb hO hν0 hν (Quotient.mk _ β) = Quotient.mk _ (colonEquiv ha hb hO hν0 hν β) := rfl

/-- `epsteinSum` of `QuatClassSum`, restated with the `Algebra` instance of this file (definitionally equal). -/
def epsteinSumColon (J : Ideal O) (s : ℝ) : ℝ≥0∞ :=
  ∑' q : MulAction.orbitRel.Quotient (centralUnitsIn (R := 𝓞 F) J) (ColonUnits J),
    ENNReal.ofReal (|(Algebra.norm ℚ (nrd (q.out.1 : QuatF F a b)) : ℝ)| ^ (-s))

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem epsteinSum_eq_colon (J : Ideal O) (s : ℝ) : epsteinSum J s = epsteinSumColon J s := rfl

include ha hb hO hν0 hν in
/-- **$E_J(s) = N(\nu)^{2s}E'_J(s)$**: the Epstein sum over $(\mathcal O : J) = \nu^{-1}\bar J$ is the Epstein sum over $J$, rescaled. -/
theorem epsteinSum_eq (s : ℝ) :
    epsteinSum J s = ENNReal.ofReal ((|(Algebra.norm ℚ (algebraMap (𝓞 F) F ν) : ℝ)| ^ 2) ^ s) *
      epsteinSumIdeal J s := by
  have hνF : algebraMap (𝓞 F) F ν ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hν0
  set e := colonOrbitEquiv ha hb hO hν0 hν
  set Nν : ℝ := |(Algebra.norm ℚ (algebraMap (𝓞 F) F ν) : ℝ)|
  have hNν : 0 < Nν := abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hνF)
  rw [epsteinSum_eq_colon]
  unfold epsteinSumColon epsteinSumIdeal
  rw [← e.tsum_eq, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun q => ?_
  set β := q.out
  have hq : e q = Quotient.mk _ (colonEquiv ha hb hO hν0 hν β) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨u, hu⟩ : ∃ u : centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b),
      u • colonEquiv ha hb hO hν0 hν β = (e q).out := by
    have : (Quotient.mk _ (e q).out : MulAction.orbitRel.Quotient
        (centralUnits (𝓞 F) (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b)) (IdealUnits J)) =
        Quotient.mk _ (colonEquiv ha hb hO hν0 hν β) := by rw [Quotient.out_eq, hq]
    exact Quotient.exact this
  have hnorm : |(Algebra.norm ℚ (nrd (((e q).out.1 : (QuatF F a b)ˣ) : QuatF F a b)) : ℝ)| =
      Nν ^ 2 * |(Algebra.norm ℚ (nrd ((β.1 : (QuatF F a b)ˣ) : QuatF F a b)) : ℝ)| := by
    rw [← hu, smul_idealUnits_val, Units.val_mul, abs_norm_nrd_central, colonEquiv_val, nrd_smul, nrd_star, map_mul,
      map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow]
  have hβ0 : 0 < |(Algebra.norm ℚ (nrd ((β.1 : (QuatF F a b)ˣ) : QuatF F a b)) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 (nrd_units_ne_zero β.1))
  rw [hnorm, ← ENNReal.ofReal_mul (Real.rpow_nonneg (sq_nonneg _) _), Real.mul_rpow (sq_nonneg _) hβ0.le,
    ← mul_assoc, Real.rpow_neg (sq_nonneg _), mul_inv_cancel₀ (Real.rpow_pos_of_pos (pow_pos hNν 2) _).ne', one_mul]

end EpsteinJ

end QuadFormsKB.QuatOrder
