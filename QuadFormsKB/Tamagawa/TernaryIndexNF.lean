/-
# $[SO(\hat L) : K'] = 2^{\#\mathrm{Ram}_f}$ for the trace-zero lattice, every class number

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$, $\mathcal O$ a maximal order, $L = \mathcal O^0$ (`pureLat`) in the
coordinates $i,j,k$, $Q = \langle -a,-b,ab\rangle$ (`QP`). Inside $G = SO(Q)(\mathbb A_f)$ (`soAf`): $\Gamma = SO(Q)(F)$ (`GamNF`),
$K_0 = SO(\hat L)$ (`K0NF`) and $K' = \prod_vc_v(\mathcal O_v^\times)$ (`KpNF`, from `KANF`).

**Proves** the parity map $K_0 \to \prod_{v\in\mathrm{Ram}_f}\mathbb Z/2$ (`chiNF`), its kernel $K'$ (`ker_chiNF`), surjectivity, and
**`relIndex_KpNF_K0NF`**: $[K_0 : K'] = 2^{\#\mathrm{Ram}_f(D)}$. Port of `TernaryIndex` (local, no frame, no PID).

Source: Voight 2021, §§23.4, 26.5 (normalizers of local maximal orders); Weil 1982, §3.7(a).
-/
import QuadFormsKB.Tamagawa.TernaryLocalNF

open NumberField IsDedekindDomain Matrix Quaternion WithZero MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization
  QuadFormsKB.QuatZeta

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-! ### The global groups -/

/-- **$K' = \prod_v c_v(\mathcal O_v^\times)$** inside $O(Q)(\mathbb A_f)$. -/
def KANF (O : Subalgebra (𝓞 F) (QuatF F a b)) : Subgroup (OAf (QP a b)) where
  carrier := {g | ∀ v, g v ∈ KvNF v O}
  mul_mem' {_ _} hg hh v := (KvNF v O).mul_mem (hg v) (hh v)
  one_mem' v := (KvNF v O).one_mem
  inv_mem' {_} hg v := (KvNF v O).inv_mem (hg v)

theorem mem_KANF {g : OAf (QP a b)} : g ∈ KANF O ↔ ∀ v, g v ∈ KvNF v O := Iff.rfl

theorem KANF_le_soAf : KANF O ≤ soAf (QP a b) := fun _ hg v => KvNF_le_soSub v (hg v)

theorem KANF_le_locStab (hO : IsOrder (𝓞 F) F O) : KANF O ≤ locStab (QP a b) (pureLat hO) :=
  fun _ hg v => KvNF_le_stab v hO (hg v)

/-- $\Gamma = SO(Q)(F)$ inside $G = SO(Q)(\mathbb A_f)$. -/
abbrev GamNF (a b : 𝓞 F) : Subgroup (soAf (QP a b)) := (ratPoints (QP a b)).subgroupOf (soAf (QP a b))

/-- $K' = \prod_vc_v(\mathcal O_v^\times)$ inside $G$. -/
abbrev KpNF (O : Subalgebra (𝓞 F) (QuatF F a b)) : Subgroup (soAf (QP a b)) := (KANF O).subgroupOf (soAf (QP a b))

/-- $K_0 = SO(\hat L)$ inside $G$. -/
abbrev K0NF (hO : IsOrder (𝓞 F) F O) : Subgroup (soAf (QP a b)) :=
  (locStab (QP a b) (pureLat hO)).subgroupOf (soAf (QP a b))

theorem KpNF_le_K0NF (hO : IsOrder (𝓞 F) F O) : KpNF O ≤ K0NF hO := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (KANF_le_locStab hO (Subgroup.mem_subgroupOf.1 hx))

/-! ### The parity of the reduced norm -/

section Parity

variable (v : HeightOneSpectrum (𝓞 F))

theorem parD_apply_nf (x : (QuatV v a b)ˣ) :
    parD v x = Multiplicative.ofAdd ((WithZero.log (Valued.v (nrd (x : QuatV v a b))) : ℤ) : ZMod 2) := rfl

theorem parD_qScalar_nf {r : v.adicCompletion F} (hr : r ≠ 0) : parD (a := a) (b := b) v (qScalar r hr) = 1 := by
  rw [parD_apply_nf, coe_qScalar]
  have : nrd (algebraMap (v.adicCompletion F) (QuatV v a b) r) = r ^ 2 := by
    simp [nrd, QuaternionAlgebra.algebraMap_eq]
  rw [this, map_pow]
  obtain ⟨k, hk⟩ := exists_valued_eq_exp v hr
  rw [hk, ← WithZero.exp_nsmul, WithZero.log_exp]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, Int.cast_mul, Int.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, ofAdd_zero]

theorem parD_eq_of_cvvNF_eq (ha : a ≠ 0) {x y : (QuatV v a b)ˣ} (h : cvvNF v x = cvvNF v y) : parD v x = parD v y := by
  have ha' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (ι_ne_zero v ha)
  obtain ⟨r, hr⟩ := (cvHom_eq_iff (two_ne_zero_Fv v) ha' 1 x y).1 (congrArg Subtype.val h)
  have hr0 : r ≠ 0 := by rintro rfl; exact x.ne_zero (by rw [hr, map_zero, zero_mul])
  have hxy : x = qScalar r hr0 * y := Units.ext (by rw [Units.val_mul, coe_qScalar]; exact hr)
  rw [hxy, map_mul, parD_qScalar_nf, one_mul]

theorem parD_eq_one_of_mem_unitsOv_nf (hO : IsOrder (𝓞 F) F O) {u : (QuatV v a b)ˣ} (hu : u ∈ unitsOv (O := O) v) :
    parD v u = 1 := by
  have hOv := Gen.isOrder_localOrder_gen v hO
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
  rw [parD_apply_nf, h3]
  simp

theorem hdiv_of_mem_ramFin_nf (ha : a ≠ 0) (hb : b ≠ 0) (hv : v ∈ ramFin ha hb) :
    ∀ x : QuatV v a b, nrd x = 0 → x = 0 := by
  have h := (Gen.mem_ramFin ha hb).1 hv
  intro x hx
  by_contra h0
  exact (isUnit_iff_nrd_ne_zero x).1 (h x h0) hx

theorem split_of_not_mem_ramFin_nf (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) (hv : v ∉ ramFin ha hb) :
    ∃ φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F),
      (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
        (v.adicCompletionIntegers F)) = matOrder (v.adicCompletionIntegers F) (v.adicCompletion F) := by
  rcases localOrder_ramified_or_split_nf (v := v) ha hb hO with ⟨hd, -⟩ | h
  · exfalso; apply hv
    rw [Gen.mem_ramFin]
    intro x hx
    exact (isUnit_iff_nrd_ne_zero x).2 fun h0 => hx (hd x h0)
  · exact h

end Parity

/-! ### The index $[K_0 : K']$ -/

section Index

variable (hO : IsMaximalOrder (𝓞 F) F O)

/-- **The parity map** $K_0 \to \prod_{v \in \mathrm{Ram}_f}\mathbb Z/2$, $k \mapsto (\operatorname{ord}_v\operatorname{nrd}x_v \bmod 2)_v$ for
$k_v = c_v(x_v)$. -/
def chiNF (ha : a ≠ 0) (hb : b ≠ 0) : K0NF hO.1 →* ((ramFin ha hb) → Multiplicative (ZMod 2)) where
  toFun k := fun w => parD w.1 (Classical.choose (exists_cvvNF_eq w.1 ha hb ((((k : K0NF hO.1) : soAf (QP a b)) :
    OAf (QP a b)) w.1) ((((k : K0NF hO.1) : soAf (QP a b))).2 w.1)))
  map_one' := by
    funext w
    have h := Classical.choose_spec (exists_cvvNF_eq w.1 ha hb ((((1 : K0NF hO.1) : soAf (QP a b)) : OAf (QP a b)) w.1)
      ((((1 : K0NF hO.1) : soAf (QP a b))).2 w.1))
    simp only [OneMemClass.coe_one, RestrictedProduct.one_apply] at h
    rw [Pi.one_apply, parD_eq_of_cvvNF_eq w.1 ha (h.trans (map_one _).symm), map_one]
  map_mul' k l := by
    funext w
    have hk := Classical.choose_spec (exists_cvvNF_eq w.1 ha hb ((((k : K0NF hO.1) : soAf (QP a b)) : OAf (QP a b)) w.1)
      ((((k : K0NF hO.1) : soAf (QP a b))).2 w.1))
    have hl := Classical.choose_spec (exists_cvvNF_eq w.1 ha hb ((((l : K0NF hO.1) : soAf (QP a b)) : OAf (QP a b)) w.1)
      ((((l : K0NF hO.1) : soAf (QP a b))).2 w.1))
    have hkl := Classical.choose_spec (exists_cvvNF_eq w.1 ha hb
      ((((k * l : K0NF hO.1) : soAf (QP a b)) : OAf (QP a b)) w.1) ((((k * l : K0NF hO.1) : soAf (QP a b))).2 w.1))
    rw [Pi.mul_apply, ← map_mul]
    apply parD_eq_of_cvvNF_eq w.1 ha
    rw [hkl, map_mul, hk, hl]
    simp only [Subgroup.coe_mul, RestrictedProduct.mul_apply]

theorem chiNF_apply (ha : a ≠ 0) (hb : b ≠ 0) (k : K0NF hO.1) (w : ramFin ha hb) {y : (QuatV w.1 a b)ˣ}
    (hy : cvvNF w.1 y = (((k : K0NF hO.1) : soAf (QP a b)) : OAf (QP a b)) w.1) : chiNF hO ha hb k w = parD w.1 y := by
  have h := Classical.choose_spec (exists_cvvNF_eq w.1 ha hb ((((k : K0NF hO.1) : soAf (QP a b)) : OAf (QP a b)) w.1)
      ((((k : K0NF hO.1) : soAf (QP a b))).2 w.1))
  exact parD_eq_of_cvvNF_eq w.1 ha (h.trans hy.symm)

/-- **The kernel of the parity map is $K'$.** -/
theorem ker_chiNF (ha : a ≠ 0) (hb : b ≠ 0) : (chiNF hO ha hb).ker = (KpNF O).subgroupOf (K0NF hO.1) := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hk0 : (((k : K0NF hO.1) : soAf (QP a b)) : OAf (QP a b)) ∈ locStab (QP a b) (pureLat hO.1) :=
    Subgroup.mem_subgroupOf.1 k.2
  constructor
  · intro h v
    obtain ⟨y, hy⟩ := exists_cvvNF_eq v ha hb ((((k : K0NF hO.1) : soAf (QP a b)) : OAf (QP a b)) v)
      ((((k : K0NF hO.1) : soAf (QP a b))).2 v)
    by_cases hv : v ∈ ramFin ha hb
    · have h1 := congrFun h ⟨v, hv⟩
      rw [chiNF_apply hO ha hb k ⟨v, hv⟩ hy, Pi.one_apply, parD_apply_nf] at h1
      have hdiv := hdiv_of_mem_ramFin_nf v ha hb hv
      have heq := localOrder_eq_valOrder_nf ha hb hO hdiv
      obtain ⟨m, hm⟩ := exists_valued_eq_exp v (nrd_units_ne_zero y)
      rw [hm, WithZero.log_exp, ofAdd_eq_one_iff_even] at h1
      rw [← hy]
      exact (cvvNF_mem_KvNF_iff_even v hdiv heq ha y m hm).2 h1
    · obtain ⟨φ, hφ⟩ := split_of_not_mem_ramFin_nf v ha hb hO hv
      have hst := hk0 v
      rw [← hy] at hst ⊢
      exact mem_KvNF_of_stab_split v φ hφ hO.1 ha y hst
  · intro h
    funext w
    obtain ⟨u, hu, huk⟩ := h w.1
    rw [chiNF_apply hO ha hb k w huk, Pi.one_apply]
    exact parD_eq_one_of_mem_unitsOv_nf w.1 hO.1 hu

/-- **The parity map is onto.** -/
theorem chiNF_surjective (ha : a ≠ 0) (hb : b ≠ 0) : Function.Surjective (chiNF hO ha hb) := by
  classical
  have ht : ∀ w : ramFin ha hb, ∃ k : K0NF hO.1, chiNF hO ha hb k = Pi.mulSingle w (Multiplicative.ofAdd 1) := by
    intro w
    obtain ⟨Pw, hPw⟩ := exists_nrd_odd_nf w.1 ha hb
    have hdiv := hdiv_of_mem_ramFin_nf w.1 ha hb w.2
    have heq := localOrder_eq_valOrder_nf ha hb hO hdiv
    obtain ⟨t, htdef⟩ : ∃ t : OAf (QP a b), t = RestrictedProduct.mulSingle _ w.1 (cvvNF w.1 Pw) := ⟨_, rfl⟩
    have hts : t ∈ soAf (QP a b) := by
      intro v
      by_cases hv : v = w.1
      · subst hv; rw [htdef, RestrictedProduct.mulSingle_eq_same]; exact cvvNF_mem_soSub _ Pw
      · rw [htdef, RestrictedProduct.mulSingle_eq_of_ne _ _ hv]; exact (soSub (QP a b) _).one_mem
    have htK : t ∈ locStab (QP a b) (pureLat hO.1) := by
      intro v
      by_cases hv : v = w.1
      · subst hv; rw [htdef, RestrictedProduct.mulSingle_eq_same]
        exact cvvNF_stab_ramified _ hdiv heq hO.1 Pw
      · rw [htdef, RestrictedProduct.mulSingle_eq_of_ne _ _ hv]; exact locAct_one _
    refine ⟨⟨⟨t, hts⟩, Subgroup.mem_subgroupOf.2 htK⟩, ?_⟩
    funext w'
    by_cases hw : w' = w
    · subst hw
      rw [chiNF_apply hO ha hb _ w' (y := Pw) (by
          show _ = t w'.1; rw [htdef]; exact (RestrictedProduct.mulSingle_eq_same (stdStab (QP a b)) w'.1 _).symm),
        Pi.mulSingle_eq_same, parD_apply_nf, hPw, WithZero.log_exp]
      rfl
    · have hw1 : w'.1 ≠ w.1 := fun h => hw (Subtype.ext h)
      rw [chiNF_apply hO ha hb _ w' (y := 1) (by
          show _ = t w'.1; rw [htdef, map_one]; exact (RestrictedProduct.mulSingle_eq_of_ne (stdStab (QP a b)) _ hw1).symm),
        Pi.mulSingle_eq_of_ne hw, map_one]
  intro f
  have hf : f = ∏ w, Pi.mulSingle w (f w) := (Finset.univ_prod_mulSingle f).symm
  have hmem : ∀ w, Pi.mulSingle w (f w) ∈ (chiNF hO ha hb).range := by
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
  have : f ∈ (chiNF hO ha hb).range := by
    rw [hf]; exact Subgroup.prod_mem _ fun w _ => hmem w
  exact this

/-- **$[K_0 : K'] = 2^{\#\mathrm{Ram}_f(D)}$** for the trace-zero lattice of a maximal order, every class number. -/
@[kb "voight2021" "§§23.4, 26.5 (normalizers of local maximal orders)"]
theorem relIndex_KpNF_K0NF (ha : a ≠ 0) (hb : b ≠ 0) : (KpNF O).relIndex (K0NF hO.1) = 2 ^ (ramFin ha hb).card := by
  rw [Subgroup.relIndex, ← ker_chiNF hO ha hb, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (chiNF_surjective hO ha hb), Subgroup.card_top, Nat.card_fun]
  simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

end Index

end QuadFormsKB.QuatOrder
