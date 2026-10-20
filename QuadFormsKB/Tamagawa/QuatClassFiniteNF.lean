/-
# Finiteness of the class set of a maximal order, for every class number

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$ a division algebra ($ab \ne 0$), $\mathcal O \subset D$ a maximal order.

The PID file `QuatClassFinite` picks an $\mathcal O_F$-basis of the ideal $J$ and a generator $\nu$ of $\operatorname{nrd}J$. Here:
* `Gen.mul_star_mem`: for $c \in \operatorname{nrd}(J)^{-1}$ and $x,y \in J$, $c\,y\bar x \in \mathcal O$ (locally $y\bar x = \operatorname{nrd}(\alpha)\,p\bar q$);
  hence $c\bar x \in (\mathcal O:J)$ (`Gen.mem_colon_of_mem_inv`).
* the pigeonhole runs on a $\mathbb Z$-basis of $\mathcal O$ (always free over $\mathbb Z$) and the $\mathbb Z$-submodule $J$ of index $N(\operatorname{nrd}J)^2$
  (`Gen.card_quot_ideal`): `Gen.exists_small_mem`.
* `Gen.finite_classes`: every class contains an integral ideal of bounded reduced norm.

Sources: Voight, *Quaternion Algebras* (2021), Lemma 16.3.7, Thm. 17.8.3 (via O'Meara's pigeonhole, 103:2).
-/
import QuadFormsKB.Tamagawa.IdealIndexNF
import QuadFormsKB.Tamagawa.QuatClassSumNF
import QuadFormsKB.Tamagawa.OrderNormFormNF
import QuadFormsKB.Tamagawa.QuatClassFinite

open NumberField IsDedekindDomain Quaternion IsLocalization
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

namespace Gen

section LocalGlobalElt

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

/-- **Membership in $J$ is local** (no PID). -/
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

/-- **Membership in $\mathcal O$ is local** (no PID). -/
theorem mem_order_of_forall_complHom_mem (hO : IsOrder (𝓞 F) F O) {z : QuatF F a b}
    (hz : ∀ v, complHom v a b z ∈ localOrder (v := v) a b O) : z ∈ O := by
  obtain ⟨n, hn, hnz'⟩ := exists_smul_mem_order_nf hO z
  have hnz : algebraMap (𝓞 F) F n • z ∈ O := by rwa [algebraMap_smul F n z]
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

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

theorem complHom_star_nf (v : HeightOneSpectrum (𝓞 F)) (x : QuatF F a b) :
    complHom v a b (star x) = star (complHom v a b x) := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp only [complHom_re, complHom_imI, complHom_imJ, complHom_imK, QuaternionAlgebra.re_star,
      QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, map_neg,
      zero_mul, add_zero]

theorem complHom_mem_idealSet_localIdeal (v : HeightOneSpectrum (𝓞 F)) {J : Ideal O} {x : QuatF F a b}
    (hx : x ∈ idealSet J) : complHom v a b x ∈ idealSet (localIdeal (v := v) J) := by
  obtain ⟨hxO, hxJ⟩ := hx
  exact ⟨mem_localOrder_of_mem a b hxO, complHom_mem_span_idealImage hxJ⟩

/-- **Local generators** ($J_v = \mathcal O_v\alpha$, $\operatorname{nrd}\alpha \sim \varpi_v^{c_v(\operatorname{nrd}J)}$), no PID. -/
theorem exists_local_generator (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (α : QuatV v a b) (t : v.adicCompletionIntegers F), α ∈ localOrder (v := v) a b O ∧
      idealSet (localIdeal (v := v) J) = rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) α ∧
      algebraMap _ (v.adicCompletion F) t = nrd α ∧ Ideal.span {t} = Ideal.span {π v ^ cI v (leftNrdIdeal J)} := by
  set I := localIdeal (v := v) J
  have hOv := isOrder_localOrder_gen v hO.1
  have hIν : leftNrdIdeal I = Ideal.span {π v ^ cI v (leftNrdIdeal J)} := by
    rw [leftNrdIdeal_localIdeal hO.1, map_ι_eq_span v hJ]
  have hI0 : leftNrdIdeal I ≠ ⊥ := by
    rw [hIν, Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero _ (irreducible_π v).ne_zero
  obtain ⟨α, -, hIα⟩ := exists_localIdeal_eq_rTrans_nf ha hb hO I hI0
  have hαO : α ∈ localOrder (v := v) a b O := by
    have : α ∈ idealSet I := by rw [hIα]; exact ⟨1, Subalgebra.one_mem _, one_mul α⟩
    exact idealSet_subset I this
  obtain ⟨t, ht⟩ := (isInteger_trd_nrd hOv hαO).2
  have hIt : leftNrdIdeal I = Ideal.span {t} :=
    leftNrdIdeal_eq_of_idealSet_eq_rTrans (IsFractionRing.injective _ _)
      (fun y hy => (isInteger_trd_nrd hOv hy).2) hIα ht
  exact ⟨α, t, hαO, hIα, ht, hIt.symm.trans hIν⟩

/-- A multiple of $\operatorname{nrd}(J)^{-1}$ clears $\varpi_v^{c_v}$ locally. -/
theorem exists_integral_mul {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) {c : F}
    (hc : ∀ m ∈ 𝔫, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = c * algebraMap (𝓞 F) F m) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ s : v.adicCompletionIntegers F, algebraMap _ (v.adicCompletion F) s =
      algebraMap F (v.adicCompletion F) c * algebraMap _ (v.adicCompletion F) (π v ^ cI v 𝔫) := by
  obtain ⟨m, hm𝔫, hm⟩ := exists_mem_not_mem_pow_succ v h𝔫
  obtain ⟨r, hr⟩ := hc m hm𝔫
  have h1 : ι v m ∈ Ideal.span {π v ^ cI v 𝔫} := (ι_mem_span_π_pow v _ _).2 (le_pow_cI v h𝔫 hm𝔫)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 h1
  have hwu : IsUnit w := by
    by_contra hnu
    have : w ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := hnu
    rw [(irreducible_π v).maximalIdeal_eq, Ideal.mem_span_singleton] at this
    obtain ⟨z, hz⟩ := this
    apply hm
    rw [← ι_mem_span_π_pow, ← hw, hz, pow_succ]
    exact Ideal.mem_span_singleton.2 ⟨z, by ring⟩
  obtain ⟨u, rfl⟩ := hwu
  refine ⟨ι v r * (u⁻¹ : (v.adicCompletionIntegers F)ˣ), ?_⟩
  have hrι : algebraMap _ (v.adicCompletion F) (ι v r) = algebraMap F (v.adicCompletion F) c *
      algebraMap _ (v.adicCompletion F) (ι v m) := by
    have := congrArg (algebraMap F (v.adicCompletion F)) hr
    rw [map_mul] at this
    exact this
  rw [map_mul, hrι, ← hw, map_mul]
  have hu : algebraMap _ (v.adicCompletion F) ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) *
      algebraMap _ (v.adicCompletion F) (u : v.adicCompletionIntegers F) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc algebraMap F (v.adicCompletion F) c * (algebraMap _ (v.adicCompletion F) (u : v.adicCompletionIntegers F) *
        algebraMap _ (v.adicCompletion F) (π v ^ cI v 𝔫)) *
        algebraMap _ (v.adicCompletion F) ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
      = algebraMap F (v.adicCompletion F) c * algebraMap _ (v.adicCompletion F) (π v ^ cI v 𝔫) *
        (algebraMap _ (v.adicCompletion F) ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) *
          algebraMap _ (v.adicCompletion F) (u : v.adicCompletionIntegers F)) := by ring
    _ = _ := by rw [hu, mul_one]

/-- **$J\bar J \subseteq \operatorname{nrd}(J)\,\mathcal O$** (any class number): $c\,y\bar x \in \mathcal O$ for $x, y \in J$ and $c \in \operatorname{nrd}(J)^{-1}$
(i.e. $c\,m \in \mathcal O_F$ for all $m \in \operatorname{nrd}J$).

Source: Voight 2021, Lemma 16.3.7 (locally $y\bar x = \operatorname{nrd}(\alpha)\,p\bar q$). -/
theorem mul_star_mem (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) {c : F}
    (hc : ∀ m ∈ leftNrdIdeal J, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = c * algebraMap (𝓞 F) F m)
    {x y : QuatF F a b} (hx : x ∈ idealSet J) (hy : y ∈ idealSet J) : c • (y * star x) ∈ O := by
  refine mem_order_of_forall_complHom_mem hO.1 fun v => ?_
  obtain ⟨α, t, hαO, hIα, ht, hspan⟩ := exists_local_generator ha hb hO hJ v
  obtain ⟨s, hs⟩ := exists_integral_mul hJ hc v
  have hx' := complHom_mem_idealSet_localIdeal v hx
  have hy' := complHom_mem_idealSet_localIdeal v hy
  rw [hIα] at hx' hy'
  obtain ⟨q, hq, hqx⟩ := hx'
  obtain ⟨p, hp, hpy⟩ := hy'
  have hOv := isOrder_localOrder_gen v hO.1
  have htπ : t ∈ Ideal.span {π v ^ cI v (leftNrdIdeal J)} := hspan ▸ Ideal.mem_span_singleton_self t
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 htπ
  rw [map_smul, map_mul, complHom_star_nf, ← hqx, ← hpy]
  simp only
  rw [star_mul, mul_assoc, ← mul_assoc α, mul_star_eq_nrd, ← ht]
  have e : c • (p * (((algebraMap _ (v.adicCompletion F) t : v.adicCompletion F) : QuatV v a b) * star q)) =
      (s * w) • (p * star q) := by
    rw [QuaternionAlgebra.coe_mul_eq_smul, mul_smul_comm, ← algebraMap_smul (v.adicCompletion F) c, smul_smul,
      ← algebraMap_smul (v.adicCompletion F) (s * w)]
    congr 1
    rw [map_mul, hs, ← hw, map_mul]
    ring
  rw [e]
  exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hp (star_mem_of_isOrder hOv hq)) _

end Inverse

/-! ### The ℤ-pigeonhole -/

section Pigeon

variable {M : Type*} [AddCommGroup M] {m : ℕ}

/-- **Pigeonhole (O'Meara 103:2, $\mathbb Z$-form):** if $N \le M$ has finite index $< T^m$ in a free $\mathbb Z$-module with basis
$b$ of rank $m$, then $N$ contains $x \ne 0$ with all coordinates $|b_k^*(x)| < T$. -/
theorem exists_small_of_index (b : Module.Basis (Fin m) ℤ M) (N : Submodule ℤ M) [Finite (M ⧸ N)] (T : ℕ)
    (hT : Nat.card (M ⧸ N) < T ^ m) : ∃ x ∈ N, x ≠ 0 ∧ ∀ k, |b.repr x k| < T := by
  classical
  let _ := Fintype.ofFinite (M ⧸ N)
  let u : (Fin m → Fin T) → M := fun t => ∑ k, ((t k : ℕ) : ℤ) • b k
  have hu : Function.Injective u := by
    intro t t' h
    funext k
    have := congrArg (fun z => b.repr z k) h
    simp only [u, map_sum, map_zsmul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
    exact Fin.ext (by exact_mod_cast this)
  have hlt : Fintype.card (M ⧸ N) < Fintype.card (Fin m → Fin T) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [Fintype.card_fun] using hT
  obtain ⟨t, t', htt, he⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun t => N.mkQ (u t)) hlt
  have hmem : u t - u t' ∈ N := (Submodule.Quotient.eq N).mp he
  refine ⟨u t - u t', hmem, fun h0 => htt (hu (sub_eq_zero.mp h0)), fun k => ?_⟩
  simp only [u, ← Finset.sum_sub_distrib, ← sub_smul, map_sum, map_zsmul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have h1 : ((t k : ℕ) : ℤ) < T := by exact_mod_cast (t k).2
  have h2 : ((t' k : ℕ) : ℤ) < T := by exact_mod_cast (t' k).2
  have h3 : (0 : ℤ) ≤ ((t k : ℕ) : ℤ) := by positivity
  have h4 : (0 : ℤ) ≤ ((t' k : ℕ) : ℤ) := by positivity
  rw [abs_lt]; constructor <;> linarith

end Pigeon

/-! ### The ℤ-rank of an order -/

section ZRank

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

theorem finite_int_order (hO : IsOrder (𝓞 F) F O) : Module.Finite ℤ O := by
  have h1 : Module.Finite (𝓞 F) (Subalgebra.toSubmodule O) := Module.Finite.iff_fg.2 hO.fg
  have h2 : Module.Finite (𝓞 F) O := h1
  exact Module.Finite.trans (𝓞 F) O

theorem noZeroSMulDivisors_int_order : NoZeroSMulDivisors ℤ O := ⟨fun {n x} h => by
  by_contra hh
  push Not at hh
  have h1 : ((n : F)) • (x : QuatF F a b) = 0 := by
    have := congrArg Subtype.val h
    rw [Int.cast_smul_eq_zsmul F n]
    simpa using this
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact hh.1 (by exact_mod_cast h2)
  · exact hh.2 (Subtype.ext h2)⟩

set_option synthInstance.maxHeartbeats 400000 in
theorem free_int_order (hO : IsOrder (𝓞 F) F O) : Module.Free ℤ O := by
  have := finite_int_order hO
  have := noZeroSMulDivisors_int_order (O := O)
  exact Module.free_of_finite_type_torsion_free'

/-- **The $\mathbb Z$-rank of an order is at least $4[F:\mathbb Q]$.** -/
theorem four_mul_finrank_le (hO : IsOrder (𝓞 F) F O) :
    4 * Module.finrank ℚ F ≤ Module.finrank ℤ O := by
  classical
  have := finite_int_order hO
  let B := QuaternionAlgebra.basisOneIJK (algebraMap (𝓞 F) F a) 0 (algebraMap (𝓞 F) F b)
  choose δ hδ0 hδ using fun i => exists_smul_mem_order_nf hO (B i)
  let ψ : (Fin 4 → 𝓞 F) →ₗ[ℤ] O :=
    { toFun := fun y => ⟨∑ i, (y i * δ i) • B i, Subalgebra.sum_mem _ fun i _ => by
        rw [mul_smul]; exact O.smul_mem (hδ i) _⟩
      map_add' := fun y z => Subtype.ext (by
        simp only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]; rfl)
      map_smul' := fun n y => Subtype.ext (by
        simp only [Pi.smul_apply, RingHom.id_apply, Subalgebra.coe_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, smul_assoc]) }
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∑ i, (y i * δ i) • B i = 0 := congrArg Subtype.val hy
    have hli := B.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    funext i
    have := hli (fun i => algebraMap (𝓞 F) F (y i * δ i)) (by simp only [algebraMap_smul]; exact h0) i
    have h2 : y i * δ i = 0 := (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 this
    exact (mul_eq_zero.1 h2).resolve_right (hδ0 i)
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at h
  simpa [NumberField.RingOfIntegers.rank] using h

end ZRank

/-! ### Small elements -/

section Small

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Small elements** (Minkowski-type bound, any class number): there is $C$ (depending on $\mathcal O$) such that every left ideal $J$ with
$\operatorname{nrd}J \ne 0$ contains $x \ne 0$ with $|N_{F/\mathbb Q}(\operatorname{nrd}x)| \le C\,N(\operatorname{nrd}J)$.

*Proof:* O'Meara's pigeonhole on a $\mathbb Z$-basis of $\mathcal O$ with the $\mathbb Z$-submodule $J$ of index $N(\operatorname{nrd}J)^2$
(`card_quot_ideal`), as in the PID file (`QuatOrder.exists_small_mem`) but with no $\mathcal O_F$-basis of $\mathcal O$ or $J$. -/
theorem exists_small_mem (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J : Ideal O}, leftNrdIdeal J ≠ ⊥ →
      ∃ x ∈ idealSet J, x ≠ 0 ∧ |(Algebra.norm ℚ (nrd x) : ℝ)| ≤ C * (Ideal.absNorm (leftNrdIdeal J) : ℝ) := by
  classical
  have hfin := finite_int_order hO.1
  have hfree : Module.Free ℤ O := free_int_order hO.1
  set m := Module.finrank ℤ O with hm
  set bZ : Module.Basis (Fin m) ℤ O := Module.finBasis ℤ O
  let B := QuaternionAlgebra.basisOneIJK (algebraMap (𝓞 F) F a) 0 (algebraMap (𝓞 F) F b)
  obtain ⟨C0, hC0, hbound⟩ := exists_abs_norm_nrd_le (a := a) (b := b) (fun i => B i)
  set d := Module.finrank ℚ F
  have hd : 0 < d := Module.finrank_pos
  have hm4 : 4 * d ≤ m := four_mul_finrank_le hO.1
  set W : ℝ := ∑ φ : F →+* ℂ, ∑ i : Fin 4, ∑ k : Fin m, ‖φ (B.repr (bZ k : QuatF F a b) i)‖ with hW
  have hW0 : 0 ≤ W := by positivity
  refine ⟨C0 * W ^ (2 * d) * 4 ^ d, by positivity, fun {J} hJ => ?_⟩
  set N := Ideal.absNorm (leftNrdIdeal J) with hNdef
  have hN : N ≠ 0 := by rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hJ
  have hcard : Nat.card (O ⧸ J) = N ^ 2 := card_quot_ideal ha hb hO hJ
  let JZ : Submodule ℤ O := J.restrictScalars ℤ
  have hcardZ : Nat.card (O ⧸ JZ) = N ^ 2 := by
    rw [← hcard]; exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ J).toEquiv
  haveI : Finite (O ⧸ JZ) := Nat.finite_of_card_ne_zero (by rw [hcardZ]; positivity)
  have hm0 : 0 < m := by omega
  have hex : ∃ T : ℕ, N ^ 2 < T ^ m :=
    ⟨N ^ 2 + 1, lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_self_pow hm0.ne' _)⟩
  set T := Nat.find hex with hTdef
  have hT : N ^ 2 < T ^ m := Nat.find_spec hex
  obtain ⟨x, hxJ, hx0, hxT⟩ := exists_small_of_index bZ JZ T (by rw [hcardZ]; exact hT)
  refine ⟨(x : QuatF F a b), ⟨x.2, hxJ⟩, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  -- coordinates
  have hxsum : (x : QuatF F a b) = ∑ k, (bZ.repr x k) • (bZ k : QuatF F a b) := by
    conv_lhs => rw [← bZ.sum_repr x]
    simp
  have hy : ∀ (φ : F →+* ℂ) (i : Fin 4), ‖φ (B.repr (x : QuatF F a b) i)‖ ≤ T * W := by
    intro φ i
    have h1 : B.repr (x : QuatF F a b) i = ∑ k, (bZ.repr x k) • B.repr (bZ k : QuatF F a b) i := by
      conv_lhs => rw [hxsum]
      simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
    rw [h1, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have hk : ∀ k, ‖φ ((bZ.repr x k) • B.repr (bZ k : QuatF F a b) i)‖ ≤ T * ‖φ (B.repr (bZ k : QuatF F a b) i)‖ := by
      intro k
      rw [map_zsmul, zsmul_eq_mul, norm_mul]
      have : ‖((bZ.repr x k : ℤ) : ℂ)‖ ≤ T := by
        rw [Complex.norm_intCast]
        exact_mod_cast (hxT k).le
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h2 : ∑ k, ‖φ (B.repr (bZ k : QuatF F a b) i)‖ ≤ ∑ i' : Fin 4, ∑ k, ‖φ (B.repr (bZ k : QuatF F a b) i')‖ :=
      Finset.single_le_sum (f := fun i' : Fin 4 => ∑ k, ‖φ (B.repr (bZ k : QuatF F a b) i')‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    refine h2.trans ?_
    exact Finset.single_le_sum (f := fun φ' : F →+* ℂ => ∑ i' : Fin 4, ∑ k, ‖φ' (B.repr (bZ k : QuatF F a b) i')‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ φ)
  have h1 := hbound (fun i => B.repr (x : QuatF F a b) i) (T * W) (by positivity) hy
  have hxB : ∑ i, B.repr (x : QuatF F a b) i • B i = (x : QuatF F a b) := B.sum_repr _
  simp only [hxB] at h1
  refine h1.trans ?_
  have hT0 : 1 ≤ T := by
    by_contra h
    have hT00 : T = 0 := by omega
    rw [hT00, zero_pow hm0.ne'] at hT
    omega
  have hT4 : (T : ℝ) ^ (2 * d) ≤ 4 ^ d * N := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN
    rcases Nat.eq_or_lt_of_le hT0 with h | h
    · rw [← h]; simp only [Nat.cast_one, one_pow]
      nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num) (n := d)]
    · have hmin : (T - 1) ^ m ≤ N ^ 2 := by
        have := Nat.find_min hex (show T - 1 < T by omega)
        omega
      have h4 : (T - 1) ^ (4 * d) ≤ (T - 1) ^ m := Nat.pow_le_pow_right (by omega) hm4
      have h5 : ((T - 1) ^ (2 * d)) ^ 2 ≤ N ^ 2 := by
        rw [← pow_mul, show 2 * d * 2 = 4 * d by ring]; exact h4.trans hmin
      have h6 : (T - 1) ^ (2 * d) ≤ N := (Nat.pow_le_pow_iff_left two_ne_zero).1 h5
      have h2 : T ≤ 2 * (T - 1) := by omega
      have h3 : T ^ (2 * d) ≤ 4 ^ d * N := by
        calc T ^ (2 * d) ≤ (2 * (T - 1)) ^ (2 * d) := Nat.pow_le_pow_left h2 _
          _ = 4 ^ d * (T - 1) ^ (2 * d) := by rw [mul_pow, pow_mul]; norm_num
          _ ≤ 4 ^ d * N := Nat.mul_le_mul_left _ h6
      exact_mod_cast h3
  calc C0 * ((T : ℝ) * W) ^ (2 * d) = C0 * W ^ (2 * d) * (T : ℝ) ^ (2 * d) := by ring
    _ ≤ C0 * W ^ (2 * d) * (4 ^ d * N) := by gcongr
    _ = C0 * W ^ (2 * d) * 4 ^ d * N := by ring

end Small

/-! ### Finiteness of the class set -/

section Finite

open QuadFormsKB.Lattices.ClassFin

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

theorem abs_norm_algebraMap_le {r : 𝓞 F} (hr : r ≠ 0) {𝔫 : Ideal (𝓞 F)} (hr𝔫 : r ∈ 𝔫) :
    (Ideal.absNorm 𝔫 : ℝ) ≤ |(Algebra.norm ℚ (algebraMap (𝓞 F) F r) : ℝ)| := by
  have h1 : Ideal.absNorm 𝔫 ≤ Ideal.absNorm (Ideal.span {r}) := by
    apply Nat.le_of_dvd
    · rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hr
    · exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 hr𝔫))
  rw [Ideal.absNorm_span_singleton] at h1
  have h2 : (Algebra.norm ℚ (algebraMap (𝓞 F) F r) : ℝ) = ((Algebra.norm ℤ r : ℤ) : ℝ) := by
    rw [← Algebra.coe_norm_int]; rfl
  rw [h2]
  have : ((Algebra.norm ℤ r).natAbs : ℝ) = |((Algebra.norm ℤ r : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [← this]; exact_mod_cast h1

/-- **Small elements of the inverse ideal:** there is $C_F$ (depending on $F$ only) such that every nonzero ideal $\mathfrak n$ has
$c \in \mathfrak n^{-1}\setminus0$ with $|N_{F/\mathbb Q}(c)|\,N\mathfrak n \le C_F$ (Minkowski, via `exists_scale_ideal`). -/
theorem exists_small_inv : ∃ CF : ℝ, 0 ≤ CF ∧ ∀ {𝔫 : Ideal (𝓞 F)}, 𝔫 ≠ ⊥ →
    ∃ c : F, c ≠ 0 ∧ (∀ m ∈ 𝔫, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = c * algebraMap (𝓞 F) F m) ∧
      |(Algebra.norm ℚ c : ℝ)| * (Ideal.absNorm 𝔫 : ℝ) ≤ CF := by
  classical
  obtain ⟨C, hC⟩ := exists_scale_ideal (F := F)
  refine ⟨(C : ℝ) ^ Module.finrank ℚ F, by positivity, fun {𝔫} h𝔫 => ?_⟩
  set I : FractionalIdeal (𝓞 F)⁰ F := ((𝔫 : FractionalIdeal (𝓞 F)⁰ F))⁻¹ with hI
  have h𝔫0 : (𝔫 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact h𝔫
  have hI0 : I ≠ 0 := inv_ne_zero h𝔫0
  have hfg : (I : Submodule (𝓞 F) F).FG := by
    have h1 : IsNoetherian (𝓞 F) I := FractionalIdeal.isNoetherian I
    have h2 : Module.Finite (𝓞 F) I := inferInstance
    exact Module.Finite.iff_fg.1 h2
  have hne : (I : Submodule (𝓞 F) F) ≠ ⊥ := by
    intro h; apply hI0; exact FractionalIdeal.coeToSubmodule_injective (by simpa using h)
  obtain ⟨b, hb0, hbA, a', ha', m, hm0, hmC, hba⟩ := hC _ hfg hne
  have ha'0 : a' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hba
    exact (Nat.pos_iff_ne_zero.1 hm0) (by exact_mod_cast hba.symm)
  have hc : ∀ m' ∈ 𝔫, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = a' * algebraMap (𝓞 F) F m' := by
    intro m' hm'
    have hy : algebraMap (𝓞 F) F m' ∈ (𝔫 : FractionalIdeal (𝓞 F)⁰ F) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨m', hm', rfl⟩
    have := (FractionalIdeal.mem_inv_iff h𝔫0).1 ha' _ hy
    exact (FractionalIdeal.mem_one_iff _).1 this
  have hbI : b ∈ I⁻¹ := (FractionalIdeal.mem_inv_iff hI0).2 fun y hy =>
    (FractionalIdeal.mem_one_iff _).2 (by obtain ⟨r, hr⟩ := hbA y hy; exact ⟨r, hr⟩)
  rw [hI, inv_inv] at hbI
  obtain ⟨r, hr𝔫, hrb⟩ := (FractionalIdeal.mem_coeIdeal _).1 hbI
  have hr0 : r ≠ 0 := by
    rintro rfl; apply hb0; rw [← hrb, map_zero]
  refine ⟨a', ha'0, hc, ?_⟩
  have hNm : Algebra.norm ℚ ((m : ℕ) : F) = (m : ℚ) ^ Module.finrank ℚ F := by
    rw [show ((m : ℕ) : F) = algebraMap ℚ F (m : ℚ) by simp]; exact Algebra.norm_algebraMap _
  have hprod : |(Algebra.norm ℚ b : ℝ)| * |(Algebra.norm ℚ a' : ℝ)| = (m : ℝ) ^ Module.finrank ℚ F := by
    have := congrArg (fun z : F => (Algebra.norm ℚ z : ℝ)) hba
    simp only [map_mul, Rat.cast_mul, hNm, Rat.cast_pow, Rat.cast_natCast] at this
    rw [← abs_mul, this, abs_of_nonneg (by positivity)]
  have h1 := abs_norm_algebraMap_le hr0 hr𝔫
  rw [hrb] at h1
  calc |(Algebra.norm ℚ a' : ℝ)| * (Ideal.absNorm 𝔫 : ℝ) ≤ |(Algebra.norm ℚ a' : ℝ)| * |(Algebra.norm ℚ b : ℝ)| :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (m : ℝ) ^ Module.finrank ℚ F := by rw [mul_comm]; exact hprod
    _ ≤ (C : ℝ) ^ Module.finrank ℚ F := by gcongr

theorem leftNrdIdeal_ne_bot (hO : IsOrder (𝓞 F) F O) (hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0) {J : Ideal O}
    (hJ : J ≠ ⊥) : leftNrdIdeal J ≠ ⊥ := by
  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  obtain ⟨n₀, hn₀⟩ := (isInteger_trd_nrd hO x₀.2).2
  have hn₀0 : n₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn₀
    exact hx₀0 (Subtype.ext (hdiv _ hn₀.symm))
  intro h
  have hmem : n₀ ∈ leftNrdIdeal J := Ideal.subset_span ⟨x₀, hx₀, hn₀⟩
  rw [h] at hmem
  exact hn₀0 ((Submodule.mem_bot _).1 hmem)

theorem finite_setOf_leftNrdIdeal_eq (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)}
    (h𝔫 : 𝔫 ≠ ⊥) : {J : Ideal O | leftNrdIdeal J = 𝔫}.Finite := by
  obtain ⟨hfin, -⟩ := finite_and_pos_card ha hb hO h𝔫
  exact Set.finite_coe_iff.mp hfin

/-- **The left ideal class set of a maximal order of a division quaternion algebra is finite, for every class number.**

Source: Voight 2021, Thm. 17.8.3 (finiteness of the class set); here via the pigeonhole `exists_small_mem` and the element
$c\bar x \in (\mathcal O : J)$, $c \in \operatorname{nrd}(J)^{-1}$ of small norm (`exists_small_inv`, `mul_star_mem`). -/
@[kb "voight2021" "Thm. 17.8.3"]
theorem finite_classes (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0) : Finite (Quotient (idealSetoid O)) := by
  classical
  obtain ⟨C, hC0, hsmall⟩ := exists_small_mem ha hb hO
  obtain ⟨CF, hCF0, hinv⟩ := exists_small_inv (F := F)
  set d := Module.finrank ℚ F
  set M0 := ⌊C * CF ^ 2⌋₊
  have hfinN : {𝔫 : Ideal (𝓞 F) | Ideal.absNorm 𝔫 ≤ M0}.Finite := Ideal.finite_setOfPred_absNorm_le M0
  set S : Set (Ideal O) := {J | J = ⊥ ∨ (Ideal.absNorm (leftNrdIdeal J) ≤ M0 ∧ leftNrdIdeal J ≠ ⊥)}
  have hS : S.Finite := by
    refine ((Set.finite_singleton ⊥).union (Set.Finite.biUnion (hfinN.subset (Set.inter_subset_left
      (t := {𝔫 : Ideal (𝓞 F) | 𝔫 ≠ ⊥}))) fun 𝔫 h𝔫 => finite_setOf_leftNrdIdeal_eq ha hb hO h𝔫.2)).subset ?_
    rintro J (rfl | ⟨h1, h2⟩)
    · exact Or.inl rfl
    · exact Or.inr (Set.mem_biUnion (x := leftNrdIdeal J) ⟨h1, h2⟩ rfl)
  have hsurj : ∀ c : Quotient (idealSetoid O), ∃ J ∈ S, Quotient.mk _ J = c := by
    intro c
    set J := c.out
    by_cases hJ : J = ⊥
    · exact ⟨⊥, Or.inl rfl, by rw [← hJ, Quotient.out_eq]⟩
    have hJn := leftNrdIdeal_ne_bot hO.1 hdiv hJ
    obtain ⟨x, hx, hx0, hxC⟩ := hsmall hJn
    obtain ⟨c0, hc00, hc0, hc0N⟩ := hinv hJn
    set N : ℕ := Ideal.absNorm (leftNrdIdeal J) with hNdef
    have hN0 : (0 : ℝ) < N := by
      rw [hNdef]; exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hJn)
    set β : QuatF F a b := c0 • star x
    have hβ : β ∈ colon J := by
      intro y hy
      have : y * β = c0 • (y * star x) := by
        simp only [β]; rw [mul_smul_comm]
      rw [this]
      exact mul_star_mem ha hb hO hJn hc0 hx hy
    have hnrdx : nrd x ≠ 0 := fun h => hx0 (hdiv x h)
    have hnrdβ : nrd β = c0 ^ 2 * nrd x := by rw [nrd_smul, nrd_star]
    have hβu : IsUnit β := by
      rw [isUnit_iff_nrd_ne_zero, hnrdβ]; exact mul_ne_zero (pow_ne_zero _ hc00) hnrdx
    set J' := rmulIdeal J β
    have hrel : IdealRel J J' := ⟨hβu.unit, by rw [IsUnit.unit_spec]; exact idealSet_rmulIdeal hβ⟩
    have hnorm : (Ideal.absNorm (leftNrdIdeal J') : ℝ) =
        (Ideal.absNorm (leftNrdIdeal J) : ℝ) * |(Algebra.norm ℚ (nrd β) : ℝ)| :=
      absNorm_leftNrdIdeal_rmulIdeal hO.1 hβ
    have hβnorm : |(Algebra.norm ℚ (nrd β) : ℝ)| =
        |(Algebra.norm ℚ c0 : ℝ)| ^ 2 * |(Algebra.norm ℚ (nrd x) : ℝ)| := by
      rw [hnrdβ, map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow]
    have hNc : 0 ≤ |(Algebra.norm ℚ c0 : ℝ)| := abs_nonneg _
    have hbound : (Ideal.absNorm (leftNrdIdeal J') : ℝ) ≤ C * CF ^ 2 := by
      rw [hnorm, hβnorm]
      have h1 : |(Algebra.norm ℚ c0 : ℝ)| * (N : ℝ) ≤ CF := hc0N
      have h2 : |(Algebra.norm ℚ (nrd x) : ℝ)| ≤ C * (N : ℝ) := hxC
      calc (N : ℝ) * (|(Algebra.norm ℚ c0 : ℝ)| ^ 2 * |(Algebra.norm ℚ (nrd x) : ℝ)|)
          ≤ (N : ℝ) * (|(Algebra.norm ℚ c0 : ℝ)| ^ 2 * (C * (N : ℝ))) := by gcongr
        _ = C * (|(Algebra.norm ℚ c0 : ℝ)| * (N : ℝ)) ^ 2 := by ring
        _ ≤ C * CF ^ 2 := by gcongr
    have hpos : (Ideal.absNorm (leftNrdIdeal J') : ℝ) ≠ 0 := by
      rw [hnorm, hβnorm]
      have : |(Algebra.norm ℚ (nrd x) : ℝ)| ≠ 0 :=
        abs_ne_zero.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hnrdx)
      have : |(Algebra.norm ℚ c0 : ℝ)| ≠ 0 :=
        abs_ne_zero.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hc00)
      positivity
    refine ⟨J', Or.inr ⟨Nat.le_floor hbound, ?_⟩, ?_⟩
    · intro h
      apply hpos
      rw [h]; simp
    · rw [← Quotient.out_eq c]
      exact Quotient.sound (IdealRel.symm hrel)
  have : Finite S := hS.to_subtype
  exact Finite.of_surjective (fun J : S => (Quotient.mk _ J.1 : Quotient (idealSetoid O))) fun c => by
    obtain ⟨J, hJS, hJc⟩ := hsurj c
    exact ⟨⟨J, hJS⟩, hJc⟩

end Finite

end Gen

end QuadFormsKB.QuatOrder
