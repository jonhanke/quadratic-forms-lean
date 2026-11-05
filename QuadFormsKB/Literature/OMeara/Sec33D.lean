/-
# O'Meara §33D, §33I: the idèle group, volume, bounded sets; $(J_F : P_FJ_F^S) = h_F(S)$ (33:14, 33:14a)

**Setting.** As in `Sec64.lean`: $F$ is a number field, $J_F$ is Mathlib's `IdeleGroup (𝓞 F) F` (the units of the
adèle ring), with components `ideleAt i 𝔭` at the finite spots and `ideleAtInf i w` at the infinite spots; the
$S$-idèles $J_F^S$ are `sIdeles S` and the principal idèles $P_F$ are Mathlib's `IdeleGroup.principalSubgroup`. The
normalized valuation at a finite spot is the norm of `v.adicCompletion F` ($|\pi|_{\mathfrak p} = N\mathfrak p^{-1}$),
at an infinite spot $w$ it is $\lVert\cdot\rVert^{m_w}$ with $m_w = 1$ (real) or $2$ (complex), `InfinitePlace.mult`.
The ideal class group at a set $S$ of finite spots is `ClassGroupAt F S` (`Sec33B.lean`).

**Proves / defines**
* `norm_idele_eq` (§33D, p. 68): the *volume* $\lVert i\rVert = \prod_{\mathfrak p}|i_{\mathfrak p}|_{\mathfrak p}$ of
  an idèle is Mathlib's norm of the adèle ring; `norm_principal_mul` (p. 69): $\lVert\alpha i\rVert = \lVert i\rVert$
  (product formula);
* `IsBoundedByIdele`, `boundedCount` (§33D, p. 69): $x$ is *bounded* by $i$ when $|x|_{\mathfrak p} \le
  |i_{\mathfrak p}|_{\mathfrak p}$ for all $\mathfrak p$; $M(i)$ the number of elements bounded by $i$;
  `boundedCount_principal_mul`: $M(\alpha i) = M(i)$;
* `index_sup_sIdeles_eq_card_classGroupAt` (**33:14**): $(J_F : P_FJ_F^S) = h_F(S)$, finite;
* `exists_index_sup_sIdeles_eq_one` (**33:14a**).
-/
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec64
import QuadFormsKB.Literature.OMeara.Sec33B
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleIdeal

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F]

local notation "J" => IdeleGroup (𝓞 F) F

/-- **The volume of an idèle** (§33D, p. 68): $\lVert i\rVert = \prod_{\mathfrak p \in \Omega}|i_{\mathfrak p}|_{\mathfrak p}$
with the normalized valuations, a finite product. It is Mathlib's norm of the adèle ring:
$\lVert i\rVert = \prod_{w \mid \infty}\lVert i_w\rVert^{m_w}\cdot\prod_{\mathfrak p}\lVert i_{\mathfrak p}\rVert$. -/
@[kb "omeara1963" "§33D, p. 68 (the volume ||i|| of an idèle)"]
theorem norm_idele_eq (i : J) :
    ‖(i : AdeleRing (𝓞 F) F)‖ =
      (∏ w : InfinitePlace F, ‖ideleAtInf i w‖ ^ w.mult) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖ideleAt i v‖ :=
  AdeleRing.norm_apply_of_isUnit i.isUnit

theorem hasFiniteMulSupport_norm_ideleAt (i : J) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖ideleAt i v‖).HasFiniteMulSupport :=
  FiniteAdeleRing.hasFiniteMulSupport_norm (Prod.isUnit_iff.1 i.isUnit).2.unit

theorem norm_idele_mul (i j : J) :
    ‖((i * j : J) : AdeleRing (𝓞 F) F)‖ = ‖(i : AdeleRing (𝓞 F) F)‖ * ‖(j : AdeleRing (𝓞 F) F)‖ := by
  rw [norm_idele_eq, norm_idele_eq, norm_idele_eq]
  have h1 := hasFiniteMulSupport_norm_ideleAt i
  have h2 := hasFiniteMulSupport_norm_ideleAt j
  have : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖ideleAt (i * j) v‖ =
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖ideleAt i v‖) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖ideleAt j v‖ := by
    rw [← finprod_mul_distrib h1 h2]
    simp [ideleAt_mul]
  rw [this]
  have : ∏ w : InfinitePlace F, ‖ideleAtInf (i * j) w‖ ^ w.mult =
      (∏ w : InfinitePlace F, ‖ideleAtInf i w‖ ^ w.mult) * ∏ w : InfinitePlace F, ‖ideleAtInf j w‖ ^ w.mult := by
    rw [← Finset.prod_mul_distrib]
    simp [mul_pow]
  rw [this]; ring

/-- **The volume is invariant under principal idèles** (§33D, p. 69, from the Product Formula):
$\lVert\alpha i\rVert = \lVert i\rVert$ for $\alpha \in F^\times$. -/
@[kb "omeara1963" "§33D, p. 69 (||αi|| = ||i||)"]
theorem norm_principal_mul (α : Fˣ) (i : J) :
    ‖((IdeleGroup.unitEmbedding (𝓞 F) F α * i : J) : AdeleRing (𝓞 F) F)‖ = ‖(i : AdeleRing (𝓞 F) F)‖ := by
  rw [norm_idele_mul]
  have : ‖((IdeleGroup.unitEmbedding (𝓞 F) F α : J) : AdeleRing (𝓞 F) F)‖ = 1 :=
    AdeleRing.norm_algebraMap_eq_one_of_ne_zero α.ne_zero
  rw [this, one_mul]

/-- An element $x \in F$ is *bounded by the idèle* $i$ (§33D, p. 69) when $|x|_{\mathfrak p} \le |i_{\mathfrak p}|_{\mathfrak p}$
at every spot: $\lVert x\rVert_{\mathfrak p} \le \lVert i_{\mathfrak p}\rVert$ at the finite spots and
$\lVert x\rVert_w \le \lVert i_w\rVert$ at the infinite ones (equivalent to the inequality of normalized valuations,
which are powers of these). A subset is bounded by $i$ when each of its elements is. -/
@[kb "omeara1963" "§33D, p. 69 (a subset X of F bounded by the idèle i)"]
def IsBoundedByIdele (i : J) (x : F) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F), ‖(x : v.adicCompletion F)‖ ≤ ‖ideleAt i v‖) ∧
    ∀ w : InfinitePlace F, ‖(x : w.Completion)‖ ≤ ‖ideleAtInf i w‖

/-- $M(i)$ (§33D, p. 69): the number of elements of $F$ bounded by the idèle $i$ (Mathlib's `Nat.card`, which is $0$
for an infinite set, where O'Meara writes $\infty$; by 33:4 the set is finite). -/
@[kb "omeara1963" "§33D, p. 69 (M(i), the number of field elements bounded by i)"]
def boundedCount (i : J) : ℕ := Nat.card {x : F // IsBoundedByIdele i x}

theorem isBoundedByIdele_principal_mul (α : Fˣ) (i : J) (x : F) :
    IsBoundedByIdele (IdeleGroup.unitEmbedding (𝓞 F) F α * i) ((α : F) * x) ↔ IsBoundedByIdele i x := by
  unfold IsBoundedByIdele
  have hu : IsUnit ((IdeleGroup.unitEmbedding (𝓞 F) F α : J) : AdeleRing (𝓞 F) F) := Units.isUnit _
  obtain ⟨hu1, hu2, -⟩ := AdeleRing.isUnit_iff.1 hu
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · have h1 : ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α * i) v =
        ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α) v * ideleAt i v := rfl
    have hx : (((α : F) * x : F) : v.adicCompletion F) =
        ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α) v * (x : v.adicCompletion F) :=
      HeightOneSpectrum.adicCompletion.coe_mul F v (α : F) x
    have h2 : 0 < ‖ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F α) v‖ := norm_pos_iff.2 (hu2 v)
    rw [h1, hx, norm_mul, norm_mul]
    exact mul_le_mul_iff_right₀ h2
  · have h1 : ideleAtInf (IdeleGroup.unitEmbedding (𝓞 F) F α * i) w =
        ideleAtInf (IdeleGroup.unitEmbedding (𝓞 F) F α) w * ideleAtInf i w := rfl
    have hx : (((α : F) * x : F) : w.Completion) =
        ideleAtInf (IdeleGroup.unitEmbedding (𝓞 F) F α) w * (x : w.Completion) :=
      InfinitePlace.Completion.coe_mul w (α : F) x
    have h2 : 0 < ‖ideleAtInf (IdeleGroup.unitEmbedding (𝓞 F) F α) w‖ := norm_pos_iff.2 (hu1 w)
    rw [h1, hx, norm_mul, norm_mul]
    exact mul_le_mul_iff_right₀ h2

/-- $M(\alpha i) = M(i)$ for $\alpha \in F^\times$ (§33D, p. 69): $x \mapsto \alpha x$ is a bijection from the
elements bounded by $i$ onto those bounded by $\alpha i$. -/
@[kb "omeara1963" "§33D, p. 69 (M(i) = M(αi))"]
theorem boundedCount_principal_mul (α : Fˣ) (i : J) :
    boundedCount (IdeleGroup.unitEmbedding (𝓞 F) F α * i) = boundedCount i := by
  unfold boundedCount
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : {x : F // IsBoundedByIdele i x} =>
      (⟨(α : F) * x.1, (isBoundedByIdele_principal_mul α i x.1).2 x.2⟩ :
        {x : F // IsBoundedByIdele (IdeleGroup.unitEmbedding (𝓞 F) F α * i) x})) ⟨?_, ?_⟩).symm
  · intro a b h
    have := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel₀ α.ne_zero this)
  · rintro ⟨y, hy⟩
    refine ⟨⟨(α : F)⁻¹ * y, ?_⟩, Subtype.ext (by simp [α.ne_zero])⟩
    rw [← isBoundedByIdele_principal_mul α i]
    simpa [← mul_assoc, α.ne_zero] using hy

open QuadFormsKB.Tamagawa.Measure.Weil (ordAt ideleIdeal count_ideleIdeal valued_eq_exp_ordAt
  ideleIdeal_finDiag ideleIdeal_surjective)

/-- The finite part of an idèle, as a unit of the finite adèle ring. -/
def finPartHom : J →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

theorem finPartHom_surjective : Function.Surjective (finPartHom (F := F)) := by
  intro z
  refine ⟨⟨(1, (z : FiniteAdeleRing (𝓞 F) F)), (1, ((z⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    FiniteAdeleRing (𝓞 F) F)), ?_, ?_⟩, ?_⟩
  · exact Prod.ext (mul_one (1 : InfiniteAdeleRing F)) (Units.mul_inv z)
  · exact Prod.ext (mul_one (1 : InfiniteAdeleRing F)) (Units.inv_mul z)
  · exact Units.ext rfl

theorem ordAt_finPartHom (i : J) (v : HeightOneSpectrum (𝓞 F)) :
    ordAt (finPartHom i) v = -WithZero.log (Valued.v (ideleAt i v)) := rfl

theorem valued_ideleAt_eq_exp (i : J) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (ideleAt i v) = WithZero.exp (-ordAt (finPartHom i) v) :=
  valued_eq_exp_ordAt (finPartHom i) v

theorem finPartHom_unitEmbedding (α : Fˣ) :
    finPartHom (IdeleGroup.unitEmbedding (𝓞 F) F α) =
      Tamagawa.Measure.Weil.finDiag α := Units.ext rfl

/-- The class of the ideal of the finite part of an idèle in $\mathrm{Cl}_F(S)$. -/
def idealClassHom (S : Set (HeightOneSpectrum (𝓞 F))) : J →* ClassGroupAt F S :=
  (QuotientGroup.mk' (principalAt F S)).comp ((ideleIdeal F).comp finPartHom)

theorem idealClassHom_surjective (S : Set (HeightOneSpectrum (𝓞 F))) :
    Function.Surjective (idealClassHom (F := F) S) :=
  (QuotientGroup.mk'_surjective _).comp ((ideleIdeal_surjective (F := F)).comp finPartHom_surjective)

theorem ker_idealClassHom (S : Set (HeightOneSpectrum (𝓞 F))) :
    (idealClassHom (F := F) S).ker = IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sIdeles S := by
  apply le_antisymm
  · intro i hi
    rw [MonoidHom.mem_ker, idealClassHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hi
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hi
    obtain ⟨α, rfl⟩ := hz
    refine Subgroup.mem_sup.2 ⟨IdeleGroup.unitEmbedding (𝓞 F) F α, ⟨α, rfl⟩,
      i * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹, ?_,
      by rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]⟩
    intro v hv
    rw [valued_ideleAt_eq_exp]
    have h1 : ideleIdeal F (finPartHom (i * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹)) = y := by
      simp only [map_mul, map_inv, finPartHom_unitEmbedding]
      rw [ideleIdeal_finDiag, ← hyz]; group
    have h2 := count_ideleIdeal (finPartHom (i * (IdeleGroup.unitEmbedding (𝓞 F) F α)⁻¹)) v
    rw [h1, hy v hv] at h2
    rw [← h2]; simp
  · refine sup_le ?_ ?_
    · rintro _ ⟨α, rfl⟩
      rw [MonoidHom.mem_ker, idealClassHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, finPartHom_unitEmbedding]
      exact Subgroup.mem_sup_right ⟨α, (ideleIdeal_finDiag α).symm⟩
    · intro i hi
      rw [MonoidHom.mem_ker, idealClassHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      refine Subgroup.mem_sup_left ?_
      intro v hv
      rw [count_ideleIdeal]
      have := hi v hv
      rw [valued_ideleAt_eq_exp, ← WithZero.exp_zero, WithZero.exp_inj, neg_eq_zero] at this
      exact this

/-- **33:14 (Theorem).** Let $S$ be a set of finite spots of the number field $F$ (a Dedekind set when non-empty,
33:12). Then the index $(J_F : P_FJ_F^S)$ of the subgroup generated by the principal idèles and the $S$-idèles equals
the class number $h_F(S)$, and it is finite. O'Meara's proof: the map $J_F \to I(S)$ sending $i$ to the fractional
ideal $\mathfrak a$ with $|\mathfrak a|_{\mathfrak p} = |i_{\mathfrak p}|_{\mathfrak p}$ ($\mathfrak p \in S$) is onto,
with kernel $J_F^S$, and the preimage of $P(S)$ is $P_FJ_F^S$. -/
@[kb "omeara1963" "§33I, 33:14, p. 80"]
theorem index_sup_sIdeles_eq_card_classGroupAt (S : Set (HeightOneSpectrum (𝓞 F))) :
    (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sIdeles S).index = Nat.card (ClassGroupAt F S) ∧
      (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sIdeles S).index ≠ 0 := by
  have h : (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sIdeles S).index = Nat.card (ClassGroupAt F S) := by
    rw [← ker_idealClassHom, Subgroup.index]
    exact Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective _ (idealClassHom_surjective S)).toEquiv
  refine ⟨h, ?_⟩
  rw [h]
  have := finite_classGroupAt F S
  exact Nat.card_pos.ne'

/-- **33:14a (Corollary).** There is a finite set $T$ of finite spots (so $S_0 = \Omega - T$ minus the infinite
spots is a Dedekind set of almost all spots) such that $(J_F : P_FJ_F^S) = 1$ for every set $S \subseteq S_0$ of
finite spots. -/
@[kb "omeara1963" "§33I, 33:14a, p. 81"]
theorem exists_index_sup_sIdeles_eq_one :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Set (HeightOneSpectrum (𝓞 F)),
      Disjoint S (T : Set _) → (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sIdeles S).index = 1 := by
  obtain ⟨T, hT⟩ := exists_finite_set_classGroupAt_subsingleton (F := F)
  refine ⟨T, fun S hS => ?_⟩
  have := hT S hS
  rw [(index_sup_sIdeles_eq_card_classGroupAt S).1]
  exact Nat.card_unique

end QuadFormsKB.OMeara
