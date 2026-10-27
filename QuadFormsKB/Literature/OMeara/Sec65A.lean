/-
# O'Meara §65A–§65B: the conventions on $S$, the group $J^{S,2}$, and the index $(J^S : J^{S,2}) = 4^s$

**Setting** (as in `Sec64.lean`): $F$ is a number field, $J_F$ = Mathlib's `IdeleGroup (𝓞 F) F`, and $S$ is a set of
finite spots. The spots of $F$ are `NFPlace F`; $\Omega - S$ is `outsideS S` (the finite spots not in $S$ and all
infinite spots), and $s = \lvert\Omega - S\rvert$ is its cardinality (`Set.ncard`).

**Defines**
* `SConventions S` (§65A, p. 174, conditions (i)–(iv)): every spot of $S$ is discrete and non-dyadic, $S$ contains
  almost all spots, and $J_F = P_F J_F^S$; condition (iii) ($S \ne \Omega$) holds automatically because $S$ consists of
  finite spots;
* `sqSIdeles S` $= J^{S,2}$ (§65A, p. 174): the $S$-idèles that are squares at every spot of $\Omega - S$;
* `splitA θ S`, `splitB θ S` (§65A, p. 176): the spots of $\Omega - S$ at which $\theta$ is a square
  (local degree $n_\mathfrak p = 1$) or a non-square ($n_\mathfrak p = 2$); that these are O'Meara's conditions on the
  local degree is the decomposition of spots in $F(\sqrt\theta)$ (`HN.two_primes_of_isSquare`, row 65.r4).

**Proves**
* `sqSIdeles_eq_sup` (p. 174): $J^{S,2} = K^S (J^S)^2$ when $\Omega - S$ is finite;
* `ncard_splitA_add_ncard_splitB` (p. 176): $a + b = s$;
* Proposition 65:7 (p. 178): $(J^S : J^{S,2}) = 4^s$ (`relIndex_sqSIdeles`).
-/
import QuadFormsKB.Literature.OMeara.Sec64
import QuadFormsKB.Defs.NumberField
import QuadFormsKB.Literature.HasseNorm.Infinite

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F]

local notation "J" => IdeleGroup (𝓞 F) F

/-- **The spots of $\Omega - S$**: the finite spots not in $S$ and all infinite spots. -/
def outsideS (S : Set (HeightOneSpectrum (𝓞 F))) : Set (NFPlace F) :=
  {p | match p with
    | .finite v => v ∉ S
    | .infinite _ => True}

/-- **O'Meara's conventions on $S$ in §65** (O'Meara 1963, §65A, p. 174): (i) every spot in $S$ is discrete and
non-dyadic ($2 \notin \mathfrak p$); (ii) $S$ consists of almost all spots ($\Omega - S$ is finite); (iii) $S$ is not
all of $\Omega$ (automatic: $S$ consists of finite spots); (iv) $J_F = P_F J_F^S$. O'Meara notes that such an $S$
exists by Corollary 33:14a; that existence is not formalized here. -/
@[kb "omeara1963" "§65A, p. 174 (conditions (i)–(iv) on S)"]
structure SConventions (S : Set (HeightOneSpectrum (𝓞 F))) : Prop where
  nondyadic : ∀ v ∈ S, (2 : 𝓞 F) ∉ v.asIdeal
  cofinite : Sᶜ.Finite
  ideles : ∀ i : J, ∃ p ∈ IdeleGroup.principalSubgroup (𝓞 F) F, ∃ j ∈ sIdeles S, i = p * j

theorem ideleAt_ofCompletion (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : w.Completionˣ) :
    ideleAt (IdeleGroup.ofCompletion (𝓞 F) F w y) v = 1 := rfl

theorem ideleAtInf_ofCompletion_self (w : InfinitePlace F) (y : w.Completionˣ) :
    ideleAtInf (IdeleGroup.ofCompletion (𝓞 F) F w y) w = y := by
  classical
  show (MonoidHom.mulSingle (fun w : InfinitePlace F => w.Completion) w (y : w.Completion) :
    Π w', w'.Completion) w = y
  exact Pi.mulSingle_eq_same w _

theorem ideleAtInf_ofCompletion_ne (w w' : InfinitePlace F) (h : w' ≠ w) (y : w.Completionˣ) :
    ideleAtInf (IdeleGroup.ofCompletion (𝓞 F) F w y) w' = 1 := by
  classical
  show (MonoidHom.mulSingle (fun w : InfinitePlace F => w.Completion) w (y : w.Completion) :
    Π w', w'.Completion) w' = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem isSquare_coe_iff {K : Type*} [Field K] (u : Kˣ) :
    IsSquare (u : K) ↔ u ∈ (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by simp at hr)
    exact ⟨Units.mk0 r hr0, Units.ext (by simp [powMonoidHom, pow_two, hr])⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp [powMonoidHom, pow_two]⟩

/-- The component of an idèle at a finite spot, as a homomorphism to the unit group. -/
def idAtHom (v : HeightOneSpectrum (𝓞 F)) : J →* (v.adicCompletion F)ˣ where
  toFun i := ⟨ideleAt i v, ideleAt i⁻¹ v, by rw [← ideleAt_mul]; simp, by rw [← ideleAt_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp)

/-- The component of an idèle at an infinite spot, as a homomorphism to the unit group. -/
def idAtInfHom (w : InfinitePlace F) : J →* w.Completionˣ where
  toFun i := ⟨ideleAtInf i w, ideleAtInf i⁻¹ w, by rw [← ideleAtInf_mul]; simp, by rw [← ideleAtInf_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp)

@[simp] theorem coe_idAtHom (v : HeightOneSpectrum (𝓞 F)) (i : J) : (idAtHom v i : v.adicCompletion F) = ideleAt i v :=
  rfl

@[simp] theorem coe_idAtInfHom (w : InfinitePlace F) (i : J) : (idAtInfHom w i : w.Completion) = ideleAtInf i w :=
  rfl

/-- **Existence of idèles with prescribed components outside $S$** when $\Omega - S$ is finite: components
$x_\mathfrak p$ at the finite spots outside $S$, $y_w$ at the infinite spots, and $1$ at the spots of $S$. -/
theorem exists_idele {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite)
    (x : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ) (y : ∀ w : InfinitePlace F, w.Completionˣ) :
    ∃ j : J, (∀ v ∉ S, ideleAt j v = x v) ∧ (∀ v ∈ S, ideleAt j v = 1) ∧ ∀ w, ideleAtInf j w = y w := by
  classical
  let j : J := (∏ u ∈ hS.toFinset, IdeleGroup.ofAdicCompletion (𝓞 F) F u (x u)) *
    ∏ w : InfinitePlace F, IdeleGroup.ofCompletion (𝓞 F) F w (y w)
  have hA : ∀ (s : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)),
      ideleAt (∏ u ∈ s, IdeleGroup.ofAdicCompletion (𝓞 F) F u (x u)) v =
        if v ∈ s then (x v : v.adicCompletion F) else 1 := by
    intro s v
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ideleAt_mul, ih]
      by_cases hv : v = a
      · subst hv; simp [ha, ideleAt_ofAdic_self]
      · simp [hv, ideleAt_ofAdic_ne a v hv]
  have hB : ∀ (v : HeightOneSpectrum (𝓞 F)),
      ideleAt (∏ w : InfinitePlace F, IdeleGroup.ofCompletion (𝓞 F) F w (y w)) v = 1 := by
    intro v
    induction (Finset.univ : Finset (InfinitePlace F)) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, ideleAt_mul, ih, ideleAt_ofCompletion]; simp
  have hC : ∀ (w : InfinitePlace F),
      ideleAtInf (∏ u ∈ hS.toFinset, IdeleGroup.ofAdicCompletion (𝓞 F) F u (x u)) w = 1 := by
    intro w
    induction hS.toFinset using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, ideleAtInf_mul, ih, ideleAtInf_ofAdic]; simp
  have hD : ∀ (w : InfinitePlace F),
      ideleAtInf (∏ w' : InfinitePlace F, IdeleGroup.ofCompletion (𝓞 F) F w' (y w')) w = y w := by
    intro w
    have : ∀ (s : Finset (InfinitePlace F)),
        ideleAtInf (∏ w' ∈ s, IdeleGroup.ofCompletion (𝓞 F) F w' (y w')) w =
          if w ∈ s then (y w : w.Completion) else 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, ideleAtInf_mul, ih]
        by_cases hv : w = a
        · subst hv; simp [ha, ideleAtInf_ofCompletion_self]
        · simp [hv, ideleAtInf_ofCompletion_ne a w hv]
    rw [this]; simp
  refine ⟨j, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
  · simp only [j, ideleAt_mul, hA, hB]
    simp [hv]
  · simp only [j, ideleAt_mul, hA, hB]
    simp [hv]
  · simp only [j, ideleAtInf_mul, hC, hD]
    simp

/-- **The group $J^{S,2}$** (O'Meara 1963, §65A, p. 174): the $S$-idèles that are squares at every spot of
$\Omega - S$. -/
@[kb "omeara1963" "§65A, p. 174 (J^{S,2}, the S-idèles that are squares outside S)"]
def sqSIdeles (S : Set (HeightOneSpectrum (𝓞 F))) : Subgroup J where
  carrier := {i | i ∈ sIdeles S ∧ (∀ v ∉ S, IsSquare (ideleAt i v)) ∧ ∀ w : InfinitePlace F, IsSquare (ideleAtInf i w)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    exact ⟨(sIdeles S).mul_mem ha1 hb1, fun v hv => by simpa using (ha2 v hv).mul (hb2 v hv),
      fun w => by simpa using (ha3 w).mul (hb3 w)⟩
  one_mem' := ⟨(sIdeles S).one_mem, fun v _ => by simp, fun w => by simp⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3⟩
    exact ⟨(sIdeles S).inv_mem ha1, fun v hv => by rw [ideleAt_inv]; exact (ha2 v hv).inv,
      fun w => by rw [ideleAtInf_inv]; exact (ha3 w).inv⟩

theorem sqSIdeles_le_sIdeles (S : Set (HeightOneSpectrum (𝓞 F))) : sqSIdeles S ≤ sIdeles S := fun _ h => h.1

/-- **$J^{S,2} = K^S (J^S)^2$** (O'Meara 1963, §65A, p. 174), when $\Omega - S$ is finite. -/
@[kb "omeara1963" "§65A, p. 174 (J^{S,2} = K^S (J^S)²)"]
theorem sqSIdeles_eq_sup {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    sqSIdeles S = kIdeles S ⊔ (sIdeles S).map (powMonoidHom 2) := by
  apply le_antisymm
  · rintro i ⟨his, hsq, hsqinf⟩
    have hx : ∀ v : HeightOneSpectrum (𝓞 F), ∃ y : (v.adicCompletion F)ˣ,
        v ∉ S → ideleAt i v = y * y := by
      intro v
      by_cases hv : v ∈ S
      · exact ⟨1, fun h => absurd hv h⟩
      · obtain ⟨r, hr⟩ := hsq v hv
        have hr0 : r ≠ 0 := by
          rintro rfl
          have h1 : ideleAt i v * ideleAt i⁻¹ v = 1 := by rw [← ideleAt_mul]; simp
          rw [hr] at h1; simp at h1
        exact ⟨Units.mk0 r hr0, fun _ => by simpa using hr⟩
    have hy : ∀ w : InfinitePlace F, ∃ y : w.Completionˣ, ideleAtInf i w = y * y := by
      intro w
      obtain ⟨r, hr⟩ := hsqinf w
      have hr0 : r ≠ 0 := by
        rintro rfl
        have h1 : ideleAtInf i w * ideleAtInf i⁻¹ w = 1 := by rw [← ideleAtInf_mul]; simp
        rw [hr] at h1; simp at h1
      exact ⟨Units.mk0 r hr0, by simpa using hr⟩
    choose x hx using hx
    choose y hy using hy
    obtain ⟨j, hj1, hj2, hj3⟩ := exists_idele hS x y
    have hjS : j ∈ sIdeles S := fun v hv => by rw [hj2 v hv]; simp
    refine Subgroup.mem_sup.mpr ⟨i * (j ^ 2)⁻¹, ?_, j ^ 2, ⟨j, hjS, by simp [powMonoidHom]⟩, by simp⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · simp [ideleAt_inv, pow_two, hj2 v hv, his v hv]
    · have := hx v hv
      simp only [pow_two, ideleAt_mul, ideleAt_inv, hj1 v hv, this]
      have h := (x v).ne_zero
      field_simp
    · simp only [pow_two, ideleAtInf_mul, ideleAtInf_inv, hj3 w, hy w]
      have h := (y w).ne_zero
      field_simp
  · refine sup_le (fun i hi => ⟨kIdeles_le_sIdeles S hi, fun v hv => ?_, fun w => ?_⟩) ?_
    · rw [hi.2.1 v hv]; exact IsSquare.one
    · rw [hi.2.2 w]; exact IsSquare.one
    · rintro _ ⟨j, hj, rfl⟩
      refine ⟨(sIdeles S).pow_mem hj 2, fun v _ => ⟨ideleAt j v, ?_⟩, fun w => ⟨ideleAtInf j w, ?_⟩⟩
      · simp [powMonoidHom, pow_two]
      · simp [powMonoidHom, pow_two]

/-- **The spots $A$** (O'Meara 1963, §65A, p. 176): the spots of $\Omega - S$ with local degree $n_\mathfrak p = 1$,
i.e. at which $\theta$ is a square. -/
@[kb "omeara1963" "§65A, p. 176 (the set A of spots outside S with n_𝔭 = 1)"]
def splitA (θ : F) (S : Set (HeightOneSpectrum (𝓞 F))) : Set (NFPlace F) :=
  {p | p ∈ outsideS S ∧ p.atPlace (fun K _ _ => IsSquare (algebraMap F K θ))}

/-- **The spots $B$** (O'Meara 1963, §65A, p. 176): the spots of $\Omega - S$ with local degree $n_\mathfrak p = 2$,
i.e. at which $\theta$ is a non-square. -/
@[kb "omeara1963" "§65A, p. 176 (the set B of spots outside S with n_𝔭 = 2)"]
def splitB (θ : F) (S : Set (HeightOneSpectrum (𝓞 F))) : Set (NFPlace F) :=
  {p | p ∈ outsideS S ∧ ¬ p.atPlace (fun K _ _ => IsSquare (algebraMap F K θ))}

open scoped Classical in
theorem outsideS_eq_coe{S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    outsideS S = ↑((hS.toFinset.map ⟨NFPlace.finite, fun _ _ h => NFPlace.finite.inj h⟩) ∪
      (Finset.univ : Finset (InfinitePlace F)).map ⟨NFPlace.infinite, fun _ _ h => NFPlace.infinite.inj h⟩) := by
  classical
  ext p
  cases p with
  | infinite w => simp [outsideS]; exact ⟨w, rfl⟩
  | finite v =>
    simp [outsideS]
    exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨x, hx, e⟩ => by cases e; exact hx⟩

theorem outsideS_finite {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) : (outsideS S).Finite := by
  rw [outsideS_eq_coe hS]; exact Finset.finite_toSet _

theorem ncard_outsideS {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    (outsideS S).ncard = hS.toFinset.card + Fintype.card (InfinitePlace F) := by
  classical
  rw [outsideS_eq_coe hS, Set.ncard_coe_finset, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map,
    Finset.card_univ]
  rw [Finset.disjoint_left]
  intro p hp hq
  simp only [Finset.mem_map] at hp hq
  obtain ⟨a, _, rfl⟩ := hp
  obtain ⟨b, _, h⟩ := hq
  cases h

/-- **$a + b = s$** (O'Meara 1963, §65A, p. 176): $\Omega - S$ is the disjoint union of $A$ and $B$. -/
@[kb "omeara1963" "§65A, p. 176 (a + b = s)"]
theorem ncard_splitA_add_ncard_splitB (θ : F) {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    (splitA θ S).ncard + (splitB θ S).ncard = (outsideS S).ncard := by
  have hfin := outsideS_finite hS
  have hA : splitA θ S ⊆ outsideS S := fun p hp => hp.1
  have hB : splitB θ S ⊆ outsideS S := fun p hp => hp.1
  have hdisj : Disjoint (splitA θ S) (splitB θ S) :=
    Set.disjoint_left.mpr fun p hp hq => hq.2 hp.2
  rw [← Set.ncard_union_eq hdisj (hfin.subset hA) (hfin.subset hB)]
  congr 1
  ext p
  simp only [Set.mem_union, splitA, splitB, Set.mem_ofPred_eq]
  tauto

theorem index_pi_dep {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Group (A i)] (H : ∀ i, Subgroup (A i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

/-- **Proposition 65:7** (O'Meara 1963, p. 178): if every spot of $S$ is non-dyadic and $\Omega - S$ is finite, then
$(J^S : J^{S,2}) = 4^{s}$ with $s = \lvert\Omega - S\rvert$. (O'Meara's proof: $J^S/J^{S,2} \cong
\prod_{\mathfrak p \in \Omega - S} \dot F_\mathfrak p/\dot F_\mathfrak p^{2}$, and the product of the local indices of
63:9 and of the archimedean indices $2$ (real) and $1$ (complex) is $4^{s}$ by the product formula for
$\lvert 2\rvert$.) -/
@[kb "omeara1963" "§65B, 65:7, p. 178 ((J^S : J^{S,2}) = 4^s)"]
theorem relIndex_sqSIdeles {S : Set (HeightOneSpectrum (𝓞 F))} (h2 : ∀ v ∈ S, (2 : 𝓞 F) ∉ v.asIdeal)
    (hS : Sᶜ.Finite) : (sqSIdeles S).relIndex (sIdeles S) = 4 ^ (outsideS S).ncard := by
  classical
  set T := hS.toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ v ∉ S := fun v => by simp [hT]
  let ψ : J →* (∀ v : T, (v.1.adicCompletion F)ˣ) × (∀ w : InfinitePlace F, w.Completionˣ) :=
    MonoidHom.prod (MonoidHom.pi fun v => idAtHom v.1) (MonoidHom.pi fun w => idAtInfHom w)
  let Sq : Subgroup ((∀ v : T, (v.1.adicCompletion F)ˣ) × (∀ w : InfinitePlace F, w.Completionˣ)) :=
    (Subgroup.pi Set.univ fun v : T => (powMonoidHom 2 : (v.1.adicCompletion F)ˣ →* _).range).prod
      (Subgroup.pi Set.univ fun w : InfinitePlace F => (powMonoidHom 2 : w.Completionˣ →* _).range)
  have hker : Sq.comap ψ ⊓ sIdeles S = sqSIdeles S := by
    ext i
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, Sq, Subgroup.mem_prod, Subgroup.mem_pi, Set.mem_univ,
      true_implies]
    constructor
    · rintro ⟨⟨h1, h2⟩, hi⟩
      refine ⟨hi, fun v hv => ?_, fun w => ?_⟩
      · exact (isSquare_coe_iff (idAtHom v i)).mpr (h1 ⟨v, (hmemT v).mpr hv⟩)
      · exact (isSquare_coe_iff (idAtInfHom w i)).mpr (h2 w)
    · rintro ⟨hi, h1, h2⟩
      exact ⟨⟨fun v => (isSquare_coe_iff (idAtHom v.1 i)).mp (h1 v.1 ((hmemT v.1).mp v.2)),
        fun w => (isSquare_coe_iff (idAtInfHom w i)).mp (h2 w)⟩, hi⟩
  have hsurj : ∀ g, ∃ i ∈ sIdeles S, ψ i = g := by
    rintro ⟨a, b⟩
    obtain ⟨j, hj1, hj2, hj3⟩ := exists_idele hS (fun v => if h : v ∈ T then a ⟨v, h⟩ else 1) b
    have hjS : j ∈ sIdeles S := fun v hv => by rw [hj2 v hv]; simp
    refine ⟨j, hjS, Prod.ext (funext fun v => ?_) (funext fun w => ?_)⟩
    · exact Units.ext ((hj1 v.1 ((hmemT v.1).mp v.2)).trans (by simp [v.2]))
    · exact Units.ext (hj3 w)
  have hmap : (sIdeles S).map ψ = ⊤ :=
    eq_top_iff.mpr fun g _ => let ⟨i, hi, e⟩ := hsurj g; ⟨i, hi, e⟩
  rw [← hker, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap, hmap, Subgroup.relIndex_top_right,
    Subgroup.index_prod, index_pi_dep, index_pi_dep]
  have hdy : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → v ∈ T := fun v hv =>
    (hmemT v).mpr fun hvS => h2 v hvS hv
  have := QuadFormsKB.HN.prod_index_sq T hdy
  rw [Finset.prod_coe_sort T (fun v => (powMonoidHom 2 : (v.adicCompletion F)ˣ →* _).range.index)]
  rw [this, ncard_outsideS hS]

end QuadFormsKB.OMeara
