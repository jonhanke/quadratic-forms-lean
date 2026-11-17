/-
# The completions of an Eichler order of level $\mathfrak M$ (Voight, Proposition 23.4.19)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): 23.4.12 (p. 384), Proposition 23.4.19 (p. 385).

**Setting.** $F$ a number field, $B = (a,b)_F$, $\mathcal O \subseteq B$ an Eichler order with a $\mathbb Z_F$-basis and
$\operatorname{discrd}\mathcal O = \mathfrak D\mathfrak M$, $\mathfrak M$ coprime to $\mathfrak D$ (`IsEichlerOrderOfLevel`).

**Theorem** (`eichlerLocalLevel`, the proposition `Wave4.EichlerLocalLevel F`, with the freeness hypothesis, proved for every
number field): at a finite place $v \mid \mathfrak D$ the completion $\mathcal O_v$ is maximal (the unique maximal order of the
division algebra $B_v$); at $v \nmid \mathfrak D$ some isomorphism $B_v \cong \mathrm M_2(F_v)$ carries $\mathcal O_v$ onto the standard Eichler
order $\mathcal O_0(\pi_v^{e_v})$ with $e_v = \operatorname{ord}_v\mathfrak M$.

*Proof.* $\mathcal O_v$ is Eichler (`eichlerIsLocal`). At a ramified $v$ every maximal order of $B_v$ is the valuation ring, so
$\mathcal O_v$ is maximal. At an unramified $v$, Proposition 23.4.3 gives $\varphi(\mathcal O_v) = \mathcal O_0(\pi^{e'})$. The Gram determinant of the
trace form in the completion of a global basis is $\iota_v(d)$, $(d) = (\mathfrak D\mathfrak M)^2$; in the standard Eichler order every basis has Gram
determinant a unit times $-\pi^{2e'}$ (`det_gram_basis`); comparing the ideals gives $e' = \operatorname{ord}_v\mathfrak M$.
-/
import QuadFormsKB.Literature.Voight.Wave9.EichlerLocalGlobal
import QuadFormsKB.Literature.Voight.Wave4.EichlerDiscriminant
import QuadFormsKB.Literature.Voight.Wave3.LocalDiscriminant

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Wave9

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Lattices QuadFormsKB.Voight QuadFormsKB.Voight.Wave3
  QuadFormsKB.Voight.Wave4 QuadFormsKB.LocalDensity.NF QuadFormsKB.Voight.MassWave2 QuadFormsKB.Voight.Disc IsLocalization

section Generic

variable {R K A : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Ring A]
  [Algebra K A] [Algebra R A] [IsScalarTower R K A]

/-- **The $R$-basis of a lattice cut out by a $K$-basis**: if $\Lambda = \{x : f\text{-coordinates of }x \in R\}$ for a
$K$-basis $f$ of $A$, then $f$ is an $R$-basis of $\Lambda$. -/
def latBasis (Λ : Subalgebra R A) (f : Module.Basis (Fin 4) K A)
    (hmem : ∀ x, x ∈ Λ ↔ ∀ i, IsInteger R (f.repr x i)) :
    Module.Basis (Fin 4) R (Subalgebra.toSubmodule Λ) :=
  Module.Basis.mk (v := fun i => (⟨f i, (hmem _).2 fun j => by
      rw [Module.Basis.repr_self]
      by_cases h : i = j
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩⟩ : Subalgebra.toSubmodule Λ))
    (by
      have : LinearIndependent R f := f.linearIndependent.restrict_scalars' R
      exact LinearIndependent.of_comp (Subalgebra.toSubmodule Λ).subtype this)
    (by
      rintro ⟨x, hx⟩ -
      choose c hc using (hmem x).1 hx
      have hx' : x = ∑ i, c i • f i := by
        conv_lhs => rw [← f.sum_repr x]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hc i, algebraMap_smul]
      have : (⟨x, hx⟩ : Subalgebra.toSubmodule Λ) = ∑ i, c i • (⟨f i, (hmem _).2 fun j => by
          rw [Module.Basis.repr_self]
          by_cases h : i = j
          · subst h; exact ⟨1, by simp⟩
          · exact ⟨0, by simp [h]⟩⟩ : Subalgebra.toSubmodule Λ) := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact hx'
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem latBasis_apply (Λ : Subalgebra R A) (f : Module.Basis (Fin 4) K A)
    (hmem : ∀ x, x ∈ Λ ↔ ∀ i, IsInteger R (f.repr x i)) (i : Fin 4) :
    ((latBasis Λ f hmem i : Subalgebra.toSubmodule Λ) : A) = f i := by
  simp [latBasis]

/-- In the standard Eichler order every basis cut out by a $K$-basis has Gram determinant a unit times $-\pi^{2e}$ (Voight 2021,
23.4.12). -/
theorem exists_unit_gram_std {π : R} (hπ : π ≠ 0) {e : ℕ} (f : Module.Basis (Fin 4) K (Matrix (Fin 2) (Fin 2) K))
    (hmem : ∀ x, x ∈ stdEichlerOrder R K π e ↔ ∀ i, IsInteger R (f.repr x i)) :
    ∃ u : Rˣ, (Matrix.of fun p q => Matrix.trace (f p * f q)).det =
      algebraMap R K (u : R) * (-(algebraMap R K π ^ e) ^ 2) := by
  obtain ⟨u, hu⟩ := det_gram_basis (e := e) hπ (latBasis _ f hmem)
  exact ⟨u, by simpa only [latBasis_apply] using hu⟩

end Generic

section Local

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **Local Gram determinant at a split place**: if $\varphi(\mathcal O_v) = \mathcal O_0(\pi^{e'})$ and $g$ is the integral trace Gram matrix
of a $\mathbb Z_F$-basis of $\mathcal O$, then $\iota_v(\det g) = u\cdot(-\pi^{2e'})$ with $u \in \mathfrak o_v^\times$. -/
theorem local_gram_std {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O)
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) (g : Matrix (Fin 4) (Fin 4) (𝓞 F))
    (hg : ∀ p q, algebraMap (𝓞 F) F (g p q) = trd ((e p : QuatF F a b) * (e q : QuatF F a b)))
    (φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv) {e' : ℕ}
    (hφ : (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[Fv] _).restrictScalars 𝔬) =
      stdEichlerOrder 𝔬 Fv (π v) e') :
    ∃ u : 𝔬ˣ, ι v g.det = u * (-(π v ^ e') ^ 2) := by
  classical
  set f := complBasis (v := v) e hO
  have hmem := mem_localOrder_iff (v := v) e hO
  have hinj : Function.Injective (algebraMap 𝔬 Fv) := IsFractionRing.injective _ _
  have hgram : gramTrd (fun q => f q) = algebraMap 𝔬 Fv (ι v g.det) := by
    have : (Matrix.of fun p q => trd (f p * f q)) =
        g.map (((algebraMap 𝔬 Fv).comp (ι v))) := by
      ext p q
      simp only [Matrix.of_apply, Matrix.map_apply, f, complBasis_apply, complBasisVec, ← map_mul,
        trd_complHom, ← hg, RingHom.comp_apply]
      rfl
    rw [gramTrd, this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, RingHom.comp_apply]
  set f' : Module.Basis (Fin 4) Fv (Matrix (Fin 2) (Fin 2) Fv) := f.map (φ : QuatV v a b ≃ₐ[Fv] _).toLinearEquiv
  have hrepr : ∀ x i, f'.repr x i = f.repr (φ.symm x) i := fun x i => rfl
  have hmem' : ∀ x, x ∈ stdEichlerOrder 𝔬 Fv (π v) e' ↔ ∀ i, IsInteger 𝔬 (f'.repr x i) := by
    intro x
    rw [← hφ, Subalgebra.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      rw [hrepr]
      show IsInteger 𝔬 (f.repr (φ.symm (φ y)) i)
      rw [φ.symm_apply_apply]
      exact (hmem y).1 hy i
    · intro h
      exact ⟨φ.symm x, (hmem _).2 fun i => by rw [← hrepr]; exact h i, φ.apply_symm_apply x⟩
  obtain ⟨u, hu⟩ := exists_unit_gram_std (irreducible_π v).ne_zero f' hmem'
  refine ⟨u, hinj ?_⟩
  rw [← hgram, map_mul, map_neg, map_pow, map_pow, ← hu]
  simp only [gramTrd]
  congr 1
  refine Matrix.ext fun p q => ?_
  simp only [Matrix.of_apply, f', Module.Basis.map_apply]
  have h := trace_algEquiv φ (f p * f q)
  rw [map_mul] at h
  exact h.symm

end Local

section Main

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-- An order with a $\mathbb Z_F$-basis (4 elements) is an `IsOrder` (it is finitely generated and spans $B$ over $F$). -/
theorem isOrder_of_basis {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) : IsOrder (𝓞 F) F O := by
  have hfin : Module.Finite (𝓞 F) (Subalgebra.toSubmodule O) := Module.Finite.of_basis e
  refine ⟨Module.Finite.iff_fg.1 hfin, ?_⟩
  have hli : LinearIndependent (𝓞 F) (fun i => (e i : QuatF F a b)) :=
    e.linearIndependent.map' (Subalgebra.toSubmodule O).subtype (Submodule.ker_subtype _)
  have hliF : LinearIndependent F (fun i => (e i : QuatF F a b)) := hli.localization F (nonZeroDivisors (𝓞 F))
  have htop := hliF.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, QuaternionAlgebra.finrank_eq_four])
  rw [eq_top_iff, ← htop]
  exact Submodule.span_mono (Set.range_subset_iff.2 fun i => (e i).2)

open Classical in
/-- **The completions of an Eichler order of level $\mathfrak M$** (Voight 2021, Proposition 23.4.19), for every number field and
every Eichler order with a $\mathbb Z_F$-basis (the statement `Wave4.EichlerLocalLevel F`). -/
@[kb "voight2021" "23.4.19, p. 385"]
theorem eichlerLocalLevel (F : Type) [Field F] [NumberField F] : EichlerLocalLevel F := by
  intro a b ha hb O 𝔐 hfree hlev v
  obtain ⟨hEich, hcop, hdisc⟩ := hlev
  obtain ⟨e⟩ := hfree
  have hOord : IsOrder (𝓞 F) F O := isOrder_of_basis e
  obtain ⟨O₁, O₂, h₁, h₂, hO12⟩ := hEich
  have hloc := (eichlerIsLocal F a b ha hb O hOord).1 ⟨O₁, O₂, h₁, h₂, hO12⟩ v
  have h2 := algebraMap_two_mul_ne_zero_nf (v := v) ha hb
  constructor
  · intro hram
    have hdiv := Gen.isRamifiedAt_finite_iff.1 ((mem_ramFin_iff ha hb).1 hram)
    obtain ⟨P₁, P₂, hP₁, hP₂, hP⟩ := hloc
    have e1 := eq_valOrder_of_isMaximalOrder (R := v.adicCompletionIntegers F) hdiv h2 hP₁
    have e2 := eq_valOrder_of_isMaximalOrder (R := v.adicCompletionIntegers F) hdiv h2 hP₂
    have : P₁ = P₂ := e1.trans e2.symm
    subst this
    rw [hP, inf_idem]
    exact hP₁
  · intro hnram
    rcases localOrder_ramified_or_split_nf (v := v) ha hb h₁ with ⟨hdiv, -⟩ | ⟨φ₀, -⟩
    · exact absurd ((mem_ramFin_iff ha hb).2 (Gen.isRamifiedAt_finite_iff.2 hdiv)) hnram
    · obtain ⟨φ, e', hφ⟩ := exists_algEquiv_localOrder_eq_stdEichlerOrder v hloc ⟨φ₀⟩
      refine ⟨φ, ?_⟩
      rw [hφ]
      congr 1
      -- compare ideals generated by the discriminant
      obtain ⟨g, hg⟩ := exists_int_gram hOord e
      obtain ⟨d, hd, hdspan⟩ := hdisc e
      have hdg : d = g.det := by
        apply (IsFractionRing.injective (𝓞 F) F)
        rw [hd, trdGramDet, RingHom.map_det]
        congr 1
        ext p q
        exact (hg p q).symm
      obtain ⟨u, hu⟩ := local_gram_std v hOord e g hg φ hφ
      rw [← hdg] at hu
      have hπ0 : π v ≠ 0 := (irreducible_π v).ne_zero
      have hπnu : ¬ IsUnit (π v) := (irreducible_π v).not_isUnit
      have hspan1 : Ideal.span {ι v d} = Ideal.span {π v ^ (2 * e')} := by
        rw [hu, Ideal.span_singleton_eq_span_singleton]
        refine Associated.symm ⟨u * (-1 : (v.adicCompletionIntegers F)ˣ), ?_⟩
        simp only [Units.val_mul, Units.val_neg, Units.val_one]
        ring
      have hd0 : d ≠ 0 := by
        intro h0
        have : ι v d ≠ 0 := by
          rw [hu]
          exact mul_ne_zero u.ne_zero (neg_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hπ0)))
        exact this (by rw [h0, map_zero])
      have hM0 : 𝔐 ≠ ⊥ := by
        rintro rfl
        have h' : Ideal.span {d} = ⊥ := by rw [hdspan]; simp
        exact hd0 (Ideal.span_singleton_eq_bot.1 h')
      have hmap : Ideal.span {ι v d} = Ideal.map (ι v) ((∏ w ∈ ramFin ha hb, w.asIdeal) ^ 2 * 𝔐 ^ 2) := by
        rw [← mul_pow, ← hdspan, Ideal.map_span, Set.image_singleton]
      rw [Ideal.map_mul, map_ι_ramIdeal_sq ha hb v, if_neg hnram, pow_zero, Ideal.span_singleton_one,
        ← Ideal.one_eq_top, one_mul] at hmap
      have hMpow : Ideal.map (ι v) (𝔐 ^ 2) = Ideal.span {π v ^ (cI v 𝔐 * 2)} := by
        have : Ideal.map (ι v) (𝔐 ^ 2) = (Ideal.map (ι v) 𝔐) ^ 2 := by
          change Ideal.mapHom (ι v) _ = _
          rw [map_pow]; rfl
        rw [this, map_ι_eq_span v hM0, Ideal.span_singleton_pow, ← pow_mul]
      rw [hMpow, hspan1, Ideal.span_singleton_eq_span_singleton] at hmap
      have hle1 := (pow_dvd_pow_iff hπ0 hπnu).1 hmap.dvd
      have hle2 := (pow_dvd_pow_iff hπ0 hπnu).1 hmap.symm.dvd
      have hee : e' = cI v 𝔐 := by omega
      rw [hee, cI, Ideal.count_associates_factors_eq hM0 v.isPrime v.ne_bot]

end Main

end QuadFormsKB.Voight.Wave9
