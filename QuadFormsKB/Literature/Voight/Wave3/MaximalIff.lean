/-
# Maximality is detected by the discriminant (Voight, Theorem 15.5.5, both directions)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Lemma 15.2.5 (p. 242),
Theorem 15.5.5 (p. 249), Lemma 9.5.3 and Lemma 10.4.3 (orders and their completions).

**Contents.**
* `exists_basis_mem_iff`: an order over a principal ideal domain has a $K$-basis $f$ of $B$ such that $\mathcal O$ is
  the set of elements with coordinates in $R$.
* `le_of_isUnit_gramTrd`, `le_of_gramTrd_ramified` (local): if $\mathcal O \subseteq \mathcal O'$ are orders over a
  discrete valuation ring and $d(\mathcal O)$ is a unit (split case) or $d(\mathcal O) \in \pi^2R^\times$ and $B$ is a
  division algebra (ramified case), then $\mathcal O' = \mathcal O$.
* **`maximalIffDiscriminant F`**: Theorem 15.5.5 for every number field $F$: an order with a $\mathbb Z_F$-basis is
  maximal iff $\operatorname{discrd}\mathcal O = \mathfrak D$. The "only if" half is `Disc.maximalOrderDiscriminant`.
-/
import QuadFormsKB.Literature.Voight.Wave3.LocalDiscriminant

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Disc

open QuadFormsKB.Quat QuadFormsKB.QuatOrder IsLocalization

/-! ## Bases of orders over a principal ideal domain -/

section Basis

variable {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {a b : K}

/-- **An order over a principal ideal domain is free of rank 4, with coordinates**: there is a $K$-basis $f$ of
$B = (a,b)_K$ with $\mathcal O = \{x : f\text{-coordinates of } x \in R\}$. -/
theorem exists_basis_mem_iff {O : Subalgebra R ℍ[K,a,b]} (hO : IsOrder R K O) :
    ∃ f : Module.Basis (Fin 4) K ℍ[K,a,b], ∀ x, x ∈ O ↔ ∀ i, IsInteger R (f.repr x i) := by
  have hlat : Submodule.IsLattice K (Subalgebra.toSubmodule O) := ⟨hO.fg, hO.span⟩
  have hr := Submodule.IsLattice.rank' K (Subalgebra.toSubmodule O)
  rw [QuaternionAlgebra.rank_eq_four] at hr
  have h4 : Module.finrank R (Subalgebra.toSubmodule O) = 4 := Module.finrank_eq_of_rank_eq hr
  set e := Module.finBasisOfFinrankEq R (Subalgebra.toSubmodule O) h4
  set f := e.extendOfIsLattice K
  have hf : ∀ i, f i = (e i : ℍ[K,a,b]) := fun i => Module.Basis.extendOfIsLattice_apply K e i
  refine ⟨f, fun x => ⟨fun hx i => ?_, fun h => ?_⟩⟩
  · refine ⟨e.repr ⟨x, hx⟩ i, ?_⟩
    have hsum : x = ∑ j, algebraMap R K (e.repr ⟨x, hx⟩ j) • f j := by
      have h := congrArg Subtype.val (e.sum_repr (⟨x, hx⟩ : Subalgebra.toSubmodule O))
      rw [Submodule.coe_sum] at h
      refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [hf, algebraMap_smul]; rfl
    have h2 := congrArg (fun y => f.repr y i) hsum
    simp only [Module.Basis.repr_sum_self] at h2
    exact h2.symm
  · choose c hc using h
    rw [← f.sum_repr x]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [← hc i, algebraMap_smul, hf]
    exact Subalgebra.smul_mem _ (e i).2 _

end Basis

/-! ## Comparing two orders by their discriminants -/

section Compare

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {a b : K}
  {O O' : Subalgebra R ℍ[K,a,b]} (f f' : Module.Basis (Fin 4) K ℍ[K,a,b])
  (hf : ∀ x, x ∈ O ↔ ∀ i, IsInteger R (f.repr x i)) (hf' : ∀ x, x ∈ O' ↔ ∀ i, IsInteger R (f'.repr x i))

include hf hf' in
/-- **Lemma 15.2.5 for a pair of orders** $\mathcal O \subseteq \mathcal O'$: $d(f) = \det(n)^2\,d(f')$ with $n$ the integral
matrix of $f$ in $f'$; if $\det n$ is a unit then $\mathcal O' \subseteq \mathcal O$. -/
theorem exists_det_gramTrd (hle : O ≤ O') :
    ∃ n : R, gramTrd (fun q => f q) = algebraMap R K n ^ 2 * gramTrd (fun q => f' q) ∧
      (IsUnit n → O' ≤ O) := by
  classical
  have hfO : ∀ q, f q ∈ O := basis_mem O f hf
  choose N hN using fun p q => (hf' (f q)).1 (hle (hfO q)) p
  have hcomb : (fun q => f q) = fun q => ∑ p, (Matrix.of N).map (algebraMap R K) p q • f' p := by
    funext q
    conv_lhs => rw [← f'.sum_repr (f q)]
    exact Finset.sum_congr rfl fun p _ => by rw [Matrix.map_apply, Matrix.of_apply, hN]
  refine ⟨(Matrix.of N).det, ?_, fun hu => ?_⟩
  · rw [hcomb, gramTrd_comb, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  · -- $f'_p = \sum_q (N^{-1})_{qp} f_q$ with $N^{-1}$ integral
    set n := Matrix.of N
    have hinv : n * n⁻¹ = 1 := Matrix.mul_nonsing_inv n hu
    have hf'p : ∀ p, f' p = ∑ q, algebraMap R K (n⁻¹ q p) • f q := fun p => by
      have : ∀ q, f q = ∑ r, algebraMap R K (n r q) • f' r := fun q => congrFun hcomb q
      simp_rw [this, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have h1 : ∀ r, ∑ q, algebraMap R K (n⁻¹ q p) * algebraMap R K (n r q) = algebraMap R K ((n * n⁻¹) r p) := by
        intro r; rw [Matrix.mul_apply, map_sum]; exact Finset.sum_congr rfl fun q _ => by rw [map_mul, mul_comm]
      simp_rw [← Finset.sum_smul, h1, hinv, Matrix.one_apply]
      simp
    intro x hx
    rw [← f'.sum_repr x]
    refine Subalgebra.sum_mem _ fun p _ => ?_
    obtain ⟨c, hc⟩ := (hf' x).1 hx p
    rw [← hc, algebraMap_smul, hf'p, Finset.smul_sum]
    refine Subalgebra.sum_mem _ fun q _ => ?_
    rw [← algebraMap_smul K, smul_smul, ← map_mul, algebraMap_smul]
    exact Subalgebra.smul_mem _ (hfO q) _

end Compare

section CompareLocal

open IsLocalRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {a b : K}

theorem exists_int_gramTrd {O' : Subalgebra R ℍ[K,a,b]} (hO' : IsOrder R K O') (f' : Module.Basis (Fin 4) K ℍ[K,a,b])
    (hf' : ∀ x, x ∈ O' ↔ ∀ i, IsInteger R (f'.repr x i)) :
    ∃ g : R, gramTrd (fun q => f' q) = algebraMap R K g := by
  have hb := basis_mem O' f' hf'
  choose g hg using fun p q => (isInteger_trd_nrd hO' (O'.mul_mem (hb p) (hb q))).1
  refine ⟨(Matrix.of g).det, ?_⟩
  rw [RingHom.map_det, gramTrd]
  congr 1
  ext p q
  exact (hg p q).symm

/-- **Split places: an order of unit discriminant is maximal** (Voight 2021, Theorem 15.5.5, "if", local form): if
$\mathcal O \subseteq \mathcal O'$ are orders over a discrete valuation ring and $d(\mathcal O) \in R^\times$, then
$\mathcal O' \subseteq \mathcal O$. -/
theorem le_of_isUnit_gramTrd {O O' : Subalgebra R ℍ[K,a,b]} (hO' : IsOrder R K O') (hle : O ≤ O')
    (f : Module.Basis (Fin 4) K ℍ[K,a,b]) (hf : ∀ x, x ∈ O ↔ ∀ i, IsInteger R (f.repr x i))
    {u : Rˣ} (hu : gramTrd (fun q => f q) = algebraMap R K u) : O' ≤ O := by
  obtain ⟨f', hf'⟩ := exists_basis_mem_iff hO'
  obtain ⟨n, hn, himp⟩ := exists_det_gramTrd f f' hf hf' hle
  obtain ⟨g, hg⟩ := exists_int_gramTrd hO' f' hf'
  refine himp ?_
  have h : (u : R) = n ^ 2 * g := IsFractionRing.injective R K (by rw [← hu, hn, hg, map_mul, map_pow])
  have h2 : IsUnit (n ^ 2 * g) := h ▸ u.isUnit
  exact (isUnit_pow_iff two_ne_zero).1 (isUnit_of_mul_isUnit_left h2)

/-- **Ramified places: an order of discriminant $\pi^2$ is maximal** (Voight 2021, Theorem 15.5.5, "if", local form):
if $B$ is a division algebra over the fraction field of a Henselian discrete valuation ring $R$ with finite residue
field, $\mathcal O \subseteq \mathcal O'$ are orders and $d(\mathcal O) \in \pi^2R^\times$, then $\mathcal O' \subseteq \mathcal O$
(every order lies in the valuation ring $V$, and $d(V) \in \pi^2R^\times$). -/
theorem le_of_gramTrd_ramified [HenselianLocalRing R] [Finite (ResidueField R)]
    (hdiv : ∀ x : ℍ[K,a,b], nrd x = 0 → x = 0) {V : Subalgebra R ℍ[K,a,b]} (hV : ∀ x, x ∈ V ↔ IsInteger R (nrd x))
    (hVo : IsOrder R K V) {π : R} (hπ : Irreducible π) {y : ℍ[K,a,b]} (hy : nrd y = algebraMap R K π)
    {O O' : Subalgebra R ℍ[K,a,b]} (hO' : IsOrder R K O') (hle : O ≤ O')
    (f : Module.Basis (Fin 4) K ℍ[K,a,b]) (hf : ∀ x, x ∈ O ↔ ∀ i, IsInteger R (f.repr x i))
    {u : Rˣ} (hu : gramTrd (fun q => f q) = algebraMap R K (π ^ 2 * u)) : O' ≤ O := by
  obtain ⟨f', hf'⟩ := exists_basis_mem_iff hO'
  obtain ⟨fV, hfV⟩ := exists_basis_mem_iff hVo
  obtain ⟨n, hn, himp⟩ := exists_det_gramTrd f f' hf hf' hle
  have hO'V : O' ≤ V := fun x hx => (hV x).2 ((isInteger_trd_nrd hO' hx).2)
  obtain ⟨m, hm, -⟩ := exists_det_gramTrd f' fV hf' hfV hO'V
  obtain ⟨uV, huV⟩ := exists_unit_gramTrd_ramified V hV hπ hy hdiv hVo.fg hVo.span fV hfV
  refine himp ?_
  have h : π ^ 2 * (u : R) = π ^ 2 * ((n * m) ^ 2 * uV) := IsFractionRing.injective R K (by
    rw [← hu, hn, hm, huV]; simp only [map_mul, map_pow]; ring)
  have h' := mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) h
  have h2 : IsUnit ((n * m) ^ 2 * uV) := h' ▸ u.isUnit
  have h3 := (isUnit_pow_iff two_ne_zero).1 (isUnit_of_mul_isUnit_left h2)
  exact isUnit_of_mul_isUnit_left h3

end CompareLocal

/-! ## The global theorem -/

section Global

open IsLocalRing QuadFormsKB.LocalDensity.NF QuadFormsKB.Voight.MassWave2

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

theorem gramTrd_complBasis (v : HeightOneSpectrum (𝓞 F)) {O : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsOrder (𝓞 F) F O) (e : Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O)) :
    gramTrd (fun q => complBasis (v := v) e hO q) =
      algebraMap F (v.adicCompletion F) (trdGramDet (fun i => (e i : QuatF F a b))) := by
  rw [gramTrd, trdGramDet, RingHom.map_det]
  congr 1
  ext p q
  simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, complBasis_apply, complBasisVec,
    ← map_mul, trd_complHom]

/-- **Voight 2021, Theorem 15.5.5, proved for every number field**: an order $\mathcal O \subseteq (a,b)_F$ with a
$\mathbb Z_F$-basis is maximal if and only if $\operatorname{discrd}(\mathcal O) = \mathfrak D =
\prod_{\mathfrak p \in \operatorname{Ram}_f B}\mathfrak p$ (`HasDiscrd`). Every class number, dyadic places included. -/
@[kb "voight2021" "Theorem 15.5.5, p. 249"]
theorem maximalIffDiscriminant (F : Type) [Field F] [NumberField F] : MaximalIffDiscriminant F := by
  classical
  intro a b ha hb O hO ⟨e⟩
  refine ⟨fun hmax e' => (maximalOrderDiscriminant F).disc_eq a b ha hb O hmax e', fun hD => ?_⟩
  refine ⟨hO, fun O' hO' hle => le_antisymm ?_ hle⟩
  obtain ⟨d, hd, hspan⟩ := hD e
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), localOrder (v := v) a b O' ≤ localOrder (v := v) a b O := by
    intro v
    set f := complBasis (v := v) e hO
    have hf := mem_localOrder_iff (v := v) e hO
    have hgram : gramTrd (fun q => f q) =
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ι v d) := by
      rw [gramTrd_complBasis, ← hd]; rfl
    have hI := congrArg (Ideal.map (ι v)) hspan
    rw [Ideal.map_span, Set.image_singleton, map_ι_ramIdeal_sq ha hb v] at hI
    obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.1 hI
    have hdu : ι v d = π v ^ (if v ∈ ramFin ha hb then 2 else 0) *
        ((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) := by
      rw [← hw, mul_assoc, Units.mul_inv, mul_one]
    have hle_v : localOrder (v := v) a b O ≤ localOrder (v := v) a b O' :=
      Submodule.span_mono (Set.image_mono hle)
    have hO'v := Gen.isOrder_localOrder_gen v hO'
    have hinj : Function.Injective (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) :=
      IsFractionRing.injective _ _
    by_cases hdiv : ∀ x : QuatV v a b, nrd x = 0 → x = 0
    · have hram : v ∈ ramFin ha hb := (mem_ramFin_iff ha hb).2 (Gen.isRamifiedAt_finite_iff.2 hdiv)
      simp only [hram, ↓reduceIte] at hdu
      have hπ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (π v) ≠ 0 :=
        (map_ne_zero_iff _ hinj).2 (irreducible_π v).ne_zero
      obtain ⟨y, hy⟩ := exists_nrd_eq_finite' (a := algebraMap (𝓞 F) F a) (b := algebraMap (𝓞 F) F b)
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha)
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb) v hπ0
      exact le_of_gramTrd_ramified hdiv (fun x => mem_valOrder hdiv)
        (isOrder_valOrder (R := v.adicCompletionIntegers F) hdiv (algebraMap_two_mul_ne_zero_nf ha hb))
        (irreducible_π v) hy hO'v hle_v f hf (by rw [hgram, hdu])
    · have hnram : v ∉ ramFin ha hb := by
        rw [mem_ramFin_iff, Gen.isRamifiedAt_finite_iff]; exact hdiv
      simp only [hnram, ↓reduceIte, pow_zero, one_mul] at hdu
      exact le_of_isUnit_gramTrd hO'v hle_v f hf (by rw [hgram, hdu])
  -- an element of $\mathcal O'$ has $v$-integral coordinates at every $v$
  intro x hx
  have : Submodule.IsLattice F (Subalgebra.toSubmodule O) := ⟨hO.fg, hO.span⟩
  set fb : Module.Basis (Fin 4) F (QuatF F a b) := e.extendOfIsLattice F
  have hfb : ∀ i, fb i = (e i : QuatF F a b) := fun i => Module.Basis.extendOfIsLattice_apply F e i
  have hint : ∀ i, ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = fb.repr x i := by
    intro i
    refine (HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v => ?_)
    have hxv := hloc v (mem_localOrder_of_mem a b hx)
    have hcoord := (mem_localOrder_iff (v := v) e hO _).1 hxv i
    have hrepr : (complBasis (v := v) e hO).repr (complHom v a b x) i =
        algebraMap F (v.adicCompletion F) (fb.repr x i) := by
      have hsum : complHom v a b x = ∑ j, algebraMap F (v.adicCompletion F) (fb.repr x j) •
          complBasis (v := v) e hO j := by
        conv_lhs => rw [← fb.sum_repr x]
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, algebraMap_smul, complBasis_apply, complBasisVec, hfb]
      rw [hsum, Module.Basis.repr_sum_self]
    rw [hrepr] at hcoord
    exact (LocFrame.isInteger_algebraMap_iff (v := v) _).1 hcoord
  choose c hc using hint
  rw [← fb.sum_repr x]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [← hc i, algebraMap_smul, hfb]
  exact Subalgebra.smul_mem _ (e i).2 _

end Global

end QuadFormsKB.Voight.Disc
