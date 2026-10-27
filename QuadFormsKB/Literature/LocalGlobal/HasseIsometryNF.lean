/-
# Isometry invariance of the Hasse invariants at every place of a number field

Let $F$ be a number field, $v$ a place of $F$ (`NFPlace F`: real, complex, or a nonzero prime $\mathfrak p$ of
$\mathcal O_F$, **dyadic included**) and $F_v$ the completion. For $a_i, b_i \in F^\times$:

* `NFPlace.hasseSerre_isometric`: if $\langle a_0,\dots,a_{n-1}\rangle \cong \langle b_0,\dots,b_{n-1}\rangle$ over
  $F_v$, then Serre's $\varepsilon_v(\langle a\rangle) = \prod_{i<j}(a_i,a_j)_v$ equals $\varepsilon_v(\langle b\rangle)$
  (Serre IV §2.1, there over $\mathbb{Q}_p$ and $\mathbb{R}$; O'Meara 58:2, p. 151, the Hasse algebra is well defined, with §63B, p. 167, over $F_{\mathfrak p}$).
* The same for Cassels' $c_v$ and Lam's $s_v$ (the same product), and, with the invariance of $(d,d)_v$
  (`NFPlace.hilbert_diagDet_self_isometric`), for O'Meara's $S_v$ and Hasse's $\alpha_v$ (Shimura §28.13)
  (`NFPlace.hasseOMeara_isometric`, `NFPlace.hasseShimura_isometric`), all unconditional.

**Route.**

* *Finite places $\mathfrak p$, dyadic or not.* $F_{\mathfrak p}$ satisfies the three Hilbert-symbol axioms
  `PadicClass.LocalHilbertField` (`localHilbertField_adicCompletion`): bimultiplicativity
  (`HN.hilbertSymbol_mul_left_finite_nf`), nondegeneracy (`SqDual.hilbCl_nondeg_fin`), and isotropy of every
  nondegenerate diagonal form of rank $5$ (`LocalRankFive.isotropic_diag_five`, proved through quaternion norms at every
  finite place, $\mathfrak p \mid 2$ included). The abstract classification argument of `PadicClassification.lean`
  (`PadicClass.hasseVec_eq_of_isometric`: rank $\le 3$ by Serre's Thm. 6, rank $\ge 4$ by a common represented value
  and Witt cancellation) then applies verbatim. So the gap noted in `HasseConventionsNF.lean` (the axiom
  `isotropic_five` at a dyadic $F_{\mathfrak p}$) was already closed by the Tamagawa track.
* *Real places.* $F_w \cong \mathbb{R}$ (`InfinitePlace.Completion.ringEquivRealOfIsReal`). The Hilbert symbol and
  isometry transport along a ring isomorphism (`hilbertSymbol_ringEquiv`, `isometricIn_ringEquiv`); over $\mathbb{R}$,
  $\varepsilon = (-1)^{r(r-1)/2}$ for $r$ negative entries (`hasseVec_real_eq`) and $r$ is an isometry invariant by
  Sylvester's law of inertia (Mathlib `QuadraticForm.sigNeg_of_equiv_weightedSumSquares`).
* *Complex places.* Every Hilbert symbol over $F_w \cong \mathbb{C}$ is $1$, so $\varepsilon_w = 1$.

*Related work.* Tau Ceti's `TauCeti.RegularFormClass.localHasse_congr` (`NumberTheory/LocalField/QuadraticForm/Hasse.lean`)
is the analogue over an abstract nonarchimedean local field with `Invertible (2 : K)`, which (in characteristic $0$)
includes the dyadic fields; it is stated for the $i<j$ invariant on isometry classes. What is added here: the
statement at every place of a number field, archimedean places included, for forms with entries in $F$, in all five
literature conventions, obtained from the repository's own local inputs (no outside code).
-/
import QuadFormsKB.Literature.LocalGlobal.HasseConventionsNF
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Tamagawa.LocalRankFive

open NumberField IsDedekindDomain

namespace QuadFormsKB

open Finset PadicClass Matrix

variable {n : ℕ}

namespace HasseIsoNF

/-! ### Transport along a ring isomorphism -/

/-- The Hilbert symbol is invariant under a ring isomorphism $e : K \cong L$: $(e a, e b)_L = (a, b)_K$. -/
theorem hilbertSymbol_ringEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (a b : K) :
    hilbertSymbol L (e a) (e b) = hilbertSymbol K a b := by
  unfold hilbertSymbol
  congr 1
  apply propext
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨e.symm x, e.symm y, e.symm z, ?_, ?_⟩
    · intro h0
      apply hne
      simp only [Prod.mk_eq_zero, map_eq_zero_iff _ e.symm.injective] at h0 ⊢
      exact h0
    · apply e.injective
      simp [h]
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨e x, e y, e z, ?_, ?_⟩
    · intro h0
      apply hne
      simp only [Prod.mk_eq_zero, map_eq_zero_iff _ e.injective] at h0 ⊢
      exact h0
    · rw [← map_pow, h]; simp

theorem hasseVec_ringEquiv {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] (e : K ≃+* L)
    (a : Fin n → K) : hasseVec (fun i => e (a i)) = hasseVec a := by
  unfold hasseVec
  simp only [hilbertSymbol_ringEquiv]

/-- Isometry of diagonal forms transports along a ring isomorphism $e : K \cong L$. -/
theorem isometricIn_ringEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) {a b : Fin n → K}
    (h : (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    (QuadForm.diag fun i => e (a i)).IsometricIn L (QuadForm.diag fun i => e (b i)) := by
  obtain ⟨P, hP, hPx⟩ := h
  refine ⟨P.map e, ?_, fun y => ?_⟩
  · have hd : (P.map e).det = e P.det := by
      rw [show e P.det = (e : K →+* L) P.det from rfl, RingHom.map_det]; rfl
    rw [hd]; exact hP.map e
  · set x : Fin n → K := fun i => e.symm (y i) with hx
    have hy : y = fun i => e (x i) := by funext i; simp [hx]
    have hm : P.map e *ᵥ y = fun i => e ((P *ᵥ x) i) := by
      funext i
      rw [hy]; exact (RingHom.map_mulVec (e : K →+* L) P x i).symm
    have := hPx x
    simp only [QuadForm.evalIn_diag, Algebra.algebraMap_self, RingHom.id_apply] at this ⊢
    rw [hm]
    calc ∑ i, e (a i) * e ((P *ᵥ x) i) ^ 2 = e (∑ i, a i * (P *ᵥ x) i ^ 2) := by
          simp [map_sum, map_mul, map_pow]
      _ = e (∑ i, b i * x i ^ 2) := by rw [this]
      _ = ∑ i, e (b i) * y i ^ 2 := by rw [hy]; simp [map_sum, map_mul, map_pow]

/-! ### Real Hasse invariant: Sylvester's law -/

/-- The number of pairs $i<j$ of negative entries of a real vector. Internal. -/
noncomputable def negPairsR (a : Fin n → ℝ) : ℕ :=
  ∑ i, ∑ j, if i < j then (if a i < 0 then 1 else 0) * (if a j < 0 then 1 else 0) else 0

/-- The number of negative entries of a real vector. Internal. -/
noncomputable def negCountR (a : Fin n → ℝ) : ℕ := ∑ i, if a i < 0 then 1 else 0

theorem two_negPairsR_add (a : Fin n → ℝ) : 2 * negPairsR a + negCountR a = negCountR a ^ 2 := by
  set e : Fin n → ℕ := fun i => if a i < 0 then 1 else 0 with he
  have h1 : negCountR a = ∑ i, e i := rfl
  have h2 : negPairsR a = ∑ i, ∑ j, if i < j then e i * e j else 0 := rfl
  have hB : (∑ i, ∑ j, if j < i then e i * e j else 0) = negPairsR a := by
    rw [h2, sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  have hD : (∑ i, ∑ j, if i = j then e i * e j else 0) = negCountR a := by
    rw [h1]
    refine sum_congr rfl fun i _ => ?_
    have : e i * e i = e i := by simp only [he]; split_ifs <;> simp
    simp [this]
  have hsq : negCountR a ^ 2 = ∑ i, ∑ j, e i * e j := by
    rw [h1, sq, sum_mul_sum]
  have htri : (∑ i, ∑ j, e i * e j) =
      (∑ i, ∑ j, if i < j then e i * e j else 0) + (∑ i, ∑ j, if j < i then e i * e j else 0) +
        ∑ i, ∑ j, if i = j then e i * e j else 0 := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt, h.ne]
    · simp [h]
    · simp [h, h.not_gt, h.ne']
  rw [hsq, htri, hB, hD, ← h2]
  ring

theorem hilbertSymbol_real_eq (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    hilbertSymbol ℝ x y = if x < 0 ∧ y < 0 then -1 else 1 := by
  have H := hilbertSymbol_real x y hx hy
  split_ifs with hc
  · exact H.mpr hc
  · rcases hs_pm (K := ℝ) x y with h | h
    · exact h
    · exact absurd (H.mp h) hc

/-- Over $\mathbb{R}$, $\varepsilon(\langle a\rangle) = (-1)^{N}$ with $N$ the number of pairs $i<j$ of negative
entries. -/
theorem hasseVec_real_eq (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) : hasseVec a = (-1) ^ negPairsR a := by
  unfold hasseVec negPairsR
  have key : ∀ i j : Fin n, (if i < j then hilbertSymbol ℝ (a i) (a j) else 1) =
      (-1 : ℤ) ^ (if i < j then (if a i < 0 then 1 else 0) * (if a j < 0 then 1 else 0) else 0) := by
    intro i j
    by_cases hij : i < j
    · simp only [hij, ite_true, hilbertSymbol_real_eq _ _ (ha i) (ha j)]
      by_cases h1 : a i < 0 <;> by_cases h2 : a j < 0 <;> simp [h1, h2]
    · simp [hij]
  calc _ = ∏ i, ∏ j, (-1 : ℤ) ^ (if i < j then (if a i < 0 then 1 else 0) *
        (if a j < 0 then 1 else 0) else 0) :=
        prod_congr rfl fun i _ => prod_congr rfl fun j _ => key i j
    _ = _ := by simp_rw [prod_pow_eq_pow_sum]

/-- **Sylvester's law** for real diagonal forms: isometric forms have the same number of negative entries. -/
theorem negCountR_eq_of_isometric (a b : Fin n → ℝ)
    (h : (QuadForm.diag a).IsometricIn ℝ (QuadForm.diag b)) : negCountR a = negCountR b := by
  have tq : ∀ c : Fin n → ℝ, (QuadForm.diag c).toQuadraticFormIn ℝ =
      QuadraticMap.weightedSumSquares ℝ c := by
    intro c
    ext x
    rw [QuadForm.toQuadraticFormIn_apply, QuadForm.evalIn_diag, QuadraticMap.weightedSumSquares_apply]
    simp [sq]
  have cnt : ∀ c : Fin n → ℝ, negCountR c = {i | c i < 0}.ncard := by
    intro c
    have : {i | c i < 0} = ↑(univ.filter fun i => c i < 0) := by
      ext i; simp
    rw [this, Set.ncard_coe_finset, Finset.card_filter]
    rfl
  have e := (QuadForm.isometricIn_iff_equivalent ℝ (QuadForm.diag a) (QuadForm.diag b)).mp h
  have sa := QuadraticForm.sigNeg_of_equiv_weightedSumSquares (𝕜 := ℝ)
    (Q := (QuadForm.diag a).toQuadraticFormIn ℝ) (w := a) (by rw [tq]; exact QuadraticMap.Equivalent.refl _)
  have sb := QuadraticForm.sigNeg_of_equiv_weightedSumSquares (𝕜 := ℝ)
    (Q := (QuadForm.diag b).toQuadraticFormIn ℝ) (w := b) (by rw [tq]; exact QuadraticMap.Equivalent.refl _)
  rw [← cnt] at sa sb
  rw [← sa, ← sb]
  exact e.sigNeg_eq.symm

/-- **Isometry invariance of the Hasse invariant over $\mathbb{R}$** (Serre IV §2.1, from Sylvester's law). -/
theorem hasseVec_real_isometric (a b : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : (QuadForm.diag a).IsometricIn ℝ (QuadForm.diag b)) : hasseVec a = hasseVec b := by
  rw [hasseVec_real_eq a ha, hasseVec_real_eq b hb]
  have h1 := two_negPairsR_add a
  have h2 := two_negPairsR_add b
  rw [negCountR_eq_of_isometric a b h] at h1
  have : negPairsR a = negPairsR b := by omega
  rw [this]

/-! ### The local fields $F_v$ -/

variable {F : Type} [Field F] [NumberField F]

/-- **Every completion $F_{\mathfrak p}$ at a finite place, dyadic included, satisfies the local Hilbert-symbol
axioms** used by the abstract classification (`PadicClass.LocalHilbertField`): bimultiplicativity, nondegeneracy,
and isotropy of nondegenerate rank-$5$ diagonal forms (O'Meara §63B, pp. 164–167: 63:11, 63:13 and the homomorphism $\alpha \mapsto (\alpha,\beta)_\mathfrak p$ on p. 167;
63:19, p. 170). -/
@[kb "omeara1963" "§63B, p. 166 (bimultiplicativity); 63:13, p. 166 (non-degeneracy); §63C, 63:19, p. 170"]
theorem localHilbertField_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    LocalHilbertField (v.adicCompletion F) where
  mul_left := fun a a' b ha ha' hb => HN.hilbertSymbol_mul_left_finite_nf v a a' b ha ha' hb
  exists_neg_one := fun a ha hns => by
    set d : (v.adicCompletion F)ˣ := Units.mk0 a ha
    have hy : (QuotientGroup.mk d : SqDual.SqCl (v.adicCompletion F)) ≠ 1 := fun h1 =>
      hns ((SqDual.mk_eq_one_iff_isSquare _ d).mp h1)
    obtain ⟨x, hx⟩ := SqDual.hilbCl_nondeg_fin v _ hy
    induction x using QuotientGroup.induction_on with
    | H u =>
      refine ⟨u, u.ne_zero, ?_⟩
      rw [SqDual.hilbCl_mk, hilbertSymbol_comm] at hx
      exact hx
  isotropic_five := LocalRankFive.isotropic_diag_five v

omit [NumberField F] in
/-- At a complex place every Hilbert symbol is $1$. -/
theorem hilbertSymbol_complex_place {w : InfinitePlace F} (hw : w.IsComplex) (x y : w.Completion) :
    hilbertSymbol w.Completion x y = 1 := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  rw [← hilbertSymbol_ringEquiv e]
  unfold hilbertSymbol
  split_ifs with hc
  · rfl
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e x) (n := 2) (by norm_num)
    exact absurd ⟨1, 0, s, by simp, by simp [hs]⟩ hc

end HasseIsoNF

open HasseIsoNF

namespace NFPlace

variable {F : Type} [Field F] [NumberField F]

/-- **Isometry invariance of Serre's $\varepsilon_v$ at every place of a number field $F$:** if
$\langle a_0,\dots,a_{n-1}\rangle$ and $\langle b_0,\dots,b_{n-1}\rangle$ ($a_i, b_i \in F^\times$) are isometric over
the completion $F_v$, then $\prod_{i<j}(a_i,a_j)_v = \prod_{i<j}(b_i,b_j)_v$. Every place: real, complex, and finite
including dyadic. (Serre IV §2.1 states it over $\mathbb{Q}_p$ and $\mathbb{R}$; over $F_{\mathfrak p}$ it is
O'Meara 58:2, p. 151, the Hasse algebra is well defined, with §63B, p. 167.) -/
@[kb "serre1973" "Ch. IV, §2.1, Thm. (p. 36) [locator unverified]"]
theorem hasseSerre_isometric (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : v.atPlace fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    v.hasseSerre a = v.hasseSerre b := by
  cases v with
  | finite v =>
    have h' := (isometricIn_cast a b).mp h
    have e : ∀ c : Fin n → F, (NFPlace.finite v).hasseSerre c =
        hasseVec (fun i => algebraMap F (v.adicCompletion F) (c i)) := fun c => rfl
    rw [e, e]
    exact hasseVec_eq_of_isometric (localHilbertField_adicCompletion v) n _ _
      (fun i => (map_ne_zero _).mpr (ha i)) (fun i => (map_ne_zero _).mpr (hb i)) h'
  | infinite w =>
    have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    have h' := (isometricIn_cast a b).mp h
    have e : ∀ c : Fin n → F, (NFPlace.infinite w).hasseSerre c =
        hasseVec (fun i => algebraMap F w.Completion (c i)) := fun c => rfl
    rw [e, e]
    rcases w.isReal_or_isComplex with hw | hw
    · let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      rw [← hasseVec_ringEquiv φ, ← hasseVec_ringEquiv φ (fun i => algebraMap F w.Completion (b i))]
      exact hasseVec_real_isometric _ _
        (fun i => (map_ne_zero _).mpr ((map_ne_zero _).mpr (ha i)))
        (fun i => (map_ne_zero _).mpr ((map_ne_zero _).mpr (hb i))) (isometricIn_ringEquiv φ h')
    · simp [hasseVec, hilbertSymbol_complex_place hw]

/-- **Isometry invariance of Cassels' $c_v$** over $F_v$ (= Serre's $\varepsilon_v$). -/
@[kb "cassels1978" "Ch. 4, Lemma 2.2, p. 57, and Cor. 1, p. 58 (over ℚ_p; over F_v derived)"]
theorem hasseCassels_isometric (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : v.atPlace fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    v.hasseCassels a = v.hasseCassels b :=
  hasseSerre_isometric v a b ha hb h

/-- **Isometry invariance of Lam's $s_v$** over $F_v$ (= Serre's $\varepsilon_v$). -/
@[kb "lam2005" "Ch. V, §3 [unverified]"]
theorem hasseLam_isometric (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : v.atPlace fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    v.hasseLam a = v.hasseLam b :=
  hasseSerre_isometric v a b ha hb h

/-- **Isometry invariance of O'Meara's Hasse symbol $S_v$** at every place of $F$, unconditional: from
`hasseSerre_isometric` and the invariance of $(d,d)_v$ via $S_v = \varepsilon_v\,(d,d)_v$. -/
@[kb "omeara1963" "§63B, p. 167 (S_p V independent of the splitting)"]
theorem hasseOMeara_isometric (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : v.atPlace fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    v.hasseOMeara a = v.hasseOMeara b :=
  hasseOMeara_isometric_of_hasseSerre v a b ha hb h (hasseSerre_isometric v a b ha hb h)

/-- **Isometry invariance of Hasse's $\alpha_v$ (Shimura §28.13)** at every place of $F$ (= O'Meara's $S_v$). -/
@[kb "shimura2010" "§28.13, p. 160"]
theorem hasseShimura_isometric (v : NFPlace F) (a b : Fin n → F) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : v.atPlace fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b)) :
    v.hasseShimura a = v.hasseShimura b :=
  hasseOMeara_isometric v a b ha hb h

end NFPlace

end QuadFormsKB
