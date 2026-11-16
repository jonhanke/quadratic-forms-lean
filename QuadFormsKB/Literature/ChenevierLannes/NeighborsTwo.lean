/-
# Chenevier–Lannes, §3.2: the neighbour numbers $N_p(x, y)$ and the Hecke operator $T_p$ at $p = 2$

Propositions 3.2.2, 3.2.3, 3.2.4 and the self-adjointness of $T_p$ (§1.3) were proved in `Neighbors.lean` for odd $p$,
because the library's theorems on the class of a neighbour (`Siegel.Kneser.nbClass_spec`, `card_nbMats`,
`nbCount_mul_autCard`) assume $p \ne 2$: that hypothesis enters only through `sameGenus_of_neighbor` (a neighbour of a
form in the genus of $Q$ lies in the genus). For an even unimodular $L$ the genus claim is simpler and holds for every prime
$p$: the Gram form $Q'$ of a basis of a neighbour is integral, positive definite, of determinant $1$
($|\det g| = 1$, `Siegel.Kneser.abs_det_eq_one`), hence even unimodular, hence in the genus of $Q$
(`sameGenus_of_isEvenUnimodular`). This file re-proves the chain for even unimodular $Q$ and every prime $p$:

* `exists_gram_unimod`, `exists_hasClass_unimod`, `nbClass_spec_unimod`, `card_nbMats_unimod`, `nbCount_mul_autCard_unimod`;
* `sum_nbNum_all` (Prop. 3.2.2), `nbNum_mul_autCard_all` (Scholium 3.1.7, Prop. 3.2.3), `sum_nbNum_div_autCard_all`
  (Prop. 3.2.4), `heckeT_selfAdjoint_all` (§1.3): all primes $p$, including $2$.
-/
import QuadFormsKB.Literature.ChenevierLannes.NeighborCountTwoProof

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- **Every $p$-neighbour of an even unimodular lattice has an integral Gram form in the genus** (every prime $p$). -/
theorem exists_gram_unimod {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {L : Submodule ℤ (Fin n → ℚ)}
    (hL : L ∈ neighbors Q p) :
    ∃ g : Matrix (Fin n) (Fin n) ℚ, g.det ≠ 0 ∧ L = imgLat g ∧
      ∃ Q' : QuadForm ℤ n, (∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) ∧ SameGenus Q Q' := by
  have hdet := not_dvd_det hQ p
  have hN := (mem_neighbors_iff hdet).mp hL
  obtain ⟨v, hv, hv0, rfl⟩ := exists_eq_nbLat hdet hN
  have hpL0 : ∀ y : Fin n → ℤ, cv ((p : ℤ) • y) ∈ nbLat Q p v :=
    fun y => by rw [cv_mem_nbLat_iff hv, bZ_smul_left]; exact dvd_mul_right _ _
  obtain ⟨g, hg, hLg⟩ := exists_basis_of_le (p := p) (L := nbLat Q p v)
    (fun x hx => exists_eq_of_mem_nbLat hx) hpL0
  have hpL : ∀ y : Fin n → ℤ, cv ((p : ℤ) • y) ∈ imgLat g := fun y => by rw [← hLg]; exact hpL0 y
  rw [hLg] at hN ⊢
  obtain ⟨Q', hQ'⟩ := exists_gramForm (Q := Q) (g := g) fun c => hN.integral _ ⟨c, rfl⟩
  have habs := abs_det_eq_one hg hN hpL
  have hH := hessian_eq_conj hQ'
  have hdetH : Q'.hessian.det = Q.hessian.det := by
    have h1 := congrArg Matrix.det hH
    rw [det_mul, det_mul, det_transpose, det_map_eq, det_map_eq] at h1
    have hsq : g.det * g.det = 1 := by
      have := congrArg (· ^ 2) habs; simp only [sq_abs, one_pow] at this; rw [← sq]; exact this
    rw [show g.det * algebraMap ℤ ℚ Q.hessian.det * g.det = algebraMap ℤ ℚ Q.hessian.det by
      rw [mul_comm, ← mul_assoc, mul_comm _ g.det, hsq, one_mul]] at h1
    exact_mod_cast h1
  have hpos : IntQF.PosDef Q' := by
    intro x hx
    have h1 : Q'.evalIn ℚ (fun i => (x i : ℚ)) = (Q'.eval x : ℚ) := evalIn_intCast Q' x
    have h2 := hQ' (fun i => (x i : ℚ))
    have hgU : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
    set y : Fin n → ℚ := g *ᵥ (fun i => (x i : ℚ)) with hy
    have hy0 : y ≠ 0 := by
      intro h0
      have h3 : (fun i => (x i : ℚ)) = 0 := by
        have := congrArg (fun v => g⁻¹ *ᵥ v) h0
        simpa [hy, mulVec_mulVec, nonsing_inv_mul _ hgU] using this
      exact hx (funext fun i => by have := congrFun h3 i; simpa using this)
    have hyR : (fun i => (y i : ℝ)) ≠ 0 := by
      intro h0
      apply hy0
      funext i
      have := congrFun h0 i
      simpa using this
    have h4 := hQ.posDef.evalIn_real_pos _ hyR
    have h5 : ((Q.evalIn ℚ y : ℚ) : ℝ) = Q.evalIn ℝ (fun i => (y i : ℝ)) := by
      unfold QuadForm.evalIn
      rw [Rat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Rat.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [← h5, ← h2, h1] at h4
    have : (0 : ℚ) < (Q'.eval x : ℚ) := by exact_mod_cast h4
    exact_mod_cast this
  exact ⟨g, hg, rfl, Q', hQ', sameGenus_of_isEvenUnimodular hQ ⟨hpos, by rw [hdetH, hQ.det_one]⟩⟩

/-- Every $p$-neighbour of an even unimodular lattice has a class, in the genus (every prime $p$). -/
theorem exists_hasClass_unimod {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {L : Submodule ℤ (Fin n → ℚ)}
    (hL : L ∈ neighbors Q p) : ∃ c ∈ genusClasses Q, hasClass Q L c := by
  obtain ⟨g, hg, rfl, Q', hQ', hgen⟩ := exists_gram_unimod hQ hL
  set gU := Matrix.nonsingInvUnit g (isUnit_iff_ne_zero.mpr hg)
  have e : (gU : Matrix (Fin n) (Fin n) ℚ) = g := rfl
  exact ⟨classOf Q', classOf_mem_genusClasses_iff.mpr hgen, gU, by rw [e], Q', rfl, by rw [e]; exact hQ'⟩

theorem nbClass_spec_unimod {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) {L : Submodule ℤ (Fin n → ℚ)}
    (hL : L ∈ neighbors Q p) :
    nbClass Q L ∈ genusClasses Q ∧ ∀ c, hasClass Q L c ↔ nbClass Q L = c := by
  obtain ⟨c, hc, hcl⟩ := exists_hasClass_unimod hQ hL
  have h : ∃ c, hasClass Q L c := ⟨c, hcl⟩
  have e : nbClass Q L = c := by
    classical
    unfold nbClass; rw [dif_pos h]; exact hasClass_unique h.choose_spec hcl
  refine ⟨e ▸ hc, fun c' => ⟨fun h' => e.trans (hasClass_unique hcl h'), fun h' => ?_⟩⟩
  rw [← h', e]; exact hcl

/-- **Counting neighbour matrices** (even unimodular $Q$, every prime $p$):
$\#\,\mathrm{nbMats}(Q, Q') = N(Q, [Q'])\cdot|\mathrm{Aut}(Q')|$. -/
theorem card_nbMats_unimod {Q Q' : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (hQ' : IntQF.PosDef Q') :
    Nat.card (nbMats Q Q' p) = nbCount Q p (classOf Q') * Nat.card (Aut Q') := by
  classical
  have hdet := not_dvd_det hQ p
  set S := (neighbors Q p).filter fun L => nbClass Q L = classOf Q'
  let F : S → Type := fun L => {g : GL (Fin n) ℚ // imgLat (g : Matrix (Fin n) (Fin n) ℚ) = L.1 ∧
      ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ ((g : Matrix (Fin n) (Fin n) ℚ) *ᵥ x)}
  have hS : ∀ L : S, hasClass Q L.1 (classOf Q') := by
    intro L
    have hL := (Finset.mem_filter.mp L.2)
    exact ((nbClass_spec_unimod hQ hL.1).2 _).mpr hL.2
  have hF : ∀ L : S, Nat.card (F L) = Nat.card (Aut Q') := fun L => card_bases_eq (hS L)
  haveI : Finite (Aut Q') := hQ'.finite_aut
  haveI : ∀ L : S, Finite (F L) := fun L => by
    have h := hF L
    exact Nat.finite_of_card_ne_zero (by rw [h]; exact (hQ'.card_aut_pos).ne')
  have e : nbMats Q Q' p ≃ Σ L : S, F L :=
    { toFun := fun g => ⟨⟨imgLat (g.1 : Matrix (Fin n) (Fin n) ℚ), Finset.mem_filter.mpr
          ⟨(mem_neighbors_iff hdet).mpr g.2.1,
            ((nbClass_spec_unimod hQ ((mem_neighbors_iff hdet).mpr g.2.1)).2 _).mp
              ⟨g.1, rfl, Q', rfl, g.2.2⟩⟩⟩, ⟨g.1, rfl, g.2.2⟩⟩
      invFun := fun x => ⟨x.2.1, by
          refine ⟨?_, x.2.2.2⟩
          rw [x.2.2.1]
          exact (mem_neighbors_iff hdet).mp (Finset.mem_filter.mp x.1.2).1⟩
      left_inv := fun g => rfl
      right_inv := fun x => by
        obtain ⟨⟨L, hL⟩, g, hgL, hgQ⟩ := x
        exact Sigma.subtype_ext (Subtype.ext hgL) rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [hF]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  rfl

/-- **Every neighbour is counted once** (even unimodular $Q$, every prime $p$). -/
theorem sum_nbCount_unimod {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (T : Finset (QClass n))
    (hT : ∀ c, c ∈ T ↔ c ∈ genusClasses Q) : ∑ c ∈ T, nbCount Q p c = (neighbors Q p).card := by
  classical
  symm
  unfold nbCount
  exact Finset.card_eq_sum_card_fiberwise fun L hL => (hT _).mpr (nbClass_spec_unimod hQ hL).1

/-- **Symmetry of the neighbour numbers** (every prime $p$, including $2$):
$N(Q, [Q'])\,|\mathrm{Aut}(Q')| = N(Q', [Q])\,|\mathrm{Aut}(Q)|$ for even unimodular $Q, Q'$. -/
theorem nbCount_mul_autCard_unimod {Q Q' : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (hQ' : IsEvenUnimodular Q') :
    nbCount Q p (classOf Q') * Nat.card (Aut Q') = nbCount Q' p (classOf Q) * Nat.card (Aut Q) := by
  rw [← card_nbMats_unimod hQ hQ'.posDef, ← card_nbMats_unimod hQ' hQ.posDef, card_nbMats_symm]

/-- **The number of $p$-neighbours, every prime** (Prop.-Def. 3.2.1): $c_n(p)$ for odd $p$ (`card_neighbors_eq_cn`) and
for $p = 2$ (`card_neighbors_eq_cn_two`). -/
theorem card_neighbors_eq_cn_all {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) (hn : 0 < n) :
    (neighbors Q p).card = cn n p := by
  by_cases hp2 : p = 2
  · subst hp2; exact card_neighbors_eq_cn_two hQ hn
  · exact card_neighbors_eq_cn hQ hn hp2

/-- **Proposition 3.2.2 for every prime $p$** (Chenevier–Lannes, p. 56; including $p = 2$): for every $x \in X_n$
($n > 0$), $\sum_{y \in X_n} N_p(x, y) = c_n(p)$. Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 3.2.2, p. 56 (every p)"]
theorem sum_nbNum_all (hn : 0 < n) {x : QClass n} (hx : x ∈ classSet n) :
    ∑ y ∈ (classSet_finite n).toFinset, nbNum p x y = cn n p := by
  have hQ := out_isEvenUnimodular hx
  unfold nbNum
  rw [sum_nbCount_unimod hQ _ (fun c => by rw [Set.Finite.mem_toFinset, classSet_eq_genusClasses hQ]),
    card_neighbors_eq_cn_all hQ hn]

/-- **Scholium 3.1.7 and Proposition 3.2.3 for every prime $p$** (pp. 49, 56; including $p = 2$):
$N_p(x, y)\,|O(y)| = N_p(y, x)\,|O(x)|$ for $x, y \in X_n$. Unconditional. -/
@[kb "chenevierlannes2019" "Scholium 3.1.7, p. 49; Prop. 3.2.3, p. 56 (every p)"]
theorem nbNum_mul_autCard_all {x y : QClass n} (hx : x ∈ classSet n) (hy : y ∈ classSet n) :
    nbNum p x y * y.autCard = nbNum p y x * x.autCard := by
  have hQ := out_isEvenUnimodular hx
  have hQ' := out_isEvenUnimodular hy
  have h := nbCount_mul_autCard_unimod (p := p) hQ hQ'
  have ex : classOf (Quotient.out (s := intSetoid n) x) = x := Quotient.out_eq _
  have ey : classOf (Quotient.out (s := intSetoid n) y) = y := Quotient.out_eq _
  rw [ex, ey] at h
  unfold nbNum
  rw [autCard_eq_out x, autCard_eq_out y]
  exact h

/-- **Proposition 3.2.4 for every prime $p$** (p. 56; including $p = 2$): $\sum_{x \in X_n} N_p(x, y)/|O(x)| =
c_n(p)/|O(y)|$ for $y \in X_n$ ($n > 0$). Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 3.2.4, p. 56 (every p)"]
theorem sum_nbNum_div_autCard_all (hn : 0 < n) {y : QClass n} (hy : y ∈ classSet n) :
    ∑ x ∈ (classSet_finite n).toFinset, (nbNum p x y : ℚ) / x.autCard = cn n p / y.autCard := by
  have hpos : ∀ x ∈ classSet n, (x.autCard : ℚ) ≠ 0 := fun x hx => by
    have h := (out_isEvenUnimodular hx).posDef.card_aut_pos
    rw [autCard_eq_out x]
    exact_mod_cast h.ne'
  calc ∑ x ∈ (classSet_finite n).toFinset, (nbNum p x y : ℚ) / x.autCard
      = ∑ x ∈ (classSet_finite n).toFinset, (nbNum p y x : ℚ) / y.autCard :=
        Finset.sum_congr rfl fun x hx => by
          have hx' := (Set.Finite.mem_toFinset _).mp hx
          rw [div_eq_div_iff (hpos x hx') (hpos y hy)]
          exact_mod_cast nbNum_mul_autCard_all hx' hy
    _ = (∑ x ∈ (classSet_finite n).toFinset, (nbNum p y x : ℚ)) / y.autCard := by rw [Finset.sum_div]
    _ = cn n p / y.autCard := by rw [← sum_nbNum_all hn hy]; push_cast; rfl

/-- **The Hecke operator $T_p$ is self-adjoint, every prime $p$** (Chenevier–Lannes, §1.3, p. 6; Prop. 3.2.3):
$\sum_x (T_pf)(x)\,g(x)/|O(x)| = \sum_x f(x)\,(T_pg)(x)/|O(x)|$ for $f, g : X_n \to K$, $K$ a field of characteristic $0$.
Unconditional; this removes the oddness hypothesis of `heckeT_selfAdjoint`. -/
@[kb "chenevierlannes2019" "Prop. 3.2.3, p. 56; §1.3, p. 6 (T_p self-adjoint, every p)"]
theorem heckeT_selfAdjoint_all {K : Type*} [Field K] [CharZero K] (f g : QClass n → K) :
    ∑ x ∈ (classSet_finite n).toFinset, heckeT p f x * g x / x.autCard =
      ∑ x ∈ (classSet_finite n).toFinset, f x * heckeT p g x / x.autCard := by
  have hpos : ∀ x ∈ classSet n, (x.autCard : K) ≠ 0 := fun x hx => by
    have h := (out_isEvenUnimodular hx).posDef.card_aut_pos
    rw [autCard_eq_out x]
    exact_mod_cast h.ne'
  simp only [heckeT, nsmul_eq_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o ho => Finset.sum_congr rfl fun i hi => ?_
  have ho' := (Set.Finite.mem_toFinset _).mp ho
  have hi' := (Set.Finite.mem_toFinset _).mp hi
  have h := nbNum_mul_autCard_all (p := p) ho' hi'
  have hK : (nbNum p o i : K) * i.autCard = nbNum p i o * o.autCard := by exact_mod_cast h
  rw [div_eq_div_iff (hpos o ho') (hpos i hi')]
  linear_combination (f i * g o) * hK

end QuadFormsKB.ChenevierLannes
