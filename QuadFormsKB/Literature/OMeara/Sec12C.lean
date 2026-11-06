/-
# O'Meara §12: complete archimedean fields in general (12:2, 12:3, 12:4, 12:5, 12:7, 12:13; 14:1 archimedean case)

**Setting.** As in `Sec12A.lean`, `Sec12B.lean`: a valuation on a field $F$ is a Mathlib `AbsoluteValue F ℝ`; it is
archimedean when it is not non-archimedean (`¬ IsNonarchimedean v`), and $F$ is complete under it when
`CompleteSpace (WithAbs v)`.

**Proves**
* `exists_ordinary_rpow` (**12:5**, existence; with **12:6**): every archimedean valuation $v$ is
  $|\ |^{\varrho}$ ($0 < \varrho \le 1$) for an ordinary absolute value $|\ |$ ($|m| = m$ on the natural numbers) in
  its spot. `Sec12A.lean` has the uniqueness;
* `complete_archimedean_rpow` and `complete_archimedean_isTopologicalIso` (**12:4**): a complete archimedean field is
  isomorphic to $\mathbb R$ or $\mathbb C$ by an isomorphism $\varphi$ with $v = |\varphi\,\cdot|^{\varrho}$, in
  particular by a topological isomorphism. `Sec12B.lean` has the case $\varrho = 1$;
* `isSquare_one_add` (**12:2**);
* `exists_prolongation_adjoin_sqrt_neg_one` (**12:3**);
* `under_bijective` (**12:7**);
* `rat_archimedean_real_spot` (**12:13**);
* `prolongation_formula_archimedean` (**14:1**, archimedean case; the non-archimedean case is `prolongation_formula`
  in `Sec14A.lean`).

**Proof route.** O'Meara proves 12:2 and 12:3 first (by an iteration and by the norm $|N\alpha|^{1/2}$) and deduces 12:4
from them. Here 12:4 is proved first: by 12:1 the valuation is $|\ |_\infty^{\varrho}$ on the rational numbers, the
power $v^{1/\varrho}$ is again a valuation (the triangle law follows from the bound on sums of $N$ terms, Artin's
argument), it is ordinary, and the ordinary case is `complete_ordinary_isReal_or_isComplex` (Mathlib's
Gelfand–Mazur theorem). Then 12:2, 12:3 and the archimedean case of 14:1 are read off in $\mathbb R$ and $\mathbb C$.
-/
import QuadFormsKB.Citation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import QuadFormsKB.Literature.OMeara.Sec11C
import QuadFormsKB.Literature.OMeara.Sec11E
import QuadFormsKB.Literature.OMeara.Sec12B

open IntermediateField Filter Topology

namespace QuadFormsKB.OMeara

universe u
variable {F : Type u} [Field F]

private theorem charZero_of_arch (v : AbsoluteValue F ℝ) (hv : ¬ IsNonarchimedean v) : CharZero F := by
  by_contra h
  apply hv
  rw [isNonarchimedean_iff_natCast_bounded]
  obtain ⟨p, hp⟩ := CharP.exists F
  have hp0 : p ≠ 0 := fun h0 => h (by subst h0; exact CharP.charP_to_charZero F)
  have := hp
  refine ⟨∑ i ∈ Finset.range p, v (i : F), fun n => ?_⟩
  have : (n : F) = ((n % p : ℕ) : F) := by
    conv_lhs => rw [← Nat.mod_add_div n p]
    simp [CharP.cast_eq_zero]
  rw [this]
  exact Finset.single_le_sum (f := fun i : ℕ => v (i : F)) (fun i _ => v.nonneg _)
    (Finset.mem_range.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero hp0)))

private theorem pow_bound (v : AbsoluteValue F ℝ) {c : ℝ} (hc : 0 < c)
    (hnat : ∀ n : ℕ, v (n : F) = (n : ℝ) ^ c)
    (x y : F) (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : v x = a ^ c) (hb : v y = b ^ c) (N : ℕ) :
    v (x + y) ^ N ≤ (N + 1) * ((a + b) ^ c) ^ N := by
  rw [← map_pow, add_pow]
  refine (v.sum_le _ _).trans ?_
  have : ∀ m ∈ Finset.range (N + 1),
      v (x ^ m * y ^ (N - m) * (N.choose m : F)) ≤ ((a + b) ^ c) ^ N := by
    intro m hm
    have h1 : a ^ m * b ^ (N - m) * (N.choose m : ℝ) ≤ (a + b) ^ N := by
      rw [add_pow]
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun m => a ^ m * b ^ (N - m) *
        (N.choose m : ℝ)) (fun i _ => by positivity) hm)
      rfl
    rw [map_mul, map_mul, map_pow, map_pow, hnat, ha, hb, Real.rpow_pow_comm ha0, Real.rpow_pow_comm hb0,
      Real.rpow_pow_comm (by positivity), ← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h1 hc.le
  calc _ ≤ ∑ m ∈ Finset.range (N + 1), ((a + b) ^ c) ^ N := Finset.sum_le_sum this
    _ = _ := by simp

private theorem le_of_pow_bound {t K : ℝ} (_ht : 0 ≤ t) (hK : 0 ≤ K)
    (h : ∀ N : ℕ, t ^ N ≤ (N + 1) * K ^ N) : t ≤ K := by
  refine le_of_forall_gt_imp_ge_of_dense fun K' hK' => ?_
  have hK'0 : 0 < K' := lt_of_le_of_lt hK hK'
  by_contra htK
  rw [not_le] at htK
  have hr : 1 < t / K' := (one_lt_div hK'0).2 htK
  have := (tendsto_pow_const_div_const_pow_of_one_lt 1 hr).eventually
    (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
  obtain ⟨N, hN, hN1⟩ := ((this.and (eventually_ge_atTop 1))).exists
  have hrp : 0 < (t / K') ^ N := pow_pos (by positivity) N
  rw [pow_one, div_lt_iff₀ hrp] at hN
  have h2 : (t / K') ^ N ≤ N + 1 := by
    rw [div_pow, div_le_iff₀ (pow_pos hK'0 N)]
    exact (h N).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK hK'.le N) (by positivity))
  have h3 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  linarith

/-- **12:5 (existence) and 12:6.** Let $v$ be an archimedean valuation on $F$. Then its spot contains an ordinary
absolute value $w$ ($w(m) = m$ for the natural numbers $m$ of $F$, `IsOrdinaryAbs`), and $v = w^{\varrho}$ for some
$0 < \varrho \le 1$. (O'Meara derives the existence from 12:4 applied to the completion; uniqueness of $w$ is
`ordinary_unique`.) -/
@[kb "omeara1963" "§12, 12:5 (existence of the ordinary absolute value), p. 19"]
theorem exists_ordinary_rpow (v : AbsoluteValue F ℝ) (hv : ¬ IsNonarchimedean v) :
    ∃ w : AbsoluteValue F ℝ, IsOrdinaryAbs w ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, w x ^ ρ = v x := by
  have hcz := charZero_of_arch v hv
  let v' : AbsoluteValue ℚ ℝ := v.comp (f := Rat.castHom F) (Rat.castHom F).injective
  have hv' : ¬ IsNonarchimedean v' := by
    intro h
    apply hv
    rw [isNonarchimedean_iff_natCast_bounded]
    obtain ⟨M, hM⟩ := (isNonarchimedean_iff_natCast_bounded v').1 h
    exact ⟨M, fun n => by simpa [v'] using hM n⟩
  obtain ⟨c, hc, hc1, hq⟩ := rat_archimedean_exists_rpow v' hv'
  have hnat : ∀ n : ℕ, v (n : F) = (n : ℝ) ^ c := fun n => by
    have := hq n
    simpa [v'] using this
  have hroot : ∀ x : F, (v x ^ (1 / c)) ^ c = v x := fun x => by
    rw [← Real.rpow_mul (v.nonneg x), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
  let w : AbsoluteValue F ℝ :=
    { toFun := fun x => v x ^ (1 / c)
      map_mul' := fun x y => by simp [map_mul, Real.mul_rpow, v.nonneg]
      nonneg' := fun x => Real.rpow_nonneg (v.nonneg x) _
      eq_zero' := fun x => by
        rw [Real.rpow_eq_zero_iff_of_nonneg (v.nonneg x)]
        simp [hc.ne']
      add_le' := fun x y => by
        have ha0 : 0 ≤ v x ^ (1 / c) := Real.rpow_nonneg (v.nonneg x) _
        have hb0 : 0 ≤ v y ^ (1 / c) := Real.rpow_nonneg (v.nonneg y) _
        have h1 : v (x + y) ≤ (v x ^ (1 / c) + v y ^ (1 / c)) ^ c :=
          le_of_pow_bound (v.nonneg _) (Real.rpow_nonneg (by positivity) _) fun N =>
            pow_bound v hc hnat x y _ _ ha0 hb0 (hroot x).symm (hroot y).symm N
        calc v (x + y) ^ (1 / c) ≤ ((v x ^ (1 / c) + v y ^ (1 / c)) ^ c) ^ (1 / c) :=
              Real.rpow_le_rpow (v.nonneg _) h1 (by positivity)
          _ = _ := by
              rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hc.ne', Real.rpow_one] }
  refine ⟨w, fun n => ?_, c, hc, hc1, hroot⟩
  show v (n : F) ^ (1 / c) = n
  rw [hnat, ← Real.rpow_mul (Nat.cast_nonneg n), mul_one_div_cancel hc.ne', Real.rpow_one]

/-- **12:4.** Let $F$ be complete under an archimedean valuation $v$. Then there are $0 < \varrho \le 1$ and a field
isomorphism $\varphi$ of $F$ onto $\mathbb R$ or onto $\mathbb C$ with $v(x) = |\varphi x|^{\varrho}$ for all $x$.
In particular $\varphi$ is a topological isomorphism (`complete_archimedean_isTopologicalIso`), which is O'Meara's
statement. -/
@[kb "omeara1963" "§12, 12:4, p. 17"]
theorem complete_archimedean_rpow (v : AbsoluteValue F ℝ) (hv : ¬ IsNonarchimedean v)
    [CompleteSpace (WithAbs v)] :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ((∃ φ : F ≃+* ℝ, ∀ x, |φ x| ^ ρ = v x) ∨ (∃ φ : F ≃+* ℂ, ∀ x, ‖φ x‖ ^ ρ = v x)) := by
  obtain ⟨w, hw, ρ, hρ, hρ1, hwρ⟩ := exists_ordinary_rpow v hv
  have hequiv : w.IsEquiv v := AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨ρ, hρ, funext hwρ⟩
  have : CompleteSpace (WithAbs w) := completeSpace_of_isEquiv hequiv.symm
  refine ⟨ρ, hρ, hρ1, ?_⟩
  rcases complete_ordinary_isReal_or_isComplex w hw with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact Or.inl ⟨φ, fun x => by rw [hφ, hwρ]⟩
  · exact Or.inr ⟨φ, fun x => by rw [hφ, hwρ]⟩

private theorem exists_hom_complex (v : AbsoluteValue F ℝ) (hv : ¬ IsNonarchimedean v)
    [CompleteSpace (WithAbs v)] :
    ∃ (ρ : ℝ) (θ : F →+* ℂ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, ‖θ x‖ ^ ρ = v x := by
  obtain ⟨ρ, hρ, hρ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩ := complete_archimedean_rpow v hv
  · exact ⟨ρ, Complex.ofRealHom.comp φ.toRingHom, hρ, hρ1, fun x => by
      simpa using hφ x⟩
  · exact ⟨ρ, φ.toRingHom, hρ, hρ1, hφ⟩

/-- **12:4 (O'Meara's form).** A complete archimedean field $F$ admits a topological isomorphism (`IsTopologicalIso`)
onto the real numbers or onto the complex numbers, each with its ordinary absolute value. -/
@[kb "omeara1963" "§12, 12:4, p. 17"]
theorem complete_archimedean_isTopologicalIso (v : AbsoluteValue F ℝ) (hv : ¬ IsNonarchimedean v)
    [CompleteSpace (WithAbs v)] :
    (∃ φ : F ≃+* ℝ, IsTopologicalIso v (NormedField.toAbsoluteValue ℝ) φ) ∨
      (∃ φ : F ≃+* ℂ, IsTopologicalIso v (NormedField.toAbsoluteValue ℂ) φ) := by
  obtain ⟨ρ, hρ, hρ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩ := complete_archimedean_rpow v hv
  · refine Or.inl ⟨φ, ?_⟩
    rw [isTopologicalIso_iff_isEquiv_carryAbs]
    refine AbsoluteValue.IsEquiv.symm (AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨ρ, hρ, ?_⟩)
    funext y
    rw [carryAbs_apply, ← hφ (φ.symm y), RingEquiv.apply_symm_apply]
    simp
  · refine Or.inr ⟨φ, ?_⟩
    rw [isTopologicalIso_iff_isEquiv_carryAbs]
    refine AbsoluteValue.IsEquiv.symm (AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨ρ, hρ, ?_⟩)
    funext y
    rw [carryAbs_apply, ← hφ (φ.symm y), RingEquiv.apply_symm_apply]
    simp

/-- **12:2 (Lemma).** Let $F$ be complete under an archimedean valuation $|\ |$. Then $1 + \alpha$ is a non-zero
square of $F$ whenever $4|\alpha| < |4|$.

The hypothesis is lost in the machine-read text of the book ("whenever $|a| < \ldots$"); it is reconstructed from
the proof, which puts $r = 4|\alpha|/|4|$ and needs $r < 1$. For the ordinary absolute value it reads $|\alpha| < 1$. -/
@[kb "omeara1963" "§12, 12:2, p. 15"]
theorem isSquare_one_add (v : AbsoluteValue F ℝ) (hv : ¬ IsNonarchimedean v) [CompleteSpace (WithAbs v)]
    {a : F} (ha : 4 * v a < v 4) : IsSquare (1 + a) ∧ 1 + a ≠ 0 := by
  obtain ⟨ρ, hρ, hρ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩ := complete_archimedean_rpow v hv
  · have h4 : v 4 ≤ 4 := by
      rw [← hφ]
      have : φ 4 = 4 := map_ofNat φ 4
      rw [this, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      calc (4 : ℝ) ^ ρ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hρ1
        _ = 4 := Real.rpow_one 4
    have h1 : |φ a| < 1 := by
      by_contra hc
      rw [not_lt] at hc
      have := Real.one_le_rpow hc hρ.le
      rw [hφ] at this
      linarith
    have hpos : 0 < φ (1 + a) := by
      rw [map_add, map_one]
      linarith [neg_abs_le (φ a)]
    have := (isPositiveElt_iff_pos φ (1 + a)).2 hpos
    exact ⟨this.2, this.1⟩
  · have h4 : v 4 ≤ 4 := by
      rw [← hφ]
      have : φ 4 = 4 := map_ofNat φ 4
      rw [this]
      have h44 : ‖(4 : ℂ)‖ = 4 := by simp
      rw [h44]
      calc (4 : ℝ) ^ ρ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hρ1
        _ = 4 := Real.rpow_one 4
    have h1 : ‖φ a‖ < 1 := by
      by_contra hc
      rw [not_lt] at hc
      have := Real.one_le_rpow hc hρ.le
      rw [hφ] at this
      linarith
    have hne : φ (1 + a) ≠ 0 := by
      intro h0
      rw [map_add, map_one] at h0
      have : φ a = -1 := by linear_combination h0
      rw [this] at h1
      simp at h1
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (φ (1 + a)) (n := 2) (by norm_num)
    refine ⟨⟨φ.symm z, φ.injective ?_⟩, fun h0 => hne (by rw [h0, map_zero])⟩
    rw [map_mul, RingEquiv.apply_symm_apply, ← sq, hz]

/-- **12:3 (Lemma).** Let $F$ be complete under an archimedean valuation $v$, and let $E = F(i)$ with $i^2 = -1$
(a field extension of $F$ generated by a square root $i$ of $-1$). Then $v$ has a prolongation to $E$: a valuation
$w$ of $E$ with $w(x) = v(x)$ for $x \in F$. -/
@[kb "omeara1963" "§12, 12:3, p. 16"]
theorem exists_prolongation_adjoin_sqrt_neg_one (v : AbsoluteValue F ℝ) (hv : ¬ IsNonarchimedean v)
    [CompleteSpace (WithAbs v)] {E : Type*} [Field E] [Algebra F E] (i : E) (hi : i ^ 2 = -1)
    (hE : F⟮i⟯ = ⊤) : ∃ w : AbsoluteValue E ℝ, ∀ x : F, w (algebraMap F E x) = v x := by
  obtain ⟨ρ, θ, hρ, hρ1, hθ⟩ := exists_hom_complex v hv
  let _ : Algebra F ℂ := θ.toAlgebra
  have hint : IsIntegral F i :=
    IsIntegral.of_pow (by norm_num : 0 < 2) (by rw [hi]; exact isIntegral_one.neg)
  have hadj : Algebra.adjoin F {i} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hE]; rfl
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hgen : pb.gen = i := PowerBasis.ofAdjoinEqTop_gen hint hadj
  have hroot : ∃ y : ℂ, Polynomial.aeval y (minpoly F pb.gen) = 0 :=
    IsAlgClosed.exists_aeval_eq_zero (k := ℂ) (R := F) _
      (by rw [hgen]; exact (minpoly.degree_pos hint).ne')
  let ψ : E →ₐ[F] ℂ := pb.lift hroot.choose hroot.choose_spec
  exact ⟨rpowAbsLeOne ((NormedField.toAbsoluteValue ℂ).comp (f := ψ.toRingHom)
      ψ.toRingHom.injective) hρ hρ1, fun x => by
    rw [rpowAbsLeOne_apply]
    show ‖ψ (algebraMap F E x)‖ ^ ρ = v x
    rw [ψ.commutes]
    exact hθ x⟩

/-- A power of a non-archimedean valuation is a valuation (every exponent $c > 0$). -/
private noncomputable def rpowNA {E : Type*} [Field E] (w : AbsoluteValue E ℝ) (hw : IsNonarchimedean w)
    {c : ℝ} (hc : 0 < c) : AbsoluteValue E ℝ where
  toFun x := w x ^ c
  map_mul' x y := by simp [map_mul, Real.mul_rpow, w.nonneg]
  nonneg' x := Real.rpow_nonneg (w.nonneg x) _
  eq_zero' x := by
    rw [Real.rpow_eq_zero_iff_of_nonneg (w.nonneg x)]
    simp [hc.ne']
  add_le' x y := by
    calc w (x + y) ^ c ≤ (max (w x) (w y)) ^ c :=
          Real.rpow_le_rpow (w.nonneg _) (hw x y) hc.le
      _ = max (w x ^ c) (w y ^ c) := by
          rcases le_total (w x) (w y) with h | h
          · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow (w.nonneg _) h hc.le)]
          · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow (w.nonneg _) h hc.le)]
      _ ≤ _ := max_le_add_of_nonneg (Real.rpow_nonneg (w.nonneg x) _) (Real.rpow_nonneg (w.nonneg y) _)

/-- **12:7 (Remark).** Let $E/F$ be a field extension, $w$ a valuation of $E$ (a spot $\mathfrak P$), and suppose the
induced spot $\mathfrak p$ on $F$ is non-trivial. Then restriction to $F$ is a bijection from the valuations in
$\mathfrak P$ onto the valuations in $\mathfrak p$. -/
@[kb "omeara1963" "§12, 12:7, p. 19"]
theorem under_bijective {E : Type*} [Field E] [Algebra F E] (w : AbsoluteValue E ℝ)
    (hnt : (w.under F).IsNontrivial) :
    Function.Bijective (fun w' : {w' : AbsoluteValue E ℝ // w'.IsEquiv w} =>
      (⟨w'.1.under F, under_isEquiv w'.2⟩ :
        {v' : AbsoluteValue F ℝ // v'.IsEquiv (w.under F)})) := by
  constructor
  · rintro ⟨w1, h1⟩ ⟨w2, h2⟩ heq
    have hr : w1.under F = w2.under _ := congrArg Subtype.val heq
    have he : w1.IsEquiv w2 := h1.trans h2.symm
    apply Subtype.ext
    refine eq_of_isEquiv_of_eq_on_subfield w1 w2 he (algebraMap F E).fieldRange ?_ ?_
    · rintro _ ⟨x, rfl⟩
      have := congrArg (fun f : AbsoluteValue F ℝ => f x) hr
      simpa [under_apply_eq] using this
    · obtain ⟨x, hx0, hx1⟩ := hnt
      refine ⟨algebraMap F E x, ⟨x, rfl⟩, by simpa using hx0, ?_⟩
      have h1' : (w1.under F).IsEquiv (w.under _) := under_isEquiv h1
      intro h
      exact hx1 (h1'.eq_one_iff.1 (by simpa [under_apply_eq] using h))
  · rintro ⟨v', hv'⟩
    by_cases hna : IsNonarchimedean w
    · obtain ⟨c, hc, hcv⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 hv'.symm
      refine ⟨⟨rpowNA w hna hc, ?_⟩, ?_⟩
      · exact (AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨c, hc, rfl⟩).symm
      · apply Subtype.ext
        ext x
        show w (algebraMap F E x) ^ c = v' x
        rw [← congrFun hcv x]
        rfl
    · obtain ⟨u, hu, σ, hσ, hσ1, huσ⟩ := exists_ordinary_rpow w hna
      have hwu : u.IsEquiv w :=
        AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨σ, hσ, funext huσ⟩
      have hru : IsOrdinaryAbs (u.under F) := fun n => by
        rw [under_apply_eq, map_natCast]
        exact hu n
      have hv'u : v'.IsEquiv (u.under _) := hv'.trans (under_isEquiv hwu.symm)
      obtain ⟨τ, hτ, hτ1, hvτ⟩ := ordinary_rpow (u.under F) v' hru hv'u
      refine ⟨⟨rpowAbsLeOne u hτ hτ1, ?_⟩, ?_⟩
      · have : u.IsEquiv (rpowAbsLeOne u hτ hτ1) :=
          AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨τ, hτ, funext fun x => (rpowAbsLeOne_apply u hτ hτ1 x).symm⟩
        exact this.symm.trans hwu
      · apply Subtype.ext
        ext x
        show rpowAbsLeOne u hτ hτ1 (algebraMap F E x) = v' x
        rw [rpowAbsLeOne_apply, hvτ x]
        rfl

/-- The canonical map to Mathlib's completion is a completion in the sense of `IsCompletion`. -/
private theorem isCompletion_completion {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    IsCompletion v v.Completion
      ((UniformSpace.Completion.coeRingHom).comp (WithAbs.equiv v).symm.toRingHom) := by
  refine ⟨fun x => ?_, ?_, inferInstance⟩
  · show ‖((WithAbs.toAbs v x : WithAbs v) : UniformSpace.Completion (WithAbs v))‖ = v x
    rw [UniformSpace.Completion.norm_coe]; rfl
  · exact (UniformSpace.Completion.denseRange_coe).comp (WithAbs.equiv v).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)

/-- **12:13 (Example).** The prime field $\mathbb Q$ of characteristic $0$ has exactly one archimedean spot, that of
the ordinary absolute value $|\ |_\infty$ (`rat_archimedean_spot_unique`, 12:1); this spot is real (its completion
is isometric to $\mathbb R$); and the positive elements of $\mathbb Q$ at it (12:11: the elements that are non-zero
squares in the completion $\mathbb R$) are the quotients $m/n$ of natural numbers $m, n > 0$. -/
@[kb "omeara1963" "§12, 12:13, p. 20"]
theorem rat_archimedean_real_spot :
    (∀ v : AbsoluteValue ℚ ℝ, ¬ IsNonarchimedean v → v.IsEquiv Rat.AbsoluteValue.real) ∧
    IsRealSpot Rat.AbsoluteValue.real ∧
    ∀ q : ℚ, IsPositiveElt (q : ℝ) ↔ ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ q = m / n := by
  refine ⟨fun v hv => rat_archimedean_equiv_real v hv, ?_, ?_⟩
  · obtain ⟨e, -, he, -⟩ := exists_unique_equiv_of_isCompletion Rat.AbsoluteValue.real _ _
      (isCompletion_completion Rat.AbsoluteValue.real) isCompletion_rat_real
    exact ⟨e, fun y => by rw [← he y, Real.norm_eq_abs]⟩
  · intro q
    rw [isPositiveElt_iff_pos (RingEquiv.refl ℝ)]
    simp only [RingEquiv.refl_apply]
    constructor
    · intro h
      have hq : 0 < q := by exact_mod_cast h
      have hnum : 0 < q.num := Rat.num_pos.2 hq
      refine ⟨q.num.toNat, q.den, by omega, q.den_pos, ?_⟩
      have : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg hnum.le
      rw [this]
      exact (Rat.num_div_den q).symm
    · rintro ⟨m, n, hm, hn, rfl⟩
      have : (0 : ℚ) < (m : ℚ) / n := by positivity
      exact_mod_cast this

section Prolong

variable {E : Type*} [Field E] [Algebra F E]

/-- A valuation `w` of `E` prolonging `v` is a seminorm on `E` as a vector space over `(F, v)`. -/
private noncomputable def seminormOf (v : AbsoluteValue F ℝ) (w : AbsoluteValue E ℝ)
    (h : ∀ x : F, w (algebraMap F E x) = v x) : Seminorm (WithAbs v) E where
  toFun e := w e
  map_zero' := by simp
  add_le' a b := w.add_le a b
  neg' a := by simp
  smul' r e := by
    show w ((WithAbs.equiv v r) • e) = ‖r‖ * w e
    rw [Algebra.smul_def, map_mul, h]
    rfl

private theorem lt_one_iff_tendsto (v : AbsoluteValue F ℝ) (w : AbsoluteValue E ℝ)
    (h : ∀ x : F, w (algebraMap F E x) = v x) (x : E) :
    w x < 1 ↔ @Filter.Tendsto ℕ E (fun n => x ^ n) Filter.atTop
      (@nhds E (seminormOf v w h).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace 0) := by
  let _ : SeminormedAddCommGroup E := (seminormOf v w h).toSeminormedAddCommGroup
  change _ ↔ Filter.Tendsto (fun n => x ^ n) Filter.atTop (nhds 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have : ∀ n : ℕ, ‖x ^ n‖ = w x ^ n := fun n => by
    show w (x ^ n) = _
    rw [map_pow]
  simp only [this]
  rw [tendsto_pow_atTop_nhds_zero_iff, abs_of_nonneg (w.nonneg x)]

private theorem completeSpace_of_seminorm (v : AbsoluteValue F ℝ) (w : AbsoluteValue E ℝ)
    (h : ∀ x : F, w (algebraMap F E x) = v x)
    (hc : @CompleteSpace E (seminormOf v w h).toSeminormedAddCommGroup.toUniformSpace) :
    CompleteSpace (WithAbs w) := by
  let _ : SeminormedAddCommGroup E := (seminormOf v w h).toSeminormedAddCommGroup
  let f : WithAbs w →+ E :=
    { toFun := fun x => x.ofAbs
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f (fun x => rfl)
  have hr : Function.Surjective f := fun e => ⟨WithAbs.toAbs w e, rfl⟩
  exact (hf.isUniformInducing.completeSpace_congr hr).2 hc

/-- Over a complete archimedean field, a finite extension has at most one prolongation of the valuation, and it is
complete (11:17). -/
private theorem prolong_unique_complete (v : AbsoluteValue F ℝ) (hv : ¬ IsNonarchimedean v)
    [CompleteSpace (WithAbs v)] [FiniteDimensional F E] (w1 w2 : AbsoluteValue E ℝ)
    (h1 : ∀ x : F, w1 (algebraMap F E x) = v x) (h2 : ∀ x : F, w2 (algebraMap F E x) = v x) :
    w1 = w2 ∧ CompleteSpace (WithAbs w1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 < v n := by
    by_contra hc
    push Not at hc
    exact hv ((isNonarchimedean_iff_natCast_bounded v).2 ⟨1, hc⟩)
  let _ : NontriviallyNormedField (WithAbs v) :=
    { (inferInstance : NormedField (WithAbs v)) with
      non_trivial := ⟨WithAbs.toAbs v n, by
        rw [WithAbs.norm_toAbs_eq]
        simpa using hn⟩ }
  have hfd : FiniteDimensional (WithAbs v) E := by
    obtain ⟨S, hS⟩ := (Module.finite_def.1 (inferInstance : Module.Finite F E))
    refine ⟨⟨S, ?_⟩⟩
    rw [eq_top_iff]
    intro e _
    have : e ∈ Submodule.span F (S : Set E) := hS ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun x _ => x ∈ Submodule.span (WithAbs v) (S : Set E))
      (fun x hx => Submodule.subset_span hx) (Submodule.zero_mem _)
      (fun x y _ _ hx hy => Submodule.add_mem _ hx hy) (fun a x _ hx => ?_) this
    have := Submodule.smul_mem _ (WithAbs.toAbs v a) hx
    exact this
  have hp : ∀ x, seminormOf v w1 h1 x = 0 → x = 0 := fun x hx => w1.eq_zero.1 hx
  have hq : ∀ x, seminormOf v w2 h2 x = 0 → x = 0 := fun x hx => w2.eq_zero.1 hx
  obtain ⟨htop, hcomp⟩ := norms_equivalent (K := WithAbs v) (V := E)
    (seminormOf v w1 h1) (seminormOf v w2 h2) hp hq
  have hequiv : w1.IsEquiv w2 := by
    rw [AbsoluteValue.isEquiv_iff_lt_one_iff]
    intro x
    rw [lt_one_iff_tendsto v w1 h1, lt_one_iff_tendsto v w2 h2, htop]
  refine ⟨?_, completeSpace_of_seminorm v w1 h1 hcomp⟩
  refine eq_of_isEquiv_of_eq_on_subfield w1 w2 hequiv (algebraMap F E).fieldRange ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [h1, h2]
  · refine ⟨algebraMap F E n, ⟨n, rfl⟩, ?_, ?_⟩
    · intro h0
      have := h1 n
      rw [h0, map_zero] at this
      linarith [v.nonneg (n : F)]
    · rw [h1]
      exact hn.ne'

end Prolong

/-- **14:1 (archimedean case).** Let $E/F$ be a finite extension of degree $n$ of a field $F$ complete under an
archimedean valuation $v$. Then there is a unique prolongation $w$ of $v$ to $E$, it is given by
$w(\alpha) = v(N_{E/F}\alpha)^{1/n}$, and $E$ is complete under it. -/
@[kb "omeara1963" "§14, 14:1 (archimedean case), p. 28"]
theorem prolongation_formula_archimedean (v : AbsoluteValue F ℝ) (hv : ¬ IsNonarchimedean v)
    [CompleteSpace (WithAbs v)] {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E] :
    ∃ w : AbsoluteValue E ℝ, (∀ x : F, w (algebraMap F E x) = v x) ∧
      (∀ a : E, w a = v (Algebra.norm F a) ^ (1 / (Module.finrank F E : ℝ))) ∧
      CompleteSpace (WithAbs w) ∧
      ∀ w' : AbsoluteValue E ℝ, (∀ x : F, w' (algebraMap F E x) = v x) → w' = w := by
  obtain ⟨ρ, θ, hρ, hρ1, hθ⟩ := exists_hom_complex v hv
  have hcz := charZero_of_arch v hv
  let _ : Algebra F ℂ := θ.toAlgebra
  let ψ : E →ₐ[F] ℂ := IsAlgClosed.lift
  let absOf : (E →ₐ[F] ℂ) → AbsoluteValue E ℝ := fun σ =>
    rpowAbsLeOne ((NormedField.toAbsoluteValue ℂ).comp (f := σ.toRingHom)
      σ.toRingHom.injective) hρ hρ1
  have habs : ∀ σ x, absOf σ x = ‖σ x‖ ^ ρ := fun σ x => rpowAbsLeOne_apply _ hρ hρ1 x
  have hpro : ∀ σ x, absOf σ (algebraMap F E x) = v x := fun σ x => by
    rw [habs, σ.commutes]
    exact hθ x
  have huniq : ∀ w', (∀ x, w' (algebraMap F E x) = v x) → w' = absOf ψ := fun w' h' =>
    (prolong_unique_complete v hv w' (absOf ψ) h' (hpro ψ)).1
  refine ⟨absOf ψ, hpro ψ, ?_, (prolong_unique_complete v hv (absOf ψ) (absOf ψ) (hpro ψ) (hpro ψ)).2,
    huniq⟩
  intro a
  have hnorm : θ (Algebra.norm F a) = ∏ σ : E →ₐ[F] ℂ, σ a := Algebra.norm_eq_prod_embeddings F ℂ a
  have hall : ∀ σ : E →ₐ[F] ℂ, ‖σ a‖ ^ ρ = absOf ψ a := fun σ => by
    rw [← habs, ← huniq (absOf σ) (hpro σ)]
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  have hv' : v (Algebra.norm F a) = (absOf ψ a) ^ (Module.finrank F E) := by
    calc v (Algebra.norm F a) = ‖θ (Algebra.norm F a)‖ ^ ρ := (hθ _).symm
      _ = (∏ σ : E →ₐ[F] ℂ, ‖σ a‖) ^ ρ := by rw [hnorm, norm_prod]
      _ = ∏ σ : E →ₐ[F] ℂ, ‖σ a‖ ^ ρ :=
          (Real.finsetProd_rpow _ _ (fun σ _ => norm_nonneg _) ρ).symm
      _ = ∏ σ : E →ₐ[F] ℂ, absOf ψ a := Finset.prod_congr rfl (fun σ _ => hall σ)
      _ = (absOf ψ a) ^ (Module.finrank F E) := by
          rw [Finset.prod_const, Finset.card_univ, AlgHom.card]
  rw [hv', ← Real.rpow_natCast, ← Real.rpow_mul ((absOf ψ).nonneg a),
    mul_one_div_cancel (by exact_mod_cast hn.ne'), Real.rpow_one]

end QuadFormsKB.OMeara
