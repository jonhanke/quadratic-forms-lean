/-
# The correction step of O'Meara 104:4 without 95:1 and 101:9

**Layer:** $V = F^n$ with $Q$ = `Q : QuadForm F n` nondegenerate over a number field $F$, its completions $V_\mathfrak p$,
the spinor kernels $O'(V)$, $O'(V_\mathfrak p)$ (`Lattices/SpinorKernel.lean`) and the commutator subgroups
$\Omega(V_\mathfrak p) = [O(V_\mathfrak p), O(V_\mathfrak p)]$ (= `eqPairGroup`, `eqPairGroup_eq_commutator`).

**Proves** `exists_correction`: for $n \ge 4$, a finite set $T$ of finite primes and $\varphi_\mathfrak p \in O'(V_\mathfrak p)$
($\mathfrak p \in T$) there is $g \in O'(V)$ with $g\varphi_\mathfrak p \in \Omega(V_\mathfrak p)$ for $\mathfrak p \in T$ and
$g \in \Omega(V_\mathfrak p)$ at every other prime. This is the hypothesis of `rotApprox_of_vecApprox_of_correction`
(step 1c of O'Meara 1973, 104:4, p. 316), which O'Meara obtains from 95:1 (local index $(O' : \Omega) \le 2$ for quaternary
spaces) and 101:9 (global elements with prescribed classes modulo $\Omega$).

*Simplification.* No index computation is needed:
* the coset $\tau_{x_1}\cdots\tau_{x_r}\Omega$ depends only on the square classes of the $Q(x_i)$
  (`symmProd_inv_mul_mem_of_forall₂`: $\tau_x\tau_y \in \Omega$ when $Q(y)/Q(x)$ is a square);
* the primes at which $V_\mathfrak p$ is anisotropic form a finite set $A$ (`finite_anisotropic`), and outside it
  $O'(V_\mathfrak p) = \Omega(V_\mathfrak p)$;
* write $\varphi_\mathfrak p^{-1}$ ($\mathfrak p \in T$) and $1$ ($\mathfrak p \in A \setminus T$) as spinor words of a common even length
  $N$, approximate the first $N - 1$ vectors by global $y_i$ (so the square classes agree), and take $y_{N-1}$ with
  $Q(y_{N-1}) = c = \prod_{i < N-1} Q(y_i)$. $V$ represents $c$ by Hasse–Minkowski: quaternary spaces over local fields
  are universal, and at a real place $V_w$ is isotropic or definite (`isotropicIn_or_isSquare_mul`).
-/
import QuadFormsKB.Lattices.StrongApproximationProof
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal
import QuadFormsKB.Literature.HasseNorm.SquareClasses

open NumberField IsDedekindDomain Matrix Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### The coset of a product of symmetries modulo `eqPairGroup` -/

section Coset

variable (K : Type*) [Field K] [Algebra F K] [CharZero K]

/-- Two anisotropic vectors whose values differ by a nonzero square factor. -/
def SqRel (x y : Fin n → K) : Prop :=
  Q.evalIn K x ≠ 0 ∧ Q.evalIn K y ≠ 0 ∧ IsSquare (Q.evalIn K y / Q.evalIn K x)

/-- **$\tau_x\tau_y \in \Omega$ when $Q(y)/Q(x)$ is a square:** $\tau_y = \tau_{s^{-1}y}$ with $Q(s^{-1}y) = Q(x)$. -/
theorem symm_mul_symm_mem_eqPairGroup {x y : Fin n → K} (h : SqRel Q K x y) :
    symm Q K x * symm Q K y ∈ eqPairGroup Q K := by
  obtain ⟨hx, hy, s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hs
    exact hs.elim hy hx
  rw [← symm_smul Q K (inv_ne_zero hs0) y]
  refine pair_mem_eqPairGroup Q K hx ?_
  rw [evalIn_smul_sq]
  have : Q.evalIn K y = s * s * Q.evalIn K x := by rw [← hs]; field_simp
  rw [this]; field_simp

/-- **The $\Omega$-coset of $\tau_{x_1}\cdots\tau_{x_r}$ depends only on the square classes of the $Q(x_i)$.** -/
theorem symmProd_inv_mul_mem_of_forall₂ {xs ys : List (Fin n → K)} (h : List.Forall₂ (SqRel Q K) xs ys) :
    (symmProd Q K xs)⁻¹ * symmProd Q K ys ∈ eqPairGroup Q K := by
  induction h with
  | nil => simp [symmProd]
  | @cons x y xs ys hxy _ ih =>
    have e : (symmProd Q K (x :: xs))⁻¹ * symmProd Q K (y :: ys) =
        (symmProd Q K xs)⁻¹ * (symm Q K x * symm Q K y) * ((symmProd Q K xs)⁻¹)⁻¹ *
          ((symmProd Q K xs)⁻¹ * symmProd Q K ys) := by
      simp only [symmProd, List.map_cons, List.prod_cons, _root_.mul_inv_rev, symm_inv, inv_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ ((eqPairGroup_normal Q K).conj_mem _
      (symm_mul_symm_mem_eqPairGroup Q K hxy) _) ih

/-- The product of the values along related lists differs by a square. -/
theorem isSquare_valProd_div_of_forall₂ {xs ys : List (Fin n → K)} (h : List.Forall₂ (SqRel Q K) xs ys) :
    IsSquare (valProd Q K ys / valProd Q K xs) := by
  induction h with
  | nil => simp [valProd]
  | @cons x y xs ys hxy _ ih =>
    have e : valProd Q K (y :: ys) / valProd Q K (x :: xs) =
        (Q.evalIn K y / Q.evalIn K x) * (valProd Q K ys / valProd Q K xs) := by
      simp only [valProd, List.map_cons, List.prod_cons]; ring
    rw [e]; exact hxy.2.2.mul ih

/-- $\tau_x^{2k} = 1$. -/
theorem symmProd_replicate_two_mul (x : Fin n → K) (k : ℕ) :
    symmProd Q K (List.replicate (2 * k) x) = 1 := by
  induction k with
  | zero => simp [symmProd]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 + 2 * k by ring, List.replicate_add, symmProd_append, ih, mul_one]
    simp [symmProd, symm_mul_self]

/-- **Padding a spinor word** with an even number of copies of an anisotropic vector. -/
theorem isSpinorWord_pad {l : List (Fin n → K)} (hl : IsSpinorWord Q K l) {x : Fin n → K}
    (hx : Q.evalIn K x ≠ 0) {N : ℕ} (hN : Even N) (hlN : l.length ≤ N) :
    IsSpinorWord Q K (l ++ List.replicate (N - l.length) x) ∧
      (l ++ List.replicate (N - l.length) x).length = N ∧
      symmProd Q K (l ++ List.replicate (N - l.length) x) = symmProd Q K l := by
  obtain ⟨hla, hle, hls⟩ := hl
  obtain ⟨k, hk⟩ : Even (N - l.length) := (Nat.even_sub hlN).mpr (by simp [hN, hle])
  rw [show N - l.length = 2 * k by omega]
  refine ⟨⟨fun z hz => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rcases List.mem_append.mp hz with h | h
    · exact hla z h
    · rw [List.eq_of_mem_replicate h]; exact hx
  · rw [List.length_append, List.length_replicate]; exact hle.add (even_two_mul k)
  · rw [valProd_append]
    refine hls.mul ⟨Q.evalIn K x ^ k, ?_⟩
    simp only [valProd, List.map_replicate, List.prod_replicate]; ring
  · rw [List.length_append, List.length_replicate]; omega
  · rw [symmProd_append, symmProd_replicate_two_mul, mul_one]

end Coset

/-! ### Finitely many anisotropic primes -/

/-- **$V_\mathfrak p$ is isotropic at almost every prime** ($n \ge 3$): diagonalize over $F$; at a non-dyadic prime where
all coefficients are units the diagonal form is isotropic (`NFLocal.isotropic_diag_units_nf`). -/
theorem finite_anisotropic (hQ : Q.Nondegenerate) (hn : 3 ≤ n) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ Q.IsotropicIn (v.adicCompletion F)}.Finite := by
  obtain ⟨b, hb, hP⟩ := FieldGen.exists_isometric_diag Q hQ
  refine (NFLocal.finite_bad_places_nf n b hb).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_ofPred_eq, not_or, not_exists, not_not] at h
  exact hv ((FieldGen.isotropicIn_iff_of_isometricIn _ (FieldGen.isometricIn_of_base _ hP)).mpr
    (NFLocal.isotropic_diag_units_nf v h.1 n hn b h.2))

/-! ### Archimedean places: isotropic or definite -/

/-- A sum of two squares relation: the discriminant argument. If $Q(x)Q(y) < 0$ over $\mathbb R$ then $x + ty$ is
isotropic for a root $t$ of $Q(x) + tB(x,y) + t^2Q(y)$. -/
theorem evalIn_add_smul (K : Type*) [Field K] [Algebra F K] [CharZero K] (x y : Fin n → K) (t : K) :
    Q.evalIn K (x + t • y) = Q.evalIn K x + t * qbil Q K x y + t ^ 2 * Q.evalIn K y := by
  have h2 : (2 : K) ≠ 0 := by
    have := (algebraMap F K).injective.ne (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat, map_zero] at this
  apply mul_left_cancel₀ h2
  rw [two_mul_evalIn_eq, qbil_add_left, qbil_add_right, qbil_add_right, qbil_smul_left, qbil_smul_left,
    qbil_smul_right, qbil_smul_right, qbil_comm Q K y x, ← two_mul_evalIn_eq, ← two_mul_evalIn_eq]
  ring

/-- **At an archimedean place $V_w$ is isotropic or definite:** if $V_w$ is anisotropic, the product of any two
nonzero values is a square in $F_w$. (Complex $w$: every element is a square. Real $w$: if $Q(x)Q(y) < 0$, the
quadratic $Q(x + ty)$ has a real root, and $x + ty \ne 0$.) -/
theorem isotropicIn_or_isSquare_mul (w : InfinitePlace F) :
    Q.IsotropicIn w.Completion ∨ ∀ x y : Fin n → w.Completion, Q.evalIn _ x ≠ 0 → Q.evalIn _ y ≠ 0 →
      IsSquare (Q.evalIn _ x * Q.evalIn _ y) := by
  have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
  by_cases hw : w.IsReal
  · let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    by_contra hcon
    simp only [not_or, not_forall] at hcon
    obtain ⟨hani, x, y, hx, hy, hns⟩ := hcon
    set a := Q.evalIn w.Completion x
    set b := Q.evalIn w.Completion y
    set B := qbil Q w.Completion x y
    have hneg : ψ a * ψ b < 0 := by
      by_contra hle
      push Not at hle
      apply hns
      refine ⟨ψ.symm (Real.sqrt (ψ a * ψ b)), ψ.injective ?_⟩
      rw [map_mul, map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hle]
    have hb0 : ψ b ≠ 0 := fun h => by rw [h, mul_zero] at hneg; exact lt_irrefl _ hneg
    set D := ψ B ^ 2 - 4 * (ψ a * ψ b)
    have hD : 0 ≤ D := by nlinarith [sq_nonneg (ψ B)]
    set r := (-ψ B + Real.sqrt D) / (2 * ψ b)
    have hr : ψ a + r * ψ B + r ^ 2 * ψ b = 0 := by
      have h1 : 2 * ψ b * r + ψ B = Real.sqrt D := by simp only [r]; field_simp; ring
      have h2 : (2 * ψ b * r + ψ B) ^ 2 = D := by rw [h1]; exact Real.sq_sqrt hD
      have h3 : (4 * ψ b) * (ψ a + r * ψ B + r ^ 2 * ψ b) = 0 := by
        simp only [D] at h2; linear_combination h2
      exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero four_ne_zero hb0)
    set t := ψ.symm r
    apply hani
    refine ⟨x + t • y, fun h0 => ?_, ?_⟩
    · have hx' : x = (-t) • y := by rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, h0]
      apply hns
      refine ⟨t * b, ?_⟩
      simp only [a, b]; rw [hx', evalIn_smul_sq]; ring
    · apply ψ.injective
      rw [evalIn_add_smul, map_zero, map_add, map_add, map_mul, map_mul, map_pow]
      simp only [t, RingEquiv.apply_symm_apply]
      exact hr
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let ψ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    refine Or.inr fun x y _ _ => ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.isSquare (ψ (Q.evalIn _ x * Q.evalIn _ y))
    exact ⟨ψ.symm z, ψ.injective (by rw [hz, map_mul, RingEquiv.apply_symm_apply])⟩

/-! ### Helpers -/

theorem isSquare_list_prod {M : Type*} [CommMonoid M] (l : List M) (h : ∀ a ∈ l, IsSquare a) :
    IsSquare l.prod := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons a l ih =>
    rw [List.prod_cons]
    exact (h a (by simp)).mul (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem list_prod_map_mul_const {M : Type*} [CommMonoid M] (l : List M) (r : M) :
    (l.map fun a => a * r).prod = l.prod * r ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]
    ac_rfl

/-- If every $a \in l$ has $ar$ a square and $l$ has odd length, then $\prod l / r$ is a square. -/
theorem isSquare_prod_div {K : Type*} [Field K] (l : List K) {r : K} (hr : r ≠ 0)
    (hl : ∀ a ∈ l, IsSquare (a * r)) (hodd : Odd l.length) : IsSquare (l.prod / r) := by
  have h1 : IsSquare (l.map fun a => a * r).prod :=
    isSquare_list_prod _ fun b hb => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact hl c hc
  obtain ⟨k, hk⟩ := hodd
  have e : l.prod / r = (l.map fun a => a * r).prod / (r ^ (k + 1)) ^ 2 := by
    rw [list_prod_map_mul_const, hk, ← pow_mul]
    field_simp
    ring
  rw [e]
  exact h1.div ⟨r ^ (k + 1), by ring⟩

/-- The image of a product of rational symmetries. -/
@[kb "omeara1963" "§101B, p. 289 (localization of an isometry; (τ_u)_{𝔭} = τ_{u_{𝔭}})"]
theorem orthMap_symmProd (v : HeightOneSpectrum (𝓞 F)) (xs : List (Fin n → F)) :
    orthMap Q (v.adicCompletion F) (symmProd Q F xs) = symmProd Q (v.adicCompletion F) (xs.map (locVec v)) := by
  rw [symmProd, symmProd, map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => orthMap_symm_locVec Q v x

theorem valProd_map_locVec (v : HeightOneSpectrum (𝓞 F)) (xs : List (Fin n → F)) :
    valProd Q (v.adicCompletion F) (xs.map (locVec v)) = algebraMap F _ (valProd Q F xs) := by
  rw [valProd, valProd, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply]
  rw [evalIn_locVec]

/-- **$\{y : Q(y)/Q(x) \in 1 + 4\mathfrak p\}$ is a neighbourhood of $x$**, and on it $Q(y)/Q(x)$ is a square. -/
theorem sqRel_mem_nhds (v : HeightOneSpectrum (𝓞 F)) {x : Fin n → v.adicCompletion F}
    (hx : Q.evalIn _ x ≠ 0) : {y | SqRel Q (v.adicCompletion F) x y} ∈ 𝓝 x := by
  have h4' : (4 : v.adicCompletion F) ≠ 0 := by
    have := (algebraMap F (v.adicCompletion F)).injective.ne (by norm_num : (4 : F) ≠ 0)
    rwa [map_ofNat, map_zero] at this
  have hc : Continuous fun y : Fin n → v.adicCompletion F =>
      Q.evalIn (v.adicCompletion F) y / Q.evalIn (v.adicCompletion F) x - 1 :=
    ((continuous_evalIn v Q).div_const _).sub continuous_const
  have hN : {u : v.adicCompletion F | Valued.v u < Valued.v (4 : v.adicCompletion F)} ∈
      𝓝 (Q.evalIn (v.adicCompletion F) x / Q.evalIn (v.adicCompletion F) x - 1) := by
    rw [div_self hx, sub_self]
    obtain ⟨k, hk⟩ := exists_valued_eq_exp v h4'
    rw [hk]
    have := valued_lt_mem_nhds_zero v (-k)
    rwa [neg_neg] at this
  have hpre := hc.continuousAt.preimage_mem_nhds hN
  refine Filter.mem_of_superset hpre fun y hy => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy
  have h41 : Valued.v (4 : v.adicCompletion F) ≤ 1 := by
    have := valued_int_le_one v (4 : 𝓞 F)
    rwa [map_ofNat] at this
  have hsq := HN.isSquare_of_valued_sub_one_lt v _ hy
  have hy0 : Q.evalIn (v.adicCompletion F) y ≠ 0 := by
    intro h0
    rw [h0, zero_div, zero_sub, Valuation.map_neg, map_one] at hy
    exact absurd (hy.trans_le h41) (lt_irrefl _)
  exact ⟨hx, hy0, hsq⟩

/-- **Approximating a list of local vectors** at finitely many primes (nonempty set) by global vectors with the same
square classes of values. -/
theorem exists_list_approx (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : T.Nonempty) :
    ∀ (m : ℕ) (tg : ∀ v : HeightOneSpectrum (𝓞 F), List (Fin n → v.adicCompletion F)),
      (∀ v ∈ T, (tg v).length = m ∧ ∀ x ∈ tg v, Q.evalIn _ x ≠ 0) →
      ∃ ys : List (Fin n → F), ys.length = m ∧ (∀ y ∈ ys, Q.evalIn F y ≠ 0) ∧
        ∀ v ∈ T, List.Forall₂ (SqRel Q (v.adicCompletion F)) (tg v) (ys.map (locVec v)) := by
  classical
  intro m
  induction m with
  | zero =>
    intro tg htg
    refine ⟨[], rfl, by simp, fun v hv => ?_⟩
    rw [List.length_eq_zero_iff.mp (htg v hv).1]; exact List.Forall₂.nil
  | succ m ih =>
    intro tg htg
    have hcons : ∀ v ∈ T, tg v = (tg v).headD 0 :: (tg v).tail := by
      intro v hv
      obtain ⟨a, l, hal⟩ := List.exists_cons_of_length_eq_add_one (htg v hv).1
      rw [hal]; rfl
    obtain ⟨ys, hlen, hani, hrel⟩ := ih (fun v => (tg v).tail) fun v hv => by
      refine ⟨by rw [List.length_tail, (htg v hv).1]; rfl, fun x hx => (htg v hv).2 x (List.mem_of_mem_tail hx)⟩
    obtain ⟨y, hyT, -⟩ := exists_vec_approx T (fun v => (tg v).headD 0)
      (fun v => {y | SqRel Q (v.adicCompletion F) ((tg v).headD 0) y}) fun v hv =>
        sqRel_mem_nhds Q v ((htg v hv).2 _ (by rw [hcons v hv]; exact List.mem_cons_self))
    obtain ⟨v₀, hv₀⟩ := hT
    have hy0 : Q.evalIn F y ≠ 0 := by
      intro h0
      have := (hyT v₀ hv₀).2.1
      rw [evalIn_locVec] at this
      exact this (by rw [show Q.eval y = Q.evalIn F y from rfl, h0, map_zero])
    refine ⟨y :: ys, by rw [List.length_cons, hlen], ?_, fun v hv => ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | h
      · exact hy0
      · exact hani z h
    · rw [hcons v hv, List.map_cons]
      exact List.Forall₂.cons (hyT v hv) (hrel v hv)

/-- **$Q$ represents $c$ over $K$ when $Q$ is isotropic over $K$.** -/
@[kb "cassels1978" "Ch. 2, Lemma 2.1, Cor. 2, p. 15"]
theorem representsIn_of_isotropicIn (K : Type*) [Field K] [Algebra F K] (hQ : Q.Nondegenerate) (c : F)
    (h : Q.IsotropicIn K) : Q.RepresentsIn K c := by
  rw [QuadForm.representsIn_iff_isotropicIn_orthSum K hQ c]
  obtain ⟨x, hx0, hx⟩ := h
  refine ⟨Fin.append x 0, fun h0 => hx0 ?_, ?_⟩
  · funext i; have := congrFun h0 (Fin.castAdd 1 i); simpa [Fin.append_left] using this
  · rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_diag]
    simp [Fin.append_left, Fin.append_right, hx]

/-! ### The correction -/

/-- **A global vector of norm $c$** when $c = \prod_{y \in ys} Q(y)$ over an odd number of anisotropic global vectors
($n \ge 4$): $V_\mathfrak p$ is universal at every finite prime, and at an infinite place $V_w$ is isotropic or $c$ is
$Q(y_0)$ times a square (`isotropicIn_or_isSquare_mul`). -/
theorem representsIn_valProd (hQ : Q.Nondegenerate) (hn : 4 ≤ n) (ys : List (Fin n → F))
    (hys : ∀ y ∈ ys, Q.evalIn F y ≠ 0) (hodd : Odd ys.length) : Q.RepresentsIn F (valProd Q F ys) := by
  have hc : valProd Q F ys ≠ 0 := by
    rw [valProd]; exact List.prod_ne_zero (by
      intro h0; obtain ⟨y, hy, hy0⟩ := List.mem_map.mp h0; exact hys y hy hy0)
  have hc' : ∀ i, (![-valProd Q F ys] : Fin 1 → F) i ≠ 0 := fun i => by
    simpa [Subsingleton.elim i 0] using hc
  rw [represents_iff_everywhere_nf Q hQ _ hc]
  intro place
  cases place with
  | finite v =>
    exact (QuadForm.representsIn_iff_isotropicIn_orthSum _ hQ _).mpr
      (isotropicIn_completion_of_five_le _ (by omega)
        (QuadForm.nondegenerate_orthSum hQ (QuadForm.nondegenerate_diag hc')) v)
  | infinite w =>
    change Q.RepresentsIn w.Completion (valProd Q F ys)
    have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    rcases isotropicIn_or_isSquare_mul Q w with hiso | hdef
    · exact representsIn_of_isotropicIn Q _ hQ _ hiso
    · obtain ⟨y₀, ys', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hodd.pos)
      set ι : (Fin n → F) → (Fin n → w.Completion) := fun y i => algebraMap F w.Completion (y i)
      have hι : ∀ y, Q.evalIn w.Completion (ι y) = algebraMap F _ (Q.evalIn F y) := fun y =>
        evalIn_map_tower Q w.Completion (K := F) y
      have hr : algebraMap F w.Completion (Q.evalIn F y₀) ≠ 0 :=
        (map_ne_zero _).mpr (hys y₀ List.mem_cons_self)
      have hsq := isSquare_prod_div (((y₀ :: ys').map (Q.evalIn F)).map (algebraMap F w.Completion)) hr
        (fun a ha => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
          have := hdef (ι y) (ι y₀) (by rw [hι]; exact (map_ne_zero _).mpr (hys y hy)) (by rw [hι]; exact hr)
          rwa [hι, hι] at this)
        (by rwa [List.length_map, List.length_map])
      obtain ⟨s, hs⟩ := hsq
      refine ⟨s • ι y₀, ?_⟩
      rw [evalIn_smul_sq, hι]
      rw [div_eq_iff hr] at hs
      have e : algebraMap F w.Completion (valProd Q F (y₀ :: ys')) =
          (((y₀ :: ys').map (Q.evalIn F)).map (algebraMap F w.Completion)).prod := by
        rw [valProd, map_list_prod]
      rw [e, hs]; ring

/-- **The correction step of O'Meara 104:4 (step 1c), proved without 95:1 and 101:9:** for $n \ge 4$, a finite set
$T$ of finite primes and $\varphi_\mathfrak p \in O'(V_\mathfrak p)$ ($\mathfrak p \in T$) there is $g \in O'(V)$ with
$g\varphi_\mathfrak p \in \Omega(V_\mathfrak p)$ for $\mathfrak p \in T$ and $g \in \Omega(V_\mathfrak p)$ for $\mathfrak p \notin T$
($\Omega$ = commutator subgroup). See the module docstring for the construction. -/
@[kb "omeara1963" "§104, proof of 104:4, step 1c, pp. 316–317"]
theorem exists_correction (hQ : Q.Nondegenerate) (hn : 4 ≤ n) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F))
    (hφ : ∀ v ∈ T, φ v ∈ spinorKernel Q (v.adicCompletion F)) :
    ∃ g ∈ spinorKernel Q F, (∀ v ∈ T, orthMap Q (v.adicCompletion F) g * φ v ∈
        commutator (↥(orthGroup Q (v.adicCompletion F)))) ∧
      ∀ v ∉ T, orthMap Q (v.adicCompletion F) g ∈ commutator (↥(orthGroup Q (v.adicCompletion F))) := by
  classical
  obtain ⟨e, -, he⟩ := exists_orthogonal_basis Q F hQ
  set u₀ := e ⟨0, by omega⟩
  have hu₀ : Q.evalIn F u₀ ≠ 0 := he _
  set A := (finite_anisotropic Q hQ (by omega)).toFinset
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (HeightOneSpectrum (𝓞 F)))
  set T' := insert v₀ (T ∪ A)
  set ψ : ∀ v : HeightOneSpectrum (𝓞 F), orthGroup Q (v.adicCompletion F) :=
    fun v => if v ∈ T then (φ v)⁻¹ else 1
  have hψ : ∀ v ∈ T', ψ v ∈ spinorKernel Q (v.adicCompletion F) := by
    intro v _
    simp only [ψ]
    split_ifs with h
    · exact Subgroup.inv_mem _ (hφ v h)
    · exact Subgroup.one_mem _
  choose! l hl hlprod using fun v (hv : v ∈ T') => hψ v hv
  set M := T'.sup fun v => (l v).length
  have hMeven : Even M := Finset.sup_induction (p := Even) (by simp) (fun a ha b hb => by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; exact hb
      · rw [max_eq_left h]; exact ha) fun v hv => (hl v hv).2.1
  set N := M + 2
  have hN : Even N := hMeven.add even_two
  have hN2 : 2 ≤ N := by show 2 ≤ M + 2; omega
  set l' : ∀ v : HeightOneSpectrum (𝓞 F), List (Fin n → v.adicCompletion F) :=
    fun v => l v ++ List.replicate (N - (l v).length) (locVec v u₀)
  have hloc₀ : ∀ v : HeightOneSpectrum (𝓞 F), Q.evalIn (v.adicCompletion F) (locVec v u₀) ≠ 0 := by
    intro v; rw [evalIn_locVec]; exact (map_ne_zero _).mpr hu₀
  have hpad : ∀ v ∈ T', IsSpinorWord Q _ (l' v) ∧ (l' v).length = N ∧ symmProd Q _ (l' v) = ψ v := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := isSpinorWord_pad Q _ (hl v hv) (hloc₀ v) hN
      ((Finset.le_sup (f := fun v => (l v).length) hv).trans (by omega))
    exact ⟨h1, h2, h3.trans (hlprod v hv)⟩
  have hsplit : ∀ v ∈ T', ∃ init : List (Fin n → v.adicCompletion F), ∃ last, l' v = init ++ [last] := by
    intro v hv
    rcases List.eq_nil_or_concat (l' v) with h | ⟨init, last, h⟩
    · have := (hpad v hv).2.1; rw [h] at this; simp at this
    · exact ⟨init, last, by rw [h, List.concat_eq_append]⟩
  choose! init last hil using hsplit
  obtain ⟨ys, hlen, hani, hrel⟩ := exists_list_approx Q T' ⟨v₀, Finset.mem_insert_self _ _⟩ (N - 1) init
    fun v hv => by
      have h2 := (hpad v hv).2.1
      rw [hil v hv, List.length_append, List.length_singleton] at h2
      refine ⟨by omega, fun x hx => (hpad v hv).1.1 x ?_⟩
      rw [hil v hv]; exact List.mem_append_left _ hx
  have hodd : Odd ys.length := by
    rw [hlen]; obtain ⟨k, hk⟩ := hN; exact ⟨k - 1, by omega⟩
  obtain ⟨y', hy'⟩ := representsIn_valProd Q hQ hn ys hani hodd
  set c := valProd Q F ys
  have hy'c : Q.evalIn F y' = c := by rw [hy']; rfl
  have hc : c ≠ 0 := by
    simp only [c, valProd]; exact List.prod_ne_zero (by
      intro h0; obtain ⟨y, hy, hy0⟩ := List.mem_map.mp h0; exact hani y hy hy0)
  set g := symmProd Q F (ys ++ [y'])
  have hg : g ∈ spinorKernel Q F := by
    refine ⟨ys ++ [y'], ⟨fun z hz => ?_, ?_, ⟨c, ?_⟩⟩, rfl⟩
    · rcases List.mem_append.mp hz with h | h
      · exact hani z h
      · rw [List.mem_singleton.mp h, hy'c]; exact hc
    · rw [List.length_append, List.length_singleton, hlen]; obtain ⟨k, hk⟩ := hN; exact ⟨k, by omega⟩
    · rw [valProd_append, show valProd Q F [y'] = c by simp [valProd, hy'c]]
  have key : ∀ v ∈ T', (ψ v)⁻¹ * orthMap Q (v.adicCompletion F) g ∈ eqPairGroup Q (v.adicCompletion F) := by
    intro v hv
    rw [← (hpad v hv).2.2, orthMap_symmProd, List.map_append, hil v hv]
    refine symmProd_inv_mul_mem_of_forall₂ Q _ (List.rel_append (hrel v hv) ?_)
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    have hw := (hpad v hv).1
    rw [hil v hv] at hw
    obtain ⟨hwa, -, hws⟩ := hw
    have hlast : Q.evalIn _ (last v) ≠ 0 := hwa _ (by simp)
    have hinit : valProd Q _ (init v) ≠ 0 := by
      rw [valProd]; exact List.prod_ne_zero (by
        intro h0; obtain ⟨y, hy, hy0⟩ := List.mem_map.mp h0
        exact hwa y (List.mem_append_left _ hy) hy0)
    have hlv : Q.evalIn (v.adicCompletion F) (locVec v y') = algebraMap F _ c := by
      rw [evalIn_locVec]; exact congrArg _ hy'c
    refine ⟨hlast, by rw [hlv]; exact (map_ne_zero _).mpr hc, ?_⟩
    have h1 := isSquare_valProd_div_of_forall₂ Q _ (hrel v hv)
    rw [valProd_map_locVec] at h1
    rw [valProd_append] at hws
    have e : Q.evalIn (v.adicCompletion F) (locVec v y') / Q.evalIn _ (last v) =
        (algebraMap F _ c / valProd Q _ (init v)) *
          (valProd Q _ (init v) * valProd Q _ [last v] / (Q.evalIn _ (last v)) ^ 2) := by
      rw [hlv]; simp only [valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      field_simp
      exact (mul_div_cancel_right₀ _ hinit).symm
    rw [e]
    exact h1.mul (hws.div ⟨Q.evalIn _ (last v), by ring⟩)
  refine ⟨g, hg, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← eqPairGroup_eq_commutator Q _ hQ]
    have hk := key v (Finset.mem_insert_of_mem (Finset.mem_union_left _ hv))
    simp only [ψ, hv, ite_true, inv_inv] at hk
    have := (eqPairGroup_normal Q (v.adicCompletion F)).conj_mem _ hk (orthMap Q (v.adicCompletion F) g)
    rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this
  · rw [← eqPairGroup_eq_commutator Q _ hQ]
    by_cases hvT' : v ∈ T'
    · have hk := key v hvT'
      simp only [ψ, hv, ite_false, inv_one, one_mul] at hk
      exact hk
    · have hvA : v ∉ A := fun h => hvT' (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
      have hiso : Q.IsotropicIn (v.adicCompletion F) := by
        by_contra h; exact hvA ((Set.Finite.mem_toFinset _).mpr h)
      rw [← spinorKernel_eq_eqPairGroup Q _ hQ hiso]
      exact orthMap_mem_spinorKernel Q v hg

/-! ### Consequences -/

/-- **Step 1 of O'Meara 104:4 for $n \ge 4$ in general:** `VecApprox Q` implies `RotApprox Q` for every nondegenerate
$Q$ in $n \ge 4$ variables (no isotropy hypothesis on the $V_\mathfrak p$; the correction is `exists_correction`). -/
@[kb "omeara1963" "§104, proof of 104:4, step 1c, pp. 316–317"]
theorem rotApprox_of_vecApprox_of_four_le (hQ : Q.Nondegenerate) (hn : 4 ≤ n) (hV : VecApprox Q) : RotApprox Q :=
  rotApprox_of_vecApprox_of_correction Q hQ (by omega) hV fun T φ hφ => exists_correction Q hQ hn T φ hφ

/-- **Strong approximation for rotations from `VecStrongApproximation F` alone** (O'Meara 1973, 104:4 and 104:5):
the named input `QuaternarySpinorInput F` (95:1, 101:9) is not needed, by `exists_correction`. -/
@[kb "omeara1963" "§104, 104:4, 104:5, pp. 315–319"]
theorem strongApproximationSpin_of_vecInput (hV : VecStrongApproximation F) : StrongApproximationSpin F := by
  refine strongApproximationSpin_of_spinApprox fun {n} Q hn hQ hind => spinApprox_of_rotApprox Q ?_
  rcases Nat.lt_or_ge n 4 with h3 | h4
  · obtain rfl : n = 3 := by omega
    exact rotApprox_ternary_of hQ fun a b ha hb hI =>
      vecApprox_of_input hV le_rfl (Quat.nrdForm_nondegenerate two_ne_zero ha hb) (isIndefinite_nrdForm hI hind)
  · exact rotApprox_of_vecApprox_of_four_le Q hQ h4 (vecApprox_of_input hV h4 hQ hind)

end QuadFormsKB.Lattices
