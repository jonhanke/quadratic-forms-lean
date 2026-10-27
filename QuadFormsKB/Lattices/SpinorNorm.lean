/-
# The spinor norm $\theta : O(V) \to K^\times/K^{\times 2}$

**Layer:** $V = K^n$ with the form $Q$ = `Q : QuadForm F n` over a field $K \supseteq F$ of characteristic $0$, the
symmetries $\tau_x$ and the spinor kernel $O'(V)(K)$ (`Lattices/SpinorKernel.lean`), Cartan–Dieudonné
(`Lattices/CartanDieudonne.lean`), and Mathlib's Clifford algebra `CliffordAlgebra` of the Mathlib form
`Q.toQuadraticFormIn K` (`Witt/Bridge.lean`).

**Proves**
* `isSquare_valProd_of_symmProd_eq_one` (**well-definedness**): if $\tau_{x_1}\cdots\tau_{x_r} = 1$ with all $Q(x_i) \ne 0$
  and $Q$ nondegenerate, then $Q(x_1)\cdots Q(x_r) \in K^{\times 2}$ (O'Meara 1963, 54:6, p. 136, as used in §55, p. 137);
* `spinorNormHom`: the **spinor norm** $\theta : O(V)(K) \to K^\times/K^{\times 2}$ (`SqClass K`), a group homomorphism with
  $\theta(\tau_{x_1}\cdots\tau_{x_r}) = Q(x_1)\cdots Q(x_r)\,K^{\times 2}$ (`spinorNorm_symmProd`, `spinorNorm_symm`);
* `spinorKernel_eq_ker`: $O'(V)(K) = \ker\theta \cap SO(V)(K)$, i.e. the definition of `spinorKernel` by spinor words
  agrees with O'Meara's $O'(V) = \ker(\theta|_{O^+(V)})$;
* `sq_mem_spinorKernel`, `commutator_mem_spinorKernel`: squares and commutators of $O(V)(K)$ lie in $O'(V)(K)$, so
  $O(V)/O'(V)$ is an elementary abelian $2$-group.

*Proof of well-definedness* (Clifford algebra $C(V)$, $\iota : V \to C(V)$, grade involution $\alpha$, reversion $^t$).
For $g = \iota(x_1)\cdots\iota(x_r)$: $\alpha(g)\,\iota(z) = \iota(\tau_{x_1}\cdots\tau_{x_r}z)\,g$ (`involute_cw_mul_ι`, from
$-\iota(x)\iota(z) = \iota(\tau_x z)\iota(x)$) and $g^t g = Q(x_1)\cdots Q(x_r)$ (`reverse_cw_mul_cw`). If the product of
symmetries is $1$, then $\alpha(g)\iota(e_j) = \iota(e_j) g$ for an orthogonal basis $(e_j)$, which forces $g \in K$
(`mem_range_algebraMap_of_twisted`): $C(V)$ is spanned by the words $e_{j_1}\cdots e_{j_k}$ (`mem_span_bw`), the
operators $T_j(z) = Q(e_j)^{-1}e_j\,\alpha(z)\,e_j$ act on a word by $(-1)^{\#\{i : j_i = j\}}$, so the projection
$\prod_j \tfrac12(1 + T_j)$ fixes $g$ and kills every word in which some $e_j$ occurs an odd number of times, and a word in
which every $e_j$ occurs an even number of times is a scalar. (Only spanning is needed, not the linear independence
of the words.) Then $g = c \in K$ and $c^2 = g^tg = \prod Q(x_i)$. Mathlib's `lipschitzGroup`, `pinGroup`, `spinGroup`
(`Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup.lean`) do not contain this kernel computation.
-/
import QuadFormsKB.Lattices.CartanDieudonne
import QuadFormsKB.Witt.Bridge

open Matrix CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

variable (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] [CharZero K]

/-- The Mathlib quadratic form $x \mapsto Q(x)$ on $K^n$. -/
abbrev qk : QuadraticForm K (Fin n → K) := Q.toQuadraticFormIn K

theorem qk_apply (x : Fin n → K) : qk Q K x = Q.evalIn K x := QuadForm.toQuadraticFormIn_apply K Q x

theorem polar_qk (x y : Fin n → K) : QuadraticMap.polar (qk Q K) x y = qbil Q K x y := by
  simp only [QuadraticMap.polar, qk_apply]
  exact QuadForm.polar_eq_hessian K Q x y

/-! ### Clifford words in vectors -/

/-- $-\iota(x)\iota(z) = \iota(\tau_x z)\,\iota(x)$ for anisotropic $x$. -/
@[kb "cassels1978" "Ch. 10, (3.2), p. 176"]
theorem neg_ι_mul_ι {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) (z : Fin n → K) :
    -(ι (qk Q K) x * ι (qk Q K) z) =
      ι (qk Q K) (((symm Q K x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) * ι (qk Q K) x := by
  rw [symm_mulVec_bil Q K hx, map_sub, map_smul, sub_mul, smul_mul_assoc, ι_sq_scalar, qk_apply,
    Algebra.smul_def, ← RingHom.map_mul, div_mul_cancel₀ _ hx, ι_mul_ι_comm, polar_qk]
  abel

/-- The Clifford word $\iota(x_1)\cdots\iota(x_r)$. -/
def cw (xs : List (Fin n → K)) : CliffordAlgebra (qk Q K) := (xs.map (ι (qk Q K))).prod

/-- **Twisted conjugation by a word:** $\alpha(g)\,\iota(z) = \iota(\tau_{x_1}\cdots\tau_{x_r}z)\,g$. -/
theorem involute_cw_mul_ι (xs : List (Fin n → K)) (hxs : ∀ x ∈ xs, Q.evalIn K x ≠ 0) (z : Fin n → K) :
    involute (cw Q K xs) * ι (qk Q K) z =
      ι (qk Q K) (((symmProd Q K xs : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) * cw Q K xs := by
  induction xs generalizing z with
  | nil => simp [cw, symmProd]
  | cons x xs ih =>
    have hx := hxs x List.mem_cons_self
    have ih' := ih (fun y hy => hxs y (List.mem_cons_of_mem x hy))
    simp only [cw, List.map_cons, List.prod_cons, map_mul, involute_ι] at ih' ⊢
    rw [symmProd_mulVec_cons, mul_assoc, ih', neg_mul, ← mul_assoc, ← neg_mul, neg_ι_mul_ι Q K hx, mul_assoc]

/-- **The norm of a word:** $g^t g = Q(x_1)\cdots Q(x_r)$. -/
theorem reverse_cw_mul_cw (xs : List (Fin n → K)) :
    reverse (cw Q K xs) * cw Q K xs = algebraMap K _ (valProd Q K xs) := by
  induction xs with
  | nil => simp [cw, valProd]
  | cons x xs ih =>
    simp only [cw, List.map_cons, List.prod_cons, reverse.map_mul, reverse_ι] at ih ⊢
    rw [show reverse (List.map (ι (qk Q K)) xs).prod * ι (qk Q K) x * (ι (qk Q K) x * (List.map (ι (qk Q K)) xs).prod)
        = reverse (List.map (ι (qk Q K)) xs).prod * (ι (qk Q K) x * ι (qk Q K) x) * (List.map (ι (qk Q K)) xs).prod
        by simp only [mul_assoc], ι_sq_scalar, qk_apply, ← Algebra.commutes, mul_assoc, ih, ← map_mul]
    simp [valProd]

/-! ### Words in an orthogonal basis -/

section Basis

variable {K} (e : Module.Basis (Fin n) K (Fin n → K))

/-- $u_j = \iota(e_j)$. -/
abbrev ub (j : Fin n) : CliffordAlgebra (qk Q K) := ι (qk Q K) (e j)

/-- The word $u_{j_1}\cdots u_{j_k}$ in the basis vectors. -/
def bw (l : List (Fin n)) : CliffordAlgebra (qk Q K) := (l.map (ub Q e)).prod

theorem bw_nil : bw Q e [] = (1 : CliffordAlgebra (qk Q K)) := rfl

theorem bw_cons (i : Fin n) (l : List (Fin n)) : bw Q e (i :: l) = ub Q e i * bw Q e l := rfl

theorem bw_append (l l' : List (Fin n)) : bw Q e (l ++ l') = bw Q e l * bw Q e l' := by
  simp [bw]

variable (he : ∀ i j, i ≠ j → qbil Q K (e i) (e j) = 0)
include he

theorem ub_anticomm {i j : Fin n} (hij : i ≠ j) : ub Q e j * ub Q e i = -(ub Q e i * ub Q e j) := by
  rw [ι_mul_ι_comm, polar_qk, he j i hij.symm, map_zero, zero_sub]

/-- $u_j\,w = (-1)^{|l| + \#_j(l)}\,w\,u_j$ for the word $w = u_l$. -/
theorem ub_mul_bw (j : Fin n) (l : List (Fin n)) :
    ub Q e j * bw Q e l = (-1 : K) ^ (l.length + l.count j) • (bw Q e l * ub Q e j) := by
  induction l with
  | nil => simp [bw_nil]
  | cons i l ih =>
    rw [bw_cons, ← mul_assoc]
    by_cases hij : i = j
    · subst hij
      rw [ι_sq_scalar, ih, smul_mul_assoc, mul_assoc, ι_sq_scalar, smul_smul, ← Algebra.commutes]
      simp only [List.length_cons, List.count_cons_self]
      rw [← pow_add, show l.length + 1 + (l.count i + 1) + (l.length + l.count i) =
        2 * (l.length + l.count i + 1) by ring, pow_mul]
      simp
    · rw [ub_anticomm Q e he hij, neg_mul, mul_assoc, ih, mul_smul_comm, ← mul_assoc]
      simp only [List.length_cons, List.count_cons, beq_iff_eq, hij, ite_false, add_zero]
      rw [show l.length + 1 + l.count j = l.length + l.count j + 1 by ring, pow_succ, mul_neg_one, neg_smul]

omit he in
theorem involute_bw (l : List (Fin n)) : involute (bw Q e l) = (-1 : K) ^ l.length • bw Q e l := by
  induction l with
  | nil => simp [bw_nil]
  | cons i l ih =>
    rw [bw_cons, map_mul, ih, involute_ι, List.length_cons, pow_succ']
    simp

/-- $u_j\,\alpha(u_l)\,u_j = (-1)^{\#_j(l)}Q(e_j)\,u_l$. -/
theorem ub_mul_involute_bw_mul_ub (j : Fin n) (l : List (Fin n)) :
    ub Q e j * (involute (bw Q e l) * ub Q e j) = ((-1 : K) ^ l.count j * Q.evalIn K (e j)) • bw Q e l := by
  rw [involute_bw, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ub_mul_bw Q e he, smul_mul_assoc, mul_assoc,
    ι_sq_scalar, qk_apply, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, smul_smul]
  congr 1
  rw [pow_add, show (-1 : K) ^ l.length * ((-1) ^ l.length * (-1) ^ l.count j) =
    ((-1) ^ l.length) ^ 2 * (-1) ^ l.count j by ring, ← pow_mul, mul_comm l.length 2, pow_mul]
  simp

end Basis

/-! ### The twisted center is $K$ -/

section Center

variable {K} (e : Module.Basis (Fin n) K (Fin n → K))

/-- **Every element of $C(V)$ is a combination of basis words.** -/
theorem mem_span_bw (g : CliffordAlgebra (qk Q K)) : g ∈ Submodule.span K (Set.range (bw Q e)) := by
  induction g using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], rfl⟩)
  | ι v =>
    rw [← e.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[i], by simp [bw]⟩)
  | mul a b ha hb =>
    have := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨l', rfl⟩, rfl⟩
    exact ⟨l ++ l', bw_append Q e l l'⟩
  | add a b ha hb => exact Submodule.add_mem _ ha hb

/-- The averaging operator $P_j = \tfrac12(1 + T_j)$, $T_j(z) = Q(e_j)^{-1}u_j\,\alpha(z)\,u_j$. -/
def Pj (j : Fin n) : CliffordAlgebra (qk Q K) →ₗ[K] CliffordAlgebra (qk Q K) :=
  (1 / 2 : K) • (LinearMap.id + (Q.evalIn K (e j))⁻¹ •
    (LinearMap.mulLeft K (ub Q e j) ∘ₗ LinearMap.mulRight K (ub Q e j) ∘ₗ
      (involute : CliffordAlgebra (qk Q K) →ₐ[K] _).toLinearMap))

theorem Pj_apply (j : Fin n) (z : CliffordAlgebra (qk Q K)) :
    Pj Q e j z = (1 / 2 : K) • (z + (Q.evalIn K (e j))⁻¹ • (ub Q e j * (involute z * ub Q e j))) := by
  rfl

variable (he : ∀ i j, i ≠ j → qbil Q K (e i) (e j) = 0) (hea : ∀ i, Q.evalIn K (e i) ≠ 0)
include he hea

/-- **A word in which every basis vector occurs an even number of times is a scalar.** -/
theorem bw_mem_range_of_even (l : List (Fin n)) (hl : ∀ j, Even (l.count j)) :
    bw Q e l ∈ Set.range (algebraMap K (CliffordAlgebra (qk Q K))) := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ m ih =>
    match l, hl with
    | [], _ => exact ⟨1, by simp [bw_nil]⟩
    | i :: l', hl =>
      have hodd : ¬ Even (l'.count i) := by
        have := hl i
        rw [List.count_cons_self, Nat.even_add_one] at this
        exact this
      have hmem : i ∈ l' := List.count_pos_iff.mp (Nat.pos_of_ne_zero fun h0 => hodd (h0 ▸ (⟨0, rfl⟩ : Even 0)))
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
      have hst : ∀ j, Even ((s ++ t).count j) := by
        intro j
        have := hl j
        simp only [List.count_cons, List.count_append, beq_iff_eq] at this ⊢
        by_cases hj : i = j
        · subst hj
          simp only [ite_true] at this
          rw [show s.count i + (t.count i + 1) + 1 = s.count i + t.count i + 2 by ring] at this
          exact (Nat.even_add.mp this).mpr even_two
        · simp only [hj, ite_false, add_zero] at this
          exact this
      obtain ⟨c, hc⟩ := ih (s ++ t).length (by rw [← h]; simp) (s ++ t) hst rfl
      have key : bw Q e (i :: (s ++ i :: t)) =
          ((-1 : K) ^ (s.length + s.count i) * Q.evalIn K (e i)) • bw Q e (s ++ t) := by
        rw [bw_cons, bw_append, bw_cons, ← mul_assoc, ub_mul_bw Q e he, smul_mul_assoc, mul_assoc,
          ← mul_assoc (ub Q e i), ι_sq_scalar, qk_apply, ← mul_assoc, ← Algebra.commutes, mul_assoc,
          ← Algebra.smul_def, ← bw_append, smul_smul]
      refine ⟨(-1 : K) ^ (s.length + s.count i) * Q.evalIn K (e i) * c, ?_⟩
      rw [key, ← hc, Algebra.smul_def, ← RingHom.map_mul]

theorem Pj_bw (j : Fin n) (l : List (Fin n)) :
    Pj Q e j (bw Q e l) = if Even (l.count j) then bw Q e l else 0 := by
  rw [Pj_apply, ub_mul_involute_bw_mul_ub Q e he, smul_smul, mul_comm ((-1 : K) ^ l.count j),
    inv_mul_cancel_left₀ (hea j)]
  split_ifs with hc
  · rw [hc.neg_one_pow, one_smul, ← two_smul K, smul_smul]; norm_num
  · rw [(Nat.not_even_iff_odd.mp hc).neg_one_pow, neg_one_smul, add_neg_cancel, smul_zero]

theorem Pj_of_twisted {g : CliffordAlgebra (qk Q K)} (j : Fin n)
    (hg : involute g * ub Q e j = ub Q e j * g) : Pj Q e j g = g := by
  rw [Pj_apply, hg, ← mul_assoc, ι_sq_scalar, qk_apply, ← Algebra.smul_def, smul_smul,
    inv_mul_cancel₀ (hea j), one_smul, ← two_smul K, smul_smul]
  norm_num

/-- **The twisted center of $C(V)$ is $K$:** if $\alpha(g)\,\iota(e_j) = \iota(e_j)\,g$ for every vector $e_j$ of an
orthogonal basis of anisotropic vectors, then $g \in K$. -/
@[kb "cassels1978" "Ch. 10, Lemma 2.3, p. 174"]
theorem mem_range_algebraMap_of_twisted (g : CliffordAlgebra (qk Q K))
    (hg : ∀ j, involute g * ub Q e j = ub Q e j * g) :
    g ∈ Set.range (algebraMap K (CliffordAlgebra (qk Q K))) := by
  let S : ℕ → Submodule K (CliffordAlgebra (qk Q K)) := fun k =>
    Submodule.span K {w | ∃ l : List (Fin n), (∀ j : Fin n, j.val < k → Even (l.count j)) ∧ bw Q e l = w}
  have step : ∀ k ≤ n, g ∈ S k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine Submodule.span_mono ?_ (mem_span_bw Q e g)
      rintro _ ⟨l, rfl⟩
      exact ⟨l, fun j hj => absurd hj (Nat.not_lt_zero _), rfl⟩
    | succ k ih =>
      intro hk
      have hg' := ih (Nat.le_of_succ_le hk)
      rw [← Pj_of_twisted Q e he hea ⟨k, hk⟩ (hg _)]
      have : Pj Q e ⟨k, hk⟩ g ∈ (S k).map (Pj Q e ⟨k, hk⟩) := Submodule.mem_map_of_mem hg'
      rw [Submodule.map_span] at this
      refine Submodule.span_le.mpr ?_ this
      rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, Pj_bw Q e he hea]
      split_ifs with hc
      · refine Submodule.subset_span ⟨l, fun j hj => ?_, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact hl j hj
        · have : j = ⟨k, hk⟩ := Fin.ext hj
          rw [this]; exact hc
      · exact Submodule.zero_mem _
  have hn := step n le_rfl
  have hle : S n ≤ LinearMap.range (Algebra.linearMap K (CliffordAlgebra (qk Q K))) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨c, hc⟩ := bw_mem_range_of_even Q e he hea l fun j => hl j j.2
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hle hn
  exact ⟨c, hc⟩

end Center

/-! ### Well-definedness of the spinor norm -/

/-- **The spinor norm is well defined** (O'Meara 1963, 54:6, p. 136, as used in §55, p. 137): if $Q$ is nondegenerate, $Q(x_i) \ne 0$ and
$\tau_{x_1}\cdots\tau_{x_r} = 1$, then $Q(x_1)\cdots Q(x_r)$ is a square in $K$.

*Update (simplification):* the Clifford-algebra proof needs only that $C(V)$ is spanned by
the basis words, not the basis theorem $\dim C(V) = 2^n$ (`mem_range_algebraMap_of_twisted`). -/
@[kb "omeara1963" "§55, p. 137 (well-definedness of the spinor norm, via 54:6)"]
theorem isSquare_valProd_of_symmProd_eq_one (hQ : Q.Nondegenerate) (xs : List (Fin n → K))
    (hxs : ∀ x ∈ xs, Q.evalIn K x ≠ 0) (h1 : symmProd Q K xs = 1) : IsSquare (valProd Q K xs) := by
  have : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨e, he, hea⟩ := exists_orthogonal_basis Q K hQ
  have htw : ∀ j, involute (cw Q K xs) * ub Q e j = ub Q e j * cw Q K xs := by
    intro j
    rw [involute_cw_mul_ι Q K xs hxs, h1]
    simp
  obtain ⟨c, hc⟩ := mem_range_algebraMap_of_twisted Q e he hea _ htw
  have h := reverse_cw_mul_cw Q K xs
  rw [← hc, reverse.commutes, ← map_mul] at h
  exact ⟨c, ((algebraMap K (CliffordAlgebra (qk Q K))).injective h).symm⟩

/-! ### The spinor norm homomorphism -/

/-- **The square-class group** $K^\times/K^{\times 2}$. -/
def SqClass (K : Type*) [Field K] : Type _ := Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range

instance (K : Type*) [Field K] : CommGroup (SqClass K) := QuotientGroup.Quotient.commGroup _

/-- The class $xK^{\times 2}$ of a unit $x \in K^\times$. -/
def SqClass.mk {K : Type*} [Field K] (x : Kˣ) : SqClass K :=
  (QuotientGroup.mk x : Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range)

open scoped Classical in
/-- **The square class** $aK^{\times 2}$ of $a \in K^\times$ (and $1$ for $a = 0$, by convention). -/
def sqClassOf {K : Type*} [Field K] (a : K) : SqClass K :=
  if h : a = 0 then 1 else SqClass.mk (Units.mk0 a h)

section SqClass

variable {K}

theorem SqClass.mk_mul (x y : Kˣ) : SqClass.mk (x * y) = SqClass.mk x * SqClass.mk y := rfl

theorem SqClass.mk_eq_one_iff (x : Kˣ) : SqClass.mk x = 1 ↔ ∃ y : Kˣ, y ^ 2 = x :=
  (QuotientGroup.eq_one_iff (N := (powMonoidHom 2 : Kˣ →* Kˣ).range) x).trans (by simp)

theorem SqClass.ind {P : SqClass K → Prop} (h : ∀ x, P (SqClass.mk x)) (c : SqClass K) : P c :=
  Quotient.inductionOn' c h

theorem sqClassOf_of_ne_zero {a : K} (ha : a ≠ 0) : sqClassOf a = SqClass.mk (Units.mk0 a ha) := by
  simp [sqClassOf, ha]

theorem sqClassOf_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : sqClassOf (a * b) = sqClassOf a * sqClassOf b := by
  rw [sqClassOf_of_ne_zero ha, sqClassOf_of_ne_zero hb, sqClassOf_of_ne_zero (mul_ne_zero ha hb),
    ← SqClass.mk_mul]
  congr 1
  ext; simp

theorem sqClassOf_one : sqClassOf (1 : K) = 1 := by
  rw [sqClassOf_of_ne_zero one_ne_zero, SqClass.mk_eq_one_iff]
  exact ⟨1, by ext; simp⟩

theorem sqClassOf_eq_one_iff {a : K} (ha : a ≠ 0) : sqClassOf a = 1 ↔ IsSquare a := by
  rw [sqClassOf_of_ne_zero ha, SqClass.mk_eq_one_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have := congrArg Units.val hy
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    rw [← this, sq]
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := fun h => ha (by rw [h, mul_zero])
    exact ⟨Units.mk0 r hr, by ext; simp [sq]⟩

/-- Every square class has order dividing $2$. -/
theorem SqClass.mul_self (c : SqClass K) : c * c = 1 := by
  induction c using SqClass.ind with
  | h x =>
    rw [← SqClass.mk_mul, SqClass.mk_eq_one_iff]
    exact ⟨x, by simp [sq]⟩

theorem SqClass.inv_eq (c : SqClass K) : c⁻¹ = c := inv_eq_of_mul_eq_one_right (SqClass.mul_self c)

end SqClass

theorem valProd_ne_zero {xs : List (Fin n → K)} (hxs : ∀ x ∈ xs, Q.evalIn K x ≠ 0) : valProd Q K xs ≠ 0 := by
  induction xs with
  | nil => simp [valProd]
  | cons x xs ih =>
    have : valProd Q K (x :: xs) = Q.evalIn K x * valProd Q K xs := by simp [valProd]
    rw [this]
    exact mul_ne_zero (hxs x List.mem_cons_self) (ih fun y hy => hxs y (List.mem_cons_of_mem x hy))

/-- Two symmetry factorizations of the same isometry give the same square class. -/
theorem sqClassOf_valProd_eq (hQ : Q.Nondegenerate) {xs ys : List (Fin n → K)}
    (hxs : ∀ x ∈ xs, Q.evalIn K x ≠ 0) (hys : ∀ y ∈ ys, Q.evalIn K y ≠ 0)
    (h : symmProd Q K xs = symmProd Q K ys) :
    sqClassOf (valProd Q K xs) = sqClassOf (valProd Q K ys) := by
  have h1 : symmProd Q K (xs ++ ys.reverse) = 1 := by
    rw [symmProd_append, symmProd_reverse, h, mul_inv_cancel]
  have hall : ∀ z ∈ xs ++ ys.reverse, Q.evalIn K z ≠ 0 := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    exacts [hxs z hz, hys z (List.mem_reverse.mp hz)]
  have hsq := isSquare_valProd_of_symmProd_eq_one Q K hQ _ hall h1
  rw [valProd_append, valProd_reverse] at hsq
  have hx := valProd_ne_zero Q K hxs
  have hy := valProd_ne_zero Q K hys
  rw [← sqClassOf_eq_one_iff (mul_ne_zero hx hy), sqClassOf_mul hx hy] at hsq
  rw [eq_inv_of_mul_eq_one_left hsq, SqClass.inv_eq]

open scoped Classical in
/-- **The spinor norm** $\theta(\sigma) = Q(x_1)\cdots Q(x_r)\,K^{\times 2}$ for any factorization
$\sigma = \tau_{x_1}\cdots\tau_{x_r}$ into symmetries (O'Meara 1963, §55, p. 137). For nondegenerate $Q$ such a
factorization exists (`exists_symmProd_eq`) and the class does not depend on it (`sqClassOf_valProd_eq`). -/
@[kb "omeara1963" "§55, p. 137 (spinor norm θ)"]
def spinorNorm (σ : orthGroup Q K) : SqClass K :=
  if h : ∃ xs : List (Fin n → K), (∀ x ∈ xs, Q.evalIn K x ≠ 0) ∧ symmProd Q K xs = σ then
    sqClassOf (valProd Q K h.choose) else 1

/-- $\theta(\tau_{x_1}\cdots\tau_{x_r}) = Q(x_1)\cdots Q(x_r)\,K^{\times 2}$. -/
@[kb "omeara1963" "§55, p. 137"]
theorem spinorNorm_symmProd (hQ : Q.Nondegenerate) (xs : List (Fin n → K))
    (hxs : ∀ x ∈ xs, Q.evalIn K x ≠ 0) : spinorNorm Q K (symmProd Q K xs) = sqClassOf (valProd Q K xs) := by
  have hex : ∃ ys : List (Fin n → K), (∀ y ∈ ys, Q.evalIn K y ≠ 0) ∧ symmProd Q K ys = symmProd Q K xs :=
    ⟨xs, hxs, rfl⟩
  unfold spinorNorm
  rw [dif_pos hex]
  exact sqClassOf_valProd_eq Q K hQ hex.choose_spec.1 hxs hex.choose_spec.2

/-- $\theta(\tau_x) = Q(x)\,K^{\times 2}$. -/
@[kb "omeara1963" "§55, p. 137"]
theorem spinorNorm_symm (hQ : Q.Nondegenerate) {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    spinorNorm Q K (symm Q K x) = sqClassOf (Q.evalIn K x) := by
  have := spinorNorm_symmProd Q K hQ [x] (by simpa using hx)
  simpa [symmProd, valProd] using this

/-- **The spinor norm is a homomorphism** $\theta : O(V)(K) \to K^\times/K^{\times 2}$ for nondegenerate $Q$
(O'Meara 1963, §55, p. 137). -/
@[kb "omeara1963" "§55, p. 137 (θ(στ) = θ(σ)θ(τ))"]
def spinorNormHom (hQ : Q.Nondegenerate) : orthGroup Q K →* SqClass K where
  toFun := spinorNorm Q K
  map_one' := by
    have := spinorNorm_symmProd Q K hQ [] (by simp)
    simpa [symmProd, valProd, sqClassOf_one] using this
  map_mul' σ τ := by
    obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q K hQ σ
    obtain ⟨ys, hys, rfl⟩ := exists_symmProd_eq Q K hQ τ
    have hall : ∀ z ∈ xs ++ ys, Q.evalIn K z ≠ 0 := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      exacts [hxs z hz, hys z hz]
    rw [← symmProd_append, spinorNorm_symmProd Q K hQ _ hall, spinorNorm_symmProd Q K hQ _ hxs,
      spinorNorm_symmProd Q K hQ _ hys, valProd_append,
      sqClassOf_mul (valProd_ne_zero Q K hxs) (valProd_ne_zero Q K hys)]

theorem spinorNormHom_apply (hQ : Q.Nondegenerate) (σ : orthGroup Q K) :
    spinorNormHom Q K hQ σ = spinorNorm Q K σ := rfl

/-- The determinant $O(V)(K) \to K^\times$. -/
def detHom : orthGroup Q K →* Kˣ := Matrix.GeneralLinearGroup.det.comp (orthGroup Q K).subtype

theorem detHom_val (σ : orthGroup Q K) :
    (detHom Q K σ : K) = ((σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := rfl

theorem detHom_symmProd (xs : List (Fin n → K)) (hxs : ∀ x ∈ xs, Q.evalIn K x ≠ 0) :
    (detHom Q K (symmProd Q K xs) : K) = (-1) ^ xs.length := by
  induction xs with
  | nil => simp [symmProd]
  | cons x xs ih =>
    have hx := hxs x List.mem_cons_self
    have ih' := ih fun y hy => hxs y (List.mem_cons_of_mem x hy)
    have e : symmProd Q K (x :: xs) = symm Q K x * symmProd Q K xs := by simp [symmProd]
    rw [e, map_mul, Units.val_mul, ih', detHom_val, symm_det Q K hx, List.length_cons, pow_succ']

/-- **$O'(V) = \ker\theta \cap SO(V)$** (O'Meara 1963, §55, p. 137): the spinor kernel defined by spinor words
(`spinorKernel`) is the kernel of the spinor norm on the rotations. -/
@[kb "omeara1963" "§55, p. 137 (O'(V) = ker θ on O⁺(V))"]
theorem spinorKernel_eq_ker (hQ : Q.Nondegenerate) :
    spinorKernel Q K = (spinorNormHom Q K hQ).ker ⊓ (detHom Q K).ker := by
  ext σ
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, spinorNormHom_apply]
  constructor
  · rintro ⟨xs, ⟨hxa, hxe, hxs⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [spinorNorm_symmProd Q K hQ xs hxa, sqClassOf_eq_one_iff (valProd_ne_zero Q K hxa)]
      exact hxs
    · ext
      rw [detHom_symmProd Q K xs hxa, hxe.neg_one_pow, Units.val_one]
  · rintro ⟨hθ, hdet⟩
    obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q K hQ σ
    refine ⟨xs, ⟨hxs, ?_, ?_⟩, rfl⟩
    · have := congrArg Units.val hdet
      rw [detHom_symmProd Q K xs hxs, Units.val_one] at this
      by_contra hodd
      rw [(Nat.not_even_iff_odd.mp hodd).neg_one_pow] at this
      exact absurd this (by norm_num)
    · rw [spinorNorm_symmProd Q K hQ xs hxs, sqClassOf_eq_one_iff (valProd_ne_zero Q K hxs)] at hθ
      exact hθ

/-- **Squares of isometries are spinor-kernel elements**: $\sigma^2 \in O'(V)$. -/
theorem sq_mem_spinorKernel (hQ : Q.Nondegenerate) (σ : orthGroup Q K) : σ ^ 2 ∈ spinorKernel Q K := by
  rw [spinorKernel_eq_ker Q K hQ]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_pow, sq, SqClass.mul_self]
  · rw [MonoidHom.mem_ker, map_pow]
    obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q K hQ σ
    ext
    rw [Units.val_pow_eq_pow_val, detHom_symmProd Q K xs hxs, ← pow_mul, mul_comm, pow_mul]
    simp

/-- **Commutators of isometries are spinor-kernel elements**: $O(V)/O'(V)$ is abelian. -/
@[kb "cassels1978" "Ch. 10, Thm. 3.2, p. 179 (Ω ⊆ Θ)"]
theorem commutator_mem_spinorKernel (hQ : Q.Nondegenerate) (σ τ : orthGroup Q K) :
    σ * τ * σ⁻¹ * τ⁻¹ ∈ spinorKernel Q K := by
  rw [spinorKernel_eq_ker Q K hQ]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩ <;>
  · rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, mul_inv_cancel_comm, mul_inv_cancel]

end QuadFormsKB.Lattices
