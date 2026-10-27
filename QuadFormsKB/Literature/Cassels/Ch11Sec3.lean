/-
# Cassels, Chapter 11, §3: the spinor norms of $V_p$ and of $V$; genus = spinor genus

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n` (Cassels: $F = \mathbb Q$);
rotations `Tamagawa.soSub` ($O^+$), the spinor norm `spinorNorm`, $\theta(O^+(V))$ = `spinorNormGroup`
(`Literature/OMeara/Sec101B.lean`), $\theta(O^+(L_\mathfrak p))$ = `localSpinorNormGroup`
(`Literature/OMeara/Sec101D.lean`), the proper spinor genus `SameProperSpinorGenus` (Cassels' spinor genus, see
`Literature/Cassels/Ch11Sec1.lean`).

**Proves**
* Lemma 3.1 (p. 207): for $n \ge 3$, every element of $F_\mathfrak p^\times$ is the spinor norm of a rotation of
  $V_\mathfrak p$ (`exists_soSub_spinorNorm_eq_local`), at every finite prime of a number field.
* Lemma 3.2 (pp. 207–208): for $n \ge 3$, $\theta(O^+(V))$ consists of the $a \in F^\times$ that are squares at every
  infinite place where $V$ is anisotropic (`mem_spinorNormGroup_iff`); over $\mathbb Q$:
  $\theta(V) = \mathbb Q^\times$ if $V_\infty$ is indefinite and $\theta(V) = \mathbb Q_+$ if it is definite
  (`mem_spinorNormGroup_rat_iff`).
* Lemma 3.6, Corollary (p. 213): if $U_p \subseteq \theta(\Lambda_p)$ for every $p$, the genus of $\Lambda$ is a
  single (proper) spinor genus (`sameProperSpinorGenus_of_sameGenus_rat`, over $\mathbb Q$ for every $Q$ of
  dimension $n \ge 3$, definite or not; `sameProperSpinorGenus_of_sameGenus_of_units` over a number field whose ring
  of integers is a principal ideal domain, under the hypothesis that every nonzero integer is a unit times an element
  of $\theta(O^+(V))$, which holds over $\mathbb Q$ and for indefinite $V$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec1
import QuadFormsKB.Lattices.SpinorGlobal
import QuadFormsKB.Tamagawa.LocalRankFive

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### Helpers: $Q(x) = aQ(y)$ from isotropy of $Q \perp (-a)Q$, and the rotation $\tau_x\tau_y$ -/

/-- Evaluation of a diagonal form with an appended coefficient vector (over a field $K$ as its own base). -/
theorem evalIn_diag_append_self {K : Type*} [Field K] {m : ℕ} (b c : Fin m → K) (z : Fin (m + m) → K) :
    (QuadForm.diag (Fin.append b c)).evalIn K z =
      (QuadForm.diag b).evalIn K (fun i => z (Fin.castAdd m i)) +
        (QuadForm.diag c).evalIn K (fun i => z (Fin.natAdd m i)) := by
  rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag, QuadForm.evalIn_diag, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **From isotropy of $\langle b\rangle \perp \langle -ab\rangle$ to $Q(x) = aQ(y)$** (over any field $K$ of
characteristic $0$, $m \ge 1$, $b_i \ne 0$, $a \ne 0$): if the diagonal form with coefficients $b_0,\dots,b_{m-1},
-ab_0,\dots,-ab_{m-1}$ is isotropic, then $\langle b\rangle(x) = a\langle b\rangle(y)$ with $\langle b\rangle(y) \ne 0$
(if the isotropic vector has $\langle b\rangle(y) = 0$ then $\langle b\rangle$ is isotropic, hence universal). -/
theorem exists_diag_eq_mul_of_isotropic {K : Type*} [Field K] [CharZero K] {m : ℕ} (hm : 0 < m)
    (b : Fin m → K) (hb : ∀ i, b i ≠ 0) {a : K}
    (hiso : (QuadForm.diag (Fin.append b fun i => -a * b i)).IsotropicIn K) :
    ∃ x y : Fin m → K, (QuadForm.diag b).evalIn K y ≠ 0 ∧
      (QuadForm.diag b).evalIn K x = a * (QuadForm.diag b).evalIn K y := by
  obtain ⟨z, hz0, hz⟩ := hiso
  set x' : Fin m → K := fun i => z (Fin.castAdd m i)
  set y' : Fin m → K := fun i => z (Fin.natAdd m i)
  have hxy : (QuadForm.diag b).evalIn K x' = a * (QuadForm.diag b).evalIn K y' := by
    rw [evalIn_diag_append_self, QuadForm.evalIn_diag, QuadForm.evalIn_diag] at hz
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at hz
    rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag, Finset.mul_sum]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have : ∑ i, -a * b i * y' i ^ 2 = -∑ i, a * (b i * y' i ^ 2) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this] at hz
    linear_combination hz
  by_cases hy : (QuadForm.diag b).evalIn K y' = 0
  · have hxz : (QuadForm.diag b).evalIn K x' = 0 := by rw [hxy, hy, mul_zero]
    have hiso : (QuadForm.diag b).IsotropicIn K := by
      by_cases hx0 : x' = 0
      · exact ⟨y', fun h => hz0 (funext fun i => by
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · exact congrFun hx0 j
          · exact congrFun h j), hy⟩
      · exact ⟨x', hx0, hxz⟩
    obtain ⟨x'', hx''⟩ := PadicClass.representsIn_of_isotropic hb hiso (a * b ⟨0, hm⟩)
    refine ⟨x'', Pi.single ⟨0, hm⟩ 1, ?_, ?_⟩
    · rw [QuadForm.evalIn_diag]; simp [Pi.single_apply, hb]
    · rw [hx'', QuadForm.evalIn_diag]; simp [Pi.single_apply]
  · exact ⟨x', y', hy, hxy⟩

section Rotation

variable {Q}

/-- **The rotation $\tau_x\tau_y$ with $Q(x) = aQ(y)$** over any field $K \supseteq F$ of characteristic $0$
($Q$ nondegenerate, $Q(y) \ne 0$, $a \ne 0$) has determinant $1$ and spinor norm $aK^{\times 2}$. -/
theorem symm_mul_symm_spec (hQ : Q.Nondegenerate) {K : Type*} [Field K] [Algebra F K] [CharZero K]
    {x y : Fin n → K} (hy : Q.evalIn K y ≠ 0) {a : K} (ha : a ≠ 0)
    (hxy : Q.evalIn K x = a * Q.evalIn K y) :
    symm Q K x * symm Q K y ∈ Tamagawa.soSub Q K ∧
      spinorNorm Q K (symm Q K x * symm Q K y) = sqClassOf a := by
  have hx : Q.evalIn K x ≠ 0 := by rw [hxy]; exact mul_ne_zero ha hy
  refine ⟨?_, ?_⟩
  · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul, symm_det Q K hx, symm_det Q K hy]
    norm_num
  · have := spinorNorm_symmProd Q K hQ [x, y] (by
      intro z hz; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
      rcases hz with rfl | rfl <;> assumption)
    simp only [symmProd, valProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    rw [this, hxy, mul_assoc, sqClassOf_mul ha (mul_ne_zero hy hy),
      (sqClassOf_eq_one_iff (mul_ne_zero hy hy)).mpr ⟨_, rfl⟩, mul_one]

end Rotation

/-! ### Lemma 3.1: $\theta(V_p)$ is everything -/

/-- **Cassels, Lemma 3.1** (Ch. 11, p. 207): *suppose $n \ge 3$; then $\theta(V_p) = \mathbb Q_p^\times$*: every
$a \in F_\mathfrak p^\times$ is, modulo squares, the spinor norm of a rotation $\sigma \in O^+(V_\mathfrak p)$. Stated
at every finite prime $\mathfrak p$ of a number field $F$ (Cassels: $F = \mathbb Q$). *Proof:* the form
$Q \perp (-a)Q$ of rank $2n \ge 6$ is isotropic over $F_\mathfrak p$, so $Q(x) = aQ(y)$ for some $x, y$; if $Q(y) \ne 0$,
then $\sigma = \tau_x\tau_y$ has $\theta(\sigma) = Q(x)Q(y) \equiv a$; otherwise $V_\mathfrak p$ is isotropic, hence
universal, and $\sigma = \tau_x\tau_y$ with $Q(x) = a$, $Q(y) = 1$. (Cassels' proof splits $a = uv$ with $u, v$
represented, using that a ternary space omits at most one square class.) -/
@[kb "cassels1978" "Ch. 11, Lemma 3.1, p. 207 (over F_𝔭)"]
theorem exists_soSub_spinorNorm_eq_local (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) :
    ∃ σ ∈ Tamagawa.soSub Q (v.adicCompletion F), spinorNorm Q (v.adicCompletion F) σ = SqClass.mk a := by
  classical
  set K := v.adicCompletion F
  have hn0 : 0 < n := by omega
  obtain ⟨b, hb, hiso0⟩ := FieldGen.exists_isometric_diag Q hQ
  obtain ⟨P, hPu, hP⟩ := FieldGen.isometricIn_of_base K hiso0
  set b' : Fin n → K := fun i => algebraMap F K (b i) with hb'def
  have hb' : ∀ i, b' i ≠ 0 := fun i => (map_ne_zero _).mpr (hb i)
  have hPK : ∀ x : Fin n → K, Q.evalIn K (P *ᵥ x) = (QuadForm.diag b').evalIn K x := fun x => by
    rw [hP, QuadForm.evalIn_diag, QuadForm.evalIn_diag]; simp [b']
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  set c : Fin (n + n) → K := Fin.append b' fun i => -(a : K) * b' i with hcdef
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [c, Fin.append_left]; exact hb' j
    · simp only [c, Fin.append_right]; exact mul_ne_zero (neg_ne_zero.mpr ha0) (hb' j)
  have hD : (QuadForm.diag c).IsotropicIn K := by
    refine FieldGen.isotropicIn_diag_of_prefix (F := K) K 5 (by omega) c ?_
    exact LocalRankFive.isotropic_diag_five v (fun i : Fin 5 => c ⟨i, lt_of_lt_of_le i.2 (by omega)⟩)
      (fun i => hc _)
  obtain ⟨x, y, hy, hxy⟩ := exists_diag_eq_mul_of_isotropic hn0 b' hb' hD
  rw [← hPK y] at hy
  rw [← hPK x, ← hPK y] at hxy
  obtain ⟨h1, h2⟩ := symm_mul_symm_spec hQ hy ha0 hxy
  exact ⟨_, h1, by rw [h2, sqClassOf_of_ne_zero ha0]; exact congrArg SqClass.mk (Units.ext rfl)⟩

/-! ### Lemma 3.2: $\theta(V)$ -/

section Archimedean

variable {Q}

/-- The completion of a number field at an infinite place has characteristic $0$. -/
instance charZero_completion (w : InfinitePlace F) : CharZero w.Completion :=
  charZero_of_injective_algebraMap (algebraMap F w.Completion).injective

/-- Value of a diagonal form on a standard-basis multiple. -/
theorem evalIn_diag_single {m : ℕ} (K : Type*) [Field K] [Algebra F K] (d : Fin m → F) (i0 : Fin m) (t : K) :
    (QuadForm.diag d).evalIn K (Pi.single i0 t) = algebraMap F K (d i0) * t ^ 2 := by
  rw [QuadForm.evalIn_diag, Finset.sum_eq_single i0]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]; simp
  · simp

/-- **Squares at an infinite place** ($F_w \cong \mathbb R$ or $\mathbb C$): every element or its negative is a
square, and a sum of two squares is a square. -/
theorem completion_isSquare_props (w : InfinitePlace F) :
    (∀ z : w.Completion, IsSquare z ∨ IsSquare (-z)) ∧
      ∀ p q : w.Completion, IsSquare p → IsSquare q → IsSquare (p + q) := by
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hsq : ∀ z, IsSquare z ↔ IsSquare (e z) := fun z =>
      ⟨fun h => h.map e, fun h => by simpa using h.map e.symm⟩
    refine ⟨fun z => ?_, fun p q hp hq => ?_⟩
    · rw [hsq z, hsq (-z), map_neg, Real.isSquare_iff, Real.isSquare_iff]
      rcases le_total 0 (e z) with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · have hp' := (hsq p).mp hp
      have hq' := (hsq q).mp hq
      rw [hsq, map_add]
      rw [Real.isSquare_iff] at hp' hq' ⊢
      linarith
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    have hsq : ∀ z, IsSquare z := fun z => by
      obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e z) (n := 2) (by norm_num)
      exact ⟨e.symm s, by apply e.injective; simp [← hs, sq]⟩
    exact ⟨fun z => Or.inl (hsq z), fun p q _ _ => hsq _⟩

/-- **An anisotropic form over a "euclidean" field has all values in one square class:** if every element of $K$ or
its negative is a square, sums of two squares are squares, and $Q$ is anisotropic over $K$, then $Q(x)Q(y)$ is a square
whenever $Q(x), Q(y) \ne 0$. (Otherwise $-Q(x)Q(y)$ is a square, the discriminant $B(x,y)^2 - 4Q(x)Q(y)$ of
$t \mapsto Q(x + ty)$ is a square, and $Q(x + ty) = 0$ has a root.) -/
theorem isSquare_mul_of_not_isotropicIn {K : Type*} [Field K] [Algebra F K] [CharZero K]
    (h1 : ∀ z : K, IsSquare z ∨ IsSquare (-z))
    (h2 : ∀ p q : K, IsSquare p → IsSquare q → IsSquare (p + q))
    (haniso : ¬ Q.IsotropicIn K) {x y : Fin n → K} (hy : Q.evalIn K y ≠ 0) :
    IsSquare (Q.evalIn K x * Q.evalIn K y) := by
  by_contra hns
  obtain ⟨s, hs⟩ := (h1 _).resolve_left hns
  set B := QuadraticMap.polar (qk Q K) x y with hB
  have e : ∀ t : K, Q.evalIn K (x + t • y) = Q.evalIn K x + t * t * Q.evalIn K y + t * B := by
    intro t
    have e1 := QuadraticMap.map_add (qk Q K) x (t • y)
    rw [QuadraticMap.map_smul, QuadraticMap.polar_smul_right] at e1
    simp only [qk_apply, smul_eq_mul] at e1
    exact e1
  obtain ⟨d, hd⟩ := h2 (B * B) ((2 * s) * (2 * s)) ⟨B, rfl⟩ ⟨2 * s, rfl⟩
  set p := Q.evalIn K x with hp
  set q := Q.evalIn K y with hq
  have h2y : (2 : K) * q ≠ 0 := mul_ne_zero two_ne_zero hy
  set t : K := (-B + d) / (2 * q) with ht
  have htq : t * (2 * q) = -B + d := div_mul_cancel₀ _ h2y
  have hroot : Q.evalIn K (x + t • y) = 0 := by
    rw [e]
    have h4 : (4 * q) * (p + t * t * q + t * B) = 0 := by
      linear_combination (t * (2 * q) + (-B + d) + 2 * B) * htq + (-1) * hd + (-4) * hs
    have h4q : (4 * q) ≠ 0 := by
      have : (4 : K) ≠ 0 := by norm_num
      exact mul_ne_zero this hy
    exact (mul_eq_zero.mp h4).resolve_left h4q
  apply haniso
  refine ⟨x + t • y, fun hz => hns ?_, hroot⟩
  have hxeq : x = -(t • y) := eq_neg_of_add_eq_zero_left hz
  have : p = t * t * q := by
    have h := congrArg (qk Q K) hxeq
    rw [QuadraticMap.map_neg, QuadraticMap.map_smul, smul_eq_mul] at h
    rw [hp, hq]
    simpa only [qk_apply] using h
  exact ⟨t * q, by rw [this]; ring⟩

/-- **Even products of values of an anisotropic form are squares** (in a "euclidean" field). -/
theorem isSquare_valProd_of_not_isotropicIn {K : Type*} [Field K] [Algebra F K] [CharZero K]
    (h1 : ∀ z : K, IsSquare z ∨ IsSquare (-z))
    (h2 : ∀ p q : K, IsSquare p → IsSquare q → IsSquare (p + q))
    (haniso : ¬ Q.IsotropicIn K) (xs : List (Fin n → K)) (hxs : ∀ x ∈ xs, Q.evalIn K x ≠ 0)
    (hev : Even xs.length) : IsSquare (valProd Q K xs) := by
  rcases xs with _ | ⟨x0, rest⟩
  · exact ⟨1, by simp [valProd]⟩
  · have hx0 : Q.evalIn K x0 ≠ 0 := hxs x0 List.mem_cons_self
    have key : ∀ ys : List (Fin n → K), (∀ y ∈ ys, Q.evalIn K y ≠ 0) →
        IsSquare (valProd Q K ys * Q.evalIn K x0 ^ ys.length) := by
      intro ys
      induction ys with
      | nil => intro _; exact ⟨1, by simp [valProd]⟩
      | cons y ys ih =>
        intro h
        have ih' := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
        have hy := isSquare_mul_of_not_isotropicIn (x := y) h1 h2 haniso hx0
        have e : valProd Q K (y :: ys) * Q.evalIn K x0 ^ (y :: ys).length =
            (Q.evalIn K y * Q.evalIn K x0) * (valProd Q K ys * Q.evalIn K x0 ^ ys.length) := by
          simp only [valProd, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
          ring
        rw [e]
        exact hy.mul ih'
    have h := key (x0 :: rest) hxs
    obtain ⟨m, hm⟩ := hev
    have hsq : IsSquare (Q.evalIn K x0 ^ (x0 :: rest).length) := ⟨Q.evalIn K x0 ^ m, by rw [hm, pow_add]⟩
    have hne : Q.evalIn K x0 ^ (x0 :: rest).length ≠ 0 := pow_ne_zero _ hx0
    have := h.div hsq
    rwa [mul_div_cancel_right₀ _ hne] at this

/-- The product of values of a mapped list of vectors. -/
theorem valProd_map_algebraMap (K : Type*) [Field K] [Algebra F K] [CharZero K] (xs : List (Fin n → F)) :
    valProd Q K (xs.map fun x i => algebraMap F K (x i)) = algebraMap F K (valProd Q F xs) := by
  induction xs with
  | nil => simp [valProd]
  | cons x xs ih =>
    simp only [valProd, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    simpa using evalIn_map_tower Q K (K := F) x

end Archimedean

/-- **Cassels, Lemma 3.2** (Ch. 11, pp. 207–208), over a number field: for $n \ge 3$, $a \in F^\times$ lies in
$\theta(O^+(V))$ if and only if $a$ is a square in $F_w$ at every infinite place $w$ at which $V$ is anisotropic
(i.e. $a > 0$ at the real places where $V$ is definite). *Proof:* "$\Rightarrow$": a rotation is a product of an even
number of symmetries $\tau_{x_i}$, and at a real place where $V$ is definite all $Q(x_i)$ have one sign.
"$\Leftarrow$": $Q \perp (-a)Q$ is isotropic at every place (at the finite places by rank $\ge 5$, at the anisotropic
infinite places because $a$ is a square there), hence over $F$ (Hasse–Minkowski), and one concludes as in Lemma 3.1. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.2, pp. 207–208 (over a number field)"]
theorem mem_spinorNormGroup_iff (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (a : Fˣ) :
    a ∈ spinorNormGroup Q hQ ↔
      ∀ w : InfinitePlace F, ¬ Q.IsotropicIn w.Completion → IsSquare (algebraMap F w.Completion (a : F)) := by
  classical
  constructor
  · intro ha w hw
    obtain ⟨σ, hσ, hθ⟩ := (mem_spinorNormGroup Q hQ).mp ha
    obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q F hQ σ
    have hev := even_length_of_symmProd_mem_soSub Q hxs hσ
    have hv0 := valProd_ne_zero Q F hxs
    have h3 : sqClassOf (valProd Q F xs) = sqClassOf (a : F) := by
      rw [← spinorNorm_symmProd Q F hQ xs hxs, hθ, sqClassOf_of_ne_zero a.ne_zero]; exact congrArg (SqClass.mk (K := F)) (Units.ext rfl)
    have h4 : IsSquare (valProd Q F xs * (a : F)) :=
      (sqClassOf_eq_one_iff (mul_ne_zero hv0 a.ne_zero)).mp (by
        rw [sqClassOf_mul hv0 a.ne_zero, h3, SqClass.mul_self])
    obtain ⟨h1, h2⟩ := completion_isSquare_props w
    have h5 : IsSquare (valProd Q w.Completion (xs.map fun x i => algebraMap F w.Completion (x i))) := by
      refine isSquare_valProd_of_not_isotropicIn h1 h2 hw _ ?_ (by simpa using hev)
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      have : Q.evalIn w.Completion (fun i => algebraMap F w.Completion (x i)) =
          algebraMap F w.Completion (Q.evalIn F x) := by
        simpa using evalIn_map_tower Q w.Completion (K := F) x
      rw [this]
      exact (map_ne_zero _).mpr (hxs x hx)
    rw [valProd_map_algebraMap] at h5
    have h6 := h4.map (algebraMap F w.Completion)
    rw [map_mul] at h6
    have h7 := h6.div h5
    have hne : algebraMap F w.Completion (valProd Q F xs) ≠ 0 := (map_ne_zero _).mpr hv0
    rwa [mul_div_cancel_left₀ _ hne] at h7
  · intro H
    obtain ⟨b, hb, hiso0⟩ := FieldGen.exists_isometric_diag Q hQ
    obtain ⟨P, hPu, hP⟩ := hiso0
    have hn0 : 0 < n := by omega
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    set c : Fin (n + n) → F := Fin.append b fun i => -(a : F) * b i with hcdef
    have hc : ∀ i, c i ≠ 0 := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [c, Fin.append_left]; exact hb j
      · simp only [c, Fin.append_right]; exact mul_ne_zero (neg_ne_zero.mpr ha0) (hb j)
    have hD : (QuadForm.diag c).IsotropicIn F := by
      rw [hasseMinkowski_nf _ (QuadForm.nondegenerate_diag hc)]
      intro w
      cases w with
      | infinite w =>
        by_cases hw : Q.IsotropicIn w.Completion
        · obtain ⟨y, hy0, hy⟩ := (FieldGen.isotropicIn_iff_of_isometricIn _
            (FieldGen.isometricIn_of_base _ ⟨P, hPu, hP⟩)).mp hw
          refine ⟨Fin.append y 0, fun h => hy0 (funext fun i => ?_), ?_⟩
          · simpa [Fin.append_left] using congrFun h (Fin.castAdd n i)
          · rw [evalIn_diag_append]
            simp only [Fin.append_left, Fin.append_right]
            rw [hy, zero_add, QuadForm.evalIn_diag]
            simp
        · obtain ⟨s, hs⟩ := H w hw
          refine ⟨Fin.append (Pi.single ⟨0, hn0⟩ s) (Pi.single ⟨0, hn0⟩ 1), fun h => ?_, ?_⟩
          · have := congrFun h (Fin.natAdd n ⟨0, hn0⟩)
            rw [Fin.append_right, Pi.single_eq_same] at this
            exact one_ne_zero this
          · rw [evalIn_diag_append]
            simp only [Fin.append_left, Fin.append_right]
            rw [evalIn_diag_single, evalIn_diag_single, map_mul, map_neg, hs]
            ring
      | finite v => exact isotropicIn_diag_finite (by omega) c hc v
    obtain ⟨x, y, hy, hxy⟩ := exists_diag_eq_mul_of_isotropic hn0 b hb hD
    rw [← hP y] at hy
    rw [← hP x, ← hP y] at hxy
    obtain ⟨h1, h2⟩ := symm_mul_symm_spec hQ hy ha0 hxy
    exact (mem_spinorNormGroup Q hQ).mpr ⟨_, h1, by rw [h2, sqClassOf_of_ne_zero ha0]; exact congrArg SqClass.mk (Units.ext rfl)⟩

/-- **Cassels, Lemma 3.2** (Ch. 11, pp. 207–208): *suppose $n \ge 3$; then $\theta(V) = \mathbb Q^\times$ if $V_\infty$
is indefinite and $\theta(V) = \mathbb Q_+$ (the positive rationals) if $V_\infty$ is definite.* Here "$V_\infty$
indefinite" is `IsIndefinite Q` ($V$ isotropic over $\mathbb R$, the completion at the infinite place). -/
@[kb "cassels1978" "Ch. 11, Lemma 3.2, pp. 207–208"]
theorem mem_spinorNormGroup_rat_iff {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (a : ℚˣ) :
    a ∈ spinorNormGroup Q hQ ↔ IsIndefinite Q ∨ 0 < (a : ℚ) := by
  rw [mem_spinorNormGroup_iff Q hQ hn a]
  have hsq : ∀ (w : InfinitePlace ℚ) [Algebra ℚ w.Completion], IsSquare (algebraMap ℚ w.Completion (a : ℚ)) ↔ 0 < (a : ℚ) := by
    intro w _
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    have he : e (algebraMap ℚ _ (a : ℚ)) = ((a : ℚ) : ℝ) := by
      rw [eq_ratCast (algebraMap ℚ Rat.infinitePlace.Completion) (a : ℚ), map_ratCast]
    have hsq' : IsSquare (algebraMap ℚ Rat.infinitePlace.Completion (a : ℚ)) ↔ IsSquare (((a : ℚ) : ℝ)) := by
      rw [← he]
      exact ⟨fun h => h.map e, fun h => by simpa using h.map e.symm⟩
    rw [hsq', Real.isSquare_iff, Rat.cast_nonneg]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm a.ne_zero), le_of_lt⟩
  constructor
  · intro h
    by_cases hind : IsIndefinite Q
    · exact Or.inl hind
    · exact Or.inr ((@hsq Rat.infinitePlace (InfinitePlace.Completion.instAlgebra _ ℚ)).mp (h Rat.infinitePlace fun hiso => hind ⟨_, hiso⟩))
  · rintro (⟨w, hw⟩ | hpos) w' hw'
    · exfalso
      rw [Subsingleton.elim w' w] at hw'
      exact hw' hw
    · exact (@hsq w' (InfinitePlace.Completion.instAlgebra _ ℚ)).mpr hpos

/-! ### Lemma 3.6, Corollary: genus = spinor genus -/

section GenusHelpers

variable {Q}

/-- A unit of $\mathcal O_F$ has valuation $1$ at every finite prime. -/
theorem valued_unit (v : HeightOneSpectrum (𝓞 F)) (u : (𝓞 F)ˣ) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (u : 𝓞 F)) = 1 := by
  rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun hmem => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem u.isUnit)

/-- **Rational spinor norms localize:** if $\theta(\gamma) = cF^{\times 2}$ for a rational isometry $\gamma$, then
$\theta(\gamma_\mathfrak p) = c F_\mathfrak p^{\times 2}$. -/
theorem spinorNorm_orthMap_of (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) (γ : orthGroup Q F) {c : F}
    (hc : c ≠ 0) (h : spinorNorm Q F γ = sqClassOf c) :
    spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ) = sqClassOf (algebraMap F (v.adicCompletion F) c) := by
  obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q F hQ γ
  rw [spinorNorm_symmProd Q F hQ xs hxs] at h
  have hv0 := valProd_ne_zero Q F hxs
  have hsq : IsSquare (valProd Q F xs * c) :=
    (sqClassOf_eq_one_iff (mul_ne_zero hv0 hc)).mp (by rw [sqClassOf_mul hv0 hc, h, SqClass.mul_self])
  have hxs' : ∀ x ∈ xs.map (locVec v), Q.evalIn (v.adicCompletion F) x ≠ 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    rw [evalIn_locVec]
    exact (map_ne_zero _).mpr (hxs x hx)
  rw [orthMap_symmProd, spinorNorm_symmProd Q _ hQ _ hxs', valProd_map_locVec]
  have hsq' := hsq.map (algebraMap F (v.adicCompletion F))
  rw [map_mul] at hsq'
  have hne : algebraMap F (v.adicCompletion F) (valProd Q F xs) ≠ 0 := (map_ne_zero _).mpr hv0
  have hne' : algebraMap F (v.adicCompletion F) c ≠ 0 := (map_ne_zero _).mpr hc
  have h1 := (sqClassOf_eq_one_iff (mul_ne_zero hne hne')).mpr hsq'
  rw [sqClassOf_mul hne hne'] at h1
  exact (mul_eq_one_iff_eq_inv.mp h1).trans (SqClass.inv_eq _)

/-- **The local condition for rotations:** if $U_\mathfrak p \subseteq \theta(O^+(L_\mathfrak p))$, then every rotation
$\tau \in O^+(V_\mathfrak p)$ whose spinor norm is a unit class factors as $\tau = \kappa\rho$ with $\kappa \in O'(V_\mathfrak p)$
and $\rho \in O(L_\mathfrak p)$. -/
theorem exists_spinorKernel_mul_locStab_of_rot (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) (L : Lat F n)
    (hloc : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      u ∈ localSpinorNormGroup Q hQ v L)
    {τ : orthGroup Q (v.adicCompletion F)} (hτ : τ ∈ Tamagawa.soSub Q (v.adicCompletion F))
    (hc : IsUnitSqClass v (spinorNorm Q (v.adicCompletion F) τ)) :
    ∃ k ∈ spinorKernel Q (v.adicCompletion F), k⁻¹ * τ ∈ locStabV Q v L := by
  obtain ⟨z, hz1, hzc⟩ := hc
  have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hz1; exact zero_ne_one hz1
  obtain ⟨ρ, hρ, hρθ⟩ := (mem_localSpinorNormGroup Q hQ v L (a := Units.mk0 z hz0)).mp (hloc _ hz1)
  obtain ⟨hρ1, hρ2⟩ := Subgroup.mem_inf.mp hρ
  refine ⟨τ * ρ⁻¹, ?_, ?_⟩
  · have hd : ((τ * ρ⁻¹ : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)).val.det = 1 :=
      (Tamagawa.soSub Q _).mul_mem hτ ((Tamagawa.soSub Q _).inv_mem hρ2)
    rw [spinorKernel_eq_ker Q _ hQ, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul, map_inv,
      spinorNormHom_apply, spinorNormHom_apply, hρθ, hzc, sqClassOf_of_ne_zero hz0]
    exact ⟨mul_inv_cancel _, Units.ext (by rw [detHom_val, Units.val_one]; exact hd)⟩
  · have e : (τ * ρ⁻¹)⁻¹ * τ = ρ := by group
    rw [e]; exact hρ1

/-- **Rotations moving $L$ to a lattice in its genus, componentwise:** if $M$ is in the genus of $L$, then
$M = hL$ for some $h \in O(V)(\mathbb A_f)$ all of whose components are rotations (gen = proper gen, 102.r7). -/
theorem exists_oaf_soSub (hQ : Q.Nondegenerate) (L : Lat F n) {M : Lat F n} (hM : SameGenus Q L.1 M.1) :
    ∃ h : OAf Q, (∀ v, h v ∈ Tamagawa.soSub Q (v.adicCompletion F)) ∧ latSMul Q h L = M := by
  classical
  have hpg : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : orthGroup Q (v.adicCompletion F),
      g ∈ Tamagawa.soSub Q (v.adicCompletion F) ∧ locAct v (g : GL (Fin n) _) (loc v L.1) = loc v M.1 :=
    (sameProperGenus_iff_sameGenus Q hQ L.2).mpr hM
  choose k hk hk' using hpg
  let hp : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q (v.adicCompletion F) := fun v =>
    if loc v L.1 = loc v M.1 then 1 else k v
  have hpspec : ∀ v, locAct v ((hp v : orthGroup Q _) : GL (Fin n) _) (loc v L.1) = loc v M.1 := by
    intro v
    simp only [hp]
    split_ifs with he
    · rw [← he]; exact locAct_one _
    · exact hk' v
  have hprot : ∀ v, hp v ∈ Tamagawa.soSub Q (v.adicCompletion F) := by
    intro v
    simp only [hp]
    split_ifs
    · exact (Tamagawa.soSub Q _).one_mem
    · exact hk v
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hp v ∈ stdStab Q v := by
    filter_upwards [loc_eventually_std L.2, loc_eventually_std M.2] with v h1 h2
    have : loc v L.1 = loc v M.1 := h1.trans h2.symm
    simp only [hp, this, ↓reduceIte]
    exact (stdStab Q v).one_mem
  let hA : OAf Q := ⟨hp, hev⟩
  refine ⟨hA, hprot, Lat.ext (loc_injective (latSMul Q hA L).2 M.2 fun v => ?_)⟩
  rw [loc_latSMul]
  exact hpspec v

end GenusHelpers

/-- **Cassels, Lemma 3.6, Corollary** (Ch. 11, p. 213), over a number field: *suppose that $U_p \subseteq
\theta(\Lambda_p)$ for all $p$; then the genus of $\Lambda$ consists of a single spinor genus.* Here $\mathcal O_F$ is a
principal ideal domain, $U_\mathfrak p \subseteq \theta(O^+(L_\mathfrak p))$ at every finite prime
(`hloc`), and (`hval`) every nonzero $a_0 \in \mathcal O_F$ is a unit times an element of $\theta(O^+(V))$ (over
$\mathbb Q$ by Lemma 3.2, `sameProperSpinorGenus_of_sameGenus_rat`; for indefinite $V$ over every such $F$ by O'Meara
101:8). The conclusion is Cassels' (proper) spinor genus `SameProperSpinorGenus`. Cassels' standing assumption
$n \ge 3$ of §3 enters only through `hval` (Lemma 3.2). -/
@[kb "cassels1978" "Ch. 11, Lemma 3.6, Cor., p. 213 (over a number field, h_F = 1)"]
theorem sameProperSpinorGenus_of_sameGenus_of_units [IsPrincipalIdealRing (𝓞 F)] (hQ : Q.Nondegenerate)
    (hval : ∀ a₀ : 𝓞 F, a₀ ≠ 0 → ∃ u : (𝓞 F)ˣ, ∃ a ∈ spinorNormGroup Q hQ,
      (a : F) = algebraMap (𝓞 F) F ((u : 𝓞 F) * a₀))
    (L : Lat F n)
    (hloc : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ), Valued.v (u : v.adicCompletion F) = 1 →
      u ∈ localSpinorNormGroup Q hQ v L)
    {M : Lat F n} (hM : SameGenus Q L.1 M.1) : SameProperSpinorGenus Q L M := by
  classical
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨h, hrot, hhM⟩ := exists_oaf_soSub hQ L hM
  subst hhM
  -- local spinor norms `θ(h_v) = x_v`
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : v.adicCompletion F, x ≠ 0 ∧
      spinorNorm Q (v.adicCompletion F) (h v) = sqClassOf x := by
    intro v
    obtain ⟨xs, hxs, hxe⟩ := exists_symmProd_eq Q (v.adicCompletion F) hQ (h v)
    exact ⟨_, valProd_ne_zero Q _ hxs, by rw [← hxe, spinorNorm_symmProd Q _ hQ xs hxs]⟩
  choose xv hxv0 hxvθ using hx
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (Valued.v (xv v))
  let ε : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (m v % 2).toNat
  have hm : ∀ v, Valued.v (xv v) = WithZero.exp (m v) := fun v =>
    (WithZero.exp_log ((map_ne_zero _).mpr (hxv0 v))).symm
  have hε : ∀ v, ((ε v : ℕ) : ℤ) = m v % 2 := fun v => Int.toNat_of_nonneg (Int.emod_nonneg _ two_ne_zero)
  -- the finite set of primes where `h_v ∉ O(L_v)`
  have hfin : {v | h v ∉ locStabV Q v L}.Finite := by
    refine ((Filter.eventually_cofinite.mp h.2).union
      (Filter.eventually_cofinite.mp (loc_eventually_std L.2))).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
    exact hv ((locStabV_eq_stdStab Q v L hc.2).mpr hc.1)
  set S := hfin.toFinset
  -- the global element `a` and `γ` with `θ(γ) = a`
  set a₀ : 𝓞 F := ∏ w ∈ S, primeGen w ^ ε w with ha₀def
  have ha₀ : a₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (primeGen_ne_zero w)
  obtain ⟨u, a, haD, hau⟩ := hval a₀ ha₀
  have hvalue : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) (a : F)) =
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a₀) := by
    intro v
    rw [hau, ← IsScalarTower.algebraMap_apply, map_mul, map_mul, valued_unit v u, one_mul]
  have hva : ∀ v ∈ S, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (-(ε v : ℤ)) := by
    intro v hv
    rw [hvalue]
    exact valued_prod_primeGen_of_mem v ε hv
  have hva' : ∀ v ∉ S, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 := by
    intro v hv
    rw [hvalue]
    exact valued_prod_primeGen_of_not_mem v ε hv
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  obtain ⟨γ, hγ, hγθ⟩ := (mem_spinorNormGroup Q hQ).mp haD
  have hγθ' : spinorNorm Q F γ = sqClassOf (a : F) := by
    rw [hγθ, sqClassOf_of_ne_zero ha0]; exact congrArg (SqClass.mk (K := F)) (Units.ext rfl)
  have hθγ : ∀ v : HeightOneSpectrum (𝓞 F), spinorNorm Q (v.adicCompletion F) (orthMap Q _ γ) =
      sqClassOf (algebraMap F (v.adicCompletion F) (a : F)) := fun v => spinorNorm_orthMap_of hQ v γ ha0 hγθ'
  have hγrot : ∀ v : HeightOneSpectrum (𝓞 F), orthMap Q (v.adicCompletion F) γ ∈
      Tamagawa.soSub Q (v.adicCompletion F) := by
    intro v
    rw [Tamagawa.mem_soSub, orthMap_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      show ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 from hγ, map_one]
  -- local decomposition `γ_v⁻¹ h_v = k_v u_v`
  have hdec : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k ∈ spinorKernel Q (v.adicCompletion F),
      k⁻¹ * ((orthMap Q _ γ)⁻¹ * h v) ∈ locStabV Q v L := by
    intro v
    set K := v.adicCompletion F
    have hav : algebraMap F K (a : F) ≠ 0 := (map_ne_zero _).mpr ha0
    by_cases hvS : v ∈ S
    · refine exists_spinorKernel_mul_locStab_of_rot hQ v L (hloc v)
        ((Tamagawa.soSub Q K).mul_mem ((Tamagawa.soSub Q K).inv_mem (hγrot v)) (hrot v)) ?_
      rw [← spinorNormHom_apply Q K hQ, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hθγ,
        SqClass.inv_eq, hxvθ, ← sqClassOf_mul hav (hxv0 v)]
      refine isUnitSqClass_of_valued_eq v _ (m v / 2) ?_
      rw [map_mul, hva v hvS, hm, ← WithZero.exp_add, hε]
      congr 1
      omega
    · have hhv : h v ∈ locStabV Q v L := by
        by_contra hc; exact hvS (hfin.mem_toFinset.mpr hc)
      obtain ⟨k, hk, hg⟩ := exists_spinorKernel_mul_locStab_of_rot hQ v L (hloc v) (hγrot v) (by
        rw [hθγ]; exact ⟨_, hva' v hvS, rfl⟩)
      set g := k⁻¹ * orthMap Q K γ
      refine ⟨g⁻¹ * k⁻¹ * g, ?_, ?_⟩
      · have := (spinorKernel_normal Q K).conj_mem k⁻¹ ((spinorKernel Q K).inv_mem hk) g⁻¹
        simpa using this
      · have e : (g⁻¹ * k⁻¹ * g)⁻¹ * ((orthMap Q K γ)⁻¹ * h v) = g⁻¹ * h v := by
          simp only [g]; group
        rw [e]
        exact (locStabV Q v L).mul_mem ((locStabV Q v L).inv_mem hg) hhv
  choose kv hkv hukv using hdec
  -- the adelic element `u ∈ O(L̂)`
  let uA : OAf Q := ⟨fun v => (kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v), by
    filter_upwards [loc_eventually_std L.2] with v hv
    exact (locStabV_eq_stdStab Q v L hv).mp (hukv v)⟩
  have huA : uA ∈ locStab Q L := fun v => hukv v
  set k : OAf Q := (diagF Q γ)⁻¹ * h * uA⁻¹ with hkdef
  have hk : k ∈ spinorKernelAf Q := by
    intro v
    have : k v = kv v := by
      change (orthMap Q _ γ)⁻¹ * h v * ((kv v)⁻¹ * ((orthMap Q _ γ)⁻¹ * h v))⁻¹ = kv v
      group
    rw [this]; exact hkv v
  have hh : h = diagF Q γ * k * uA := by simp only [k]; group
  refine (sameProperSpinorGenus_iff Q).mpr ⟨γ, hγ, k, hk, ?_⟩
  have huL : latSMul Q uA L = L :=
    MulAction.mem_stabilizer_iff.mp ((stabilizer_eq_locStab Q L).symm ▸ huA)
  change h • L = (diagF Q γ) • (k • L)
  conv_lhs => rw [hh, mul_smul, mul_smul]
  change diagF Q γ • (k • latSMul Q uA L) = _
  rw [huL]

/-- **Cassels, Lemma 3.6, Corollary** (Ch. 11, p. 213): *suppose that $U_p \subseteq \theta(\Lambda_p)$ for all $p$.
Then the genus of $\Lambda$ consists of a single spinor genus.* Over $\mathbb Q$, for every regular $V$ of dimension
$n \ge 3$ (definite or indefinite), with Cassels' (proper) spinor genus. -/
@[kb "cassels1978" "Ch. 11, Lemma 3.6, Cor., p. 213"]
theorem sameProperSpinorGenus_of_sameGenus_rat {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (L : Lat ℚ n)
    (hloc : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ), Valued.v (u : v.adicCompletion ℚ) = 1 →
      u ∈ localSpinorNormGroup Q hQ v L)
    {M : Lat ℚ n} (hM : SameGenus Q L.1 M.1) : SameProperSpinorGenus Q L M := by
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective
  refine sameProperSpinorGenus_of_sameGenus_of_units Q hQ ?_ L hloc hM
  intro a₀ ha₀
  have hq : (algebraMap (𝓞 ℚ) ℚ a₀) ≠ 0 := by
    intro h
    exact ha₀ ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ)).mp h)
  by_cases hpos : 0 < algebraMap (𝓞 ℚ) ℚ a₀
  · refine ⟨1, Units.mk0 (algebraMap (𝓞 ℚ) ℚ a₀) hq, ?_, by simp⟩
    exact (mem_spinorNormGroup_rat_iff Q hQ hn _).mpr (Or.inr hpos)
  · have hneg : 0 < -(algebraMap (𝓞 ℚ) ℚ a₀) := by
      rcases lt_or_gt_of_ne hq with h | h
      · linarith
      · exact absurd h hpos
    refine ⟨-1, Units.mk0 (-(algebraMap (𝓞 ℚ) ℚ a₀)) (neg_ne_zero.mpr hq), ?_, by simp⟩
    exact (mem_spinorNormGroup_rat_iff Q hQ hn _).mpr (Or.inr hneg)

end QuadFormsKB.Lattices
