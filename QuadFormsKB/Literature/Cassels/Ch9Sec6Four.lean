import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Literature.Cassels.Ch9Sec6Local
import QuadFormsKB.Literature.Cassels.Ch9Sec4Congr
import QuadFormsKB.Siegel.FourSquaresClassNumber
import QuadFormsKB.Siegel.NeighborGenus

open Matrix

set_option linter.unusedSectionVars false

/-!
# Cassels, Chapter 9, §6: Lemma 6.6 and its Corollary, ternary forms of determinant $a^2$

**Layer:** classically integral positive definite ternary forms $g$ (Cassels' matrix $(g_{ij}) = H/2$, `casselsMat`) and
$f = I_4 = x_0^2 + \dots + x_3^2$ (`sumSq 4`); $o^{+}$ = number of proper automorphs (`AutPlus`); 0-based indices
(Cassels' $-y_1^2 + 2ay_2y_3$ is $-y_0^2 + 2ay_1y_2$ here, matrix `CongrLocal.G₀ a`).

**Proves**
* `weight_lemma66` (Lemma 6.6): for $a$ odd squarefree, the weight $W = \sum 1/o^{+}$ over the proper classes of the
  set `lemma66Set a` of positive definite ternary forms of determinant $a^2$ that are $\mathbb Z_p$-equivalent to
  $-y_0^2 + 2ay_1y_2$ for all odd $p$ equals $\frac1{24}\prod_{p\mid a}\frac{p+1}2$. The formula (6.47) is lost in the
  scan and is reconstructed from Lemmas 6.5 and 6.2.
* `exists_many_classes` (Corollary): a genus may contain arbitrarily many proper classes.

*Method (reversing Cassels' logic, not his lattice count (6.48)–(6.59)):* Lemma 6.5 (here from Jacobi's four-square
theorem, `primRepNum_sumSq_four`) gives $8\prod_{p\mid a}(p+1)$ primitive representations of $a$ by $I_4$. Lemma 6.2
for one class (`sigmaWeight_eq`) shows that those associated with the class of $g$ number $192\cdot 2^\alpha/o^{+}(g)$,
with $\rho = 2^\alpha$ (`rhoCount_sumSq_four`, Chinese remainder theorem) and $o^{+}(I_4) = 192$; the associated classes
are exactly those of `lemma66Set` (`assocClass_mem_four`, `CongrLocal.meq_G₀`). Summing over the classes gives
$8\prod(p+1) = 192\cdot 2^\alpha W$.

*Not proved:* that `lemma66Set a` is a single genus (Cassels presupposes it); $W$ is taken over the set. The Corollary is
proved by sorting the classes of the set by Cassels' matrix modulo $4$: forms of the set with congruent matrices are in
one genus (`sameGenus_lemma66`: odd $p$ by the local equivalence to $G_0(a)$, $p = 2$ by `CongrLocal.meq_of_congr`,
$\mathbb R$ by `isometricGL_real_of_posDef`), and there are at most $4^9$ residue classes.
-/

noncomputable section

namespace QuadFormsKB.Siegel

/-- $I_n$ is classically integral. -/
theorem ci_sumSq_gen (n : ℕ) : IsClassicallyIntegral (sumSq n) :=
  ⟨1, Matrix.isSymm_one, fun x => by simp [gramForm, eval_sumSq, dotProduct, sq]⟩

/-- Cassels' matrix of $I_n$ is $1$. -/
theorem casselsMat_sumSq_gen (n : ℕ) : casselsMat (sumSq n) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [casselsMat, hessian_sumSq]
  · simp [casselsMat, hessian_sumSq, h]

/-! ### Part A: the genus of $I_4$ and $o^{+}(I_4) = 192$ -/

/-- $\mathrm{diag}(-1, 1, 1, 1)$ is an improper automorph of $I_4$. -/
theorem hasImproperAut_sumSq_four : HasImproperAut (sumSq 4) := by
  set D : Matrix (Fin 4) (Fin 4) ℤ := Matrix.diagonal ![-1, 1, 1, 1] with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  refine ⟨⟨D, D, hDD, hDD⟩, ?_, ?_⟩
  · rw [mem_aut_sumSq_iff]
    show Dᵀ * D = 1
    rw [hD, Matrix.diagonal_transpose]
    exact hDD
  · show D.det = -1
    rw [hD, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ]

/-- $o^{+}(I_4) = 192$ ($\lvert O(I_4)\rvert = 2^4\cdot 4! = 384$). -/
theorem card_autPlus_sumSq_four : Nat.card (AutPlus (sumSq 4)) = 192 := by
  have h := card_aut_eq_mul (sumSq 4)
  simp only [card_aut_sumSq, hasImproperAut_sumSq_four, ite_true] at h
  norm_num [Nat.factorial] at h
  omega

/-- The genus of $I_4$ is a single proper class. -/
theorem pgenusClasses_sumSq_four : pgenusClasses (sumSq 4) = {pclassOf (sumSq 4)} := by
  ext D
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨f', hf', hg⟩
    rw [← hf']
    have h1 := sameGenus_sumSq_intEquiv (n := 4) (by norm_num) hg
    have h2 := (intEquiv_iff_properIntEquiv_of_hasImproperAut hasImproperAut_sumSq_four f').mp h1
    exact (pclassOf_eq_pclassOf_iff.mpr h2).symm
  · rintro rfl
    exact ⟨sumSq 4, rfl, SameGenus.refl _⟩

/-! ### Part B: the form $h$ of (6.8) is in the genus of $I_4$ -/

/-- For symmetric $A$: Hermite's Schur complement is `assocMat (A 0 0) A`. -/
theorem schur_eq_assocMat {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : A.IsSymm) :
    Hermite.schur A = assocMat (A 0 0) A := by
  ext i j
  simp only [Hermite.schur, Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, vecMulVec_apply,
    smul_eq_mul, assocMat, Matrix.of_apply, Hermite.colT, Hermite.rowT]
  rw [hA.apply i.succ 0]

/-- $A_{00}^m\det A = A_{00}\det(\mathrm{assocMat}\,A_{00}\,A)$ for symmetric $A$. -/
theorem det_assocMat_gen {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hA : A.IsSymm) :
    A 0 0 ^ m * A.det = A 0 0 * (assocMat (A 0 0) A).det := by
  rw [← schur_eq_assocMat hA]
  exact Hermite.det_schur A

/-- `hMat` has determinant $1$ when $\det G = a^2$ ($4 \times 4$ case). -/
theorem det_hMat_four {a : ℕ} (ha0 : 0 < a) {c : Fin 3 → ℤ} {G : Matrix (Fin 3) (Fin 3) ℤ} (hG : G.IsSymm)
    (hdiv : ∀ i j, (a : ℤ) ∣ c i * c j + G i j) (hdet : G.det = (a : ℤ) ^ 2) :
    (hMat (a : ℤ) c G).det = 1 := by
  have h := det_assocMat_gen (hMat_isSymm (a := (a : ℤ)) (c := c) hG)
  rw [hMat_zero_zero, assocMat_hMat hdiv, hdet] at h
  have ha : (a : ℤ) ≠ 0 := by exact_mod_cast ha0.ne'
  have h' : (a : ℤ) ^ 3 * (hMat (a : ℤ) c G).det = (a : ℤ) ^ 3 * 1 := by rw [mul_one]; rw [h]; ring
  exact mul_left_cancel₀ (pow_ne_zero 3 ha) h'

/-- `hMat` is positive definite (any number of variables). -/
theorem isPosDefInt_hMat_gen {m : ℕ} {a : ℕ} (ha0 : 0 < a) {c : Fin m → ℤ} {g : QuadForm ℤ m}
    (hg : IsClassicallyIntegral g) (hpd : IntQF.PosDef g)
    (hdiv : ∀ i j, (a : ℤ) ∣ c i * c j + casselsMat g i j) :
    Hermite.IsPosDefInt (hMat (a : ℤ) c (casselsMat g)) := by
  refine ⟨hMat_isSymm (casselsMat_isSymm g), fun x hx => ?_⟩
  have key := complete_square (hMat_isSymm (a := (a : ℤ)) (c := c) (casselsMat_isSymm g)) x
  rw [hMat_zero_zero, assocMat_hMat hdiv, ← eval_eq_casselsMat hg] at key
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha0
  by_cases ht : Fin.tail x = 0
  · have hx0 : x 0 ≠ 0 := by
      intro h0
      apply hx
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun ht j
    have h1 : (hMat (a : ℤ) c (casselsMat g) *ᵥ x) 0 = a * x 0 := by
      have hx1 : ∀ j : Fin m, x j.succ = 0 := fun j => congrFun ht j
      simp [mulVec, dotProduct, Fin.sum_univ_succ, hx1]
    rw [h1, ht] at key
    have : (a : ℤ) * x 0 ≠ 0 := mul_ne_zero haZ.ne' hx0
    have hpos : 0 < ((a : ℤ) * x 0) ^ 2 := by positivity
    have h0 : g.eval 0 = 0 := by simp [eval_eq_casselsMat hg]
    rw [h0] at key
    by_contra hneg
    nlinarith
  · have := hpd _ ht
    by_contra hneg
    nlinarith [sq_nonneg ((hMat (a : ℤ) c (casselsMat g) *ᵥ x) 0)]

/-- The genus of $I_4$ contains `ofGram (hMat a c G)` whenever $a \mid c_ic_j + g_{ij}$ ($g$ positive definite
ternary with $\det(g_{ij}) = a^2$): positive definite of determinant $1$, hence equivalent to $I_4$. -/
theorem sameGenus_hMat_four {a : ℕ} (ha0 : 0 < a) {c : Fin 3 → ℤ} {g : QuadForm ℤ 3}
    (hg : IsClassicallyIntegral g) (hpd : IntQF.PosDef g) (hdet : (casselsMat g).det = (a : ℤ) ^ 2)
    (hdiv : ∀ i j, (a : ℤ) ∣ c i * c j + casselsMat g i j) :
    SameGenus (sumSq 4) (ofGram (hMat (a : ℤ) c (casselsMat g))) := by
  obtain ⟨T, hT⟩ := Hermite.unimodular_posDef_equiv_one 4 (by norm_num) _ (isPosDefInt_hMat_gen ha0 hg hpd hdiv)
    (det_hMat_four ha0 (casselsMat_isSymm g) hdiv hdet)
  refine IntEquiv.sameGenus (IsometricGL.symm
    (⟨T, fun x => ?_⟩ : IntEquiv (ofGram (hMat (a : ℤ) c (casselsMat g))) (sumSq 4)))
  rw [eval_ofGram (hMat_isSymm (casselsMat_isSymm g)), dotProduct_conj, hT, eval_sumSq]
  simp [dotProduct, sq]

/-! ### Part C: counting the solutions of $\mathbf v\mathbf v^{\mathsf T} \equiv -G \pmod a$ -/

/-- The solutions $\mathbf v \in (\mathbb Z/n)^k$ of $v_iv_j + G_{ij} = 0$ for all $i, j$. -/
def solSetK {k : ℕ} (n : ℕ) (G : Matrix (Fin k) (Fin k) ℤ) : Set (Fin k → ZMod n) :=
  {v | ∀ i j, v i * v j + (G i j : ZMod n) = 0}

/-- **CRT:** the solutions modulo $mn$ ($m, n$ coprime) are the pairs of solutions. -/
def solSetKCRT {k : ℕ} {m n : ℕ} (h : Nat.Coprime m n) (G : Matrix (Fin k) (Fin k) ℤ) :
    solSetK (m * n) G ≃ solSetK m G × solSetK n G where
  toFun v := (⟨fun i => (ZMod.chineseRemainder h (v.1 i)).1, fun i j => by
      have h' := congrArg (ZMod.chineseRemainder h) (v.2 i j)
      rw [map_add, map_mul, map_intCast, map_zero] at h'
      simpa using congrArg Prod.fst h'⟩,
    ⟨fun i => (ZMod.chineseRemainder h (v.1 i)).2, fun i j => by
      have h' := congrArg (ZMod.chineseRemainder h) (v.2 i j)
      rw [map_add, map_mul, map_intCast, map_zero] at h'
      simpa using congrArg Prod.snd h'⟩)
  invFun w := ⟨fun i => (ZMod.chineseRemainder h).symm (w.1.1 i, w.2.1 i), fun i j => by
    apply (ZMod.chineseRemainder h).injective
    rw [map_add, map_mul, map_intCast, map_zero]
    simp only [RingEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · simpa using w.1.2 i j
    · simpa using w.2.2 i j⟩
  left_inv v := by
    ext i
    simp
  right_inv w := by
    ext i <;> simp

theorem card_solSetK_mul {k : ℕ} {m n : ℕ} (h : Nat.Coprime m n) (G : Matrix (Fin k) (Fin k) ℤ) :
    Nat.card (solSetK (m * n) G) = Nat.card (solSetK m G) * Nat.card (solSetK n G) := by
  rw [Nat.card_congr (solSetKCRT h G), Nat.card_prod]

/-- Over $\mathbb Z/p$: a nonzero solution forces exactly $\{\pm v\}$. -/
theorem card_solSetK_prime {k : ℕ} {p : ℕ} [Fact p.Prime] {G : Matrix (Fin k) (Fin k) ℤ} {v : Fin k → ZMod p}
    (hv : v ∈ solSetK p G) (hnz : ∃ i j, (G i j : ZMod p) ≠ 0) :
    Nat.card (solSetK p G) = if p = 2 then 1 else 2 := by
  obtain ⟨i0, j0, hij⟩ := hnz
  have hk : ∃ k, v k ≠ 0 := by
    by_contra hcon
    have hcon : ∀ k, v k = 0 := fun k => by_contra fun h => hcon ⟨k, h⟩
    apply hij
    have := hv i0 j0
    rw [hcon i0, hcon j0] at this
    simpa using this
  obtain ⟨k, hk⟩ := hk
  have hset : solSetK p G = {v, -v} := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hw
      have hww : ∀ i j, w i * w j = v i * v j := fun i j => by
        have h1 := hw i j
        have h2 := hv i j
        linear_combination h1 - h2
      have hk2 : w k ^ 2 = v k ^ 2 := by rw [sq, sq]; exact hww k k
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hk2 with h | h
      · left
        funext i
        have := hww i k
        rw [h] at this
        exact mul_right_cancel₀ hk this
      · right
        funext i
        have := hww i k
        rw [h] at this
        have : (w i + v i) * v k = 0 := by linear_combination -this
        have := (mul_eq_zero.mp this).resolve_right hk
        simp only [Pi.neg_apply]
        linear_combination this
    · rintro (rfl | rfl)
      · exact hv
      · intro i j
        have := hv i j
        simp only [Pi.neg_apply, neg_mul_neg]
        exact this
  rw [hset, Nat.card_coe_set_eq]
  by_cases hp2 : p = 2
  · subst hp2
    have : -v = v := by
      funext i
      simp only [Pi.neg_apply]
      have : (2 : ZMod 2) = 0 := rfl
      linear_combination (-(v i)) * this
    rw [this]; simp
  · have hne : v ≠ -v := by
      intro h
      have := congrFun h k
      simp only [Pi.neg_apply] at this
      have h2 : (2 : ZMod p) * v k = 0 := by linear_combination this
      rcases mul_eq_zero.mp h2 with h | h
      · have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at this
        exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
      · exact hk h
    rw [Set.ncard_pair hne]
    simp [hp2]

theorem card_solSetK_one {k : ℕ} (G : Matrix (Fin k) (Fin k) ℤ) : Nat.card (solSetK 1 G) = 1 := by
  have : Unique (solSetK 1 G) :=
    ⟨⟨⟨fun _ => 0, fun i j => Subsingleton.elim _ _⟩⟩, fun w => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_unique

/-- The count over a squarefree modulus is the product over its prime factors. -/
theorem card_solSetK_finset {k : ℕ} (G : Matrix (Fin k) (Fin k) ℤ) :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ (∃ v : Fin k → ZMod p, v ∈ solSetK p G) ∧
        ∃ i j, (G i j : ZMod p) ≠ 0) →
      Nat.card (solSetK (∏ p ∈ s, p) G) = ∏ p ∈ s, (if p = 2 then 1 else 2) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simpa using card_solSetK_one G
  | insert q s hq ih =>
    intro hs
    have hqp : q.Prime := (hs q (Finset.mem_insert_self _ _)).1
    have hsp : ∀ p ∈ s, p.Prime ∧ (∃ v : Fin k → ZMod p, v ∈ solSetK p G) ∧
        ∃ i j, (G i j : ZMod p) ≠ 0 := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hq, Finset.prod_insert hq]
    have hcop : Nat.Coprime q (∏ p ∈ s, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes hqp (hsp p hp).1).mpr (fun h => hq (h ▸ hp))
    rw [card_solSetK_mul hcop, ih hsp]
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨-, ⟨v, hv⟩, hnz⟩ := hs q (Finset.mem_insert_self _ _)
    rw [card_solSetK_prime hv hnz]

/-- For squarefree $a$ with every prime factor having a solution and a nonzero entry of $G$: the number of solutions
modulo $a$ is $\prod_{p \mid a}(\text{2 if } p \ne 2, \text{1 if } p = 2)$. -/
theorem card_solSetK {k : ℕ} {a : ℕ} (hsf : Squarefree a) {G : Matrix (Fin k) (Fin k) ℤ}
    (hcond : ∀ p : ℕ, p.Prime → p ∣ a →
      (∃ w : Fin k → ZMod p, w ∈ solSetK p G) ∧ ∃ i j, (G i j : ZMod p) ≠ 0) :
    Nat.card (solSetK a G) = ∏ p ∈ a.primeFactors, (if p = 2 then 1 else 2) := by
  have h := card_solSetK_finset G a.primeFactors (fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, hcond p (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)⟩)
  rwa [Nat.prod_primeFactors_of_squarefree hsf] at h

/-! ### Part D: Cassels' set for Lemma 6.6 -/

/-- **Cassels' set of ternary forms for Lemma 6.6** (Ch. 9, §6, p. 152): the classically integral positive definite
ternary forms $g$ with $d(g) = \det(g_{ij}) = a^2$ that are $\mathbb Z_p$-equivalent to $-y_0^2 + 2a\,y_1y_2$ (6.46) for
every odd prime $p$, in the matrix form `MEq` ($T^{\mathsf T}G_0(a)T = (g_{ij})$ with $\det T$ a $p$-adic unit;
equivalent to the form-level `IsometricGL` over $\mathbb Z_p$ by `isometricGL_of_meq_casselsMat`, and conversely by
`CongrLocal.meq_of_isometricGL`-type arguments). The library does not prove that this set is a single genus
(Cassels presupposes it); the weight $W$ below is taken over this set. -/
def lemma66Set (a : ℕ) : Set (QuadForm ℤ 3) :=
  {g | IsClassicallyIntegral g ∧ IntQF.PosDef g ∧ (casselsMat g).det = (a : ℤ) ^ 2 ∧
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      CongrLocal.MEq ((CongrLocal.G₀ (a : ℤ)).map (Int.castRingHom ℤ_[p]))
        ((casselsMat g).map (Int.castRingHom ℤ_[p]))}

/-- For $p \mid a$, $G \sim G_0(a)$ over $\mathbb Z_p$ gives a solution of $w_iw_j + G_{ij} \equiv 0 \pmod p$. -/
theorem exists_sol_of_meq {p : ℕ} [Fact p.Prime] {a : ℕ} (hpa : p ∣ a) {G : Matrix (Fin 3) (Fin 3) ℤ}
    (h : CongrLocal.MEq ((CongrLocal.G₀ (a : ℤ)).map (Int.castRingHom ℤ_[p])) (G.map (Int.castRingHom ℤ_[p]))) :
    ∃ w : Fin 3 → ZMod p, w ∈ solSetK p G := by
  obtain ⟨T, -, hT⟩ := h
  set φ : ℤ_[p] →+* ZMod p := PadicInt.toZMod with hφ
  have h1 := congrArg (fun M => M.map φ) hT
  simp only [Matrix.map_mul, Matrix.transpose_map] at h1
  have ha : ((a : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hpa
  have ha' : ((a : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).mpr hpa
  have hG0 : ((CongrLocal.G₀ (a : ℤ)).map (Int.castRingHom ℤ_[p])).map φ =
      !![-1, 0, 0; 0, 0, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CongrLocal.G₀, ha']
  have hG : (G.map (Int.castRingHom ℤ_[p])).map φ = G.map (Int.castRingHom (ZMod p)) := by
    ext i j; simp
  rw [hG0, hG] at h1
  refine ⟨fun i => (T.map φ) 0 i, fun i j => ?_⟩
  have := congrFun (congrFun h1 i) j
  simp [Matrix.mul_apply, Fin.sum_univ_three] at this
  simp only [Matrix.map_apply]
  linear_combination -this

/-- Some entry of $G$ is nonzero modulo $p$ when $p \parallel a$ and $\det G = a^2$. -/
theorem exists_ne_zero_mod {p : ℕ} [Fact p.Prime] {a : ℕ} (hsf : Squarefree a) (hpa : p ∣ a)
    {G : Matrix (Fin 3) (Fin 3) ℤ} (hdet : G.det = (a : ℤ) ^ 2) : ∃ i j, (G i j : ZMod p) ≠ 0 := by
  by_contra hcon
  have hcon : ∀ i j, (G i j : ZMod p) = 0 := fun i j => by_contra fun h => hcon ⟨i, j, h⟩
  have hd : ∀ i j, (p : ℤ) ∣ G i j := fun i j => (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (hcon i j)
  choose X hX using hd
  have hGX : G = (p : ℤ) • Matrix.of X := by
    ext i j; simp [hX i j]
  have h3 : (p : ℤ) ^ 3 ∣ (a : ℤ) ^ 2 := by
    rw [← hdet, hGX, det_smul, Fintype.card_fin]
    exact dvd_mul_right _ _
  obtain ⟨a', rfl⟩ := hpa
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h4 : (p : ℤ) ∣ (a' : ℤ) ^ 2 := by
    obtain ⟨e, he⟩ := h3
    push_cast at he
    exact ⟨e, mul_left_cancel₀ (pow_ne_zero 2 hp0) (by linear_combination he)⟩
  have h5 : (p : ℤ) ∣ a' := Int.Prime.dvd_pow' (Fact.out) h4
  have h5' : p ∣ a' := by exact_mod_cast h5
  obtain ⟨b, hb⟩ := h5'
  have hu := hsf p ⟨b, by rw [hb]; ring⟩
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.isUnit_iff.mp hu)

/-- **Cassels' $\rho(I_4, g) = 2^{\alpha}$** (the analogue of (6.41) for Lemma 6.6), $\alpha$ the number of prime
divisors of $a$ ($a$ odd squarefree): for $g$ in the set of Lemma 6.6 the congruence classes $\mathbf c \bmod a$ counted
by $\rho$ are the solutions of $c_ic_j + g_{ij} \equiv 0 \pmod a$ (the form $h$ is automatically in the genus of $I_4$),
and at each $p \mid a$ there are exactly the two solutions $\pm\mathbf w$ (from $G \sim G_0(a) \equiv \mathrm{diag}(-1,0,0)
\pmod p$). -/
theorem rhoCount_sumSq_four {a : ℕ} (ha : Odd a) (hsf : Squarefree a) {g : QuadForm ℤ 3}
    (hgs : g ∈ lemma66Set a) :
    rhoCount (sumSq 4) a (casselsMat g) = 2 ^ a.primeFactors.card := by
  obtain ⟨hg, hpd, hdet, hloc⟩ := hgs
  have ha0 : 0 < a := ha.pos
  have : NeZero a := ⟨ha0.ne'⟩
  have hcard : Nat.card (solSetK a (casselsMat g)) = 2 ^ a.primeFactors.card := by
    rw [card_solSetK hsf (fun p hp hpa => ?_)]
    · rw [Finset.prod_congr rfl (g := fun _ => 2)]
      · simp
      · intro p hp
        have hp2 : p ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
        simp [hp2]
    · have : Fact p.Prime := ⟨hp⟩
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr hpa)
      exact ⟨exists_sol_of_meq hpa (hloc p hp2), exists_ne_zero_mod hsf hpa hdet⟩
  rw [← hcard, rhoCount]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  show _ ↔ w ∈ solSetK a (casselsMat g)
  simp only [solSetK, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, hc, hdiv, -⟩ i j
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mpr (hdiv i j)
    push_cast at this
    rw [← hc i, ← hc j]
    exact this
  · intro hw
    have hdiv : ∀ i j, (a : ℤ) ∣ canLift w i * canLift w j + casselsMat g i j := fun i j => by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mp ?_
      push_cast
      rw [cast_canLift, cast_canLift]
      exact hw i j
    exact ⟨canLift w, cast_canLift w, hdiv, sameGenus_hMat_four ha0 hg hpd hdet hdiv⟩

/-! ### Part E: the forms $g$ associated with representations -/

/-- Every primitive representation of $a$ by a form $f_0$ of the genus of $I_4$ is associated with the proper class of a
form of Cassels' set (Cassels, p. 152: the forms $g$ which occur have $d(g) = a^2$ and are $\mathbb Z_p$-equivalent to
$-y_0^2 + 2ay_1y_2$ for odd $p$). -/
theorem assocClass_mem_four {f0 : QuadForm ℤ 4} (hf0 : IsClassicallyIntegral f0) (hpd0 : IntQF.PosDef f0)
    (hdet0 : (casselsMat f0).det = 1) {a : ℕ} (hsf : Squarefree a) {b : Fin 4 → ℤ}
    (hb : b ∈ primRepSet f0 a) :
    ∃ g ∈ lemma66Set a, assocClass f0 b = pclassOf g := by
  have hex : ∃ T : GL (Fin 4) ℤ, T.val.det = 1 ∧ T.val *ᵥ Pi.single 0 1 = b := by
    obtain ⟨T, hT, hTb⟩ := exists_sl_first_of_gcd (n := 4) (by omega) b hb.1
    exact ⟨T, hT, by simpa only [Fin.zero_eta] using hTb⟩
  obtain ⟨hT1, hT2⟩ := Tsel_spec hex
  have hev : f0.eval b = a := hb.2
  set T := (Tsel b).val with hTdef
  set A := Tᵀ * casselsMat f0 * T with hAdef
  have hA : A.IsSymm := isSymm_conj (casselsMat_isSymm f0) T
  have h00 : A 0 0 = a := by rw [hAdef, ← eval_first_col hf0, hT2, hev]
  have hGs : (assocMat (a : ℤ) A).IsSymm := assocMat_isSymm hA _
  have hcl : assocClass f0 b = pclassOf (ofGram (assocMat (a : ℤ) A)) := by
    rw [assocClass_eq f0 hex, assocGram_eq, hev]
  have hdetA : A.det = 1 := by
    rw [hAdef, det_mul, det_mul, det_transpose, hT1, hdet0]; simp
  have hdetG : (assocMat (a : ℤ) A).det = (a : ℤ) ^ 2 := by
    have h := det_assocMat_gen hA
    rw [h00, hdetA] at h
    have ha0 : (a : ℤ) ≠ 0 := by
      have := hsf.ne_zero
      exact_mod_cast this
    have h' : (a : ℤ) * (a : ℤ) ^ 2 = (a : ℤ) * (assocMat (a : ℤ) A).det := by rw [← h]; ring
    exact (mul_left_cancel₀ ha0 h').symm
  refine ⟨ofGram (assocMat (a : ℤ) A), ⟨ci_ofGram hGs, ?_, ?_, ?_⟩, hcl⟩
  · have hP0 : Hermite.IsPosDefInt (casselsMat f0) :=
      ⟨casselsMat_isSymm f0, fun x hx => by rw [← eval_eq_casselsMat hf0]; exact hpd0 x hx⟩
    have hP : Hermite.IsPosDefInt A := hP0.conj (Tsel b)
    have hS := hP.schur
    rw [schur_eq_assocMat hA, h00] at hS
    intro y hy
    rw [eval_ofGram hGs]
    exact hS.2 y hy
  · rw [casselsMat_ofGram hGs]; exact hdetG
  · intro p _ hp2
    rw [casselsMat_ofGram hGs]
    have ha0 : (a : ℤ) ≠ 0 := by
      have := hsf.ne_zero
      exact_mod_cast this
    have hsq : ¬ (p : ℤ) ^ 2 ∣ (a : ℤ) := by
      intro h
      have h' : p * p ∣ a := by
        have : (p * p : ℤ) ∣ (a : ℤ) := by simpa [sq] using h
        exact_mod_cast this
      have hu := hsf p h'
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.isUnit_iff.mp hu)
    refine CongrLocal.meq_G₀ hp2 ha0 hsq hGs.eq hdetG ⟨fun j => A 0 j.succ, fun i j => ?_⟩
    by_cases h : (p : ℤ) ∣ (a : ℤ)
    · left
      exact h.trans ⟨A i.succ j.succ, by simp only [assocMat, Matrix.of_apply]; ring⟩
    · right; exact h

/-! ### Part F: the weight -/

/-- The weight of the set of Lemma 6.6: $W = \sum 1/o^{+}(f')$ over representatives $f'$ of the proper classes of the
forms of `lemma66Set a` (a `finsum`, so $0$ if there were infinitely many classes). -/
def lemma66Weight (a : ℕ) : ℝ :=
  ∑ᶠ C ∈ pclassOf '' lemma66Set a, ((Nat.card (AutPlus C.out) : ℝ))⁻¹

/-- **The representation count attached to a class of $g$:** the number of primitive representations of $a$ by the
representative of the class of $I_4$ associated with the class of $g$ is $192\cdot 2^\alpha / o^{+}(g)$ (Lemma 6.2
for one class, $\rho = 2^\alpha$, $o^{+}(I_4) = 192$). -/
theorem fiber_card_four {a : ℕ} (ha : Odd a) (hsf : Squarefree a) {g : QuadForm ℤ 3} (hgs : g ∈ lemma66Set a) :
    (Nat.card {b // b ∈ primRepSet (pclassOf (sumSq 4)).out a ∧
        assocClass (pclassOf (sumSq 4)).out b = pclassOf g} : ℝ) =
      192 * 2 ^ a.primeFactors.card / Nat.card (AutPlus g) := by
  have hgs' := hgs
  obtain ⟨hg, hpd, hdet, -⟩ := hgs'
  have ha0 : 0 < a := ha.pos
  have key := sigmaWeight_eq (m := 3) (by norm_num) (ci_sumSq_gen 4) posDef_sumSq ha0 hg hpd
    (by rw [hdet, casselsMat_sumSq_gen, det_one]; simp)
  rw [rhoCount_sumSq_four ha hsf hgs] at key
  unfold sigmaWeight at key
  rw [pgenusClasses_sumSq_four, finsum_mem_singleton] at key
  have hs : SameGenus (sumSq 4) (pclassOf (sumSq 4)).out :=
    mem_pgenusClasses_iff_out.mp (by rw [pgenusClasses_sumSq_four]; rfl)
  have hA : Nat.card (AutPlus (pclassOf (sumSq 4)).out) = 192 := by
    rw [← card_autPlus_eq_of_intEquiv (sameGenus_sumSq_intEquiv (n := 4) (by norm_num) hs),
      card_autPlus_sumSq_four]
  rw [hA] at key
  have hog : (0 : ℝ) < Nat.card (AutPlus g) := by exact_mod_cast card_autPlus_pos hpd
  push_cast at key
  field_simp at key ⊢
  linarith

/-- **Cassels, Lemma 6.6** (Ch. 9, p. 152; formula (6.47) reconstructed): *let $a > 0$ be odd and squarefree and let
$\mathcal G$ be the genus of positive definite forms $g$ with $d(g) = a^2$ which are $\mathbb Z_p$-equivalent to
$-y_1^2 + 2ay_2y_3$ (6.46) for all odd primes $p$. Then $W(\mathcal G) = \frac{1}{24}\prod_{p \mid a}\frac{p+1}{2}$
(6.47).* The formula (6.47) is lost in the scan; this value is forced by Lemma 6.5 and Lemma 6.2 (and agrees with the
case $a = 1$, where the set is the class of $I_3$ and $W = 1/o^{+}(I_3) = 1/24$).

Hypotheses: `ha` ($a$ odd, so $a > 0$) and `hsf` ($a$ squarefree). The weight is `lemma66Weight a`, over the proper classes of
the forms of `lemma66Set a` (the library does not prove that this set is a single genus, which Cassels presupposes;
$W$ is a sum over the set). *Proof (not Cassels'):* Cassels computes the weight by a lattice count (6.48)–(6.59) and
then deduces Lemma 6.5 from it. Here the logic is reversed: the number of primitive representations of $a$ by $I_4$ is
$8\prod_{p \mid a}(p+1)$ (Lemma 6.5, `primRepNum_sumSq_four`, from Jacobi's four-square theorem); Lemma 6.2 for one class
(`sigmaWeight_eq`) shows that those associated with the class of $g$ number $192\cdot 2^\alpha/o^{+}(g)$ and that the
classes that occur are those of the set (`assocClass_mem_four`); summing over the classes gives
$8\prod(p+1) = 192\cdot 2^\alpha W$, $\alpha = \omega(a)$. Unconditional. -/
@[kb "cassels1978" "Ch. 9, Lemma 6.6, (6.47), p. 152"]
theorem weight_lemma66 {a : ℕ} (ha : Odd a) (hsf : Squarefree a) :
    lemma66Weight a = (1 / 24) * ∏ p ∈ a.primeFactors, ((p : ℝ) + 1) / 2 := by
  classical
  have ha0 : 0 < a := ha.pos
  have hsfZ : Squarefree (a : ℤ) := Int.squarefree_natCast.mpr hsf
  set f0 := (pclassOf (sumSq 4)).out with hf0def
  have hs : SameGenus (sumSq 4) f0 :=
    mem_pgenusClasses_iff_out.mp (by rw [pgenusClasses_sumSq_four]; rfl)
  have hci : IsClassicallyIntegral f0 := hs.isClassicallyIntegral (ci_sumSq_gen 4)
  have hpd : IntQF.PosDef f0 := hs.posDef posDef_sumSq
  have hdet : (casselsMat f0).det = 1 := by
    rw [← casselsMat_det_eq (ci_sumSq_gen 4) hci hs, casselsMat_sumSq_gen, det_one]
  have hequiv : IntEquiv (sumSq 4) f0 := sameGenus_sumSq_intEquiv (n := 4) (by norm_num) hs
  have hset : ∀ f : QuadForm ℤ 4, primRepSet f a = repSet f a := fun f => by
    ext b
    exact ⟨fun h => h.2, fun h => ⟨gcd_eq_one_of_squarefree hsfZ h, h⟩⟩
  have hrep : Nat.card (primRepSet f0 a) = 8 * ∏ p ∈ a.primeFactors, (p + 1) := by
    rw [← primRepNum_sumSq_four ha hsf, primRepNum, hset, hset]
    exact (repNum_eq_of_intEquiv hequiv a).symm
  have hPfin : (primRepSet f0 a).Finite := (IntQF.PosDef.repSet_finite hpd a).subset fun b hb => hb.2
  set φ : (Fin 4 → ℤ) → PClass 3 := assocClass f0 with hφ
  have hout : ∀ g : QuadForm ℤ 3, Nat.card (AutPlus (pclassOf g).out) = Nat.card (AutPlus g) := fun g =>
    card_autPlus_eq_of_intEquiv (pclassOf_eq_pclassOf_iff.mp (pclassOf_out (pclassOf g))).intEquiv
  -- the real count of each fibre
  have hfib : ∀ C ∈ hPfin.toFinset.image φ,
      ((hPfin.toFinset.filter (fun b => φ b = C)).card : ℝ) =
        192 * 2 ^ a.primeFactors.card * ((Nat.card (AutPlus C.out) : ℝ))⁻¹ := by
    intro C hC
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨g, hg, hbg⟩ := assocClass_mem_four hci hpd hdet hsf ((Set.Finite.mem_toFinset _).mp hb)
    have hcard : (hPfin.toFinset.filter (fun b' => φ b' = φ b)).card =
        Nat.card {b' // b' ∈ primRepSet f0 a ∧ assocClass f0 b' = pclassOf g} := by
      rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hφ, hbg]
    rw [hcard, fiber_card_four ha hsf hg]
    have hbg' : φ b = pclassOf g := hbg
    rw [hbg', hout g, div_eq_mul_inv]
  have himage : (↑(hPfin.toFinset.image φ) : Set (PClass 3)) = pclassOf '' lemma66Set a := by
    ext C
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨g, hg, hbg⟩ := assocClass_mem_four hci hpd hdet hsf hb
      exact ⟨g, hg, hbg.symm⟩
    · rintro ⟨g, hg, rfl⟩
      have hog : (0 : ℝ) < Nat.card (AutPlus g) := by exact_mod_cast card_autPlus_pos hg.2.1
      have hpos : 0 < Nat.card {b // b ∈ primRepSet f0 a ∧ assocClass f0 b = pclassOf g} := by
        have := fiber_card_four ha hsf hg
        have h0 : (0 : ℝ) < (Nat.card {b // b ∈ primRepSet (pclassOf (sumSq 4)).out a ∧
            assocClass (pclassOf (sumSq 4)).out b = pclassOf g} : ℝ) := by
          rw [this]; positivity
        exact_mod_cast h0
      obtain ⟨⟨b, hb⟩⟩ := Nat.card_pos_iff.mp hpos |>.1
      exact ⟨b, hb.1, hb.2⟩
  have hsum : (Nat.card (primRepSet f0 a) : ℝ) = 192 * 2 ^ a.primeFactors.card * lemma66Weight a := by
    rw [lemma66Weight, ← himage, finsum_mem_coe_finset, Finset.mul_sum, Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card _ hPfin, Finset.card_eq_sum_card_image φ, Nat.cast_sum]
    exact Finset.sum_congr rfl hfib
  rw [hrep] at hsum
  have h2 : (0 : ℝ) < 2 ^ a.primeFactors.card := by positivity
  rw [Finset.prod_div_distrib, Finset.prod_const, mul_div_assoc']
  push_cast at hsum
  field_simp
  linarith

/-! ### Part G: positive definite forms are equivalent over $\mathbb R$ -/

/-- A positive definite real symmetric matrix is $S^{\mathsf T}S$ with $S$ invertible (LDL decomposition). -/
theorem exists_transpose_mul_self_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, IsUnit S.det ∧ Sᵀ * S = A := by
  set L := LDL.lowerInv hA with hL
  have hLi : Invertible L := LDL.invertibleLowerInv hA
  have hLu : IsUnit L := isUnit_of_invertible L
  have hLd : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp hLu
  have hD : LDL.diag hA = L * A * Lᵀ := by
    rw [LDL.diag_eq_lowerInv_conj hA, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hDpd : (LDL.diag hA).PosDef := by
    have := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := A) hLu).mpr hA
    rw [hD]
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hpos : ∀ i, 0 < LDL.diagEntries hA i := fun i => by
    have := hDpd.diag_pos (i := i)
    simpa [LDL.diag] using this
  set d := LDL.diagEntries hA with hd
  set Dh : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => Real.sqrt (d i)) with hDh
  refine ⟨Dh * (L⁻¹)ᵀ, ?_, ?_⟩
  · rw [det_mul, det_transpose, hDh, det_diagonal]
    refine IsUnit.mul ?_ ?_
    · exact (Finset.prod_ne_zero_iff.mpr fun i _ => (Real.sqrt_pos.mpr (hpos i)).ne').isUnit
    · exact isUnit_iff_exists_inv.mpr ⟨L.det, by rw [← det_mul, Matrix.nonsing_inv_mul L hLd, det_one]⟩
  · have hsq : Dh * Dh = LDL.diag hA := by
      rw [hDh, LDL.diag, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact Real.mul_self_sqrt (hpos i).le
    have hDhT : Dhᵀ = Dh := by rw [hDh, Matrix.diagonal_transpose]
    have e1 : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hLd
    have e2 : Lᵀ * (L⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    calc (Dh * (L⁻¹)ᵀ)ᵀ * (Dh * (L⁻¹)ᵀ) = L⁻¹ * (Dh * Dh) * (L⁻¹)ᵀ := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose, hDhT]
          simp only [Matrix.mul_assoc]
      _ = A := by
          rw [hsq, hD]
          calc L⁻¹ * (L * A * Lᵀ) * (L⁻¹)ᵀ = (L⁻¹ * L) * A * (Lᵀ * (L⁻¹)ᵀ) := by
                simp only [Matrix.mul_assoc]
            _ = A := by rw [e1, e2]; simp

/-- Cassels' matrix of a positive definite classically integral form is positive definite over $\mathbb R$. -/
theorem posDef_real_casselsMat {n : ℕ} {f : QuadForm ℤ n} (hf : IsClassicallyIntegral f) (hp : IntQF.PosDef f) :
    ((casselsMat f).map (Int.castRingHom ℝ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.map_apply, star_trivial]
    rw [(casselsMat_isSymm f).apply j i]
  · have h := Kneser.two_mul_evalIn (K := ℝ) f x
    have hpos := hp.evalIn_real_pos x hx
    rw [hessian_eq_two_smul_casselsMat hf] at h
    simp only [star_trivial]
    have hm : ((2 : ℤ) • casselsMat f).map (algebraMap ℤ ℝ) =
        (2 : ℝ) • (casselsMat f).map (Int.castRingHom ℝ) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, algebraMap_int_eq, Int.cast_mul, Int.cast_ofNat]
    rw [hm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
    linarith

/-- **Positive definite classically integral forms are equivalent over $\mathbb R$.** -/
theorem isometricGL_real_of_posDef {n : ℕ} {f g : QuadForm ℤ n} (hf : IsClassicallyIntegral f)
    (hg : IsClassicallyIntegral g) (hfp : IntQF.PosDef f) (hgp : IntQF.PosDef g) :
    IsometricGL (f.map (Int.castRingHom ℝ)) (g.map (Int.castRingHom ℝ)) := by
  obtain ⟨S, hS, hSe⟩ := exists_transpose_mul_self_of_posDef (posDef_real_casselsMat hf hfp)
  obtain ⟨S', hS', hSe'⟩ := exists_transpose_mul_self_of_posDef (posDef_real_casselsMat hg hgp)
  refine isometricGL_of_meq_casselsMat' hf hg ⟨S⁻¹ * S', ?_, ?_⟩
  · rw [det_mul]
    exact IsUnit.mul (by rw [Matrix.det_nonsing_inv]; simpa using hS) hS'
  · rw [← hSe, ← hSe', Matrix.transpose_mul]
    have e1 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS
    have e2 : Sᵀ * (S⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    calc S'ᵀ * (S⁻¹)ᵀ * (Sᵀ * S) * (S⁻¹ * S') = S'ᵀ * ((S⁻¹)ᵀ * Sᵀ) * (S * S⁻¹) * S' := by
          simp only [Matrix.mul_assoc]
      _ = S'ᵀ * S' := by
          have e3 : (S⁻¹)ᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv S hS, Matrix.transpose_one]
          rw [e3, Matrix.mul_nonsing_inv S hS]; simp

/-! ### Part H: the corollary -/

/-- **Forms of Cassels' set with Cassels matrices congruent modulo $4$ lie in one genus.** At an odd prime both are
$\mathbb Z_p$-equivalent to $-y_0^2 + 2ay_1y_2$; at $p = 2$ the matrices are congruent modulo $4$ and of the same
$2$-adic unit determinant $a^2$ (`CongrLocal.meq_of_congr` with $c = 1$); over $\mathbb R$ both are positive definite. -/
theorem sameGenus_lemma66 {a : ℕ} (ha : Odd a) {g g' : QuadForm ℤ 3} (hg : g ∈ lemma66Set a)
    (hg' : g' ∈ lemma66Set a) (hcong : ∀ i j, (4 : ℤ) ∣ casselsMat g i j - casselsMat g' i j) :
    SameGenus g g' := by
  obtain ⟨hci, hpd, hdet, hloc⟩ := hg
  obtain ⟨hci', hpd', hdet', hloc'⟩ := hg'
  refine ⟨fun p hp => ?_, isometricGL_real_of_posDef hci hci' hpd hpd'⟩
  by_cases hp2 : p = 2
  · subst hp2
    apply isometricGL_of_meq_casselsMat 2 hci hci'
    have hsym : ∀ q : QuadForm ℤ 3, ((casselsMat q).map (Int.castRingHom ℤ_[2]))ᵀ =
        (casselsMat q).map (Int.castRingHom ℤ_[2]) := fun q => by
      rw [← transpose_map, (casselsMat_isSymm q).eq]
    have hmap : ∀ M : Matrix (Fin 3) (Fin 3) ℤ, (M.map (Int.castRingHom ℤ_[2])).det = (M.det : ℤ_[2]) :=
      fun M => (RingHom.map_det _ M).symm
    have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.pos.ne'
    have hunit : IsUnit ((a : ℤ_[2]) ^ 2) := by
      refine IsUnit.pow 2 ?_
      rw [CongrLocal.isUnit_iff_not_dvd]
      intro hd
      have : ((2 : ℕ) : ℤ_[2]) ∣ (((a : ℕ) : ℤ) : ℤ_[2]) := by simpa using hd
      rw [CongrLocal.cast_dvd_iff] at this
      exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr (by exact_mod_cast this))
    refine CongrLocal.meq_of_congr (p := 2) (Fin 3) _ _ 1 (hsym g) (hsym g') ?_ ?_ ?_ ⟨1, isUnit_one, ?_⟩
    · rw [hmap, hdet]; exact_mod_cast pow_ne_zero 2 ha0
    · rw [hmap, hdet]
      simpa using hunit.dvd
    · intro i j
      have h1 := map_dvd (Int.castRingHom ℤ_[2]) (hcong i j).neg_right
      rw [neg_sub] at h1
      simpa using h1
    · rw [hmap, hmap, hdet, hdet']; simp
  · have h1 := hloc p hp2
    have h2 := hloc' p hp2
    exact isometricGL_of_meq_casselsMat p hci hci' (h1.symm.trans h2)

/-- **Pigeonhole:** a finite set `s` of more than `card β * N` elements mapped to a finite type `β` has a fibre
with more than `N` elements. -/
theorem exists_lt_ncard_fiber {α β : Type*} [Fintype β] (s : Set α) (hs : s.Finite) (F : α → β) (N : ℕ)
    (h : Fintype.card β * N < hs.toFinset.card) : ∃ y : β, N < {x | x ∈ s ∧ F x = y}.ncard := by
  classical
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := hs.toFinset)
    (t := (Finset.univ : Finset β)) (f := F) (n := N) (fun _ _ => Finset.mem_univ _)
    (by rwa [Finset.card_univ])
  refine ⟨y, ?_⟩
  have : {x | x ∈ s ∧ F x = y} = ↑(hs.toFinset.filter fun x => F x = y) := by
    ext x; simp
  rw [this, Set.ncard_coe_finset]
  exact hy

/-- For each $k$ there is an odd squarefree $a$ with exactly $k$ prime factors. -/
theorem exists_odd_squarefree_card (k : ℕ) : ∃ a : ℕ, Odd a ∧ Squarefree a ∧ a.primeFactors.card = k := by
  induction k with
  | zero => exact ⟨1, odd_one, squarefree_one, by simp⟩
  | succ k ih =>
    obtain ⟨a, hao, hasf, hac⟩ := ih
    obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (a + 3)
    have ha0 : 0 < a := hao.pos
    have hpa : ¬ p ∣ a := fun h => by have := Nat.le_of_dvd ha0 h; omega
    have hp2 : p ≠ 2 := by omega
    refine ⟨a * p, hao.mul (hp.odd_of_ne_two hp2), ?_, ?_⟩
    · exact (Nat.squarefree_mul ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa).symm).mpr ⟨hasf, hp.squarefree⟩
    · rw [Nat.primeFactors_mul ha0.ne' hp.ne_zero, hp.primeFactors, Finset.card_union_of_disjoint]
      · simp [hac]
      · exact Finset.disjoint_singleton_right.mpr (fun h => hpa (Nat.dvd_of_mem_primeFactors h))

/-- **Cassels, Corollary to Lemma 6.6** (Ch. 9, p. 154): *the number of classes in a genus may be arbitrarily large.*
For every $N$ there is a positive definite ternary form $g$ (classically integral, of determinant $a^2$, $a$ odd
squarefree) whose genus contains at least $N$ proper classes (`(pgenusClasses g).ncard`, the proper classes of the
genus of $g$; the set is finite).

*Proof (via Lemma 6.6):* for $a$ the product of $k$ odd primes the weight of Cassels' set is
$W = \frac1{24}\prod_{p\mid a}\frac{p+1}{2} \ge 2^k/24$ (`weight_lemma66`), and $o^{+} \ge 1$, so the set has at least
$2^k/24$ proper classes. The classes can be sorted into at most $4^9$ residue classes of Cassels' matrix modulo $4$,
and forms of the set with congruent matrices modulo $4$ lie in one genus (`sameGenus_lemma66`). So some genus
has at least $2^k/(24\cdot 4^9)$ classes. -/
@[kb "cassels1978" "Ch. 9, Cor. to Lemma 6.6, p. 154"]
theorem exists_many_classes (N : ℕ) : ∃ g : QuadForm ℤ 3, IntQF.PosDef g ∧ N ≤ (pgenusClasses g).ncard := by
  classical
  obtain ⟨a, hao, hasf, hac⟩ := exists_odd_squarefree_card (24 * 4 ^ 9 * N + 1)
  set k := 24 * 4 ^ 9 * N + 1 with hk
  have hW := weight_lemma66 hao hasf
  have hWge : (2 : ℝ) ^ k / 24 ≤ lemma66Weight a := by
    rw [hW]
    have h2 : (2 : ℝ) ^ k ≤ ∏ p ∈ a.primeFactors, ((p : ℝ) + 1) / 2 := by
      calc (2 : ℝ) ^ k = ∏ _p ∈ a.primeFactors, (2 : ℝ) := by rw [Finset.prod_const, hac]
        _ ≤ _ := by
          refine Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun p hp => ?_)
          have hp2 : p ≠ 2 := by
            rintro rfl
            exact (Nat.not_even_iff_odd.mpr hao) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
          have h3 : 3 ≤ p := by
            have := (Nat.prime_of_mem_primeFactors hp).two_le
            omega
          have : (3 : ℝ) ≤ p := by exact_mod_cast h3
          linarith
    linarith
  set f : PClass 3 → ℝ := fun C => ((Nat.card (AutPlus C.out) : ℝ))⁻¹ with hf
  set S := pclassOf '' lemma66Set a with hS
  have hWpos : 0 < lemma66Weight a := lt_of_lt_of_le (by positivity) hWge
  have hTfin : (S ∩ Function.support f).Finite := by
    by_contra h
    have h0 : lemma66Weight a = 0 := finsum_mem_eq_zero_of_infinite h
    linarith
  have hWeq : lemma66Weight a = ∑ᶠ C ∈ S ∩ Function.support f, f C := (finsum_mem_inter_support f S).symm
  have hle : lemma66Weight a ≤ (hTfin.toFinset.card : ℝ) := by
    rw [hWeq, finsum_mem_eq_finite_toFinset_sum _ hTfin]
    calc ∑ C ∈ hTfin.toFinset, f C ≤ ∑ _C ∈ hTfin.toFinset, (1 : ℝ) := by
          refine Finset.sum_le_sum fun C _ => ?_
          simp only [hf]
          rcases Nat.eq_zero_or_pos (Nat.card (AutPlus C.out)) with h | h
          · simp [h]
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast h)
      _ = _ := by simp
  have hcardR : ((4 ^ 9 * N : ℕ) : ℝ) < hTfin.toFinset.card := by
    have h1 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (k : ℝ) = 24 * 4 ^ 9 * N + 1 := by rw [hk]; push_cast; ring
    push_cast
    linarith
  have hcardN : 4 ^ 9 * N < hTfin.toFinset.card := by exact_mod_cast hcardR
  have hrep : ∀ C ∈ hTfin.toFinset, ∃ g, g ∈ lemma66Set a ∧ pclassOf g = C := fun C hC =>
    ((Set.Finite.mem_toFinset hTfin).mp hC).1
  have : Nonempty (QuadForm ℤ 3) := ⟨sumSq 3⟩
  choose! rep hrepmem hrepcls using hrep
  set F : PClass 3 → (Fin 3 → Fin 3 → ZMod 4) := fun C i j => ((casselsMat (rep C) i j : ℤ) : ZMod 4) with hF
  have hcardU : Fintype.card (Fin 3 → Fin 3 → ZMod 4) = 4 ^ 9 := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  obtain ⟨y, hy⟩ := exists_lt_ncard_fiber (S ∩ Function.support f) hTfin F N (by rw [hcardU]; exact hcardN)
  have hne : {x | x ∈ S ∩ Function.support f ∧ F x = y}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨C0, hC0⟩ := hne
  have hg0 := hrepmem C0 ((Set.Finite.mem_toFinset hTfin).mpr hC0.1)
  refine ⟨rep C0, hg0.2.1, ?_⟩
  have hsub : {x | x ∈ S ∩ Function.support f ∧ F x = y} ⊆ pgenusClasses (rep C0) := by
    intro C hC
    have hCT := (Set.Finite.mem_toFinset hTfin).mpr hC.1
    refine ⟨rep C, hrepcls C hCT, sameGenus_lemma66 hao hg0 (hrepmem C hCT) fun i j => ?_⟩
    have h1 : F C i j = F C0 i j := by rw [hC.2, hC0.2]
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (casselsMat (rep C) i j) (casselsMat (rep C0) i j) 4).mp h1
    exact_mod_cast this
  exact hy.le.trans (Set.ncard_le_ncard hsub (pgenusClasses_finite (by norm_num) hg0.2.1.nondegenerate))

end QuadFormsKB.Siegel
