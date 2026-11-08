/-
# Cassels, Chapter 10, Theorem 7.1: the first stage of the proof for $n \ge 4$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §7, proof of Theorem 7.1 for $n \ge 4$, p. 189:
"For $p \in P_1$ select $u^{(p)} \in \mathcal U_p$. Then ... $u^{(p)} = a_1^{(p)}\cdots a_r^{(p)}$ ... with $\phi(a_1^{(p)})\cdots\phi(a_r^{(p)}) = 1$
... The next stage is to find $a_j \in V$ such that $\phi(a_1)\cdots\phi(a_r) = 1$ and the $a_j$ are arbitrarily close to the $a_j^{(p)}$."

**Proves.**
* `exists_vprod_of_mem_spinGroup`: every $u \in \operatorname{Spin}(V)$ is $a_1\cdots a_r$ with $r \ge 2$ even, anisotropic $a_j$ and
  $\prod\phi(a_j) = 1$ (Theorem 3.1, Corollary 1, with the scalar absorbed into $a_1$); padding to any larger even length
  (`exists_vprod_length`);
* `continuous_vprodP`: the product map $(\xi_1, \dots, \xi_r) \mapsto a_1\cdots a_r$ in coordinates is continuous.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Main
import QuadFormsKB.Literature.Cassels.Ch10.SquareRoot

open CliffordAlgebra TensorProduct Module Matrix Topology Filter

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Thm71Five

open QuadFormsKB.Cassels Thm71Ternary Thm71Spin Thm71Coords Thm71Approx

/-- Helper (file-local): the vector space topology on $C(V_p)$. -/
noncomputable local instance cliffTop' {V : Type} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : TopologicalSpace (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  cliffordTopology (Q.baseChange ℚ_[p])

local instance cliffModTop' {V : Type} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : IsModuleTopology ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) := ⟨rfl⟩

local instance cliffFin' {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : Module.Finite ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  finiteDimensional_clifford (Q.baseChange ℚ_[p])

local instance cliffTopRing' {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Q : QuadraticForm ℚ V) (p : ℕ) [Fact p.Prime] : IsTopologicalRing (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  IsModuleTopology.isTopologicalRing ℚ_[p] _

section Decomp

variable {k W : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup W] [Module k W] {Q : QuadraticForm k W}

theorem coe_vecProd [FiniteDimensional k W] (l : List W) (hl : ∀ y ∈ l, Q y ≠ 0) :
    (((vecProd l hl : cliffordGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = vprod Q l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [vecProd_cons, vprod_cons, ← ih fun z hz => hl z (List.mem_cons_of_mem a hz)]
    rfl

/-- **Cassels, Theorem 3.1, Corollary 1 for $\operatorname{Spin}$** (p. 177, as used on p. 189): $u = a_1\cdots a_r$ with $r \ge 2$
even, anisotropic $a_j$, $\prod_j\phi(a_j) = 1$. -/
theorem exists_vprod_of_mem_spinGroup [FiniteDimensional k W] [Nontrivial W]
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (u : spinGroup Q) :
    ∃ l : List W, 2 ≤ l.length ∧ Even l.length ∧ (∀ a ∈ l, Q a ≠ 0) ∧ (u : CliffordAlgebra Q) = vprod Q l ∧
      (l.map Q).prod = 1 := by
  obtain ⟨l, hl, c, hc, hev, -, hu⟩ := exists_eq_smul_vecProd hQ ⟨spinGroup.toUnits u, spinGroup_mem_M0 u⟩
  change (u : CliffordAlgebra Q) = _ at hu
  rw [coe_vecProd] at hu
  obtain ⟨a₀, ha₀⟩ := exists_anisotropic hQ
  -- absorb the scalar
  obtain ⟨l', hl'2, hl'ev, hl'a, hl'u⟩ : ∃ l' : List W, 2 ≤ l'.length ∧ Even l'.length ∧ (∀ a ∈ l', Q a ≠ 0) ∧
      (u : CliffordAlgebra Q) = vprod Q l' := by
    cases l with
    | nil =>
      refine ⟨[c • a₀, (Q a₀)⁻¹ • a₀], le_rfl, ⟨1, rfl⟩, ?_, ?_⟩
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · rw [QuadraticMap.map_smul, smul_eq_mul]; exact mul_ne_zero (mul_ne_zero hc hc) ha₀
        · rw [QuadraticMap.map_smul, smul_eq_mul]
          exact mul_ne_zero (mul_ne_zero (inv_ne_zero ha₀) (inv_ne_zero ha₀)) ha₀
      · rw [hu]
        simp only [vprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_smul,
          smul_mul_smul_comm, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul]
        rw [mul_assoc, inv_mul_cancel₀ ha₀, mul_one]
    | cons a l₀ =>
      refine ⟨(c • a) :: l₀, ?_, by simpa using hev, ?_, ?_⟩
      · have : l₀.length ≠ 0 := by
          intro h0
          rw [List.length_cons, h0] at hev
          exact (Nat.not_even_one) hev
        simp only [List.length_cons]; omega
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · rw [QuadraticMap.map_smul, smul_eq_mul]; exact mul_ne_zero (mul_ne_zero hc hc) (hl a List.mem_cons_self)
        · exact hl b (List.mem_cons_of_mem _ hb)
      · rw [hu, vprod_cons, vprod_cons, map_smul, smul_mul_assoc]
  refine ⟨l', hl'2, hl'ev, hl'a, hl'u, ?_⟩
  have h1 := spinGroup_mul_reverse u
  rw [hl'u, vprod_mul_reverse, ← map_one (algebraMap k (CliffordAlgebra Q))] at h1
  exact (algebraMap k (CliffordAlgebra Q)).injective h1

/-- Helper: the padding pairs $[a, \phi(a)^{-1}a]$ multiply to $1$. -/
theorem vprod_flatten_replicate {a : W} (ha : Q a ≠ 0) (k : ℕ) :
    vprod Q (List.replicate k [a, (Q a)⁻¹ • a]).flatten = 1 ∧
      ((List.replicate k [a, (Q a)⁻¹ • a]).flatten.map Q).prod = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, vprod_append, List.map_append, List.prod_append, ih.1, ih.2]
    simp only [vprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_smul,
      mul_smul_comm, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul, QuadraticMap.map_smul, smul_eq_mul]
    constructor
    · rw [inv_mul_cancel₀ ha, one_smul]
    · field_simp

/-- **Padding to a prescribed even length** (Cassels, p. 189: "by appending terms of the type $aa^{-1}$ ... we may suppose
that $r$ is the same for all $p$"). -/
theorem exists_vprod_length [FiniteDimensional k W] [Nontrivial W]
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (u : spinGroup Q) (l : List W) (_hl2 : 2 ≤ l.length)
    (hlev : Even l.length) (hla : ∀ a ∈ l, Q a ≠ 0) (hlu : (u : CliffordAlgebra Q) = vprod Q l)
    (hlQ : (l.map Q).prod = 1) (r : ℕ) (hr : l.length ≤ r) (hrev : Even r) :
    ∃ l' : List W, l'.length = r ∧ (∀ a ∈ l', Q a ≠ 0) ∧ (u : CliffordAlgebra Q) = vprod Q l' ∧
      (l'.map Q).prod = 1 := by
  obtain ⟨a₀, ha₀⟩ := exists_anisotropic hQ
  obtain ⟨k, hk⟩ : ∃ k, r = l.length + 2 * k := by
    obtain ⟨a, ha⟩ := hlev; obtain ⟨b, hb⟩ := hrev; exact ⟨b - a, by omega⟩
  have hpad := vprod_flatten_replicate ha₀ k
  refine ⟨l ++ (List.replicate k [a₀, (Q a₀)⁻¹ • a₀]).flatten, ?_, ?_, ?_, ?_⟩
  · simp [hk, List.length_flatten]; ring
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hla a ha
    · obtain ⟨x, hx, hax⟩ := List.mem_flatten.1 ha
      rw [(List.eq_of_mem_replicate hx)] at hax
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with rfl | rfl
      · exact ha₀
      · rw [QuadraticMap.map_smul, smul_eq_mul]
        exact mul_ne_zero (mul_ne_zero (inv_ne_zero ha₀) (inv_ne_zero ha₀)) ha₀
  · rw [vprod_append, hpad.1, mul_one, hlu]
  · rw [List.map_append, List.prod_append, hpad.2, mul_one, hlQ]

end Decomp

section Cont

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] {Q : QuadraticForm ℚ V}
  {n : ℕ} (e : Basis (Fin n) ℚ V)

/-- The product $a_1\cdots a_r$ in coordinates. -/
noncomputable def vprodP (p : ℕ) [Fact p.Prime] {r : ℕ} (ξ : Fin r → Fin n → ℚ_[p]) :
    CliffordAlgebra (Q.baseChange ℚ_[p]) :=
  vprod (Q.baseChange ℚ_[p]) (List.ofFn fun i => vecP e p (ξ i))

theorem continuous_vprodP (p : ℕ) [Fact p.Prime] :
    ∀ r : ℕ, Continuous fun ξ : Fin r → Fin n → ℚ_[p] => vprodP (Q := Q) e p ξ
  | 0 => by simp only [vprodP, List.ofFn_zero, vprod_nil]; exact continuous_const
  | r + 1 => by
    have h := continuous_vprodP p r
    have : (fun ξ : Fin (r + 1) → Fin n → ℚ_[p] => vprodP (Q := Q) e p ξ) =
        fun ξ => ι (Q.baseChange ℚ_[p]) (vecP e p (ξ 0)) * vprodP (Q := Q) e p (fun i => ξ i.succ) := by
      funext ξ
      simp only [vprodP, List.ofFn_succ, vprod_cons]
    rw [this]
    exact ((continuous_ι_vecP (Q := Q) (e := e) p).comp (continuous_apply 0)).mul
      (h.comp (continuous_pi fun i => continuous_apply i.succ))

/-- **Closeness neighbourhoods of a continuous function of $r$ coordinate vectors.** -/
theorem exists_closeR {p : ℕ} [Fact p.Prime] {r : ℕ} {X : Type*} [TopologicalSpace X]
    {F : (Fin r → Fin n → ℚ_[p]) → X} {x₀ : Fin r → Fin n → ℚ_[p]}
    (hF : ContinuousAt F x₀) {S : Set X} (hS : S ∈ 𝓝 (F x₀)) :
    ∃ K : ℕ, ∀ x, (∀ i, Close p K (x i) (x₀ i)) → F x ∈ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hF hS)
  obtain ⟨K, hK⟩ := exists_pow_lt (p := p) hε
  refine ⟨K, fun x hx => hball ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  exact fun i => dist_lt_of_close hε hK (hx i)

end Cont

section Good

variable {n : ℕ}

/-- Helper: at an odd prime not dividing its Hessian determinant, an integral form in $n \ge 3$ variables is isotropic over
$\mathbb Q_p$ (a unimodular lattice of rank $\ge 3$ represents $0$ primitively). -/
theorem exists_isotropic_good (f : QuadForm ℤ n) (hn : 3 ≤ n) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ f.hessian.det) : ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ f.evalIn ℚ_[p] x = 0 := by
  obtain ⟨x, ⟨i, hi⟩, hx⟩ := Lattices.exists_primitive_padic_of_unimodular p hp2 f hdet hn 0
  refine ⟨fun j => (x j : ℚ_[p]), fun h => hi.ne_zero ?_, ?_⟩
  · have := congrFun h i
    simpa using this
  · rw [← coe_eval_padic, hx]; simp

/-- Helper: at such a prime $f$ represents every rational over $\mathbb Q_p$. -/
theorem exists_rep_good (f : QuadForm ℤ n) (hn : 3 ≤ n) (hf : f.hessian.det ≠ 0) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ f.hessian.det) (c : ℚ) :
    ∃ x : Fin n → ℚ_[p], f.evalIn ℚ_[p] x = (c : ℚ_[p]) := by
  obtain ⟨x, hx0, hx⟩ := exists_isotropic_good f hn p hp2 hdet
  have hnd : (f.map (Int.castRingHom ℚ)).Nondegenerate := Lattices.nondegenerate_map_of_det_ne_zero f hf
  have hiso : (f.map (Int.castRingHom ℚ)).IsotropicIn ℚ_[p] :=
    ⟨x, hx0, by rw [← hx]; simp [QuadForm.evalIn, QuadForm.map]⟩
  obtain ⟨y, hy⟩ := Lattices.representsIn_of_isotropicIn (f.map (Int.castRingHom ℚ)) ℚ_[p] hnd c hiso
  refine ⟨y, ?_⟩
  rw [← eq_ratCast (algebraMap ℚ ℚ_[p]), ← hy]
  simp [QuadForm.evalIn, QuadForm.map]

end Good

section FirstStage

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] {Q : QuadraticForm ℚ V}
  {n : ℕ} (e : Basis (Fin n) ℚ V)

/-- **The first stage of Cassels' proof of Theorem 7.1, $n \ge 4$** (p. 189): given at each $p$ of a finite non-empty set $T$
(containing $2$ and the primes dividing the determinant of the integral model $f$) anisotropic vectors
$a_1^{(p)}, \dots, a_{s+1}^{(p)}$ (coordinates `a p i`) with $\prod_i\phi(a_i^{(p)}) = 1$ and an open neighbourhood $\mathcal O_p$ of
$a_1^{(p)}\cdots a_{s+1}^{(p)}$, there are rational vectors $a_1, \dots, a_{s+1}$ with $\prod_i\phi(a_i) = 1$ and $a_1\cdots a_{s+1} \in \mathcal O_p$
for $p \in T$. Proof: $a_1, \dots, a_s$ close to the $a_i^{(p)}$ (weak approximation); $m = (\phi(a_1)\cdots\phi(a_s))^{-1}$; local
$\tilde a^{(p)}_{s+1} = \sqrt{m/\phi(a^{(p)}_{s+1})}\,a^{(p)}_{s+1}$ close to $a^{(p)}_{s+1}$ with $\phi = m$; $a_{s+1}$ with $\phi(a_{s+1}) = m$ close to
them (Lemma 7.1; Cassels uses the Strong Hasse Principle and Ch. 6, Lemma 9.1, Corollary). -/
theorem firstStage (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 4 ≤ n)
    {N : Matrix (Fin n) (Fin n) ℤ} (hNs : Nᵀ = N) {D : ℕ} (hD : 0 < D)
    (hND : N.map (Int.cast : ℤ → ℚ) = (D : ℚ) • gram Q e)
    (hfind : ∃ x y : Fin n → ℝ, (LocalDensity.ofMatrixZ N).evalIn ℝ x < 0 ∧ 0 < (LocalDensity.ofMatrixZ N).evalIn ℝ y)
    (T : Finset Nat.Primes) (hTne : T.Nonempty) (hT2 : ∀ p : Nat.Primes, p ∉ T → (p : ℕ) ≠ 2)
    (hTd : ∀ p : Nat.Primes, p ∉ T → ¬ ((p : ℕ) : ℤ) ∣ (LocalDensity.ofMatrixZ N).hessian.det)
    (s : ℕ) (a : ∀ p : Nat.Primes, Fin (s + 1) → Fin n → ℚ_[(p : ℕ)])
    (ha : ∀ p ∈ T, ∀ i, Q.baseChange ℚ_[(p : ℕ)] (vecP e p (a p i)) ≠ 0)
    (hprod : ∀ p ∈ T, ∏ i, Q.baseChange ℚ_[(p : ℕ)] (vecP e p (a p i)) = 1)
    (O : ∀ p : Nat.Primes, Set (CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])))
    (hO : ∀ p ∈ T, IsOpen (O p) ∧ vprodP (Q := Q) e p (a p) ∈ O p) :
    ∃ y : Fin (s + 1) → Fin n → ℚ, ∏ i, Q (vecG e (y i)) = 1 ∧
      ∀ p ∈ T, vprodP (Q := Q) e p (fun i j => (y i j : ℚ_[(p : ℕ)])) ∈ O p := by
  classical
  set f := LocalDensity.ofMatrixZ N with hfdef
  have hfdet : f.hessian.det ≠ 0 := det_hessian_ne_zero e hQ hNs hD hND
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  -- precision for the product
  have hK1 : ∀ p : Nat.Primes, ∃ K : ℕ, p ∈ T → ∀ x : Fin (s + 1) → Fin n → ℚ_[(p : ℕ)],
      (∀ i, Close p K (x i) (a p i)) → vprodP (Q := Q) e p x ∈ O p := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨K, hK⟩ := exists_closeR (continuous_vprodP (Q := Q) e p (s + 1)).continuousAt
        ((hO p hp).1.mem_nhds (hO p hp).2)
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose K1 hK1 using hK1
  -- the square root near $1$ and the corrected last vector
  have hloc : ∀ p : Nat.Primes, ∃ (K : ℕ) (W : Set ℚ_[(p : ℕ)]) (r : ℚ_[(p : ℕ)] → ℚ_[(p : ℕ)]), p ∈ T →
      (∀ d ∈ W, r d ^ 2 = d) ∧ ∀ ξ : Fin s → Fin n → ℚ_[(p : ℕ)], (∀ i, Close p K (ξ i) (a p i.castSucc)) →
        (∏ i, Q.baseChange ℚ_[(p : ℕ)] (vecP e p (ξ i))) ≠ 0 ∧
        (∏ i, Q.baseChange ℚ_[(p : ℕ)] (vecP e p (ξ i)))⁻¹ *
          (Q.baseChange ℚ_[(p : ℕ)] (vecP e p (a p (Fin.last s))))⁻¹ ∈ W ∧
        Close p (K1 p) (r ((∏ i, Q.baseChange ℚ_[(p : ℕ)] (vecP e p (ξ i)))⁻¹ *
          (Q.baseChange ℚ_[(p : ℕ)] (vecP e p (a p (Fin.last s))))⁻¹) • a p (Fin.last s)) (a p (Fin.last s)) := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨W, hW, r, hrc, hr1, hrsq⟩ := exists_local_sqrt_padic (p : ℕ) (b := 1) one_ne_zero
      rw [one_pow] at hW
      set qL := Q.baseChange ℚ_[(p : ℕ)] (vecP e p (a p (Fin.last s)))
      have hqL : qL ≠ 0 := ha p hp _
      set P : (Fin s → Fin n → ℚ_[(p : ℕ)]) → ℚ_[(p : ℕ)] :=
        fun ξ => ∏ i, Q.baseChange ℚ_[(p : ℕ)] (vecP e p (ξ i))
      have hPc : Continuous P :=
        continuous_finsetProd _ fun i _ => (continuous_Q_vecP (Q := Q) (e := e) p).comp (continuous_apply i)
      have hP0 : P (fun i => a p i.castSucc) = qL⁻¹ := by
        have := hprod p hp
        rw [Fin.prod_univ_castSucc] at this
        exact eq_inv_of_mul_eq_one_left this
      have hP0ne : P (fun i => a p i.castSucc) ≠ 0 := by rw [hP0]; exact inv_ne_zero hqL
      have hR : ContinuousAt (fun ξ => (P ξ)⁻¹ * qL⁻¹) (fun i => a p i.castSucc) :=
        (hPc.continuousAt.inv₀ hP0ne).mul continuousAt_const
      have hR1 : (P (fun i => a p i.castSucc))⁻¹ * qL⁻¹ = 1 := by rw [hP0, inv_inv, mul_inv_cancel₀ hqL]
      have hrc' : ContinuousAt r 1 := hrc.continuousAt hW
      have hz : ContinuousAt (fun ξ => r ((P ξ)⁻¹ * qL⁻¹) • a p (Fin.last s)) (fun i => a p i.castSucc) := by
        have h1 : ContinuousAt (fun ξ => r ((P ξ)⁻¹ * qL⁻¹)) (fun i => a p i.castSucc) := by
          refine ContinuousAt.comp (g := r) ?_ hR
          rw [hR1]; exact hrc'
        exact h1.smul continuousAt_const
      have hF : ContinuousAt (fun ξ => (P ξ, (P ξ)⁻¹ * qL⁻¹, r ((P ξ)⁻¹ * qL⁻¹) • a p (Fin.last s)))
          (fun i => a p i.castSucc) := hPc.continuousAt.prodMk (hR.prodMk hz)
      have hS : {w : ℚ_[(p : ℕ)] × ℚ_[(p : ℕ)] × (Fin n → ℚ_[(p : ℕ)]) | w.1 ≠ 0 ∧ w.2.1 ∈ W ∧
          Close p (K1 p) w.2.2 (a p (Fin.last s))} ∈
          𝓝 (P (fun i => a p i.castSucc), (P (fun i => a p i.castSucc))⁻¹ * qL⁻¹,
            r ((P (fun i => a p i.castSucc))⁻¹ * qL⁻¹) • a p (Fin.last s)) := by
        rw [one_pow] at hr1
        rw [hR1, hr1, one_smul]
        refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem
          ((isOpen_ne.preimage continuous_fst).mem_nhds hP0ne)
          (continuous_snd.continuousAt.preimage_mem_nhds (continuous_fst.continuousAt.preimage_mem_nhds hW)))
          (continuous_snd.continuousAt.preimage_mem_nhds
            (continuous_snd.continuousAt.preimage_mem_nhds (close_mem_nhds (K1 p) _)))) ?_
        intro w hw
        exact ⟨hw.1.1, hw.1.2, hw.2⟩
      obtain ⟨K, hK⟩ := exists_closeR hF hS
      refine ⟨K, W, r, fun _ => ⟨hrsq, fun ξ hξ => ?_⟩⟩
      obtain ⟨h1, h2, h3⟩ := hK ξ hξ
      exact ⟨h1, h2, h3⟩
    · exact ⟨0, ∅, id, fun h => absurd h hp⟩
  choose K2 W r hloc using hloc
  set KA : ℕ := T.sup fun p => max (K1 p) (K2 p) with hKA
  -- global $a_1, \dots, a_s$
  have hy := fun (i : Fin s) (j : Fin n) => exists_rat_approx T (fun p => a p i.castSucc j) KA
  choose y₀ hy₀ using hy
  have hcy₀ : ∀ p ∈ T, ∀ i, Close p (K2 p) (fun j => (y₀ i j : ℚ_[(p : ℕ)])) (a p i.castSucc) :=
    fun p hp i j => (hy₀ i j p hp).trans (zpow_le_zpow_right₀ (by exact_mod_cast p.2.one_lt.le)
      (by have := le_trans (le_max_right _ _) (Finset.le_sup (f := fun p => max (K1 p) (K2 p)) hp); omega))
  have hcy₀' : ∀ p ∈ T, ∀ i, Close p (K1 p) (fun j => (y₀ i j : ℚ_[(p : ℕ)])) (a p i.castSucc) :=
    fun p hp i j => (hy₀ i j p hp).trans (zpow_le_zpow_right₀ (by exact_mod_cast p.2.one_lt.le)
      (by have := le_trans (le_max_left _ _) (Finset.le_sup (f := fun p => max (K1 p) (K2 p)) hp); omega))
  have hcast : ∀ (p : Nat.Primes) (y : Fin n → ℚ),
      Q.baseChange ℚ_[(p : ℕ)] (vecP e p fun j => (y j : ℚ_[(p : ℕ)])) = (Q (vecG e y) : ℚ_[(p : ℕ)]) :=
    fun p y => Q_vecP_cast e p y
  set μ : ℚ := ∏ i, Q (vecG e (y₀ i)) with hμ
  have hμcast : ∀ p : Nat.Primes, (μ : ℚ_[(p : ℕ)]) =
      ∏ i, Q.baseChange ℚ_[(p : ℕ)] (vecP e p fun j => (y₀ i j : ℚ_[(p : ℕ)])) := by
    intro p; rw [hμ, Rat.cast_prod]; simp only [hcast]
  obtain ⟨p₀, hp₀⟩ := hTne
  have hμ0 : μ ≠ 0 := by
    have := ((hloc p₀ hp₀).2 _ (hcy₀ p₀ hp₀)).1
    rw [← hμcast] at this
    exact_mod_cast this
  set m : ℚ := μ⁻¹ with hm
  have hm0 : m ≠ 0 := inv_ne_zero hμ0
  -- local targets for the last vector
  set zT : ∀ p : Nat.Primes, Fin n → ℚ_[(p : ℕ)] := fun p =>
    r p ((∏ i, Q.baseChange ℚ_[(p : ℕ)] (vecP e p fun j => (y₀ i j : ℚ_[(p : ℕ)])))⁻¹ *
      (Q.baseChange ℚ_[(p : ℕ)] (vecP e p (a p (Fin.last s))))⁻¹) • a p (Fin.last s) with hzT
  have hzTQ : ∀ p ∈ T, Q.baseChange ℚ_[(p : ℕ)] (vecP e p (zT p)) = (m : ℚ_[(p : ℕ)]) := by
    intro p hp
    obtain ⟨hrsq, hξ⟩ := hloc p hp
    obtain ⟨-, hW, -⟩ := hξ _ (hcy₀ p hp)
    rw [hzT, vecP_smul, QuadraticMap.map_smul, smul_eq_mul, ← sq, hrsq _ hW, hm, Rat.cast_inv, hμcast,
      inv_mul_cancel_right₀ (ha p hp _)]
  have hzTc : ∀ p ∈ T, Close p (K1 p) (zT p) (a p (Fin.last s)) :=
    fun p hp => ((hloc p hp).2 _ (hcy₀ p hp)).2.2
  -- the extra primes where $Dm$ is not a unit
  set Pm : Finset Nat.Primes := (((D : ℚ) * m).num.natAbs * ((D : ℚ) * m).den).primeFactors.subtype Nat.Prime
  set P : Finset Nat.Primes := T ∪ Pm with hP
  have hgoodrep : ∀ p : Nat.Primes, ∃ x : Fin n → ℚ_[(p : ℕ)], p ∉ T →
      f.evalIn ℚ_[(p : ℕ)] x = (((D : ℚ) * m : ℚ) : ℚ_[(p : ℕ)]) := by
    intro p
    by_cases hp : p ∈ T
    · exact ⟨0, fun h => absurd hp h⟩
    · obtain ⟨x, hx⟩ := exists_rep_good f (by omega) hfdet p (hT2 p hp) (hTd p hp) ((D : ℚ) * m)
      exact ⟨x, fun _ => hx⟩
  choose zG hzG using hgoodrep
  set z : ∀ p : Nat.Primes, Fin n → ℚ_[(p : ℕ)] := fun p => if p ∈ T then zT p else zG p with hz
  have hfz : ∀ p ∈ P, f.evalIn ℚ_[(p : ℕ)] (z p) = (((D : ℚ) * m : ℚ) : ℚ_[(p : ℕ)]) := by
    intro p _
    simp only [hz]
    split_ifs with hp
    · rw [f_vecP hNs hND, hzTQ p hp]; push_cast; ring
    · exact hzG p hp
  have hDm : (D : ℚ) * m ≠ 0 := mul_ne_zero hD' hm0
  set KK : ℕ := T.sup K1
  obtain ⟨yL, hyL, hyLT, -⟩ := lemma71 f hn hfdet hfind P
    (fun p hp => hT2 p fun h => hp (Finset.mem_union_left _ h))
    (fun p hp => hTd p fun h => hp (Finset.mem_union_left _ h)) ((D : ℚ) * m) hDm
    (fun p hp => norm_rat_le_one _ fun h => hp (Finset.mem_union_right _ (Finset.mem_subtype.2
      (Nat.mem_primeFactors.2 ⟨p.2, dvd_mul_of_dvd_right h _,
        mul_ne_zero (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hDm)) ((D : ℚ) * m).den_nz⟩)))) z hfz KK
  have hQL : Q (vecG e yL) = m := by
    rw [f_vecG hNs hND] at hyL
    exact mul_left_cancel₀ hD' hyL
  refine ⟨Fin.snoc y₀ yL, ?_, fun p hp => hK1 p hp _ fun i => ?_⟩
  · rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← hμ, hQL, hm, mul_inv_cancel₀ hμ0]
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]
      have h1 : Close p KK (fun j => (yL j : ℚ_[(p : ℕ)])) (z p) := fun j => hyLT p (Finset.mem_union_left _ hp) j
      have h2 : Close p (K1 p) (fun j => (yL j : ℚ_[(p : ℕ)])) (zT p) := by
        have := h1.mono (Finset.le_sup (f := K1) hp)
        simpa [hz, hp] using this
      exact h2.trans (hzTc p hp)
    · simp only [Fin.snoc_castSucc]
      exact hcy₀' p hp i

end FirstStage

end QuadFormsKB.Cassels.Thm71Five
