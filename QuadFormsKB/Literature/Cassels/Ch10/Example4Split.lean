/-
# Cassels, Chapter 10, Example 4 (ii)–(iv): the even Clifford algebra of an isotropic ternary space is $M_2(k)$

**Setting.** As in `Ch10/Example4.lean`: $k$ a field of characteristic $\ne 2$, $(V, Q)$ regular of dimension $3$.
$C_0(V)$ is Mathlib's subalgebra `CliffordAlgebra.even Q`; its canonical involution $u \mapsto u'$ is `evenReverse`.

**Proves** (Cassels, *Rational Quadratic Forms*, Ch. 10, Example 4, p. 193)
* (ii) if $V$ is isotropic there is an algebra isomorphism $\lambda : C_0(V) \to M_2(k)$ with
  $\lambda(u') = \operatorname{adj}\lambda(u)$ (`exists_even_algEquiv_matrix`).
  *Erratum.* Cassels asks for $(\lambda(u))' = \lambda(u')$ where the $(')$ on the matrix is the transpose (his notation,
  Ch. 1, §2, p. 6). No isomorphism has that property (`not_exists_even_algEquiv_transpose`): $uu' \in k$ for every
  $u \in C_0(V)$ (Theorem 3.1, Corollary 2), while $AA^{\mathsf T}$ is not a scalar for
  $A = \begin{pmatrix}1&1\\0&1\end{pmatrix}$. The canonical involution corresponds to the adjugate
  $A \mapsto \operatorname{adj}A = (\operatorname{tr}A)I - A$.
* (iii) if moreover $-1 \in d(k^\times)^2$, i.e. $-d = -f_0f_1f_2$ is a square, every isomorphism $\lambda$ extends in
  exactly two ways to an algebra homomorphism $\mu_j : C(V) \to M_2(k)$ (`extensions_of_even_algEquiv`);
* (iv) for each extension, $M_2(k)$ is spanned by $\mu(1)$ and the $\mu(\vec v)$, $\vec v \in V$, and the $\mu(\vec v)$ are
  exactly the matrices of trace $0$ (`span_extension_eq_top`, `range_extension_eq_trace_zero`). (Cassels assumes the
  hypotheses of (iii); the statements hold for any homomorphism extending an isomorphism.)
-/
import QuadFormsKB.Literature.Cassels.Ch10.Example4

open Module CliffordAlgebra QuadFormsKB.OMeara

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {Q : QuadraticForm k V}

/-- The canonical involution restricted to $C_0(V)$. -/
def evenReverse (u : CliffordAlgebra.even Q) : CliffordAlgebra.even Q :=
  ⟨reverse (u : CliffordAlgebra Q), (reverse_mem_evenOdd_iff Q (n := 0)).2 u.2⟩

theorem coe_evenReverse (u : CliffordAlgebra.even Q) :
    ((evenReverse u : CliffordAlgebra.even Q) : CliffordAlgebra Q) = reverse (u : CliffordAlgebra Q) := rfl

theorem ex4ii_adapted (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : finrank k V = 3)
    (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0) :
    ∃ e : Basis (Fin 3) k V, (∀ i j, i ≠ j → bil Q (e i) (e j) = 0) ∧ Q (e 0) = 1 ∧ Q (e 1) = -1 ∧
      Q (e 2) ≠ 0 := by
  obtain ⟨x, hx0, hx⟩ := hiso
  obtain ⟨y, hy, hxy⟩ := QuadFormsKB.OMeara.exists_hyperbolic_pair Q hQ hx0 hx
  have hyx : bil Q y x = 1 := by rw [bil_comm, hxy]
  have hxx : bil Q x x = 0 := by rw [bil_self, hx]
  have hyy : bil Q y y = 0 := by rw [bil_self, hy]
  let φ : V →ₗ[k] k × k := (QuadraticMap.associated Q x).prod (QuadraticMap.associated Q y)
  have hrk : finrank k (LinearMap.range φ) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hker : 0 < finrank k (LinearMap.ker φ) := by omega
  obtain ⟨⟨z, hzk⟩, hz0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hker
  have hz0' : z ≠ 0 := fun h => hz0 (Subtype.ext h)
  have hzk' : φ z = 0 := hzk
  have hxz : bil Q x z = 0 := congrArg Prod.fst hzk'
  have hyz : bil Q y z = 0 := congrArg Prod.snd hzk'
  have hzx : bil Q z x = 0 := by rw [bil_comm]; exact hxz
  have hzy : bil Q z y = 0 := by rw [bil_comm]; exact hyz
  -- independence of x, y, z
  have hli : LinearIndependent k ![x, y, z] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hg
    have h1 := congrArg (fun w => bil Q w y) hg
    have h2 := congrArg (fun w => bil Q w x) hg
    simp only [bil_add_left, bil_smul_left, hxy, hyy, hzy, hyx, hxx, hzx] at h1 h2
    have h1' : bil Q 0 y = 0 := by simp [bil]
    have h2' : bil Q 0 x = 0 := by simp [bil]
    rw [h1'] at h1
    rw [h2'] at h2
    have g0 : g 0 = 0 := by simpa using h1
    have g1 : g 1 = 0 := by simpa using h2
    have g2 : g 2 = 0 := by
      rw [g0, g1] at hg
      simpa [hz0'] using hg
    intro i; fin_cases i <;> assumption
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hn])
  have hb : ∀ i, b i = ![x, y, z] i := fun i => by simp [b]
  have hzz : bil Q z z ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ : ∃ w, bil Q z w ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hz0' (hQ.1 z hcon)
    apply hw
    rw [← b.sum_repr w]
    simp only [Fin.sum_univ_three, hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    simp only [bil_add_right, bil_smul_right, bil_comm Q z x, bil_comm Q z y, hxz, hyz, h0]
    ring
  have h2 : (2 : k) ≠ 0 := Invertible.ne_zero (2 : k)
  have hli' : LinearIndependent k ![x + (2 : k)⁻¹ • y, x - (2 : k)⁻¹ • y, z] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hg
    have h1 := congrArg (fun w => bil Q w y) hg
    have h2' := congrArg (fun w => bil Q w x) hg
    simp only [bil_add_left, bil_sub_left, bil_smul_left, hxy, hyy, hzy, hyx, hxx, hzx] at h1 h2'
    have h1' : bil Q 0 y = 0 := by simp [bil]
    have h2'' : bil Q 0 x = 0 := by simp [bil]
    rw [h1'] at h1
    rw [h2''] at h2'
    have g01 : g 0 + g 1 = 0 := by linear_combination h1
    have g01' : g 0 - g 1 = 0 := by
      have : (2 : k)⁻¹ * (g 0 - g 1) = 0 := by linear_combination h2'
      simpa [h2] using this
    have g0 : g 0 = 0 := by
      have : (2 : k) * g 0 = 0 := by linear_combination g01 + g01'
      simpa [h2] using this
    have g1 : g 1 = 0 := by linear_combination g01 - g0
    have g2 : g 2 = 0 := by
      rw [g0, g1] at hg
      simpa [hz0'] using hg
    intro i; fin_cases i <;> assumption
  let e := basisOfLinearIndependentOfCardEqFinrank hli' (by simp [hn])
  have he : ∀ i, e i = ![x + (2 : k)⁻¹ • y, x - (2 : k)⁻¹ • y, z] i := fun i => by simp [e]
  have e0 := he 0
  have e1 := he 1
  have e2 := he 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e0 e1 e2
  have hq0 : bil Q (e 0) (e 0) = 1 := by
    rw [e0]
    simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, hxy, hyy, hyx, hxx]
    field_simp
    ring
  have hq1 : bil Q (e 1) (e 1) = -1 := by
    rw [e1]
    simp only [bil_sub_left, bil_sub_right, bil_smul_left, bil_smul_right, hxy, hyy, hyx, hxx]
    field_simp
    ring
  have h01 : bil Q (e 0) (e 1) = 0 := by
    rw [e0, e1]
    simp only [bil_add_left, bil_add_right, bil_sub_right, bil_smul_left, bil_smul_right, hxy, hyy, hyx, hxx]
    ring
  have h02 : bil Q (e 0) (e 2) = 0 := by
    rw [e0, e2]
    simp only [bil_add_left, bil_smul_left, hxz, hyz]
    ring
  have h12 : bil Q (e 1) (e 2) = 0 := by
    rw [e1, e2]
    simp only [bil_sub_left, bil_smul_left, hxz, hyz]
    ring
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip
    · exact h01
    · exact h02
    · rw [bil_comm]; exact h01
    · exact h12
    · rw [bil_comm]; exact h02
    · rw [bil_comm]; exact h12
  · rw [← bil_self]; exact hq0
  · rw [← bil_self]; exact hq1
  · rw [← bil_self, e2]; exact hzz


/-- Matrices for the products `e_i e_j` in the adapted basis. -/
def ex4ii_M (c : k) : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 2) k :=
  ![![1, !![1, 0; 0, -1], -!![0, 1; -c, 0]], ![-!![1, 0; 0, -1], -1, !![0, 1; c, 0]],
    ![!![0, 1; -c, 0], -!![0, 1; c, 0], c • 1]]

theorem ex4ii_Q_expand (e : Basis (Fin 3) k V)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0) (m : V) :
    Q m = ∑ i, (e.repr m i) ^ 2 * Q (e i) := by
  conv_lhs => rw [← e.sum_repr m]
  have hpol : ∀ (x y : Fin 3) (s t : k), x ≠ y →
      QuadraticMap.polar Q (s • e x) (t • e y) = 0 := by
    intro x y s t hxy
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, horth x y hxy]
    simp
  simp only [Fin.sum_univ_three]
  rw [QuadraticMap.map_add Q (_ + _) _, QuadraticMap.map_add Q (_ • _) _, QuadraticMap.polar_add_left,
    hpol 0 1 _ _ (by decide), hpol 0 2 _ _ (by decide), hpol 1 2 _ _ (by decide)]
  simp only [QuadraticMap.map_smul, smul_eq_mul]
  ring

variable (e : Basis (Fin 3) k V) (c : k)

theorem ex4ii_bilin_left (i : Fin 3) (n : V) :
    (e.constr k (fun i => e.constr k (fun j => ex4ii_M c i j))) (e i) n =
      ∑ j, e.repr n j • ex4ii_M c i j := by
  rw [Basis.constr_basis, Basis.constr_apply, Finsupp.sum_fintype _ _ (by simp)]

theorem ex4ii_bilin_right (m : V) (l : Fin 3) :
    (e.constr k (fun i => e.constr k (fun j => ex4ii_M c i j))) m (e l) =
      ∑ i, e.repr m i • ex4ii_M c i l := by
  rw [Basis.constr_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [LinearMap.sum_apply, Basis.constr_basis]

theorem ex4ii_bilin_apply (m n : V) :
    (e.constr k (fun i => e.constr k (fun j => ex4ii_M c i j))) m n =
      ∑ i, ∑ j, (e.repr m i * e.repr n j) • ex4ii_M c i j := by
  rw [Basis.constr_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [LinearMap.sum_apply, Basis.constr_apply, Finset.smul_sum, smul_smul]

theorem ex4ii_contract (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0)
    (h0 : Q (e 0) = 1) (h1 : Q (e 1) = -1) (h2 : Q (e 2) = c) (m : V) :
    (e.constr k (fun i => e.constr k (fun j => ex4ii_M c i j))) m m = algebraMap k _ (Q m) := by
  rw [ex4ii_bilin_apply, ex4ii_Q_expand e horth]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [ex4ii_M, Fin.sum_univ_three, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, h0, h1, h2] <;> ring

theorem ex4ii_key (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0)
    (h0 : Q (e 0) = 1) (h1 : Q (e 1) = -1) (h2 : Q (e 2) = c) (i l : Fin 3) (m : V) :
    (e.constr k (fun i => e.constr k (fun j => ex4ii_M c i j))) (e i) m *
      (e.constr k (fun i => e.constr k (fun j => ex4ii_M c i j))) m (e l) =
    Q m • (e.constr k (fun i => e.constr k (fun j => ex4ii_M c i j))) (e i) (e l) := by
  rw [ex4ii_bilin_left, ex4ii_bilin_right, ex4ii_bilin_left, ex4ii_Q_expand e horth]
  fin_cases i <;> fin_cases l <;> (ext p q; fin_cases p <;> fin_cases q) <;>
    simp [ex4ii_M, Fin.sum_univ_three, Matrix.mul_apply, h0, h1, h2] <;> ring

/-- The even-Clifford `EvenHom` into `M₂(k)`. -/
noncomputable def ex4ii_hom (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0)
    (h0 : Q (e 0) = 1) (h1 : Q (e 1) = -1) (h2 : Q (e 2) = c) :
    EvenHom Q (Matrix (Fin 2) (Fin 2) k) where
  bilin := e.constr k (fun i => e.constr k (fun j => ex4ii_M c i j))
  contract := ex4ii_contract e c horth h0 h1 h2
  contract_mid m₁ m₂ m₃ := by
    have key := fun i l => ex4ii_key e c horth h0 h1 h2 i l m₂
    rw [← e.sum_repr m₁, ← e.sum_repr m₃]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_mul,
      Finset.mul_sum, smul_mul_assoc, mul_smul_comm, key, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    module

theorem ex4ii_coe_ι (m n : V) :
    (((even.ι Q).bilin m n : CliffordAlgebra.even Q) : CliffordAlgebra Q) = ι Q m * ι Q n := rfl

/-- The even element $u_0 + u_1E_0 + u_2E_1 + u_3E_2$. -/
noncomputable def ex4ii_U (Q : QuadraticForm k V) (e : Basis (Fin 3) k V) (cc : Fin 4 → k) :
    CliffordAlgebra.even Q :=
  algebraMap k _ (cc 0) + cc 1 • (even.ι Q).bilin (e 1) (e 2) + cc 2 • (even.ι Q).bilin (e 2) (e 0) +
    cc 3 • (even.ι Q).bilin (e 0) (e 1)

theorem ex4ii_coe_U (Q : QuadraticForm k V) (e : Basis (Fin 3) k V) (cc : Fin 4 → k) :
    ((ex4ii_U Q e cc : CliffordAlgebra.even Q) : CliffordAlgebra Q) = ternElt Q e cc := by
  simp only [ex4ii_U, ternElt, ternE]
  rfl

/-- The matrix of $u_0 + u_1E_0 + u_2E_1 + u_3E_2$. -/
def ex4ii_Φ (c : k) (cc : Fin 4 → k) : Matrix (Fin 2) (Fin 2) k :=
  !![cc 0 + cc 3, cc 1 + cc 2; c * (cc 1 - cc 2), cc 0 - cc 3]

theorem ex4ii_main (e : Basis (Fin 3) k V)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0)
    (h0 : Q (e 0) = 1) (h1 : Q (e 1) = -1) (hc : Q (e 2) ≠ 0) :
    ∃ L : CliffordAlgebra.even Q ≃ₐ[k] Matrix (Fin 2) (Fin 2) k,
      ∀ u : CliffordAlgebra.even Q, L (evenReverse u) = (L u).adjugate := by
  have h2 : (2 : k) ≠ 0 := Invertible.ne_zero (2 : k)
  set c := Q (e 2) with hcdef
  let Λ := even.lift Q (ex4ii_hom (e := e) (c := c) horth h0 h1 rfl)
  have hΛ : ∀ a b, Λ ((even.ι Q).bilin (e a) (e b)) = ex4ii_M c a b := by
    intro a b
    show (even.lift Q (ex4ii_hom (e := e) (c := c) horth h0 h1 rfl)) ((even.ι Q).bilin (e a) (e b)) = _
    rw [even.lift_ι]
    show (e.constr k (fun i => e.constr k (fun j => ex4ii_M c i j))) (e a) (e b) = _
    rw [Basis.constr_basis, Basis.constr_basis]
  have hΛU : ∀ cc, Λ (ex4ii_U Q e cc) = ex4ii_Φ c cc := by
    intro cc
    simp only [ex4ii_U, map_add, map_smul, AlgHom.commutes, hΛ]
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [ex4ii_M, ex4ii_Φ, Algebra.algebraMap_eq_smul_one] <;> ring
  have hU : ∀ u : CliffordAlgebra.even Q, ∃ cc, u = ex4ii_U Q e cc := by
    intro u
    obtain ⟨cc, hcc⟩ := (mem_evenOdd_zero_iff_ternary horth _).1 u.2
    exact ⟨cc, Subtype.ext (by rw [ex4ii_coe_U]; exact hcc)⟩
  have hinj : Function.Injective Λ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨cc, rfl⟩ := hU u
    rw [hΛU] at hu
    have a1 := congrFun (congrFun hu 0) 0
    have a2 := congrFun (congrFun hu 0) 1
    have a3 := congrFun (congrFun hu 1) 0
    have a4 := congrFun (congrFun hu 1) 1
    simp only [ex4ii_Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply] at a1 a2 a3 a4
    have c3 : cc 3 = 0 := by
      have : (2 : k) * cc 3 = 0 := by linear_combination a1 - a4
      simpa [h2] using this
    have c0 : cc 0 = 0 := by linear_combination a1 - c3
    have c12 : cc 1 - cc 2 = 0 := by simpa [hc] using a3
    have c2 : cc 2 = 0 := by
      have : (2 : k) * cc 2 = 0 := by linear_combination a2 - c12
      simpa [h2] using this
    have c1 : cc 1 = 0 := by linear_combination c12 + c2
    simp [ex4ii_U, c0, c1, c2, c3]
  have hsurj : Function.Surjective Λ := by
    intro A
    refine ⟨ex4ii_U Q e ![(A 0 0 + A 1 1) / 2, (A 0 1 + A 1 0 / c) / 2, (A 0 1 - A 1 0 / c) / 2,
      (A 0 0 - A 1 1) / 2], ?_⟩
    rw [hΛU]
    ext p q
    fin_cases p <;> fin_cases q <;> simp [ex4ii_Φ] <;> field_simp <;> ring
  refine ⟨AlgEquiv.ofBijective Λ ⟨hinj, hsurj⟩, fun u => ?_⟩
  obtain ⟨cc, rfl⟩ := hU u
  have hr1 : reverse (1 : CliffordAlgebra Q) = 1 := by
    simpa using reverse.commutes (Q := Q) (1 : k)
  have hrev : evenReverse (ex4ii_U Q e cc) = ex4ii_U Q e ![cc 0, -cc 1, -cc 2, -cc 3] := by
    apply Subtype.ext
    rw [coe_evenReverse, ex4ii_coe_U, ex4ii_coe_U]
    simp only [ternElt, map_add, map_smul, reverse.commutes, reverse_ternE horth,
      Algebra.algebraMap_eq_smul_one, smul_neg, hr1]
    simp [sub_eq_add_neg]
  show Λ (evenReverse (ex4ii_U Q e cc)) = (Λ (ex4ii_U Q e cc)).adjugate
  rw [hrev, hΛU, hΛU, ex4ii_Φ, ex4ii_Φ, Matrix.adjugate_fin_two]
  ext p q
  fin_cases p <;> fin_cases q <;> simp <;> ring

/-- **Cassels, Ch. 10, Example 4 (ii)** (p. 193), corrected: if $V$ is a regular isotropic ternary space, there is an
algebra isomorphism $\lambda : C_0(V) \to M_2(k)$ carrying the canonical involution to the adjugate,
$\lambda(u') = \operatorname{adj}\lambda(u)$. -/
@[kb "cassels1978" "Ch. 10, Example 4 (ii), p. 193 (C₀(V) ≅ M₂(k) for isotropic V; involution ↦ adjugate)"]
theorem exists_even_algEquiv_matrix (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : finrank k V = 3)
    (hiso : ∃ x : V, x ≠ 0 ∧ Q x = 0) :
    ∃ L : CliffordAlgebra.even Q ≃ₐ[k] Matrix (Fin 2) (Fin 2) k,
      ∀ u : CliffordAlgebra.even Q, L (evenReverse u) = (L u).adjugate := by
  obtain ⟨e, hb, h0, h1, hc⟩ := ex4ii_adapted hQ hn hiso
  refine ex4ii_main e (fun i j hij => ?_) h0 h1 hc
  rw [polar_eq_two_mul_bil, hb i j hij, mul_zero]

/-- **Erratum to Cassels, Ch. 10, Example 4 (ii)**: no algebra isomorphism $\lambda : C_0(V) \to M_2(k)$ carries the
canonical involution to the transpose. -/
@[kb "cassels1978" "Ch. 10, Example 4 (ii), p. 193 (erratum: transpose impossible)"]
theorem not_exists_even_algEquiv_transpose (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : finrank k V = 3) :
    ¬ ∃ L : CliffordAlgebra.even Q ≃ₐ[k] Matrix (Fin 2) (Fin 2) k,
      ∀ u : CliffordAlgebra.even Q, L (evenReverse u) = Matrix.transpose (L u) := by
  rintro ⟨L, hL⟩
  obtain ⟨u, hu⟩ := L.surjective !![1, 1; 0, 1]
  obtain ⟨c, hc⟩ := mul_reverse_mem_of_even hQ hn u.2
  have h1 : u * evenReverse u = algebraMap k (CliffordAlgebra.even Q) c :=
    Subtype.ext (by simpa [coe_evenReverse] using hc)
  have h2 := congrArg L h1
  rw [map_mul, hL, AlgEquiv.commutes, hu] at h2
  have h3 := congrFun (congrFun h2 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_eq_diagonal] at h3

section Extensions

variable (e : Basis (Fin 3) k V) (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0)
  (hne : ∀ i, Q (e i) ≠ 0) (hQ : (QuadraticMap.associated Q).Nondegenerate)
include horth hne hQ

/-- $-f_0f_1f_2$. -/
noncomputable abbrev ex4iii_c (Q : QuadraticForm k V) (e : Basis (Fin 3) k V) : k := -(Q (e 0) * Q (e 1) * Q (e 2))

theorem ex4iii_c_ne : ex4iii_c Q e ≠ 0 := by
  have := hne 0; have := hne 1; have := hne 2
  simp only [ex4iii_c, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2)

theorem ex4iii_eps_odd : ternEps Q e ∈ evenOdd Q 1 := by
  have h := SetLike.mul_mem_graded (t_ee (Q := Q) (e 0) (e 1)) (ι_mem_evenOdd_one Q (e 2))
  rwa [zero_add] at h

theorem ex4iii_mem (x : V) : ι Q x * ternEps Q e ∈ evenOdd Q 0 := by
  have h := SetLike.mul_mem_graded (ι_mem_evenOdd_one Q x) (ex4iii_eps_odd e horth hne hQ)
  rwa [show (1 : ZMod 2) + 1 = 0 from by decide] at h

/-- $x \mapsto x\epsilon \in C_0(V)$. -/
noncomputable def ex4iii_g (x : V) : CliffordAlgebra.even Q :=
  ⟨ι Q x * ternEps Q e, ex4iii_mem e horth hne hQ x⟩

theorem ex4iii_g_val (x : V) :
    (ex4iii_g e horth hne hQ x : CliffordAlgebra Q) = ι Q x * ternEps Q e := rfl

theorem ex4iii_g_mul (x y : V) :
    ex4iii_g e horth hne hQ x * ex4iii_g e horth hne hQ y =
      ex4iii_c Q e • (⟨ι Q x * ι Q y, t_ee x y⟩ : CliffordAlgebra.even Q) := by
  apply Subtype.ext
  show ι Q x * ternEps Q e * (ι Q y * ternEps Q e) = ex4iii_c Q e • (ι Q x * ι Q y)
  have h1 := ternEps_comm_ι horth y
  have h2 := ternEps_sq horth
  calc ι Q x * ternEps Q e * (ι Q y * ternEps Q e)
      = ι Q x * (ternEps Q e * ι Q y) * ternEps Q e := by simp only [mul_assoc]
    _ = ι Q x * ι Q y * (ternEps Q e * ternEps Q e) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by
      rw [h2, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

theorem ex4iii_g_sq (x : V) :
    ex4iii_g e horth hne hQ x * ex4iii_g e horth hne hQ x =
      algebraMap k (CliffordAlgebra.even Q) (Q x * ex4iii_c Q e) := by
  rw [ex4iii_g_mul]
  apply Subtype.ext
  show ex4iii_c Q e • (ι Q x * ι Q x) = algebraMap k (CliffordAlgebra Q) (Q x * ex4iii_c Q e)
  rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]

theorem ex4iii_g_inj (x : V) (h : ex4iii_g e horth hne hQ x = 0) : x = 0 := by
  have h0 : ι Q x * ternEps Q e = 0 := congrArg Subtype.val h
  have h2 := ternEps_sq horth (e := e)
  have : ι Q x * (ternEps Q e * ternEps Q e) = 0 := by rw [← mul_assoc, h0, zero_mul]
  rw [h2, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at this
  have hc := ex4iii_c_ne e horth hne hQ
  have hx : ι Q x = 0 := by
    rcases smul_eq_zero.1 this with h | h
    · exact absurd h hc
    · exact h
  exact cliffordι_injective Q (by rw [hx, map_zero])

theorem ex4iii_rev_g (x : V) : reverse (ι Q x * ternEps Q e) = -(ι Q x * ternEps Q e) := by
  have hε : reverse (ternEps Q e) = -ternEps Q e := by
    have : ternEps Q e = ι Q (e 0) * (ι Q (e 1) * ι Q (e 2)) := by simp only [ternEps, mul_assoc]
    rw [this]; exact t_revT horth
  rw [reverse.map_mul, hε, reverse_ι, neg_mul, ternEps_comm_ι horth]

variable (L : CliffordAlgebra.even Q ≃ₐ[k] Matrix (Fin 2) (Fin 2) k)

noncomputable def ex4iii_lin (t : k) : V →ₗ[k] Matrix (Fin 2) (Fin 2) k where
  toFun x := t⁻¹ • L (ex4iii_g e horth hne hQ x)
  map_add' x y := by
    have : ex4iii_g e horth hne hQ (x + y) = ex4iii_g e horth hne hQ x + ex4iii_g e horth hne hQ y :=
      Subtype.ext (by simp only [ex4iii_g_val, map_add, add_mul]; rfl)
    rw [this, map_add, smul_add]
  map_smul' c x := by
    have : ex4iii_g e horth hne hQ (c • x) = c • ex4iii_g e horth hne hQ x :=
      Subtype.ext (by simp only [ex4iii_g_val, map_smul, smul_mul_assoc]; rfl)
    rw [this, map_smul]
    simp only [RingHom.id_apply]
    rw [smul_comm]

theorem ex4iii_lin_sq {t : k} (ht : t * t = ex4iii_c Q e) (x : V) :
    ex4iii_lin e horth hne hQ L t x * ex4iii_lin e horth hne hQ L t x = algebraMap k _ (Q x) := by
  have hc := ex4iii_c_ne e horth hne hQ
  have ht0 : t ≠ 0 := fun h => hc (by rw [← ht, h, zero_mul])
  show (t⁻¹ • L (ex4iii_g e horth hne hQ x)) * (t⁻¹ • L (ex4iii_g e horth hne hQ x)) = _
  rw [smul_mul_smul_comm, ← map_mul, ex4iii_g_sq, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, smul_smul]
  congr 1
  rw [← ht]
  field_simp

noncomputable def ex4iii_mu (t : k) (ht : t * t = ex4iii_c Q e) :
    CliffordAlgebra Q →ₐ[k] Matrix (Fin 2) (Fin 2) k :=
  CliffordAlgebra.lift Q ⟨ex4iii_lin e horth hne hQ L t, ex4iii_lin_sq e horth hne hQ L ht⟩

theorem ex4iii_mu_ι (t : k) (ht : t * t = ex4iii_c Q e) (x : V) :
    ex4iii_mu e horth hne hQ L t ht (ι Q x) = t⁻¹ • L (ex4iii_g e horth hne hQ x) := by
  simp [ex4iii_mu, ex4iii_lin]

theorem ex4iii_mu_even (t : k) (ht : t * t = ex4iii_c Q e) (u : CliffordAlgebra.even Q) :
    ex4iii_mu e horth hne hQ L t ht u = L u := by
  have hc := ex4iii_c_ne e horth hne hQ
  have ht0 : t ≠ 0 := fun h => hc (by rw [← ht, h, zero_mul])
  obtain ⟨u, hu⟩ := u
  refine CliffordAlgebra.even_induction Q
    (motive := fun x hx => ex4iii_mu e horth hne hQ L t ht x = L ⟨x, hx⟩) ?_ ?_ ?_ u hu
  · intro r
    rw [AlgHom.commutes]
    exact (L.commutes r).symm
  · intro x y hx hy ihx ihy
    rw [map_add, ihx, ihy]
    exact (map_add L ⟨x, hx⟩ ⟨y, hy⟩).symm
  · intro a b x hx ih
    rw [map_mul, map_mul, ex4iii_mu_ι, ex4iii_mu_ι, ih]
    have key : t⁻¹ * t⁻¹ * ex4iii_c Q e = 1 := by rw [← ht]; field_simp
    calc t⁻¹ • L (ex4iii_g e horth hne hQ a) * t⁻¹ • L (ex4iii_g e horth hne hQ b) * L ⟨x, hx⟩
        = (t⁻¹ * t⁻¹) • L (ex4iii_g e horth hne hQ a * ex4iii_g e horth hne hQ b * ⟨x, hx⟩) := by
          rw [smul_mul_smul_comm, smul_mul_assoc, map_mul, map_mul]
      _ = _ := by
          rw [ex4iii_g_mul, smul_mul_assoc, map_smul, smul_smul, key, one_smul]
          rfl

theorem ex4iii_ext (μ : CliffordAlgebra Q →ₐ[k] Matrix (Fin 2) (Fin 2) k)
    (hμ : ∀ u : CliffordAlgebra.even Q, μ u = L u) :
    ∃ a : k, a * a = ex4iii_c Q e ∧ ∀ x : V, μ (ι Q x) = a⁻¹ • L (ex4iii_g e horth hne hQ x) := by
  have hcomm : ∀ B : Matrix (Fin 2) (Fin 2) k, μ (ternEps Q e) * B = B * μ (ternEps Q e) := by
    intro B
    obtain ⟨u, rfl⟩ := L.surjective B
    rw [← hμ u, ← map_mul, ← map_mul, ternEps_comm horth]
  obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single (M := μ (ternEps Q e))
    (fun i j _ => (hcomm _).symm)
  have hT : μ (ternEps Q e) = algebraMap k _ a := by
    rw [← ha]
    rw [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  have haa : a * a = ex4iii_c Q e := by
    have h1 : μ (ternEps Q e * ternEps Q e) = algebraMap k _ (ex4iii_c Q e) := by
      rw [ternEps_sq horth, AlgHom.commutes]
    rw [map_mul, hT, ← map_mul] at h1
    exact (algebraMap k (Matrix (Fin 2) (Fin 2) k)).injective h1
  have hc := ex4iii_c_ne e horth hne hQ
  have ha0 : a ≠ 0 := fun h => hc (by rw [← haa, h, zero_mul])
  refine ⟨a, haa, fun x => ?_⟩
  have h2 : μ (ι Q x * ternEps Q e) = L (ex4iii_g e horth hne hQ x) := hμ (ex4iii_g e horth hne hQ x)
  rw [map_mul, hT, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at h2
  rw [← h2, smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem ex4iii_range (μ : CliffordAlgebra Q →ₐ[k] Matrix (Fin 2) (Fin 2) k)
    (hμ : ∀ u : CliffordAlgebra.even Q, μ u = L u) (x : V) : (μ (ι Q x)).trace = 0 := by
  obtain ⟨a, ha, hι⟩ := ex4iii_ext e horth hne hQ L μ hμ
  have hc := ex4iii_c_ne e horth hne hQ
  have ha0 : a ≠ 0 := fun h => hc (by rw [← ha, h, zero_mul])
  have hAA : μ (ι Q x) * μ (ι Q x) = Q x • (1 : Matrix (Fin 2) (Fin 2) k) := by
    rw [← map_mul, ι_sq_scalar, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  have hCH : ∀ A : Matrix (Fin 2) (Fin 2) k, A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) k) := by
    intro A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring
  by_contra htr
  have hι' := hι x
  generalize hA : μ (ι Q x) = A at hAA htr hι'
  have h1 : A.trace • A = (Q x + A.det) • (1 : Matrix (Fin 2) (Fin 2) k) := by
    have := hCH A
    rw [hAA] at this
    rw [add_smul]
    exact sub_eq_iff_eq_add.1 this.symm
  obtain ⟨r, hr⟩ : ∃ r : k, A = r • (1 : Matrix (Fin 2) (Fin 2) k) :=
    ⟨A.trace⁻¹ * (Q x + A.det), by rw [← smul_smul, ← h1, smul_smul, inv_mul_cancel₀ htr, one_smul]⟩
  have hLg : L (ex4iii_g e horth hne hQ x) = a • A := by
    rw [hι', smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hg : ex4iii_g e horth hne hQ x = algebraMap k _ (a * r) := by
    apply L.injective
    rw [hLg, hr, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one, smul_smul]
  have hv : ι Q x * ternEps Q e = algebraMap k (CliffordAlgebra Q) (a * r) := congrArg Subtype.val hg
  have hrev := ex4iii_rev_g e horth hne hQ x
  rw [hv, reverse.commutes, eq_neg_iff_add_eq_zero, ← map_add] at hrev
  have h3 := (algebraMap k (CliffordAlgebra Q)).injective (hrev.trans (map_zero _).symm)
  rw [← two_mul] at h3
  have h2 : (2 : k) ≠ 0 := Invertible.ne_zero (2 : k)
  have hr0 : a * r = 0 := (mul_eq_zero.1 h3).resolve_left h2
  have hr00 : r = 0 := (mul_eq_zero.1 hr0).resolve_left ha0
  apply htr
  rw [hr, hr00, zero_smul, Matrix.trace_zero]

theorem ex4iii_range_eq (μ : CliffordAlgebra Q →ₐ[k] Matrix (Fin 2) (Fin 2) k)
    (hμ : ∀ u : CliffordAlgebra.even Q, μ u = L u) :
    Set.range (fun x => μ (ι Q x)) = {A : Matrix (Fin 2) (Fin 2) k | A.trace = 0} := by
  obtain ⟨a, ha, hι⟩ := ex4iii_ext e horth hne hQ L μ hμ
  have hc := ex4iii_c_ne e horth hne hQ
  have ha0 : a ≠ 0 := fun h => hc (by rw [← ha, h, zero_mul])
  let φ : V →ₗ[k] Matrix (Fin 2) (Fin 2) k := μ.toLinearMap ∘ₗ ι Q
  have hφ : ∀ x, φ x = μ (ι Q x) := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : a⁻¹ • L (ex4iii_g e horth hne hQ x) = 0 := by rw [← hι, ← hφ]; exact hx
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd (inv_eq_zero.1 h) ha0
    · exact ex4iii_g_inj e horth hne hQ x ((map_eq_zero_iff L L.injective).1 h)
  have hle : LinearMap.range φ ≤ LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k) := by
    rintro _ ⟨x, rfl⟩
    exact ex4iii_range e horth hne hQ L μ hμ x
  have hdim : finrank k V = 3 := by simpa using Module.finrank_eq_card_basis e
  have hr : finrank k (LinearMap.range φ) = 3 := by rw [LinearMap.finrank_range_of_inj hinj, hdim]
  have hk : finrank k (LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)) = 3 := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) k k)
    have hsurj : LinearMap.range (Matrix.traceLinearMap (Fin 2) k k) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨Matrix.of ![![c, 0], ![0, 0]], by simp [Matrix.trace_fin_two]⟩
    rw [hsurj, finrank_top, finrank_self, Module.finrank_matrix] at h
    simp at h
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle (hr.trans hk.symm)
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    exact ex4iii_range e horth hne hQ L μ hμ x
  · intro hA
    have : A ∈ LinearMap.range φ := by
      rw [heq]; exact LinearMap.mem_ker.2 hA
    obtain ⟨x, rfl⟩ := this
    exact ⟨x, rfl⟩


/-- **Cassels, Ch. 10, Example 4 (iii)** (p. 193): if $-1 \in d(k^\times)^2$ (equivalently $-f_0f_1f_2$ is a square),
an algebra isomorphism $\lambda : C_0(V) \to M_2(k)$ extends in exactly two ways to an algebra homomorphism
$\mu_j : C(V) \to M_2(k)$. -/
@[kb "cassels1978" "Ch. 10, Example 4 (iii), p. 193 (exactly two extensions to C(V))"]
theorem extensions_of_even_algEquiv (hd : IsSquare (-(Q (e 0) * Q (e 1) * Q (e 2))))
    (L : CliffordAlgebra.even Q ≃ₐ[k] Matrix (Fin 2) (Fin 2) k) :
    ∃ μ₁ μ₂ : CliffordAlgebra Q →ₐ[k] Matrix (Fin 2) (Fin 2) k, μ₁ ≠ μ₂ ∧
      (∀ u : CliffordAlgebra.even Q, μ₁ u = L u) ∧ (∀ u : CliffordAlgebra.even Q, μ₂ u = L u) ∧
      ∀ μ : CliffordAlgebra Q →ₐ[k] Matrix (Fin 2) (Fin 2) k, (∀ u : CliffordAlgebra.even Q, μ u = L u) →
        μ = μ₁ ∨ μ = μ₂ := by
  obtain ⟨s, hs⟩ := hd
  have hs' : s * s = ex4iii_c Q e := hs.symm
  have hs2 : (-s) * (-s) = ex4iii_c Q e := by rw [neg_mul_neg]; exact hs'
  have hc := ex4iii_c_ne e horth hne hQ
  have hs0 : s ≠ 0 := fun h => hc (by rw [← hs', h, zero_mul])
  refine ⟨ex4iii_mu e horth hne hQ L s hs', ex4iii_mu e horth hne hQ L (-s) hs2, ?_,
    ex4iii_mu_even e horth hne hQ L s hs', ex4iii_mu_even e horth hne hQ L (-s) hs2, ?_⟩
  · intro h
    have h1 := congrArg (fun f => f (ι Q (e 0))) h
    simp only [ex4iii_mu_ι, inv_neg, neg_smul] at h1
    rw [eq_neg_iff_add_eq_zero, ← two_smul k] at h1
    have h2 : (2 : k) ≠ 0 := Invertible.ne_zero (2 : k)
    have h3 := (smul_eq_zero.1 h1).resolve_left h2
    have h4 := (smul_eq_zero.1 h3).resolve_left (inv_ne_zero hs0)
    have h5 := ex4iii_g_inj e horth hne hQ (e 0) ((map_eq_zero_iff L L.injective).1 h4)
    exact hne 0 (by rw [h5]; simp)
  · intro μ hμ
    obtain ⟨a, ha, hι⟩ := ex4iii_ext e horth hne hQ L μ hμ
    have hμa : μ = ex4iii_mu e horth hne hQ L a ha :=
      CliffordAlgebra.hom_ext (LinearMap.ext fun x => by
        simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, ex4iii_mu_ι, hι])
    rcases mul_self_eq_mul_self_iff.1 (ha.trans hs) with h | h
    · left; subst h; exact hμa
    · right; subst h; exact hμa

/-- **Cassels, Ch. 10, Example 4 (iv)** (p. 193), first part: $M_2(k)$ is spanned by $\mu(1)$ and the $\mu(\vec v)$. -/
@[kb "cassels1978" "Ch. 10, Example 4 (iv), p. 193 (M₂(k) spanned by μ(1), μ(v))"]
theorem span_extension_eq_top (L : CliffordAlgebra.even Q ≃ₐ[k] Matrix (Fin 2) (Fin 2) k)
    (μ : CliffordAlgebra Q →ₐ[k] Matrix (Fin 2) (Fin 2) k) (hμ : ∀ u : CliffordAlgebra.even Q, μ u = L u) :
    Submodule.span k (insert (μ 1) (Set.range fun x => μ (ι Q x))) = ⊤ := by
  rw [eq_top_iff]
  intro B _
  have h2 : (2 : k) ≠ 0 := Invertible.ne_zero (2 : k)
  have hB : B - (B.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) k) ∈ Set.range (fun x => μ (ι Q x)) := by
    rw [ex4iii_range_eq e horth hne hQ L μ hμ]
    show (B - (B.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) k)).trace = 0
    simp [Matrix.trace_sub, Matrix.trace_smul]
  have hsum : B = (B.trace / 2) • μ 1 + (B - (B.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) k)) := by
    rw [map_one]; abel
  rw [hsum]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
    (Submodule.subset_span (Set.mem_insert_of_mem _ hB))

/-- **Cassels, Ch. 10, Example 4 (iv)** (p. 193), second part: the $\mu(\vec v)$, $\vec v \in V$, are precisely the
matrices of trace $0$. -/
@[kb "cassels1978" "Ch. 10, Example 4 (iv), p. 193 (μ(V) = matrices of trace 0)"]
theorem range_extension_eq_trace_zero (L : CliffordAlgebra.even Q ≃ₐ[k] Matrix (Fin 2) (Fin 2) k)
    (μ : CliffordAlgebra Q →ₐ[k] Matrix (Fin 2) (Fin 2) k) (hμ : ∀ u : CliffordAlgebra.even Q, μ u = L u) :
    Set.range (fun x => μ (ι Q x)) = {A : Matrix (Fin 2) (Fin 2) k | A.trace = 0} := by
  exact ex4iii_range_eq e horth hne hQ L μ hμ

end Extensions

end QuadFormsKB.Cassels
