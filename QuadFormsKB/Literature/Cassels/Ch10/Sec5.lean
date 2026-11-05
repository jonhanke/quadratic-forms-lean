/-
# Cassels, Chapter 10, §5: topological considerations — a continuous local section of $u \mapsto T_u$

**Setting.** $k$ a field of characteristic $\ne 2$; from `Topology` on: a complete nontrivially normed field
(Cassels: "in practice $k$ will be $\mathbb Q_p$ or $\mathbb R$"). $V$ a regular finite-dimensional quadratic space,
$C(V)$ its Clifford algebra, $M_0(V)$ = `M0 Q`, $T_u$ = `conjM0`. Cassels topologizes $C(V)$ as a finite-dimensional
$k$-vector space and $O(V)$ through matrices with respect to a basis; here $C(V)$ and $\operatorname{End}_k(V)$ carry
any Hausdorff topological-vector-space topology (on a finite-dimensional space over a complete field it is the unique
one, the topology of coordinates), and $O(V)$ the topology induced from $\operatorname{End}_k(V)$.

**The section.** Fix an orthogonal basis $\vec e_0, \dots, \vec e_{n-1}$ of anisotropic vectors. For
$\sigma \in \operatorname{End}_k(V)$ put
$$P^\sigma_j(z) = \tfrac12\bigl(z + \phi(\vec e_j)^{-1}\,\sigma(\vec e_j)\,\alpha(z)\,\vec e_j\bigr)$$
($\alpha$ the grade involution) and $\psi(\sigma) = P^\sigma_{n-1}\cdots P^\sigma_0(u_0)$. This is a polynomial in the
matrix entries of $\sigma$, hence continuous. If $\sigma = T_v$ with $v \in M_0(V)$ then $P^\sigma_j(vw) = v\,P_j(w)$, where
$P_j = P^{1}_j$ are the projections of `Ch10/Clifford.lean`, whose product maps $C(V)$ onto $k$. Hence
$\psi(T_v) = v\cdot c$ with $c \in k$, $\psi(T_{u_0}) = u_0$, and on the open set where $\psi(\sigma) \ne 0$ the value
$\psi(\sigma)$ lies in $M_0(V)$ and $T_{\psi(\sigma)} = \sigma$.

(Cassels' proof: "it is enough to show that $\vec a_1, \dots, \vec a_r$ in (3.4) can be chosen so that locally they depend
continuously on $\sigma$ … clear from an inspection of the proofs in Section 4 of Chapter 2". The explicit formula
above replaces that inspection.)

**Proves** (Cassels, *Rational Quadratic Forms*, Ch. 10, §5, pp. 184–185)
* Lemma 5.1: $u \mapsto T_u$ has a continuous local cross-section (`exists_continuous_local_section`);
* Corollary 1: the spinor norm is continuous: near every rotation it is the square class of a continuous nonvanishing
  function (`spinorNorm_locally_continuous`), so it is locally constant when the nonzero squares are open in $k^\times$,
  as in $\mathbb Q_p$ and $\mathbb R$ (`spinorNorm_locally_constant`);
* Corollary 2: if squaring has a continuous local cross-section near $1$, so has $\operatorname{Spin}(V) \to \Theta$
  (`exists_continuous_local_section_spin`).
-/
import QuadFormsKB.Literature.Cassels.Ch10.SpinGroup
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Module CliffordAlgebra Topology

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

open QuadFormsKB.OMeara

section Algebra

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {Q : QuadraticForm k V} {n : ℕ} (e : Basis (Fin n) k V)

/-- The twisted projection $P^\sigma_j(z) = \tfrac12(z + \phi(\vec e_j)^{-1}\sigma(\vec e_j)\alpha(z)\vec e_j)$. -/
noncomputable def projSigma (σ : Module.End k V) (j : Fin n) : CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q :=
  (⅟2 : k) • (LinearMap.id + (Q (e j))⁻¹ •
    ((LinearMap.mulLeft k (ι Q (σ (e j)))).comp ((LinearMap.mulRight k (ι Q (e j))).comp
      (involute : CliffordAlgebra Q →ₐ[k] CliffordAlgebra Q).toLinearMap)))

theorem projSigma_apply (σ : Module.End k V) (j : Fin n) (z : CliffordAlgebra Q) :
    projSigma e σ j z = (⅟2 : k) • (z + (Q (e j))⁻¹ • (ι Q (σ (e j)) * (involute z * ι Q (e j)))) := by
  simp [projSigma]

theorem projSigma_one (j : Fin n) : projSigma (Q := Q) e 1 j = projP (Q := Q) (e := e) j := by
  ext z
  rw [projSigma_apply, projP_apply]
  rfl

/-- $P^\sigma_{m-1}\cdots P^\sigma_0(z)$ (indices $\ge n$ are skipped). -/
noncomputable def iterSigma (σ : Module.End k V) : ℕ → CliffordAlgebra Q → CliffordAlgebra Q
  | 0, z => z
  | m + 1, z => if h : m < n then projSigma e σ ⟨m, h⟩ (iterSigma σ m z) else iterSigma σ m z

/-- **The intertwining identity**: if $v$ is an even unit with $\sigma(\vec x) = v\vec x v^{-1}$, then
$P^\sigma_j(vw) = v\,P_j(w)$. -/
theorem projSigma_mul {σ : Module.End k V} {v : (CliffordAlgebra Q)ˣ} (hv : (v : CliffordAlgebra Q) ∈ evenOdd Q 0)
    (hσ : ∀ x, ι Q (σ x) = v * ι Q x * ↑v⁻¹) (j : Fin n) (w : CliffordAlgebra Q) :
    projSigma e σ j ((v : CliffordAlgebra Q) * w) = (v : CliffordAlgebra Q) * projSigma e 1 j w := by
  rw [projSigma_apply, projSigma_apply, map_mul, involute_eq_of_mem_even hv, hσ]
  simp only [Module.End.one_apply]
  rw [mul_smul_comm, mul_add, mul_smul_comm]
  congr 3
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem iterSigma_mul {σ : Module.End k V} {v : (CliffordAlgebra Q)ˣ} (hv : (v : CliffordAlgebra Q) ∈ evenOdd Q 0)
    (hσ : ∀ x, ι Q (σ x) = v * ι Q x * ↑v⁻¹) (m : ℕ) (w : CliffordAlgebra Q) :
    iterSigma e σ m ((v : CliffordAlgebra Q) * w) = (v : CliffordAlgebra Q) * iterSigma e 1 m w := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [iterSigma]
    split_ifs with h
    · rw [ih, projSigma_mul e hv hσ]
    · exact ih

theorem iterSigma_algebraMap (hne : ∀ i, Q (e i) ≠ 0) (m : ℕ) (c : k) :
    iterSigma e 1 m (algebraMap k (CliffordAlgebra Q) c) = algebraMap k _ c := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [iterSigma]
    split_ifs with h
    · rw [ih, projSigma_apply, involute.commutes, Module.End.one_apply, Algebra.commutes c (ι Q _), ← mul_assoc,
        ι_sq_scalar, ← map_mul, Algebra.smul_def (Q (e ⟨m, h⟩))⁻¹, ← map_mul,
        show (Q (e ⟨m, h⟩))⁻¹ * (Q (e ⟨m, h⟩) * c) = c by field_simp [hne ⟨m, h⟩],
        ← two_smul k (algebraMap k _ c), smul_smul, invOf_mul_self, one_smul]
    · exact ih

variable {e}
variable (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (e i) (e j) = 0) (hne : ∀ i, Q (e i) ≠ 0)
include horth hne

/-- **The product of the projections lands in $k$**: $P_{n-1}\cdots P_0(w) \in k$ for every $w \in C(V)$. -/
theorem iterSigma_one_mem_range (w : CliffordAlgebra Q) :
    iterSigma e 1 n w ∈ Set.range (algebraMap k (CliffordAlgebra Q)) := by
  let S : ℕ → Submodule k (CliffordAlgebra Q) := fun m =>
    Submodule.span k {z | ∃ l : List (Fin n), (∀ j : Fin n, j.val < m → Even (l.count j)) ∧ bword Q e l = z}
  have step : ∀ m ≤ n, iterSigma e 1 m w ∈ S m := by
    intro m
    induction m with
    | zero =>
      intro _
      refine Submodule.span_mono ?_ (mem_span_bword Q e w)
      rintro _ ⟨l, rfl⟩; exact ⟨l, fun j hj => absurd hj (Nat.not_lt_zero _), rfl⟩
    | succ m ih =>
      intro hm
      have hm' : m < n := by omega
      have hw' := ih (by omega)
      simp only [iterSigma, hm', dite_true, projSigma_one]
      have : (S m).map (projP (Q := Q) (e := e) ⟨m, hm'⟩) ≤ S (m + 1) := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
        rw [projP_bword horth hne]
        split_ifs with h
        · refine Submodule.subset_span ⟨l, fun j hj => ?_, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
          · exact hl j hj
          · have : j = ⟨m, hm'⟩ := Fin.ext hj
            exact this ▸ h
        · exact Submodule.zero_mem _
      exact this (Submodule.mem_map_of_mem hw')
  have hfin := step n le_rfl
  have hle : S n ≤ LinearMap.range (Algebra.linearMap k (CliffordAlgebra Q)) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨c, hc⟩ := bword_mem_range_of_even horth l.length l rfl (fun j => hl j j.isLt)
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hle hfin
  exact ⟨c, hc⟩

/-- **The section, algebraically** (Cassels, Lemma 5.1): for $u_0 \in M_0(V)$ and $\psi(\sigma) = P^\sigma_{n-1}\cdots
P^\sigma_0(u_0)$: (i) $\psi(T_{u_0}) = u_0$; (ii) for every rotation $\sigma$ there are $v \in M_0(V)$ with $T_v = \sigma$
and $c \in k$ with $\psi(\sigma) = c\,v$. -/
theorem iterSigma_conjM0_self (u₀ : M0 Q) :
    iterSigma e (conjM0 u₀ : Module.End k V) n ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  have hσ : ∀ x, ι Q ((conjM0 u₀ : Module.End k V) x) = ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      ι Q x * ↑(u₀ : (CliffordAlgebra Q)ˣ)⁻¹ := fun x => conjHom_spec _ x
  have := iterSigma_mul e u₀.2.1 hσ n 1
  rw [mul_one] at this
  rw [this, ← map_one (algebraMap k (CliffordAlgebra Q)), iterSigma_algebraMap e hne, map_one, mul_one]

theorem iterSigma_eq_smul (hQ : (QuadraticMap.associated Q).Nondegenerate) (u₀ : M0 Q) {σ : V ≃ₗ[k] V}
    (hσ : σ ∈ orthPlus Q) :
    ∃ v : M0 Q, conjM0 v = σ ∧ ∃ c : k, iterSigma e (σ : Module.End k V) n
      ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = c • ((v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  obtain ⟨v, rfl⟩ : σ ∈ (conjM0 (Q := Q)).range := by rw [range_conjM0 hQ]; exact hσ
  refine ⟨v, rfl, ?_⟩
  have hσv : ∀ x, ι Q ((conjM0 v : Module.End k V) x) = ((v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      ι Q x * ↑(v : (CliffordAlgebra Q)ˣ)⁻¹ := fun x => conjHom_spec _ x
  have e1 : ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = ((v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      (↑(v : (CliffordAlgebra Q)ˣ)⁻¹ * ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [e1, iterSigma_mul e v.2.1 hσv]
  obtain ⟨c, hc⟩ := iterSigma_one_mem_range horth hne
    (↑(v : (CliffordAlgebra Q)ˣ)⁻¹ * ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
  exact ⟨c, by rw [← hc, ← Algebra.commutes, Algebra.smul_def]⟩

end Algebra

section Topology

variable {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [Invertible (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] {Q : QuadraticForm k V}
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul k V] [T2Space V]
  [TopologicalSpace (CliffordAlgebra Q)] [IsTopologicalAddGroup (CliffordAlgebra Q)]
  [ContinuousSMul k (CliffordAlgebra Q)] [T2Space (CliffordAlgebra Q)]
  [TopologicalSpace (Module.End k V)] [IsTopologicalAddGroup (Module.End k V)]
  [ContinuousSMul k (Module.End k V)] [T2Space (Module.End k V)]

theorem continuous_mul_clifford :
    Continuous (fun ab : CliffordAlgebra Q × CliffordAlgebra Q => ab.1 * ab.2) := by
  have := isModuleTopologyOfFiniteDimensional (𝕜 := k) (E := CliffordAlgebra Q)
  exact IsModuleTopology.continuous_mul_of_finite k (CliffordAlgebra Q)

/-- The section $\sigma \mapsto P^\sigma_{m-1}\cdots P^\sigma_0(z)$ is continuous in $\sigma$. -/
theorem continuous_iterSigma {n : ℕ} (e : Basis (Fin n) k V) (m : ℕ) (z : CliffordAlgebra Q) :
    Continuous fun σ : Module.End k V => iterSigma e σ m z := by
  induction m with
  | zero => exact continuous_const
  | succ m ih =>
    simp only [iterSigma]
    split_ifs with h
    · simp only [projSigma_apply]
      have hev : Continuous fun σ : Module.End k V => σ (e ⟨m, h⟩) :=
        (LinearMap.applyₗ (R := k) (e ⟨m, h⟩) : Module.End k V →ₗ[k] V).continuous_of_finiteDimensional
      have hι : Continuous (ι Q) := (ι Q).continuous_of_finiteDimensional
      have hinv : Continuous (involute : CliffordAlgebra Q →ₐ[k] CliffordAlgebra Q) :=
        (involute : CliffordAlgebra Q →ₐ[k] CliffordAlgebra Q).toLinearMap.continuous_of_finiteDimensional
      have hmul := continuous_mul_clifford (k := k) (Q := Q)
      have h1 : Continuous fun σ : Module.End k V => involute (iterSigma e σ m z) * ι Q (e ⟨m, h⟩) :=
        hmul.comp ((hinv.comp ih).prodMk continuous_const)
      have h2 : Continuous fun σ : Module.End k V =>
          ι Q (σ (e ⟨m, h⟩)) * (involute (iterSigma e σ m z) * ι Q (e ⟨m, h⟩)) :=
        hmul.comp ((hι.comp hev).prodMk h1)
      exact (ih.add (h2.const_smul ((Q (e ⟨m, h⟩))⁻¹ : k))).const_smul (⅟2 : k)
    · exact ih

/-- **Cassels, Ch. 10, Lemma 5.1** (p. 184). Let $k$ be a complete nontrivially normed field of characteristic
$\ne 2$ (e.g. $\mathbb Q_p$, $\mathbb R$) and $V$ a regular quadratic space. The map $u \mapsto T_u$ of $M_0(V)$ onto
$O^+(V)$ has locally a continuous cross-section: for $u_0 \in M_0(V)$ there are a continuous map
$\psi : \operatorname{End}_k(V) \to C(V)$ with $\psi(T_{u_0}) = u_0$ and an open neighbourhood $U$ of $T_{u_0}$ such that
for every rotation $\sigma \in U$, $\psi(\sigma) \in M_0(V)$ and $T_{\psi(\sigma)} = \sigma$. -/
@[kb "cassels1978" "Ch. 10, Lemma 5.1, p. 184"]
theorem exists_continuous_local_section (hQ : (QuadraticMap.associated Q).Nondegenerate) (u₀ : M0 Q) :
    ∃ ψ : Module.End k V → CliffordAlgebra Q, Continuous ψ ∧
      ψ (conjM0 u₀ : Module.End k V) = ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∧
      ∃ U : Set (Module.End k V), IsOpen U ∧ (conjM0 u₀ : Module.End k V) ∈ U ∧
        ∀ σ ∈ orthPlus Q, (σ : Module.End k V) ∈ U →
          ∃ v : M0 Q, ((v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = ψ σ ∧ conjM0 v = σ := by
  obtain ⟨e, horth, hne⟩ := exists_orthogonal_basis_aniso hQ
  set ψ : Module.End k V → CliffordAlgebra Q := fun σ =>
    iterSigma e σ (finrank k V) ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hψ : Continuous ψ := continuous_iterSigma e _ _
  refine ⟨ψ, hψ, iterSigma_conjM0_self horth hne u₀, {σ | ψ σ ≠ 0},
    isOpen_ne_fun hψ continuous_const, ?_, ?_⟩
  · change ψ _ ≠ 0
    rw [show ψ (conjM0 u₀ : Module.End k V) = _ from iterSigma_conjM0_self horth hne u₀]
    exact Units.ne_zero _
  · intro σ hσ hU
    obtain ⟨v, hv, c, hc⟩ := iterSigma_eq_smul horth hne hQ u₀ hσ
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hU (by rw [show ψ σ = _ from hc, zero_smul])
    refine ⟨⟨_, (M0 Q).mul_mem (scalar_mem_M0 (Units.mk0 c hc0)) v.2⟩, ?_, ?_⟩
    · change algebraMap k _ c * _ = ψ σ
      rw [show ψ σ = _ from hc, Algebra.smul_def]
    · change conjM0 (⟨_, scalar_mem_M0 (Units.mk0 c hc0)⟩ * v) = σ
      rw [map_mul, (conjM0_eq_one_iff hQ ⟨_, scalar_mem_M0 _⟩).2 ⟨_, rfl⟩, one_mul, hv]

/-- A linear functional on $C(V)$ that reads off scalars: $\lambda(c) = c$ for $c \in k$. -/
theorem exists_scalar_functional :
    ∃ φ : CliffordAlgebra Q →ₗ[k] k, ∀ c : k, φ (algebraMap k _ c) = c := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (CliffordAlgebra Q), φ 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff k (1 : CliffordAlgebra Q)).1 h)
  refine ⟨(φ 1)⁻¹ • φ, fun c => ?_⟩
  rw [LinearMap.smul_apply, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, smul_eq_mul]
  field_simp

/-- **Cassels, Ch. 10, Lemma 5.1, Corollary 1** (p. 185): the spinor norm $\theta : O^+(V) \to k^\times/(k^\times)^2$ is
continuous: near every rotation $\sigma_0$ it is the square class of a continuous function $c$ with nonzero values,
$\theta(\sigma) = c(\sigma)(k^\times)^2$ (so $\theta$ is the quotient map composed with a continuous map; Cassels gives
$k^\times/(k^\times)^2$ the quotient topology). Proof as in the book: $c(\sigma) = \psi(\sigma)\psi(\sigma)'$ for the local
section $\psi$ of Lemma 5.1. -/
@[kb "cassels1978" "Ch. 10, Lemma 5.1, Cor. 1, p. 185"]
theorem spinorNorm_locally_continuous (hQ : (QuadraticMap.associated Q).Nondegenerate) {σ₀ : V ≃ₗ[k] V}
    (hσ₀ : σ₀ ∈ orthPlus Q) :
    ∃ c : Module.End k V → k, Continuous c ∧ ∃ U : Set (Module.End k V), IsOpen U ∧ (σ₀ : Module.End k V) ∈ U ∧
      ∀ σ (hσ : σ ∈ orthPlus Q), (σ : Module.End k V) ∈ U →
        c σ ≠ 0 ∧ spinorNormHom Q hQ ⟨σ, hσ⟩ = Lattices.sqClassOf (c σ) := by
  obtain ⟨u₀, rfl⟩ : σ₀ ∈ (conjM0 (Q := Q)).range := by rw [range_conjM0 hQ]; exact hσ₀
  obtain ⟨ψ, hψ, -, U, hUo, hU0, hsec⟩ := exists_continuous_local_section hQ u₀
  obtain ⟨φ, hφ⟩ := exists_scalar_functional (k := k) (Q := Q)
  have hrev : Continuous (reverse : CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q) :=
    LinearMap.continuous_of_finiteDimensional _
  refine ⟨fun σ => φ (ψ σ * reverse (ψ σ)), ?_, U, hUo, hU0, fun σ hσ hσU => ?_⟩
  · exact φ.continuous_of_finiteDimensional.comp
      (continuous_mul_clifford.comp (hψ.prodMk (hrev.comp hψ)))
  · obtain ⟨v, hv, rfl⟩ := hsec σ hσ hσU
    obtain ⟨d, hd0, hd⟩ := M0_mul_reverse hQ v
    simp only [← hv, hd, hφ]
    exact ⟨hd0, spinorNormHom_conjM0 hQ v hd⟩

/-- **The spinor norm is locally constant** when the nonzero squares form a neighbourhood of $1$ in every coset
(as in $\mathbb Q_p$ and $\mathbb R$; Cassels' note after Corollary 1 to Lemma 5.1, p. 185): every rotation $\sigma_0$ has
a neighbourhood on which $\theta$ is constant. -/
@[kb "cassels1978" "Ch. 10, Lemma 5.1, Cor. 1, p. 185 (θ locally constant when squares are open)"]
theorem spinorNorm_locally_constant (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hsq : ∀ d : k, d ≠ 0 → {x : k | ∃ s : k, s ≠ 0 ∧ x = d * s ^ 2} ∈ 𝓝 d) {σ₀ : V ≃ₗ[k] V}
    (hσ₀ : σ₀ ∈ orthPlus Q) :
    ∃ U : Set (Module.End k V), IsOpen U ∧ (σ₀ : Module.End k V) ∈ U ∧
      ∀ σ (hσ : σ ∈ orthPlus Q), (σ : Module.End k V) ∈ U →
        spinorNormHom Q hQ ⟨σ, hσ⟩ = spinorNormHom Q hQ ⟨σ₀, hσ₀⟩ := by
  obtain ⟨c, hc, U, hUo, hU0, hcU⟩ := spinorNorm_locally_continuous hQ hσ₀
  obtain ⟨hc0, hθ0⟩ := hcU σ₀ hσ₀ hU0
  obtain ⟨W, hWsub, hWo, hW0⟩ := mem_nhds_iff.1 (hsq _ hc0)
  refine ⟨U ∩ c ⁻¹' W, hUo.inter (hWo.preimage hc), ⟨hU0, hW0⟩, fun σ hσ hσU => ?_⟩
  obtain ⟨-, hθ⟩ := hcU σ hσ hσU.1
  obtain ⟨s, hs, hcs⟩ := hWsub hσU.2
  rw [hθ, hθ0, hcs, Sp55.sqClassOf_mul' hc0 (pow_ne_zero 2 hs),
    (Sp55.sqClassOf_eq_one_iff' (pow_ne_zero 2 hs)).2 ⟨s, sq s⟩, mul_one]

/-- **Cassels, Ch. 10, Lemma 5.1, Corollary 2** (p. 185). Suppose squaring $b \mapsto b^2$ has a continuous local
cross-section near $1$: a continuous $r$ on a neighbourhood $W$ of $1$ with $r(1) = 1$ and $r(d)^2 = d$ for the squares
$d \in W$. Then $u \mapsto T_u$ of $\operatorname{Spin}(V)$ onto $\Theta$ (Theorem 3.3) has locally a continuous
cross-section: for $w_0 \in \operatorname{Spin}(V)$ there are a map $\chi : \operatorname{End}_k(V) \to C(V)$ and an
open neighbourhood $U$ of $T_{w_0}$ such that $\chi$ is continuous on $U$, $\chi(T_{w_0}) = w_0$, and for every
$\sigma \in \Theta \cap U$, $\chi(\sigma) \in \operatorname{Spin}(V)$ and $T_{\chi(\sigma)} = \sigma$. ($V \ne 0$, as for
Theorem 3.3.) -/
@[kb "cassels1978" "Ch. 10, Lemma 5.1, Cor. 2, p. 185"]
theorem exists_continuous_local_section_spin [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {W : Set k} (hW : W ∈ 𝓝 (1 : k)) {r : k → k} (hr : ContinuousOn r W) (hr1 : r 1 = 1)
    (hrsq : ∀ d ∈ W, IsSquare d → r d ^ 2 = d) (w₀ : spinGroup Q) :
    ∃ χ : Module.End k V → CliffordAlgebra Q, ∃ U : Set (Module.End k V), IsOpen U ∧
      (spinConj w₀ : Module.End k V) ∈ U ∧ ContinuousOn χ U ∧
      χ (spinConj w₀ : Module.End k V) = (w₀ : CliffordAlgebra Q) ∧
      ∀ σ ∈ orthPrime Q, (σ : Module.End k V) ∈ U →
        ∃ w : spinGroup Q, (w : CliffordAlgebra Q) = χ σ ∧ spinConj w = σ := by
  set u₀ : M0 Q := ⟨_, spinGroup_mem_M0 w₀⟩
  obtain ⟨ψ, hψ, hψ0, U, hUo, hU0, hsec⟩ := exists_continuous_local_section (k := k) hQ u₀
  obtain ⟨φ, hφ⟩ := exists_scalar_functional (k := k) (Q := Q)
  have hrev : Continuous (reverse : CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q) :=
    LinearMap.continuous_of_finiteDimensional _
  set c : Module.End k V → k := fun σ => φ (ψ σ * reverse (ψ σ))
  have hc : Continuous c := φ.continuous_of_finiteDimensional.comp
    (continuous_mul_clifford.comp (hψ.prodMk (hrev.comp hψ)))
  have hc0 : c (spinConj w₀ : Module.End k V) = 1 := by
    simp only [c]
    rw [show (spinConj w₀ : Module.End k V) = (conjM0 u₀ : Module.End k V) from rfl, hψ0]
    rw [show ((u₀ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = (w₀ : CliffordAlgebra Q) from rfl,
      spinGroup_mul_reverse, ← map_one (algebraMap k (CliffordAlgebra Q)), hφ]
  -- the neighbourhood: inside `U`, with `c σ` in an open set around `1` where `r` is continuous and nonzero
  obtain ⟨W', hW'sub, hW'o, hW'1⟩ := mem_nhds_iff.1 hW
  have hrc : ContinuousOn r W' := hr.mono hW'sub
  have hr0 : {d | d ∈ W' ∧ r d ≠ 0} ∈ 𝓝 (1 : k) := by
    have : ∀ᶠ d in 𝓝 (1 : k), r d ≠ 0 := by
      have hcont : ContinuousAt r 1 := hrc.continuousAt (hW'o.mem_nhds hW'1)
      exact hcont.eventually_ne (by rw [hr1]; exact one_ne_zero)
    exact Filter.inter_mem (hW'o.mem_nhds hW'1) this
  obtain ⟨W'', hW''sub, hW''o, hW''1⟩ := mem_nhds_iff.1 hr0
  refine ⟨fun σ => (r (c σ))⁻¹ • ψ σ, U ∩ c ⁻¹' W'', hUo.inter (hW''o.preimage hc), ⟨hU0, by
    change c _ ∈ W''; rw [hc0]; exact hW''1⟩, ?_, ?_, ?_⟩
  · intro σ hσ
    have h1 : ContinuousWithinAt (fun σ => r (c σ)) (U ∩ c ⁻¹' W'') σ :=
      (hrc.continuousAt (hW'o.mem_nhds (hW''sub hσ.2).1)).comp_continuousWithinAt
        hc.continuousWithinAt
    exact (h1.inv₀ (hW''sub hσ.2).2).smul hψ.continuousWithinAt
  · simp only
    rw [hc0, hr1, inv_one, one_smul]
    exact hψ0
  · intro σ hσ hσU
    obtain ⟨v, hv, rfl⟩ := hsec σ hσ.1 hσU.1
    obtain ⟨d, hd0, hd⟩ := M0_mul_reverse hQ v
    have hcd : c (conjM0 v : Module.End k V) = d := by simp only [c, ← hv, hd, hφ]
    have hdW : d ∈ W' := by rw [← hcd]; exact (hW''sub hσU.2).1
    have hrd0 : r d ≠ 0 := by rw [← hcd]; exact (hW''sub hσU.2).2
    -- `d` is a square since `T_v ∈ Θ`
    have hdsq : IsSquare d := by
      have h1 := spinorNormHom_conjM0 hQ v hd
      have h2 : spinorNormHom Q hQ ⟨conjM0 v, conjM0_mem_orthPlus hQ v⟩ = 1 := by
        rw [← MonoidHom.mem_ker, ker_spinorNormHom]; exact hσ
      rw [h2] at h1
      exact (Sp55.sqClassOf_eq_one_iff' hd0).1 h1.symm
    have hr2 : r d ^ 2 = d := hrsq d (hW'sub hdW) hdsq
    set t : kˣ := Units.mk0 (r d)⁻¹ (inv_ne_zero hrd0)
    set U' : M0 Q := ⟨_, (M0 Q).mul_mem (scalar_mem_M0 t) v.2⟩
    have hU'val : ((U' : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        (r d)⁻¹ • ((v : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
      change algebraMap k _ (r d)⁻¹ * _ = _
      rw [Algebra.smul_def]
    have hT : conjM0 U' = conjM0 v := by
      change conjM0 (⟨_, scalar_mem_M0 t⟩ * v) = _
      rw [map_mul, (conjM0_eq_one_iff hQ ⟨_, scalar_mem_M0 _⟩).2 ⟨_, rfl⟩, one_mul]
    have hw : ((U' : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ spinGroup Q := by
      rw [mem_spinGroup_iff hQ]
      have hnorm : ((U' : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
          reverse ((U' : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = 1 := by
        rw [hU'val, map_smul, smul_mul_smul_comm, hd, Algebra.smul_def, ← map_mul,
          show (r d)⁻¹ * (r d)⁻¹ * d = 1 by
            rw [← mul_inv, ← sq, inv_mul_eq_div, div_eq_one_iff_eq (pow_ne_zero 2 hrd0)]; exact hr2.symm,
          map_one]
      refine ⟨U'.2.1, hnorm, fun x => ?_⟩
      obtain ⟨y, hy⟩ := U'.2.2 x
      have hinv : (↑((U' : (CliffordAlgebra Q)ˣ)⁻¹) : CliffordAlgebra Q) =
          reverse ((U' : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
        eq_of_mul_eq_one_of_mul_eq_one (U' : (CliffordAlgebra Q)ˣ).mul_inv
          (mul_eq_one_comm_of_finiteDimensional k hnorm)
      exact ⟨y, by rw [hy, hinv]⟩
    refine ⟨⟨_, hw⟩, by simp only [hU'val, hcd, hv], ?_⟩
    rw [spinConj_eq, ← hT]
    exact congrArg conjM0 (Subtype.ext (Units.ext rfl))

end Topology

end QuadFormsKB.Cassels
