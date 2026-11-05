/-
# Cassels, Chapter 10, §§2–3, 5: the grade automorphism, dimensions of $C_0, C_1$, commutators, topology

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 10, pp. 174, 178, 184.

**Setting.** $k$ a field of characteristic $\ne 2$ (`[Invertible (2 : k)]`), $V$ a finite-dimensional $k$-vector
space with quadratic form $Q$ (Cassels' $\phi$), $C(V)$ = `CliffordAlgebra Q`, $C_0(V), C_1(V)$ = `evenOdd Q 0`,
`evenOdd Q 1`, $u \mapsto u'$ = `reverse`, $M_0(V)$ = `M0 Q`, $T_u$ = `conjM0 u`. "Regular" means
`(QuadraticMap.associated Q).Nondegenerate`. Indices are 0-based (`Fin n`).

**Proves.**
* (p. 174) The autometry $\vec x \mapsto -\vec x$ induces the grade automorphism of order $2$
  (`CliffordAlgebra.involute`); $C_0(V)$ and $C_1(V)$ are the elements fixed, respectively negated, by it
  (`mem_evenOdd_zero_iff_involute_eq`, `mem_evenOdd_one_iff_involute_eq_neg`, `involute_automorphism_order_two`).
* (p. 174) $\dim C_0(V) = \dim C_1(V) = 2^{n-1}$ for regular $V$ with $n \ge 1$ (`finrank_evenOdd`). Cassels reads
  this off the basis $e(J)$ ($|J|$ even, resp. odd); here it is proved by left multiplication by an anisotropic
  vector, which swaps $C_0$ and $C_1$, together with $C(V) = C_0(V) \oplus C_1(V)$ and $\dim C(V) = 2^n$.
* (p. 178) Facts on the commutator subgroup $G'$ of a group (`commutator_subgroup_facts`), all from Mathlib.
* (p. 184) Topology on $C(V)$: addition, multiplication and the involution are continuous, $u \mapsto u^{-1}$
  is continuous on $M_0(V)$ (`inv_continuousOn_M0`), $M_0(V)$ with the topology induced from $C(V)$ is a topological
  group (`isTopologicalGroup_M0`), and $u \mapsto T_u$ is continuous into $\operatorname{End}_k(V)$
  (`continuous_conjM0`). The topologies are as in `Ch10/Sec5.lean`: any Hausdorff vector space topology
  (unique on a finite-dimensional space over a complete field).
-/
import QuadFormsKB.Literature.Cassels.Ch10.Sec5

open Module CliffordAlgebra Topology
open scoped commutatorElement

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

section Grading

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {Q : QuadraticForm k V}

/-- **$C_0(V)$ is the fixed space of the grade automorphism** (Cassels, Ch. 10, §2, p. 174): for
$u \in C(V)$ and $\alpha$ = `involute` (induced by $\vec x \mapsto -\vec x$), $u \in C_0(V)$ if and only if
$\alpha(u) = u$. Characteristic $\ne 2$ is used for "if". -/
@[kb "cassels1978" "Ch. 10, §2, p. 174 (C₀(V), C₁(V) are the elements fixed, resp. negated, by the automorphism induced by x ↦ −x)"]
theorem mem_evenOdd_zero_iff_involute_eq (u : CliffordAlgebra Q) :
    u ∈ evenOdd Q 0 ↔ involute u = u :=
  ⟨involute_eq_of_mem_even, mem_even_of_involute_eq Q⟩

/-- **$C_1(V)$ is the negated space of the grade automorphism** (Cassels, Ch. 10, §2, p. 174): for
$u \in C(V)$, $u \in C_1(V)$ if and only if $\alpha(u) = -u$. -/
@[kb "cassels1978" "Ch. 10, §2, p. 174 (C₀(V), C₁(V) are the elements fixed, resp. negated, by the automorphism induced by x ↦ −x)"]
theorem mem_evenOdd_one_iff_involute_eq_neg (u : CliffordAlgebra Q) :
    u ∈ evenOdd Q 1 ↔ involute u = -u :=
  ⟨involute_eq_of_mem_odd, mem_odd_of_involute_eq_neg Q⟩

/-- **The grade automorphism has order 2** (Cassels, Ch. 10, §2, p. 174): there is a $k$-algebra automorphism
$\alpha$ of $C(V)$ equal to `involute`, with $\alpha(\iota\vec x) = \iota(-\vec x)$ (it is induced by
$\vec x \mapsto -\vec x$), $\alpha \circ \alpha = \mathrm{id}$, and, if $V \ne 0$, $\alpha \ne \mathrm{id}$ (so its
order is exactly $2$). -/
@[kb "cassels1978" "Ch. 10, §2, p. 174 (C₀(V), C₁(V) are the elements fixed, resp. negated, by the automorphism induced by x ↦ −x)"]
theorem involute_automorphism_order_two :
    ∃ α : CliffordAlgebra Q ≃ₐ[k] CliffordAlgebra Q,
      (∀ u, α u = involute u) ∧ (∀ x : V, α (ι Q x) = ι Q (-x)) ∧
      α.trans α = AlgEquiv.refl ∧ (Nontrivial V → α ≠ AlgEquiv.refl) := by
  let α : CliffordAlgebra Q ≃ₐ[k] CliffordAlgebra Q :=
    AlgEquiv.ofAlgHom involute involute (AlgHom.ext involute_involute) (AlgHom.ext involute_involute)
  refine ⟨α, fun u => rfl, fun x => by simp [α], ?_, fun hV h => ?_⟩
  · ext u; exact involute_involute u
  · obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have h1 : involute (ι Q x) = ι Q x := congrArg (fun f : CliffordAlgebra Q ≃ₐ[k] CliffordAlgebra Q => f (ι Q x)) h
    rw [involute_ι] at h1
    have := eq_zero_of_eq_neg Q h1.symm
    exact hx (cliffordι_injective Q (by rw [this, map_zero]))

/-- **Helper:** left multiplication by a vector sends $C_0(V)$ into $C_1(V)$ and $C_1(V)$ into $C_0(V)$. -/
theorem ι_mul_mem_evenOdd (v : V) {i : ZMod 2} {x : CliffordAlgebra Q} (hx : x ∈ evenOdd Q i) :
    ι Q v * x ∈ evenOdd Q (i + 1) := by
  have := SetLike.mul_mem_graded (ι_mem_evenOdd_one Q v) hx
  rwa [add_comm] at this

/-- **Helper:** left multiplication by an anisotropic vector is injective on $C(V)$. -/
theorem ι_mul_injective {v : V} (hv : Q v ≠ 0) : Function.Injective (fun x : CliffordAlgebra Q => ι Q v * x) := by
  intro x y h
  have h2 := congrArg (fun z => ι Q v * z) h
  simp only [← mul_assoc, ι_sq_scalar, ← Algebra.smul_def] at h2
  exact smul_right_injective _ hv h2

/-- **Dimensions of $C_0(V)$ and $C_1(V)$** (Cassels, Ch. 10, §2, p. 174): for a regular quadratic space $V$ of
dimension $n \ge 1$ over a field of characteristic $\ne 2$,
$\dim C_0(V) = \dim C_1(V) = 2^{n-1}$. (Regularity is used only to find an anisotropic vector; for $n = 0$ one has
$C_0 = k$, $C_1 = 0$.) -/
@[kb "cassels1978" "Ch. 10, §2, p. 174 (dim C₀(V) = dim C₁(V) = 2^{n−1})"]
theorem finrank_evenOdd (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 0 < finrank k V) :
    finrank k (evenOdd Q 0) = 2 ^ (finrank k V - 1) ∧ finrank k (evenOdd Q 1) = 2 ^ (finrank k V - 1) := by
  obtain ⟨e, -, hne⟩ := exists_orthogonal_basis_aniso hQ
  have hv : Q (e ⟨0, hn⟩) ≠ 0 := hne _
  let f : evenOdd Q 0 →ₗ[k] evenOdd Q 1 :=
    (LinearMap.mulLeft k (ι Q (e ⟨0, hn⟩))).restrict (fun x hx => by
      simpa using ι_mul_mem_evenOdd (Q := Q) (e ⟨0, hn⟩) (i := 0) hx)
  let g : evenOdd Q 1 →ₗ[k] evenOdd Q 0 :=
    (LinearMap.mulLeft k (ι Q (e ⟨0, hn⟩))).restrict (fun x hx => by
      have := ι_mul_mem_evenOdd (Q := Q) (e ⟨0, hn⟩) (i := 1) hx
      rwa [show (1 + 1 : ZMod 2) = 0 from rfl] at this)
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (ι_mul_injective hv (congrArg Subtype.val h))
  have hg : Function.Injective g := fun x y h =>
    Subtype.ext (ι_mul_injective hv (congrArg Subtype.val h))
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  have h2 := LinearMap.finrank_le_finrank_of_injective hg
  have hsum := Submodule.finrank_add_eq_of_isCompl (evenOdd_isCompl Q)
  rw [finrank_cliffordAlgebra] at hsum
  obtain ⟨m, hm⟩ : ∃ m, finrank k V = m + 1 := ⟨finrank k V - 1, by omega⟩
  rw [hm, pow_succ] at hsum
  rw [hm, Nat.add_sub_cancel]
  omega

end Grading

section Commutator

/-- **The commutator subgroup** (Cassels, Ch. 10, §3, p. 178, running text before Lemma 3.2): for a group $G$
with commutator subgroup $G' = [G, G]$ (Mathlib `commutator G`): (i) $G'$ is generated by the commutators
$aba^{-1}b^{-1}$ ($a, b \in G$); (ii) $G'$ is normal; (iii) $G/G'$ is abelian; (iv) if $H$ is a normal subgroup of
$G$ with $G/H$ abelian then $G' \le H$. All are Mathlib results (`commutator_eq_closure`,
`Subgroup.commutator_normal`, `Subgroup.Normal.quotient_commutative_iff_commutator_le`). -/
@[kb "cassels1978" "Ch. 10, §3, p. 178 (the commutator subgroup)"]
theorem commutator_subgroup_facts (G : Type*) [Group G] :
    commutator G = Subgroup.closure {g : G | ∃ a b : G, g = a * b * a⁻¹ * b⁻¹} ∧
    (commutator G).Normal ∧
    (∀ x y : G ⧸ commutator G, x * y = y * x) ∧
    (∀ (H : Subgroup G) [H.Normal], (∀ x y : G ⧸ H, x * y = y * x) → commutator G ≤ H) := by
  refine ⟨?_, inferInstance, fun x y => (IsMulCommutative.is_comm (M := G ⧸ commutator G)).comm x y,
    fun H _ hab => ?_⟩
  · rw [commutator_eq_closure]
    congr 1
    ext g
    simp only [commutatorSet_def, Set.mem_ofPred_eq, commutatorElement_def]
    exact ⟨fun ⟨a, b, h⟩ => ⟨a, b, h.symm⟩, fun ⟨a, b, h⟩ => ⟨a, b, h.symm⟩⟩
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.1 ⟨⟨hab⟩⟩

end Commutator

section Topology

variable {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [Invertible (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] {Q : QuadraticForm k V}
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul k V] [T2Space V]
  [TopologicalSpace (CliffordAlgebra Q)] [IsTopologicalAddGroup (CliffordAlgebra Q)]
  [ContinuousSMul k (CliffordAlgebra Q)] [T2Space (CliffordAlgebra Q)]
  [TopologicalSpace (Module.End k V)] [IsTopologicalAddGroup (Module.End k V)]
  [ContinuousSMul k (Module.End k V)] [T2Space (Module.End k V)]

/-- **The vector space topology on $C(V)$** (Cassels, Ch. 10, §5, p. 184): with $C(V)$ carrying any Hausdorff vector
space topology over the complete field $k$ (it is unique, the topology of coordinates), addition, scalar
multiplication, multiplication $(u, v) \mapsto uv$ and the canonical involution $u \mapsto u'$ are continuous, and so
is every $k$-linear map out of $C(V)$ (finite-dimensionality). -/
@[kb "cassels1978" "Ch. 10, §5, p. 184 (topology on C(V); M₀(V) is a topological group)"]
theorem clifford_operations_continuous :
    Continuous (fun p : CliffordAlgebra Q × CliffordAlgebra Q => p.1 + p.2) ∧
    Continuous (fun p : k × CliffordAlgebra Q => p.1 • p.2) ∧
    Continuous (fun p : CliffordAlgebra Q × CliffordAlgebra Q => p.1 * p.2) ∧
    Continuous (reverse : CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q) :=
  ⟨continuous_add, continuous_smul, continuous_mul_clifford, LinearMap.continuous_of_finiteDimensional _⟩

/-- **The inverse on $M_0(V)$ is continuous** (Cassels, Ch. 10, §5, p. 184): for regular $V$ there is a continuous
function $N : C(V) \to k$ ($N(u) = $ the scalar part of $uu'$) such that for every $u \in M_0(V)$, $uu' = N(u) \ne 0$
and $u^{-1} = N(u)^{-1}u'$; consequently $u \mapsto N(u)^{-1}u'$ is continuous on the set $M_0(V) \subseteq C(V)$ and
agrees there with the inverse $u \mapsto u^{-1}$. -/
@[kb "cassels1978" "Ch. 10, §5, p. 184 (topology on C(V); M₀(V) is a topological group)"]
theorem inv_continuousOn_M0 (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    ∃ N : CliffordAlgebra Q → k, Continuous N ∧
      (∀ g : M0 Q, N ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ≠ 0 ∧
        ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * reverse ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
          algebraMap k _ (N ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) ∧
        (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
          (N ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))⁻¹ • reverse ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) ∧
      ContinuousOn (fun u : CliffordAlgebra Q => (N u)⁻¹ • reverse u)
        (Set.range fun g : M0 Q => ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
  obtain ⟨φ, hφ⟩ := exists_scalar_functional (k := k) (Q := Q)
  have hrev : Continuous (reverse : CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q) :=
    LinearMap.continuous_of_finiteDimensional _
  have hN : Continuous fun u : CliffordAlgebra Q => φ (u * reverse u) :=
    φ.continuous_of_finiteDimensional.comp (continuous_mul_clifford.comp (continuous_id.prodMk hrev))
  have key : ∀ g : M0 Q, φ (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      reverse ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) ≠ 0 ∧
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * reverse ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        algebraMap k _ (φ (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
          reverse ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))) := by
    intro g
    obtain ⟨c, hc0, hc⟩ := M0_mul_reverse hQ g
    rw [hc, hφ]
    exact ⟨hc0, rfl⟩
  refine ⟨fun u => φ (u * reverse u), hN, fun g => ⟨(key g).1, (key g).2, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := key g
    have := inverse_of_mul_reverse Q h1 h2
    exact (eq_of_mul_eq_one_of_mul_eq_one (g : (CliffordAlgebra Q)ˣ).mul_inv this.2.2).symm ▸ rfl
  · rintro _ ⟨g, rfl⟩
    exact ((hN.continuousAt.inv₀ (key g).1).smul hrev.continuousAt).continuousWithinAt

/-- Helper: the topology on $M_0(V)$ induced from $C(V)$ (Cassels takes the subspace topology). -/
@[instance_reducible] def M0.inducedTopology (Q : QuadraticForm k V) [TopologicalSpace (CliffordAlgebra Q)] :
    TopologicalSpace (M0 Q) :=
  TopologicalSpace.induced (fun g : M0 Q => ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) inferInstance

/-- **$M_0(V)$ is a topological group** (Cassels, Ch. 10, §5, p. 184): for regular $V$, with the subspace topology
induced from $C(V)$, multiplication and inversion on $M_0(V)$ are continuous. -/
@[kb "cassels1978" "Ch. 10, §5, p. 184 (topology on C(V); M₀(V) is a topological group)"]
theorem isTopologicalGroup_M0 (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    @IsTopologicalGroup (M0 Q) (M0.inducedTopology Q) _ := by
  let _ : TopologicalSpace (M0 Q) := M0.inducedTopology Q
  have hcoe : Continuous fun g : M0 Q => ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := continuous_induced_dom
  obtain ⟨N, hN, hg, -⟩ := inv_continuousOn_M0 (k := k) (Q := Q) hQ
  have hrev : Continuous (reverse : CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q) :=
    LinearMap.continuous_of_finiteDimensional _
  refine @IsTopologicalGroup.mk _ _ _ ⟨?_⟩ ⟨?_⟩
  · refine continuous_induced_rng.2 ?_
    exact continuous_mul_clifford.comp ((hcoe.comp continuous_fst).prodMk (hcoe.comp continuous_snd))
  · refine continuous_induced_rng.2 ?_
    change Continuous fun g : M0 Q => (((g⁻¹ : M0 Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
    have : (fun g : M0 Q => (((g⁻¹ : M0 Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
        fun g : M0 Q => (N ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))⁻¹ •
          reverse ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := funext fun g => (hg g).2.2
    rw [this]
    exact ((hN.comp hcoe).inv₀ fun g => (hg g).1).smul (hrev.comp hcoe)

/-- **$u \mapsto T_u$ is continuous** (Cassels, Ch. 10, §5, p. 184): for regular $V$, the map $M_0(V) \to
\operatorname{End}_k(V)$, $u \mapsto T_u$ (with $M_0(V)$ carrying the topology induced from $C(V)$) is continuous. -/
@[kb "cassels1978" "Ch. 10, §5, p. 184 (topology on C(V); M₀(V) is a topological group)"]
theorem continuous_conjM0 (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    @Continuous (M0 Q) (Module.End k V) (M0.inducedTopology Q) _
      (fun u : M0 Q => (conjM0 u : Module.End k V)) := by
  let _ : TopologicalSpace (M0 Q) := M0.inducedTopology Q
  have hcoe : Continuous fun g : M0 Q => ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := continuous_induced_dom
  obtain ⟨N, hN, hg, hcont⟩ := inv_continuousOn_M0 (k := k) (Q := Q) hQ
  have hrev : Continuous (reverse : CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q) :=
    LinearMap.continuous_of_finiteDimensional _
  have hinv : Continuous fun g : M0 Q => (((g⁻¹ : M0 Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
    have : (fun g : M0 Q => (((g⁻¹ : M0 Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
        fun g : M0 Q => (N ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))⁻¹ •
          reverse ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := funext fun g => (hg g).2.2
    rw [this]
    exact ((hN.comp hcoe).inv₀ fun g => (hg g).1).smul (hrev.comp hcoe)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (ι Q) (LinearMap.ker_eq_bot.2 (cliffordι_injective Q))
  have hT : ∀ (g : M0 Q) (x : V), (conjM0 g : Module.End k V) x =
      r (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q x *
        (((g⁻¹ : M0 Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
    intro g x
    have h := conjHom_spec (Subgroup.inclusion M0_le g) x
    have h' : ι Q (conjM0 g x) = ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q x *
        (((g⁻¹ : M0 Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := h
    rw [← h']
    exact (LinearMap.congr_fun hr (conjM0 g x)).symm
  have hx : ∀ x : V, Continuous fun g : M0 Q => (conjM0 g : Module.End k V) x := by
    intro x
    simp only [hT]
    exact r.continuous_of_finiteDimensional.comp
      (continuous_mul_clifford.comp ((continuous_mul_clifford.comp (hcoe.prodMk continuous_const)).prodMk hinv))
  let b := Module.finBasis k V
  have hb : ∀ g : M0 Q, (conjM0 g : Module.End k V) = b.constr k (fun i => (conjM0 g : Module.End k V) (b i)) := by
    intro g
    exact b.ext fun i => by rw [Module.Basis.constr_basis]
  have : (fun g : M0 Q => (conjM0 g : Module.End k V)) =
      fun g => (b.constr k).toLinearMap (fun i => (conjM0 g : Module.End k V) (b i)) :=
    funext fun g => hb g
  rw [this]
  exact (b.constr k).toLinearMap.continuous_of_finiteDimensional.comp (continuous_pi fun i => hx (b i))

end Topology

end QuadFormsKB.Cassels
