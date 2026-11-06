/-
# Cassels, Chapter 10, §6–7: change of fields and rings, and the topology of $\mathbb Z_p$-lattices

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §6 (p. 185, "Change of fields and rings") and the
opening paragraphs of §7 (p. 186, "The strong approximation theorem").

**Setting.** $k$ is a field with $2$ invertible, $V$ a $k$-vector space with a quadratic form $Q$, and $K \supseteq k$ an
extension field (`[Field K] [Algebra k K]`). The extended space is $V_K = K \otimes_k V$ with the quadratic form
`Q.baseChange K` (Mathlib's `QuadraticForm.baseChange`, $Q_K(a \otimes v) = a^2 Q(v)$). The Clifford algebras are
Mathlib's `CliffordAlgebra Q` and `CliffordAlgebra (Q.baseChange K)`.

**Formalized (Cassels' "triviality", p. 185).**
* the natural ring homomorphism $C(V) \to C(V_K)$, $\iota(v) \mapsto \iota(1 \otimes v)$, is Mathlib's
  `CliffordAlgebra.ofBaseChangeAux K Q`; it is injective (`ofBaseChangeAux_injective`), commutes with the canonical
  involution $u \mapsto u'$ (`reverse`), the grade involution and the star involution (`ofBaseChangeAux_reverse`,
  `ofBaseChangeAux_involute`, `ofBaseChangeAux_star`) and preserves the even Clifford algebra;
* the group homomorphism $\operatorname{Spin}(V) \to \operatorname{Spin}(V_K)$ (`spinBaseChange`) and Cassels' remark on
  p. 186 that it is "actually, an embedding" (`spinBaseChange_injective`);
* the homomorphisms $O(V) \to O(V_K)$ (`orthBaseChange`, $\sigma \mapsto \mathrm{id}_K \otimes \sigma$) and
  $\Omega(V) \to \Omega(V_K)$ (`glBaseChange_mem_omega`), the latter because every group homomorphism maps the
  commutator subgroup into the commutator subgroup (`Subgroup.map_commutator`);
* the lattice version: for rings $I \subseteq k$ and $J \subseteq K$ with compatible algebra structures and an
  $I$-submodule $\Lambda \subseteq V$, the $J$-submodule $\Lambda_J$ of $V_K$ spanned by the vectors $1 \otimes x$
  ($x \in \Lambda$) (`baseChangeLat`); the homomorphism maps $C(\Lambda)$ into $C(\Lambda_J)$
  (`ofBaseChangeAux_mem_intClifford`) and $\operatorname{Spin}(\Lambda)$ into $\operatorname{Spin}(\Lambda_J)$
  (`spinBaseChange_mem_intSpin`).

**Formalized (§7, p. 186: topology of $\mathbb Z_p$-lattices).** For a $\mathbb Z_p$-lattice $\Lambda_p$ in a
finite-dimensional $\mathbb Q_p$-vector space $V_p$ with a quadratic form $Q$ (`Λ`: a $\mathbb Z_p$-submodule spanning
$V_p$ over $\mathbb Q_p$), with the vector space topology (`moduleTopology`, written `cliffordTopology Q` on
$C(V_p)$, and the subspace topology on $\operatorname{Spin}(V_p)$): $\Lambda_p$ is open and closed in $V_p$
(`isOpen_and_isClosed_padicLattice`), $C(\Lambda_p)$ is open and closed in $C(V_p)$
(`isOpen_and_isClosed_intClifford`), and $\operatorname{Spin}(\Lambda_p)$ is open and closed in
$\operatorname{Spin}(V_p)$ (`isOpen_and_isClosed_intSpin`). The proof is one lemma: a $\mathbb Z_p$-submodule of a
finite-dimensional $\mathbb Q_p$-space which spans it contains a $\mathbb Q_p$-basis, hence the $\mathbb Z_p$-span
of that basis, which is open; an open additive subgroup is closed. The hypotheses (7.2) ($\phi(\Lambda_p) \subseteq
\mathbb Z_p$) and "finitely generated" are **not needed** for these statements (they are needed for $C(\Lambda_p)$ to
be a finitely generated $\mathbb Z_p$-module, which is not part of the claim), so the statements here are
slightly more general than Cassels'. Finally, for the local orthogonal group in the repository's coordinate model
($O(V)(F_v) \subseteq \mathrm{GL}_n(F_v)$ for a number field $F$ and finite place $v$; $F = \mathbb Q$ is the case
of the book) the stabilizer $O(\Lambda_v)$ of a lattice is open (already in the library) and closed
(`isOpen_and_isClosed_stabLat`).

**Indices.** All indexing is 0-based; nothing in this file is indexed.
-/
import QuadFormsKB.Literature.Cassels.Ch10.SpinGroup
import QuadFormsKB.Literature.Cassels.Ch10.IntegralClifford
import QuadFormsKB.Literature.OMeara.Sec54Dim
import QuadFormsKB.Tamagawa.Measure.LocalSO
import Mathlib

open Module CliffordAlgebra
open scoped TensorProduct

namespace QuadFormsKB.Cassels

set_option linter.unusedSectionVars false

section BaseChange

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  (K : Type*) [Field K] [Algebra k K] (Q : QuadraticForm k V)

/-- Helper: the natural map $C(V) \to C(V_K)$ commutes with the canonical involution $u \mapsto u'$ (`reverse`).
Arguments: `K` the extension field, `Q` the quadratic form on $V$, `x` an element of $C(V)$. -/
theorem ofBaseChangeAux_reverse (x : CliffordAlgebra Q) :
    ofBaseChangeAux K Q (reverse x) = reverse (ofBaseChangeAux K Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [reverse.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply k K (CliffordAlgebra (Q.baseChange K)), reverse.commutes]
  | ι v => simp
  | mul a b ha hb => simp [reverse.map_mul, ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- Helper: the natural map $C(V) \to C(V_K)$ commutes with the grade involution (`involute`).
Arguments: `K` the extension field, `Q` the quadratic form on $V$, `x` an element of $C(V)$. -/
theorem ofBaseChangeAux_involute (x : CliffordAlgebra Q) :
    ofBaseChangeAux K Q (involute x) = involute (ofBaseChangeAux K Q x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- Helper: the natural map $C(V) \to C(V_K)$ commutes with the star involution (the composite of `reverse` and
`involute`, Mathlib's `star`). -/
theorem ofBaseChangeAux_star (x : CliffordAlgebra Q) :
    ofBaseChangeAux K Q (star x) = star (ofBaseChangeAux K Q x) := by
  simp [star_def, ofBaseChangeAux_reverse, ofBaseChangeAux_involute]

/-- Helper: under Mathlib's isomorphism $C(V_K) \cong K \otimes_k C(V)$ (`toBaseChange`), the natural map
$C(V) \to C(V_K)$ becomes $u \mapsto 1 \otimes u$. -/
theorem toBaseChange_ofBaseChangeAux (x : CliffordAlgebra Q) :
    toBaseChange K Q (ofBaseChangeAux K Q x) = 1 ⊗ₜ[k] x := by
  have h : ((toBaseChange K Q).restrictScalars k).comp (ofBaseChangeAux K Q) =
      (Algebra.TensorProduct.includeRight : CliffordAlgebra Q →ₐ[k] K ⊗[k] CliffordAlgebra Q) := by
    ext v
    simp
  exact congr($h x)

/-- **Cassels, Ch. 10, §6, p. 185 ($C(V) \to C(V_K)$).** The natural homomorphism of rings
$C(V) \to C(V_K)$ (Mathlib's `CliffordAlgebra.ofBaseChangeAux K Q`, $\iota(v) \mapsto \iota(1 \otimes v)$) from the
Clifford algebra of $(V, Q)$ to the Clifford algebra of the extended space $V_K = K \otimes_k V$ with the form
`Q.baseChange K` is injective. Arguments: `K` the extension field of the ground field $k$, `Q` the quadratic form on
$V$. Proof: composing with the isomorphism $C(V_K) \cong K \otimes_k C(V)$ gives $u \mapsto 1 \otimes u$, which is
injective because $K$ is flat over the field $k$. -/
@[kb "cassels1978" "Ch. 10, §6, p. 185 (C(V) → C(V_K))"]
theorem ofBaseChangeAux_injective : Function.Injective (ofBaseChangeAux K Q) := by
  intro x y hxy
  have := congrArg (toBaseChange K Q) hxy
  rw [toBaseChange_ofBaseChangeAux, toBaseChange_ofBaseChangeAux] at this
  exact Algebra.TensorProduct.includeRight_injective (RingHom.injective _) this

/-- Helper: the natural map $C(V) \to C(V_K)$ maps the even Clifford algebra $C_0(V)$ into $C_0(V_K)$. -/
theorem ofBaseChangeAux_mem_even {x : CliffordAlgebra Q} (hx : x ∈ even Q) :
    ofBaseChangeAux K Q x ∈ even (Q.baseChange K) := by
  change x ∈ evenOdd Q 0 at hx
  change _ ∈ evenOdd (Q.baseChange K) 0
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [AlgHom.commutes]; exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, ofBaseChangeAux_ι, ofBaseChangeAux_ι]
    have := SetLike.mul_mem_graded
      (ι_mul_ι_mem_evenOdd_zero (Q.baseChange K) (1 ⊗ₜ[k] m₁) (1 ⊗ₜ[k] m₂)) ih
    simpa using this

/-- Helper: the natural map $C(V) \to C(V_K)$ maps the Lipschitz group of $Q$ (a subgroup of the units of $C(V)$)
into the Lipschitz group of `Q.baseChange K`: it sends the generators $\iota(v)$ to the generators $\iota(1 \otimes v)$. -/
theorem units_map_mem_lipschitzGroup {u : (CliffordAlgebra Q)ˣ} (hu : u ∈ lipschitzGroup Q) :
    Units.map (ofBaseChangeAux K Q : CliffordAlgebra Q →* _) u ∈ lipschitzGroup (Q.baseChange K) := by
  induction hu using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    refine Subgroup.subset_closure ⟨1 ⊗ₜ[k] v, ?_⟩
    simp [← hv]
  | inv_mem x hx =>
    obtain ⟨v, hv⟩ := hx
    rw [map_inv]
    refine inv_mem (Subgroup.subset_closure ⟨1 ⊗ₜ[k] v, ?_⟩)
    simp [← hv]
  | one => simp [one_mem]
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- Helper: the natural map $C(V) \to C(V_K)$ maps the Pin group into the Pin group. -/
theorem ofBaseChangeAux_mem_pinGroup {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    ofBaseChangeAux K Q x ∈ pinGroup (Q.baseChange K) := by
  obtain ⟨⟨y, hy, rfl⟩, hu⟩ := hx
  refine ⟨⟨Units.map (ofBaseChangeAux K Q : CliffordAlgebra Q →* _) y,
    units_map_mem_lipschitzGroup K Q hy, rfl⟩, ?_⟩
  obtain ⟨h1, h2⟩ := Unitary.mem_iff.1 hu
  simp only [Units.coeHom_apply] at h1 h2 ⊢
  refine Unitary.mem_iff.2 ⟨?_, ?_⟩
  · rw [← ofBaseChangeAux_star, ← map_mul, h1, map_one]
  · rw [← ofBaseChangeAux_star, ← map_mul, h2, map_one]

/-- Helper: the natural map $C(V) \to C(V_K)$ maps the spin group (as a set of elements of $C(V)$) into the spin
group of `Q.baseChange K`. -/
theorem ofBaseChangeAux_mem_spinGroup {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) :
    ofBaseChangeAux K Q x ∈ spinGroup (Q.baseChange K) :=
  ⟨ofBaseChangeAux_mem_pinGroup K Q hx.1, ofBaseChangeAux_mem_even K Q hx.2⟩

/-- **Cassels, Ch. 10, §6, p. 185 ($\operatorname{Spin}(V) \to \operatorname{Spin}(V_K)$).** The natural group
homomorphism from the spin group of $(V, Q)$ (Mathlib's `spinGroup Q`, a group of elements of $C(V)$) to the spin
group of the extended space $(V_K, Q_K)$, $V_K = K \otimes_k V$: the restriction of the natural ring homomorphism
$C(V) \to C(V_K)$ (`CliffordAlgebra.ofBaseChangeAux K Q`). Arguments: `K` the extension field of the ground field
$k$, `Q` the quadratic form on $V$. -/
@[kb "cassels1978" "Ch. 10, §6, p. 185 (Spin(V) → Spin(V_K))"]
noncomputable def spinBaseChange : spinGroup Q →* spinGroup (Q.baseChange K) where
  toFun x := ⟨ofBaseChangeAux K Q x, ofBaseChangeAux_mem_spinGroup K Q x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The underlying element of $C(V_K)$ of `spinBaseChange K Q x` is the image of $x$ under the natural ring
homomorphism $C(V) \to C(V_K)$. -/
@[simp] theorem coe_spinBaseChange (x : spinGroup Q) :
    (spinBaseChange K Q x : CliffordAlgebra (Q.baseChange K)) = ofBaseChangeAux K Q x := rfl

/-- **Cassels, Ch. 10, §7, p. 186 ($\operatorname{Spin}(V) \to \operatorname{Spin}(V_K)$ is an embedding).** The natural
homomorphism $\operatorname{Spin}(V) \to \operatorname{Spin}(V_K)$ (`spinBaseChange K Q`) is injective (Cassels:
"actually, an embedding", stated for $K = \mathbb Q_p$ and $k = \mathbb Q$). It follows from the injectivity of
$C(V) \to C(V_K)$ (`ofBaseChangeAux_injective`). -/
@[kb "cassels1978" "Ch. 10, §7, p. 186 (Spin(V) → Spin(V_p) is an embedding)"]
theorem spinBaseChange_injective : Function.Injective (spinBaseChange K Q) := fun _ _ h =>
  Subtype.ext (ofBaseChangeAux_injective K Q (congrArg Subtype.val h))

end BaseChange

section Orth

open QuadFormsKB.OMeara
open scoped commutatorElement

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  (K : Type*) [Field K] [Algebra k K] (Q : QuadraticForm k V)

/-- Helper: the group homomorphism $GL(V) \to GL(V_K)$, $\sigma \mapsto \mathrm{id}_K \otimes \sigma$ (Mathlib's
`LinearEquiv.baseChange`). Arguments: `K` the extension field, and the type `V` of the $k$-vector space (implicit). -/
noncomputable def glBaseChange : (V ≃ₗ[k] V) →* (K ⊗[k] V ≃ₗ[K] K ⊗[k] V) where
  toFun σ := LinearEquiv.baseChange k K V V σ
  map_one' := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul a v => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  map_mul' σ τ := by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul a v => simp
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Helper: `glBaseChange K` on a pure tensor, $(\mathrm{id}_K \otimes \sigma)(a \otimes v) = a \otimes \sigma v$. -/
@[simp] theorem glBaseChange_tmul (σ : V ≃ₗ[k] V) (a : K) (v : V) :
    glBaseChange K σ (a ⊗ₜ[k] v) = a ⊗ₜ[k] σ v := by
  simp [glBaseChange]

/-- Helper: $\mathrm{id}_K \otimes \sigma$ preserves the extended form $Q_K$ whenever $\sigma$ preserves $Q$. -/
theorem glBaseChange_mem_orth {σ : V ≃ₗ[k] V} (hσ : σ ∈ orth Q) :
    glBaseChange K σ ∈ orth (Q.baseChange K) := by
  have h : (Q.baseChange K).comp (glBaseChange K σ : K ⊗[k] V →ₗ[K] K ⊗[k] V) = Q.baseChange K := by
    refine _root_.baseChange_ext fun m => ?_
    simp [QuadraticMap.comp_apply, hσ m]
  intro z
  exact congr($h z)

/-- **Cassels, Ch. 10, §6, p. 185 ($O(V) \to O(V_K)$).** The natural group homomorphism from the orthogonal group
$O(V)$ (`orth Q`, the $k$-linear automorphisms of $V$ preserving $Q$) to $O(V_K)$ (`orth (Q.baseChange K)`),
$\sigma \mapsto \mathrm{id}_K \otimes \sigma$. Arguments: `K` the extension field of the ground field $k$, `Q` the
quadratic form on $V$. -/
@[kb "cassels1978" "Ch. 10, §6, p. 185 (O(V) → O(V_K))"]
noncomputable def orthBaseChange : orth Q →* orth (Q.baseChange K) where
  toFun σ := ⟨glBaseChange K (σ : V ≃ₗ[k] V), glBaseChange_mem_orth K Q σ.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- **Cassels, Ch. 10, §6, p. 185 ($\Omega(V) \to \Omega(V_K)$).** The natural homomorphism $O(V) \to O(V_K)$ maps the
commutator subgroup $\Omega(V) = [O(V), O(V)]$ (`omega Q`) into $\Omega(V_K)$ (`omega (Q.baseChange K)`): if
$\sigma \in \Omega(V)$ then $\mathrm{id}_K \otimes \sigma \in \Omega(V_K)$. Proof: a group homomorphism maps a
commutator subgroup into the commutator subgroup of the images (`Subgroup.map_commutator`), and
`glBaseChange K` maps $O(V)$ into $O(V_K)$ (`glBaseChange_mem_orth`). Arguments: `K` the extension field, `Q` the
quadratic form on $V$, `σ` an element of $\Omega(V)$ (`hσ`). -/
@[kb "cassels1978" "Ch. 10, §6, p. 185 (Ω(V) → Ω(V_K))"]
theorem glBaseChange_mem_omega {σ : V ≃ₗ[k] V} (hσ : σ ∈ omega Q) :
    glBaseChange K σ ∈ omega (Q.baseChange K) := by
  have h : (omega Q).map (glBaseChange K) ≤ omega (Q.baseChange K) := by
    rw [omega, Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_ <;>
      exact fun _ ⟨σ, hσ, h⟩ => h ▸ glBaseChange_mem_orth K Q hσ
  exact h ⟨σ, hσ, rfl⟩

end Orth

section Lattice

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  (K : Type*) [Field K] [Algebra k K] (Q : QuadraticForm k V)
  {I : Type*} [CommRing I] [Algebra I k] [Module I V] [IsScalarTower I k V]
  (J : Type*) [CommRing J] [Algebra J K] [Algebra I J] [Algebra I K] [IsScalarTower I J K]
  [IsScalarTower I k K]

/-- **The extended lattice $\Lambda_J$** (Cassels, Ch. 10, §6, p. 185: "the $J$-lattice $\Lambda_J$ in $V_K$ with the
'same' basis"): for an $I$-submodule $\Lambda \subseteq V$ and a ring $J$ with $J \to K$, the $J$-submodule of
$V_K = K \otimes_k V$ spanned by the vectors $1 \otimes x$, $x \in \Lambda$. (If $\Lambda$ has an $I$-basis
$e_0, \dots, e_{n-1}$ this is the $J$-module with basis $1 \otimes e_0, \dots, 1 \otimes e_{n-1}$ when $I \to J$ is
flat enough; Cassels only uses it for $I = \mathbb Z$, $J = \mathbb Z_p$.) Arguments: `K` the extension field, `J`
the extended ring, `Λ` the lattice in $V$. -/
@[kb "cassels1978" "Ch. 10, §6, p. 185 (Λ_J)"]
def baseChangeLat (Λ : Submodule I V) : Submodule J (K ⊗[k] V) :=
  Submodule.span J ((fun x : V => (1 : K) ⊗ₜ[k] x) '' (Λ : Set V))

variable {K J}

/-- Helper: $1 \otimes x \in \Lambda_J$ for $x \in \Lambda$. -/
theorem one_tmul_mem_baseChangeLat {Λ : Submodule I V} {x : V} (hx : x ∈ Λ) :
    (1 : K) ⊗ₜ[k] x ∈ baseChangeLat K J Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- **Cassels, Ch. 10, §6, p. 185 ($C(\Lambda) \to C(\Lambda_J)$).** The natural ring homomorphism
$C(V) \to C(V_K)$ maps the integral Clifford algebra $C(\Lambda)$ of an $I$-lattice $\Lambda \subseteq V$ into the
integral Clifford algebra $C(\Lambda_J)$ of the extended $J$-lattice $\Lambda_J \subseteq V_K$
(`baseChangeLat K J Λ`). Hypotheses: $I \to k$, $J \to K$, $I \to J$, $I \to K$ are ring maps and the squares
$I \to J \to K$, $I \to k \to K$ commute (the scalar tower conditions). -/
@[kb "cassels1978" "Ch. 10, §6, p. 185 (C(Λ) → C(Λ_J))"]
theorem ofBaseChangeAux_mem_intClifford {Λ : Submodule I V} {z : CliffordAlgebra Q}
    (hz : z ∈ intClifford Q Λ) :
    ofBaseChangeAux K Q z ∈ intClifford (Q.baseChange K) (baseChangeLat K J Λ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [ofBaseChangeAux_ι]
    exact ι_mem_intClifford (one_tmul_mem_baseChangeLat hy)
  | algebraMap r =>
    rw [IsScalarTower.algebraMap_apply I k (CliffordAlgebra Q), AlgHom.commutes,
      IsScalarTower.algebraMap_apply k K (CliffordAlgebra (Q.baseChange K)),
      ← IsScalarTower.algebraMap_apply I k K, IsScalarTower.algebraMap_apply I J K,
      ← IsScalarTower.algebraMap_apply J K (CliffordAlgebra (Q.baseChange K))]
    exact (intClifford (Q.baseChange K) (baseChangeLat K J Λ)).algebraMap_mem (algebraMap I J r)
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- **Cassels, Ch. 10, §6, p. 185 ($\operatorname{Spin}(\Lambda) \to \operatorname{Spin}(\Lambda_J)$).** The natural
homomorphism $\operatorname{Spin}(V) \to \operatorname{Spin}(V_K)$ (`spinBaseChange K Q`) maps the integral spin group
$\operatorname{Spin}(\Lambda) = C(\Lambda) \cap \operatorname{Spin}(V)$ (`intSpin Q Λ`) of an $I$-lattice $\Lambda$ into
$\operatorname{Spin}(\Lambda_J)$ (`intSpin (Q.baseChange K) (baseChangeLat K J Λ)`). Same hypotheses as
`ofBaseChangeAux_mem_intClifford`. -/
@[kb "cassels1978" "Ch. 10, §6, p. 185 (Spin(Λ) → Spin(Λ_J))"]
theorem spinBaseChange_mem_intSpin {Λ : Submodule I V} {x : spinGroup Q} (hx : x ∈ intSpin (Q := Q) Λ) :
    spinBaseChange K Q x ∈ intSpin (Q := Q.baseChange K) (baseChangeLat K J Λ) :=
  ofBaseChangeAux_mem_intClifford (J := J) Q hx

end Lattice

section PadicTopology

variable {p : ℕ} [Fact p.Prime]

/-- Helper: a $\mathbb Z_p$-submodule `M` of a finite-dimensional $\mathbb Q_p$-vector space `W` which spans `W` over
$\mathbb Q_p$ (`hM`) is open for the vector space topology (`moduleTopology`). Proof: `M` contains a $\mathbb Q_p$-basis
`B`; the set of vectors all of whose coordinates in `B` have absolute value at most $1$ is open (the coordinate maps
are continuous and the closed unit ball of $\mathbb Q_p$ is open), contained in `M` (such a vector is a
$\mathbb Z_p$-combination of `B`) and contains $0$; an additive subgroup containing a neighbourhood of $0$ is open. -/
theorem isOpen_of_span_eq_top {W : Type*} [AddCommGroup W] [Module ℚ_[p] W] [Module ℤ_[p] W]
    [IsScalarTower ℤ_[p] ℚ_[p] W] [FiniteDimensional ℚ_[p] W] (M : Submodule ℤ_[p] W)
    (hM : Submodule.span ℚ_[p] (M : Set W) = ⊤) :
    @IsOpen W (moduleTopology ℚ_[p] W) (M : Set W) := by
  let _ : TopologicalSpace W := moduleTopology ℚ_[p] W
  have : IsModuleTopology ℚ_[p] W := ⟨rfl⟩
  obtain ⟨b, hbM, hspan, hli⟩ := exists_linearIndependent ℚ_[p] (M : Set W)
  let B : Basis b ℚ_[p] W := Basis.mk hli (by rw [Subtype.range_coe, hspan, hM])
  have : Finite b := Module.Finite.finite_basis B
  have : IsTopologicalAddGroup W := IsModuleTopology.isTopologicalAddGroup ℚ_[p] W
  let _ : Fintype b := Fintype.ofFinite b
  have hB : ∀ i, B i ∈ M := fun i => by
    have : B i = (i : W) := by simp [B]
    rw [this]; exact hbM i.2
  let U : Set W := ⋂ i, (fun w => B.equivFun w i) ⁻¹' Metric.closedBall (0 : ℚ_[p]) 1
  have hUo : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => ?_
    refine (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage ?_
    exact (continuous_apply i).comp (IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap)
  have hU0 : (0 : W) ∈ U := by simp [U]
  have hUM : U ⊆ M := by
    intro w hw
    rw [← B.sum_equivFun w]
    refine sum_mem fun i _ => ?_
    have hc : ‖B.equivFun w i‖ ≤ 1 := by simpa [U] using Set.mem_iInter.1 hw i
    obtain ⟨z, hz⟩ : ∃ z : ℤ_[p], (z : ℚ_[p]) = B.equivFun w i := ⟨⟨_, hc⟩, rfl⟩
    have : B.equivFun w i • B i = z • B i := by
      rw [← hz, ← PadicInt.algebraMap_apply, algebraMap_smul]
    rw [this]
    exact M.smul_mem _ (hB i)
  exact AddSubgroup.isOpen_of_mem_nhds M.toAddSubgroup (g := 0)
    (Filter.mem_of_superset (hUo.mem_nhds hU0) hUM)

/-- Helper: a $\mathbb Z_p$-submodule `M` of a finite-dimensional $\mathbb Q_p$-vector space `W` which spans `W` over
$\mathbb Q_p$ (`hM`) is closed for the vector space topology: it is an open additive subgroup
(`isOpen_of_span_eq_top`), and open subgroups of topological groups are closed. -/
theorem isClosed_of_span_eq_top {W : Type*} [AddCommGroup W] [Module ℚ_[p] W] [Module ℤ_[p] W]
    [IsScalarTower ℤ_[p] ℚ_[p] W] [FiniteDimensional ℚ_[p] W] (M : Submodule ℤ_[p] W)
    (hM : Submodule.span ℚ_[p] (M : Set W) = ⊤) :
    @IsClosed W (moduleTopology ℚ_[p] W) (M : Set W) := by
  let _ : TopologicalSpace W := moduleTopology ℚ_[p] W
  have : IsModuleTopology ℚ_[p] W := ⟨rfl⟩
  have : IsTopologicalAddGroup W := IsModuleTopology.isTopologicalAddGroup ℚ_[p] W
  exact AddSubgroup.isClosed_of_isOpen M.toAddSubgroup (isOpen_of_span_eq_top M hM)

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V] (Q : QuadraticForm ℚ_[p] V)

/-- **The vector space topology on $C(V_p)$** (Cassels, Ch. 10, §7, p. 186): Mathlib's `moduleTopology` of the
$\mathbb Q_p$-vector space `CliffordAlgebra Q`, the unique Hausdorff topology making it a topological vector space over
$\mathbb Q_p$ (finite-dimensional case). Arguments: `Q` the quadratic form on $V_p$. -/
noncomputable abbrev cliffordTopology : TopologicalSpace (CliffordAlgebra Q) :=
  moduleTopology ℚ_[p] (CliffordAlgebra Q)

/-- Helper: the Clifford algebra of a quadratic form on a finite-dimensional $\mathbb Q_p$-space is finite-dimensional
(its dimension is $2^n$, `QuadFormsKB.OMeara.CliffordDim.finrank_cliffordAlgebra`). -/
theorem finiteDimensional_clifford : FiniteDimensional ℚ_[p] (CliffordAlgebra Q) :=
  Module.finite_of_finrank_pos
    (by rw [QuadFormsKB.OMeara.CliffordDim.finrank_cliffordAlgebra]; positivity)

variable {Q}

/-- Helper: if the $\mathbb Z_p$-lattice `Λ` spans $V_p$ over $\mathbb Q_p$, then $C(\Lambda)$ spans $C(V_p)$ over
$\mathbb Q_p$: the $\mathbb Q_p$-algebra generated by $\iota(\Lambda)$ is all of $C(V_p)$ (it contains $\iota(V_p)$) and
lies in the $\mathbb Q_p$-span of the products of elements of $\iota(\Lambda)$, which lie in $C(\Lambda)$. -/
theorem span_intClifford_eq_top {Λ : Submodule ℤ_[p] V} (hΛ : Submodule.span ℚ_[p] (Λ : Set V) = ⊤) :
    Submodule.span ℚ_[p]
      ((intClifford Q Λ : Subalgebra ℤ_[p] (CliffordAlgebra Q)) : Set (CliffordAlgebra Q)) = ⊤ := by
  have h1 : (Algebra.adjoin ℚ_[p] (ι Q '' (Λ : Set V))).toSubmodule ≤ Submodule.span ℚ_[p]
      ((intClifford Q Λ : Subalgebra ℤ_[p] (CliffordAlgebra Q)) : Set (CliffordAlgebra Q)) := by
    rw [Algebra.adjoin_eq_span]
    refine Submodule.span_mono ?_
    show (Submonoid.closure (ι Q '' (Λ : Set V)) : Set (CliffordAlgebra Q)) ⊆ _
    refine Submonoid.closure_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ι_mem_intClifford hx
  have h2 : Algebra.adjoin ℚ_[p] (ι Q '' (Λ : Set V)) = ⊤ := by
    rw [eq_top_iff, ← adjoin_range_ι (Q := Q)]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span ℚ_[p] (Λ : Set V) := by rw [hΛ]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx c
  rw [h2] at h1
  exact eq_top_iff.2 h1

/-- **Cassels, Ch. 10, §7, p. 186 ($\Lambda_p$ is open and closed in $V_p$).** A $\mathbb Z_p$-lattice `Λ` in the
finite-dimensional $\mathbb Q_p$-vector space $V_p$ (a $\mathbb Z_p$-submodule spanning $V_p$ over $\mathbb Q_p$,
`hΛ`) is an open and closed subset of $V_p$ for the vector space topology. (Finite generation of `Λ` is not needed.) -/
@[kb "cassels1978" "Ch. 10, §7, p. 186 (Λ_p is open and closed in V_p)"]
theorem isOpen_and_isClosed_padicLattice {Λ : Submodule ℤ_[p] V}
    (hΛ : Submodule.span ℚ_[p] (Λ : Set V) = ⊤) :
    @IsOpen V (moduleTopology ℚ_[p] V) (Λ : Set V) ∧ @IsClosed V (moduleTopology ℚ_[p] V) (Λ : Set V) :=
  ⟨isOpen_of_span_eq_top Λ hΛ, isClosed_of_span_eq_top Λ hΛ⟩

/-- **Cassels, Ch. 10, §7, p. 186 ($C(\Lambda_p)$ is open and closed in $C(V_p)$).** For a $\mathbb Z_p$-lattice `Λ` in
the finite-dimensional $\mathbb Q_p$-space $V_p$ with quadratic form `Q` (a $\mathbb Z_p$-submodule spanning $V_p$,
`hΛ`), the integral Clifford algebra $C(\Lambda_p)$ (`intClifford Q Λ`) is an open and closed subset of $C(V_p)$ for
the vector space topology `cliffordTopology Q`. Cassels assumes in addition that $\phi(\Lambda_p) \subseteq \mathbb Z_p$
(7.2) so that $C(\Lambda_p)$ is defined by his definition; this hypothesis is not needed here. -/
@[kb "cassels1978" "Ch. 10, §7, p. 186 (C(Λ_p) and Spin(Λ_p) are open and closed)"]
theorem isOpen_and_isClosed_intClifford {Λ : Submodule ℤ_[p] V}
    (hΛ : Submodule.span ℚ_[p] (Λ : Set V) = ⊤) :
    @IsOpen _ (cliffordTopology Q)
        ((intClifford Q Λ : Subalgebra ℤ_[p] (CliffordAlgebra Q)) : Set (CliffordAlgebra Q)) ∧
      @IsClosed _ (cliffordTopology Q)
        ((intClifford Q Λ : Subalgebra ℤ_[p] (CliffordAlgebra Q)) : Set (CliffordAlgebra Q)) := by
  have := finiteDimensional_clifford (p := p) (Q := Q)
  exact ⟨isOpen_of_span_eq_top (intClifford Q Λ).toSubmodule (span_intClifford_eq_top hΛ),
    isClosed_of_span_eq_top (intClifford Q Λ).toSubmodule (span_intClifford_eq_top hΛ)⟩

/-- **Cassels, Ch. 10, §7, p. 186 ($\operatorname{Spin}(\Lambda_p)$ is open and closed in $\operatorname{Spin}(V_p)$).**
Under the hypotheses of `isOpen_and_isClosed_intClifford`, the integral spin group
$\operatorname{Spin}(\Lambda_p) = C(\Lambda_p) \cap \operatorname{Spin}(V_p)$ (`intSpin`) is an open and closed subset of
$\operatorname{Spin}(V_p)$ (Mathlib's `spinGroup Q`) with the subspace topology induced from `cliffordTopology Q`: it is
the preimage of $C(\Lambda_p)$ under the (continuous) inclusion. -/
@[kb "cassels1978" "Ch. 10, §7, p. 186 (C(Λ_p) and Spin(Λ_p) are open and closed)"]
theorem isOpen_and_isClosed_intSpin {Λ : Submodule ℤ_[p] V}
    (hΛ : Submodule.span ℚ_[p] (Λ : Set V) = ⊤) :
    @IsOpen (spinGroup Q) (@instTopologicalSpaceSubtype _ _ (cliffordTopology Q))
        (intSpin (Q := Q) Λ : Set (spinGroup Q)) ∧
      @IsClosed (spinGroup Q) (@instTopologicalSpaceSubtype _ _ (cliffordTopology Q))
        (intSpin (Q := Q) Λ : Set (spinGroup Q)) := by
  let _ := cliffordTopology (p := p) Q
  exact ⟨(isOpen_and_isClosed_intClifford hΛ).1.preimage continuous_subtype_val,
    (isOpen_and_isClosed_intClifford hΛ).2.preimage continuous_subtype_val⟩

end PadicTopology

section OrthLattice

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F n)

/-- **Cassels, Ch. 10, §7, p. 186 ($O(\Lambda_p)$ is open and closed).** In the repository's coordinate model of the
local orthogonal group ($O(V)(F_v) = $ `orthGroup Q (v.adicCompletion F)`, the matrices in
$\mathrm{GL}_n(F_v)$ preserving the form `Q`, for a number field `F` and a finite place `v`; Cassels' case is
$F = \mathbb Q$, $F_v = \mathbb Q_p$), the stabilizer $O(\Lambda_v)$ of a lattice $\Lambda_v = g\,\mathfrak o_v^n$
(`g : GL (Fin n) (v.adicCompletion F)`) is an open and closed subgroup. Openness is
`Tamagawa.Measure.isOpen_stabLat`; closedness holds because an open subgroup of a topological group is closed
(`Subgroup.isClosed_of_isOpen`). -/
@[kb "cassels1978" "Ch. 10, §7, p. 186 (O(Λ_p) is open and closed)"]
theorem isOpen_and_isClosed_stabLat (g : GL (Fin n) (v.adicCompletion F)) :
    IsOpen (stabLat v (orthGroup Q (v.adicCompletion F)).subtype (locAct v g (std v)) :
        Set (orthGroup Q (v.adicCompletion F))) ∧
      IsClosed (stabLat v (orthGroup Q (v.adicCompletion F)).subtype (locAct v g (std v)) :
        Set (orthGroup Q (v.adicCompletion F))) :=
  ⟨Measure.isOpen_stabLat v Q g, Subgroup.isClosed_of_isOpen _ (Measure.isOpen_stabLat v Q g)⟩

end OrthLattice

end QuadFormsKB.Cassels
