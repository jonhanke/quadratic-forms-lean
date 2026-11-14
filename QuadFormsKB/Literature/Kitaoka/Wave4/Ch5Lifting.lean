/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import QuadFormsKB.Citation
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Module.Lattice
import QuadFormsKB.Literature.Kitaoka.Ch5Extension
import QuadFormsKB.Literature.OMeara.Sec82Dual
import QuadFormsKB.Literature.OMeara.Sec82Classes

/-!
# Kitaoka 1993, §§5.3–5.4: Proposition 5.3.2, Proposition 5.3.3, Corollaries 5.4.1, 5.4.2, 5.4.5

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (Cambridge Tracts in Mathematics 106, 1993), Chapter 5:
§5.3, Proposition 5.3.2 (printed p. 85) and Proposition 5.3.3 (p. 86); §5.4, Corollary 5.4.1 (p. 87),
Corollary 5.4.2 (p. 90) and Corollary 5.4.5 (p. 92). Printed page numbers. (The book also has a
"Corollary 5.3.2" on Jordan decompositions, p. 84; it is a different result.)

**Setting** (Kitaoka, p. 70): $p$ is a prime, $R = \mathbb Z_p$, $F = \mathbb Q_p$, $(a) = aR$. A quadratic space is
$V = F^n$ with a quadratic form $Q$ (Mathlib `QuadraticForm ℚ_[p] (Fin n → ℚ_[p])`), with Kitaoka's bilinear form
$B(x, y) = \tfrac12(Q(x+y) - Q(x) - Q(y))$ (`OMeara.bil Q`, equal to `pbil Q`, see `pbil_eq_bil`). A lattice is a
finitely generated $\mathbb Z_p$-submodule of $V$ spanning $V$ (`L.IsLattice ℚ_[p]`). The notions $\mathfrak s(L)$,
$\mathfrak n(L)$, modular, maximal, $O(L)$ are those of `QuadFormsKB/Literature/OMeara/Sec82.lean`
(`OMeara.scale`, `OMeara.normIdeal`, `OMeara.IsModular`, `OMeara.IsMaximal`, `OMeara.orthLat`). The ideal $(a)$
is `ℤ_[p] ∙ a`.

**Proves**
* `corollary541`: Corollary 5.4.1, *conditional on Theorem 5.4.1* (stated, `Theorem541` in `Ch5Extension.lean`):
  hypothesis `h : Theorem541`.

**Stated only** (as `Prop`s, not proved here)
* `Proposition532`: Proposition 5.3.2;
* `Proposition533`: Proposition 5.3.3;
* `Corollary542`: Corollary 5.4.2 (the book derives it from Theorem 5.4.2 (Kneser), which has no formal statement
  in the repository);
* `Corollary545`: Corollary 5.4.5 (the book derives it from Corollary 5.4.3 and Theorem 5.4.1).
-/

open QuadraticMap Submodule Module QuadFormsKB

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.Padic

variable {p : ℕ} [Fact p.Prime]

/-- Kitaoka's bilinear form `pbil` of `Ch5Extension.lean` is O'Meara's `OMeara.bil`:
$\tfrac12 (Q(x+y) - Q(x) - Q(y)) = B(x,y)$. -/
theorem pbil_eq_bil {n : ℕ} (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])) (x y : Fin n → ℚ_[p]) :
    pbil Q x y = OMeara.bil Q x y := by
  have h := OMeara.Q_add Q x y
  have h2 : polar Q x y = 2 * OMeara.bil Q x y := by
    rw [QuadraticMap.polar, h]; ring
  rw [pbil, h2]; ring

/-- **A hyperbolic basis of a lattice $N$** (the orthogonal sum of $n$ hyperbolic planes
$\begin{pmatrix}0&1\\1&0\end{pmatrix}$): there are $e_1,\dots,e_n,f_1,\dots,f_n \in V$ with $B(e_i,e_j) = 0 =
B(f_i,f_j)$, $B(e_i,f_j) = \delta_{ij}$ and $N = \mathbb Z_p[e_1,\dots,e_n,f_1,\dots,f_n]$ (indices $0,\dots,n-1$ here).
Then $Q(\sum x_ie_i + \sum y_if_i) = 2\sum x_iy_i$. -/
def IsHyperbolicSum {m : ℕ} (Q : QuadraticForm ℚ_[p] (Fin m → ℚ_[p])) (N : Submodule ℤ_[p] (Fin m → ℚ_[p]))
    (n : ℕ) : Prop :=
  ∃ e f : Fin n → (Fin m → ℚ_[p]),
    (∀ i j, OMeara.bil Q (e i) (e j) = 0) ∧ (∀ i j, OMeara.bil Q (f i) (f j) = 0) ∧
    (∀ i j, OMeara.bil Q (e i) (f j) = if i = j then 1 else 0) ∧
    N = span ℤ_[p] (Set.range e ∪ Set.range f)

/-- **Kitaoka 1993, Proposition 5.3.2** (p. 85), *stated*. Let $N$ be a maximal lattice isometric to the orthogonal
sum of $n$ copies of the hyperbolic plane $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and let $M$ be a regular quadratic
lattice over $R = \mathbb Z_p$ of rank $n$ with $\mathfrak s(M) \subseteq 2R$. Then there is a primitive submodule
$M_0$ of $N$ (i.e. $FM_0 \cap N = M_0$) with $M_0 \cong M$ and $M_0^\perp \cong M^{(-1)}$, where $M_0^\perp = \{x
\in N \mid B(x, M_0) = 0\}$ and $M^{(-1)}$ is $M$ with the form $-Q$.

*Encoding.* $N$ is a lattice on $\mathbb Q_p^{2n}$ with form `QN`, $M$ a lattice on $\mathbb Q_p^n$ with regular
form `QM`. "Maximal" is read as $(2)$-maximal (`OMeara.IsMaximal QN (ℤ_[p] ∙ 2) N`), which is what the hyperbolic
lattice with $Q = 2\sum x_iy_i$ is (Kitaoka's Lemma 5.2.3 with $a = 2$) and what the hypothesis $\mathfrak s(M)
\subseteq 2R$ requires; the printed text says only "maximal" (the machine-read text is garbled at this point).
The isometries are `OMeara.IsometricLat`: `IsometricLat QM QN M M₀` is $M \cong M_0$ and
`IsometricLat (-QM) QN M M₀ᗮ` is $M^{(-1)} \cong M_0^\perp$. -/
@[kb "kitaoka1993" "§5.3, Prop. 5.3.2, p. 85"]
def Proposition532 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (QN : QuadraticForm ℚ_[p] (Fin (2 * n) → ℚ_[p]))
    (N : Submodule ℤ_[p] (Fin (2 * n) → ℚ_[p])) (QM : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]))
    (M : Submodule ℤ_[p] (Fin n → ℚ_[p])),
    OMeara.IsMaximal QN (ℤ_[p] ∙ (2 : ℚ_[p])) N → IsHyperbolicSum QN N n →
    (polarBilin QM).Nondegenerate → M.IsLattice ℚ_[p] → OMeara.scale QM M ≤ ℤ_[p] ∙ (2 : ℚ_[p]) →
    ∃ M0 : Submodule ℤ_[p] (Fin (2 * n) → ℚ_[p]),
      M0 ≤ N ∧ (span ℚ_[p] (M0 : Set (Fin (2 * n) → ℚ_[p]))).restrictScalars ℤ_[p] ⊓ N = M0 ∧
      OMeara.IsometricLat QM QN M M0 ∧ OMeara.IsometricLat (-QM) QN M (OMeara.splitComp QN N M0)

/-- **Kitaoka 1993, Proposition 5.3.3** (p. 86), *stated*. Let $N$ be a regular quadratic lattice over
$R = \mathbb Z_p$ with $\mathfrak s(N) \subseteq R$ and $L$ a regular submodule of $N$. Then the discriminant
$d L^\perp$ of $L^\perp = \{x \in N \mid B(x, L) = 0\}$ divides $dN\cdot dL$, and the submodules of $N$ isometric to
$L$ fall into finitely many orbits under the isometries of $N$.

*Encoding.* $N$ is a lattice on $V = \mathbb Q_p^n$, regular form `Q`. Discriminants are represented by the volumes
$\mathfrak v$ (`OMeara.volume`: the ideal generated by the discriminant, $= (dL)$); "$dL^\perp$ divides
$dN\,dL$" is the inclusion of ideals $\mathfrak vN \cdot \mathfrak vL \subseteq \mathfrak v(L^\perp)$. "Regular
submodule" is `OMeara.IsRegular Q L` ($L \subseteq N$, the radical of $L$ is $0$). Finiteness is the existence of a
finite set $S$ of submodules such that every $K \subseteq N$ isometric to $L$ equals $\sigma K'$ for some $K' \in S$
and $\sigma \in O(N)$ (`OMeara.orthLat`, `OMeara.latMap`). -/
@[kb "kitaoka1993" "§5.3, Prop. 5.3.3, p. 86"]
def Proposition533 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]))
    (N L : Submodule ℤ_[p] (Fin n → ℚ_[p])),
    (polarBilin Q).Nondegenerate → N.IsLattice ℚ_[p] → OMeara.scale Q N ≤ 1 → L ≤ N →
    OMeara.IsRegular Q L →
    OMeara.volume Q N * OMeara.volume Q L ≤ OMeara.volume Q (OMeara.splitComp Q N L) ∧
    ∃ S : Set (Submodule ℤ_[p] (Fin n → ℚ_[p])), S.Finite ∧
      ∀ K : Submodule ℤ_[p] (Fin n → ℚ_[p]), K ≤ N → OMeara.IsometricLat Q Q L K →
        ∃ K' ∈ S, ∃ σ ∈ OMeara.orthLat Q N, OMeara.latMap σ K' = K

/-- A direct summand of $L$ is primitive: if $L = M \oplus M'$ then $\mathbb Q_p M \cap L = M$. -/
theorem primitive_of_summand {n : ℕ} {L M M' : Submodule ℤ_[p] (Fin n → ℚ_[p])} (hdisj : M ⊓ M' = ⊥)
    (hsup : M ⊔ M' = L) {x : Fin n → ℚ_[p]}
    (hx : x ∈ (span ℚ_[p] (M : Set (Fin n → ℚ_[p]))).restrictScalars ℤ_[p] ⊓ L) : x ∈ M := by
  obtain ⟨hxs, hxL⟩ := hx
  obtain ⟨d, hd0, hdx⟩ := OMeara.exists_smul_mem_of_mem_span (R := ℤ_[p]) (F := ℚ_[p]) hxs
  rw [← hsup] at hxL
  obtain ⟨m, hm, m', hm', rfl⟩ := Submodule.mem_sup.mp hxL
  have h1 : d • m' ∈ M ⊓ M' := by
    refine ⟨?_, M'.smul_mem d hm'⟩
    have : d • m' = d • (m + m') - d • m := by rw [smul_add]; abel
    rw [this]
    exact M.sub_mem hdx (M.smul_mem d hm)
  rw [hdisj, Submodule.mem_bot] at h1
  have : m' = 0 := (smul_eq_zero.mp h1).resolve_left hd0
  rw [this, add_zero]
  exact hm

/-- **Kitaoka 1993, Corollary 5.4.1** (p. 87), *conditional on Theorem 5.4.1 (stated)*: hypothesis
`h : Theorem541`. Let $L$ be a unimodular lattice over $R = \mathbb Z_p$ with $\mathfrak n(L) = (2)$. If $M$ and $N$
are isometric submodules of $L$ and both are direct summands of $L$ (as $R$-modules), then they are transformed into
each other by an isometry of $L$: there is $\tau \in O(L)$ with $\tau M = N$.

*Encoding.* $L$ is a lattice on $\mathbb Q_p^n$ with regular form `Q`; "$M$ is a direct summand of $L$" is
`∃ M', M ⊓ M' = ⊥ ∧ M ⊔ M' = L`; "isometric" is `OMeara.IsometricLat Q Q M N`.

*Proof (the book's).* Apply Theorem 5.4.1 with $\tilde M = M$, $\tilde N = N$ (summands are primitive), $L^\sharp = L$
(unimodular, 82:14b), $a = 1$ (as $\mathfrak n(L^\sharp) = (2)$) and no exponents ($r = 0$); the congruence
hypothesis holds since $\sigma x - x \in L = L^\sharp$. The isometry extending $\sigma$ lies in $O(L)$ and
maps $M$ onto $N$. -/
@[kb "kitaoka1993" "§5.4, Cor. 5.4.1, p. 87"]
theorem corollary541 (h : Theorem541) {n : ℕ} (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]))
    {L M N : Submodule ℤ_[p] (Fin n → ℚ_[p])} (hQ : (polarBilin Q).Nondegenerate)
    (hL : L.IsLattice ℚ_[p]) (hU : OMeara.IsUnimodular Q L) (hnorm : OMeara.normIdeal Q L = ℤ_[p] ∙ (2 : ℚ_[p]))
    (hML : M ≤ L) (hNL : N ≤ L) (hMN : OMeara.IsometricLat Q Q M N)
    (hMs : ∃ M' : Submodule ℤ_[p] (Fin n → ℚ_[p]), M ⊓ M' = ⊥ ∧ M ⊔ M' = L)
    (hNs : ∃ N' : Submodule ℤ_[p] (Fin n → ℚ_[p]), N ⊓ N' = ⊥ ∧ N ⊔ N' = L) :
    ∃ τ ∈ OMeara.orthLat Q L, OMeara.latMap τ M = N := by
  have hU' : OMeara.IsModular Q 1 L := hU
  have hLfg := hL.fg
  have hL0 : L ≠ ⊥ := by
    intro hbot
    apply hU'.1
    rw [← hU'.2.1, hbot]
    exact OMeara.scale_bot Q
  have hreg := OMeara.IsModular.isRegular Q hU' hLfg
  have hdual := (OMeara.isUnimodular_iff_dual_eq Q hLfg hL0 hreg).mp hU
  -- `L^♯ = L`
  have hdL : ∀ x, x ∈ dualL Q L ↔ x ∈ L := by
    intro x
    constructor
    · intro hx
      have : x ∈ OMeara.dual Q L := by
        refine ⟨by rw [hL.span_eq_top]; trivial, fun y hy => ?_⟩
        obtain ⟨r, hr⟩ := hx y hy
        rw [Submodule.mem_one]
        exact ⟨r, by rw [PadicInt.algebraMap_apply, ← pbil_eq_bil, hr, one_mul]⟩
      rwa [hdual] at this
    · intro hx y hy
      have : OMeara.bil Q x y ∈ OMeara.scale Q L := OMeara.bil_mem_scale Q hx hy
      rw [hU'.2.1, Submodule.mem_one] at this
      obtain ⟨r, hr⟩ := this
      exact ⟨r, by rw [pbil_eq_bil, ← hr, PadicInt.algebraMap_apply, one_mul]⟩
  obtain ⟨σ, hσ⟩ := hMN
  have key := h p n Q L M N 1 0 (fun i => i.elim0) hQ hL hML hNL one_ne_zero (by intro i; exact i.elim0)
  have hMne : ∀ {M M' : Submodule ℤ_[p] (Fin n → ℚ_[p])}, M ⊓ M' = ⊥ → M ⊔ M' = L →
      Nonempty ((↥((span ℚ_[p] (M : Set (Fin n → ℚ_[p]))).restrictScalars ℤ_[p] ⊓ L) ⧸
        M.comap ((span ℚ_[p] (M : Set (Fin n → ℚ_[p]))).restrictScalars ℤ_[p] ⊓ L).subtype) ≃ₗ[ℤ_[p]]
        ((i : Fin 0) → ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (fun i : Fin 0 => i.elim0 : Fin 0 → ℕ) i})) := by
    intro M M' h1 h2
    have hs : Subsingleton ((↥((span ℚ_[p] (M : Set (Fin n → ℚ_[p]))).restrictScalars ℤ_[p] ⊓ L) ⧸
        M.comap ((span ℚ_[p] (M : Set (Fin n → ℚ_[p]))).restrictScalars ℤ_[p] ⊓ L).subtype)) := by
      rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
      intro y _
      exact primitive_of_summand h1 h2 y.2
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  obtain ⟨M', hM1, hM2⟩ := hMs
  obtain ⟨N', hN1, hN2⟩ := hNs
  have hdc : ∀ x ∈ dualL Q L, InIdeal 2 ((1 : ℚ_[p]) * Q x) := by
    intro x hx
    have : Q x ∈ OMeara.normIdeal Q L := OMeara.Q_mem_normIdeal Q ((hdL x).mp hx)
    rw [hnorm] at this
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨r, by rw [one_mul, ← hr, Algebra.smul_def, PadicInt.algebraMap_apply, mul_comm]⟩
  have happ : ∀ x : M, ∃ z ∈ dualL Q L, (σ x : Fin n → ℚ_[p]) - x =
      ((1 : ℚ_[p]) * (p : ℚ_[p]) ^ (Finset.univ.sup (fun i : Fin 0 => i.elim0 : Fin 0 → ℕ))) • z := by
    intro x
    refine ⟨(σ x : Fin n → ℚ_[p]) - x, (hdL _).mpr (L.sub_mem (hNL (σ x).2) (hML x.2)), ?_⟩
    simp
  obtain ⟨τ, hτQ, hτL, hτL', hτM, -⟩ := key (hMne hM1 hM2) (hMne hN1 hN2) hdc σ hσ happ
  have hτ : τ ∈ OMeara.orthLat Q L := by
    show τ ∈ OMeara.orth Q ∧ OMeara.latMap τ L = L
    refine ⟨hτQ, ?_⟩
    ext x
    simp only [OMeara.latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hτL y hy
    · intro hx
      exact ⟨τ.symm x, hτL' x hx, by simp⟩
  refine ⟨τ, hτ, ?_⟩
  ext y
  simp only [OMeara.latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [show τ x = σ ⟨x, hx⟩ from hτM ⟨x, hx⟩]
    exact (σ ⟨x, hx⟩).2
  · intro hy
    refine ⟨(σ.symm ⟨y, hy⟩ : Fin n → ℚ_[p]), (σ.symm ⟨y, hy⟩).2, ?_⟩
    rw [show τ (σ.symm ⟨y, hy⟩ : Fin n → ℚ_[p]) = σ (σ.symm ⟨y, hy⟩) from hτM _]
    simp

/-- **Kitaoka 1993, Corollary 5.4.2** (p. 90), *stated*. Let $L$ and $M$ be quadratic lattices over $R = \mathbb Z_p$
with $L$ regular, and fix an integer $h$ with $p^h Q(L^\sharp) \subseteq (2)$. If $\sigma \in \mathrm{Hom}_F(FL, FM)$
satisfies $\sigma(L) \subseteq M$ and $Q(\sigma x) \equiv Q(x) \bmod 2p^{h+1}R$ for $x \in L$, then there is an
isometry $\eta : FL \to FM$ with $\eta(L) = \sigma(L)$, $\eta(L^\sharp) = \sigma(L^\sharp)$ and
$\eta(x) \equiv \sigma(x) \bmod p^{h+1}\sigma(L^\sharp)$ for $x \in L$.

*Encoding.* $V = FL = \mathbb Q_p^n$ with regular form `QL` and lattice $L$ on it; $W = \mathbb Q_p^m$ with form `QM`;
$M \subseteq W$ a finitely generated $R$-submodule (it enters only through $\sigma(L) \subseteq M$); $h \in \mathbb Z$
(`(p : ℚ_[p]) ^ h` is an integer power). "$c \equiv d \bmod 2p^{h+1}R$" is `InIdeal (2 * p ^ (h+1)) (c - d)`;
the isometry $\eta$ is an $F$-linear map $V \to W$ with $Q_M(\eta x) = Q_L(x)$ (injective, as $V$ is regular);
$\eta(x) \equiv \sigma(x) \bmod p^{h+1}\sigma(L^\sharp)$ means $\eta(x) - \sigma(x) = p^{h+1}\sigma(z)$ with
$z \in L^\sharp$ (`dualL`). *Printed text:* "$\eta : L \cong M$"; the proof calls $\eta$ an isometry from $L$ to $FM$,
which is what is stated. -/
@[kb "kitaoka1993" "§5.4, Cor. 5.4.2, p. 90"]
def Corollary542 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m : ℕ) (QL : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]))
    (QM : QuadraticForm ℚ_[p] (Fin m → ℚ_[p])) (L : Submodule ℤ_[p] (Fin n → ℚ_[p]))
    (M : Submodule ℤ_[p] (Fin m → ℚ_[p])) (h : ℤ) (σ : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin m → ℚ_[p])),
    (polarBilin QL).Nondegenerate → L.IsLattice ℚ_[p] → M.FG →
    (∀ x ∈ dualL QL L, InIdeal 2 ((p : ℚ_[p]) ^ h * QL x)) →
    (∀ x ∈ L, σ x ∈ M) →
    (∀ x ∈ L, InIdeal (2 * (p : ℚ_[p]) ^ (h + 1)) (QM (σ x) - QL x)) →
    ∃ η : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin m → ℚ_[p]),
      (∀ x, QM (η x) = QL x) ∧ η '' (L : Set (Fin n → ℚ_[p])) = σ '' (L : Set (Fin n → ℚ_[p])) ∧
      η '' dualL QL L = σ '' dualL QL L ∧
      ∀ x ∈ L, ∃ z ∈ dualL QL L, η x - σ x = (p : ℚ_[p]) ^ (h + 1) • σ z

/-- **Kitaoka 1993, Corollary 5.4.5** (p. 92), *stated*. Let $N$ be a regular quadratic lattice over
$R = \mathbb Z_p$ and $L = R[v_1, \dots, v_k]$ a regular submodule of $N$. If $w_i \in N$ is sufficiently close to
$v_i$ for $i = 1, \dots, k$, then there is an isometry $\sigma \in O(N)$ with $\sigma(L) = R[w_1, \dots, w_k]$.

*Encoding.* $N$ is a lattice on $\mathbb Q_p^m$ with regular form `Q`; $v_1, \dots, v_k$ (indices $0, \dots, k-1$)
are $R$-linearly independent elements of $N$ (a basis of $L$: the book takes $L = R[v_1,\dots,v_n]$ to have these as
its basis, as in its other statements on $R[v_1, \dots, v_n]$) with $L$ regular (`OMeara.IsRegular`).
"Sufficiently close" is: there is $\varepsilon > 0$ such that all $w_i \in N$ with $\|w_i - v_i\| < \varepsilon$ (the
supremum norm on $\mathbb Q_p^m$) satisfy the conclusion. $O(N)$ is `OMeara.orthLat Q N`. -/
@[kb "kitaoka1993" "§5.4, Cor. 5.4.5, p. 92"]
def Corollary545 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m k : ℕ) (Q : QuadraticForm ℚ_[p] (Fin m → ℚ_[p]))
    (N : Submodule ℤ_[p] (Fin m → ℚ_[p])) (v : Fin k → (Fin m → ℚ_[p])),
    (polarBilin Q).Nondegenerate → N.IsLattice ℚ_[p] → (∀ i, v i ∈ N) → LinearIndependent ℤ_[p] v →
    OMeara.IsRegular Q (span ℤ_[p] (Set.range v)) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : Fin k → (Fin m → ℚ_[p]), (∀ i, w i ∈ N) → (∀ i, ‖w i - v i‖ < ε) →
      ∃ σ ∈ OMeara.orthLat Q N, OMeara.latMap σ (span ℤ_[p] (Set.range v)) = span ℤ_[p] (Set.range w)

end QuadFormsKB.Kitaoka.Padic
