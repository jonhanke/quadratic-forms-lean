/-
# Cassels, Chapter 8, Examples 6 and 7: maximal $\mathbb Z_p$-lattices

**Setting.** $(V, \varphi)$ is a regular quadratic space over $\mathbb Q_p$ (`Q : QuadraticForm ℚ_[p] V`, regular:
the associated bilinear form is nondegenerate), and a $\mathbb Z_p$-lattice is a $\mathbb Z_p$-submodule
$\Lambda \subseteq V$ that is a lattice on $V$ (`Submodule.IsLattice`), as in O'Meara's §82 (`Literature/OMeara/Sec82.lean`).
Cassels' bilinear form $\varphi(\vec x, \vec y)$, with $\varphi(\vec x, \vec x) = \varphi(\vec x)$, is O'Meara's
$B$ (`OMeara.bil`). The form $\varphi$ induces a *classically integral* form on $\Lambda$ when
$\varphi(\vec c, \vec d) \in \mathbb Z_p$ for all $\vec c, \vec d \in \Lambda$, i.e. the scale $\mathfrak s\Lambda$
(`OMeara.scale`) is contained in $\mathbb Z_p$; with the *non-classical* definition (Example 7) one asks only
$\varphi(\vec c) \in \mathbb Z_p$, i.e. the norm $\mathfrak n\Lambda \subseteq \mathbb Z_p$, which is O'Meara's
$\mathfrak o$-maximality (`OMeara.IsMaximal Q 1`).

**Defines** `IsClassMaximal` (Example 6: classically maximal lattices).

**Proves**
* `isClassMaximal_iff_isMaximal` ($p \ne 2$): classically maximal is O'Meara's $\mathfrak o$-maximal (Examples 6 and 7
  agree for $p \ne 2$, since $\mathfrak n\Lambda = \mathfrak s\Lambda$ when $2$ is a unit, O'Meara p. 246);
* `exists_isClassMaximal_ge` (**Example 6 (i)**, p. 126): every lattice on which $\varphi$ is classically integral is
  contained in a classically maximal lattice. *Update:* the book says "every lattice $\Lambda$"; the hypothesis that
  $\varphi$ is integral on $\Lambda$ is needed (a lattice on which $\varphi$ is not integral is contained in no
  integral lattice);
* `exists_basis_of_isClassMaximal` (**Example 6 (ii)**, p. 126): for $p \ne 2$ a classically maximal lattice has a
  basis $\vec b_1, \dots, \vec b_n$ with $\varphi(\sum x_j\vec b_j) = \sum c_jx_j^{2}$, $|c_j| \in \{1, p^{-1}\}$, and
  $|c_j| = p^{-1}$ for at most two $j$;
* `exists_basis_of_isMaximal` (**Example 7 (ii)**, p. 126, $p \ne 2$): the same for O'Meara's $\mathfrak o$-maximal
  lattices (Example 7 (i) is O'Meara 82:18, cited in `Ch7/Citations.lean`).
Examples 6 (iii) and 7 (iii) ("state and prove the corresponding statement for $p = 2$") are not formalized.

**Proof sketch of Example 6 (ii).** Take an orthogonal basis (O'Meara §92, p. 246; $p \ne 2$), $c_j = \varphi(\vec b_j)$
integral. If $|c_j| \le p^{-2}$, then $\Lambda + \mathbb Z_p p^{-1}\vec b_j$ is integral and larger. If
$|c_i| = |c_j| = |c_k| = p^{-1}$ for three indices, the ternary form $p^{-1}(c_ix^{2} + c_jy^{2} + c_kz^{2})$ has a
non-trivial zero modulo $p$ (Chevalley), $(x, y, z)$ not all divisible by $p$, and with
$\vec v = x\vec b_i + y\vec b_j + z\vec b_k$ the lattice $\Lambda + \mathbb Z_p p^{-1}\vec v$ is integral and larger.
-/
import QuadFormsKB.Literature.Cassels.Ch8.LatticeBridge
import QuadFormsKB.Literature.OMeara.Sec82Max
import QuadFormsKB.Literature.OMeara.Sec92

namespace QuadFormsKB.Cassels

open Submodule OMeara

variable {p : ℕ} [hp : Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
  [FiniteDimensional ℚ_[p] V]

/-- **Classically maximal lattice** (Cassels 1978, Ch. 8, Example 6, p. 125): a $\mathbb Z_p$-lattice $\Lambda$ on
$V$ is *(classically) maximal* when (i) $\varphi$ induces on $\Lambda$ a classically integral form
($\varphi(\vec c, \vec d) \in \mathbb Z_p$ for $\vec c, \vec d \in \Lambda$: the scale `OMeara.scale Q Λ` is contained
in $\mathbb Z_p$, `(1 : Submodule ℤ_[p] ℚ_[p])`) and (ii) if $\Gamma$ is a $\mathbb Z_p$-lattice on $V$ properly
containing $\Lambda$ then $\varphi$ does not induce a classically integral form on $\Gamma$. -/
@[kb "cassels1978" "Ch. 8, Ex. 6, p. 125 ((classically) maximal lattice)"]
def IsClassMaximal (Q : QuadraticForm ℚ_[p] V) (Λ : Submodule ℤ_[p] V) : Prop :=
  Λ.IsLattice ℚ_[p] ∧ scale Q Λ ≤ 1 ∧
    ∀ Γ : Submodule ℤ_[p] V, Γ.IsLattice ℚ_[p] → Λ ≤ Γ → scale Q Γ ≤ 1 → Γ = Λ

/-- For $p \ne 2$ classically maximal lattices are O'Meara's $\mathfrak o$-maximal lattices (the norm and the scale
agree when $2$ is a unit), so Examples 6 and 7 of Cassels, Ch. 8, are the same for $p \ne 2$. -/
theorem isClassMaximal_iff_isMaximal (hp2 : p ≠ 2) (Q : QuadraticForm ℚ_[p] V) (Λ : Submodule ℤ_[p] V) :
    IsClassMaximal Q Λ ↔ IsMaximal Q 1 Λ := by
  have h2 : IsUnit (2 : ℤ_[p]) := by
    have : IsUnit ((2 : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.2
      (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2))
    simpa using this
  have hn : ∀ L : Submodule ℤ_[p] V, normIdeal Q L = scale Q L := fun L => normIdeal_eq_scale Q h2 L
  simp only [IsClassMaximal, IsMaximal, hn]

/-- **Cassels, Ch. 8, Example 6 (i)** (p. 126): *every lattice $\Lambda$ is contained in at least one (classically)
maximal lattice*, for a regular quadratic space $V$ over $\mathbb Q_p$. *Update:* the hypothesis that $\varphi$ is
classically integral on $\Lambda$ (`scale Q Λ ≤ 1`) is needed and added. -/
@[kb "cassels1978" "Ch. 8, Ex. 6 (i), p. 126 (with the hypothesis that the form is integral on the lattice)"]
theorem exists_isClassMaximal_ge {Q : QuadraticForm ℚ_[p] V} (hV : (QuadraticMap.associated Q).Nondegenerate)
    {Λ : Submodule ℤ_[p] V} (hΛ : Λ.IsLattice ℚ_[p]) (hs : scale Q Λ ≤ 1) :
    ∃ Γ, Λ ≤ Γ ∧ IsClassMaximal Q Γ := by
  classical
  set a : Submodule ℤ_[p] ℚ_[p] := Submodule.span ℤ_[p] {(2 : ℚ_[p])} with ha
  have ha2 : ∀ c : ℚ_[p], 2 * c ∈ a ↔ c ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
    intro c
    have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
    rw [ha, Submodule.mem_span_singleton, Submodule.mem_one]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_⟩
      rw [Algebra.smul_def] at hr
      have : (2 : ℚ_[p]) * (algebraMap ℤ_[p] ℚ_[p] r) = 2 * c := by rw [← hr]; ring
      exact mul_left_cancel₀ h2 this
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_⟩
      rw [Algebra.smul_def, hr]; ring
  set K' := dualLatMax Q a Λ with hK'
  have hLK' : Λ ≤ K' := by
    intro k hk k' hk'
    exact (ha2 _).2 (hs (bil_mem_scale Q hk hk'))
  have hfg : K'.FG := fg_dualLatMax Q hV (Submodule.fg_span_singleton _) hΛ
  have : Module.Finite ℤ_[p] K' := Module.Finite.iff_fg.mpr hfg
  let S : Set (Submodule ℤ_[p] K') :=
    {N | Λ ≤ N.map K'.subtype ∧ scale Q (N.map K'.subtype) ≤ 1}
  have e : (Λ.comap K'.subtype).map K'.subtype = Λ := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hLK'
  have hS : S.Nonempty := ⟨Λ.comap K'.subtype, by rw [e], by rw [e]; exact hs⟩
  obtain ⟨N, hNS, hNmax⟩ :=
    (set_has_maximal_iff_noetherian (R := ℤ_[p]) (M := K')).mpr inferInstance S hS
  have hfgM : (N.map K'.subtype).FG := (IsNoetherian.noetherian N).map _
  have hlat : (N.map K'.subtype).IsLattice ℚ_[p] :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ_[p] hNS.1 hfgM
  refine ⟨N.map K'.subtype, hNS.1, hlat, hNS.2, ?_⟩
  intro N2 hN2 hMN2 hnN2
  have hKN2 : Λ ≤ N2 := hNS.1.trans hMN2
  have hN2K' : N2 ≤ K' := by
    intro m hm k hk
    exact (ha2 _).2 (hnN2 (bil_mem_scale Q hm (hKN2 hk)))
  have e2 : (N2.comap K'.subtype).map K'.subtype = N2 := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hN2K'
  have hle : N ≤ N2.comap K'.subtype := Submodule.map_le_iff_le_comap.mp hMN2
  have hmem : N2.comap K'.subtype ∈ S := ⟨by rw [e2]; exact hKN2, by rw [e2]; exact hnN2⟩
  have heq : N = N2.comap K'.subtype := by
    by_contra hne
    exact hNmax _ hmem (lt_of_le_of_ne hle hne)
  rw [heq, e2]

omit [FiniteDimensional ℚ_[p] V] in
/-- A vector $w$ with $\varphi(w, \Lambda) \subseteq \mathbb Z_p$ and $\varphi(w) \in \mathbb Z_p$ lies in a
classically maximal lattice $\Lambda$ (else $\Lambda + \mathbb Z_p w$ is a larger integral lattice). -/
private theorem mem_of_integral {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} (hΛ : IsClassMaximal Q Λ)
    {w : V} (h1 : ∀ y ∈ Λ, OMeara.bil Q w y ∈ (1 : Submodule ℤ_[p] ℚ_[p]))
    (h2 : OMeara.bil Q w w ∈ (1 : Submodule ℤ_[p] ℚ_[p])) : w ∈ Λ := by
  have := hΛ.1
  have hΓ : (Λ ⊔ Submodule.span ℤ_[p] {w}).IsLattice ℚ_[p] :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ_[p] le_sup_left
      (hΛ.1.fg.sup (Submodule.fg_span_singleton _))
  have hm : ∀ (r : ℤ_[p]) (z : ℚ_[p]), z ∈ (1 : Submodule ℤ_[p] ℚ_[p]) →
      algebraMap ℤ_[p] ℚ_[p] r * z ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := fun r z hz => by
    simpa [Algebra.smul_def] using (1 : Submodule ℤ_[p] ℚ_[p]).smul_mem r hz
  have hs : scale Q (Λ ⊔ Submodule.span ℤ_[p] {w}) ≤ 1 := by
    rw [scale, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨l, hl, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨l', hl', s', hs', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hs
    obtain ⟨r', rfl⟩ := Submodule.mem_span_singleton.mp hs'
    have hll : OMeara.bil Q l l' ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := hΛ.2.1 (bil_mem_scale Q hl hl')
    have hlw : OMeara.bil Q l w ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by rw [OMeara.bil_comm Q]; exact h1 l hl
    have hwl : OMeara.bil Q w l' ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := h1 l' hl'
    simp only [SetLike.mem_coe, bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right]
    exact add_mem (add_mem hll (hm _ _ hwl)) (hm _ _ (add_mem hlw (hm _ _ h2)))
  have := hΛ.2.2 _ hΓ le_sup_left hs
  rw [← this]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)

omit [FiniteDimensional ℚ_[p] V] in
/-- Integrality of $\varphi(w, \cdot)$ on $\Lambda$ can be checked on a basis. -/
private theorem forall_mem_one_of_basis {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V} {m : ℕ}
    (b : Module.Basis (Fin m) ℤ_[p] Λ) {w : V}
    (h : ∀ k, OMeara.bil Q w (b k : V) ∈ (1 : Submodule ℤ_[p] ℚ_[p])) :
    ∀ y ∈ Λ, OMeara.bil Q w y ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
  intro y hy
  have hy' : y = ∑ k, (b.repr ⟨y, hy⟩ k) • (b k : V) := by
    have h2 := congrArg (fun z : Λ => (z : V)) (b.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have : OMeara.bil Q w y = ∑ k, algebraMap ℤ_[p] ℚ_[p] (b.repr ⟨y, hy⟩ k) * OMeara.bil Q w (b k : V) := by
    calc OMeara.bil Q w y = OMeara.bil Q w (∑ k, (b.repr ⟨y, hy⟩ k) • (b k : V)) := congrArg _ hy'
      _ = _ := by
        show (QuadraticMap.associated Q w) (∑ k, (b.repr ⟨y, hy⟩ k) • (b k : V)) = _
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => OMeara.bil_rsmul_right Q _ _ _
  rw [this]
  refine Submodule.sum_mem _ fun k _ => ?_
  have := (1 : Submodule ℤ_[p] ℚ_[p]).smul_mem (b.repr ⟨y, hy⟩ k) (h k)
  simpa [Algebra.smul_def] using this

omit [FiniteDimensional ℚ_[p] V] in
/-- **Key extension step.** Let $b_0, \dots, b_{m-1}$ be an orthogonal basis of a classically maximal lattice
$\Lambda$ and $x_k \in \mathbb Z_p$ such that $w = p^{-1}\sum x_kb_k$ has $\varphi(w, b_k) \in \mathbb Z_p$ and
$\varphi(w) \in \mathbb Z_p$. Then $w \in \Lambda$, so $p \mid x_k$ for all $k$. -/
private theorem dvd_of_integral_ext {Q : QuadraticForm ℚ_[p] V} {Λ : Submodule ℤ_[p] V}
    (hΛ : IsClassMaximal Q Λ) {m : ℕ} (b : Module.Basis (Fin m) ℤ_[p] Λ)
    (horth : ∀ i j, i ≠ j → OMeara.bil Q (b i : V) (b j : V) = 0) (x : Fin m → ℤ_[p])
    (h1 : ∀ k, (p : ℚ_[p])⁻¹ * algebraMap ℤ_[p] ℚ_[p] (x k) * Q (b k : V) ∈ (1 : Submodule ℤ_[p] ℚ_[p]))
    (h2 : (p : ℚ_[p])⁻¹ ^ 2 * ∑ k, (algebraMap ℤ_[p] ℚ_[p] (x k)) ^ 2 * Q (b k : V) ∈
      (1 : Submodule ℤ_[p] ℚ_[p])) :
    ∀ k, (p : ℤ_[p]) ∣ x k := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  set v : V := ∑ k, x k • (b k : V) with hv
  have hbv : ∀ k, OMeara.bil Q v (b k : V) = algebraMap ℤ_[p] ℚ_[p] (x k) * Q (b k : V) := by
    intro k
    have : OMeara.bil Q v (b k : V) = ∑ j, algebraMap ℤ_[p] ℚ_[p] (x j) * OMeara.bil Q (b j : V) (b k : V) := by
      show (QuadraticMap.associated Q) (∑ j, x j • (b j : V)) _ = _
      rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun j _ => OMeara.bil_rsmul_left Q _ _ _
    rw [this, Finset.sum_eq_single k]
    · rw [OMeara.bil_self]
    · intro j _ hjk
      rw [horth j k hjk, mul_zero]
    · simp
  set w : V := (p : ℚ_[p])⁻¹ • v with hw
  have hbw : ∀ k, OMeara.bil Q w (b k : V) = (p : ℚ_[p])⁻¹ * (algebraMap ℤ_[p] ℚ_[p] (x k) * Q (b k : V)) := by
    intro k
    rw [hw, OMeara.bil_smul_left, hbv]
  have h1' : ∀ k, OMeara.bil Q w (b k : V) ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
    intro k
    rw [hbw, ← mul_assoc]
    exact h1 k
  have hwv : OMeara.bil Q w v = ∑ k, algebraMap ℤ_[p] ℚ_[p] (x k) * OMeara.bil Q w (b k : V) := by
    show (QuadraticMap.associated Q w) (∑ j, x j • (b j : V)) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => OMeara.bil_rsmul_right Q _ _ _
  have hww : OMeara.bil Q w w = (p : ℚ_[p])⁻¹ ^ 2 * ∑ k, (algebraMap ℤ_[p] ℚ_[p] (x k)) ^ 2 * Q (b k : V) := by
    have : OMeara.bil Q w w = (p : ℚ_[p])⁻¹ * OMeara.bil Q w v := by
      conv_lhs => rw [hw]
      rw [OMeara.bil_smul_right]
    rw [this, hwv, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hbw]; ring
  have hwΛ : w ∈ Λ := mem_of_integral hΛ (forall_mem_one_of_basis b h1') (by rw [hww]; exact h2)
  obtain ⟨w', hw'⟩ : ∃ w' : Λ, (w' : V) = w := ⟨⟨w, hwΛ⟩, rfl⟩
  set v' : Λ := ∑ k, x k • b k with hv'
  have hv'v : (v' : V) = v := by simp [hv', hv]
  have hpw : (p : ℤ_[p]) • w' = v' := by
    apply Subtype.ext
    rw [hv'v, Submodule.coe_smul, hw', ← algebraMap_smul ℚ_[p] (p : ℤ_[p]) w]
    rw [hw, map_natCast, smul_smul, mul_inv_cancel₀ hp0, one_smul]
  intro k
  have hrep : b.repr v' k = x k := by rw [hv']; exact congrFun (b.repr_sum_self x) k
  have := congrArg (fun z : Λ => b.repr z k) hpw
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hrep] at this
  exact ⟨_, this.symm⟩

/-- A nonzero element of $\mathbb Z_p$ is a unit, $p\cdot$unit or in $p^2\mathbb Z_p$. -/
private theorem classify_padic {r : ℤ_[p]} (hr : r ≠ 0) :
    IsUnit r ∨ (∃ u : ℤ_[p], IsUnit u ∧ r = p * u) ∨ ∃ s : ℤ_[p], r = p ^ 2 * s := by
  by_cases h : (p : ℤ_[p]) ∣ r
  · obtain ⟨r', rfl⟩ := h
    by_cases h' : (p : ℤ_[p]) ∣ r'
    · obtain ⟨s, rfl⟩ := h'
      exact Or.inr (Or.inr ⟨s, by ring⟩)
    · refine Or.inr (Or.inl ⟨r', ?_, rfl⟩)
      rw [PadicInt.isUnit_iff]
      by_contra hne
      exact h' ((PadicInt.norm_lt_one_iff_dvd _).1 (lt_of_le_of_ne (PadicInt.norm_le_one _) hne))
  · refine Or.inl (PadicInt.isUnit_iff.2 ?_)
    by_contra hne
    exact h ((PadicInt.norm_lt_one_iff_dvd _).1 (lt_of_le_of_ne (PadicInt.norm_le_one _) hne))

/-- For units $a, b, c$ of $\mathbb Z_p$ ($p$ odd) there are $X, Y, Z \in \mathbb Z_p$, not all divisible by $p$,
with $p \mid aX^2 + bY^2 + cZ^2$ (a non-trivial zero of a ternary form over $\mathbb F_p$). -/
private theorem ternary_zero_padic (hp2 : p ≠ 2) {a b c : ℤ_[p]} (ha : IsUnit a) (hb : IsUnit b) (_hc : IsUnit c) :
    ∃ X Y Z : ℤ_[p], ¬ ((p : ℤ_[p]) ∣ X ∧ (p : ℤ_[p]) ∣ Y ∧ (p : ℤ_[p]) ∣ Z) ∧
      (p : ℤ_[p]) ∣ a * X ^ 2 + b * Y ^ 2 + c * Z ^ 2 := by
  have hdvd : ∀ z : ℤ_[p], (p : ℤ_[p]) ∣ z ↔ PadicInt.toZMod z = 0 := by
    intro z
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  have nz : ∀ u : ℤ_[p], IsUnit u → PadicInt.toZMod u ≠ 0 := by
    intro u hu h
    exact PadicInt.p_nonunit (isUnit_of_dvd_unit ((hdvd u).2 h) hu)
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.C (PadicInt.toZMod a) * Polynomial.X ^ 2)
    (g := Polynomial.C (PadicInt.toZMod b) * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X +
      Polynomial.C (PadicInt.toZMod c))
    (by rw [Polynomial.degree_C_mul_X_pow 2 (nz a ha)]; rfl)
    (Polynomial.degree_quadratic (nz b hb)) hodd
  refine ⟨(s.val : ℤ_[p]), (t.val : ℤ_[p]), 1, ?_, ?_⟩
  · rintro ⟨-, -, h⟩
    exact PadicInt.p_nonunit (isUnit_of_dvd_one h)
  · rw [hdvd]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, zero_mul, add_zero] at hst
    simp only [map_add, map_mul, map_pow, map_natCast, ZMod.natCast_zmod_val, map_one, one_pow, mul_one]
    linear_combination hst

/-- **Cassels, Ch. 8, Example 6 (ii)** (p. 126): *let $p \ne 2$ and suppose that $\Lambda$ is (classically) maximal.
Then $\Lambda$ has a basis $\vec b_1, \dots, \vec b_n$ such that $\varphi(\sum x_j\vec b_j) = \sum c_jx_j^{2}$ where
$|c_j| = 1$ or $p^{-1}$ for all $j$ and $|c_j| = p^{-1}$ for at most two values of $j$.* Here the basis is
`b : Basis (Fin (finrank ℤ_[p] Λ)) ℤ_[p] Λ` (indices $0, \dots, n-1$), "$\varphi(\sum x_j\vec b_j) = \sum c_jx_j^{2}$"
is orthogonality $\varphi(\vec b_i, \vec b_j) = 0$ ($i \ne j$) with $c_j = \varphi(\vec b_j)$, and $|\cdot|$ is the
$p$-adic norm. -/
@[kb "cassels1978" "Ch. 8, Ex. 6 (ii), p. 126"]
theorem exists_basis_of_isClassMaximal (hp2 : p ≠ 2) {Q : QuadraticForm ℚ_[p] V}
    (hV : (QuadraticMap.associated Q).Nondegenerate) {Λ : Submodule ℤ_[p] V} (hΛ : IsClassMaximal Q Λ) :
    ∃ b : Module.Basis (Fin (Module.finrank ℤ_[p] Λ)) ℤ_[p] Λ,
      (∀ i j, i ≠ j → OMeara.bil Q (b i : V) (b j : V) = 0) ∧
      (∀ j, ‖Q (b j : V)‖ = 1 ∨ ‖Q (b j : V)‖ = (p : ℝ)⁻¹) ∧
      (Finset.univ.filter fun j => ‖Q (b j : V)‖ = (p : ℝ)⁻¹).card ≤ 2 := by
  have h2 : IsUnit (2 : ℤ_[p]) := by
    have : IsUnit ((2 : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.2
      (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2))
    simpa using this
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨b, horth, hQ0⟩ := exists_orthogonal_basis Q h2 hΛ.1.fg (isRegular_of_lattice_max Q hV hΛ.1)
  have hint : ∀ j, ∃ r : ℤ_[p], Q (b j : V) = algebraMap ℤ_[p] ℚ_[p] r := by
    intro j
    have := hΛ.2.1 (bil_mem_scale Q (b j).2 (b j).2)
    rw [OMeara.bil_self] at this
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp this
    exact ⟨r, hr.symm⟩
  choose r hr using hint
  have hr0 : ∀ j, r j ≠ 0 := by
    intro j h
    apply hQ0 j
    rw [hr j, h, map_zero]
  have hnorm : ∀ j, ‖Q (b j : V)‖ = ‖r j‖ := fun j => by
    rw [hr j, PadicInt.algebraMap_apply, PadicInt.norm_coe]
  have hnotC : ∀ j s, r j ≠ (p : ℤ_[p]) ^ 2 * s := by
    intro j s hs
    have hdvd := dvd_of_integral_ext hΛ b horth (fun k => if k = j then 1 else 0) ?_ ?_ j
    · simp only [if_true] at hdvd
      exact PadicInt.p_nonunit (isUnit_of_dvd_one hdvd)
    · intro k
      by_cases hk : k = j
      · subst hk
        simp only [if_true, map_one, mul_one]
        refine Submodule.mem_one.mpr ⟨p * s, ?_⟩
        rw [hr k, hs]
        simp only [map_mul, map_pow, map_natCast]
        field_simp
      · simp [hk]
    · rw [Finset.sum_eq_single j]
      · simp only [if_true, map_one, one_pow, one_mul]
        refine Submodule.mem_one.mpr ⟨s, ?_⟩
        rw [hr j, hs]
        simp only [map_mul, map_pow, map_natCast]
        field_simp
      · intro k _ hk
        simp [hk]
      · simp
  have hcase : ∀ j, ‖r j‖ = 1 ∨ ‖r j‖ = (p : ℝ)⁻¹ := by
    intro j
    rcases classify_padic (hr0 j) with h | ⟨u, hu, h⟩ | ⟨s, h⟩
    · exact Or.inl (PadicInt.isUnit_iff.1 h)
    · right
      rw [h, norm_mul, PadicInt.norm_p, PadicInt.isUnit_iff.1 hu, mul_one]
    · exact absurd h (hnotC j s)
  refine ⟨b, horth, fun j => by rw [hnorm]; exact hcase j, ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp hlt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hk
  have hform : ∀ m, ‖Q (b m : V)‖ = (p : ℝ)⁻¹ → ∃ u : ℤ_[p], IsUnit u ∧ r m = p * u := by
    intro m hm
    rcases classify_padic (hr0 m) with h | ⟨u, hu, h⟩ | ⟨s, h⟩
    · exfalso
      rw [hnorm, PadicInt.isUnit_iff.1 h] at hm
      have h1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
      have := inv_lt_one_of_one_lt₀ h1
      linarith
    · exact ⟨u, hu, h⟩
    · exact absurd h (hnotC m s)
  obtain ⟨ui, hui, hri⟩ := hform i hi
  obtain ⟨uj, huj, hrj⟩ := hform j hj
  obtain ⟨uk, huk, hrk⟩ := hform k hk
  obtain ⟨X, Y, Z, hXYZ, t, ht⟩ := ternary_zero_padic hp2 hui huj huk
  have key : ∀ (m : Fin (Module.finrank ℤ_[p] Λ)) (u X' : ℤ_[p]), r m = p * u →
      (p : ℚ_[p])⁻¹ * algebraMap ℤ_[p] ℚ_[p] X' * Q (b m : V) ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
    intro m u X' h
    refine Submodule.mem_one.mpr ⟨X' * u, ?_⟩
    rw [hr m, h]
    simp only [map_mul, map_natCast]
    field_simp
  let x : Fin (Module.finrank ℤ_[p] Λ) → ℤ_[p] :=
    fun m => if m = i then X else if m = j then Y else if m = k then Z else 0
  have hxi : x i = X := by simp [x]
  have hxj : x j = Y := by simp [x, hij.symm]
  have hxk : x k = Z := by simp [x, hik.symm, hjk.symm]
  have hsum : ∑ m, (algebraMap ℤ_[p] ℚ_[p] (x m)) ^ 2 * Q (b m : V) =
      (algebraMap ℤ_[p] ℚ_[p] X) ^ 2 * Q (b i : V) + (algebraMap ℤ_[p] ℚ_[p] Y) ^ 2 * Q (b j : V) +
        (algebraMap ℤ_[p] ℚ_[p] Z) ^ 2 * Q (b k : V) := by
    rw [← Finset.sum_subset (Finset.subset_univ {i, j, k}) ?_]
    · rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]), Finset.sum_singleton,
        hxi, hxj, hxk]
      ring
    · intro m _ hm
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      simp [x, hm.1, hm.2.1, hm.2.2]
  have hdvd := dvd_of_integral_ext hΛ b horth x ?_ ?_
  · exact hXYZ ⟨hxi ▸ hdvd i, hxj ▸ hdvd j, hxk ▸ hdvd k⟩
  · intro m
    by_cases hmi : m = i
    · subst hmi; rw [hxi]; exact key m ui X hri
    by_cases hmj : m = j
    · subst hmj; rw [hxj]; exact key m uj Y hrj
    by_cases hmk : m = k
    · subst hmk; rw [hxk]; exact key m uk Z hrk
    simp [x, hmi, hmj, hmk]
  · rw [hsum, hr i, hr j, hr k, hri, hrj, hrk]
    refine Submodule.mem_one.mpr ⟨t, ?_⟩
    have ht' := congrArg (algebraMap ℤ_[p] ℚ_[p]) ht
    simp only [map_add, map_mul, map_pow, map_natCast] at ht' ⊢
    field_simp
    linear_combination (-1 : ℚ_[p]) * ht'

/-- **Cassels, Ch. 8, Example 7 (ii)** (p. 126): Example 6 (ii) with the non-classical definition of integrality
($\varphi(\vec c) \in \mathbb Z_p$ for $\vec c \in \Lambda$): for $p \ne 2$ an O'Meara $\mathfrak o$-maximal lattice
(`OMeara.IsMaximal Q 1 Λ`) has a basis with $\varphi(\sum x_j\vec b_j) = \sum c_jx_j^{2}$, $|c_j| \in \{1, p^{-1}\}$,
and $|c_j| = p^{-1}$ for at most two $j$. -/
@[kb "cassels1978" "Ch. 8, Ex. 7 (ii), p. 126 (p ≠ 2)"]
theorem exists_basis_of_isMaximal (hp2 : p ≠ 2) {Q : QuadraticForm ℚ_[p] V}
    (hV : (QuadraticMap.associated Q).Nondegenerate) {Λ : Submodule ℤ_[p] V} (hΛ : IsMaximal Q 1 Λ) :
    ∃ b : Module.Basis (Fin (Module.finrank ℤ_[p] Λ)) ℤ_[p] Λ,
      (∀ i j, i ≠ j → OMeara.bil Q (b i : V) (b j : V) = 0) ∧
      (∀ j, ‖Q (b j : V)‖ = 1 ∨ ‖Q (b j : V)‖ = (p : ℝ)⁻¹) ∧
      (Finset.univ.filter fun j => ‖Q (b j : V)‖ = (p : ℝ)⁻¹).card ≤ 2 :=
  exists_basis_of_isClassMaximal hp2 hV ((isClassMaximal_iff_isMaximal hp2 Q Λ).2 hΛ)

end QuadFormsKB.Cassels
