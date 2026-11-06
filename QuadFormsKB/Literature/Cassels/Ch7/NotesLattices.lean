/-
# Cassels, Chapter 7, Notes: two notions of lattice over a ring that is not a principal ideal domain

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 7, Notes, pp. 109–110.

**Setting.** $I$ is an integral domain with field of fractions $k$ and $V$ is a finite-dimensional $k$-vector space.
Cassels' definition (2.1) calls $\Lambda \subseteq V$ a lattice when it is a *free* $I$-module spanning $V$ over $k$,
i.e. $\Lambda = \{r_0 b_0 + \cdots + r_{n-1} b_{n-1} : r_j \in I\}$ for a $k$-basis $b_0, \dots, b_{n-1}$ of $V$
(sense (i)). The Notes point out the second notion: any finitely generated $I$-submodule of $V$ spanning $V$
(sense (ii)). Indices are 0-based here (Cassels' $b_1, \dots, b_n$ are `b 0`, …, `b (n-1)`).

**Proves**
* `exists_basis_of_fg_span` and `fg_span_of_basis` (p. 109): for $I$ a principal ideal domain the two senses agree.
* `not_free_of_not_isPrincipal` and `fg_ideal_spans` (p. 109): for a non-principal ideal $J$ of $I$, the set
  $\{s b_0 : s \in J\}$ is not a lattice in sense (i) (it is not even a free module), but it is one in sense (ii)
  when $J$ is finitely generated.
* `printed_example_splits` (p. 110): the counter-example at the end of §4 (the singular form
  $\{(1 + 2\sqrt{-5})x_0 + 3x_1\}^2$ over $\mathbb Z[\sqrt{-5}]$, which is not equivalent to a form in one variable)
  disappears for lattices in sense (ii): $\mathbb Z[\sqrt{-5}]^2$ splits as the radical plus a sublattice $\Lambda_1$ on
  which the form is regular, but $\Lambda_1$ is *not free* (it is isomorphic to the non-principal ideal
  $(3, 1 + 2\sqrt{-5})$), so the splitting is available only in sense (ii).

**Reconstructed.** The scan of the printed formula is partly illegible; the form
$\{(1+2\sqrt{-5})x_0 + 3x_1\}^2$ is as transcribed from the page images, and the complement $\Lambda_1$
is an explicit choice (the book does not give one).
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

section PID

variable {I k V : Type*} [CommRing I] [IsDomain I] [IsPrincipalIdealRing I] [Field k] [Algebra I k]
  [IsFractionRing I k] [AddCommGroup V] [Module k V] [Module I V] [IsScalarTower I k V]

/-- Helper: $V$ has no $I$-torsion when $I$ embeds in $k$ and $V$ is a $k$-vector space. -/
theorem noZeroSMulDivisors_of_isFractionRing (I k V : Type*) [CommRing I] [Field k] [Algebra I k]
    [IsFractionRing I k] [AddCommGroup V] [Module k V] [Module I V] [IsScalarTower I k V] :
    NoZeroSMulDivisors I V := by
  have hinj : Function.Injective (algebraMap I k) := IsFractionRing.injective I k
  refine ⟨fun {c x} h => ?_⟩
  rw [← algebraMap_smul k c x, smul_eq_zero] at h
  rcases h with h | h
  · left; exact hinj (by rw [h, map_zero])
  · right; exact h

/-- **Cassels, Ch. 7, Notes, p. 109**: *when $I$ is a principal ideal domain, lattices in sense (ii) are lattices in
sense (i).* Let $I$ be a principal ideal domain with field of fractions $k$ (`k`, with `IsFractionRing I k`), let $V$
be a finite-dimensional $k$-vector space that is also an $I$-module compatibly (`IsScalarTower I k V`), and let
$\Lambda$ (`Λ`) be a finitely generated $I$-submodule of $V$ spanning $V$ over $k$. Then there is a $k$-basis
$b_0, \dots, b_{n-1}$ of $V$ (`b`, with $n = \dim_k V$ `= Module.finrank k V`) such that
$\Lambda = I b_0 + \cdots + I b_{n-1}$. -/
@[kb "cassels1978" "Ch. 7, Notes, p. 109 (for I a principal ideal domain, lattices in sense (ii) are lattices in sense (i))"]
theorem exists_basis_of_fg_span [FiniteDimensional k V] (Λ : Submodule I V) (hfg : Λ.FG)
    (hspan : Submodule.span k (Λ : Set V) = ⊤) :
    ∃ b : Fin (Module.finrank k V) → V, LinearIndependent k b ∧
      Λ = Submodule.span I (Set.range b) := by
  have : NoZeroSMulDivisors I V := noZeroSMulDivisors_of_isFractionRing I k V
  have : Module.Finite I Λ := Module.Finite.iff_fg.mpr hfg
  have : Module.Free I Λ := Module.free_of_finite_type_torsion_free'
  let bΛ := Module.finBasis I Λ
  let b' : Fin (Module.finrank I Λ) → V := fun i => (bΛ i : V)
  have hlI : LinearIndependent I b' :=
    bΛ.linearIndependent.map' Λ.subtype (LinearMap.ker_eq_bot.mpr Λ.injective_subtype)
  have hlk : LinearIndependent k b' := (LinearIndependent.iff_fractionRing I k).mp hlI
  have hΛ : Λ = Submodule.span I (Set.range b') := by
    have h1 : Submodule.span I (Set.range b') = Submodule.map Λ.subtype (Submodule.span I (Set.range bΛ)) := by
      rw [Submodule.map_span, ← Set.range_comp]; rfl
    rw [h1, bΛ.span_eq, Submodule.map_subtype_top]
  have hspan' : Submodule.span k (Set.range b') = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.mpr fun x hx => ?_
    have : x ∈ Submodule.span I (Set.range b') := by rw [← hΛ]; exact hx
    exact (Submodule.span_subset_span I k _) this
  let B : Module.Basis (Fin (Module.finrank I Λ)) k V := Module.Basis.mk hlk hspan'.ge
  have hcard : Module.finrank k V = Module.finrank I Λ := by
    simpa using Module.finrank_eq_card_basis B
  refine ⟨b' ∘ finCongr hcard, ?_, ?_⟩
  · exact hlk.comp _ (finCongr hcard).injective
  · rw [Function.Surjective.range_comp (finCongr hcard).surjective]
    exact hΛ

end PID

/-- **Cassels, Ch. 7, Notes, p. 109**: *a lattice in sense (i) is one in sense (ii).* If $b_0, \dots, b_{n-1}$ (`b`)
is a $k$-basis of $V$ (a $k$-linearly independent family indexed by $\mathrm{Fin}\ n$ with $n = \dim_k V$) and
$\Lambda = I b_0 + \cdots + I b_{n-1}$, then $\Lambda$ is a finitely generated $I$-module spanning $V$ over $k$. Here
$I$ is any commutative ring and $k$ an $I$-algebra (no principal ideal hypothesis is needed). -/
@[kb "cassels1978" "Ch. 7, Notes, p. 109 (a lattice in sense (i) is a lattice in sense (ii); converse of the previous)"]
theorem fg_span_of_basis {I k V : Type*} [CommRing I] [Field k] [Algebra I k] [AddCommGroup V] [Module k V]
    [Module I V] [IsScalarTower I k V] [FiniteDimensional k V] (b : Fin (Module.finrank k V) → V)
    (hb : LinearIndependent k b) (Λ : Submodule I V) (hΛ : Λ = Submodule.span I (Set.range b)) :
    Λ.FG ∧ Submodule.span k (Λ : Set V) = ⊤ := by
  classical
  subst hΛ
  refine ⟨⟨(Finset.univ.image b), ?_⟩, ?_⟩
  · simp
  · have hB := hb.span_eq_top_of_card_eq_finrank' (by simp)
    rw [eq_top_iff, ← hB]
    exact Submodule.span_mono (Submodule.subset_span)

/-- **Cassels, Ch. 7, Notes, p. 109**: *a non-principal ideal is not a lattice in sense (i).* Let $I$ be an integral
domain and $J$ (`J`) an ideal of $I$ that is not principal. Then $J$, as an $I$-module, is not free; so
$\{s b_0 : s \in J\}$ is not a lattice in sense (i) (the case $n = 1$). The reason: for $x, y \in J$ one has
$y \cdot x - x \cdot y = 0$, so a basis has at most one element, and then $J$ is generated by it. -/
@[kb "cassels1978" "Ch. 7, Notes, p. 109 (a non-principal ideal is not a lattice in sense (i))"]
theorem not_free_of_not_isPrincipal {I : Type*} [CommRing I] [IsDomain I] (J : Ideal I)
    (hJ : ¬ J.IsPrincipal) : ¬ Module.Free I J := by
  intro hfree
  let b := Module.Free.chooseBasis I J
  have hsub : Subsingleton (Module.Free.ChooseBasisIndex I J) := by
    refine ⟨fun i j => ?_⟩
    by_contra hij
    have hji : ¬ j = i := fun h => hij h.symm
    have hne : ((b j : J) : I) ≠ 0 := fun h => b.ne_zero j (Subtype.ext h)
    have h0 : ((b j : J) : I) • b i - ((b i : J) : I) • b j = 0 := by
      apply Subtype.ext
      simp [smul_eq_mul, mul_comm]
    have := congrArg (fun z => b.repr z i) h0
    simp [hji] at this
    exact hne (congrArg Subtype.val this)
  have hmap : ∀ s : Set J, Submodule.map J.subtype (Submodule.span I s) = Submodule.span I (J.subtype '' s) :=
    fun s => Submodule.map_span _ _
  have htop : Submodule.map J.subtype (Submodule.span I (Set.range b)) = J := by
    rw [b.span_eq, Submodule.map_subtype_top]
  by_cases hne : Nonempty (Module.Free.ChooseBasisIndex I J)
  · obtain ⟨i⟩ := hne
    apply hJ
    refine ⟨⟨(b i : I), ?_⟩⟩
    have hr : Set.range b = {b i} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; rw [Subsingleton.elim j i]
      · rintro rfl; exact ⟨i, rfl⟩
    refine htop.symm.trans ?_
    rw [hr, hmap]
    simp
  · rw [not_nonempty_iff] at hne
    apply hJ
    refine ⟨⟨0, ?_⟩⟩
    refine htop.symm.trans ?_
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.map_bot]
    simp

/-- **Cassels, Ch. 7, Notes, p. 109**: *a non-zero ideal $J$ spans the field of fractions, so is a lattice in sense (ii)
when finitely generated.* Let $I$ be an integral domain with field of fractions $k$ (`IsFractionRing I k`) and $J$
(`J`) a non-zero ideal. Then the image $\{s \cdot 1 : s \in J\}$ of $J$ in the one-dimensional $k$-vector space $k$
(basis $b_0 = 1$) spans $k$ over $k$; and the $I$-submodule it forms is finitely generated whenever $J$ is. So for $J$
finitely generated this is a lattice in sense (ii) in $V = k$. (Finite generation of the image is the second
conjunct, `J.FG → ...`.) -/
@[kb "cassels1978" "Ch. 7, Notes, p. 109 (...but it is a lattice in sense (ii) if J is finitely generated)"]
theorem fg_ideal_spans {I k : Type*} [CommRing I] [IsDomain I] [Field k] [Algebra I k] [IsFractionRing I k]
    (J : Ideal I) (hJ : J ≠ ⊥) :
    Submodule.span k (Submodule.map (Algebra.linearMap I k) J : Set k) = ⊤ ∧
      (J.FG → (Submodule.map (Algebra.linearMap I k) J).FG) := by
  refine ⟨?_, fun h => Submodule.FG.map _ h⟩
  obtain ⟨a, haJ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hA : algebraMap I k a ≠ 0 := fun h => ha0 (IsFractionRing.injective I k (by rw [h, map_zero]))
  rw [eq_top_iff]
  intro x _
  have hmem : algebraMap I k a ∈ Submodule.span k (Submodule.map (Algebra.linearMap I k) J : Set k) :=
    Submodule.subset_span ⟨a, haJ, rfl⟩
  have := Submodule.smul_mem _ (x * (algebraMap I k a)⁻¹) hmem
  rwa [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hA, mul_one] at this

/-! ### The counter-example of §4 over $\mathbb Z[\sqrt{-5}]$ (p. 110) -/

section Example

/-- Helper: $\mathbb Z[\sqrt{-5}]$ is an integral domain (Mathlib has the instance only for $d \in \mathbb N$ not a
square, not for negative $d$). The proof uses that the norm is multiplicative and vanishes only at $0$. -/
instance isDomain_zsqrtd_neg_five : IsDomain (ℤ√(-5)) :=
  have : NoZeroDivisors (ℤ√(-5)) := ⟨fun {a b} h => by
    have h1 := congrArg Zsqrtd.norm h
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (by norm_num) a).mp h2)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (by norm_num) b).mp h2)⟩
  NoZeroDivisors.to_isDomain _

/-- The linear form $\ell(x_0, x_1) = (1 + 2\sqrt{-5})x_0 + 3x_1$ on $R^2$, $R = \mathbb Z[\sqrt{-5}]$ (`ℤ√(-5)`),
whose square $\varphi(x, y) = \ell(x)\ell(y)$ is the singular form of the counter-example at the end of Cassels'
§4 (Ch. 7, p. 109; the scan of the printed formula is partly illegible and this is the transcription from the page
images). Here $\sqrt{-5}$ is `⟨0, 1⟩` and $1 + 2\sqrt{-5}$ is `⟨1, 2⟩`. -/
def noteForm : (Fin 2 → ℤ√(-5)) →ₗ[ℤ√(-5)] ℤ√(-5) :=
  (⟨1, 2⟩ : ℤ√(-5)) • LinearMap.proj 0 + (3 : ℤ√(-5)) • LinearMap.proj 1

/-- Helper: the value of `noteForm`. -/
@[simp] theorem noteForm_apply (x : Fin 2 → ℤ√(-5)) : noteForm x = ⟨1, 2⟩ * x 0 + 3 * x 1 := by
  simp [noteForm]

/-- The first generator $(7,\ -2 - 4\sqrt{-5})$ of the complement $\Lambda_1$ below. -/
def noteVec0 : Fin 2 → ℤ√(-5) := ![7, ⟨-2, -4⟩]

/-- The second generator $(1 - 2\sqrt{-5},\ -6)$ of the complement $\Lambda_1$ below. -/
def noteVec1 : Fin 2 → ℤ√(-5) := ![⟨1, -2⟩, -6]

/-- The sublattice $\Lambda_1 = R\,(7, -2 - 4\sqrt{-5}) + R\,(1 - 2\sqrt{-5}, -6)$ of $R^2$, $R = \mathbb Z[\sqrt{-5}]$:
a complement of the radical $\ker \ell$ on which the form is regular. It is an explicit choice (the book gives none),
found from the projection $\pi(x) = x_0 v_0 + x_1 v_1$ with $\ell \circ \pi = \ell$ (`noteForm_comb`). -/
def noteLat : Submodule (ℤ√(-5)) (Fin 2 → ℤ√(-5)) :=
  Submodule.span (ℤ√(-5)) {noteVec0, noteVec1}

/-- Helper: $\ell(c_0 v_0 + c_1 v_1) = c_0(1 + 2\sqrt{-5}) + 3c_1$ (`ℓ v₀ = 1 + 2√−5`, `ℓ v₁ = 3`). -/
theorem noteForm_comb (c0 c1 : ℤ√(-5)) :
    noteForm (c0 • noteVec0 + c1 • noteVec1) = c0 * ⟨1, 2⟩ + c1 * 3 := by
  simp only [noteForm_apply, noteVec0, noteVec1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Zsqrtd.ext <;> simp <;> ring

/-- Helper: $3\,x = \ell(x)\, v_1$ for $x = c_0 v_0 + c_1 v_1$ in $\Lambda_1$. -/
theorem note_three_smul (c0 c1 : ℤ√(-5)) :
    (3 : ℤ√(-5)) • (c0 • noteVec0 + c1 • noteVec1) = noteForm (c0 • noteVec0 + c1 • noteVec1) • noteVec1 := by
  rw [noteForm_comb]
  funext i
  fin_cases i <;> (apply Zsqrtd.ext <;> simp [noteVec0, noteVec1] <;> ring)

/-- Helper: membership in `noteLat`. -/
theorem mem_noteLat {x : Fin 2 → ℤ√(-5)} :
    x ∈ noteLat ↔ ∃ c0 c1 : ℤ√(-5), c0 • noteVec0 + c1 • noteVec1 = x :=
  Submodule.mem_span_pair

/-- Helper: `ℓ` has trivial kernel on `noteLat`. -/
theorem noteForm_eq_zero_of_mem {x : Fin 2 → ℤ√(-5)} (hx : x ∈ noteLat) (h : noteForm x = 0) : x = 0 := by
  obtain ⟨c0, c1, rfl⟩ := mem_noteLat.mp hx
  have := note_three_smul c0 c1
  rw [h, zero_smul] at this
  exact (smul_eq_zero.mp this).resolve_left (by
    intro h3
    have := congrArg Zsqrtd.re h3
    simp at this)

/-- Helper: $\ell(\Lambda_1)$ is the ideal $(3, 1 + 2\sqrt{-5})$. -/
theorem map_noteForm_noteLat :
    Submodule.map noteForm noteLat = Ideal.span {(3 : ℤ√(-5)), ⟨1, 2⟩} := by
  rw [noteLat, Submodule.map_span, Set.image_pair, Set.pair_comm]
  have h0 : noteForm noteVec0 = ⟨1, 2⟩ := by
    have := noteForm_comb 1 0
    simpa using this
  have h1 : noteForm noteVec1 = 3 := by
    have := noteForm_comb 0 1
    simpa using this
  rw [h0, h1]

/-- Helper: the ideal $(3, 1 + 2\sqrt{-5})$ of $\mathbb Z[\sqrt{-5}]$ is not principal. A generator $g$ would have
norm dividing $\gcd(9, 21) = 3$, while every element of the ideal has $\mathrm{re} + \mathrm{im} \equiv 0 \pmod 3$,
hence norm divisible by $3$; so the norm would be $3$, but $a^2 + 5b^2 = 3$ has no integer solution. -/
theorem not_isPrincipal_note_ideal : ¬ (Ideal.span {(3 : ℤ√(-5)), ⟨1, 2⟩}).IsPrincipal := by
  rintro ⟨⟨g, hg⟩⟩
  have h3 : (3 : ℤ√(-5)) ∈ Submodule.span (ℤ√(-5)) {g} := by rw [← hg]; exact Ideal.subset_span (by simp)
  have ha : (⟨1, 2⟩ : ℤ√(-5)) ∈ Submodule.span (ℤ√(-5)) {g} := by
    rw [← hg]; exact Ideal.subset_span (by simp)
  have hgJ : g ∈ Ideal.span {(3 : ℤ√(-5)), ⟨1, 2⟩} := by rw [hg]; exact Submodule.mem_span_singleton_self g
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp h3
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp ha
  rw [smul_eq_mul, mul_comm] at hu hw
  have e3 : (3 : ℤ√(-5)).norm = 9 := by simp [Zsqrtd.norm_def]
  have ea : (⟨1, 2⟩ : ℤ√(-5)).norm = 21 := by simp [Zsqrtd.norm_def]
  have n1 : g.norm ∣ 9 := by
    have : g.norm ∣ (3 : ℤ√(-5)).norm := by rw [← hu, Zsqrtd.norm_mul]; exact dvd_mul_right _ _
    rwa [e3] at this
  have n2 : g.norm ∣ 21 := by
    have : g.norm ∣ (⟨1, 2⟩ : ℤ√(-5)).norm := by rw [← hw, Zsqrtd.norm_mul]; exact dvd_mul_right _ _
    rwa [ea] at this
  have n3 : g.norm ∣ 3 := by
    have := dvd_sub n2 (dvd_mul_of_dvd_right n1 2)
    norm_num at this
    exact this
  obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.mp hgJ
  have hre : g.re = p.re * 3 + (q.re - 10 * q.im) := by
    rw [← hpq]; simp; ring
  have him : g.im = p.im * 3 + (2 * q.re + q.im) := by
    rw [← hpq]; simp; ring
  have hN : g.norm = g.re * g.re + 5 * g.im * g.im := by
    simp [Zsqrtd.norm_def]
  have hk : ∃ k, g.re = -g.im + 3 * k := ⟨(g.re + g.im) / 3, by omega⟩
  obtain ⟨k, hk⟩ := hk
  have h3N : (3 : ℤ) ∣ g.norm := ⟨3 * k * k - 2 * k * g.im + 2 * g.im * g.im, by rw [hN, hk]; ring⟩
  have hnn : 0 ≤ g.norm := by rw [hN]; nlinarith [mul_self_nonneg g.re, mul_self_nonneg g.im]
  have hle := Int.le_of_dvd (by norm_num) n3
  have hg3 : g.norm = 3 := by
    obtain ⟨m, hm⟩ := h3N
    rcases (show m = 0 ∨ m = 1 by omega) with h | h
    · rw [h, mul_zero] at hm; rw [hm] at n3; simp at n3
    · rw [hm, h]; norm_num
  rw [hN] at hg3
  by_cases hy : g.im = 0
  · rw [hy] at hg3
    rcases (show g.re ≤ -2 ∨ (-1 ≤ g.re ∧ g.re ≤ 1) ∨ 2 ≤ g.re by omega) with h | h | h <;> nlinarith
  · nlinarith [mul_self_pos.mpr hy, mul_self_nonneg g.re]

/-- **Cassels, Ch. 7, Notes, p. 110**: *the counter-example at the end of §4 evaporates in the context of lattices in
sense (ii).* Let $R = \mathbb Z[\sqrt{-5}]$ (`ℤ√(-5)`), $\ell(x) = (1 + 2\sqrt{-5})x_0 + 3x_1$ (`noteForm`; the singular
form is $\varphi(x, y) = \ell(x)\ell(y)$, i.e. $\{(1 + 2\sqrt{-5})x_0 + 3x_1\}^2$ on $R^2$) and
$\Lambda_1$ (`noteLat`) $= R\,(7, -2 - 4\sqrt{-5}) + R\,(1 - 2\sqrt{-5}, -6)$. Then, with $x \in R^2$ arbitrary:
(a) $x \in \ker \ell$ (the radical of $\varphi$) iff $\ell(x)\ell(y) = 0$ for all $y$;
(b) $R^2 = \ker \ell \oplus \Lambda_1$ (`IsCompl`);
(c) $\ell$ is injective on $\Lambda_1$, so $\varphi$ restricted to $\Lambda_1$ is regular (indeed anisotropic:
$\varphi(x,x) = \ell(x)^2 \ne 0$ for $x \ne 0$);
(d) $\Lambda_1$ is *not* a free $R$-module (it is isomorphic to $\ell(\Lambda_1) = (3, 1 + 2\sqrt{-5})$, a
non-principal ideal; `not_free_of_not_isPrincipal`), so the splitting exists for lattices in sense (ii) but not
(i), consistent with the non-equivalence to a form in one variable. The complement $\Lambda_1$ is a choice of ours;
the book only states the evaporation. -/
@[kb "cassels1978" "Ch. 7, Notes, p. 110 (the counter-example of §4 evaporates for lattices in sense (ii); explicit splitting reconstructed)"]
theorem printed_example_splits :
    (∀ x : Fin 2 → ℤ√(-5), x ∈ LinearMap.ker noteForm ↔ ∀ y, noteForm x * noteForm y = 0) ∧
    IsCompl (LinearMap.ker noteForm) noteLat ∧
    Function.Injective (noteForm.domRestrict noteLat) ∧
    ¬ Module.Free (ℤ√(-5)) noteLat := by
  have hinj : Function.Injective (noteForm.domRestrict noteLat) := by
    intro x y h
    apply Subtype.ext
    have hxy : ((x : Fin 2 → ℤ√(-5)) - y) ∈ noteLat := noteLat.sub_mem x.2 y.2
    have := noteForm_eq_zero_of_mem hxy (by
      rw [map_sub]
      exact sub_eq_zero.mpr h)
    exact sub_eq_zero.mp this
  refine ⟨?_, ?_, hinj, ?_⟩
  · intro x
    refine ⟨fun h y => by rw [LinearMap.mem_ker.mp h, zero_mul], fun h => ?_⟩
    have h1 := h ![1, 0]
    have hl : noteForm ![1, 0] = ⟨1, 2⟩ := by simp
    have hne : (⟨1, 2⟩ : ℤ√(-5)) ≠ 0 := fun h0 => by simpa using congrArg Zsqrtd.re h0
    rw [hl] at h1
    exact LinearMap.mem_ker.mpr ((mul_eq_zero.mp h1).resolve_right hne)
  · constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      exact noteForm_eq_zero_of_mem hx' (LinearMap.mem_ker.mp hx)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      have hmem : x 0 • noteVec0 + x 1 • noteVec1 ∈ noteLat := mem_noteLat.mpr ⟨_, _, rfl⟩
      refine ⟨x - (x 0 • noteVec0 + x 1 • noteVec1), ?_, _, hmem, by abel⟩
      rw [LinearMap.mem_ker, map_sub, noteForm_comb, noteForm_apply]
      ring
  · intro hfree
    have hrange : LinearMap.range (noteForm.domRestrict noteLat) =
        Ideal.span {(3 : ℤ√(-5)), ⟨1, 2⟩} := by
      rw [LinearMap.range_domRestrict]; exact map_noteForm_noteLat
    let e : noteLat ≃ₗ[ℤ√(-5)] Ideal.span {(3 : ℤ√(-5)), ⟨1, 2⟩} :=
      (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)
    have : Module.Free (ℤ√(-5)) (Ideal.span {(3 : ℤ√(-5)), ⟨1, 2⟩}) := Module.Free.of_equiv e
    exact not_free_of_not_isPrincipal _ not_isPrincipal_note_ideal this

end Example

end QuadFormsKB.Cassels
