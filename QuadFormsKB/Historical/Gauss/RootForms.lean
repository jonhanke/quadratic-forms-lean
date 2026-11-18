import QuadFormsKB.Historical.Gauss.Opposite

/-!
# Primitive representations and the forms $(M, N, (N^2 - D)/M)$ (*Disquisitiones Arithmeticae*, Arts. 168-170, 224)

Three statements from the historical sources and one recorded loose end. Throughout, Gauss's $(a, b, c)$ is `gaussForm a b c`, i.e.
$a x^2 + 2 b x y + c y^2$, with determinant $D = b^2 - a c$ (`gaussDet`). A primitive (proper) representation of $M$
is $(m, n)$ with $\gcd(m, n) = 1$ and $(a, b, c)(m, n) = M$; with a Bezout pair $\mu m + \nu n = 1$ its value is
$N = \mu (m b + n c) - \nu (m a + n b)$ (`art155Value`), and `primitiveRepresentationValues a b c M` is the set of all
such values.

* **Art. 168** (the key lemma; used by all items below): the proper substitution $(m, -\nu; n, \mu)$ carries $(a, b, c)$ to
  $(M, N, L)$ with $M L = N^2 - D$ (`art168_sLEquiv`, `art168_proper_transformation`), and conversely the first column
  of a proper transformation of $(a, b, c)$ into $(M, N, L)$ is a primitive representation of $M$ with value $N$
  (`art168_firstColumn`). All proved for arbitrary integers (no sign condition on $M$ or $D$ except $M \ne 0$ where
  a quotient by $M$ is written).
* **Arts. 168-169**, proved: `art168_mem_values_iff` (for $M \ne 0$: $N$ is a value of a
  primitive representation of $M$ iff $M \mid N^2 - D$ and $(a, b, c)$ is properly equivalent to
  $(M, N, (N^2 - D)/M)$), `art168_dvd_of_mem_values` ("possible only if $D$ is a square modulo $M$").
  Differences from the historical sources: they have $M > 0$, determinant $-D < 0$ and representatives $|N| \le M/2$; here $M$
  is any nonzero integer, $D$ any integer, and $N$ any integer (the set of values is a union of residue classes modulo
  $M$, `mem_values_of_modEq`, so "belongs to the class of $N$" is the same as "$N$ is a value").
* **Art. 224, converse clause** (a recorded loose end), proved: `art224_sLEquiv_of_modEq` (two
  forms of the same determinant with primitive representations of $M \ne 0$ whose values are congruent modulo $M$ are
  properly equivalent) and `art224_iff` (for forms of the same determinant that both represent $M \ne 0$
  primitively, properly equivalent iff they have a common value). Not formalized: the class-field reformulation of
  classes as roots.
* **Art. 170**: (i) proved, `art170_values_neg_of_sLEquiv_ambiguous`: if $F$ is properly
  equivalent to an ambiguous form $(a', b', c')$ with $a' \mid 2b'$ then the values of the primitive
  representations of $M$ are closed under $N \mapsto -N$. (ii) proved, `art170_converse`: values $N$ and $-N$ give
  that $F$ is properly and improperly equivalent to $(M, N, (N^2 - D)/M)$ and properly equivalent to its opposite.
  The last clause "hence $F$ is properly equivalent to an ambiguous form" needs Gauss's Art. 165 (a form properly
  equivalent to its opposite is equivalent to an ambiguous form): it is stated here as the named propositions
  `Art165AmbiguousClause` and `Art170AmbiguousClause`, with the implication `art170_ambiguousClause_of_art165`, and
  both are proved in `AmbiguousClasses.lean` (`art165_ambiguousClause`, `art170_ambiguousClause`).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-! ### Helper lemmas -/

/-- **Shifting the middle coefficient by a multiple of the first:** the substitution $x \mapsto x + k y$ carries
$(M, N, L)$ to $(M, N + k M, M k^2 + 2 N k + L)$ (a proper equivalence). -/
theorem sLEquiv_shift (M N L k : ℤ) :
    SLEquiv (gaussForm M N L) (gaussForm M (N + k * M) (M * k ^ 2 + 2 * N * k + L)) := by
  refine (sLEquiv_iff _ _).mpr ⟨1, k, 0, 1, by ring, ?_⟩
  rw [subst_gaussForm]
  congr 1 <;> ring

/-- Every integer congruent to a value of a primitive representation of $M$ is again such a value
(`exists_bezout_art155Value_eq` in terms of `primitiveRepresentationValues`). -/
theorem mem_values_of_modEq {a b c M v w : ℤ} (hv : v ∈ primitiveRepresentationValues a b c M)
    (hw : w ≡ v [ZMOD M]) : w ∈ primitiveRepresentationValues a b c M := by
  obtain ⟨m, n, μ, ν, hb, he, rfl⟩ := hv
  obtain ⟨μ', ν', hb', hv'⟩ := exists_bezout_art155Value_eq a b c m n μ ν w hb (by rw [he]; exact hw)
  exact ⟨m, n, μ', ν', hb', he, hv'⟩

/-- A primitive representation has a value: if $M$ is represented by $(a, b, c)$ with coprime variables then
`primitiveRepresentationValues a b c M` is nonempty. -/
theorem values_nonempty_of_hasPrimitiveRepresentation {a b c M : ℤ}
    (h : HasPrimitiveRepresentation (gaussForm a b c) M) :
    (primitiveRepresentationValues a b c M).Nonempty := by
  obtain ⟨m, n, hg, hM⟩ := h
  have h1 := Int.gcd_eq_gcd_ab m n
  rw [hg] at h1
  push_cast at h1
  exact ⟨_, m, n, Int.gcdA m n, Int.gcdB m n, by linarith, hM, rfl⟩

/-- Conjugation (opposite form) evaluates as $\bar f(x, y) = f(x, -y)$. -/
private theorem eval_conjForm_aux (f : BinQF) (x y : ℤ) : (conjForm f).eval x y = f.eval x (-y) := by
  simp only [eval_eq, a_conjForm, b_conjForm, c_conjForm]; ring

/-- Proper equivalence is preserved by taking opposite forms. -/
theorem sLEquiv_conjForm_conjForm {f g : BinQF} (h : SLEquiv f g) :
    SLEquiv (conjForm f) (conjForm g) := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  refine (sLEquiv_iff _ _).mpr ⟨p, -q, -r, s, by linear_combination hd, ?_⟩
  apply ext_eval
  intro x y
  rw [eval_subst, eval_conjForm_aux, eval_conjForm_aux, eval_subst]
  congr 1 <;> ring

/-! ### Art. 168: the key lemma -/

/-- **Art. 168, the key lemma** (*Disq. Arith.* Art. 168): if
$\mu m + \nu n = 1$, then the proper substitution $x = m x' - \nu y'$, $y = n x' + \mu y'$ (determinant
$m\mu + \nu n = 1$) carries $(a, b, c)$ to $(M, N, L)$, where $M = (a, b, c)(m, n)$ is the value of the form at
$(m, n)$, $N = \mu (m b + n c) - \nu (m a + n b)$ (`art155Value`) and $L = a \nu^2 - 2 b \mu \nu + c \mu^2$ is the
value of the form at $(-\nu, \mu)$. Here $M$ need not be nonzero; for $M \ne 0$ see `art168_proper_transformation`
for $L = (N^2 - D)/M$. -/
@[kb "gauss1801" "Art. 168"]
theorem art168_sLEquiv (a b c m n μ ν : ℤ) (h : μ * m + ν * n = 1) :
    SLEquiv (gaussForm a b c)
      (gaussForm ((gaussForm a b c).eval m n) (art155Value a b c m n μ ν)
        (a * ν ^ 2 - 2 * b * μ * ν + c * μ ^ 2)) := by
  refine (sLEquiv_iff _ _).mpr ⟨m, -ν, n, μ, by linear_combination h, ?_⟩
  rw [subst_gaussForm, eval_gaussForm]
  unfold art155Value
  congr 1 <;> ring

/-- **The product relation** $M L = N^2 - D$ (*Disq. Arith.* Art. 168): with $M$, $N$, $L$ as in
`art168_sLEquiv`, $M L = N^2 - (b^2 - a c)$. -/
theorem art168_mul_eq (a b c m n μ ν : ℤ) (h : μ * m + ν * n = 1) :
    (gaussForm a b c).eval m n * (a * ν ^ 2 - 2 * b * μ * ν + c * μ ^ 2) =
      (art155Value a b c m n μ ν) ^ 2 - gaussDet a b c := by
  rw [eval_gaussForm]
  have e : (a * m ^ 2 + 2 * b * m * n + c * n ^ 2) * (a * ν ^ 2 - 2 * b * μ * ν + c * μ ^ 2) =
      (art155Value a b c m n μ ν) ^ 2 - (b ^ 2 - a * c) * (μ * m + ν * n) ^ 2 := by
    unfold art155Value; ring
  rw [e, h]; unfold gaussDet; ring

/-- **Art. 168: a primitive representation gives a proper transformation into $(M, N, (N^2 - D)/M)$**
(*Disq. Arith.* Art. 168): if $(a, b, c)(m, n) = M \ne 0$ and $\mu m + \nu n = 1$, then
$M \mid N^2 - D$ and $(a, b, c)$ is properly equivalent to $(M, N, (N^2 - D)/M)$, where $D = b^2 - a c$ and
$N$ is the value `art155Value a b c m n μ ν`. Proved for arbitrary integers $a, b, c$ (no sign
condition on $D$ or $M$). -/
@[kb "gauss1801" "Art. 168"]
theorem art168_proper_transformation (a b c m n μ ν M : ℤ) (h : μ * m + ν * n = 1)
    (hM : (gaussForm a b c).eval m n = M) (hM0 : M ≠ 0) :
    M ∣ (art155Value a b c m n μ ν) ^ 2 - gaussDet a b c ∧
      SLEquiv (gaussForm a b c)
        (gaussForm M (art155Value a b c m n μ ν)
          (((art155Value a b c m n μ ν) ^ 2 - gaussDet a b c) / M)) := by
  have h1 := art168_sLEquiv a b c m n μ ν h
  have h2 := art168_mul_eq a b c m n μ ν h
  rw [hM] at h1 h2
  refine ⟨⟨_, h2.symm⟩, ?_⟩
  rw [← h2, Int.mul_ediv_cancel_left _ hM0]
  exact h1

/-- **Art. 168, converse: the first column is a primitive representation with the given value** (the historical sources; *Disq. Arith.* Art. 168): if the proper transformation $x = \alpha x' + \beta y'$,
$y = \gamma x' + \delta y'$ carries $(a, b, c)$ to $(M, N, L)$, then $(\alpha, \gamma)$ is a primitive
representation of $M$ by $(a, b, c)$, with Bezout pair $(\mu, \nu) = (\delta, -\beta)$
($\delta \alpha - \beta\gamma = 1$) and value exactly $N$. -/
@[kb "gauss1801" "Art. 168"]
theorem art168_firstColumn {a b c M N L α β γ δ : ℤ} (hdet : α * δ - β * γ = 1)
    (h : subst α β γ δ (gaussForm a b c) = gaussForm M N L) :
    δ * α + (-β) * γ = 1 ∧ Int.gcd α γ = 1 ∧ (gaussForm a b c).eval α γ = M ∧
      art155Value a b c α γ δ (-β) = N := by
  rw [subst_gaussForm] at h
  obtain ⟨h1, h2, -⟩ := gaussForm_inj h
  have hb : δ * α + (-β) * γ = 1 := by linear_combination hdet
  refine ⟨hb, Int.isCoprime_iff_gcd_eq_one.mp ⟨δ, -β, hb⟩, ?_, ?_⟩
  · rw [eval_gaussForm]; linear_combination h1
  · unfold art155Value; linear_combination h2

/-! ### Arts. 168-169: values and the forms $(M, N, (N^2 - D)/M)$ -/

/-- **A value is a square root of the determinant modulo $M$** (*Disq. Arith.*
Arts. 154-155, 168): if $N$ is the value of a primitive representation of $M$ by $(a, b, c)$ then
$M \mid N^2 - (b^2 - a c)$. So a primitive representation of $M$ is possible only if $D = b^2 - ac$ is a square
modulo $M$. -/
@[kb "gauss1801" "Art. 168"]
theorem art168_dvd_of_mem_values {a b c M N : ℤ} (hN : N ∈ primitiveRepresentationValues a b c M) :
    M ∣ N ^ 2 - gaussDet a b c := by
  obtain ⟨m, n, μ, ν, hb, he, rfl⟩ := hN
  have := art155_value_sq a b c m n μ ν hb
  rw [he] at this
  exact Int.modEq_iff_dvd.mp this.symm

/-- **Primitive representations of $M$ with value $N$ and proper equivalence to $(M, N, (N^2 - D)/M)$** (the historical sources; *Disq. Arith.* Arts. 168-169): for $M \ne 0$ and any integer $N$, the integer $N$ is a value of a
primitive representation of $M$ by $(a, b, c)$ (`primitiveRepresentationValues`) iff $M \mid N^2 - D$ and
$(a, b, c)$ is properly equivalent to $(M, N, (N^2 - D)/M)$, with $D = b^2 - ac$. By `art168_firstColumn`, the
representation is then the first column of any proper transformation. Differences from the historical sources: they take
$M > 0$, determinant $-D < 0$ and $|N| \le M/2$; none of these is needed here, and since the set of values is a
union of residue classes modulo $M$ (`mem_values_of_modEq`), "a representation belonging to the root class of $N$"
is the same as "$N$ is a value". -/
@[kb "gauss1801" "Art. 168-169"]
theorem art168_mem_values_iff {a b c M : ℤ} (hM : M ≠ 0) (N : ℤ) :
    N ∈ primitiveRepresentationValues a b c M ↔
      M ∣ N ^ 2 - gaussDet a b c ∧
        SLEquiv (gaussForm a b c) (gaussForm M N ((N ^ 2 - gaussDet a b c) / M)) := by
  constructor
  · rintro ⟨m, n, μ, ν, hb, he, rfl⟩
    exact art168_proper_transformation a b c m n μ ν M hb he hM
  · rintro ⟨_, hs⟩
    rw [primitiveRepresentationValues_eq_of_sLEquiv hs M]
    exact ⟨1, 0, 1, 0, by ring, by rw [eval_gaussForm]; ring, by simp [art155Value]⟩

/-! ### Art. 224: forms with a common value are properly equivalent -/

/-- Two forms $(M, N, (N^2 - D)/M)$ and $(M, N', (N'^2 - D)/M)$ with $N' \equiv N \pmod M$ and $M \mid N^2 - D$ are
properly equivalent (via $x \mapsto x + k y$). -/
theorem sLEquiv_of_modEq_roots {M N N' D : ℤ} (hM : M ≠ 0) (hd : M ∣ N ^ 2 - D) (hmod : N ≡ N' [ZMOD M]) :
    SLEquiv (gaussForm M N ((N ^ 2 - D) / M)) (gaussForm M N' ((N' ^ 2 - D) / M)) := by
  obtain ⟨L, hL⟩ := hd
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  have hN' : N' = N + k * M := by linear_combination hk
  have e1 : (N ^ 2 - D) / M = L := by rw [hL]; exact Int.mul_ediv_cancel_left _ hM
  have e2 : (N' ^ 2 - D) / M = M * k ^ 2 + 2 * N * k + L :=
    (Int.eq_ediv_of_mul_eq_right hM (by rw [hN']; linear_combination (-1 : ℤ) * hL)).symm
  rw [e1, e2, hN']
  exact sLEquiv_shift M N L k

/-- **Primitive representations of the same number with congruent values give properly equivalent forms**
(a recorded loose end; *Disq. Arith.* Arts. 168-169, 224): let $(a, b, c)$ and $(a', b', c')$ have the
same determinant $D$ and let $M \ne 0$. If $N$ is a value of a primitive representation of $M$ by the first form and
$N'$ one by the second, with $N \equiv N' \pmod M$ (in particular if $N = N'$), then the two forms are properly
equivalent: both are properly equivalent to $(M, N, (N^2 - D)/M)$ up to the shift $N \mapsto N + kM$. -/
@[kb "gauss1801" "Art. 224"]
theorem art224_sLEquiv_of_modEq {a b c a' b' c' M N N' : ℤ} (hM : M ≠ 0)
    (hD : gaussDet a b c = gaussDet a' b' c') (hN : N ∈ primitiveRepresentationValues a b c M)
    (hN' : N' ∈ primitiveRepresentationValues a' b' c' M) (hmod : N ≡ N' [ZMOD M]) :
    SLEquiv (gaussForm a b c) (gaussForm a' b' c') := by
  have h1 := (art168_mem_values_iff hM N).mp hN
  have h2 := (art168_mem_values_iff hM N').mp hN'
  rw [← hD] at h2
  exact h1.2.trans ((sLEquiv_of_modEq_roots hM h1.1 hmod).trans h2.2.symm)

/-- **Art. 224 as an equivalence** (a recorded loose end; *Disq. Arith.* Art. 224): let
$(a, b, c)$ and $(a', b', c')$ have the same determinant, let $M \ne 0$ and suppose $(a, b, c)$ represents $M$
primitively. Then the forms are properly equivalent iff they have a common value (root of $D$ modulo $M$)
of primitive representations of $M$. (The forward direction is `primitiveRepresentationValues_eq_of_sLEquiv`, the
backward direction is `art224_sLEquiv_of_modEq`.) Not formalized: the class-field reformulation. -/
@[kb "gauss1801" "Art. 224"]
theorem art224_iff {a b c a' b' c' M : ℤ} (hM : M ≠ 0) (hD : gaussDet a b c = gaussDet a' b' c')
    (hF : HasPrimitiveRepresentation (gaussForm a b c) M) :
    SLEquiv (gaussForm a b c) (gaussForm a' b' c') ↔
      ∃ N, N ∈ primitiveRepresentationValues a b c M ∧ N ∈ primitiveRepresentationValues a' b' c' M := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := values_nonempty_of_hasPrimitiveRepresentation hF
    exact ⟨N, hN, by rw [← primitiveRepresentationValues_eq_of_sLEquiv h M]; exact hN⟩
  · rintro ⟨N, h1, h2⟩
    exact art224_sLEquiv_of_modEq hM hD h1 h2 (Int.ModEq.refl _)

/-! ### Art. 170: ambiguous forms and opposite roots -/

/-- The involution $x \mapsto -x + k y$ fixes an ambiguous form: if $a k = -2 b$ then
$(a, b, c)(-x + k y, y) = (a, b, c)(x, y)$ as forms. -/
private theorem subst_ambiguous_aux (a b c k : ℤ) (hk : a * k = -(2 * b)) :
    subst (-1) k 0 1 (gaussForm a b c) = gaussForm a b c := by
  rw [subst_gaussForm]
  congr 1
  · ring
  · linear_combination (-1 : ℤ) * hk
  · linear_combination k * hk

/-- **Values of an ambiguous form are closed under negation** (*Disq. Arith.* Art. 170, part of (i)): if $a \mid 2b$
and $N$ is a value of a primitive representation of $M$ by $(a, b, c)$ then so is $-N$ (exactly, not only modulo
$M$): the involution $(m, n) \mapsto (-m + k n, n)$, $a k = -2b$, with Bezout pair $(-\mu, \nu + \mu k)$. -/
theorem values_neg_of_ambiguous {a b c M N : ℤ} (hamb : a ∣ 2 * b)
    (hN : N ∈ primitiveRepresentationValues a b c M) : -N ∈ primitiveRepresentationValues a b c M := by
  obtain ⟨k0, hk0⟩ := hamb
  have hk : a * (-k0) = -(2 * b) := by rw [hk0]; ring
  generalize -k0 = k at hk
  obtain ⟨m, n, μ, ν, hb, he, rfl⟩ := hN
  refine ⟨-m + k * n, n, -μ, ν + μ * k, by linear_combination hb, ?_, ?_⟩
  · rw [eval_gaussForm] at he ⊢
    linear_combination he + (k * n ^ 2 - 2 * m * n) * hk
  · unfold art155Value
    linear_combination (μ * m - (ν + μ * k) * n) * hk

/-- **Art. 170 (i)** (*Disq. Arith.* Art. 170): if $(a, b, c)$ is properly equivalent to an
ambiguous form $(a', b', c')$, i.e. $a' \mid 2b'$ (Gauss: $2b' \equiv 0 \pmod{a'}$), and $N$ is the value of a
primitive representation of $M$ by $(a, b, c)$, then so is $-N$; in particular the representations belonging to the
root $N$ and those belonging to $-N$ both exist. Proved for arbitrary integers. -/
@[kb "gauss1801" "Art. 170"]
theorem art170_values_neg_of_sLEquiv_ambiguous {a b c a' b' c' M N : ℤ}
    (h : SLEquiv (gaussForm a b c) (gaussForm a' b' c')) (hamb : a' ∣ 2 * b')
    (hN : N ∈ primitiveRepresentationValues a b c M) : -N ∈ primitiveRepresentationValues a b c M := by
  rw [primitiveRepresentationValues_eq_of_sLEquiv h M] at hN ⊢
  exact values_neg_of_ambiguous hamb hN

/-- **Art. 170 (ii), the proved part** (*Disq. Arith.* Art. 170, via Arts. 164, 168, 169):
let $M \ne 0$ and suppose $N$ and $-N$ are both values of primitive representations of $M$ by $(a, b, c)$
(by `mem_values_of_modEq` it suffices that representations with values $N$ and a value congruent to $-N$
modulo $M$ exist). Then, with $G = (M, N, (N^2 - D)/M)$: $(a, b, c)$ is properly equivalent to $G$, is improperly
equivalent to $G$, and is properly equivalent to its opposite form $(a, -b, c)$. -/
@[kb "gauss1801" "Art. 170"]
theorem art170_converse {a b c M N : ℤ} (hM : M ≠ 0) (hN : N ∈ primitiveRepresentationValues a b c M)
    (hN' : -N ∈ primitiveRepresentationValues a b c M) :
    SLEquiv (gaussForm a b c) (gaussForm M N ((N ^ 2 - gaussDet a b c) / M)) ∧
      ImproperlyEquivalent (gaussForm a b c) (gaussForm M N ((N ^ 2 - gaussDet a b c) / M)) ∧
      SLEquiv (gaussForm a b c) (gaussForm a (-b) c) := by
  have h1 := ((art168_mem_values_iff hM N).mp hN).2
  have h2 := ((art168_mem_values_iff hM (-N)).mp hN').2
  rw [neg_sq] at h2
  have h3 : SLEquiv (gaussForm a b c) (conjForm (gaussForm M N ((N ^ 2 - gaussDet a b c) / M))) := by
    rw [conjForm_gaussForm]; exact h2
  refine ⟨h1, (improperlyEquivalent_iff_sLEquiv_conjForm _ _).mpr h3, ?_⟩
  rw [← conjForm_gaussForm]
  exact h3.trans (sLEquiv_conjForm_conjForm h1).symm

/-- **Gauss's Art. 165, as a named proposition (proved in `AmbiguousClasses.lean` as `art165_ambiguousClause`):** a form properly equivalent to its opposite is
properly equivalent to an ambiguous form $(a', b', c')$ with $a' \mid 2b'$. This is the content of Gauss's
Arts. 163-165. It is stated for all integers $a, b, c$ and holds for all of them (including square and zero
determinants). -/
def Art165AmbiguousClause : Prop :=
  ∀ a b c : ℤ, SLEquiv (gaussForm a b c) (gaussForm a (-b) c) →
    ∃ a' b' c' : ℤ, a' ∣ 2 * b' ∧ SLEquiv (gaussForm a b c) (gaussForm a' b' c')

/-- **The last clause of Art. 170 (ii), as a named proposition (proved in `AmbiguousClasses.lean` as `art170_ambiguousClause`):** if $M \ne 0$ and $(a, b, c)$ has
primitive representations of $M$ with values $N$ and $-N$, then $(a, b, c)$ is properly equivalent to an ambiguous
form $(a', b', c')$ with $a' \mid 2b'$. What is missing is exactly Gauss's Art. 165 (`Art165AmbiguousClause`); see
`art170_ambiguousClause_of_art165`. -/
def Art170AmbiguousClause : Prop :=
  ∀ a b c M N : ℤ, M ≠ 0 → N ∈ primitiveRepresentationValues a b c M →
    -N ∈ primitiveRepresentationValues a b c M →
    ∃ a' b' c' : ℤ, a' ∣ 2 * b' ∧ SLEquiv (gaussForm a b c) (gaussForm a' b' c')

/-- **Art. 170 (ii) from Art. 165**: `Art165AmbiguousClause` implies
`Art170AmbiguousClause`, by `art170_converse` (the form is properly equivalent to its opposite). -/
@[kb "gauss1801" "Art. 170"]
theorem art170_ambiguousClause_of_art165 (h : Art165AmbiguousClause) : Art170AmbiguousClause :=
  fun a b c _ _ hM hN hN' => h a b c (art170_converse hM hN hN').2.2

end QuadFormsKB.Historical.Gauss
