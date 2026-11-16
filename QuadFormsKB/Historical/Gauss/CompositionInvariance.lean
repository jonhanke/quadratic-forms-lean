import QuadFormsKB.Historical.Gauss.Composition

/-!
# Composition is invariant under proper equivalence (Disquisitiones Arithmeticae, Arts. 236, 238)

(Art. 238, end: if $F, f, f'$ are equivalent to $G, g, g'$, and $F$ is compounded of
$f, f'$, then $G$ is compounded of $g, g'$, the factors entering in the same way) and (Art. 236:
existence of a form compounded of two given forms).

## The computation

Write a bilinear substitution $X = p_0\,xx' + p_1\,xy' + p_2\,yx' + p_3\,yy'$ as the $2 \times 2$ matrix
$\mathsf P = \begin{pmatrix} p_0 & p_1 \\ p_2 & p_3 \end{pmatrix}$, so that $X = u^{\mathsf T} \mathsf P\, v$ with
$u = (x, y)$, $v = (x', y')$ (`bmat`). If $F(X, Y) = g(u)\, g'(v)$ and $f(u) = g(\tau u)$, $f'(v) = g'(\tau' v)$, then
$F$ is transformed into $f f'$ by $\tau^{\mathsf T} \mathsf P \tau'$, $\tau^{\mathsf T} \mathsf Q \tau'$
(`transport`). Gauss's six numbers are the $2 \times 2$ minors
$M(ab, cd) = \mathsf P_{ab} \mathsf Q_{cd} - \mathsf Q_{ab} \mathsf P_{cd}$ (`bminor`), and they transform tensorially
(`bminor_transport`). Gauss's relations of Art. 235 say exactly
$M(ab, cd) = n' A_{ac} \varepsilon_{bd} + n\, \varepsilon_{ac} A'_{bd}$, with $A, A'$ the Gram matrices of $g, g'$
($A_{01} = b/2$ in the library's coefficients) and $\varepsilon$ the alternating matrix; since
$\tau^{\mathsf T} A \tau$ is the Gram matrix of $f$ and $\tau'^{\mathsf T} \varepsilon \tau' = \det(\tau')\,\varepsilon$,
the relations persist with the same $n, n'$ when $\det \tau = \det \tau' = 1$. Coprimality of the six numbers persists
because the transport by $\tau^{-1}, \tau'^{-1}$ undoes it.

## What is proved

* `isCompounded_subst` (Art. 238): if $F$ is compounded directly of $g, g'$, it is compounded directly of every pair
  $f, f'$ properly equivalent to $g, g'$.
* `art236_exists_compounded` (Art. 236 for the given forms themselves): any two primitive forms of the same nonzero
  discriminant have a form compounded directly of them. Gauss's Art. 236 also covers non-primitive forms and
  determinants in the ratio of two squares; those cases remain the named statement `GaussCompositionExistence`.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-- The coefficient vector $(p_0, p_1, p_2, p_3)$ of a bilinear substitution as the $2 \times 2$ matrix
$\begin{pmatrix} p_0 & p_1 \\ p_2 & p_3 \end{pmatrix}$ (rows: $x, y$; columns: $x', y'$). -/
def bmat (p : Fin 4 → ℤ) : Fin 2 → Fin 2 → ℤ := ![![p 0, p 1], ![p 2, p 3]]

/-- The $2 \times 2$ matrix $\begin{pmatrix} t_0 & t_1 \\ t_2 & t_3 \end{pmatrix}$ of a linear substitution
$x \mapsto t_0 x + t_1 y$, $y \mapsto t_2 x + t_3 y$. -/
def smat (t : Fin 4 → ℤ) : Fin 2 → Fin 2 → ℤ := ![![t 0, t 1], ![t 2, t 3]]

/-- The entry $(\tau^{\mathsf T} \mathsf P \tau')_{ij} = \sum_{a, b} \tau_{ai} \mathsf P_{ab} \tau'_{bj}$. -/
def trEntry (t t' p : Fin 4 → ℤ) (i j : Fin 2) : ℤ :=
  ∑ a : Fin 2, ∑ b : Fin 2, smat t a i * bmat p a b * smat t' b j

/-- **Transport of a bilinear substitution** by the linear substitutions $\tau$ (first factor) and $\tau'$ (second
factor): the coefficients of $\tau^{\mathsf T} \mathsf P \tau'$, i.e. of $X(\tau u, \tau' v)$. -/
def transport (t t' p : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![trEntry t t' p 0 0, trEntry t t' p 0 1, trEntry t t' p 1 0, trEntry t t' p 1 1]

/-- The minor $M(ab, cd) = \mathsf P_{ab}\mathsf Q_{cd} - \mathsf Q_{ab}\mathsf P_{cd}$. -/
def bminor (p q : Fin 4 → ℤ) (a b c d : Fin 2) : ℤ := bmat p a b * bmat q c d - bmat q a b * bmat p c d

theorem minors_eq_bminor (p q : Fin 4 → ℤ) :
    minors p q = ![bminor p q 0 0 0 1, bminor p q 0 0 1 0, bminor p q 0 0 1 1, bminor p q 0 1 1 0,
      bminor p q 0 1 1 1, bminor p q 1 0 1 1] := by
  ext i; fin_cases i <;> simp [minors, bminor, bmat]

theorem bmat_transport (t t' p : Fin 4 → ℤ) (i j : Fin 2) :
    bmat (transport t t' p) i j = ∑ a : Fin 2, ∑ b : Fin 2, smat t a i * bmat p a b * smat t' b j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- **The minors transform tensorially:**
$M'(ij, kl) = \sum_{a,b,c,d} \tau_{ai}\tau'_{bj}\tau_{ck}\tau'_{dl}\, M(ab, cd)$. -/
theorem bminor_transport (t t' p q : Fin 4 → ℤ) (i j k l : Fin 2) :
    bminor (transport t t' p) (transport t t' q) i j k l =
      ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
        smat t a i * smat t' b j * smat t c k * smat t' d l * bminor p q a b c d := by
  simp only [bminor, bmat_transport, Fin.sum_univ_two]
  ring

theorem bilin_transport (t t' p : Fin 4 → ℤ) (x y x' y' : ℤ) :
    bilin (transport t t' p) x y x' y' =
      bilin p (t 0 * x + t 1 * y) (t 2 * x + t 3 * y) (t' 0 * x' + t' 1 * y') (t' 2 * x' + t' 3 * y') := by
  simp [bilin, transport, trEntry, smat, bmat, Fin.sum_univ_two]
  ring

/-- Transporting by $\tau$ and then by $\sigma$ is transporting by $\tau\sigma$. -/
theorem transport_transport (t t' s s' p : Fin 4 → ℤ) :
    transport s s' (transport t t' p) =
      transport ![t 0 * s 0 + t 1 * s 2, t 0 * s 1 + t 1 * s 3, t 2 * s 0 + t 3 * s 2, t 2 * s 1 + t 3 * s 3]
        ![t' 0 * s' 0 + t' 1 * s' 2, t' 0 * s' 1 + t' 1 * s' 3, t' 2 * s' 0 + t' 3 * s' 2,
          t' 2 * s' 1 + t' 3 * s' 3] p := by
  ext e; fin_cases e <;> simp [transport, trEntry, smat, bmat, Fin.sum_univ_two] <;> ring

theorem transport_one (p : Fin 4 → ℤ) : transport ![1, 0, 0, 1] ![1, 0, 0, 1] p = p := by
  ext e; fin_cases e <;> simp [transport, trEntry, smat, bmat, Fin.sum_univ_two]

theorem bminor_swap (p q : Fin 4 → ℤ) (a b c d : Fin 2) : bminor p q a b c d = -bminor p q c d a b := by
  simp only [bminor]; ring

theorem bminor_self (p q : Fin 4 → ℤ) (a b : Fin 2) : bminor p q a b a b = 0 := by
  simp only [bminor]; ring

/-- A common divisor of the six numbers of $(\mathsf P, \mathsf Q)$ divides those of the transport. -/
theorem dvd_minors_transport {p q : Fin 4 → ℤ} (t t' : Fin 4 → ℤ) {d : ℤ} (h : ∀ i, d ∣ minors p q i) :
    ∀ i, d ∣ minors (transport t t' p) (transport t t' q) i := by
  rw [minors_eq_bminor] at h
  have h0 : d ∣ bminor p q 0 0 0 1 := h 0
  have h1 : d ∣ bminor p q 0 0 1 0 := h 1
  have h2 : d ∣ bminor p q 0 0 1 1 := h 2
  have h3 : d ∣ bminor p q 0 1 1 0 := h 3
  have h4 : d ∣ bminor p q 0 1 1 1 := h 4
  have h5 : d ∣ bminor p q 1 0 1 1 := h 5
  have hb : ∀ a b c e : Fin 2, d ∣ bminor p q a b c e := by
    intro a b c e
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
      first
      | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5
      | (rw [bminor_self]; exact dvd_zero d)
      | (rw [bminor_swap]; first
          | exact dvd_neg.mpr h0 | exact dvd_neg.mpr h1 | exact dvd_neg.mpr h2
          | exact dvd_neg.mpr h3 | exact dvd_neg.mpr h4 | exact dvd_neg.mpr h5)
  have hgen : ∀ i j k l : Fin 2, d ∣ bminor (transport t t' p) (transport t t' q) i j k l := by
    intro i j k l
    rw [bminor_transport]
    refine Finset.dvd_sum fun a _ => Finset.dvd_sum fun b _ => Finset.dvd_sum fun c _ =>
      Finset.dvd_sum fun e _ => Dvd.dvd.mul_left (hb a b c e) _
  intro i
  rw [minors_eq_bminor]
  fin_cases i
  · exact hgen 0 0 0 1
  · exact hgen 0 0 1 0
  · exact hgen 0 0 1 1
  · exact hgen 0 1 1 0
  · exact hgen 0 1 1 1
  · exact hgen 1 0 1 1

/-- The Gram matrix $\begin{pmatrix} a & b/2 \\ b/2 & c \end{pmatrix}$ of $a x^2 + b x y + c y^2$, over $\mathbb{Q}$. -/
def gram (g : BinQF) : Fin 2 → Fin 2 → ℚ := ![![(g.a : ℚ), (g.b : ℚ) / 2], ![(g.b : ℚ) / 2, (g.c : ℚ)]]

/-- The alternating matrix $\varepsilon = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$. -/
def eps : Fin 2 → Fin 2 → ℚ := ![![0, 1], ![-1, 0]]

/-- **Gauss's relations of Art. 235 in tensor form:**
$M(ab, cd) = n' A_{ac}\varepsilon_{bd} + n\,\varepsilon_{ac}A'_{bd}$. -/
theorem bminor_of_rel {p q : Fin 4 → ℤ} {g g' : BinQF} {n n' : ℚ}
    (h0 : (minors p q 0 : ℚ) = g.a * n') (h1 : ((minors p q 2 : ℚ) - minors p q 3) = g.b * n')
    (h2 : (minors p q 5 : ℚ) = g.c * n') (h3 : (minors p q 1 : ℚ) = g'.a * n)
    (h4 : ((minors p q 2 : ℚ) + minors p q 3) = g'.b * n) (h5 : (minors p q 4 : ℚ) = g'.c * n) :
    ∀ a b c d : Fin 2, (bminor p q a b c d : ℚ) = n' * gram g a c * eps b d + n * eps a c * gram g' b d := by
  simp only [minors, Matrix.cons_val] at h0 h1 h2 h3 h4 h5
  push_cast at h0 h1 h2 h3 h4 h5
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [bminor, bmat, gram, eps] <;> ring_nf <;> ring_nf at h0 h1 h2 h3 h4 h5 <;> linarith

/-- **Gauss, *Disq. Arith.* Art. 238 (end): composition is invariant under proper
equivalence.** If $F$ is compounded directly of $g$ and $g'$ (Art. 235, `IsCompounded`) and $f$, $f'$ are obtained
from $g$, $g'$ by substitutions of determinant $+1$ ($f(x, y) = g(t_0 x + t_1 y, t_2 x + t_3 y)$ and likewise
$f'$), then $F$ is compounded directly of $f$ and $f'$, with the same $n, n'$. -/
@[kb "gauss1801" "Art. 238"]
theorem isCompounded_subst {F g g' : BinQF} (h : IsCompounded F g g') (t t' : Fin 4 → ℤ)
    (ht : t 0 * t 3 - t 1 * t 2 = 1) (ht' : t' 0 * t' 3 - t' 1 * t' 2 = 1) :
    IsCompounded F (subst (t 0) (t 1) (t 2) (t 3) g) (subst (t' 0) (t' 1) (t' 2) (t' 3) g') := by
  obtain ⟨p, q, hT, hcop, n, n', hn, hn', h0, h1, h2, h3, h4, h5⟩ := h
  have hB := bminor_of_rel h0 h1 h2 h3 h4 h5
  refine ⟨transport t t' p, transport t t' q, ?_, ?_, n, n', hn, hn', ?_⟩
  · intro x y x' y'
    rw [bilin_transport, bilin_transport, hT, eval_subst, eval_subst]
  · intro d hd
    apply hcop d
    -- transport back by the inverse substitutions
    have hback := dvd_minors_transport ![t 3, -t 1, -t 2, t 0] ![t' 3, -t' 1, -t' 2, t' 0] hd
    have e1 : ∀ r : Fin 4 → ℤ,
        transport ![t 3, -t 1, -t 2, t 0] ![t' 3, -t' 1, -t' 2, t' 0] (transport t t' r) = r := by
      intro r
      rw [transport_transport]
      have : (![t 0 * t 3 + t 1 * -t 2, t 0 * -t 1 + t 1 * t 0, t 2 * t 3 + t 3 * -t 2, t 2 * -t 1 + t 3 * t 0] :
          Fin 4 → ℤ) = ![1, 0, 0, 1] := by
        ext e; fin_cases e <;> simp <;> linarith
      have h' : (![t' 0 * t' 3 + t' 1 * -t' 2, t' 0 * -t' 1 + t' 1 * t' 0, t' 2 * t' 3 + t' 3 * -t' 2,
          t' 2 * -t' 1 + t' 3 * t' 0] : Fin 4 → ℤ) = ![1, 0, 0, 1] := by
        ext e; fin_cases e <;> simp <;> linarith
      simp only [Matrix.cons_val] at this h' ⊢
      rw [this, h', transport_one]
    rw [e1, e1] at hback
    exact hback
  · have htQ : ((t 0 : ℚ) * t 3 - t 1 * t 2) = 1 := by exact_mod_cast ht
    have htQ' : ((t' 0 : ℚ) * t' 3 - t' 1 * t' 2) = 1 := by exact_mod_cast ht'
    have key : ∀ i j k l : Fin 2, (bminor (transport t t' p) (transport t t' q) i j k l : ℚ) =
        ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
          (smat t a i : ℚ) * smat t' b j * smat t c k * smat t' d l *
            (n' * gram g a c * eps b d + n * eps a c * gram g' b d) := by
      intro i j k l
      rw [bminor_transport]
      push_cast
      simp only [hB]
    rw [minors_eq_bminor]
    simp only [Matrix.cons_val]
    simp only [key, Fin.sum_univ_two, smat, gram, eps, subst, a_mk, b_mk, c_mk]
    simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination n' * ((g.a : ℚ) * t 0 ^ 2 + g.b * t 0 * t 2 + g.c * t 2 ^ 2) * htQ'
    · linear_combination n' * (2 * (g.a : ℚ) * t 0 * t 1 + g.b * (t 0 * t 3 + t 1 * t 2) + 2 * g.c * t 2 * t 3) * htQ'
    · linear_combination n' * ((g.a : ℚ) * t 1 ^ 2 + g.b * t 1 * t 3 + g.c * t 3 ^ 2) * htQ'
    · linear_combination n * ((g'.a : ℚ) * t' 0 ^ 2 + g'.b * t' 0 * t' 2 + g'.c * t' 2 ^ 2) * htQ
    · linear_combination n * (2 * (g'.a : ℚ) * t' 0 * t' 1 + g'.b * (t' 0 * t' 3 + t' 1 * t' 2) +
        2 * g'.c * t' 2 * t' 3) * htQ
    · linear_combination n * ((g'.a : ℚ) * t' 1 ^ 2 + g'.b * t' 1 * t' 3 + g'.c * t' 3 ^ 2) * htQ

/-- **Art. 238 for proper equivalence** (`Binary.SLEquiv`): if $F$ is compounded directly of $g, g'$, and $f \sim g$,
$f' \sim g'$ properly, then $F$ is compounded directly of $f, f'$. -/
@[kb "gauss1801" "Art. 238"]
theorem isCompounded_of_sLEquiv {F f f' g g' : BinQF} (h : IsCompounded F g g') (e : SLEquiv g f)
    (e' : SLEquiv g' f') : IsCompounded F f f' := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp e
  obtain ⟨p', q', r', s', hd', rfl⟩ := (sLEquiv_iff _ _).mp e'
  exact isCompounded_subst h ![p, q, r, s] ![p', q', r', s'] (by simpa using hd) (by simpa using hd')

/-- **Gauss, *Disq. Arith.* Art. 236, for the given forms themselves, primitive and of
the same determinant:** for any two primitive forms $f, f'$ of the same discriminant $D \ne 0$ there is a primitive
form $F$ of discriminant $D$ compounded directly of $f$ and $f'$ (Art. 235). Gauss's Art. 236 also allows
non-primitive forms and determinants in the ratio of two squares (`GaussCompositionExistence`, stated). -/
@[kb "gauss1801" "Art. 236, pp. 350-353"]
theorem art236_exists_compounded {f f' : BinQF} (hf : f.IsPrimitive) (hf' : f'.IsPrimitive)
    (hD : f.disc = f'.disc) (hD0 : f.disc ≠ 0) :
    ∃ F : BinQF, IsCompounded F f f' ∧ F.IsPrimitive ∧ F.disc = f.disc := by
  obtain ⟨g, g', F, e, e', hc, hp, hd⟩ := art236_exists_compounded_of_classes hf hf' hD hD0
  exact ⟨F, isCompounded_of_sLEquiv hc e.symm e'.symm, hp, hd⟩

/-- **Art. 236 in Gauss's notation:** for properly primitive forms $(a, b, c)$, $(a', b', c')$ (i.e.
$a x^2 + 2bxy + cy^2$ with $\gcd(a, 2b, c) = 1$) of the same nonzero determinant $b^2 - ac = b'^2 - a'c'$ there is a
properly primitive form $(A, B, C)$ of the same determinant compounded directly of them. -/
@[kb "gauss1801" "Art. 236, pp. 350-353"]
theorem art236_exists_compounded_gauss {a b c a' b' c' : ℤ} (hf : (gaussForm a b c).IsPrimitive)
    (hf' : (gaussForm a' b' c').IsPrimitive) (hD : gaussDet a b c = gaussDet a' b' c') (hD0 : gaussDet a b c ≠ 0) :
    ∃ A B C : ℤ, IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') ∧
      (gaussForm A B C).IsPrimitive ∧ gaussDet A B C = gaussDet a b c := by
  obtain ⟨F, hc, hp, hd⟩ := art236_exists_compounded hf hf' (by rw [disc_gaussForm, disc_gaussForm, hD])
    (by rw [disc_gaussForm]; exact mul_ne_zero four_ne_zero hD0)
  -- the composite has even middle coefficient, since its discriminant $b^2 - 4AC = 4(b^2 - ac)$ is even
  have hev : Even F.b := by
    have hd' : F.b ^ 2 - 4 * F.a * F.c = 4 * gaussDet a b c := by
      have := hd; rw [disc_gaussForm] at this; exact this
    have : Even (F.b ^ 2) := ⟨2 * F.a * F.c + 2 * gaussDet a b c, by linear_combination hd'⟩
    exact (Int.even_pow' two_ne_zero).mp this
  obtain ⟨A, B, C, rfl⟩ := (exists_gaussForm_iff F).mpr hev
  refine ⟨A, B, C, hc, hp, ?_⟩
  have := hd
  rw [disc_gaussForm, disc_gaussForm] at this
  linarith

end QuadFormsKB.Historical.Gauss
