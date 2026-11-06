/-
# Hanke 2011, §8: automorphisms of rank-two lattices and the class number formula

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §8.

Throughout, $K/F$ is a CM extension, $\mu_K$ the group of roots of unity of $K$, and $G(\mathcal O_K)$ Kneser's group of
(projective, primitive) rank-two quadratic $\mathcal O_F$-lattices $(L, Q)$ which are rank-one $\mathcal O_K$-modules
with $Q(cx) = N_{K/F}(c)\,Q(x)$.

* `lemma_8_5_false` (**Update/erratum**): Lemma 8.5 (p. 35) claims
  $\mathrm{Aut}^+(L) = \mu_K$ and $|\mathrm{Aut}(L)| = 2\,|\mu_K|$. The second claim is false in general. The proof argues
  that the nontrivial Galois element $\sigma$ lies in $\mathrm{Aut}(L)$ because "$I\,\sigma(I) = a\mathcal O_K$ gives
  $\sigma(I) = I$ in $\mathrm{Pic}(\mathcal O_K)$"; but $I\,\sigma(I) = a\mathcal O_K$ gives $\sigma(I) = I^{-1}$ in
  $\mathrm{Pic}(\mathcal O_K)$, so $\sigma$ preserves the class of $L$ only when $[I]^2 = 1$ (the class is *ambiguous*).
  Counterexample over $F = \mathbb{Q}$, $K = \mathbb{Q}(\sqrt{-23})$ ($D = -23$, $|\mu_K| = 2$): the form
  $f = 2x^2 + xy + 3y^2$ has class of order $3$ in the class group of discriminant $-23$ (not ambiguous). It has no
  automorphism of determinant $-1$ (`no_improper_aut_f23`), so $|\mathrm{Aut}(f)| = |\mathrm{Aut}^+(f)| = 2$, whereas the
  paper's formula would give $2\,|\mu_K| = 4$.
* `lemma_8_5_corrected` (**proposed correction**, over $F = \mathbb{Q}$): $|\mathrm{Aut}(L)| = 2\,|\mu_K|$ if the class of
  $L$ is ambiguous (order $\le 2$, equivalently $\bar f \sim_{\mathrm{SL}_2(\mathbb Z)} f$), and $|\mathrm{Aut}(L)| = |\mu_K|$
  otherwise. A citing wrapper of `QuadFormsKB.Binary.card_aut`; the first claim $|\mathrm{Aut}^+(f)| = |\mu_K|$ is
  `QuadFormsKB.Binary.card_autSL`.
* `lemma_8_5_corrected_relative`: the same correction over a general totally real $F$, as a wrapper of
  `QuadFormsKB.Binary.Rel.card_autLat_ideal_cm`.
* `theorem_8_6_rat`: Theorem 8.6 (p. 36) for $F = \mathbb{Q}$, which is Dirichlet's class number formula for an
  imaginary quadratic field of discriminant $D$:
  $h(\mathcal O_K) = |\mu_K|\,\dfrac{|D|^{1/2}}{2\pi}\,L(1, \chi_D)$, where $Q_{K/\mathbb Q} = 1$, $h(\mathbb Z) = 1$ and
  $N(I(S)) = |D|$, $S$ being the Hessian-determinant squareclass of the norm form of $\mathcal O_K$ (the Hessian
  determinant of the principal form of discriminant $D$ is $-D$, `det_hessian_principalForm`).
* `remark_8_9`: Remark 8.9 (p. 37), the class number formula for a CM field $K$ with maximal totally real subfield
  $K^+$, as a statement about the limit $\lim_{s\to1^+}L(s,\chi_{K/K^+})$ of the Euler product (the repository's
  `relLR`).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.FormAut
import QuadFormsKB.Binary.ClassNumberFormula
import QuadFormsKB.Binary.RelativeCNF
import QuadFormsKB.Binary.RelFormAut

open NumberField NumberField.Units Filter Topology
open QuadFormsKB.Binary

namespace QuadFormsKB.Hanke2011Structure

/-! ### Lemma 8.5: the counterexample $2x^2 + xy + 3y^2$ of discriminant $-23$ -/

/-- The binary form $f_{23} = 2x^2 + xy + 3y^2$ of discriminant $1 - 24 = -23$. -/
def f23 : BinQF := BinQF.mk 2 1 3

private theorem isFund_neg23 : Int.IsFundamentalDiscr (-23) := by
  rw [Int.isFundamentalDiscr_iff_squarefree]
  left
  refine ⟨by norm_num, ?_⟩
  exact Int.squarefree_natAbs.mp (by norm_num; exact Nat.prime_iff.mp (by norm_num : Nat.Prime 23) |>.squarefree)

/-- $-23$ is a fundamental discriminant different from $1$ (local copy, to avoid importing Cassels' file). -/
private instance isQuadDisc_neg23 : IsQuadDisc (-23) where
  fund := isFund_neg23
  ne_one := by norm_num

/-- $f_{23}$ is a primitive positive definite form of discriminant $-23$. -/
def f23Prim : PrimPosForm (-23) :=
  ⟨f23, (mem_primPosForm_iff isFund_neg23 (by norm_num) f23).mpr
    ⟨by simp [f23, BinQF.disc], by simp [f23]⟩⟩

/-- **$f_{23}$ has no automorphism of determinant $-1$:** every $\gamma \in \mathrm{GL}_2(\mathbb{Z})$ with
$f_{23}\circ\gamma = f_{23}$ has $\det\gamma = 1$. *Proof:* with $\gamma = \begin{pmatrix} p & q\\ r & s\end{pmatrix}$ the
$x^2$-coefficient gives $2p^2 + pr + 3r^2 = 2$, hence $r = 0$, $p = \pm1$; the $y^2$-coefficient gives
$2q^2 + qs + 3s^2 = 3$, hence $q = 0$, $s = \pm 1$; the $xy$-coefficient gives $ps = 1$. -/
theorem no_improper_aut_f23 : ∀ γ ∈ Siegel.Aut f23, γ.val.det = 1 := by
  intro γ hγ
  rw [mem_aut_iff] at hγ
  have ha := congrArg BinQF.a hγ
  have hb := congrArg BinQF.b hγ
  have hc := congrArg BinQF.c hγ
  simp only [BinQF.subst, f23, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk] at ha hb hc
  rw [Matrix.det_fin_two]
  generalize γ.val 0 0 = p at *
  generalize γ.val 0 1 = q at *
  generalize γ.val 1 0 = r at *
  generalize γ.val 1 1 = s at *
  have hr : r = 0 := by nlinarith [sq_nonneg (4 * p + r), sq_nonneg r]
  subst hr
  have hp : p ^ 2 = 1 := by nlinarith
  have hs1 : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg (4 * q + s)]
  have hs : s = 1 ∨ s = -1 := by
    have hs0 : s ≠ 0 := by
      rintro rfl
      nlinarith [sq_nonneg (4 * q)]
    have : 1 ≤ s ^ 2 := by
      have := sq_pos_of_ne_zero hs0
      omega
    have : s ^ 2 = 1 := le_antisymm hs1 this
    have h0 : (s - 1) * (s + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h0 with h | h
    · left; omega
    · right; omega
  have hq : q = 0 := by
    rcases hs with rfl | rfl <;> nlinarith [sq_nonneg (4 * q + 1), sq_nonneg (4 * q - 1)]
  subst hq
  have hp' : p = 1 ∨ p = -1 := by
    have h0 : (p - 1) * (p + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h0 with h | h
    · left; omega
    · right; omega
  rcases hs with rfl | rfl <;> rcases hp' with rfl | rfl <;> simp_all

/-- **Lemma 8.5 is false as stated** (*Update/erratum*).

Paper (Lemma 8.5, p. 35, "Computing automorphisms"): for $K/F$ a CM extension and $(L, Q) \in G(\mathcal O_K)$,
$\mathrm{Aut}^+(L) = \mu_K$ and $|\mathrm{Aut}(L)| = 2\,|\mu_K|$.

Counterexample for $F = \mathbb{Q}$, $K = \mathbb{Q}(\sqrt{-23})$, $L = (\mathbb{Z}^2, f_{23})$ with
$f_{23} = 2x^2 + xy + 3y^2$ (discriminant $-23$, class of order $3$): $f_{23}$ has no improper automorphism
(`no_improper_aut_f23`), so $|\mathrm{Aut}(f_{23})| = |\mathrm{Aut}^+(f_{23})| = |\mu_K| = 2$, while the paper's formula
gives $2\,|\mu_K| = 4$. Stated here as: $|\mathrm{Aut}(f_{23})| = 2$, $|\mu_{\mathbb{Q}(\sqrt{-23})}| = 2$ and
$|\mathrm{Aut}(f_{23})| \ne 2\,|\mu_{\mathbb{Q}(\sqrt{-23})}|$. The faulty step is "$I\sigma(I) = a\mathcal O_K$ gives
$\sigma(I) = I$ in $\mathrm{Pic}(\mathcal O_K)$": it gives $\sigma(I) = I^{-1}$. -/
@[kb "hanke2011structure" "Lemma 8.5, p. 35"]
theorem lemma_8_5_false :
    Nat.card (Siegel.Aut f23) = 2 ∧ torsionOrder (QField (-23)) = 2 ∧
      Nat.card (Siegel.Aut f23) ≠ 2 * torsionOrder (QField (-23)) := by
  have hw : torsionOrder (QField (-23)) = 2 := by
    rw [torsionOrder_of_neg (by norm_num)]; norm_num
  have hcard : Nat.card (Siegel.Aut f23) = 2 := by
    have h := card_aut (by norm_num : (-23 : ℤ) < 0) f23Prim
    have hn : ¬ SLEquiv (conjForm f23) f23 := fun hs => by
      obtain ⟨γ, hγ, hd⟩ := (exists_improper_iff f23).mpr hs
      have := no_improper_aut_f23 γ hγ
      omega
    simpa [f23Prim, hn, hw] using h
  refine ⟨hcard, hw, ?_⟩
  rw [hcard, hw]; norm_num

open Classical in
/-- **Lemma 8.5, corrected** (*Update*; case $F = \mathbb{Q}$).
Let $D < 0$ be a fundamental discriminant, $K = \mathbb{Q}(\sqrt D)$, $f$ a primitive positive definite binary form of
discriminant $D$ (a lattice $L \in G(\mathcal O_K)$), $w = |\mu_K|$. Then
$$|\mathrm{Aut}^+(f)| = w,\qquad
|\mathrm{Aut}(f)| = \begin{cases} 2w & \text{if } \bar f \sim_{\mathrm{SL}_2(\mathbb Z)} f
  \ (\text{the class of } f \text{ is ambiguous, order} \le 2),\\ w & \text{otherwise,}\end{cases}$$
where $\bar f(x,y) = f(x,-y)$ and $\mathrm{Aut}(f) \subseteq \mathrm{GL}_2(\mathbb{Z})$. This is the repository's
`QuadFormsKB.Binary.card_autSL` and `card_aut`. -/
@[kb "hanke2011structure" "Lemma 8.5, p. 35 (corrected)"]
theorem lemma_8_5_corrected {D : ℤ} [IsQuadDisc D] (hD : D < 0) (f : PrimPosForm D) :
    Nat.card (AutSL f.1) = torsionOrder (QField D) ∧
      Nat.card (Siegel.Aut f.1) =
        (if SLEquiv (conjForm f.1) f.1 then 2 else 1) * torsionOrder (QField D) :=
  ⟨card_autSL hD f, card_aut hD f⟩

open QuadFormsKB.Binary.Rel in
/-- **Lemma 8.5, corrected, over a totally real field $F$** (*Update*). Let $K/F$ be a CM extension (`IsTotallyReal F`, `IsTotallyComplex K`, $[K:F] = 2$), $c \in F^\times$,
$\mathfrak A \ne 0$ an ideal of $\mathcal O_K$, and $L = \mathfrak A$ with the quadratic form $c\,N_{K/F}$ (a lattice in
$G(\mathcal O_K)$ up to scaling). Then
$$|\mathrm{Aut}(L)| = \begin{cases} 2\,|\mu_K| & \text{if some } u \in K \text{ with } N_{K/F}(u) = 1 \text{ satisfies }
  u\,\sigma(\mathfrak A) = \mathfrak A \ (\text{an improper automorphism exists; the class of } L \text{ is ambiguous}),\\
  |\mu_K| & \text{otherwise,}\end{cases}$$
with $\sigma$ the nontrivial element of $\mathrm{Gal}(K/F)$. Wrapper of `card_autLat_ideal_cm`; the existence of an
improper automorphism implies $\sigma_*[\mathfrak A] = [\mathfrak A]$ (`conjClass_eq_of_improper`), so the paper's
$2|\mu_K|$ cannot hold for non-ambiguous classes. -/
@[kb "hanke2011structure" "Lemma 8.5, p. 35 (corrected, relative)"]
theorem lemma_8_5_corrected_relative {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyReal F] [IsTotallyComplex K]
    {c : F} (hc : c ≠ 0) {𝔄 : Ideal (𝓞 K)} (h𝔄 : 𝔄 ≠ ⊥) :
    Nat.card (Lattices.autLatV (c • normForm F K) (idealLat F 𝔄)) =
      torsionOrder K *
        (open Classical in
          if ∃ u : K, Algebra.norm F u = 1 ∧ smulLat u (idealLat F (conjIdeal F 𝔄)) = idealLat F 𝔄
          then 2 else 1) :=
  card_autLat_ideal_cm hc h𝔄

/-! ### Definition 8.1: the discriminant of a quadratic algebra -/

/-- **The discriminant of a free quadratic algebra** (Hanke 2011, Def. 8.1, p. 34): for $R = A[x]/(x^2 + bx + c)$ over a
commutative ring $A$ (locally $A = \mathcal O_{\mathfrak p}$), $\mathrm{Disc}_A(R) = b^2 - 4c$; the paper's
$\mathrm{Disc}_{\mathcal O_F}(R) \in \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$ is the family of the local squareclasses of these. -/
@[kb "hanke2011structure" "Def. 8.1, p. 34"]
def discQuadAlg {A : Type*} [CommRing A] (b c : A) : A := b ^ 2 - 4 * c

/-- **The Hessian determinant of the norm form is minus the discriminant** (used in the proof of Theorem 8.6, p. 36:
"$-S$ is the fundamental discriminant squareclass for $\mathcal O_K$"). Over $\mathbb Z$: for $R = \mathbb Z[x]/(x^2+bx+c)$
with $x \mapsto \alpha$, the norm form in the basis $1, \alpha$ is $N(u + v\alpha) = u^2 - b\,uv + c\,v^2$ (as
$\alpha + \bar\alpha = -b$, $\alpha\bar\alpha = c$), and $\det_H(u^2 - b\,uv + c\,v^2) = 4c - b^2 = -\mathrm{Disc}(R)$. -/
@[kb "hanke2011structure" "Def. 8.1, p. 34; Thm. 8.6, proof, p. 36"]
theorem det_hessian_normForm_quadAlg (b c : ℤ) :
    (QuadForm.hessian (BinQF.mk 1 (-b) c)).det = -discQuadAlg b c := by
  have h := BinQF.disc_eq_neg_det_hessian (BinQF.mk 1 (-b) c)
  simp only [BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk] at h
  unfold discQuadAlg
  linarith

/-! ### Lemma 8.3: Kneser's group counts proper classes -/

/-- **Lemma 8.3 needs proper classes** (*Update/erratum*).

Paper (Lemma 8.3, p. 34): $G(C) = \bigsqcup_{\vec\sigma'_\infty}\mathrm{Cls}^*(\det_H(C),\vec\sigma'_\infty;n=2)$, where
$\mathrm{Cls}^*$ is the set of *classes* (§1.3, p. 6; proper classes are $\mathrm{Cls}^{*,+}$). An element of Kneser's
$G(C)$ is a lattice with a $C$-module structure; the lattices $(L, Q)$ and $(L, Q)$ with the conjugate structure
$c \cdot x := \sigma(c)x$ are isometric (same class) but correspond to inverse ideal classes, so the map
$G(C) \to \bigsqcup\mathrm{Cls}^*$ is not injective: $G(C)$ is in bijection with the **proper** classes
$\bigsqcup\mathrm{Cls}^{*,+}$. Witness over $F = \mathbb Q$, $C = \mathcal O_K$, $K = \mathbb Q(\sqrt{-23})$:
$f_{23} = 2x^2 + xy + 3y^2$ and $\bar f_{23} = 2x^2 - xy + 3y^2$ are isometric via
$\operatorname{diag}(1,-1) \in \mathrm{GL}_2(\mathbb Z)$ (one class) but not properly equivalent (two proper classes,
the classes of order $3$ and their inverses). Counting: Lemma 8.4 gives $|G(\mathcal O_K)| = 2h(\mathcal O_K) = 6$, which is
the number of proper classes of definite primitive forms of discriminant $-23$ ($3$ positive, $3$ negative), while there
are only $2 + 2 = 4$ classes. With $\mathrm{Cls}^{*,+}$ in Lemma 8.3 and $\mathrm{Aut}^+ = \mu_K$ (Lemma 8.5, first claim), the
proof of Theorem 8.6 goes through using $\mathrm{Mass}^+ = 2\,\mathrm{Mass}$ (proof of Corollary 6.3) in place of the
second claim of Lemma 8.5 (`lemma_8_5_false`); the formula of Theorem 8.6 is unaffected. -/
@[kb "hanke2011structure" "Lemma 8.3, p. 34 (classes vs. proper classes)"]
theorem lemma_8_3_not_proper :
    conjForm f23 = BinQF.subst 1 0 0 (-1) f23 ∧ ¬ SLEquiv (conjForm f23) f23 := by
  refine ⟨rfl, fun hs => ?_⟩
  obtain ⟨γ, hγ, hd⟩ := (exists_improper_iff f23).mpr hs
  have := no_improper_aut_f23 γ hγ
  omega

/-! ### Remark 8.8: class numbers of orders -/

/-- **Remark 8.8 as printed gives a non-integer** (*Erratum*).

Paper (Rem. 8.8, p. 37): for an order $R_K \subseteq \mathcal O_K$,
$h(R_K) = h(\mathcal O_K)\prod_{\mathfrak p \mid I(S')/I(S)}\bigl(1 - \chi_S(\mathfrak p)/q\bigr)$ with $S = \det_H(\mathcal O_K, N_{K/F})$,
$S' = \det_H(R_K, N_{K/F})$. Take $F = \mathbb Q$, $K = \mathbb Q(i)$, $R_K = \mathbb Z[3i]$: the norm forms are $x^2+y^2$ and
$x^2+9y^2$, so $I(S) = 4\mathbb Z$, $I(S') = 36\mathbb Z$, $I(S')/I(S) = 9\mathbb Z$, the only prime is $3$, and
$\chi_S(3) = \left(\frac{-4}{3}\right) = -1$ (with the convention $\chi_u(\mathfrak p) = \left(\frac{-u}{\mathfrak p}\right)$ of Def. 7.5;
the other reading $\left(\frac{4}{3}\right) = 1$ fails as well); with $h(\mathbb Z[i]) = 1$ the printed formula gives
$h(\mathbb Z[3i]) = 1 - \chi_S(3)/3 \in \{4/3, 2/3\}$, which is not an integer (this theorem, for $\chi = \pm1$). The classical formula (Cox, Thm. 7.24; Shimura's formula cited in the remark)
has the extra factor $N(\mathfrak f)/[\mathcal O_K^\times : R_K^\times]$, $\mathfrak f$ the conductor
($N(\mathfrak f) = (N(I(S'))/N(I(S)))^{1/2}$): $h(\mathbb Z[3i]) = 1\cdot\frac{3}{2}\cdot\frac43 = 2$ (the forms $x^2+9y^2$,
$2x^2+2xy+5y^2$ of discriminant $-36$). -/
@[kb "hanke2011structure" "Rem. 8.8, p. 37 (printed, not integral)"]
theorem remark_8_8_printed_not_integral (χ : ℚ) (hχ : χ = 1 ∨ χ = -1) :
    ¬ ∃ h : ℕ, (h : ℚ) = 1 * (1 - χ / 3) := by
  rintro ⟨h, hh⟩
  rcases hχ with rfl | rfl
  · have h3 : ((h * 3 : ℕ) : ℚ) = 2 := by push_cast; rw [hh]; norm_num
    have : h * 3 = 2 := by exact_mod_cast h3
    omega
  · have h3 : ((h * 3 : ℕ) : ℚ) = 4 := by push_cast; rw [hh]; norm_num
    have : h * 3 = 4 := by exact_mod_cast h3
    omega

/-! ### Theorem 8.6 for $F = \mathbb{Q}$ -/

/-- The principal form of discriminant $D$ ($D \equiv 0, 1 \bmod 4$): $x^2 + bxy + cy^2$ with $b = D \bmod 2$ and
$c = (b - D)/4$, i.e. $x^2 + xy + \frac{1-D}{4}y^2$ for $D \equiv 1$ and $x^2 - \frac D4 y^2$ for $D \equiv 0 \pmod 4$.
It is the norm form of $\mathcal O_K$ in the basis $1, \omega$. -/
def principalForm (D : ℤ) : BinQF := BinQF.mk 1 (D % 2) ((D % 2 - D) / 4)

/-- For $D \equiv 0, 1 \pmod 4$ the principal form has discriminant $D$. -/
theorem disc_principalForm {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) : (principalForm D).disc = D := by
  have h4 : 4 * ((D % 2 - D) / 4) = D % 2 - D := by omega
  have hb : D % 2 = 0 ∨ D % 2 = 1 := by omega
  simp only [principalForm, BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]
  rcases hb with h | h <;> rw [h] at h4 ⊢ <;> nlinarith

/-- **The Hessian determinant of the principal form of discriminant $D$ is $-D$** (so $N(I(S)) = |D|$ in
Theorem 8.6 for $F = \mathbb{Q}$): $\det\begin{pmatrix} 2 & b\\ b & 2c\end{pmatrix} = 4c - b^2 = -D$. -/
theorem det_hessian_principalForm {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (QuadForm.hessian (principalForm D)).det = -D := by
  have h := BinQF.disc_eq_neg_det_hessian (principalForm D)
  rw [disc_principalForm hD] at h
  linarith

/-- **Theorem 8.6 for $F = \mathbb{Q}$** (Dirichlet's class number formula, imaginary quadratic fields).

Paper (Thm. 8.6, p. 36): the class number $h(\mathcal O_K)$ of a CM extension $K/F$ is expressed through
$h(\mathcal O_F)$, $Q_{K/F}$, $|\mu_K|$, $N(I(S))^{1/2}$, $(2\pi)^{[F:\mathbb Q]}$ and $L_F(1,\chi_{K/F})$ (see Remark 8.9).
For $F = \mathbb{Q}$ ($h(\mathbb Z) = 1$, $Q_{K/\mathbb Q} = 1$, $|\Delta_{\mathbb Q}| = 1$, $[F:\mathbb Q] = 1$) it reads
$$h(\mathcal O_K) = |\mu_K|\,\frac{N(I(S))^{1/2}}{2\pi}\,L(1,\chi_D),\qquad N(I(S)) = |D|,$$
for $K = \mathbb{Q}(\sqrt D)$, $D < 0$ a fundamental discriminant, $\chi_D$ the Kronecker character, $S$ the
Hessian-determinant squareclass of the norm form of $\mathcal O_K$. Here $N(I(S))$ is written as the absolute value of the
Hessian determinant of the principal form of discriminant $D$, which equals $|D|$ (`det_hessian_principalForm`).
The specialization of the paper's right-hand side to $F = \mathbb Q$ is the formalization's reading. -/
@[kb "hanke2011structure" "Thm. 8.6, p. 36 (F = ℚ)"]
theorem theorem_8_6_rat {D : ℤ} [IsQuadDisc D] (hD : D < 0) :
    ((classNumber (QField D) : ℝ) : ℂ) =
      ((torsionOrder (QField D) : ℝ) : ℂ) *
        ((Real.sqrt |((QuadForm.hessian (principalForm D)).det : ℝ)| / (2 * Real.pi) : ℝ) : ℂ) *
          (kroneckerChar D).LFunction 1 := by
  have hmod := (IsQuadDisc.fund (D := D)).1
  rw [det_hessian_principalForm hmod, classNumberFormula_neg hD]
  have hDpos : (0 : ℝ) < |(D : ℝ)| := abs_pos.mpr (by exact_mod_cast hD.ne)
  have hw : (0 : ℝ) < torsionOrder (QField D) := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [torsionOrder_of_neg hD]; split_ifs <;> norm_num)
  have hs : 0 < Real.sqrt |(D : ℝ)| := Real.sqrt_pos.mpr hDpos
  rw [Int.cast_neg, abs_neg]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  field_simp

/-! ### Remark 8.9: CM fields -/

section CM

open QuadFormsKB.Binary.Rel

/-- **Remark 8.9** (class number formula for a CM extension), with $K^+$ the maximal totally real subfield (so
$F = K^+$ and $[F:\mathbb Q] = d$).

Paper (Rem. 8.9, p. 37): for $K/F$ a CM extension,
$$h(\mathcal O_K) = h(\mathcal O_F)\,\frac{|\Delta_K|^{1/2}\,Q_{K/F}\,|\mu_K|}{(2\pi)^{[F:\mathbb Q]}\,|\Delta_F|^{1/2}}
\,L_F(1,\chi_{K/F}),$$
where $\Delta_K, \Delta_F$ are the discriminants, $Q_{K/F} = [\mathcal O_K^\times : \mu_K\mathcal O_F^\times] \in \{1,2\}$
is Hasse's unit index (`IsCMField.indexRealUnits`), and $L_F(1,\chi_{K/F}) = \lim_{s\to1^+}L(s,\chi_{K/F})$ is the
value at $1$ of the Euler product (`relLR`), which is only known to converge for $s > 1$. Hence this wrapper is
phrased with the limit: for every real $\ell$ with $L(s,\chi_{K/K^+}) \to \ell$ as $s \to 1^+$,
$h(\mathcal O_K) = h(\mathcal O_{K^+})\,\dfrac{|\Delta_K|^{1/2}\,Q_K\,|\mu_K|}{(2\pi)^{d}\,|\Delta_{K^+}|^{1/2}}\,\ell$,
where `classNumber` is the class number of the ring of integers. Taking $\ell$ to be the limit (which exists, by
`QuadFormsKB.Binary.Rel.relativeClassNumberFormula_hasse`) gives the remark. -/
@[kb "hanke2011structure" "Rem. 8.9, p. 37"]
theorem remark_8_9 (K : Type) [Field K] [NumberField K] [IsCMField K] (ℓ : ℝ)
    (hℓ : Tendsto (relLR (maximalRealSubfield K) K) (𝓝[>] 1) (𝓝 ℓ)) :
    (classNumber K : ℝ) =
      classNumber (maximalRealSubfield K) * Real.sqrt |(discr K : ℝ)| *
        (IsCMField.indexRealUnits K : ℝ) * torsionOrder K /
          ((2 * Real.pi) ^ Module.finrank ℚ (maximalRealSubfield K) *
            Real.sqrt |(discr (maximalRealSubfield K) : ℝ)|) * ℓ := by
  have h := tendsto_nhds_unique hℓ (relativeClassNumberFormula_hasse K)
  rw [h]
  have hQ : (0 : ℝ) < IsCMField.indexRealUnits K := by
    rcases hasseUnitIndex_eq_one_or_two K with h | h <;> rw [h] <;> norm_num
  have h1 : (0 : ℝ) < classNumber (maximalRealSubfield K) := by exact_mod_cast classNumber_pos _
  have h2 : (0 : ℝ) < torsionOrder K := by exact_mod_cast torsionOrder_pos K
  have h3 : 0 < Real.sqrt |(discr K : ℝ)| := Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast discr_ne_zero K))
  have h4 : 0 < Real.sqrt |(discr (maximalRealSubfield K) : ℝ)| :=
    Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast discr_ne_zero _))
  have h5 : (0 : ℝ) < 2 * Real.pi := by positivity
  field_simp

end CM

end QuadFormsKB.Hanke2011Structure
