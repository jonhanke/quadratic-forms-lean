import QuadFormsKB.Binary.ClassBijection

/-!
# Conway–Sloane, Ch. 15, §3.4: normed ideals and the normed ideal class group

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §3.4,
printed pp. 364–365, display (13) (bibliography key `conwaysloane1999`; printed page = PDF page of the chapter file
$+ 351$). The book cites Reiner and Gauss for the background and gives no proofs.

**Setting (the book's).** $d$ is an integer with $-d$ squarefree and $-d \not\equiv 1 \pmod 4$ (`SquarefreeDet`); then
$\mathbb{Z}[\sqrt{-d}] = \{r + s\sqrt{-d} : r, s \in \mathbb{Z}\}$ is the ring of integers of $\mathbb{Q}(\sqrt{-d})$. Here
it is the library's order `Binary.QOrder (4 * -d)` of discriminant $D = -4d$ (`SqrtRing d`): its generator
$\omega$ satisfies $\omega^2 = -d$ (`omega_sq`), so $\omega = \sqrt{-d}$ and `⟨r, s⟩` is $r + s\sqrt{-d}$. Since $-4d$
is a fundamental discriminant (`isQuadDisc`), the ring is a Dedekind domain and the norm of a nonzero ideal is
Mathlib's `Ideal.absNorm` (the index of the ideal). The element norm is $N(r + s\sqrt{-d}) = r^2 + s^2 d$
(`norm_mk`).

**Definitions.**
* `NormedIdeal d`: the book's *normed* (or *oriented*) ideal $\mathcal I_N$: a nonzero ideal $\mathcal I$ (field
  `ideal`) together with an integer $N$ (field `norm`) with $\lvert N\rvert = N(\mathcal I)$ (field `natAbs_norm`) and
  $N \ne 0$ (field `norm_ne_zero`). Each nonzero ideal of norm $N$ thus gives exactly two normed ideals
  $\mathcal I_N$ and $\mathcal I_{-N}$.
* Multiplication (13): $\mathcal I_N \cdot \mathcal J_M = (\mathcal I\mathcal J)_{NM}$ (`mul_ideal`, `mul_norm`), with
  unit $\mathbb{Z}[\sqrt{-d}]_1$; this makes `NormedIdeal d` a commutative monoid.
* `principal α`: the principal normed ideal $\langle\alpha\rangle_{N(\alpha)}$, $N(r + s\sqrt{-d}) = r^2 + s^2 d$ with
  its sign (the book: $\langle r + s\sqrt{-d}\rangle_{r^2+s^2d}$, *not* $\langle r + s\sqrt{-d}\rangle_{-(r^2+s^2d)}$).
* `classCon d`: $\mathcal I \sim \mathcal J$ iff $\mathcal I\mathcal P = \mathcal J\mathcal Q$ for principal normed
  ideals $\mathcal P$, $\mathcal Q$; `NormedClassGroup d` is the quotient, a commutative group (`instCommGroup`).

**Proved.**
* `absNorm_eq_natAbs_odet`: for any $\mathbb{Z}$-basis $\langle r + s\sqrt{-d},\ t + u\sqrt{-d}\rangle$ of a nonzero
  ideal, its norm (index) is $\lvert ru - st\rvert$, the book's definition; `exists_basis`: such a basis exists.
* `absNorm_span_singleton_eq`: the principal ideal $\langle r + s\sqrt{-d}\rangle$ has norm $\lvert r^2 + s^2d\rvert$.
* (13) is well defined (the norm of a product of ideals is the product of the norms), and the normed ideal classes
  form a commutative group (every normed ideal has an inverse class: `exists_mul_eq_principal`).

The correspondence with forms (§3.4, p. 365) is in `NormedIdealsForms.lean`.

**Conventions.** The book's $d$ is the determinant $ac - b^2$ of the form $ax^2 + 2bxy + cy^2$; $D = -4d$ is the
discriminant of the library's forms. Element coordinates: `re` is $r$ and `im` is $s$ in $r + s\sqrt{-d}$.
The library's oriented index `Binary.odet α β` is $\alpha_{\mathrm{im}}\beta_{\mathrm{re}} - \alpha_{\mathrm{re}}\beta_{\mathrm{im}}$,
i.e. $st - ru$ for the basis above (the negative of the book's $ru - st$; only its absolute value enters the norm).
-/

open QuadraticAlgebra
open QuadFormsKB.Binary (QOrder qa qb odet IsQuadDisc formIdeal fα fβ)

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane

/-- **The book's hypothesis on $d$** (Ch. 15, §3.4, p. 364): $-d$ is squarefree (field `squarefree_neg`) and
$-d \not\equiv 1 \pmod 4$ (field `neg_emod_four_ne_one`), so that $\mathbb{Z}[\sqrt{-d}]$ is the full ring of integers
of $\mathbb{Q}(\sqrt{-d})$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 364"]
class SquarefreeDet (d : ℤ) : Prop where
  /-- $-d$ is squarefree. -/
  squarefree_neg : Squarefree (-d)
  /-- $-d \not\equiv 1 \pmod 4$. -/
  neg_emod_four_ne_one : (-d) % 4 ≠ 1

variable {d : ℤ}

/-- Under `SquarefreeDet d`, $-d \equiv 2$ or $3 \pmod 4$ ($4 \nmid -d$ since $-d$ is squarefree). -/
theorem SquarefreeDet.emod_four [h : SquarefreeDet d] : (-d) % 4 = 2 ∨ (-d) % 4 = 3 := by
  have h1 := h.neg_emod_four_ne_one
  have h0 : (-d) % 4 ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
    have := h.squarefree_neg 2 ⟨k, by rw [hk]; ring⟩
    exact absurd (Int.isUnit_iff.mp this) (by omega)
  omega

/-- **$-4d$ is a fundamental discriminant** when $-d$ is squarefree and $\not\equiv 1 \pmod 4$
(Mathlib's `Int.isFundamentalDiscr_four_mul`). -/
instance SquarefreeDet.isQuadDisc [h : SquarefreeDet d] : IsQuadDisc (4 * -d) where
  fund := Int.isFundamentalDiscr_four_mul.mpr ⟨h.squarefree_neg, SquarefreeDet.emod_four⟩
  ne_one := by omega

/-- **The ring $\mathbb{Z}[\sqrt{-d}]$** (Ch. 15, §3.4, p. 364): the library's order `Binary.QOrder (4 * -d)`, i.e.
`QuadraticAlgebra ℤ (qa (-4d)) (qb (-4d))` with $\omega^2 = -d$ (`omega_sq`). The element `⟨r, s⟩` is
$r + s\sqrt{-d}$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 364"]
abbrev SqrtRing (d : ℤ) : Type := QOrder (4 * -d)

theorem qa_eq : qa (4 * -d) = -d := by unfold Binary.qa; omega

theorem qb_eq : qb (4 * -d) = 0 := by unfold Binary.qb; omega

/-- $\omega^2 = -d$ in `SqrtRing d`: $\omega = \sqrt{-d}$. -/
theorem omega_sq : (ω : SqrtRing d) * ω = ((-d : ℤ) : SqrtRing d) := by
  ext
  · rw [re_mul, re_omega, im_omega, re_intCast, qa_eq, Int.cast_id]; ring
  · rw [im_mul, re_omega, im_omega, im_intCast, qb_eq]; ring

/-- **The norm of $r + s\sqrt{-d}$ is $r^2 + s^2 d$** (Ch. 15, §3.4, p. 364). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 364"]
theorem norm_mk (r s : ℤ) : QuadraticAlgebra.norm (⟨r, s⟩ : SqrtRing d) = r ^ 2 + s ^ 2 * d := by
  rw [QuadraticAlgebra.norm_def, qa_eq, qb_eq]; ring

/-- The algebra norm of `SqrtRing d` over $\mathbb{Z}$ is the quadratic norm. -/
theorem algebraNorm_eq (z : SqrtRing d) : Algebra.norm ℤ z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply]; exact det_toLinearMap_eq_norm z

variable [SquarefreeDet d]

/-- **The norm of a principal ideal** (Ch. 15, §3.4, p. 364): $N(\langle r + s\sqrt{-d}\rangle) = \lvert r^2 + s^2d\rvert$;
in general $N(\langle\alpha\rangle) = \lvert N(\alpha)\rvert$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 364"]
theorem absNorm_span_singleton_eq (α : SqrtRing d) :
    Ideal.absNorm (Ideal.span {α}) = (QuadraticAlgebra.norm α).natAbs := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq]

/-- The norm of the principal ideal $\langle C\rangle$ of an integer $C$ is $C^2$. -/
theorem absNorm_span_intCast (C : ℤ) : Ideal.absNorm (Ideal.span {(C : SqrtRing d)}) = (C ^ 2).natAbs := by
  rw [absNorm_span_singleton_eq, norm_intCast, Int.cast_id]

/-! ### Bases and the norm $\lvert ru - st\rvert$ -/

/-- **Every nonzero ideal of $\mathbb{Z}[\sqrt{-d}]$ has a two-member $\mathbb{Z}$-basis** (Ch. 15, §3.4, p. 364):
$\mathcal I = \mathbb{Z}\alpha + \mathbb{Z}\beta$ with $\alpha, \beta$ linearly independent ($\operatorname{odet} \ne 0$).
From the Hermite normal form `Binary.exists_eq_span_mul_formIdeal`. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 364"]
theorem exists_basis (J : Ideal (SqrtRing d)) (hJ : J ≠ ⊥) :
    ∃ α β : SqrtRing d, (∀ z, z ∈ J ↔ ∃ x y : ℤ, z = x • α + y • β) ∧ odet α β ≠ 0 := by
  obtain ⟨C, f, hC, hf, ha, hJC⟩ := Binary.exists_eq_span_mul_formIdeal J hJ
  refine ⟨(C : SqrtRing d) * fα _ f, (C : SqrtRing d) * fβ _ f, fun z => ?_, ?_⟩
  · rw [hJC, Binary.mem_span_mul_formIdeal_iff hf]
  · rw [Binary.odet_mul, Binary.odet_fα_fβ hf]
    exact mul_ne_zero (Binary.norm_ne_zero (by exact_mod_cast hC.ne')) ha.ne'

/-- **The norm of an ideal is $\lvert ru - st\rvert$** (Ch. 15, §3.4, p. 364): if
$\mathcal I = \langle r + s\sqrt{-d},\ t + u\sqrt{-d}\rangle$ as a $\mathbb{Z}$-module (a $\mathbb{Z}$-basis
$(\alpha, \beta)$), then its index $N(\mathcal I)$ (`Ideal.absNorm`) is $\lvert ru - st\rvert = \lvert\operatorname{odet}(\alpha,
\beta)\rvert$. *Proof:* by the Hermite normal form $\mathcal I = C\mathfrak a_f$, whose basis $(Ca, C(k_f - \omega))$
has oriented index $C^2a$ and norm $C^2 a$; any other basis differs by a matrix of determinant $\pm 1$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 364"]
theorem absNorm_eq_natAbs_odet (J : Ideal (SqrtRing d)) {α β : SqrtRing d}
    (hb : ∀ z, z ∈ J ↔ ∃ x y : ℤ, z = x • α + y • β) (hn : odet α β ≠ 0) :
    Ideal.absNorm J = (α.re * β.im - α.im * β.re).natAbs := by
  have hJ : J ≠ ⊥ := by
    intro h
    have : α ∈ J := (hb α).mpr ⟨1, 0, by simp⟩
    rw [h, Ideal.mem_bot] at this
    exact Binary.ne_zero_of_odet hn this
  obtain ⟨C, f, hC, hf, ha, hJC⟩ := Binary.exists_eq_span_mul_formIdeal J hJ
  have hn0 : odet ((C : SqrtRing d) * fα _ f) ((C : SqrtRing d) * fβ _ f) = C ^ 2 * f.a := by
    rw [Binary.odet_mul, Binary.odet_fα_fβ hf, norm_intCast, Int.cast_id]
  have hlat : ∀ z, (∃ x y : ℤ, z = x • ((C : SqrtRing d) * fα _ f) + y • ((C : SqrtRing d) * fβ _ f)) ↔
      (∃ x y : ℤ, z = x • α + y • β) := fun z => by
    rw [← hb, hJC, Binary.mem_span_mul_formIdeal_iff hf]
  obtain ⟨p, q, r, s, -, -, e, hd⟩ := Binary.exists_basis_change hlat
    (by rw [hn0]; exact mul_ne_zero (pow_ne_zero _ hC.ne') ha.ne')
  have hnorm : Ideal.absNorm J = (C ^ 2 * f.a).natAbs := by
    rw [hJC, map_mul, absNorm_span_intCast, Binary.absNorm_formIdeal hf ha.ne', Int.natAbs_mul]
  rw [hnorm, ← hn0]
  have e' : α.re * β.im - α.im * β.re = -odet α β := by simp only [odet]; ring
  rw [e', Int.natAbs_neg, e]
  rcases hd with hd | hd
  · rw [hd, one_mul]
  · rw [hd, neg_one_mul, Int.natAbs_neg]

/-! ### Normed ideals -/

/-- **A normed (oriented) ideal** $\mathcal I_N$ (Ch. 15, §3.4, p. 364): a nonzero ideal $\mathcal I$ of
$\mathbb{Z}[\sqrt{-d}]$ (field `ideal`) together with a nonzero integer $N$ (field `norm`, sign included) with
$\lvert N\rvert = N(\mathcal I)$ (field `natAbs_norm`; `Ideal.absNorm` is the index) and $N \ne 0$ (field
`norm_ne_zero`, which also forces $\mathcal I \ne 0$). An ideal of norm $N$ corresponds to the two normed ideals
$\mathcal I_N$ and $\mathcal I_{-N}$ (`exists_normedIdeal_iff`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 364", ext]
structure NormedIdeal (d : ℤ) [SquarefreeDet d] where
  /-- The underlying ideal $\mathcal I$. -/
  ideal : Ideal (SqrtRing d)
  /-- The signed norm $N$. -/
  norm : ℤ
  /-- $\lvert N\rvert = N(\mathcal I)$. -/
  natAbs_norm : norm.natAbs = Ideal.absNorm ideal
  /-- $N \ne 0$. -/
  norm_ne_zero : norm ≠ 0

namespace NormedIdeal

theorem ideal_ne_bot (I : NormedIdeal d) : I.ideal ≠ ⊥ := by
  intro h
  have := I.natAbs_norm
  rw [h, Ideal.absNorm_bot] at this
  exact I.norm_ne_zero (Int.natAbs_eq_zero.mp this)

/-- **Exactly two normed ideals over each nonzero ideal** (Ch. 15, §3.4, p. 364): $\mathcal I_N$ exists iff
$N = \pm N(\mathcal I)$ and $\mathcal I \ne 0$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 364"]
theorem exists_normedIdeal_iff (J : Ideal (SqrtRing d)) (N : ℤ) :
    (∃ I : NormedIdeal d, I.ideal = J ∧ I.norm = N) ↔
      J ≠ ⊥ ∧ (N = Ideal.absNorm J ∨ N = -(Ideal.absNorm J : ℤ)) := by
  constructor
  · rintro ⟨I, rfl, rfl⟩
    refine ⟨I.ideal_ne_bot, ?_⟩
    rw [← I.natAbs_norm]
    exact Int.natAbs_eq I.norm
  · rintro ⟨hJ, hN⟩
    have h0 : Ideal.absNorm J ≠ 0 := fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)
    refine ⟨⟨J, N, ?_, ?_⟩, rfl, rfl⟩
    · rcases hN with rfl | rfl <;> simp
    · rcases hN with rfl | rfl <;> simpa using h0

/-- **Multiplication of normed ideals** (Ch. 15, §3.4, (13), p. 365): $\mathcal I_N\,\mathcal J_M =
(\mathcal I\mathcal J)_{NM}$; well defined since $N(\mathcal I\mathcal J) = N(\mathcal I)N(\mathcal J)$
(`Ideal.absNorm` is multiplicative). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, (13), p. 365"]
instance : Mul (NormedIdeal d) where
  mul I J := ⟨I.ideal * J.ideal, I.norm * J.norm,
    by rw [Int.natAbs_mul, I.natAbs_norm, J.natAbs_norm, map_mul],
    mul_ne_zero I.norm_ne_zero J.norm_ne_zero⟩

/-- The unit normed ideal $\mathbb{Z}[\sqrt{-d}]_1$. -/
instance : One (NormedIdeal d) where
  one := ⟨⊤, 1, by rw [Ideal.absNorm_top, Int.natAbs_one], one_ne_zero⟩

/-- (13), ideal part: the ideal of $\mathcal I_N\mathcal J_M$ is $\mathcal I\mathcal J$. -/
@[simp] theorem mul_ideal (I J : NormedIdeal d) : (I * J).ideal = I.ideal * J.ideal := rfl

/-- (13), norm part: the signed norm of $\mathcal I_N\mathcal J_M$ is $NM$. -/
@[simp] theorem mul_norm (I J : NormedIdeal d) : (I * J).norm = I.norm * J.norm := rfl

@[simp] theorem one_ideal : (1 : NormedIdeal d).ideal = ⊤ := rfl

@[simp] theorem one_norm : (1 : NormedIdeal d).norm = 1 := rfl

/-- **Normed ideals form a commutative monoid under (13)** (Ch. 15, §3.4, (13), p. 365). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, (13), p. 365"]
instance instCommMonoid : CommMonoid (NormedIdeal d) where
  mul_assoc I J K := NormedIdeal.ext (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul I := NormedIdeal.ext (Ideal.top_mul _) (one_mul _)
  mul_one I := NormedIdeal.ext (Ideal.mul_top _) (mul_one _)
  mul_comm I J := NormedIdeal.ext (mul_comm _ _) (mul_comm _ _)

/-! ### Principal normed ideals -/

/-- **The principal normed ideal** $\langle\alpha\rangle_{N(\alpha)}$ (Ch. 15, §3.4, p. 364): for
$\alpha = r + s\sqrt{-d} \ne 0$, the ideal $\langle\alpha\rangle$ with the signed norm $N(\alpha) = r^2 + s^2 d$
(`norm_mk`), not $-(r^2 + s^2d)$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 364"]
noncomputable def principal (α : SqrtRing d) (hα : α ≠ 0) : NormedIdeal d :=
  ⟨Ideal.span {α}, QuadraticAlgebra.norm α, (absNorm_span_singleton_eq α).symm, Binary.norm_ne_zero hα⟩

@[simp] theorem principal_ideal (α : SqrtRing d) (hα : α ≠ 0) : (principal α hα).ideal = Ideal.span {α} := rfl

@[simp] theorem principal_norm (α : SqrtRing d) (hα : α ≠ 0) :
    (principal α hα).norm = QuadraticAlgebra.norm α := rfl

/-- $\langle\alpha\rangle_{N(\alpha)}\langle\beta\rangle_{N(\beta)} = \langle\alpha\beta\rangle_{N(\alpha\beta)}$. -/
theorem principal_mul {α β : SqrtRing d} (hα : α ≠ 0) (hβ : β ≠ 0) :
    principal α hα * principal β hβ = principal (α * β) (mul_ne_zero hα hβ) :=
  NormedIdeal.ext (by simp [Ideal.span_singleton_mul_span_singleton]) (by simp)

theorem principal_one : principal (1 : SqrtRing d) one_ne_zero = 1 :=
  NormedIdeal.ext (by simp) (by simp)

/-- **The submonoid of principal normed ideals** $\{\langle\alpha\rangle_{N(\alpha)} : \alpha \ne 0\}$. -/
def principals (d : ℤ) [SquarefreeDet d] : Submonoid (NormedIdeal d) where
  carrier := {I | ∃ α : SqrtRing d, ∃ hα : α ≠ 0, I = principal α hα}
  mul_mem' := by
    rintro _ _ ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩
    exact ⟨α * β, mul_ne_zero hα hβ, principal_mul hα hβ⟩
  one_mem' := ⟨1, one_ne_zero, principal_one.symm⟩

theorem principal_mem (α : SqrtRing d) (hα : α ≠ 0) : principal α hα ∈ principals d := ⟨α, hα, rfl⟩

/-! ### The normed ideal class group -/

/-- **Same normed ideal class** (Ch. 15, §3.4, p. 365): $\mathcal I \sim \mathcal J$ iff
$\mathcal I\mathcal P = \mathcal J\mathcal Q$ for some principal normed ideals $\mathcal P$, $\mathcal Q$; a congruence
for (13). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 365"]
def classCon (d : ℤ) [SquarefreeDet d] : Con (NormedIdeal d) where
  r I J := ∃ P ∈ principals d, ∃ Q ∈ principals d, I * P = J * Q
  iseqv := by
    refine ⟨fun I => ⟨1, one_mem _, 1, one_mem _, rfl⟩, ?_, ?_⟩
    · rintro I J ⟨P, hP, Q, hQ, h⟩; exact ⟨Q, hQ, P, hP, h.symm⟩
    · rintro I J K ⟨P, hP, Q, hQ, h⟩ ⟨P', hP', Q', hQ', h'⟩
      refine ⟨P * P', mul_mem hP hP', Q * Q', mul_mem hQ hQ', ?_⟩
      calc I * (P * P') = (I * P) * P' := by rw [mul_assoc]
        _ = (J * P') * Q := by rw [h]; ac_rfl
        _ = K * (Q * Q') := by rw [h']; ac_rfl
  mul' := by
    rintro I J I' J' ⟨P, hP, Q, hQ, h⟩ ⟨P', hP', Q', hQ', h'⟩
    refine ⟨P * P', mul_mem hP hP', Q * Q', mul_mem hQ hQ', ?_⟩
    calc I * I' * (P * P') = (I * P) * (I' * P') := by ac_rfl
      _ = (J * Q) * (J' * Q') := by rw [h, h']
      _ = J * J' * (Q * Q') := by ac_rfl

/-- **The normed ideal class group** (Ch. 15, §3.4, p. 365): normed ideals modulo `classCon`, with the
multiplication induced by (13). A commutative group (`instCommGroup`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 365"]
abbrev _root_.QuadFormsKB.ConwaySloane.NormedClassGroup (d : ℤ) [SquarefreeDet d] : Type :=
  (classCon d).Quotient

/-- A principal normed ideal is in the unit class. -/
theorem classCon_principal (α : SqrtRing d) (hα : α ≠ 0) : classCon d (principal α hα) 1 :=
  ⟨1, one_mem _, principal α hα, principal_mem α hα, by rw [mul_one, one_mul]⟩

/-- **Every normed ideal has an inverse up to a principal one:** $\mathcal I_N\mathcal J_M = \langle\gamma\rangle_{N(\gamma)}$
for some normed $\mathcal J_M$ and some $\gamma \neq 0$. *Proof:* write $\mathcal I = C\mathfrak a_f$
(Hermite normal form); then $\mathcal I \cdot C\mathfrak a_{\bar f} = \langle C^2 a\rangle$ (`Binary.formIdeal_conj_mul`),
and $M = \operatorname{sign}(N)\,C^2a$ makes the norms match: $NM = (C^2a)^2 = N(C^2a)$. -/
theorem exists_mul_eq_principal (I : NormedIdeal d) :
    ∃ (J : NormedIdeal d) (γ : SqrtRing d) (hγ : γ ≠ 0), I * J = principal γ hγ := by
  obtain ⟨C, f, hC, hf, ha, hJC⟩ := Binary.exists_eq_span_mul_formIdeal I.ideal I.ideal_ne_bot
  have hp := Binary.isPrimitive_of_fund (IsQuadDisc.fund (D := 4 * -d)) hf
  set K : Ideal (SqrtRing d) := Ideal.span {(C : SqrtRing d)} * formIdeal _ (Binary.conjForm f)
  have hfc : (Binary.conjForm f).disc = 4 * -d := by rw [Binary.disc_conjForm, hf]
  have hKn : Ideal.absNorm K = C ^ 2 * f.a := by
    rw [map_mul, absNorm_span_intCast, Binary.absNorm_formIdeal hfc (by simpa using ha.ne')]
    simp only [Binary.a_conjForm]; push_cast
    rw [abs_of_nonneg (by positivity), abs_of_nonneg ha.le]
  have hIn : (Ideal.absNorm I.ideal : ℤ) = C ^ 2 * f.a := by
    rw [hJC, map_mul, absNorm_span_intCast, Binary.absNorm_formIdeal hf ha.ne']; push_cast
    rw [abs_of_nonneg (by positivity), abs_of_nonneg ha.le]
  have hCa : C ^ 2 * f.a ≠ 0 := mul_ne_zero (pow_ne_zero _ hC.ne') ha.ne'
  have hγ : ((C ^ 2 * f.a : ℤ) : SqrtRing d) ≠ 0 := by exact_mod_cast hCa
  refine ⟨⟨K, I.norm.sign * (C ^ 2 * f.a), ?_, ?_⟩, _, hγ, ?_⟩
  · rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero I.norm_ne_zero, one_mul, ← Int.natCast_inj, hKn,
      Int.natAbs_of_nonneg (by positivity)]
  · exact mul_ne_zero (fun h => I.norm_ne_zero (Int.sign_eq_zero_iff_zero.mp h)) hCa
  · refine NormedIdeal.ext ?_ ?_
    · simp only [mul_ideal, principal_ideal]
      rw [hJC]
      calc Ideal.span {(C : SqrtRing d)} * formIdeal _ f * K
          = Ideal.span {(C : SqrtRing d)} * Ideal.span {(C : SqrtRing d)} *
              (formIdeal _ (Binary.conjForm f) * formIdeal _ f) := by ring
        _ = _ := by
          rw [Binary.formIdeal_conj_mul hf hp, Ideal.span_singleton_mul_span_singleton,
            Ideal.span_singleton_mul_span_singleton]
          push_cast; ring_nf
    · simp only [mul_norm, principal_norm]
      have h1 : I.norm * I.norm.sign = (Ideal.absNorm I.ideal : ℤ) := by
        rw [Int.mul_sign_self, ← I.natAbs_norm, Int.natCast_natAbs]
      rw [← mul_assoc, h1, hIn, norm_intCast, Int.cast_id]; ring

/-- **The normed ideal classes form a commutative group** (Ch. 15, §3.4, p. 365). -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 365"]
theorem isUnit_classes (x : NormedClassGroup d) : IsUnit x := by
  induction x using Con.induction_on with
  | H I =>
    obtain ⟨J, γ, hγ, h⟩ := exists_mul_eq_principal I
    refine isUnit_iff_exists_inv.mpr ⟨(J : NormedClassGroup d), ?_⟩
    rw [← Con.coe_mul, h]
    exact (Con.eq _).mpr (classCon_principal γ hγ)

end NormedIdeal

/-- **The normed ideal class group is a commutative group** (Ch. 15, §3.4, p. 365): the inverse of the class of
$\mathcal I_N$ is the class of any $\mathcal J_M$ with $\mathcal I_N\mathcal J_M$ principal. -/
@[kb "conwaysloane1999" "Ch. 15, §3.4, p. 365"]
noncomputable instance NormedClassGroup.instCommGroup : CommGroup (NormedClassGroup d) where
  inv x := ((NormedIdeal.isUnit_classes x).unit⁻¹ : (NormedClassGroup d)ˣ)
  inv_mul_cancel x := (NormedIdeal.isUnit_classes x).val_inv_mul

end QuadFormsKB.ConwaySloane
