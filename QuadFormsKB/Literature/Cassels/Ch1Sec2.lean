/-
# Cassels, Chapter 1, §2: representation of a form by a form, $I$-equivalence, determinants

**Setting.** Cassels (Ch. 1, §2, p. 5) takes a ring $I$ (with $1$) inside a field $k$ of characteristic $\ne 2$ and
forms $f$ with coefficients in $k$. Here $k$ is a field, the forms are `QuadForm k n`
($f(\vec x) = \sum_{i \le j} c_{ij}x_ix_j$), and $I$ is a commutative ring $R$ with an algebra map
$R \to k$ (`algebraMap R k`), which Cassels' setting makes injective; injectivity is assumed where it is used.
Indices are $0$-based ($x_0, \dots, x_{n-1}$).

**Matrices.** Cassels writes $f(\vec x) = \vec x' F\vec x$ with $F = (f_{ij})$ symmetric (2.7)–(2.8). The library's
Hessian $H = C + C^{\mathsf T}$ (`QuadForm.hessian`) is $2F$, so Cassels' $d(f) = \det F$ is $2^{-n}\det H$; the
relations (2.9), (2.11)–(2.13) and Lemma 2.1 are stated for $H$, where they read the same (the factor $2$, or $2^n$
for determinants, cancels on both sides). Over $\mathbb Q$, $F$ is `RatQF.gram`.

**Defines**
* `RepresentsFormOver R f g`: $f$ (in $n$ variables) represents $g$ (in $m$ variables) over $I = R$: there is an
  $n \times m$ matrix $B$ over $I$ with $f(B\vec y) = g(\vec y)$ (Cassels (2.4)–(2.6); the columns of $B$ are his
  $\vec b_1, \dots, \vec b_m$);
* `RepresentsOver R f c`: $f(\vec b) = c$ for some $\vec b \in I^n$ (Cassels (2.3));
* `EquivOver R f g`: $I$-equivalence, each of $f, g$ represents the other (p. 5).

**Proves**
* representation of forms is reflexive and transitive, and $f$ represents over $I$ every $c$ represented by $g$
  (`RepresentsFormOver.trans`, `RepresentsFormOver.representsOver`); $I$-equivalence is an equivalence relation and
  equivalent forms represent the same elements (`equivOver_equivalence`, `EquivOver.representsOver_iff`);
* (2.9): $f(B\vec y) = g(\vec y)$ implies $G = B'FB$ (`hessian_eq_of_representsFormOver`); (2.12)–(2.13):
  $d(g) = (\det B)^2 d(f)$ (`det_hessian_eq_of_representsFormOver`); equivalent forms are both singular or both
  regular (`EquivOver.nondegenerate_iff`);
* (2.14)–(2.16): if $f, g$ are regular and $I$-equivalent, every $B$ with $f(B\vec y) = g(\vec y)$ has
  $\det B \in U$, the units of $I$ (`isUnit_det_of_equivOver`);
* Lemma 2.1 (p. 7): regular $f, g$ are $I$-equivalent if and only if $G = B'FB$ for a matrix $B$ over $I$ with
  $\det B \in U$ (`equivOver_iff`);
* the bridge to the library's definitions: for $I = k$, $I$-equivalence of regular forms is `Siegel.IsometricGL`
  (`equivOver_self_iff_isometricGL`); for $I = \mathbb Z \subset k = \mathbb Q$ it is `Siegel.IntEquiv`
  (`intEquiv_iff_equivOver`), and `RepresentsOver` is `QuadForm.RepresentsIn` for forms with coefficients in $I$
  (`representsOver_map_iff`).
-/
import QuadFormsKB.Siegel.Genus

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

open QuadFormsKB.Siegel

section Basic

variable {k : Type*} [Field k] (R : Type*) [CommRing R] [Algebra R k] {n m l : ℕ}

/-- **Representation of a form by a form** (Cassels, Ch. 1, §2, (2.4)–(2.6), p. 5). The form $f$ in $n$ variables
represents the form $g$ in $m$ variables over $I = R$ if there are $\vec b_1, \dots, \vec b_m \in I^n$ with
$$f(y_1\vec b_1 + \cdots + y_m\vec b_m) = g(\vec y),$$
i.e. there is an $n \times m$ matrix $B$ over $I$ (columns $\vec b_j$) with $f(B\vec y) = g(\vec y)$. Cassels asks for
an identity in the variables $\vec y$; here it is required for all $\vec y \in k^m$, which is the same, since a
quadratic form is determined by its values at $\vec e_i$ and $\vec e_i + \vec e_j$. -/
@[kb "cassels1978" "Ch. 1, §2, (2.4)–(2.6), p. 5"]
def RepresentsFormOver (f : QuadForm k n) (g : QuadForm k m) : Prop :=
  ∃ B : Matrix (Fin n) (Fin m) R, ∀ y : Fin m → k, f.eval (B.map (algebraMap R k) *ᵥ y) = g.eval y

/-- **Representation of an element over $I$** (Cassels, Ch. 1, §2, (2.3), p. 5): $f(\vec b) = c$ for some
$\vec b \in I^n$. The form has coefficients in the field $k$ and $c \in k$. For a form with coefficients in $I$ this
is `QuadForm.RepresentsIn` (`representsOver_map_iff`). -/
@[kb "cassels1978" "Ch. 1, §2, (2.3), p. 5"]
def RepresentsOver (f : QuadForm k n) (c : k) : Prop :=
  ∃ b : Fin n → R, f.eval (fun i => algebraMap R k (b i)) = c

/-- **$I$-equivalence** (Cassels, Ch. 1, §2, p. 5): two forms in the same number of variables are equivalent over
$I$ if each represents the other over $I$. -/
@[kb "cassels1978" "Ch. 1, §2, p. 5 (I-equivalence)"]
def EquivOver (f g : QuadForm k n) : Prop := RepresentsFormOver R f g ∧ RepresentsFormOver R g f

variable {R}

theorem RepresentsFormOver.refl (f : QuadForm k n) : RepresentsFormOver R f f :=
  ⟨1, fun y => by simp⟩

/-- Representation of forms is transitive: if $f(B\vec y) = g(\vec y)$ and $g(C\vec z) = h(\vec z)$ then
$f(BC\vec z) = h(\vec z)$. -/
@[kb "cassels1978" "Ch. 1, §2, p. 5 (I-equivalence is transitive)"]
theorem RepresentsFormOver.trans {f : QuadForm k n} {g : QuadForm k m} {h : QuadForm k l}
    (hfg : RepresentsFormOver R f g) (hgh : RepresentsFormOver R g h) : RepresentsFormOver R f h := by
  obtain ⟨B, hB⟩ := hfg
  obtain ⟨C, hC⟩ := hgh
  exact ⟨B * C, fun y => by rw [Matrix.map_mul, ← mulVec_mulVec, hB, hC]⟩

/-- **If $f$ represents $g$ over $I$, then $f$ represents over $I$ every $c \in k$ that $g$ represents over $I$**
(Cassels, Ch. 1, §2, p. 5: "Clearly $f$ represents over $I$ every $c \in k$ which is so represented by $g$"). -/
@[kb "cassels1978" "Ch. 1, §2, p. 5 (f represents what g represents)"]
theorem RepresentsFormOver.representsOver {f : QuadForm k n} {g : QuadForm k m} {c : k}
    (hfg : RepresentsFormOver R f g) (hg : RepresentsOver R g c) : RepresentsOver R f c := by
  obtain ⟨B, hB⟩ := hfg
  obtain ⟨b, hb⟩ := hg
  refine ⟨B *ᵥ b, ?_⟩
  rw [← hb, ← hB]
  congr 1
  ext i
  exact RingHom.map_mulVec (algebraMap R k) B b i

/-- **$I$-equivalence is an equivalence relation** (Cassels, Ch. 1, §2, p. 5). -/
@[kb "cassels1978" "Ch. 1, §2, p. 5 (I-equivalence is an equivalence relation)"]
theorem equivOver_equivalence : Equivalence (EquivOver R (k := k) (n := n)) :=
  ⟨fun f => ⟨.refl f, .refl f⟩, fun h => ⟨h.2, h.1⟩,
    fun h h' => ⟨h.1.trans h'.1, h'.2.trans h.2⟩⟩

/-- **$I$-equivalent forms represent the same elements over $I$** (Cassels, Ch. 1, §2, p. 6). -/
@[kb "cassels1978" "Ch. 1, §2, p. 6 (equivalent forms represent the same elements)"]
theorem EquivOver.representsOver_iff {f g : QuadForm k n} (h : EquivOver R f g) (c : k) :
    RepresentsOver R f c ↔ RepresentsOver R g c :=
  ⟨h.2.representsOver, h.1.representsOver⟩

end Basic

/-! ### Matrices: (2.9)–(2.16) and Lemma 2.1 -/

section Matrices

variable {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra R k] {n m : ℕ}

theorem eval_eq_dotProduct (f : QuadForm k n) (x : Fin n → k) : f.eval x = x ⬝ᵥ (f.coeff *ᵥ x) := by
  rw [QuadForm.eval, QuadForm.evalIn_eq_dotProduct]
  simp

/-- $2f(\vec x) = \vec x' H\vec x$ ($H = 2F$ the Hessian). -/
theorem two_mul_eval (f : QuadForm k n) (x : Fin n → k) : 2 * f.eval x = x ⬝ᵥ (f.hessian *ᵥ x) := by
  rw [eval_eq_dotProduct, QuadForm.hessian, add_mulVec, dotProduct_add, dotProduct_mulVec_transpose_self]
  ring

/-- The polarization identity over $k$: $f(\vec x + \vec y) - f(\vec x) - f(\vec y) = \vec x' H\vec y$. -/
theorem polar_eq (f : QuadForm k n) (x y : Fin n → k) :
    f.eval (x + y) - f.eval x - f.eval y = x ⬝ᵥ (f.hessian *ᵥ y) := by
  have := QuadForm.polar_eq_hessian k f x y
  simpa using this

/-- A matrix is determined by its bilinear form: if $\vec x' M\vec y = \vec x' N\vec y$ for all $\vec x, \vec y$, then
$M = N$. -/
theorem matrix_eq_of_dotProduct {M N : Matrix (Fin m) (Fin m) k}
    (h : ∀ x y : Fin m → k, x ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ (N *ᵥ y)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [mulVec_single_one, single_one_dotProduct] using this

/-- **Cassels (2.9)** (Ch. 1, §2, p. 6): if $f(B\vec y) = g(\vec y)$ then $G = B'FB$; here for the Hessians
$H_g = B'H_fB$ ($H = 2F$). -/
@[kb "cassels1978" "Ch. 1, §2, (2.9)–(2.10), p. 6"]
theorem hessian_eq_of_eval {f : QuadForm k n} {g : QuadForm k m} (B : Matrix (Fin n) (Fin m) k)
    (h : ∀ y, f.eval (B *ᵥ y) = g.eval y) : g.hessian = Bᵀ * f.hessian * B := by
  apply matrix_eq_of_dotProduct
  intro x y
  rw [← polar_eq, ← h, ← h, ← h, mulVec_add, polar_eq, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec x Bᵀ, vecMul_transpose]

/-- **Cassels (2.9)** for a representation over $I$: $H_g = B'H_fB$ with $B$ mapped to $k$. -/
@[kb "cassels1978" "Ch. 1, §2, (2.9), p. 6"]
theorem hessian_eq_of_representsFormOver {f : QuadForm k n} {g : QuadForm k m} {B : Matrix (Fin n) (Fin m) R}
    (h : ∀ y, f.eval (B.map (algebraMap R k) *ᵥ y) = g.eval y) :
    g.hessian = (B.map (algebraMap R k))ᵀ * f.hessian * B.map (algebraMap R k) :=
  hessian_eq_of_eval _ h

/-- **Cassels (2.12)–(2.13)** (Ch. 1, §2, p. 6): if $f(B\vec y) = g(\vec y)$ with $B$ square, then
$d(g) = (\det B)^2 d(f)$; stated for the Hessians, $\det H_g = (\det B)^2\det H_f$ (the factor $2^n$ cancels). -/
@[kb "cassels1978" "Ch. 1, §2, (2.12)–(2.13), p. 6"]
theorem det_hessian_eq_of_representsFormOver {f g : QuadForm k n} {B : Matrix (Fin n) (Fin n) R}
    (h : ∀ y, f.eval (B.map (algebraMap R k) *ᵥ y) = g.eval y) :
    g.hessian.det = (algebraMap R k B.det) ^ 2 * f.hessian.det := by
  have hd : (B.map (algebraMap R k)).det = algebraMap R k B.det := (RingHom.map_det _ B).symm
  rw [hessian_eq_of_representsFormOver h, det_mul, det_mul, det_transpose, hd]
  ring

/-- **Equivalent forms are both singular or both regular** (Cassels, Ch. 1, §2, p. 6, after (2.13)). -/
@[kb "cassels1978" "Ch. 1, §2, p. 6 (singular and regular equivalence classes)"]
theorem EquivOver.nondegenerate_iff {f g : QuadForm k n} (h : EquivOver R f g) :
    f.Nondegenerate ↔ g.Nondegenerate := by
  obtain ⟨⟨B, hB⟩, ⟨C, hC⟩⟩ := h
  have e1 := det_hessian_eq_of_representsFormOver hB
  have e2 := det_hessian_eq_of_representsFormOver hC
  unfold QuadForm.Nondegenerate
  constructor
  · intro hf hg; rw [hg, mul_zero] at e2; exact hf e2
  · intro hg hf; rw [hf, mul_zero] at e1; exact hg e1

/-- **Cassels (2.14)–(2.16)** (Ch. 1, §2, pp. 6–7): if $f, g$ are regular and $I$-equivalent and
$f(B\vec y) = g(\vec y)$ with $B$ over $I$, then $\det B \in U$, the group of units of $I$ (from
$(\det B)^2(\det C)^2 = 1$). Cassels' $I \subseteq k$: `algebraMap R k` is injective. -/
@[kb "cassels1978" "Ch. 1, §2, (2.14)–(2.16), pp. 6–7"]
theorem isUnit_det_of_equivOver (hR : Function.Injective (algebraMap R k)) {f g : QuadForm k n}
    (hf : f.Nondegenerate) (hgf : RepresentsFormOver R g f) {B : Matrix (Fin n) (Fin n) R}
    (hB : ∀ y, f.eval (B.map (algebraMap R k) *ᵥ y) = g.eval y) : IsUnit B.det := by
  obtain ⟨C, hC⟩ := hgf
  have e1 := det_hessian_eq_of_representsFormOver hB
  have e2 := det_hessian_eq_of_representsFormOver hC
  rw [e1] at e2
  have h1 : algebraMap R k (B.det ^ 2 * C.det ^ 2) = algebraMap R k 1 := by
    rw [map_mul, map_pow, map_pow, map_one]
    have hf' : f.hessian.det ≠ 0 := hf
    field_simp at e2
    linear_combination -e2
  have h2 := hR h1
  exact isUnit_iff_exists_inv.2 ⟨B.det * C.det ^ 2, by linear_combination h2⟩

variable [Invertible (2 : k)]

/-- Conversely, $H_g = B'H_fB$ implies $f(B\vec y) = g(\vec y)$ (characteristic $\ne 2$). -/
theorem eval_of_hessian_eq {f : QuadForm k n} {g : QuadForm k m} (B : Matrix (Fin n) (Fin m) k)
    (h : g.hessian = Bᵀ * f.hessian * B) (y : Fin m → k) : f.eval (B *ᵥ y) = g.eval y := by
  have h2 : (2 : k) ≠ 0 := Invertible.ne_zero 2
  apply mul_left_cancel₀ h2
  rw [two_mul_eval, two_mul_eval, h, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y Bᵀ,
    vecMul_transpose]

/-- **Cassels, Ch. 1, Lemma 2.1** (p. 7). Regular forms $f, g$ in $n$ variables are $I$-equivalent if and only if
$G = B'FB$ (2.15) for some matrix $B$ with entries in $I$ and $\det B \in U$ (2.16), $U$ the units of $I$. Stated
with the Hessians $H = 2F$. Here $k$ has characteristic $\ne 2$ and $I \subseteq k$ (`algebraMap R k` injective). -/
@[kb "cassels1978" "Ch. 1, §2, Lemma 2.1, p. 7"]
theorem equivOver_iff (hR : Function.Injective (algebraMap R k)) {f g : QuadForm k n}
    (hf : f.Nondegenerate) :
    EquivOver R f g ↔ ∃ B : Matrix (Fin n) (Fin n) R, IsUnit B.det ∧
      g.hessian = (B.map (algebraMap R k))ᵀ * f.hessian * B.map (algebraMap R k) := by
  constructor
  · rintro ⟨⟨B, hB⟩, hgf⟩
    exact ⟨B, isUnit_det_of_equivOver hR hf hgf hB, hessian_eq_of_representsFormOver hB⟩
  · rintro ⟨B, hB, hG⟩
    refine ⟨⟨B, eval_of_hessian_eq _ hG⟩, ⟨B⁻¹, eval_of_hessian_eq _ ?_⟩⟩
    -- `C = B⁻¹` has entries in `I` and `F = C'GC`
    have hBC : B.map (algebraMap R k) * (B⁻¹).map (algebraMap R k) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hB, Matrix.map_one _ (map_zero _) (map_one _)]
    calc f.hessian = (B.map (algebraMap R k) * (B⁻¹).map (algebraMap R k))ᵀ * f.hessian *
          (B.map (algebraMap R k) * (B⁻¹).map (algebraMap R k)) := by rw [hBC]; simp
      _ = _ := by rw [hG, transpose_mul]; simp only [Matrix.mul_assoc]

end Matrices

/-! ### Bridges to the library's notions -/

section Bridge

variable {k : Type*} [Field k] {n : ℕ}

/-- **For $I = k$, $I$-equivalence of regular forms is $\mathrm{GL}_n(k)$-equivalence** (`Siegel.IsometricGL`). -/
theorem equivOver_self_iff_isometricGL {f g : QuadForm k n} (hf : f.Nondegenerate) :
    EquivOver k f g ↔ IsometricGL f g := by
  constructor
  · rintro ⟨⟨B, hB⟩, hgf⟩
    have hu := isUnit_det_of_equivOver (R := k) (algebraMap k k).injective hf hgf hB
    refine ⟨Matrix.nonsingInvUnit B hu, fun x => ?_⟩
    have := hB x
    change f.eval (B *ᵥ x) = g.eval x
    simpa using this
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨g', hg'⟩ := h
      exact ⟨g'.val, fun y => by simpa using hg' y⟩
    · obtain ⟨g', hg'⟩ := h.symm
      exact ⟨g'.val, fun y => by simpa using hg' y⟩

/-- The value of a base-changed form at an image vector: $(\varphi_*Q)(\varphi(\vec b)) = \varphi(Q(\vec b))$. -/
theorem eval_map_apply {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (Q : QuadForm R n)
    (b : Fin n → R) : (Q.map φ).eval (fun i => φ (b i)) = φ (Q.eval b) := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.map, Matrix.map_apply, Algebra.algebraMap_self,
    RingHom.id_apply, map_sum, apply_ite φ, map_mul, map_zero]

/-- **`RepresentsOver` is `QuadForm.RepresentsIn`** for a form $Q$ with coefficients in $I$ (viewed in $k$) and
$c \in I$, when $I \subseteq k$. -/
theorem representsOver_map_iff {R : Type*} [CommRing R] [Algebra R k]
    (hR : Function.Injective (algebraMap R k)) (Q : QuadForm R n) (c : R) :
    RepresentsOver R (Q.map (algebraMap R k)) (algebraMap R k c) ↔ Q.RepresentsIn R c := by
  constructor
  · rintro ⟨b, hb⟩
    rw [eval_map_apply] at hb
    exact ⟨b, by simpa using hR hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [eval_map_apply]; simpa using congrArg (algebraMap R k) hb⟩

/-- **The library's $\mathbb Z$-equivalence is Cassels' $\mathbb Z$-equivalence** (Ch. 1, §2, p. 5, and Lemma 2.1,
p. 7, with $I = \mathbb Z$, $k = \mathbb Q$): for integral forms $Q, Q'$ with $Q$ regular, `Siegel.IntEquiv Q Q'`
holds if and only if $Q$ and $Q'$ (viewed over $\mathbb Q$) each represent the other over $\mathbb Z$. -/
@[kb "cassels1978" "Ch. 1, §2, p. 5, and Lemma 2.1, p. 7 (I = ℤ, k = ℚ)"]
theorem intEquiv_iff_equivOver {Q Q' : QuadForm ℤ n} (hQ : Q.Nondegenerate) :
    IntEquiv Q Q' ↔ EquivOver ℤ (Q.map (Int.castRingHom ℚ)) (Q'.map (Int.castRingHom ℚ)) := by
  have hφ : algebraMap ℤ ℚ = Int.castRingHom ℚ := algebraMap_int_eq ℚ
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨g, hg⟩ := h
      exact ⟨g.val, fun y => by rw [hφ]; exact eval_mulVec_map _ hg y⟩
    · obtain ⟨g, hg⟩ := IsometricGL.symm h
      exact ⟨g.val, fun y => by rw [hφ]; exact eval_mulVec_map _ hg y⟩
  · rintro ⟨⟨B, hB⟩, hgf⟩
    have hQℚ : (Q.map (Int.castRingHom ℚ)).Nondegenerate := by
      unfold QuadForm.Nondegenerate at hQ ⊢
      have : (Q.map (Int.castRingHom ℚ)).hessian = Q.hessian.map (Int.castRingHom ℚ) := by
        ext i j; simp [QuadForm.hessian, QuadForm.map]
      have hd : (Q.hessian.map (Int.castRingHom ℚ)).det = Int.castRingHom ℚ Q.hessian.det :=
        (RingHom.map_det _ _).symm
      rw [this, hd, eq_intCast]
      exact_mod_cast hQ
    have hu := isUnit_det_of_equivOver (R := ℤ) (algebraMap ℤ ℚ).injective_int hQℚ hgf hB
    refine ⟨Matrix.nonsingInvUnit B hu, fun x => ?_⟩
    change Q.eval (B *ᵥ x) = Q'.eval x
    have := hB (fun i => (x i : ℚ))
    have e : (B.map (algebraMap ℤ ℚ) *ᵥ fun i => (x i : ℚ)) = fun i => Int.castRingHom ℚ ((B *ᵥ x) i) := by
      ext i; rw [hφ]; exact (RingHom.map_mulVec (Int.castRingHom ℚ) B x i).symm
    rw [e, eval_map_apply] at this
    have this' := this.trans (eval_map_apply (Int.castRingHom ℚ) Q' x)
    exact (Int.cast_injective (α := ℚ)) this'

end Bridge

end QuadFormsKB.Cassels
