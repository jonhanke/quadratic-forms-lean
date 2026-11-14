/-
# Octonion algebras by Cayley–Dickson doubling

The defining algebra of the exceptional group $G_2$ (`Tamagawa/Exceptional/G2.lean`): for a commutative
ring $R$ and $a, b, c \in R$, the **octonion algebra** $\mathbb O = (a, b, c)_R$ is the Cayley–Dickson double of
the quaternion algebra $D = (a,b)_R$ = `ℍ[R,a,b]` ($i^2 = a$, $j^2 = b$, $ij = -ji$; Mathlib's
`QuaternionAlgebra R a 0 b`) with parameter $c$: the $R$-module $D\times D$ with the product
$$(p, q)(r, s) = (pr + c\,\bar s q,\ sp + q\bar r),$$
where $\bar{\ }$ is the standard involution of $D$ (Mathlib's `star`). Writing $\ell = (0, 1)$, an element is
$x = p + q\ell$ and $\ell^2 = c$. This is the convention of Springer–Veldkamp 2000, §1.5 [unverified locator].

**Contents.**
* `Octonion R a b c`, its $R$-module structure, the product, the unit $1 = (1, 0)$, the conjugation
  $\overline{(p,q)} = (\bar p, -q)$, the trace $T(x) = x + \bar x = 2\operatorname{re}(p)$ (`Octonion.trace`) and
  the norm $N(p, q) = \operatorname{nrd}(p) - c\operatorname{nrd}(q)$ (`Octonion.norm`); over a field
  $\operatorname{nrd}$ is the library's `Quat.nrd` (`Octonion.norm_eq_nrd`).
* $x\bar x = \bar x x = N(x)$ (`mul_conj`, `conj_mul`), the quadratic equation $x^2 - T(x)x + N(x) = 0$
  (`sq_eq`), and $\overline{xy} = \bar y\bar x$ (`conj_mul_conj`).
* **The composition law** $N(xy) = N(x)N(y)$ (`norm_mul`).
* **Alternativity**: $x(xy) = (xx)y$ and $(yx)x = y(xx)$ (`mul_mul_self_left`, `mul_self_mul_right`); flexibility
  $(xy)x = x(yx)$ (`flexible`).
* The norm form in the coordinates $p = x_0 + x_1 i + x_2 j + x_3 k$, $q = x_4 + x_5 i + x_6 j + x_7 k$ is the
  3-fold Pfister form $\langle 1, -a, -b, ab, -c, ac, bc, -abc\rangle$ (`norm_eq_coords`); on the trace-zero
  part ($x_0 = 0$) it is $\langle -a, -b, ab, -c, ac, bc, -abc\rangle$.

All identities are proved over an arbitrary commutative ring by expanding in coordinates; nothing is
assumed about $2$ or about $a, b, c$.

Sources: Springer–Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups* (2000), Ch. 1 [unverified
locators]; Schafer, *An Introduction to Nonassociative Algebras* (1966), Ch. III.4 [unverified].
-/
import QuadFormsKB.Tamagawa.Quaternion

open Quaternion

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

namespace QuadFormsKB.Exceptional

/-- **The octonion algebra** $(a, b, c)_R$: the Cayley–Dickson double of the quaternion algebra
$(a, b)_R$ = `ℍ[R,a,b]` with parameter $c$. An element is a pair $(p, q)$ of quaternions, written
$p + q\ell$ with $\ell^2 = c$; the fields are `fst` $= p$ and `snd` $= q$. The product is
$(p, q)(r, s) = (pr + c\,\bar s q,\ sp + q\bar r)$ (`Octonion.fst_mul`, `Octonion.snd_mul`).

Source: Springer–Veldkamp 2000, §1.5 [unverified locator]. -/
@[kb "springerveldkamp2000" "§1.5"]
structure Octonion (R : Type*) [CommRing R] (a b c : R) where
  /-- The first quaternion coordinate $p$ of $p + q\ell$. -/
  fst : ℍ[R,a,b]
  /-- The second quaternion coordinate $q$ of $p + q\ell$. -/
  snd : ℍ[R,a,b]

namespace Octonion

variable {R : Type*} [CommRing R] {a b c : R}

@[ext]
theorem ext {x y : Octonion R a b c} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y := by
  cases x; cases y; simp_all

instance : Zero (Octonion R a b c) := ⟨⟨0, 0⟩⟩
instance : One (Octonion R a b c) := ⟨⟨1, 0⟩⟩
instance : Add (Octonion R a b c) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (Octonion R a b c) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance : Sub (Octonion R a b c) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance {S : Type*} [SMul S ℍ[R,a,b]] : SMul S (Octonion R a b c) := ⟨fun r x => ⟨r • x.fst, r • x.snd⟩⟩

/-- The Cayley–Dickson product $(p, q)(r, s) = (pr + c\,\bar s q,\ sp + q\bar r)$. -/
instance : Mul (Octonion R a b c) :=
  ⟨fun x y => ⟨x.fst * y.fst + c • (star y.snd * x.snd), y.snd * x.fst + x.snd * star y.fst⟩⟩

@[simp] theorem fst_zero : (0 : Octonion R a b c).fst = 0 := rfl
@[simp] theorem snd_zero : (0 : Octonion R a b c).snd = 0 := rfl
@[simp] theorem fst_one : (1 : Octonion R a b c).fst = 1 := rfl
@[simp] theorem snd_one : (1 : Octonion R a b c).snd = 0 := rfl
@[simp] theorem fst_add (x y : Octonion R a b c) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_add (x y : Octonion R a b c) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem fst_neg (x : Octonion R a b c) : (-x).fst = -x.fst := rfl
@[simp] theorem snd_neg (x : Octonion R a b c) : (-x).snd = -x.snd := rfl
@[simp] theorem fst_sub (x y : Octonion R a b c) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem snd_sub (x y : Octonion R a b c) : (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem fst_smul {S : Type*} [SMul S ℍ[R,a,b]] (r : S) (x : Octonion R a b c) :
    (r • x).fst = r • x.fst := rfl
@[simp] theorem snd_smul {S : Type*} [SMul S ℍ[R,a,b]] (r : S) (x : Octonion R a b c) :
    (r • x).snd = r • x.snd := rfl
@[simp] theorem fst_mul (x y : Octonion R a b c) :
    (x * y).fst = x.fst * y.fst + c • (star y.snd * x.snd) := rfl
@[simp] theorem snd_mul (x y : Octonion R a b c) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

/-- The pair map, injective; used to transfer the module structure from $D\times D$. -/
def toProd (x : Octonion R a b c) : ℍ[R,a,b] × ℍ[R,a,b] := (x.fst, x.snd)

theorem toProd_injective : Function.Injective (toProd : Octonion R a b c → _) := by
  intro x y h; simp only [toProd, Prod.mk.injEq] at h; exact ext h.1 h.2

instance : AddCommGroup (Octonion R a b c) :=
  toProd_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The pair map as an additive homomorphism. -/
def toProdHom : Octonion R a b c →+ ℍ[R,a,b] × ℍ[R,a,b] where
  toFun := toProd
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module R (Octonion R a b c) :=
  toProd_injective.module R toProdHom (fun _ _ => rfl)

/-- **Conjugation** $\overline{(p, q)} = (\bar p, -q)$. -/
@[kb "springerveldkamp2000" "§1.5"]
def conj (x : Octonion R a b c) : Octonion R a b c := ⟨star x.fst, -x.snd⟩

@[simp] theorem fst_conj (x : Octonion R a b c) : (conj x).fst = star x.fst := rfl
@[simp] theorem snd_conj (x : Octonion R a b c) : (conj x).snd = -x.snd := rfl

/-- The scalar embedding $R\to\mathbb O$, $t\mapsto t\cdot 1 = (t, 0)$. -/
def scalar (t : R) : Octonion R a b c := ⟨(t : ℍ[R,a,b]), 0⟩

@[simp] theorem fst_scalar (t : R) : (scalar t : Octonion R a b c).fst = t := rfl
@[simp] theorem snd_scalar (t : R) : (scalar t : Octonion R a b c).snd = 0 := rfl

/-- **The trace** $T(p + q\ell) = \operatorname{trd}(p) = 2\operatorname{re}(p)$, so that $x + \bar x = T(x)$
(`add_conj`). -/
@[kb "springerveldkamp2000" "§1.3"]
def trace (x : Octonion R a b c) : R := 2 * x.fst.re

/-- **The norm** $N(p + q\ell) = \operatorname{nrd}(p) - c\operatorname{nrd}(q)$, with
$\operatorname{nrd}(p) = p\bar p$ $= p_0^2 - a p_1^2 - b p_2^2 + ab\,p_3^2$ (taken as the real part of
$p\bar p$, so that it makes sense over any commutative ring; over a field it is `Quat.nrd`,
`norm_eq_nrd`). -/
@[kb "springerveldkamp2000" "§1.5"]
def norm (x : Octonion R a b c) : R := (x.fst * star x.fst).re - c * (x.snd * star x.snd).re

/-- The norm in coordinates: the 3-fold Pfister form $\langle 1,-a,-b,ab,-c,ac,bc,-abc\rangle$ in
$x_0, \dots, x_7$ (0-based: $p = x_0 + x_1 i + x_2 j + x_3 k$, $q = x_4 + x_5 i + x_6 j + x_7 k$). -/
@[kb "springerveldkamp2000" "§1.10"]
theorem norm_eq_coords (x : Octonion R a b c) :
    norm x = x.fst.re ^ 2 - a * x.fst.imI ^ 2 - b * x.fst.imJ ^ 2 + a * b * x.fst.imK ^ 2
      - c * (x.snd.re ^ 2 - a * x.snd.imI ^ 2 - b * x.snd.imJ ^ 2 + a * b * x.snd.imK ^ 2) := by
  simp only [norm, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
  ring

/-- Over a field the quaternion part of the norm is the library's reduced norm `Quat.nrd`. -/
theorem norm_eq_nrd {K : Type*} [Field K] {a b c : K} (x : Octonion K a b c) :
    norm x = Quat.nrd x.fst - c * Quat.nrd x.snd := by
  rw [norm_eq_coords]; simp only [Quat.nrd]

/-- Expand octonion identities into the 8 coordinates of each argument. -/
syntax "oct_coords" (ppSpace Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| oct_coords $[$loc]?) =>
  `(tactic| (simp only [fst_mul, snd_mul, fst_add, snd_add, fst_sub, snd_sub, fst_neg, snd_neg,
      fst_smul, snd_smul, fst_conj, snd_conj, fst_one, snd_one, fst_zero, snd_zero, fst_scalar,
      snd_scalar, smul_eq_mul, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star,
      QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star,
      QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub,
      QuaternionAlgebra.imJ_sub, QuaternionAlgebra.imK_sub, QuaternionAlgebra.re_neg,
      QuaternionAlgebra.imI_neg, QuaternionAlgebra.imJ_neg, QuaternionAlgebra.imK_neg,
      QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
      QuaternionAlgebra.imK_smul, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one,
      QuaternionAlgebra.imJ_one, QuaternionAlgebra.imK_one, QuaternionAlgebra.re_zero,
      QuaternionAlgebra.imI_zero, QuaternionAlgebra.imJ_zero, QuaternionAlgebra.imK_zero,
      QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
      QuaternionAlgebra.imK_coe, norm, trace] $[$loc]?))

/-- Prove an octonion identity coordinatewise by `ring`. -/
macro "oct_ring" : tactic =>
  `(tactic| (ext <;> oct_coords <;> ring))

theorem smul_eq_scalar_mul (t : R) (x : Octonion R a b c) : t • x = scalar t * x := by oct_ring

theorem scalar_one : (scalar 1 : Octonion R a b c) = 1 := by oct_ring

theorem one_mul (x : Octonion R a b c) : 1 * x = x := by oct_ring

theorem mul_one (x : Octonion R a b c) : x * 1 = x := by oct_ring

theorem mul_add (x y z : Octonion R a b c) : x * (y + z) = x * y + x * z := by oct_ring

theorem add_mul (x y z : Octonion R a b c) : (x + y) * z = x * z + y * z := by oct_ring

theorem mul_smul (t : R) (x y : Octonion R a b c) : x * (t • y) = t • (x * y) := by oct_ring

theorem smul_mul (t : R) (x y : Octonion R a b c) : (t • x) * y = t • (x * y) := by oct_ring

/-- **$x + \bar x = T(x)$.** -/
@[kb "springerveldkamp2000" "§1.3"]
theorem add_conj (x : Octonion R a b c) : x + conj x = scalar (trace x) := by oct_ring

/-- **$x\bar x = N(x)$.** -/
@[kb "springerveldkamp2000" "§1.3"]
theorem mul_conj (x : Octonion R a b c) : x * conj x = scalar (norm x) := by oct_ring

/-- **$\bar x x = N(x)$.** -/
@[kb "springerveldkamp2000" "§1.3"]
theorem conj_mul (x : Octonion R a b c) : conj x * x = scalar (norm x) := by oct_ring

/-- **The quadratic equation** $x^2 - T(x)\,x + N(x) = 0$, i.e. $x^2 = T(x)x - N(x)$. -/
@[kb "springerveldkamp2000" "§1.2"]
theorem sq_eq (x : Octonion R a b c) : x * x = trace x • x - scalar (norm x) := by oct_ring

/-- Conjugation is an anti-automorphism: $\overline{xy} = \bar y\,\bar x$. -/
@[kb "springerveldkamp2000" "§1.3"]
theorem conj_mul_conj (x y : Octonion R a b c) : conj (x * y) = conj y * conj x := by oct_ring

theorem conj_conj (x : Octonion R a b c) : conj (conj x) = x := by oct_ring

theorem conj_one : conj (1 : Octonion R a b c) = 1 := by oct_ring

theorem trace_add (x y : Octonion R a b c) : trace (x + y) = trace x + trace y := by
  simp only [trace, fst_add, QuaternionAlgebra.re_add]; ring

theorem trace_smul (t : R) (x : Octonion R a b c) : trace (t • x) = t * trace x := by
  simp only [trace, fst_smul, QuaternionAlgebra.re_smul, smul_eq_mul]; ring

theorem trace_one : trace (1 : Octonion R a b c) = 2 := by simp [trace]

theorem trace_scalar (t : R) : trace (scalar t : Octonion R a b c) = 2 * t := by simp [trace]

theorem norm_scalar (t : R) : norm (scalar t : Octonion R a b c) = t ^ 2 := by
  oct_coords; ring

theorem norm_conj (x : Octonion R a b c) : norm (conj x) = norm x := by oct_coords; ring

theorem norm_smul (t : R) (x : Octonion R a b c) : norm (t • x) = t ^ 2 * norm x := by
  oct_coords; ring

/-- **The composition law** $N(xy) = N(x)N(y)$: $\mathbb O$ is a composition algebra. -/
@[kb "springerveldkamp2000" "Prop. 1.5.3"]
theorem norm_mul (x y : Octonion R a b c) : norm (x * y) = norm x * norm y := by
  oct_coords; ring

/-- **Left alternativity** $x(xy) = (xx)y$. -/
@[kb "springerveldkamp2000" "Lemma 1.4.1"]
theorem mul_mul_self_left (x y : Octonion R a b c) : x * (x * y) = (x * x) * y := by oct_ring

/-- **Right alternativity** $(yx)x = y(xx)$. -/
@[kb "springerveldkamp2000" "Lemma 1.4.1"]
theorem mul_self_mul_right (x y : Octonion R a b c) : (y * x) * x = y * (x * x) := by oct_ring

/-- **Flexibility** $(xy)x = x(yx)$. -/
@[kb "springerveldkamp2000" "Lemma 1.4.1"]
theorem flexible (x y : Octonion R a b c) : (x * y) * x = x * (y * x) := by oct_ring

/-- **The polar form** $\langle x, y\rangle = N(x + y) - N(x) - N(y)$ of the norm. -/
@[kb "springerveldkamp2000" "§1.2"]
def polar (x y : Octonion R a b c) : R := norm (x + y) - norm x - norm y

/-- $\langle x, y\rangle = T(x\bar y)$. -/
theorem polar_eq_trace (x y : Octonion R a b c) : polar x y = trace (x * conj y) := by
  simp only [polar]; oct_coords; ring

/-- $\langle x, 1\rangle = T(x)$. -/
theorem polar_one (x : Octonion R a b c) : polar x 1 = trace x := by
  simp only [polar]; oct_coords; ring

/-- The distinguished element $\ell = (0, 1)$, with $\ell^2 = c$ and $N(\ell) = -c$. -/
def ell : Octonion R a b c := ⟨0, 1⟩

theorem ell_mul_ell : (ell : Octonion R a b c) * ell = scalar c := by
  simp only [ell]; oct_ring

theorem norm_ell : norm (ell : Octonion R a b c) = -c := by simp only [ell]; oct_coords; ring

/-- Pure octonions ($T(x) = 0$) satisfy $\bar x = -x$ and $x^2 = -N(x)$. -/
theorem sq_of_trace_eq_zero {x : Octonion R a b c} (hx : trace x = 0) :
    x * x = - scalar (norm x) := by
  rw [sq_eq, hx, zero_smul, zero_sub]

end Octonion

end QuadFormsKB.Exceptional
