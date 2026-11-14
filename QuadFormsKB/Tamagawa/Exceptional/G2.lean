/-
# The exceptional group $G_2$ as the automorphism group of an octonion algebra

For an octonion algebra $\mathbb O = (a, b, c)_R$ (`Tamagawa/Exceptional/Octonion.lean`), the group of
$R$-points of $G_2$ is
$$G_2(R) = \operatorname{Aut}(\mathbb O) = \{g\in\mathrm{GL}_R(\mathbb O) : g(1) = 1,\ g(xy) = g(x)g(y)\},$$
here a subgroup `G2 R a b c` of the linear automorphisms `Octonion R a b c ≃ₗ[R] Octonion R a b c`
(Springer–Veldkamp 2000, §2.3 [unverified locator]). Every $G_2$ over a field of characteristic $\ne 2$ arises
this way from some octonion algebra; over a number field the octonion algebras, hence the forms of $G_2$,
are classified by their norm forms (3-fold Pfister forms). This file contains the algebra that
routes to the Tamagawa number of $G_2$ start from.

**Contents** ($K$ a field, for the results that compare coefficients).
* `G2 R a b c`: the automorphism group, over any commutative ring $R$.
* Automorphisms preserve the trace and the norm (`trace_apply`, `norm_apply`), hence the polar form
  (`polar_apply`) and the trace-zero subspace $\mathbb O_0 = \ker T$ (`pureOct`), over every field $K$
  (no assumption on the characteristic). *Proof:* if $x\notin K\cdot1$ then $1, x$ are linearly
  independent and so are $1, g(x)$; comparing $g(x)^2 = T(x)g(x) - N(x)$ with
  $g(x)^2 = T(g(x))g(x) - N(g(x))$ gives the claim (Springer–Veldkamp 2000, §2.1 [unverified]).
* `toPure`: the homomorphism $G_2(K)\to\mathrm{GL}(\mathbb O_0)$, $g\mapsto g|_{\mathbb O_0}$, with image in the isometries
  of $(\mathbb O_0, N)$ (`norm_toPure`), injective when $2\ne0$ in $K$ (`toPure_injective`). So $G_2(K)$ is a subgroup
  of the orthogonal group of the 7-dimensional form $\langle -a,-b,ab,-c,ac,bc,-abc\rangle$.
* `sl1ToG2`: the injective homomorphism $\mathrm{SL}_1(D)\to G_2(R)$, $u\mapsto\varphi_u$, $\varphi_u(p + q\ell) = p + (uq)\ell$,
  from the norm-one quaternions $D^1 = $ Mathlib's `unitary ℍ[R,a,b]` (over a field: $\operatorname{nrd}(u) = 1$).
* `eq_sl1ToG2_of_fix` (**the stabilizer of the quaternion subalgebra**): over a field with $2, a, b, c\ne0$,
  an automorphism fixing $D = \{p + 0\ell\}$ pointwise is $\varphi_u$ for a unique $u\in D^1$. So the pointwise
  stabilizer of $D$ in $G_2$ is $\mathrm{SL}_1(D)$ (Springer–Veldkamp 2000, Prop. 2.2.1 [unverified locator]).

Sources: Springer–Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups* (2000), Ch. 1–2 [unverified
locators].
-/
import QuadFormsKB.Tamagawa.Exceptional.Octonion

open Quaternion

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

namespace QuadFormsKB.Exceptional

open Octonion

section Ring

variable (R : Type*) [CommRing R] (a b c : R)

/-- **The group $G_2(R) = \operatorname{Aut}(\mathbb O)$** of the octonion algebra $\mathbb O = (a, b, c)_R$: the
$R$-linear automorphisms $g$ of $\mathbb O$ with $g(1) = 1$ and $g(xy) = g(x)g(y)$ for all $x, y$.

Source: Springer–Veldkamp 2000, §2.3 [unverified locator]. -/
@[kb "springerveldkamp2000" "§2.3"]
def G2 : Subgroup (Octonion R a b c ≃ₗ[R] Octonion R a b c) where
  carrier := {g | g 1 = 1 ∧ ∀ x y, g (x * y) = g x * g y}
  one_mem' := ⟨rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg⟩ ⟨hh1, hh⟩
    refine ⟨?_, fun x y => ?_⟩
    · simp [hh1, hg1]
    · simp [hh, hg]
  inv_mem' := by
    rintro g ⟨hg1, hg⟩
    refine ⟨?_, fun x y => ?_⟩
    · simp only [LinearEquiv.coe_inv]
      conv_lhs => rw [← hg1]
      exact g.symm_apply_apply 1
    · simp only [LinearEquiv.coe_inv]
      apply g.injective
      rw [hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]

variable {R a b c}

namespace G2

theorem map_one (g : G2 R a b c) : g.1 1 = 1 := g.2.1

theorem map_mul (g : G2 R a b c) (x y : Octonion R a b c) :
    g.1 (x * y) = g.1 x * g.1 y := g.2.2 x y

theorem scalar_eq_smul_one (t : R) : (scalar t : Octonion R a b c) = t • 1 := by oct_ring

theorem map_scalar (g : G2 R a b c) (t : R) : g.1 (scalar t) = scalar t := by
  rw [scalar_eq_smul_one, LinearEquiv.map_smul, G2.map_one]

end G2

end Ring

section Field

variable {K : Type*} [Field K] {a b c : K}

namespace Octonion

theorem scalar_injective : Function.Injective (scalar : K → Octonion K a b c) := by
  intro s t h
  have := congrArg (fun x : Octonion K a b c => x.fst.re) h
  simpa using this

/-- If $s x - N = s' x - N'$ with $x$ not a scalar, then $s = s'$ and $N = N'$. -/
theorem coeff_eq_of_not_scalar {x : Octonion K a b c} (hx : ∀ t, x ≠ scalar t) {s s' n n' : K}
    (h : s • x - scalar n = s' • x - scalar n') : s = s' ∧ n = n' := by
  have h1 : (s - s') • x = scalar (n - n') := by
    have e : (s - s') • x - scalar (n - n') = (s • x - scalar n) - (s' • x - scalar n') := by
      oct_ring
    rw [h, sub_self] at e
    exact sub_eq_zero.mp e
  by_cases hs : s - s' = 0
  · refine ⟨sub_eq_zero.mp hs, ?_⟩
    rw [hs, zero_smul] at h1
    have : scalar (n - n') = (scalar 0 : Octonion K a b c) := by
      rw [← h1]; oct_ring
    exact sub_eq_zero.mp (scalar_injective this)
  · exfalso
    apply hx ((s - s')⁻¹ * (n - n'))
    have : x = (s - s')⁻¹ • ((s - s') • x) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [this, h1]; oct_ring

end Octonion

namespace G2

/-- **Automorphisms preserve trace and norm** (both at once), over every field. -/
theorem trace_norm_apply (g : G2 K a b c) (x : Octonion K a b c) :
    trace (g.1 x) = trace x ∧ norm (g.1 x) = norm x := by
  by_cases hx : ∃ t, x = scalar t
  · obtain ⟨t, rfl⟩ := hx
    rw [map_scalar]; exact ⟨rfl, rfl⟩
  · push Not at hx
    have hgx : ∀ t, g.1 x ≠ scalar t := by
      intro t h
      apply hx t
      apply g.1.injective
      rw [h, map_scalar]
    have h1 := sq_eq (g.1 x)
    rw [← G2.map_mul, sq_eq x, map_sub, LinearEquiv.map_smul, map_scalar] at h1
    obtain ⟨h2, h3⟩ := coeff_eq_of_not_scalar hgx h1
    exact ⟨h2.symm, h3.symm⟩

/-- **Automorphisms preserve the trace:** $T(g x) = T(x)$. -/
@[kb "springerveldkamp2000" "§2.1"]
theorem trace_apply (g : G2 K a b c) (x : Octonion K a b c) : trace (g.1 x) = trace x :=
  (trace_norm_apply g x).1

/-- **Automorphisms preserve the norm:** $N(g x) = N(x)$. -/
@[kb "springerveldkamp2000" "§2.1"]
theorem norm_apply (g : G2 K a b c) (x : Octonion K a b c) : norm (g.1 x) = norm x :=
  (trace_norm_apply g x).2

/-- Automorphisms preserve the polar form $\langle x, y\rangle = N(x+y) - N(x) - N(y)$. -/
theorem polar_apply (g : G2 K a b c) (x y : Octonion K a b c) : polar (g.1 x) (g.1 y) = polar x y := by
  simp only [polar, ← map_add, norm_apply]

end G2

namespace Octonion

/-- The trace as a linear form. -/
def traceLM : Octonion K a b c →ₗ[K] K where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

/-- **The pure (trace-zero) octonions** $\mathbb O_0 = \ker T$, a 7-dimensional subspace on which the norm
is $\langle -a, -b, ab, -c, ac, bc, -abc\rangle$ (`Octonion.norm_eq_coords` with $x_0 = 0$). -/
@[kb "springerveldkamp2000" "§1.3"]
def pureOct (K : Type*) [Field K] (a b c : K) : Submodule K (Octonion K a b c) := LinearMap.ker traceLM

theorem mem_pure {x : Octonion K a b c} : x ∈ pureOct K a b c ↔ trace x = 0 := Iff.rfl

end Octonion

namespace G2

theorem map_pure (g : G2 K a b c) : (pureOct K a b c).map g.1.toLinearMap =
    pureOct K a b c := by
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, mem_pure]
  constructor
  · rintro ⟨x, hx, rfl⟩; rwa [trace_apply]
  · intro hy
    refine ⟨g.1.symm y, ?_, g.1.apply_symm_apply y⟩
    rw [← trace_apply g, LinearEquiv.apply_symm_apply]; exact hy

/-- **Restriction to the pure octonions**, $G_2(K)\to\mathrm{GL}(\mathbb O_0)$, $g\mapsto g|_{\mathbb O_0}$. -/
@[kb "springerveldkamp2000" "§2.3"]
def toPure : G2 K a b c →* (pureOct K a b c ≃ₗ[K] pureOct K a b c) where
  toFun g := g.1.ofSubmodules (pureOct K a b c) (pureOct K a b c) (map_pure g)
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

@[simp] theorem toPure_apply (g : G2 K a b c) (v : pureOct K a b c) :
    ((toPure g v : pureOct K a b c) : Octonion K a b c) = g.1 v := rfl

/-- The image of $G_2(K)$ consists of isometries of $(\mathbb O_0, N)$. -/
@[kb "springerveldkamp2000" "§2.3"]
theorem norm_toPure (g : G2 K a b c) (v : pureOct K a b c) :
    norm ((toPure g v : pureOct K a b c) : Octonion K a b c) = norm (v : Octonion K a b c) := by
  rw [toPure_apply, norm_apply]

/-- **$G_2(K)$ embeds in the orthogonal group of $(\mathbb O_0, N)$** when $2\ne0$: an automorphism is
determined by its restriction to the pure octonions, since $x = \tfrac12T(x) + (x - \tfrac12T(x))$. -/
@[kb "springerveldkamp2000" "§2.3"]
theorem toPure_injective (h2 : (2 : K) ≠ 0) : Function.Injective (toPure : G2 K a b c →* _) := by
  intro g h hgh
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  have hdec : x = scalar (trace x / 2) + (x - scalar (trace x / 2)) := by abel
  have hp : x - scalar (trace x / 2) ∈ pureOct K a b c := by
    rw [mem_pure]
    have : trace (x - scalar (trace x / 2)) = trace x - 2 * (trace x / 2) := by
      simp only [trace]; oct_coords; ring
    rw [this]; field_simp; ring
  have := congrArg (fun φ : pureOct K a b c ≃ₗ[K] pureOct K a b c =>
    ((φ ⟨_, hp⟩ : pureOct K a b c) : Octonion K a b c)) hgh
  simp only [toPure_apply] at this
  rw [hdec, map_add, map_add, map_scalar, map_scalar, this]

end G2

end Field

section SL1

variable {R : Type*} [CommRing R] {a b c : R}

/-- The linear map $\varphi_u(p + q\ell) = p + (uq)\ell$. -/
def phiLin (u : ℍ[R,a,b]) : Octonion R a b c →ₗ[R] Octonion R a b c where
  toFun x := ⟨x.fst, u * x.snd⟩
  map_add' x y := by ext <;> simp [_root_.mul_add]
  map_smul' t x := by ext <;> simp

/-- $\varphi_u$ for a norm-one quaternion $u$, as a linear automorphism (inverse $\varphi_{\bar u}$). -/
def phiEquiv (u : unitary ℍ[R,a,b]) : Octonion R a b c ≃ₗ[R] Octonion R a b c :=
  LinearEquiv.ofLinearMap (phiLin (u : ℍ[R,a,b])) (phiLin (star (u : ℍ[R,a,b])))
    (by ext x <;> simp [phiLin, ← mul_assoc, Unitary.mul_star_self_of_mem u.2])
    (by ext x <;> simp [phiLin, ← mul_assoc, Unitary.star_mul_self_of_mem u.2])

@[simp] theorem phiEquiv_apply (u : unitary ℍ[R,a,b]) (x : Octonion R a b c) :
    phiEquiv u x = ⟨x.fst, (u : ℍ[R,a,b]) * x.snd⟩ := rfl

theorem phiEquiv_mem (u : unitary ℍ[R,a,b]) : phiEquiv (c := c) u ∈ G2 R a b c := by
  refine ⟨?_, fun x y => ?_⟩
  · ext <;> simp
  · have hu : star (u : ℍ[R,a,b]) * u = 1 := Unitary.star_mul_self_of_mem u.2
    apply Octonion.ext
    · simp only [phiEquiv_apply, fst_mul, star_mul]
      congr 2
      rw [mul_assoc, ← mul_assoc (star (u : ℍ[R,a,b])), hu, _root_.one_mul]
    · simp only [phiEquiv_apply, snd_mul, _root_.mul_add, mul_assoc]

/-- **$\mathrm{SL}_1(D)\hookrightarrow G_2$**: the homomorphism $u\mapsto\varphi_u$, $\varphi_u(p + q\ell) = p + (uq)\ell$,
from the norm-one quaternions of $D = (a,b)_R$ to $G_2(R) = \operatorname{Aut}((a,b,c)_R)$. Its image fixes $D$
pointwise; over a field it is the whole pointwise stabilizer of $D$ (`eq_sl1ToG2_of_fix`).

Source: Springer–Veldkamp 2000, Prop. 2.2.1 [unverified locator]. -/
@[kb "springerveldkamp2000" "Prop. 2.2.1"]
def sl1ToG2 : unitary ℍ[R,a,b] →* G2 R a b c where
  toFun u := ⟨phiEquiv u, phiEquiv_mem u⟩
  map_one' := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x; ext <;> simp
  map_mul' u v := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x
    ext <;> simp [mul_assoc]

@[simp] theorem sl1ToG2_apply (u : unitary ℍ[R,a,b]) (x : Octonion R a b c) :
    (sl1ToG2 u).1 x = ⟨x.fst, (u : ℍ[R,a,b]) * x.snd⟩ := rfl

theorem sl1ToG2_injective : Function.Injective (sl1ToG2 : unitary ℍ[R,a,b] →* G2 R a b c) := by
  intro u v h
  have := congrArg (fun g : G2 R a b c => (g.1 (⟨0, 1⟩ : Octonion R a b c)).snd) h
  simp only [sl1ToG2_apply, _root_.mul_one] at this
  exact Subtype.ext this

/-- $\varphi_u$ fixes the quaternion subalgebra $D = \{p + 0\ell\}$ pointwise. -/
theorem sl1ToG2_fix (u : unitary ℍ[R,a,b]) (p : ℍ[R,a,b]) :
    (sl1ToG2 u).1 (⟨p, 0⟩ : Octonion R a b c) = ⟨p, 0⟩ := by
  ext <;> simp

end SL1

section Stabilizer

variable {K : Type*} [Field K] {a b c : K}

/-- **The pointwise stabilizer of the quaternion subalgebra is $\mathrm{SL}_1(D)$**: over a field with
$2, a, b, c \ne 0$, every $g\in G_2(K)$ fixing $D = \{p + 0\ell\}$ pointwise is $\varphi_u$ for some
$u\in D^1$ (unique by `sl1ToG2_injective`). *Proof:* $g(\ell)$ is orthogonal to $g(D) = D$, hence of the form
$(0, u)$ because the norm form of $D$ is nondegenerate; $N(g\ell) = N(\ell) = -c$ gives $\operatorname{nrd}(u) = 1$;
and $g(0, q) = g((q,0)\ell) = (q,0)(0,u) = (0, uq)$.

Source: Springer–Veldkamp 2000, Prop. 2.2.1 [unverified locator]. -/
@[kb "springerveldkamp2000" "Prop. 2.2.1"]
theorem eq_sl1ToG2_of_fix (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (g : G2 K a b c) (hg : ∀ p : ℍ[K,a,b], g.1 (⟨p, 0⟩ : Octonion K a b c) = ⟨p, 0⟩) :
    ∃ u : unitary ℍ[K,a,b], sl1ToG2 u = g := by
  set w := g.1 (⟨0, 1⟩ : Octonion K a b c) with hw
  -- `w.fst = 0` from orthogonality to `D`
  have horth : ∀ p : ℍ[K,a,b], polar (⟨p, 0⟩ : Octonion K a b c) w = 0 := by
    intro p
    rw [hw, ← hg p, G2.polar_apply]
    simp only [polar]; oct_coords; ring
  have h0 := horth 1
  have h1 := horth ⟨0, 1, 0, 0⟩
  have h2' := horth ⟨0, 0, 1, 0⟩
  have h3 := horth ⟨0, 0, 0, 1⟩
  simp only [polar] at h0 h1 h2' h3
  oct_coords at h0 h1 h2' h3
  have e0 : w.fst.re = 0 := by
    have : 2 * w.fst.re = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h2
    · exact h
  have e1 : w.fst.imI = 0 := by
    have : (-2 * a) * w.fst.imI = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exfalso; rcases mul_eq_zero.mp h with h | h
      · exact h2 (by linear_combination -h)
      · exact ha h
    · exact h
  have e2 : w.fst.imJ = 0 := by
    have : (-2 * b) * w.fst.imJ = 0 := by linear_combination h2'
    rcases mul_eq_zero.mp this with h | h
    · exfalso; rcases mul_eq_zero.mp h with h | h
      · exact h2 (by linear_combination -h)
      · exact hb h
    · exact h
  have e3 : w.fst.imK = 0 := by
    have : (2 * a * b) * w.fst.imK = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h | h
    · exfalso; rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact h2 h
        · exact ha h
      · exact hb h
    · exact h
  have hwfst : w.fst = 0 := QuaternionAlgebra.ext e0 e1 e2 e3
  -- the norm of `w`
  have hN : Octonion.norm w = Octonion.norm (⟨0, 1⟩ : Octonion K a b c) := G2.norm_apply g _
  have hnrd : (w.snd * star w.snd).re = 1 := by
    have e1 : Octonion.norm w = -c * (w.snd * star w.snd).re := by
      simp only [Octonion.norm, hwfst, zero_mul, star_zero, QuaternionAlgebra.re_zero]; ring
    have e2 : Octonion.norm (⟨0, 1⟩ : Octonion K a b c) = -c := by oct_coords; ring
    rw [e1, e2] at hN
    exact mul_left_cancel₀ (neg_ne_zero.mpr hc) (hN.trans (_root_.mul_one (-c)).symm)
  have hunit : w.snd ∈ unitary ℍ[K,a,b] := by
    have hm : w.snd * star w.snd = 1 := by
      rw [QuaternionAlgebra.mul_star_eq_coe, hnrd]; rfl
    refine Unitary.mem_iff.mpr ⟨?_, hm⟩
    rw [star_comm_self']; exact hm
  refine ⟨⟨w.snd, hunit⟩, ?_⟩
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  have hx : x = (⟨x.fst, 0⟩ : Octonion K a b c) + (⟨x.snd, 0⟩ : Octonion K a b c) * ⟨0, 1⟩ := by
    ext <;> simp
  have hgx : g.1 x = (⟨x.fst, 0⟩ : Octonion K a b c) + (⟨x.snd, 0⟩ : Octonion K a b c) * w := by
    conv_lhs => rw [hx]
    rw [map_add, G2.map_mul, hg, hg]
  rw [hgx, sl1ToG2_apply]
  have hw' : w = ⟨0, w.snd⟩ := Octonion.ext hwfst rfl
  conv_rhs => rw [hw']
  ext <;> simp

end Stabilizer

end QuadFormsKB.Exceptional
