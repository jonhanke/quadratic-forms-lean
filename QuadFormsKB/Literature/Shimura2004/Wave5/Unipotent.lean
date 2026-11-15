/-
# Shimura 2004, §4.7: the unipotent radical $R^\varphi$, formula (4.26) and $\sigma(R^\varphi) = 1$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §4.7, (4.23b), Lemma 4.9 and
(4.26) (printed pp. 32–34). Page numbers are printed pages.

**Setting.** As in `Wave5/Levi.lean`: a field $F$ of characteristic $\ne 2$, the weak Witt decomposition (4.3)
$V = I'_m + W + I_m$ given by a hyperbolic family `e f : Fin m → V` (`IsHypFamily Q e f`), $J = I_m$ = `spanE F e`.

**Defines**
* (4.23b) $R^\varphi = P^\varphi_m \cap \mathrm{Ker}(\pi^\varphi) \cap \mathrm{Ker}(\lambda^\varphi)$ (`unipR`), with
  $P^\varphi_m = P^J \cap SO^\varphi$ = `parabolicSO Q (spanE F e)` (4.8a).

**Proves** (all unconditional; standard axioms only)
* a unipotent endomorphism has determinant $1$ (`det_one_add_of_isNilpotent`), so $R^J \subseteq SO^\varphi$ and
  $R^\varphi = R^J$ (`unipRO_le_orthPlus`, `unipR_eq_unipRO`); for $r \in R^J$, $(r - 1)^3 = 0$
  (`sub_one_pow_three`);
* **(4.26)**: $\varepsilon \mapsto \varepsilon^2$ maps $R^\varphi$ onto itself (`formula_4_26`), with the explicit
  square root $1 + \tfrac12 N - \tfrac18 N^2$, $N = \varepsilon - 1$;
* **Lemma 4.9, last assertion**: $\sigma(R^\varphi) = 1$ for the spinor norm $\sigma$ (`lemma_4_9_unipR`), for
  nondegenerate $\varphi$. Shimura derives it from the main formula of Lemma 4.9 ($\sigma(\varepsilon) =
  \det(d)\sigma(e)$), whose proof uses Proposition 4.8 (characteristic $0$); here it follows from (4.26) alone,
  for every field of characteristic $\ne 2$, since $\sigma(s^2) = \sigma(s)^2 = 1$ (Shimura's own argument for
  $\sigma(\gamma\beta) = 1$ in the proof of Lemma 4.9).
-/
import QuadFormsKB.Literature.Shimura2004.Wave5.Levi
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.Basic
import QuadFormsKB.Citation

open Module Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.OMeara

namespace Levi

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {m : ℕ}

/-! ### Unipotent endomorphisms have determinant one -/

omit [Invertible (2 : F)] in
/-- $\det(1 + N) = 1$ for a nilpotent endomorphism $N$ of a finite-dimensional vector space. -/
theorem det_one_add_of_isNilpotent {N : Module.End F V} (hN : IsNilpotent N) :
    LinearMap.det (1 + N) = 1 := by
  have h := LinearMap.eval_charpoly N (-1)
  rw [hN.charpoly_eq_X_pow_finrank, eval_pow, eval_X] at h
  have h' : algebraMap F (Module.End F V) (-1) - N = (-1 : F) • (1 + N) := by
    rw [map_neg, map_one, neg_one_smul]; abel
  rw [h', LinearMap.det_smul] at h
  have hu : ((-1 : F) ^ finrank F V) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  exact (mul_eq_left₀ hu).1 h.symm

/-! ### The structure of $r \in R^J$ -/

variable {e f : Fin m → V} (hH : IsHypFamily Q e f)
include hH

/-- For $r \in R^J$ and $N = r - 1$: $N$ maps $V$ into $J^\perp$. -/
theorem polar_sub_eq_zero {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) (x : V) {y : V} (hy : y ∈ spanE F e) :
    QuadraticMap.polar Q (r x - x) y = 0 := by
  obtain ⟨hP, h1, _⟩ := hr
  have := polar_map_of_mem_orth hP.1 x y
  rw [h1 y hy] at this
  rw [QuadraticMap.polar_sub_left, this, sub_self]

/-- For $r \in R^J$ and $N = r - 1$: $N$ maps $J^\perp$ into $J$. -/
theorem sub_mem_spanE_of_perp {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) {x : V}
    (hx : ∀ y ∈ spanE F e, QuadraticMap.polar Q x y = 0) : r x - x ∈ spanE F e := by
  obtain ⟨_, h1, h2⟩ := hr
  have hd := decomp (Q := Q) (e := e) (f := f) x
  rw [(projF_eq_zero_iff hH x).2 hx, add_zero] at hd
  rw [hd, map_add, h1 _ (projE_mem x)]
  have := h2 _ (projW_mem hH x)
  rwa [show projE Q e f x + r (projW Q e f x) - (projE Q e f x + projW Q e f x) =
    r (projW Q e f x) - projW Q e f x by abel]

/-- $N = r - 1$ for $r \in R^J$, as an endomorphism. -/
abbrev nilN (r : V ≃ₗ[F] V) : Module.End F V := (r : V →ₗ[F] V) - 1

omit hH in
theorem nilN_apply (r : V ≃ₗ[F] V) (x : V) : nilN r x = r x - x := rfl

/-- **$(r - 1)^3 = 0$ for $r \in R^J$**: $N = r - 1$ maps $V \to J^\perp \to J \to 0$. -/
theorem sub_one_pow_three {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) : nilN r ^ 3 = 0 := by
  ext x
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, LinearMap.zero_apply]
  have h1 : nilN r x ∈ spanE F e ∨ True := Or.inr trivial
  clear h1
  have hJ : nilN r (nilN r x) ∈ spanE F e :=
    sub_mem_spanE_of_perp hH hr fun y hy => polar_sub_eq_zero hH hr x hy
  rw [nilN_apply (r := r) (nilN r (nilN r x)), hr.2.1 _ hJ, sub_self]

theorem isNilpotent_nilN {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) : IsNilpotent (nilN r) :=
  ⟨3, sub_one_pow_three hH hr⟩

/-- $R^J \subseteq SO^\varphi$: an element of $R^J$ is unipotent, so has determinant $1$. -/
theorem unipRO_le_orthPlus : unipRO Q e f ≤ orthPlus Q := by
  intro r hr
  refine ⟨hr.1.1, (MonoidHom.mem_ker).2 ?_⟩
  rw [← Units.val_eq_one, LinearEquiv.coe_det]
  have := det_one_add_of_isNilpotent (isNilpotent_nilN hH hr)
  rwa [add_sub_cancel] at this

omit hH in
variable (Q e f) in
/-- **$R^\varphi = P^\varphi_m \cap \mathrm{Ker}(\pi^\varphi) \cap \mathrm{Ker}(\lambda^\varphi)$** ((4.23b),
p. 32), $P^\varphi_m = P^J \cap SO^\varphi$ (4.8a): the unipotent radical of $P^\varphi_m$. -/
@[kb "shimura2004" "(4.23b), p. 32 (the unipotent radical R^φ of P^φ_m)"]
def unipR : Subgroup (V ≃ₗ[F] V) := parabolicSO Q (spanE F e) ⊓ unipRO Q e f

/-- $R^\varphi = R^J$: intersecting with $SO^\varphi$ changes nothing. -/
theorem unipR_eq_unipRO : unipR Q e f = unipRO Q e f :=
  le_antisymm inf_le_right fun _ hr => ⟨⟨hr.1, unipRO_le_orthPlus hH hr⟩, hr⟩

/-! ### (4.26): square roots in $R^\varphi$ -/

omit hH in
/-- The polynomial $p = 1 + \tfrac12X - \tfrac18X^2$, with $p^2 \equiv 1 + X \pmod{X^3}$. -/
def sqrtPoly : F[X] := 1 + C (⅟2 : F) * X - C ((⅟2 : F) ^ 3) * X ^ 2

omit hH in
theorem sqrtPoly_sq : ∃ q : F[X], (sqrtPoly : F[X]) * sqrtPoly = 1 + X + X ^ 3 * q := by
  have hC : (2 : F[X]) * C (⅟2 : F) = 1 := by
    rw [← map_ofNat C 2, ← map_mul, mul_invOf_self, map_one]
  refine ⟨-2 * C (⅟2 : F) ^ 4 + C (⅟2 : F) ^ 6 * X, ?_⟩
  simp only [sqrtPoly, map_pow]
  linear_combination (X - C (⅟2 : F) ^ 2 * X ^ 2) * hC

omit hH in
theorem Q_add' (u v : V) : Q (u + v) = Q u + Q v + QuadraticMap.polar Q u v := by
  unfold QuadraticMap.polar; ring

/-- The square root $s = 1 + \tfrac12 N - \tfrac18 N^2$ of $r = 1 + N$, as an endomorphism. -/
def sqrtLin (r : V ≃ₗ[F] V) : Module.End F V := aeval (nilN r) (sqrtPoly : F[X])

omit hH in
theorem sqrtLin_apply (r : V ≃ₗ[F] V) (x : V) :
    sqrtLin r x = x + (⅟2 : F) • nilN r x - ((⅟2 : F) ^ 3) • nilN r (nilN r x) := by
  simp [sqrtLin, sqrtPoly, pow_two, Module.End.mul_apply]

theorem sqrtLin_mul_self {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) : sqrtLin r * sqrtLin r = r := by
  obtain ⟨q, hq⟩ := (sqrtPoly_sq : ∃ q : F[X], _)
  rw [sqrtLin, ← map_mul, hq, map_add, map_add, map_mul, map_pow, aeval_X, aeval_one,
    sub_one_pow_three hH hr, zero_mul, add_zero, add_sub_cancel]

theorem sqrtLin_of_mem_spanE {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) {x : V} (hx : x ∈ spanE F e) :
    sqrtLin r x = x := by
  have h0 : nilN r x = 0 := by rw [nilN_apply, hr.2.1 x hx, sub_self]
  rw [sqrtLin_apply, h0, map_zero]; simp

theorem sqrtLin_sub_mem {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) {w : V} (hw : w ∈ wSpace Q e f) :
    sqrtLin r w - w ∈ spanE F e := by
  have hN : nilN r w ∈ spanE F e := hr.2.2 w hw
  have h0 : nilN r (nilN r w) = 0 := by rw [nilN_apply, hr.2.1 _ hN, sub_self]
  rw [sqrtLin_apply, h0, smul_zero, sub_zero, add_sub_cancel_left]
  exact Submodule.smul_mem _ _ hN

theorem Q_sqrtLin {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) (x : V) : Q (sqrtLin r x) = Q x := by
  set y := nilN r x with hy
  set z := nilN r y with hz
  have hzJ : z ∈ spanE F e := sub_mem_spanE_of_perp hH hr fun _ hj => polar_sub_eq_zero hH hr x hj
  have hyz : QuadraticMap.polar Q y z = 0 := polar_sub_eq_zero hH hr x hzJ
  have hQz : Q z = 0 := Q_eq_zero_of_mem_spanE hH hzJ
  have hrx : r x = x + y := by rw [hy, nilN_apply]; abel
  have hry : r y = y + z := by rw [hz, nilN_apply]; abel
  -- `Q(rx) = Q(x)`
  have E1 : Q y + QuadraticMap.polar Q x y = 0 := by
    have := hr.1.1 x
    rw [hrx, Q_add'] at this
    linear_combination this
  -- `φ(ry, rx) = φ(y, x)`
  have E2 : 2 * Q y + QuadraticMap.polar Q z x = 0 := by
    have := polar_map_of_mem_orth hr.1.1 y x
    rw [hry, hrx, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      QuadraticMap.polar_self, QuadraticMap.polar_comm Q z y, hyz] at this
    linear_combination this
  have h2 : (2 : F) * ⅟2 = 1 := mul_invOf_self 2
  rw [sqrtLin_apply, ← hy, ← hz, sub_eq_add_neg, ← neg_smul, Q_add', Q_add', QuadraticMap.map_smul,
    QuadraticMap.map_smul, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, hyz, hQz,
    QuadraticMap.polar_comm Q x z]
  simp only [smul_eq_mul]
  linear_combination (⅟2 : F) * E1 - (⅟2 : F) ^ 3 * E2 + Q y * ((⅟2 : F) ^ 2 + ⅟2) * h2

theorem sqrtLin_injective {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) : Function.Injective (sqrtLin r) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have : r x = 0 := by
    have := congrArg (fun g : Module.End F V => g x) (sqrtLin_mul_self hH hr)
    simp only [Module.End.mul_apply, hx, map_zero] at this
    exact this.symm
  exact r.injective (this.trans (map_zero r).symm)

/-- The square root $s = 1 + \tfrac12 N - \tfrac18 N^2$ of $r \in R^J$, as a linear automorphism. -/
def sqrtR {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) : V ≃ₗ[F] V :=
  LinearEquiv.ofInjectiveEndo _ (sqrtLin_injective hH hr)

theorem sqrtR_mem {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) : sqrtR hH hr ∈ unipRO Q e f := by
  refine ⟨⟨fun x => Q_sqrtLin hH hr x, map_eq_of_map_le ?_⟩, fun x hx => sqrtLin_of_mem_spanE hH hr hx,
    fun w hw => sqrtLin_sub_mem hH hr hw⟩
  rintro _ ⟨x, hx, rfl⟩
  change sqrtLin r x ∈ spanE F e
  rw [sqrtLin_of_mem_spanE hH hr hx]; exact hx

theorem sqrtR_mul_self {r : V ≃ₗ[F] V} (hr : r ∈ unipRO Q e f) : sqrtR hH hr * sqrtR hH hr = r := by
  ext x
  have := congrArg (fun g : Module.End F V => g x) (sqrtLin_mul_self hH hr)
  exact this

/-- **(4.26)** (Shimura, p. 34): the map $\varepsilon \mapsto \varepsilon^2$ is a surjection of $R^\varphi$ onto
itself: every $r \in R^\varphi$ is $s^2$ with $s \in R^\varphi$ (explicitly $s = 1 + \tfrac12N - \tfrac18N^2$,
$N = r - 1$, `sqrtR`). -/
@[kb "shimura2004" "(4.26), p. 34 (ε ↦ ε² is a surjection of R^φ onto itself)"]
theorem formula_4_26 {r : V ≃ₗ[F] V} (hr : r ∈ unipR Q e f) : ∃ s ∈ unipR Q e f, s * s = r := by
  rw [unipR_eq_unipRO hH] at hr ⊢
  exact ⟨sqrtR hH hr, sqrtR_mem hH hr, sqrtR_mul_self hH hr⟩

omit hH in
theorem sqClass_mul_self (c : Lattices.SqClass F) : c * c = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := (powMonoidHom 2 : Fˣ →* Fˣ).range) c
  change ((↑(x * x) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)) = 1
  rw [QuotientGroup.eq_one_iff]
  exact ⟨x, by simp [sq]⟩

theorem unipR_le_orthPlus : unipR Q e f ≤ orthPlus Q := fun _ h => h.1.2

/-- **Lemma 4.9, last assertion** (Shimura, p. 34): $\sigma(R^\varphi) = 1$, $\sigma$ the spinor norm
$SO^\varphi(V) \to F^\times/F^{\times 2}$ (O'Meara's $\theta$ = `OMeara.spinorNormHom`, equal to Shimura's
$\sigma$ by `spinorNormHom_tau`), for nondegenerate $\varphi$. Proved from (4.26): $\sigma(s^2) = \sigma(s)^2 = 1$. -/
@[kb "shimura2004" "Lemma 4.9, p. 34 (σ(R^φ) = 1)"]
theorem lemma_4_9_unipR (hQ : (QuadraticMap.associated Q).Nondegenerate) {r : V ≃ₗ[F] V} (hr : r ∈ unipR Q e f) :
    spinorNormHom Q hQ ⟨r, unipR_le_orthPlus hH hr⟩ = 1 := by
  obtain ⟨s, hs, rfl⟩ := formula_4_26 hH hr
  have : (⟨s * s, unipR_le_orthPlus hH hr⟩ : orthPlus Q) =
      ⟨s, unipR_le_orthPlus hH hs⟩ * ⟨s, unipR_le_orthPlus hH hs⟩ := rfl
  rw [this, map_mul, sqClass_mul_self]

end Levi

end QuadFormsKB.Shimura2004
