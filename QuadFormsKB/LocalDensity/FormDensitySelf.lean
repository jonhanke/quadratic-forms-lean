/-
# The self-density $\beta_\pi(L, L)$ and the orthogonal group mod $\pi^k$
**Layer:** DVR, every residue characteristic.

**Defines** `DVR.orthMod Q π k`, the **orthogonal group of $Q$ mod $\pi^k$**: the $X \in \mathrm{GL}_n(R/\pi^k)$
with $Q \circ X = Q$ over $R/\pi^k$ (a subgroup, via `QuadForm.compMat_mul`).

**Proves**
* the composition laws $Q \circ 1 = Q$ and $(Q \circ X) \circ Y = Q \circ (XY)$ over any commutative ring
  (`QuadForm.compMat_one`, `QuadForm.compMat_mul`, via `QuadForm.eq_of_eval_eq`);
* for $k > d = \mathrm{ord}_\pi \det H_Q$, every self-representation mod $\pi^k$ is invertible, so
  $A_{\pi^k}(Q, Q) = |O(Q \bmod \pi^k)|$ (`repCountForm_self_eq_card_orthMod`);
* **existence of the self-density** for nondegenerate $Q$ and the stabilization
  $A_{\pi^{k+1}}(Q, Q) = q^{n(n-1)/2} A_{\pi^k}(Q, Q)$ for $k \ge 2d + 1$ (`repCountForm_self_succ`,
  `localDensityForm_self_eq`), hence $\beta_\pi(Q, Q) = |O(Q \bmod \pi^k)| / q^{k\,n(n-1)/2}$ for every $k \ge 2d+1$
  (`localDensityForm_self_eq_card`);
* when $H_Q$ is invertible mod $\pi$ (unimodular non-dyadic, or even unimodular dyadic):
  $\beta_\pi(Q, Q) = |O(\bar Q)| / q^{n(n-1)/2}$ with $\bar Q$ over the residue field (`localDensityForm_self_unimodular`);
* the rank-one closed form $\beta_\pi(\langle u\rangle, \langle u\rangle) = 2q^e$ for a unit $u$, $e = \mathrm{ord}_\pi 2$
  (`localDensityForm_self_unary`; so $= 2$ and Siegel's $\alpha = 1$ at non-dyadic primes).

*Closed forms* at unimodular non-dyadic primes, $|O_n(\mathbb F_q)|/q^{n(n-1)/2} = 2\prod_{i=1}^{m}(1 - q^{-2i})$ ($n = 2m+1$)
and $2(1 - \chi q^{-m})\prod_{i=1}^{m-1}(1 - q^{-2i})$ ($n = 2m$), are proved in `Tamagawa/OrthFq.lean`
(`DVR.localDensityForm_self_odd`, `DVR.localDensityForm_self_even`) by counting column by column (no Witt theorem).
**Depends on** `FormDensityStab.lean`, `DyadicBad.lean` (rank-one counts).
-/
import QuadFormsKB.LocalDensity.FormDensityStab
import QuadFormsKB.LocalDensity.DyadicBad

namespace QuadFormsKB

open Matrix

set_option linter.deprecated false

namespace QuadForm

variable {A : Type*} [CommRing A] {n r s : ℕ}

theorem eval_single (Q : QuadForm A n) (i : Fin n) : Q.eval (Pi.single i 1) = Q.coeff i i := by
  rw [eval_eq_dotProduct', mulVec_single_one, single_one_dotProduct]
  rfl

/-- **A form is determined by its values** over any commutative ring: $c_{ii} = Q(e_i)$ and
$c_{ij} = Q(e_i + e_j) - Q(e_i) - Q(e_j)$ for $i < j$. -/
theorem eq_of_eval_eq {Q₁ Q₂ : QuadForm A n} (h : ∀ x, Q₁.eval x = Q₂.eval x) : Q₁ = Q₂ := by
  apply ext_upper
  intro i j hij
  rcases hij.lt_or_eq with hlt | heq
  · have key : ∀ Q : QuadForm A n, Q.coeff i j =
        Q.eval (Pi.single i 1 + Pi.single j 1) - Q.eval (Pi.single i 1) - Q.eval (Pi.single j 1) := by
      intro Q
      rw [eval_polar, mulVec_single_one, single_one_dotProduct]
      have hz : Q.coeff j i = 0 := Q.upper (show id i < id j from hlt)
      simp [hessian, hz]
    rw [key Q₁, key Q₂, h, h, h]
  · subst heq
    rw [← eval_single, ← eval_single, h]

/-- $Q \circ 1 = Q$. -/
theorem compMat_one (Q : QuadForm A n) : Q.compMat (1 : Matrix (Fin n) (Fin n) A) = Q :=
  eq_of_eval_eq fun y => by rw [eval_compMat, one_mulVec]

/-- **$(Q \circ X) \circ Y = Q \circ (XY)$.** -/
theorem compMat_mul (Q : QuadForm A n) (X : Matrix (Fin n) (Fin r) A) (Y : Matrix (Fin r) (Fin s) A) :
    (Q.compMat X).compMat Y = Q.compMat (X * Y) :=
  eq_of_eval_eq fun y => by rw [eval_compMat, eval_compMat, eval_compMat, mulVec_mulVec]

theorem hessian_map {B : Type*} [CommRing B] (f : A →+* B) (Q : QuadForm A n) :
    (Q.map f).hessian = Q.hessian.map f := by
  ext i j
  simp [hessian, QuadForm.map]

end QuadForm

namespace LocalDensity.DVR

open QuadForm

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **The orthogonal group of $Q$ mod $\pi^k$**: $\{g \in \mathrm{GL}_n(R/\pi^k) : \bar Q \circ g = \bar Q\}$ with
$\bar Q$ the reduction of $Q$, i.e. the isometries of $L/\pi^k L$ for the lattice $L = R^n$ with form $Q$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
def orthMod (Q : QuadForm R n) (π : R) (k : ℕ) : Subgroup (GL (Fin n) (R ⧸ Ideal.span {π ^ k})) where
  carrier := {g | (Q.map (Ideal.Quotient.mk _)).compMat g.val = Q.map (Ideal.Quotient.mk _)}
  mul_mem' {g h} hg hh := by
    show _ = _
    rw [Units.val_mul, ← compMat_mul, Set.mem_setOf_eq.mp hg, Set.mem_setOf_eq.mp hh]
  one_mem' := by
    show _ = _
    rw [Units.val_one, compMat_one]
  inv_mem' {g} hg := by
    show _ = _
    conv_lhs => rw [← Set.mem_setOf_eq.mp hg]
    rw [compMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, compMat_one]

/-- **Self-representations mod $\pi^k$ are invertible** once $k > d = \mathrm{ord}_\pi \det H_Q$: from
$X^{\mathsf T} \bar H X = \bar H$, $(\det X)^2 \det H \equiv \det H$, so $\det X$ is a unit. -/
theorem isUnit_det_of_compMat_eq (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (d k : ℕ)
    (hd : π ^ d ∣ Q.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ Q.hessian.det) (hdk : d < k)
    (X : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k}))
    (hX : (Q.map (Ideal.Quotient.mk _)).compMat X = Q.map (Ideal.Quotient.mk _)) : IsUnit X.det := by
  have hπ0 := hπ.ne_zero
  have h1 := congrArg QuadForm.hessian hX
  rw [hessian_compMat, hessian_map] at h1
  have h2 := congrArg Matrix.det h1
  rw [det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
  obtain ⟨u, hu, huu⟩ := dvr_exact hπ hd hd'
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective X.det
  rw [← hy, ← map_mul, ← map_mul, hu, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
  have h3 : π ^ k ∣ π ^ d * (u * (y * y - 1)) := by
    rw [show π ^ d * (u * (y * y - 1)) = y * (π ^ d * u) * y - π ^ d * u by ring]; exact h2
  rw [show k = d + (k - d) by omega, pow_add, mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)] at h3
  have h4 : π ∣ u * (y * y - 1) := (dvd_pow_self π (by omega)).trans h3
  have h5 : π ∣ y * y - 1 := by
    rcases hπ.prime.dvd_or_dvd h4 with h | h
    · exact absurd h (dvr_not_dvd_of_isUnit hπ huu)
    · exact h
  have hy1 : IsUnit y := by
    apply dvr_isUnit_of_not_dvd hπ
    intro hpy
    apply hπ.not_isUnit
    have : π ∣ 1 := by
      have := dvd_sub (dvd_mul_of_dvd_left hpy y) h5
      simpa using this
    exact isUnit_of_dvd_one this
  rw [← hy]
  exact hy1.map _

/-- **$A_{\pi^k}(Q, Q) = |O(Q \bmod \pi^k)|$** for $k > \mathrm{ord}_\pi \det H_Q$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem repCountForm_self_eq_card_orthMod (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (d k : ℕ)
    (hd : π ^ d ∣ Q.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ Q.hessian.det) (hdk : d < k) :
    repCountForm Q Q π k = Nat.card (orthMod Q π k) := by
  unfold repCountForm
  symm
  refine Nat.card_congr
    { toFun := fun g => ⟨g.1.val, g.2⟩
      invFun := fun X =>
        ⟨Matrix.nonsingInvUnit X.1 (isUnit_det_of_compMat_eq Q π hπ d k hd hd' hdk X.1 X.2), X.2⟩
      left_inv := fun g => by
        apply Subtype.ext; apply Units.ext; rfl
      right_inv := fun X => by
        apply Subtype.ext; rfl }

theorem self_exp (n : ℕ) : n * n - n * (n + 1) / 2 = n * (n - 1) / 2 := by
  have he := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h1 : n * (n + 1) = n * (n - 1) + 2 * n := by
    cases n with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel]; ring
  have h2 : n * n = n * (n - 1) + n := by
    cases n with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel]; ring
  rw [h1, h2]
  omega

section Self

variable [Finite (IsLocalRing.ResidueField R)]

/-- **Stabilization of the self-representation count** (Siegel 1935; Kitaoka 1993, §5.6 [unverified]): for
$\pi^d \,\|\, \det H_Q$ and $k \ge 2d + 1$, $A_{\pi^{k+1}}(Q, Q) = q^{n(n-1)/2} A_{\pi^k}(Q, Q)$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem repCountForm_self_succ (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (d k : ℕ)
    (hd : π ^ d ∣ Q.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ Q.hessian.det) (hk : 2 * d + 1 ≤ k) :
    repCountForm Q Q π (k + 1) = q R ^ (n * (n - 1) / 2) * repCountForm Q Q π k := by
  rw [repCountForm_succ' Q Q π hπ d k hd hd' hk le_rfl, self_exp]

/-- **The self-density** $\beta_\pi(Q, Q) = A_{\pi^k}(Q, Q)/q^{k\,n(n-1)/2}$ for every $k \ge 2d + 1$,
$\pi^d \,\|\, \det H_Q$ (Siegel's $\alpha_\pi(Q, Q)$ is half of this: `siegelDensity`). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_self_eq (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (d : ℕ)
    (hd : π ^ d ∣ Q.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ Q.hessian.det) (k : ℕ) (hk : 2 * d + 1 ≤ k) :
    localDensityForm Q Q π = (repCountForm Q Q π k : ℝ) / (q R : ℝ) ^ (k * (n * (n - 1) / 2)) := by
  rw [localDensityForm_eq Q Q π hπ d hd hd' le_rfl k hk, self_exp]

/-- **$\beta_\pi(Q, Q) = |O(Q \bmod \pi^k)| / q^{k\,n(n-1)/2}$** for every $k \ge 2d + 1$, $\pi^d \,\|\, \det H_Q$:
the self-density is the normalized order of the orthogonal group of $L/\pi^k L$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_self_eq_card (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (d : ℕ)
    (hd : π ^ d ∣ Q.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ Q.hessian.det) (k : ℕ) (hk : 2 * d + 1 ≤ k) :
    localDensityForm Q Q π = (Nat.card (orthMod Q π k) : ℝ) / (q R : ℝ) ^ (k * (n * (n - 1) / 2)) := by
  rw [localDensityForm_self_eq Q π hπ d hd hd' k hk,
    repCountForm_self_eq_card_orthMod Q π hπ d k hd hd' (by omega)]

/-- **Existence of the self-density** $\beta_\pi(Q, Q)$ for nondegenerate $Q$, at every prime. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_self_eventually_eq (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R)
    (hπ : Irreducible π) :
    ∀ᶠ k in Filter.atTop,
      (repCountForm Q Q π k : ℝ) / (q R : ℝ) ^ (k * (n * (n - 1) / 2)) = localDensityForm Q Q π := by
  have h := localDensityForm_eventually_eq Q Q hQ π hπ le_rfl
  simpa only [self_exp] using h

/-- **Unimodular case** ($H_Q$ invertible mod $\pi$): $\beta_\pi(Q, Q) = |O(\bar Q)|/q^{n(n-1)/2}$, $\bar Q = Q \bmod \pi$
over the residue field. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_self_unimodular (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (hQ : IsUnit Q.hessian.det) :
    localDensityForm Q Q π = (Nat.card (orthMod Q π 1) : ℝ) / (q R : ℝ) ^ (n * (n - 1) / 2) := by
  rw [localDensityForm_self_eq_card Q π hπ 0 (by simp) (by simpa using dvr_not_dvd_of_isUnit hπ hQ) 1
    le_rfl, one_mul]

theorem unary_eq_diag (u : R) : unary u = QuadForm.diag ![u] := by
  unfold unary; congr 1; funext i; rw [Fin.fin_one_eq_zero i]; rfl

/-- **Rank one:** $\beta_\pi(\langle u\rangle, \langle u\rangle) = 2q^e$ for a unit $u$, $e = \mathrm{ord}_\pi 2$ (the solutions of
$ux^2 \equiv u$ mod $\pi^{2e+1}$ are $x \equiv \pm 1 \bmod \pi^{e+1}$). At a non-dyadic prime $\beta = 2 = |O_1|$ and
Siegel's $\alpha_\pi(\langle u\rangle, \langle u\rangle) = 1$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_self_unary (π : R) (hπ : Irreducible π) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {u : R} (hu : IsUnit u) :
    localDensityForm (unary u) (unary u) π = 2 * (q R : ℝ) ^ e := by
  have hH : (unary u).hessian.det = 2 * u := by
    simp [hessian, unary, QuadForm.diag, Matrix.det_unique]; ring
  have hd : π ^ e ∣ (unary u).hessian.det := by rw [hH]; exact dvd_mul_of_dvd_left he.1 u
  have hd' : ¬ π ^ (e + 1) ∣ (unary u).hessian.det := by
    rw [hH, hu.dvd_mul_right]; exact he.2
  rw [localDensityForm_self_eq (unary u) π hπ e hd hd' (2 * e + 1) le_rfl, repCountForm_unary,
    unary_eq_diag]
  obtain ⟨v, hv2, hv⟩ := dvr_exact hπ he.1 he.2
  rw [repCount_unary_eq π hπ hv hv2 hu isUnit_one (by simp)]
  push_cast
  simp

end Self

end LocalDensity.DVR

end QuadFormsKB
