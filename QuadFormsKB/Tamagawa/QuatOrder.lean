/-
# Orders in quaternion algebras; existence of maximal orders

**Layer:** $R$ an integrally closed domain with fraction field $K$ (e.g. $\mathcal O_F \subset F$, or $\mathfrak o_v \subset F_v$);
$D = (a,b)_K$ = `ℍ[K,a,b]` (the conventions: $i^2 = a$, $j^2 = b$, $ij = -ji = k$, coordinates `re, imI, imJ, imK`).

Mathlib has quaternion algebras but no orders (searched 2026-10-17: Mathlib, GitHub, Zulip; nothing found), so the basic
theory is built here.

**Contents.**
* `isInteger_of_quadratic`: Gauss's lemma for an element $x$ of a $K$-algebra with $x^2 = tx - n$, $x \notin K$, integral
  over $R$: then $t, n \in R$.
* `IsOrder`, `IsMaximalOrder` (Voight Def. 10.2.1, 10.4.1) for any $K$-algebra; `isInteger_trd_nrd`: $\operatorname{trd}$ and
  $\operatorname{nrd}$ of elements of an order lie in $R$.
* `stdOrder K a b` $= R\langle 1, i, j, k\rangle$ for $a, b \in R$, an order (`isOrder_stdOrder`).
* `smul_mem_stdOrder`, `le_stdBound`: every order $\mathcal O \supseteq R\langle1,i,j,k\rangle$ lies in $(2ab)^{-1}R\langle1,i,j,k\rangle$.
* `exists_isMaximalOrder_ge`, `exists_isMaximalOrder_ge_stdOrder`: maximal orders containing a given order containing
  the standard order exist ($R$ Noetherian, $2ab \ne 0$).

Sources: Voight, *Quaternion Algebras* (2021), Ch. 10 and 15; Weil 1982, §3.1 (orders appear as the lattices of his
zeta function). Indices 0-based.
-/
import QuadFormsKB.Tamagawa.Quaternion

open Polynomial Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat IsLocalization

section Integrality

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [IsIntegrallyClosed R]
variable {A : Type*} [Ring A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

/-- A scalar $c \in K$ that is integral over $R$ inside a $K$-algebra lies in $R$. -/
theorem isInteger_of_isIntegral_algebraMap [Nontrivial A] {c : K} (h : IsIntegral R (algebraMap K A c)) :
    IsInteger R c := by
  have hinj : Function.Injective ((Algebra.ofId K A).restrictScalars R) :=
    (algebraMap K A).injective
  have : IsIntegral R c := by
    rw [← isIntegral_algHom_iff _ hinj] at *; exact h
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact ⟨r, hr⟩

/-- **Gauss's lemma for quadratic elements.** If $x$ in a $K$-algebra satisfies $x^2 = t x - n$,
is not a scalar, and is integral over the integrally closed domain $R$ ($K = \operatorname{Frac} R$),
then $t, n \in R$. -/
theorem isInteger_of_quadratic {x : A} {t n : K} (hx : x * x = t • x - algebraMap K A n)
    (hns : ∀ c : K, x ≠ algebraMap K A c) (hint : IsIntegral R x) : IsInteger R t ∧ IsInteger R n := by
  have hA : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hns 0 (Subsingleton.elim _ _)
  obtain ⟨p, hpm, hp⟩ := hint
  set g : K[X] := C 1 * X ^ 2 + C (-t) * X + C n with hg
  have hg2 : g.degree = 2 := degree_quadratic one_ne_zero
  have hgm : g.Monic := by
    rw [Monic, hg, leadingCoeff_quadratic one_ne_zero]
  have hgx : aeval x g = 0 := by
    simp only [hg, map_add, map_mul, aeval_C, aeval_X, pow_two, map_one, one_mul, map_neg]
    rw [hx, Algebra.smul_def]; noncomm_ring
  set pK := p.map (algebraMap R K)
  have hpK : aeval x pK = 0 := by
    rw [aeval_map_algebraMap]; exact hp
  have hdeg : (pK %ₘ g).degree ≤ 1 := by
    have := degree_modByMonic_lt pK hgm
    rw [hg2] at this
    exact Order.le_of_lt_succ this
  have hr := eq_X_add_C_of_degree_le_one hdeg
  have hrx : aeval x (pK %ₘ g) = 0 := by
    rw [modByMonic_eq_sub_mul_div pK g, map_sub, map_mul, hpK, hgx, zero_mul, sub_zero]
  rw [hr] at hrx
  simp only [map_add, map_mul, aeval_C, aeval_X] at hrx
  have h1 : (pK %ₘ g).coeff 1 = 0 := by
    by_contra h1
    apply hns (-((pK %ₘ g).coeff 1)⁻¹ * (pK %ₘ g).coeff 0)
    have : algebraMap K A ((pK %ₘ g).coeff 1) * x = -algebraMap K A ((pK %ₘ g).coeff 0) :=
      eq_neg_of_add_eq_zero_left hrx
    calc x = algebraMap K A ((pK %ₘ g).coeff 1)⁻¹ * (algebraMap K A ((pK %ₘ g).coeff 1) * x) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ h1, map_one, one_mul]
      _ = _ := by rw [this, map_mul, map_neg, neg_mul, mul_neg]
  have h0 : (pK %ₘ g).coeff 0 = 0 := by
    rw [h1, map_zero, zero_mul, zero_add] at hrx
    exact (algebraMap K A).injective (by rw [hrx, map_zero])
  have hdvd : g ∣ pK := by
    rw [← modByMonic_eq_zero_iff_dvd hgm, hr, h1, h0, map_zero, zero_mul, zero_add]
  obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hpm hdvd
  rw [hgm.leadingCoeff, map_one, mul_one] at hg'
  constructor
  · refine ⟨-g'.coeff 1, ?_⟩
    have := congrArg (fun q => q.coeff 1) hg'
    simp only [coeff_map, hg, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X_one, coeff_C] at this
    rw [map_neg, this]; norm_num
  · refine ⟨g'.coeff 0, ?_⟩
    have := congrArg (fun q => q.coeff 0) hg'
    simp only [coeff_map, hg, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X_zero, coeff_C] at this
    rw [this]; norm_num

end Integrality

section QuatBasic

variable {K : Type*} [Field K] {a b : K}

/-- The reduced trace $\operatorname{trd}(x) = x + \bar x = 2x_0$ of $x \in (a,b)_K$. -/
def trd (x : ℍ[K,a,b]) : K := 2 * x.re

/-- $x^2 = \operatorname{trd}(x)\,x - \operatorname{nrd}(x)$ (the reduced characteristic polynomial). -/
theorem mul_self_eq (x : ℍ[K,a,b]) : x * x = trd x • x - algebraMap K ℍ[K,a,b] (nrd x) := by
  ext <;> simp [trd, nrd, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem eq_algebraMap_iff (x : ℍ[K,a,b]) (c : K) :
    x = algebraMap K ℍ[K,a,b] c ↔ x.re = c ∧ x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0 := by
  rw [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.ext_iff]

/-- The basis quaternions $i$, $j$, $k$ of $(a,b)_K$ (`qi`, `qj`, `qk`). -/
def qi : ℍ[K,a,b] := ⟨0, 1, 0, 0⟩
def qj : ℍ[K,a,b] := ⟨0, 0, 1, 0⟩
def qk : ℍ[K,a,b] := ⟨0, 0, 0, 1⟩

@[simp] theorem trd_mul_qi (x : ℍ[K,a,b]) : trd (x * qi) = 2 * a * x.imI := by
  simp [trd, qi]; ring
@[simp] theorem trd_mul_qj (x : ℍ[K,a,b]) : trd (x * qj) = 2 * b * x.imJ := by
  simp [trd, qj]; ring
@[simp] theorem trd_mul_qk (x : ℍ[K,a,b]) : trd (x * qk) = -(2 * a * b * x.imK) := by
  simp [trd, qk]; ring

theorem eq_sum_basis (x : ℍ[K,a,b]) :
    x = x.re • (1 : ℍ[K,a,b]) + x.imI • qi + x.imJ • qj + x.imK • qk := by
  ext <;> simp [qi, qj, qk]

end QuatBasic

section Orders

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
variable {A : Type*} [Ring A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

/-- **An $R$-order** in a $K$-algebra $A$ ($K = \operatorname{Frac} R$): a subring $\mathcal O \subseteq A$
containing $R$ (an $R$-subalgebra) that is a finitely generated $R$-module (`fg`) and spans $A$ over $K$
(`span`), i.e. a full $R$-lattice in $A$ that is a subring.

Source: Voight 2021, Def. 10.2.1 (lattices, Def. 9.3.1/9.3.3). -/
@[kb "voight2021" "Def. 10.2.1"]
structure IsOrder (O : Subalgebra R A) : Prop where
  /-- $\mathcal O$ is a finitely generated $R$-module. -/
  fg : (Subalgebra.toSubmodule O).FG
  /-- $K\mathcal O = A$. -/
  span : Submodule.span K (O : Set A) = ⊤

/-- **A maximal $R$-order**: an order not properly contained in another order.

Source: Voight 2021, Def. 10.4.1. -/
@[kb "voight2021" "Def. 10.4.1"]
def IsMaximalOrder (O : Subalgebra R A) : Prop :=
  IsOrder R K O ∧ ∀ O' : Subalgebra R A, IsOrder R K O' → O ≤ O' → O' = O

variable {R K}

theorem IsOrder.isIntegral {O : Subalgebra R A} (hO : IsOrder R K O) {x : A} (hx : x ∈ O) :
    IsIntegral R x :=
  IsIntegral.of_mem_of_fg O hO.fg x hx

end Orders

section QuatOrders

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [IsIntegrallyClosed R] {a b : K}

/-- **Elements of an order are integral:** for $x$ in an $R$-order of $(a,b)_K$ ($R$ integrally closed,
$K = \operatorname{Frac} R$), $\operatorname{trd}(x), \operatorname{nrd}(x) \in R$.

Source: Voight 2021, Lemma 10.3.1 and Cor. 10.3.6. -/
@[kb "voight2021" "Cor. 10.3.6"]
theorem isInteger_trd_nrd {O : Subalgebra R ℍ[K,a,b]} (hO : IsOrder R K O) {x : ℍ[K,a,b]} (hx : x ∈ O) :
    IsInteger R (trd x) ∧ IsInteger R (nrd x) := by
  have hint := hO.isIntegral hx
  by_cases hs : ∃ c : K, x = algebraMap K ℍ[K,a,b] c
  · obtain ⟨c, rfl⟩ := hs
    obtain ⟨r, hr⟩ := isInteger_of_isIntegral_algebraMap (R := R) hint
    refine ⟨⟨2 * r, ?_⟩, ⟨r ^ 2, ?_⟩⟩
    · simp [trd, QuaternionAlgebra.algebraMap_eq, hr, map_ofNat]
    · simp [nrd, QuaternionAlgebra.algebraMap_eq, hr]
  · push Not at hs
    exact isInteger_of_quadratic (mul_self_eq x) hs hint

end QuatOrders

section StdOrder

variable {R : Type*} (K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The coordinatewise inclusion $(a,b)_R \to (a,b)_K$ of the quaternion algebra over $R$ into the one over
$K = \operatorname{Frac} R$. -/
def stdHom (a b : R) : ℍ[R,a,b] →ₐ[R] ℍ[K,algebraMap R K a,algebraMap R K b] where
  toFun x := ⟨algebraMap R K x.re, algebraMap R K x.imI, algebraMap R K x.imJ, algebraMap R K x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  commutes' r := by
    ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> rfl

/-- **The standard order** $R\langle 1, i, j, k\rangle = R + Ri + Rj + Rk$ of $(a,b)_K$ for $a, b \in R$: the quaternions
whose four coordinates lie in $R$ (the image of $(a,b)_R$).

Source: Voight 2021, Example 10.2.4 (the standard order $R\langle i, j\rangle$ of $(a,b \mid F)$). -/
@[kb "voight2021" "Ex. 10.2.4"]
def stdOrder (a b : R) : Subalgebra R ℍ[K,algebraMap R K a,algebraMap R K b] := (stdHom K a b).range

variable {K}

theorem mem_stdOrder {a b : R} {x : ℍ[K,algebraMap R K a,algebraMap R K b]} :
    x ∈ stdOrder K a b ↔ IsInteger R x.re ∧ IsInteger R x.imI ∧ IsInteger R x.imJ ∧ IsInteger R x.imK := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.re, rfl⟩, ⟨y.imI, rfl⟩, ⟨y.imJ, rfl⟩, ⟨y.imK, rfl⟩⟩
  · rintro ⟨⟨r0, h0⟩, ⟨r1, h1⟩, ⟨r2, h2⟩, ⟨r3, h3⟩⟩
    refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
    ext <;> simp [stdHom, h0, h1, h2, h3]

theorem stdHom_injective (a b : R) : Function.Injective (stdHom K a b) := by
  intro x y h
  have hi := IsFractionRing.injective R K
  simp only [stdHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    QuaternionAlgebra.mk.injEq] at h
  ext
  exacts [hi h.1, hi h.2.1, hi h.2.2.1, hi h.2.2.2]

theorem qi_mem_stdOrder (a b : R) : (qi : ℍ[K,algebraMap R K a,algebraMap R K b]) ∈ stdOrder K a b :=
  mem_stdOrder.2 ⟨⟨0, by simp [qi]⟩, ⟨1, by simp [qi]⟩, ⟨0, by simp [qi]⟩, ⟨0, by simp [qi]⟩⟩
theorem qj_mem_stdOrder (a b : R) : (qj : ℍ[K,algebraMap R K a,algebraMap R K b]) ∈ stdOrder K a b :=
  mem_stdOrder.2 ⟨⟨0, by simp [qj]⟩, ⟨0, by simp [qj]⟩, ⟨1, by simp [qj]⟩, ⟨0, by simp [qj]⟩⟩
theorem qk_mem_stdOrder (a b : R) : (qk : ℍ[K,algebraMap R K a,algebraMap R K b]) ∈ stdOrder K a b :=
  mem_stdOrder.2 ⟨⟨0, by simp [qk]⟩, ⟨0, by simp [qk]⟩, ⟨0, by simp [qk]⟩, ⟨1, by simp [qk]⟩⟩

/-- **The standard order is an order** (for any $a, b \in R$). -/
@[kb "voight2021" "Ex. 10.2.4"]
theorem isOrder_stdOrder (a b : R) : IsOrder R K (stdOrder K a b) where
  fg := by
    have : Subalgebra.toSubmodule (stdOrder K a b) = Submodule.map (stdHom K a b).toLinearMap ⊤ := by
      ext x; simp [stdOrder]
    rw [this]
    exact (Module.Finite.fg_top).map _
  span := by
    refine eq_top_iff.2 fun x _ => ?_
    rw [eq_sum_basis x]
    have h1 : (1 : ℍ[K,algebraMap R K a,algebraMap R K b]) ∈ stdOrder K a b := one_mem _
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exacts [h1, qi_mem_stdOrder a b, qj_mem_stdOrder a b, qk_mem_stdOrder a b]

end StdOrder

section Maximal

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [IsIntegrallyClosed R]

theorem isInteger_mul_left {r : R} {t : K} (ht : IsInteger R t) : IsInteger R (algebraMap R K r * t) := by
  obtain ⟨s, rfl⟩ := ht; exact ⟨r * s, by simp⟩

/-- **Subrings with integral traces containing the standard order are bounded by its dual:** if
$\mathcal O \supseteq R\langle 1,i,j,k\rangle$ is a subring of $(a,b)_K$ all of whose elements have reduced trace in $R$,
then $2ab\,x \in R\langle 1,i,j,k\rangle$ for all $x \in \mathcal O$ (since $\operatorname{trd}(x\cdot 1) = 2x_0$,
$\operatorname{trd}(xi) = 2ax_1$, $\operatorname{trd}(xj) = 2bx_2$, $\operatorname{trd}(xk) = -2abx_3$ lie in $R$).

Source: Voight 2021, §15.5 (proof of Prop. 15.5.2: $\mathcal O \subseteq \mathcal O^\sharp$); here with the explicit dual basis of
the standard order. -/
@[kb "voight2021" "Prop. 15.5.2"]
theorem smul_mem_stdOrder_of_trd {a b : R} {O : Subalgebra R ℍ[K,algebraMap R K a,algebraMap R K b]}
    (htrd : ∀ x ∈ O, IsInteger R (trd x))
    (hstd : stdOrder K a b ≤ O) {x : ℍ[K,algebraMap R K a,algebraMap R K b]} (hx : x ∈ O) :
    (algebraMap R K (2 * a * b)) • x ∈ stdOrder K a b := by
  have t0 := htrd x hx
  have t1 := htrd _ (O.mul_mem hx (hstd (qi_mem_stdOrder a b)))
  have t2 := htrd _ (O.mul_mem hx (hstd (qj_mem_stdOrder a b)))
  have t3 := htrd _ (O.mul_mem hx (hstd (qk_mem_stdOrder a b)))
  rw [trd_mul_qi] at t1; rw [trd_mul_qj] at t2; rw [trd_mul_qk] at t3; rw [trd] at t0
  refine mem_stdOrder.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
    QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul]
  · convert isInteger_mul_left (r := a * b) t0 using 1; simp [map_ofNat]; ring
  · convert isInteger_mul_left (r := b) t1 using 1; simp [map_ofNat]; ring
  · convert isInteger_mul_left (r := a) t2 using 1; simp [map_ofNat]; ring
  · convert isInteger_mul_left (r := -1) t3 using 1; simp [map_ofNat]

/-- **Orders containing the standard order are bounded by its dual:** $2ab\,\mathcal O \subseteq R\langle 1,i,j,k\rangle$. -/
@[kb "voight2021" "Prop. 15.5.2"]
theorem smul_mem_stdOrder {a b : R} {O : Subalgebra R ℍ[K,algebraMap R K a,algebraMap R K b]} (hO : IsOrder R K O)
    (hstd : stdOrder K a b ≤ O) {x : ℍ[K,algebraMap R K a,algebraMap R K b]} (hx : x ∈ O) :
    (algebraMap R K (2 * a * b)) • x ∈ stdOrder K a b :=
  smul_mem_stdOrder_of_trd (fun _ hy => (isInteger_trd_nrd hO hy).1) hstd hx

/-- The $R$-module $(2ab)^{-1}R\langle 1,i,j,k\rangle$, which contains every order containing the standard order. -/
def stdBound (a b : R) : Submodule R ℍ[K,algebraMap R K a,algebraMap R K b] :=
  (Subalgebra.toSubmodule (stdOrder K a b)).map
    ((((algebraMap R K (2 * a * b))⁻¹ : K) • LinearMap.id :
      ℍ[K,algebraMap R K a,algebraMap R K b] →ₗ[K] ℍ[K,algebraMap R K a,algebraMap R K b]).restrictScalars R)

theorem stdBound_fg (a b : R) : (stdBound (K := K) a b).FG :=
  (isOrder_stdOrder a b).fg.map _

theorem le_stdBound_of_trd {a b : R} (h2ab : algebraMap R K (2 * a * b) ≠ 0)
    {O : Subalgebra R ℍ[K,algebraMap R K a,algebraMap R K b]} (htrd : ∀ x ∈ O, IsInteger R (trd x))
    (hstd : stdOrder K a b ≤ O) : Subalgebra.toSubmodule O ≤ stdBound a b := by
  intro x hx
  refine ⟨_, smul_mem_stdOrder_of_trd htrd hstd hx, ?_⟩
  change ((algebraMap R K (2 * a * b))⁻¹ : K) • ((algebraMap R K (2 * a * b)) • x) = x
  rw [smul_smul, inv_mul_cancel₀ h2ab, one_smul]

theorem le_stdBound {a b : R} (h2ab : algebraMap R K (2 * a * b) ≠ 0)
    {O : Subalgebra R ℍ[K,algebraMap R K a,algebraMap R K b]} (hO : IsOrder R K O)
    (hstd : stdOrder K a b ≤ O) : Subalgebra.toSubmodule O ≤ stdBound a b :=
  le_stdBound_of_trd h2ab (fun _ hy => (isInteger_trd_nrd hO hy).1) hstd

/-- **Existence of maximal orders** (over a Noetherian integrally closed domain $R$, $2ab \ne 0$): every order of
$(a,b)_K$ containing the standard order $R\langle 1,i,j,k\rangle$ is contained in a maximal order. (All such orders lie in
the Noetherian module $(2ab)^{-1}R\langle 1,i,j,k\rangle$, so a maximal one exists.)

Source: Voight 2021, 10.4.2 and Prop. 15.5.2 (Noetherian argument). -/
@[kb "voight2021" "Prop. 15.5.2"]
theorem exists_isMaximalOrder_ge [IsNoetherianRing R] {a b : R} (h2ab : algebraMap R K (2 * a * b) ≠ 0)
    {O : Subalgebra R ℍ[K,algebraMap R K a,algebraMap R K b]} (hO : IsOrder R K O) (hstd : stdOrder K a b ≤ O) :
    ∃ M, IsMaximalOrder R K M ∧ O ≤ M := by
  set N := stdBound (K := K) a b
  have : IsNoetherian R N := isNoetherian_of_fg_of_noetherian N (stdBound_fg a b)
  let S : Set (Submodule R N) := {P | ∃ O' : Subalgebra R ℍ[K,algebraMap R K a,algebraMap R K b],
    IsOrder R K O' ∧ O ≤ O' ∧ P = (Subalgebra.toSubmodule O').comap N.subtype}
  obtain ⟨P, ⟨M, hM, hOM, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.2 inferInstance S ⟨_, O, hO, le_rfl, rfl⟩
  refine ⟨M, ⟨hM, fun O' hO' hMO' => ?_⟩, hOM⟩
  have hO'N := le_stdBound h2ab hO' (hstd.trans (hOM.trans hMO'))
  have hle : (Subalgebra.toSubmodule M).comap N.subtype ≤ (Subalgebra.toSubmodule O').comap N.subtype :=
    Submodule.comap_mono hMO'
  have heq : (Subalgebra.toSubmodule M).comap N.subtype = (Subalgebra.toSubmodule O').comap N.subtype := by
    by_contra hne
    exact hmax _ ⟨O', hO', hOM.trans hMO', rfl⟩ (lt_of_le_of_ne hle hne)
  refine le_antisymm (fun x hx => ?_) hMO'
  have hxN : x ∈ N := hO'N hx
  have : (⟨x, hxN⟩ : N) ∈ (Subalgebra.toSubmodule O').comap N.subtype := hx
  rw [← heq] at this
  exact this

/-- **Maximal orders containing the standard order exist.** -/
@[kb "voight2021" "Prop. 15.5.2"]
theorem exists_isMaximalOrder_ge_stdOrder [IsNoetherianRing R] {a b : R} (h2ab : algebraMap R K (2 * a * b) ≠ 0) :
    ∃ M, IsMaximalOrder R K M ∧ stdOrder K a b ≤ M :=
  exists_isMaximalOrder_ge h2ab (isOrder_stdOrder a b) le_rfl

end Maximal

section Transport

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
variable {A B : Type*} [Ring A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  [Ring B] [Algebra K B] [Algebra R B] [IsScalarTower R K B]

/-- **Orders transport along algebra isomorphisms:** if $\varphi : A \cong B$ is a $K$-algebra isomorphism and $\mathcal O$ an
$R$-order of $A$, then $\varphi(\mathcal O)$ is an $R$-order of $B$. -/
theorem IsOrder.map {O : Subalgebra R A} (hO : IsOrder R K O) (φ : A ≃ₐ[K] B) :
    IsOrder R K (O.map ((φ : A →ₐ[K] B).restrictScalars R)) where
  fg := by
    have : Subalgebra.toSubmodule (O.map ((φ : A →ₐ[K] B).restrictScalars R)) =
        (Subalgebra.toSubmodule O).map ((φ : A →ₐ[K] B).restrictScalars R).toLinearMap := rfl
    rw [this]; exact hO.fg.map _
  span := by
    have h := congrArg (Submodule.map (φ.toLinearEquiv : A →ₗ[K] B)) hO.span
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    rw [← h]
    congr 1

/-- **Maximal orders transport along algebra isomorphisms.** -/
theorem IsMaximalOrder.map {O : Subalgebra R A} (hO : IsMaximalOrder R K O) (φ : A ≃ₐ[K] B) :
    IsMaximalOrder R K (O.map ((φ : A →ₐ[K] B).restrictScalars R)) := by
  refine ⟨hO.1.map φ, fun O' hO' hle => ?_⟩
  have h1 := hO'.map φ.symm
  have hle' : O ≤ O'.map ((φ.symm : B →ₐ[K] A).restrictScalars R) := by
    intro x hx
    refine ⟨φ x, hle ⟨x, hx, rfl⟩, ?_⟩
    simp
  have heq := hO.2 _ h1 hle'
  apply le_antisymm _ hle
  intro y hy
  refine ⟨φ.symm y, ?_, by simp⟩
  rw [← heq]
  exact ⟨y, hy, rfl⟩

end Transport

end QuadFormsKB.QuatOrder
