/-
# Gan–Hanke–Yu 2001, §§8–9: quaternionic hermitian spaces (Propositions 9.3 and 9.4)

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), §8 ((8.1)–(8.10)),
§9 ((9.1)–(9.2), Props. 9.3, 9.4), pp. 120–122.

**Setting (Gan–Hanke–Yu §9).** $k$ is a totally real number field of degree $d$ and $D$ a quaternion algebra over $k$ ramified at
every real place; $S_D$ is the set of finite places where $D$ is ramified, and $A_D$ a maximal order of $D$. Here
$D = (a,b)_k$ with $a, b\in\mathcal O_k$ (`QuatF k a b`, the library's quaternion algebra $\mathbb H[k,a,b]$ of
`Tamagawa/QuatOrderGlobal.lean`), ramification is `Quat.IsRamifiedAt` (the completion is a division algebra), and $A_D$ is a
maximal $\mathcal O_k$-order (`QuatOrder.IsMaximalOrder`). $V = D^m$ is a left $D$-vector space with the quaternionic
hermitian form $\langle x,y\rangle = \sum_{i,j}x_iH_{ij}\bar y_j$ ($H_{ji} = \bar H_{ij}$, $\bar{\ }$ the canonical involution
`star`); it is linear in $x$ for left multiplication: $\langle cx,y\rangle = c\langle x,y\rangle$. $G = U(V)$ is the group of
$D$-linear automorphisms of $V$ preserving the form (an inner form of $Sp_{2m}$, §8).

An *$A_D$-lattice* is a finitely generated $\mathcal O_k$-submodule of $V$ spanning $V$ over $k$ and stable under left
multiplication by $A_D$. It is **maximal** (Gan–Hanke–Yu p. 120) if $\langle x,x\rangle\in A = \mathcal O_k$ for $x\in\Lambda$ and $\Lambda$ is
maximal with this property; **maximal integral** (Gan–Hanke–Yu p. 121) if $\langle x,y\rangle\in A_D$ for $x,y\in\Lambda$ and $\Lambda$ is
maximal with this property.

**The mass.** As for the unitary groups (`UnitaryMass.lean`), all maximal (resp. maximal integral) lattices are locally
conjugate under $G$ (Gan–Hanke–Yu §8 citing [S3]), so they form one genus and Gan–Hanke–Yu's $\mathrm{Mass}(\Lambda) = \mathrm{Mass}(K)$ is the sum
of $1/\#\mathrm{Stab}_{G(k)}(\Lambda')$ over the $G(k)$-orbits of maximal (resp. maximal integral) lattices (`quatMass`,
`quatIntMass`).

**$L(M)$** (9.1): $\prod_{r=1}^m\zeta_k(1-2r)$, read in absolute value through Hecke's functional equation (`lMotiveOdd k m`,
already used for Prop. 7.4). $\tau(G) = 1$ (9.2). *Clarification:* Gan–Hanke–Yu print $L(M)$, whose sign is $(-1)^{dm(m+1)/2}$; the
mass is positive, so $|L(M)|$ is meant (check: $k = \mathbb Q$, Hamilton quaternions, $m = 1$, the Hurwitz order:
$\mathrm{Mass} = 1/24 = \frac12|\zeta(-1)|$).

**What is proved.** Gan–Hanke–Yu's derivation of Props 9.3 and 9.4 from Prop. 2.13: given the general mass formula with the local
types of §8 ((8.5), (8.9)) and hyperspecial $Sp_{2m}$ at $v\notin S_D$ (the named inputs `QuatProp213`, `QuatIntProp213`),
$v\in S$ iff $v\in S_D$ (`quat_inS_iff`, `quatInt_inS_iff`), the $\lambda_v$ are those printed (`lam_quat`, `lam_quatInt`
in `LambdaTables.lean`, from (2.12)), and the mass is as printed (`ghy_prop93`, `ghy_prop94`).
-/
import QuadFormsKB.Literature.GanHankeYu2001.LambdaTables
import QuadFormsKB.Literature.Hanke2005.GHYMassFormula
import QuadFormsKB.Tamagawa.Quaternion
import QuadFormsKB.Tamagawa.QuatOrderGlobal

set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Pointwise
open scoped ENNReal

namespace QuadFormsKB.GanHankeYu2001

open QuadFormsKB.Hanke2005 (normQ one_lt_normQ lMotiveOdd)
open QuadFormsKB.QuatOrder (QuatF IsMaximalOrder)

variable {k : Type} [Field k] [NumberField k] (a b : 𝓞 k) {m : ℕ}

/-! ### Quaternionic hermitian forms and lattices -/

/-- **The quaternionic hermitian form** $\langle x,y\rangle = \sum_{i,j}x_iH_{ij}\bar y_j$ on $V = D^m$ (Gan–Hanke–Yu 2001, §8, p. 120),
$\bar{\ }$ the canonical involution of $D = (a,b)_k$. -/
@[kb "ganhankeyu2001" "§8, p. 120 (quaternionic hermitian form)"]
def qHerm (H : Matrix (Fin m) (Fin m) (QuatF k a b)) (x y : Fin m → QuatF k a b) : QuatF k a b :=
  ∑ i, ∑ j, x i * H i j * star (y j)

/-- **$H$ is quaternionic hermitian**: $\overline{H_{ji}} = H_{ij}$, so $\langle y,x\rangle = \overline{\langle x,y\rangle}$. -/
def IsQHermitian (H : Matrix (Fin m) (Fin m) (QuatF k a b)) : Prop := ∀ i j, star (H j i) = H i j

/-- **The quaternionic hermitian space is totally definite** (Gan–Hanke–Yu §9: $G(k\otimes\mathbb R)$ compact): for $x\ne0$,
$\langle x,x\rangle$ is an element $c$ of $k$ positive at every real embedding. -/
@[kb "ganhankeyu2001" "§9, p. 121 (totally definite quaternionic hermitian space)"]
def IsTotDefQHerm (H : Matrix (Fin m) (Fin m) (QuatF k a b)) : Prop :=
  ∀ x : Fin m → QuatF k a b, x ≠ 0 → ∃ c : k, algebraMap k (QuatF k a b) c = qHerm a b H x x ∧ ∀ φ : k →+* ℝ, 0 < φ c

/-- **An $A_D$-lattice in $V = D^m$** (Gan–Hanke–Yu §8–9): an $\mathcal O_k$-lattice (finitely generated, spanning $V$ over $k$:
Mathlib's `Submodule.IsLattice`) stable under left multiplication by the order $O = A_D$. -/
@[kb "ganhankeyu2001" "§9, p. 121 (A_D-lattice)"]
def IsQLattice (O : Subalgebra (𝓞 k) (QuatF k a b)) (Λ : Submodule (𝓞 k) (Fin m → QuatF k a b)) : Prop :=
  Λ.IsLattice k ∧ ∀ c ∈ O, ∀ x ∈ Λ, (fun i => c * x i) ∈ Λ

/-- **$\langle x,x\rangle\in A$ for all $x\in\Lambda$** ($A = \mathcal O_k$; Gan–Hanke–Yu (8.3)–(8.4), p. 120). -/
def IsNormIntegralQ (H : Matrix (Fin m) (Fin m) (QuatF k a b)) (Λ : Submodule (𝓞 k) (Fin m → QuatF k a b)) : Prop :=
  ∀ x ∈ Λ, ∃ c : 𝓞 k, algebraMap k (QuatF k a b) (c : k) = qHerm a b H x x

/-- **$\langle x,y\rangle\in A_D$ for all $x,y\in\Lambda$** (Gan–Hanke–Yu p. 121). -/
def IsIntegralQ (O : Subalgebra (𝓞 k) (QuatF k a b)) (H : Matrix (Fin m) (Fin m) (QuatF k a b))
    (Λ : Submodule (𝓞 k) (Fin m → QuatF k a b)) : Prop :=
  ∀ x ∈ Λ, ∀ y ∈ Λ, qHerm a b H x y ∈ O

/-- **A maximal $A_D$-lattice** (Gan–Hanke–Yu 2001, §8, p. 120): $\langle x,x\rangle\in A$ for all $x\in\Lambda$, and $\Lambda$ is maximal
among $A_D$-lattices with this property. -/
@[kb "ganhankeyu2001" "§8, p. 120 (maximal lattice)"]
def IsMaximalQLat (O : Subalgebra (𝓞 k) (QuatF k a b)) (H : Matrix (Fin m) (Fin m) (QuatF k a b))
    (Λ : Submodule (𝓞 k) (Fin m → QuatF k a b)) : Prop :=
  IsQLattice a b O Λ ∧ IsNormIntegralQ a b H Λ ∧
    ∀ Λ', IsQLattice a b O Λ' → IsNormIntegralQ a b H Λ' → Λ ≤ Λ' → Λ' = Λ

/-- **A maximal integral $A_D$-lattice** (Gan–Hanke–Yu 2001, §8, p. 121): $\langle x,y\rangle\in A_D$ for all $x,y\in\Lambda$, and $\Lambda$ is
maximal among $A_D$-lattices with this property. -/
@[kb "ganhankeyu2001" "§8, p. 121 (maximal integral lattice)"]
def IsMaximalIntQLat (O : Subalgebra (𝓞 k) (QuatF k a b)) (H : Matrix (Fin m) (Fin m) (QuatF k a b))
    (Λ : Submodule (𝓞 k) (Fin m → QuatF k a b)) : Prop :=
  IsQLattice a b O Λ ∧ IsIntegralQ a b O H Λ ∧
    ∀ Λ', IsQLattice a b O Λ' → IsIntegralQ a b O H Λ' → Λ ≤ Λ' → Λ' = Λ

/-- **The quaternionic unitary group** $G(k) = \{g\in\mathrm{GL}_D(V) : \langle gx,gy\rangle = \langle x,y\rangle\}$ (Gan–Hanke–Yu §8–9),
$g$ ranging over the $D$-linear automorphisms of $V = D^m$ (for left multiplication). -/
@[kb "ganhankeyu2001" "§8, p. 120; §9, p. 121 (G the unitary group of V)"]
def qUnitaryGroup (H : Matrix (Fin m) (Fin m) (QuatF k a b)) :
    Subgroup ((Fin m → QuatF k a b) ≃ₗ[QuatF k a b] (Fin m → QuatF k a b)) where
  carrier := {g | ∀ x y, qHerm a b H (g x) (g y) = qHerm a b H x y}
  mul_mem' {g h} hg hh x y := by
    change qHerm a b H (g (h x)) (g (h y)) = _
    rw [hg, hh]
  one_mem' x y := rfl
  inv_mem' {g} hg x y := by
    have := hg (g⁻¹ x) (g⁻¹ y)
    change qHerm a b H (g (g.symm x)) (g (g.symm y)) = _ at this
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    exact this.symm

open Classical in
/-- **The mass of the genus of maximal $A_D$-lattices** (Gan–Hanke–Yu 2001, §9, $\mathrm{Mass}(\Lambda) = \mathrm{Mass}(K)$):
$\sum 1/\#\mathrm{Stab}_{G(k)}(\Lambda')$ over the $G(k)$-orbits of maximal lattices $\Lambda'$. $G(k)$ acts on subsets of $V$
by images; an orbit counts when its representative is (the underlying set of) a maximal lattice, and the stabilizer of
that set is the stabilizer of the lattice. -/
@[kb "ganhankeyu2001" "§9, p. 121 (Mass(Λ) = Mass(K))"]
def quatMass (O : Subalgebra (𝓞 k) (QuatF k a b)) (H : Matrix (Fin m) (Fin m) (QuatF k a b)) : ℝ≥0∞ :=
  ∑' c : MulAction.orbitRel.Quotient (qUnitaryGroup a b H) (Set (Fin m → QuatF k a b)),
    if ∃ Λ, IsMaximalQLat a b O H Λ ∧ (Λ : Set (Fin m → QuatF k a b)) = c.out then
      ((Nat.card (MulAction.stabilizer (qUnitaryGroup a b H) c.out) : ℝ≥0∞))⁻¹ else 0

open Classical in
/-- **The mass of the genus of maximal integral $A_D$-lattices** (Gan–Hanke–Yu 2001, §9, $\mathrm{Mass}(\Lambda_0)$), as `quatMass`
with maximal integral lattices. -/
@[kb "ganhankeyu2001" "§9, p. 122 (Mass(Λ₀))"]
def quatIntMass (O : Subalgebra (𝓞 k) (QuatF k a b)) (H : Matrix (Fin m) (Fin m) (QuatF k a b)) : ℝ≥0∞ :=
  ∑' c : MulAction.orbitRel.Quotient (qUnitaryGroup a b H) (Set (Fin m → QuatF k a b)),
    if ∃ Λ, IsMaximalIntQLat a b O H Λ ∧ (Λ : Set (Fin m → QuatF k a b)) = c.out then
      ((Nat.card (MulAction.stabilizer (qUnitaryGroup a b H) c.out) : ℝ≥0∞))⁻¹ else 0

/-- **$D$ is ramified at the finite place $v$** ($v\in S_D$; Gan–Hanke–Yu §9): `Quat.IsRamifiedAt`, i.e. $D\otimes_kk_v$ is a division
algebra, equivalently $(a,b)_v = -1$ (`Quat.isRamifiedAt_iff`). -/
@[kb "ganhankeyu2001" "§9, p. 121 (S_D)"]
def InSD (v : HeightOneSpectrum (𝓞 k)) : Prop :=
  Quat.IsRamifiedAt (algebraMap (𝓞 k) k a) (algebraMap (𝓞 k) k b) (.finite v)

/-! ### The named inputs: Proposition 2.13 for the quaternionic unitary group -/

/-- **Gan–Hanke–Yu Proposition 2.13 for the unitary group of a totally definite quaternionic hermitian space, maximal lattices**
(a **named input**): $\mathrm{Mass}(\Lambda) = \big(2^{-md}|L(M)|\tau(G)\big)\prod_v\lambda_v$ with $\tau(G) = 1$ (9.2),
$|L(M)| = \prod_{r=1}^m|\zeta_k(1-2r)|$ (9.1), and $\lambda_v$ the volume ratio (2.12) of $\overline H{}^0_v = Sp_{2m}$ and the
reductive quotient $\overline G_v$ of the stabilizer of $\Lambda_v$: hyperspecial $Sp_{2m}$ for $v\notin S_D$ (Gan–Hanke–Yu p. 121), and
(8.5) for $v\in S_D$ (`quatGbar`).

This packages Gan–Hanke–Yu Prop. 2.13 (from Gross–Gan [GrG] and Gross [Gr]), the Bruhat–Tits identification of the stabilizers
(§8, (8.3)–(8.5), and the hyperspecial claim of §9), and $\tau(G) = 1$; the library has no Bruhat–Tits theory or Tamagawa
measures for these groups. It is *not* the conclusion of Prop. 9.3: the printed $\lambda_v$ and the set $S$ are derived
here from (2.12) (`lam_quat`, `quat_inS_iff`). Field: `mass_eq`. -/
@[kb "ganhankeyu2001" "Proposition 2.13, p. 105; (8.5), p. 120; (9.1)–(9.2), pp. 121–122"]
structure QuatProp213 (O : Subalgebra (𝓞 k) (QuatF k a b)) (H : Matrix (Fin m) (Fin m) (QuatF k a b)) : Prop where
  mass_eq : quatMass a b O H = ENNReal.ofReal (((2 : ℝ) ^ (m * Module.finrank ℚ k))⁻¹ * lMotiveOdd k m * 1 *
    ∏' v : HeightOneSpectrum (𝓞 k), lam (.Sp m) (quatGbar m (InSD a b v)) (normQ v))

/-- **Gan–Hanke–Yu Proposition 2.13 for the quaternionic unitary group, maximal integral lattices** (a **named input**): as
`QuatProp213`, with $\overline G_v = U_m$ (8.9) for $v\in S_D$ (`quatIntGbar`) and hyperspecial $Sp_{2m}$ for $v\notin S_D$
(Gan–Hanke–Yu p. 122). Field: `mass_eq`. -/
@[kb "ganhankeyu2001" "Proposition 2.13, p. 105; (8.9), p. 121; (9.1)–(9.2), pp. 121–122"]
structure QuatIntProp213 (O : Subalgebra (𝓞 k) (QuatF k a b)) (H : Matrix (Fin m) (Fin m) (QuatF k a b)) : Prop where
  mass_eq : quatIntMass a b O H = ENNReal.ofReal (((2 : ℝ) ^ (m * Module.finrank ℚ k))⁻¹ * lMotiveOdd k m * 1 *
    ∏' v : HeightOneSpectrum (𝓞 k), lam (.Sp m) (quatIntGbar m (InSD a b v)) (normQ v))

/-! ### The set $S$ -/

/-- **Proposition 9.3, the set $S$**: $\overline G_v\ne\overline H{}^0_v = Sp_{2m}$ iff $v\in S_D$. -/
@[kb "ganhankeyu2001" "Proposition 9.3, p. 122 (v ∈ S iff v ∈ S_D)"]
theorem quat_inS_iff (m : ℕ) (ram : Prop) : quatGbar m ram ≠ .Sp m ↔ ram := by
  classical
  by_cases hr : ram
  · simp only [quatGbar, hr, ite_true, iff_true]
    split_ifs <;> simp
  · simp [quatGbar, hr]

/-- **Proposition 9.4, the set $S$**: $\overline G_v\ne Sp_{2m}$ iff $v\in S_D$. -/
@[kb "ganhankeyu2001" "Proposition 9.4, p. 122 (v ∈ S iff v ∈ S_D)"]
theorem quatInt_inS_iff (m : ℕ) (ram : Prop) : quatIntGbar m ram ≠ .Sp m ↔ ram := by
  classical
  by_cases hr : ram <;> simp [quatIntGbar, hr]

/-! ### Propositions 9.3 and 9.4 -/

open Classical in
/-- **Gan–Hanke–Yu 2001, Proposition 9.3**: for $V$ a totally definite quaternionic hermitian space of rank $m$ over $D$
($D$ ramified at every real place, `hD`) and $\Lambda$ a maximal $A_D$-lattice,
$$\mathrm{Mass}(\Lambda) = \Big(\frac1{2^{md}}\,|L(M)|\Big)\prod_{v\in S_D}\lambda_v,\qquad
\lambda_v = \begin{cases}\prod_{r=1}^n(q_v^{4r-2}-1) & m = 2n,\\
\prod_{r=1}^n(q_v^{4r-2}-1)\cdot\dfrac{q_v^{4n+2}-1}{q_v+1} & m = 2n+1,\end{cases}$$
written as a product over all finite $v$ with factor $1$ off $S_D$ (`quat_inS_iff`: $S = S_D$). **Conditional** on the named
input `QuatProp213` (Gan–Hanke–Yu's own proof). -/
@[kb "ganhankeyu2001" "Proposition 9.3, p. 122"]
theorem ghy_prop93 [IsTotallyReal k] (O : Subalgebra (𝓞 k) (QuatF k a b)) (_hO : IsMaximalOrder (𝓞 k) k O)
    (_hD : ∀ w : InfinitePlace k, Quat.IsRamifiedAt (algebraMap (𝓞 k) k a) (algebraMap (𝓞 k) k b) (.infinite w))
    (H : Matrix (Fin m) (Fin m) (QuatF k a b)) (_hH : IsQHermitian a b H) (_hdef : IsTotDefQHerm a b H)
    (I : QuatProp213 a b O H) :
    quatMass a b O H = ENNReal.ofReal (((2 : ℝ) ^ (m * Module.finrank ℚ k))⁻¹ * lMotiveOdd k m *
      ∏' v : HeightOneSpectrum (𝓞 k), (if InSD a b v then lambdaProp93 m (normQ v) else 1)) := by
  rw [I.mass_eq, mul_one]
  congr 2
  congr 1
  funext v
  exact lam_quat (one_lt_normQ v) m _

open Classical in
/-- **Gan–Hanke–Yu 2001, Proposition 9.4**: for $\Lambda_0$ a maximal integral $A_D$-lattice in a totally definite quaternionic
hermitian space of rank $m$,
$$\mathrm{Mass}(\Lambda_0) = \Big(\frac1{2^{md}}\,|L(M)|\Big)\prod_{v\in S_D}\prod_{r=1}^m\big(q_v^r+(-1)^r\big),$$
written as a product over all finite $v$ with factor $1$ off $S_D$ (`quatInt_inS_iff`: $S = S_D$). **Conditional** on the
named input `QuatIntProp213`. -/
@[kb "ganhankeyu2001" "Proposition 9.4, p. 122"]
theorem ghy_prop94 [IsTotallyReal k] (O : Subalgebra (𝓞 k) (QuatF k a b)) (_hO : IsMaximalOrder (𝓞 k) k O)
    (_hD : ∀ w : InfinitePlace k, Quat.IsRamifiedAt (algebraMap (𝓞 k) k a) (algebraMap (𝓞 k) k b) (.infinite w))
    (H : Matrix (Fin m) (Fin m) (QuatF k a b)) (_hH : IsQHermitian a b H) (_hdef : IsTotDefQHerm a b H)
    (I : QuatIntProp213 a b O H) :
    quatIntMass a b O H = ENNReal.ofReal (((2 : ℝ) ^ (m * Module.finrank ℚ k))⁻¹ * lMotiveOdd k m *
      ∏' v : HeightOneSpectrum (𝓞 k), (if InSD a b v then lambdaProp94 m (normQ v) else 1)) := by
  rw [I.mass_eq, mul_one]
  congr 2
  congr 1
  funext v
  exact lam_quatInt (one_lt_normQ v) m _

end QuadFormsKB.GanHankeYu2001
