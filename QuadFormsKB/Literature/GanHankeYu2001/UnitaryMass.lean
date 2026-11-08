/-
# Gan–Hanke–Yu 2001, §4: the mass formula for unitary groups (Propositions 4.4 and 4.5)

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), §2 (Prop. 2.13), §3
(Tables 1–2), §4 ((4.1)–(4.3), Props. 4.4, 4.5), pp. 103–111.

**Setting (Gan–Hanke–Yu §4).** $k$ is a totally real number field of degree $d$, $L/k$ a totally imaginary quadratic extension with
nontrivial automorphism $x\mapsto\bar x$ and quadratic character $\chi$; $V = L^m$ with a totally definite hermitian form
$\langle x,y\rangle = \sum_{i,j}x_iH_{ij}\bar y_j$ ($H = {}^t\bar H$), $G = U(V)$. Here $L = k(\sqrt\delta)$ with $\delta$ totally negative
(`CMData`: the data $\delta$, $s = \sqrt\delta$, $\sigma$ with $\sigma(s) = -s$). A lattice $\Lambda$ ($\mathcal O_L$-submodule, finitely generated,
spanning) is *maximal* if $\langle x,x\rangle\in\mathcal O_k$ for $x\in\Lambda$ and $\Lambda$ is maximal with this property (Gan–Hanke–Yu p. 106).

**The mass.** Gan–Hanke–Yu define $\mathrm{Mass}(\Lambda) = \mathrm{Mass}(K)$ (4.1), $K$ the stabilizer of $\Lambda$ in $G(\mathbb A)$, i.e. the sum of
$1/\#\Gamma_i$ over the classes in the genus of $\Lambda$. All maximal lattices of $V$ form one genus (locally all maximal lattices
are $G(k_v)$-conjugate, Gan–Hanke–Yu §3 citing [S1]; and $\Lambda$ is maximal iff every $\Lambda_v$ is, [S1, Lemma 8.10], Gan–Hanke–Yu p. 109), so
here `hermMass` is the sum over the $G(k)$-orbits of maximal lattices of $1/\#\mathrm{Stab}_{G(k)}(\Lambda')$.

**The local data at a finite place $v$** (`localExt`): $L_v$ split ($\delta$ a square in $k_v$), unramified (`IsUnramSqrt`), or
ramified. The discriminant of $V$ is $\alpha = (-1)^{m(m-1)/2}\det H\in k$ (`discL`, `discK`; this is the normalization for which
$V_\alpha = \mathbb H^n\oplus E_\alpha$ (3.1) and $\mathbb H^{n-1}\oplus D$ (3.7) have discriminant $\alpha$), and "$\alpha\in N L_v^\times$" is the
Hilbert symbol condition $(\alpha,\delta)_v = 1$ (`IsNormAt`).

**$L(M)$** (4.2): $\prod_{r=1}^mL(1-r,\chi^r)$, read as $|L(M)|$ (as in Prop. 7.4 of Hanke 2005).
*Clarification:* the factors $\zeta_k(1-r)$, $r$ even, can be negative; check: $k = \mathbb Q$, $L = \mathbb Q(i)$, $m = 1$:
$\mathrm{Mass} = 1/4 = \frac12\cdot L(0,\chi_{-4})\cdot2\cdot\frac12$. Since Mathlib has
no analytic continuation, $|L(1-r,\chi^r)|$ is written through the functional equation: for $r$ even ($\chi^r = 1$)
$|\zeta_k(1-r)|$ (`absZetaNeg`); for $r$ odd ($\chi$ odd at every real place)
$|L(1-r,\chi)| = (|D_k|\,N\mathfrak f_\chi)^{r-1/2}\big(2(r-1)!/(2\pi)^r\big)^dL(r,\chi)$ (`absLNegL`), with $L(1,\chi)$ the limit
of the (absolutely convergent for $s>1$) Euler product as $s\to1^+$ (`lOneL`).

**What is proved.** Gan–Hanke–Yu's derivation of Props 4.4 and 4.5 from Prop. 2.13: given the general mass formula with the local types
of Tables 1–2 and $\tau(G) = 2$ (the named input `UnitaryProp213`, which is Gan–Hanke–Yu Prop. 2.13 + the Bruhat–Tits identification of
the stabilizers in §3 + Kottwitz's $\tau(G) = 2$ (4.3)), the $\lambda_v$ of (2.12) are those printed in Props 4.4/4.5
(`lam_unitary_odd`, `lam_unitary_even`), the set $S$ is as printed (`unitary_inS_odd`, `unitary_inS_even`), and the mass is as
printed (`ghy_prop44`, `ghy_prop45`).
-/
import QuadFormsKB.Literature.GanHankeYu2001.LambdaTables
import QuadFormsKB.Literature.Hanke2005.GHYMassFormulaEven

set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Real Pointwise Matrix Filter Topology
open scoped ENNReal

namespace QuadFormsKB.GanHankeYu2001

open QuadFormsKB.Hanke2005 (normQ IsUnramSqrt condExp absZetaNeg one_lt_normQ)

/-- **A totally imaginary quadratic extension $L = k(\sqrt\delta)$ of $k$** (Gan–Hanke–Yu 2001, §4, p. 109: "$L$ a totally imaginary quadratic
extension of $k$, $\chi$ the nontrivial character of the Galois group of $L$ over $k$"). Fields: `δ` ($\delta\in k$, totally
negative: `δ_neg`); `s` with `sq_s` ($s^2 = \delta$, so $L = k(s)$ by `finrank_eq`); `σ`, the nontrivial automorphism
($\sigma(s) = -s$, `σ_s`), written $x\mapsto\bar x$ in Gan–Hanke–Yu. -/
@[kb "ganhankeyu2001" "§4, p. 109 (L/k totally imaginary quadratic)"]
structure CMData (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] where
  δ : k
  s : L
  sq_s : s ^ 2 = algebraMap k L δ
  finrank_eq : Module.finrank k L = 2
  δ_neg : ∀ φ : k →+* ℝ, φ δ < 0
  σ : L ≃ₐ[k] L
  σ_s : σ s = -s

variable {k : Type} [Field k] [NumberField k] {L : Type} [Field L] [NumberField L] [Algebra k L]
variable (D : CMData k L) {m : ℕ}

/-! ### Hermitian forms and maximal lattices -/

/-- **The hermitian form** $\langle x,y\rangle = \sum_{i,j}x_iH_{ij}\bar y_j$ on $L^m$ (Gan–Hanke–Yu 2001, §3–4; linear in $x$,
conjugate-linear in $y$, as $\langle x,y\rangle = \alpha x\bar y$ in (3.1)). -/
@[kb "ganhankeyu2001" "§3, p. 105; §4, p. 109 (hermitian form)"]
def herm (H : Matrix (Fin m) (Fin m) L) (x y : Fin m → L) : L := ∑ i, ∑ j, x i * H i j * D.σ (y j)

/-- **$H$ is hermitian**: $\overline{H_{ji}} = H_{ij}$, i.e. $\langle y,x\rangle = \overline{\langle x,y\rangle}$. -/
def IsHermitianσ (H : Matrix (Fin m) (Fin m) L) : Prop := ∀ i j, D.σ (H j i) = H i j

/-- **The hermitian form is totally definite** (Gan–Hanke–Yu §4: $G(k\otimes\mathbb R)$ compact): for $x\ne0$, $\langle x,x\rangle$ is an
element $c$ of $k$ positive at every real embedding. -/
@[kb "ganhankeyu2001" "§4, p. 109 (totally definite hermitian form)"]
def IsTotDefHerm (H : Matrix (Fin m) (Fin m) L) : Prop :=
  ∀ x : Fin m → L, x ≠ 0 → ∃ c : k, algebraMap k L c = herm D H x x ∧ ∀ φ : k →+* ℝ, 0 < φ c

/-- **$\langle x,x\rangle\in A$ for all $x\in\Lambda$** ($A = \mathcal O_k$; Gan–Hanke–Yu p. 106, p. 101). -/
def IsIntegralHerm (H : Matrix (Fin m) (Fin m) L) (Λ : Submodule (𝓞 L) (Fin m → L)) : Prop :=
  ∀ x ∈ Λ, ∃ c : 𝓞 k, algebraMap k L (c : k) = herm D H x x

/-- **A maximal lattice** (Gan–Hanke–Yu 2001, p. 106 and p. 101): an $\mathcal O_L$-lattice $\Lambda$ in $L^m$ (finitely generated, spanning
$L^m$: Mathlib's `Submodule.IsLattice`) with $\langle x,x\rangle\in\mathcal O_k$ for $x\in\Lambda$, maximal with respect to this
property. -/
@[kb "ganhankeyu2001" "§3, p. 106 (maximal lattice)"]
def IsMaximalHermLat (H : Matrix (Fin m) (Fin m) L) (Λ : Submodule (𝓞 L) (Fin m → L)) : Prop :=
  Λ.IsLattice L ∧ IsIntegralHerm D H Λ ∧
    ∀ Λ' : Submodule (𝓞 L) (Fin m → L), Λ'.IsLattice L → IsIntegralHerm D H Λ' → Λ ≤ Λ' → Λ' = Λ

/-- **The unitary group** $G(k) = U(V)(k) = \{g\in GL_m(L) : \langle gx,gy\rangle = \langle x,y\rangle\}$ (Gan–Hanke–Yu §4). -/
@[kb "ganhankeyu2001" "§4, p. 109 (G the unitary group)"]
def unitaryGroup (H : Matrix (Fin m) (Fin m) L) : Subgroup (GL (Fin m) L) where
  carrier := {g | ∀ x y, herm D H (g • x) (g • y) = herm D H x y}
  mul_mem' {a b} ha hb x y := by rw [mul_smul, mul_smul, ha, hb]
  one_mem' x y := by rw [one_smul, one_smul]
  inv_mem' {a} ha x y := by
    have := ha (a⁻¹ • x) (a⁻¹ • y)
    rw [smul_inv_smul, smul_inv_smul] at this
    exact this.symm

open Classical in
/-- **The mass of the genus of maximal lattices** (Gan–Hanke–Yu 2001, (4.1)): $\sum_{[\Lambda']}1/\#\mathrm{Stab}_{G(k)}(\Lambda')$ over the
$G(k)$-orbits of maximal lattices (orbits of $G(k)$ acting on all $\mathcal O_L$-submodules of $L^m$ by $g\Lambda$, restricted to the
maximal ones). See the module docstring for why this is Gan–Hanke–Yu's $\mathrm{Mass}(\Lambda) = \mathrm{Mass}(K)$. -/
@[kb "ganhankeyu2001" "(4.1), p. 109 (Mass(Λ) = Mass(K))"]
def hermMass (H : Matrix (Fin m) (Fin m) L) : ℝ≥0∞ :=
  ∑' c : MulAction.orbitRel.Quotient (unitaryGroup D H) (Submodule (𝓞 L) (Fin m → L)),
    if IsMaximalHermLat D H c.out then ((Nat.card (MulAction.stabilizer (unitaryGroup D H) c.out) : ℝ≥0∞))⁻¹ else 0

/-! ### Local data -/

section Local

variable (v : HeightOneSpectrum (𝓞 k))

local notation "kv" => v.adicCompletion k

open Classical in
/-- **The type of $L_v = L\otimes_kk_v$** (Gan–Hanke–Yu §4, p. 109): split if $\delta$ is a square in $k_v$, unramified if
$k_v(\sqrt\delta)/k_v$ is unramified (`IsUnramSqrt`, O'Meara 63:3–63:4), ramified otherwise. -/
@[kb "ganhankeyu2001" "§4, p. 109 (v split, unramified or ramified in L)"]
def localExt : LocalExt :=
  if IsSquare (algebraMap k kv D.δ) then .split
  else if IsUnramSqrt v (algebraMap k kv D.δ) then .inert else .ram

/-- **The discriminant** $\alpha = (-1)^{m(m-1)/2}\det H$ of the hermitian space (Gan–Hanke–Yu §3: the invariant in $F^\times/NE^\times$
classifying hermitian spaces; normalized so that $V_\alpha$ of (3.1), (3.4), (3.7) has discriminant $\alpha$). -/
@[kb "ganhankeyu2001" "§3, p. 105 (discriminant of a hermitian space)"]
def discL (H : Matrix (Fin m) (Fin m) L) : L := (-1) ^ (m * (m - 1) / 2) * H.det

/-- **The discriminant as an element of $k$** (it is fixed by $\sigma$; `algebraMap_discK`). -/
def discK (H : Matrix (Fin m) (Fin m) L) : k := Classical.epsilon fun c : k => algebraMap k L c = discL H

/-- **$\alpha\in N(L_v^\times)$** (Gan–Hanke–Yu Props 4.4, 4.5: "$V\otimes_kk_v\cong V_\alpha$ with $\alpha\in NL_v^\times$"): the Hilbert symbol
$(\alpha,\delta)_v = 1$, $L_v = k_v(\sqrt\delta)$. -/
@[kb "ganhankeyu2001" "Propositions 4.4, 4.5, p. 110 (α ∈ N L_v^×)"]
def IsNormAt (H : Matrix (Fin m) (Fin m) L) : Prop :=
  hilbertSymbol kv (algebraMap k kv (discK H)) (algebraMap k kv D.δ) = 1

/-- **The quadratic character $\chi$ of $L/k$ at $v$**: $1$ split, $-1$ inert, $0$ ramified. -/
@[kb "ganhankeyu2001" "§4, p. 109 (χ)"]
def chiL : ℝ :=
  match localExt D v with
  | .split => 1
  | .inert => -1
  | .ram => 0

open Classical in
/-- The local factor $q_v^{f_v}$ of the conductor norm $N\mathfrak f_\chi$ ($f_v$ = `condExp`, the conductor exponent of
$k_v(\sqrt\delta)/k_v$, defined through the Hilbert symbol), $1$ at unramified places. -/
def condFactorL : ℝ := if localExt D v = .ram then normQ v ^ condExp v (algebraMap k kv D.δ) else 1

end Local

/-- **$N\mathfrak f_\chi = \prod_vq_v^{f_v}$**, the norm of the conductor of $\chi$. -/
def condNormL : ℝ := ∏' v : HeightOneSpectrum (𝓞 k), condFactorL D v

/-- **$L(1,\chi)$** as the limit of the Euler product $L(s,\chi)$ (absolutely convergent for $s>1$) as $s\to1^+$; by continuity
of the entire function $L(s,\chi)$ this is its value at $s = 1$. -/
@[kb "ganhankeyu2001" "(4.2), p. 109 (L(0, χ), via the functional equation)"]
def lOneL : ℝ := limUnder (𝓝[>] (1 : ℝ)) (NFEuler.LFunctionNF (chiL D))

/-- **$|L(1-r,\chi)|$ for $r$ odd** through the functional equation (χ odd at every real place):
$(|D_k|N\mathfrak f_\chi)^{r-1/2}\big(2(r-1)!/(2\pi)^r\big)^dL(r,\chi)$. -/
def absLNegL (r : ℕ) : ℝ :=
  (|(discr k : ℝ)| * condNormL D) ^ ((r : ℝ) - 1 / 2) *
    (2 * (Nat.factorial (r - 1) : ℝ) / (2 * π) ^ r) ^ Module.finrank ℚ k *
      (if r = 1 then lOneL D else NFEuler.LFunctionNF (chiL D) (r : ℝ))

/-- **Gan–Hanke–Yu's $|L(M)|$ for the unitary group** (4.2): $\prod_{r=1}^m|L(1-r,\chi^r)|$, with $\chi^r = 1$ for $r$ even
($|\zeta_k(1-r)|$ = `absZetaNeg k (r/2)`) and $\chi^r = \chi$ for $r$ odd. -/
@[kb "ganhankeyu2001" "(4.2), p. 109 (L(M) = ∏ L(1 − r, χ^r), in absolute value)"]
def lMotiveUnitary (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.range m, (if Even (r + 1) then absZetaNeg k ((r + 1) / 2) else absLNegL D (r + 1))

/-! ### The named input: Proposition 2.13 for the unitary group -/

/-- **Gan–Hanke–Yu Proposition 2.13 for the unitary group of a totally definite hermitian space** (a **named input**):
$$\mathrm{Mass}(\Lambda) = \Big(\frac1{2^{md}}\,|L(M)|\,\tau(G)\Big)\prod_v\lambda_v,\qquad \tau(G) = 2,$$
with $\lambda_v$ the volume ratio (2.12) (`lam`) of $\overline H{}^0_v$ and $\overline G_v$, the latter being the reductive quotient of the
Bruhat–Tits model of the stabilizer of a maximal lattice as listed in Tables 1–2 (`unitaryGbar`; $GL_m$ at split places).

This packages three cited results that need Bruhat–Tits theory and Tamagawa measures, which the library does not have:
Gan–Hanke–Yu Prop. 2.13 (from Gross–Gan [GrG, Prop. 10.7] and Gross [Gr]), the identification of the stabilizers (Gan–Hanke–Yu §3, Tables 1–2,
from [T, §3.11], [BT1], [BT2]), and $\tau(G) = 2$ (4.3) (Kottwitz [K], Ono [O]). It is *not* the conclusion of
Props. 4.4/4.5: those have Gan–Hanke–Yu's printed $\lambda_v$ and set $S$, which are derived from (2.12) here (`lam_unitary_odd`,
`lam_unitary_even`, `unitary_inS_odd`, `unitary_inS_even`). Field: `mass_eq`. -/
@[kb "ganhankeyu2001" "Proposition 2.13, p. 105; Tables 1–2, pp. 106–107; (4.3), p. 110"]
structure UnitaryProp213 (H : Matrix (Fin m) (Fin m) L) : Prop where
  mass_eq : hermMass D H = ENNReal.ofReal (((2 : ℝ) ^ (m * Module.finrank ℚ k))⁻¹ * lMotiveUnitary D m * 2 *
    ∏' v : HeightOneSpectrum (𝓞 k),
      lam (unitaryHbar m (localExt D v)) (unitaryGbar m (localExt D v) (IsNormAt D v H)) (normQ v))

/-! ### The set $S$ -/

/-- **Proposition 4.4, the set $S$** ($m$ odd): $\overline G_v\ne\overline H{}^0_v$ (the stabilizer model is not $\underline H{}^0_v$) iff
$L_v$ is ramified, or $L_v$ is unramified and $\alpha\notin NL_v^\times$. -/
@[kb "ganhankeyu2001" "Proposition 4.4, p. 110 (v ∈ S iff …)"]
theorem unitary_inS_odd (n : ℕ) (e : LocalExt) (isNorm : Prop) :
    unitaryGbar (2 * n + 1) e isNorm ≠ unitaryHbar (2 * n + 1) e ↔ InS44 e isNorm := by
  classical
  have hodd : ¬ Even (2 * n + 1) := Nat.not_even_iff_odd.2 ⟨n, rfl⟩
  cases e <;> by_cases hN : isNorm <;> simp [unitaryGbar, unitaryHbar, InS44, hN, hodd]

/-- **Proposition 4.5, the set $S$** ($m = 2n$ even, $n\ge1$): $\overline G_v\ne\overline H{}^0_v$ iff $v$ does not split in $L$ and
$\alpha\notin NL_v^\times$. -/
@[kb "ganhankeyu2001" "Proposition 4.5, p. 110 (v ∈ S iff …)"]
theorem unitary_inS_even {n : ℕ} (hn : 1 ≤ n) (e : LocalExt) (isNorm : Prop) :
    unitaryGbar (2 * n) e isNorm ≠ unitaryHbar (2 * n) e ↔ InS45 e isNorm := by
  classical
  have hev : Even (2 * n) := ⟨n, by ring⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  cases e <;> by_cases hN : isNorm <;>
    simp [unitaryGbar, unitaryHbar, InS45, hN, hev, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]

/-! ### Propositions 4.4 and 4.5 -/

/-- **Gan–Hanke–Yu 2001, Proposition 4.4** ($m = 2n+1$ odd): for $V$ a totally definite hermitian space over $L/k$,
$$\mathrm{Mass}(\Lambda) = \Big(\frac1{2^{md}}\,|L(M)|\,\tau(G)\Big)\prod_{v\in S}\lambda_v,\quad \tau(G) = 2,\quad
\lambda_v = \begin{cases}\frac12 & L_v\text{ ramified},\\ \frac{q_v^m+1}{q_v+1} & L_v\text{ unramified},\ \alpha\notin NL_v^\times,\end{cases}$$
written as a product over all $v$ of `lambdaProp44` ($=1$ off $S$). **Conditional** on the named input `UnitaryProp213`
(Gan–Hanke–Yu's own proof: Prop. 2.13 with the types of Table 1 and $\tau(G) = 2$; the local factors are derived from (2.12)). As in Gan–Hanke–Yu,
the discriminant of $V$ need not be a unit (Remark (i)). -/
@[kb "ganhankeyu2001" "Proposition 4.4, p. 110"]
theorem ghy_prop44 (H : Matrix (Fin m) (Fin m) L) (_hH : IsHermitianσ D H) (_hdef : IsTotDefHerm D H) {n : ℕ}
    (hm : m = 2 * n + 1) (I : UnitaryProp213 D H) :
    hermMass D H = ENNReal.ofReal (((2 : ℝ) ^ (m * Module.finrank ℚ k))⁻¹ * lMotiveUnitary D m * 2 *
      ∏' v : HeightOneSpectrum (𝓞 k), lambdaProp44 m (localExt D v) (IsNormAt D v H) (normQ v)) := by
  subst hm
  rw [I.mass_eq]
  congr 2
  congr 1
  funext v
  exact lam_unitary_odd (one_lt_normQ v) n _ _

/-- **Gan–Hanke–Yu 2001, Proposition 4.5** ($m = 2n$ even, $n\ge1$):
$$\mathrm{Mass}(\Lambda) = \Big(\frac1{2^{md}}\,|L(M)|\,\tau(G)\Big)\prod_{v\in S}\lambda_v,\quad
\lambda_v = \begin{cases}\frac{q_v^m-1}{q_v+1} & L_v\text{ unramified},\\ \frac12\cdot\frac{q_v^m-1}{q_v+1} & L_v\text{ ramified},\end{cases}$$
$v\in S$ iff $v$ does not split in $L$ and $\alpha\notin NL_v^\times$; written as a product over all $v$ of `lambdaProp45`.
**Conditional** on the named input `UnitaryProp213`. -/
@[kb "ganhankeyu2001" "Proposition 4.5, p. 110"]
theorem ghy_prop45 (H : Matrix (Fin m) (Fin m) L) (_hH : IsHermitianσ D H) (_hdef : IsTotDefHerm D H) {n : ℕ}
    (hn : 1 ≤ n) (hm : m = 2 * n) (I : UnitaryProp213 D H) :
    hermMass D H = ENNReal.ofReal (((2 : ℝ) ^ (m * Module.finrank ℚ k))⁻¹ * lMotiveUnitary D m * 2 *
      ∏' v : HeightOneSpectrum (𝓞 k), lambdaProp45 m (localExt D v) (IsNormAt D v H) (normQ v)) := by
  subst hm
  rw [I.mass_eq]
  congr 2
  congr 1
  funext v
  exact lam_unitary_even (one_lt_normQ v) hn _ _

end QuadFormsKB.GanHankeYu2001
