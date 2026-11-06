/-
# O'Meara 93:3 (unimodular overlattices on a hyperbolic space) and Example 93:11 (binary unimodular lattices of norm $2\mathfrak o$)

**Setting** (as in `Sec93Gap3.lean`): $R$ a discrete valuation ring (Henselian with finite residue field and dyadic where
stated) with fraction field $F$, $2 \in F^\times$; $(V, Q)$ a quadratic space over $F$, O'Meara's $B$ = `bil Q`, lattices
= `Submodule R V`; $\mathfrak gL$ = `normGroup Q L`. Helper lemmas live in `QuadFormsKB.OMeara.D93`.

**Proves** (O'Meara 1963, §93A–§93B, pp. 252–256)
* `IsHyperbolicSpace Q` (definition): $Q \cong \mathbb H^m$ = `QuadraticForm.hyperbolicSpace F m` (an orthogonal sum of
  hyperbolic planes), the notion of "hyperbolic space" of 93:3;
* `exists_isUnimodular_of_isHyperbolicSpace` (**93:3**): for a lattice $L$ with $\mathfrak sL = \mathfrak o$ on a hyperbolic
  space $V$ there is a unimodular lattice $K$ on $V$ with $L \subseteq K$ and $\mathfrak gK = \mathfrak gL$ (only needs $R$ a DVR,
  not Henselian/dyadic);
* `hasMatrixA_zero_zero_of_isotropic` (**93:11**, isotropic case): $L \cong A(0, 0)$;
* `hasMatrixA_two_of_anisotropic` (**93:11**, anisotropic case): $L \cong A(2, 2\rho)$ for $1 + 4\rho$ a non-square;
* `hasMatrixA_of_normIdeal_le_two` (**93:11**): $L \cong A(0,0)$ or $L \cong A(2, 2\rho)$ for a binary unimodular $L$ with
  $\mathfrak nL \subseteq 2\mathfrak o$; `hasMatrixA_of_quadDefect` is the same with the hypothesis
  $\mathfrak d(1 + 4\rho) = 4\mathfrak o$.

**Proof notes.** 93:3 follows O'Meara: a lattice $K \supseteq L$ with $\mathfrak sK \subseteq \mathfrak o$,
$\mathfrak gK \subseteq \mathfrak gL$ maximal for these (ACC in $L^\#$) has $B(x, K) = \mathfrak o$ for each maximal
isotropic $x \in K$, so $K = (\mathfrak ox + \mathfrak oy) \perp K'$ and one inducts; to avoid Witt cancellation, "$FK$
hyperbolic" is carried in the induction as "$FK$ has a totally isotropic subspace $T$ with $\dim FK \le 2 \dim T$", and
$T \cap y^\perp$ serves in $FK'$. For 93:11 the Hasse-symbol computation is replaced by Hensel's lemma plus the
Artin–Schreier map $\lambda \mapsto \lambda^2 + \lambda$ on the residue field (index $2$ in its image), see
`hasMatrixA_two_of_anisotropic`; the isotropic case is proved directly (not via 82:19, 82:22).
-/
import QuadFormsKB.Literature.OMeara.Sec93FIdeal
import QuadFormsKB.Literature.OMeara.Sec82Modular
import QuadFormsKB.Witt.Decomposition

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace D93

section Hensel

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- Hensel's lemma for a quadratic polynomial $a X^2 + b X + c$ with unit leading coefficient $a$: a root modulo
$\mathfrak p$ at which the derivative $2 a r_0 + b$ is a unit lifts to a root in $R$. -/
theorem hensel_quad {a b c r₀ : R} (ha : IsUnit a) (h0 : a * r₀ ^ 2 + b * r₀ + c ∈ maximalIdeal R)
    (hd : IsUnit (2 * a * r₀ + b)) : ∃ r : R, a * r ^ 2 + b * r + c = 0 ∧ r - r₀ ∈ maximalIdeal R := by
  open Polynomial in
  obtain ⟨a', ha'⟩ := ha.exists_right_inv
  have ha'u : IsUnit a' := isUnit_iff_exists_inv.2 ⟨a, by rw [mul_comm]; exact ha'⟩
  let f : R[X] := X ^ 2 + C (a' * b) * X + C (a' * c)
  have hf : f.Monic := by
    simp only [f]
    monicity!
  have hev : ∀ r : R, f.eval r = a' * (a * r ^ 2 + b * r + c) := by
    intro r
    simp only [f, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    linear_combination (-(r ^ 2)) * ha'
  have hder : f.derivative.eval r₀ = a' * (2 * a * r₀ + b) := by
    simp only [f, derivative_add, derivative_mul, derivative_X_pow, derivative_C, derivative_X, eval_add,
      eval_mul, eval_pow, eval_X, eval_C, eval_zero, eval_one]
    push_cast
    linear_combination (-(2 * r₀)) * ha'
  obtain ⟨r, hr, hrr⟩ := HenselianLocalRing.is_henselian f hf r₀
    (by rw [hev]; exact Ideal.mul_mem_left _ _ h0) (by rw [hder]; exact ha'u.mul hd)
  refine ⟨r, ?_, hrr⟩
  have h1 : a' * (a * r ^ 2 + b * r + c) = 0 := by rw [← hev]; exact hr
  have h2 := congrArg (fun z => a * z) h1
  simp only [mul_zero] at h2
  calc a * r ^ 2 + b * r + c = (a * a') * (a * r ^ 2 + b * r + c) := by rw [ha', one_mul]
    _ = 0 := by rw [mul_assoc]; exact h2

end Hensel

section ArtinSchreier

variable {k : Type*} [Field k] [Finite k]

/-- **Artin–Schreier in a finite field of characteristic $2$**: the additive map $x \mapsto x^2 + x$ has image of
index $2$, so if neither $a$ nor $b$ is of the form $x^2 + x$, then $a + b$ is. -/
theorem artinSchreier_add (h2 : (2 : k) = 0) {a b : k} (ha : ¬ ∃ x : k, x ^ 2 + x = a)
    (hb : ¬ ∃ x : k, x ^ 2 + x = b) : ∃ x : k, x ^ 2 + x = a + b := by
  let ℘ : k →+ k :=
    { toFun := fun x => x ^ 2 + x
      map_zero' := by simp
      map_add' := fun x y => by
        have : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by linear_combination (x * y) * h2
        simp only [this]; ring }
  have hker : (℘.ker : Set k) = {0, 1} := by
    ext x
    simp only [AddMonoidHom.coe_ker, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
    show x ^ 2 + x = 0 ↔ x = 0 ∨ x = 1
    constructor
    · intro h
      have : x * (x + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · exact Or.inr (by linear_combination h - h2)
    · rintro (rfl | rfl)
      · simp
      · linear_combination h2
  have hcard : Nat.card ℘.ker = 2 := by
    have : Nat.card ℘.ker = (℘.ker : Set k).ncard := Nat.card_coe_set_eq _
    rw [this, hker, Set.ncard_pair zero_ne_one]
  have h1 := AddSubgroup.index_ker ℘
  have h3 := AddSubgroup.card_mul_index ℘.ker
  have h4 := AddSubgroup.card_mul_index ℘.range
  rw [hcard, h1] at h3
  have hidx : ℘.range.index = 2 := by
    have hpos : 0 < Nat.card ℘.range := Nat.card_pos
    have : Nat.card ℘.range * ℘.range.index = Nat.card ℘.range * 2 := by rw [h4]; omega
    exact Nat.eq_of_mul_eq_mul_left hpos this
  obtain ⟨w, hw⟩ := AddSubgroup.index_eq_two_iff.1 hidx
  have hmem : ∀ c : k, c ∉ ℘.range → c + w ∈ ℘.range := by
    intro c hc
    rcases hw c with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hc
  have hnr : ∀ c : k, (¬ ∃ x : k, x ^ 2 + x = c) → c ∉ ℘.range := fun c hc ⟨x, hx⟩ => hc ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hmem a (hnr a ha)
  obtain ⟨y, hy⟩ := hmem b (hnr b hb)
  refine ⟨x + y, ?_⟩
  have hx' : x ^ 2 + x = a + w := hx
  have hy' : y ^ 2 + y = b + w := hy
  have : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by linear_combination (x * y) * h2
  rw [this]
  linear_combination hx' + hy' + w * h2

end ArtinSchreier

section Binary

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- Two vectors $x, y$ of a binary unimodular lattice $L$ with $Q(x) = \alpha$, $B(x, y) = 1$, $Q(y) = \beta$ and
$-1 + \alpha\beta$ a unit form a base of $L$, so $L \cong A(\alpha, \beta)$. -/
theorem hasMatrixA_of_vecs {L : Submodule R V} (hfg : L.FG) (hL : IsUnimodular Q L) (hrk : finrank R L = 2)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) {α β : R} (hQx : Q x = algebraMap R F α)
    (hQy : Q y = algebraMap R F β) (hxy : bil Q x y = 1) (hu : IsUnit (-1 + α * β)) :
    HasMatrixA Q L α β := by
  let v : Fin 2 → V := ![x, y]
  let U : Matrix (Fin 2) (Fin 2) R := !![α, 1; 1, β]
  have hUdet : IsUnit U.det := by
    have : U.det = -1 + α * β := by simp [U, Matrix.det_fin_two_of]; ring
    rw [this]; exact hu
  have hG : gram Q v = (1 : F) • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, hQx, hQy, hxy, bil_comm Q y x]
  have hspan := a10_span_eq Q hfg hL hrk (v := v) (fun i => by fin_cases i <;> simp [v, hx, hy]) hUdet hG
  have hli : LinearIndependent R v := by
    refine linearIndependent_of_det_gram_ne_zero Q ?_
    rw [hG, Matrix.det_smul, one_pow, one_mul]
    have hd : (U.map (algebraMap R F)).det = algebraMap R F U.det :=
      (RingHom.map_det (algebraMap R F) U).symm
    rw [hd]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hUdet.ne_zero
  let b : Basis (Fin 2) R L := (Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hb : ∀ i, (b i : V) = v i := fun i => by simp [b]
  refine ⟨hu, b, ?_⟩
  have : (fun i => (b i : V)) = v := funext hb
  rw [this, hG]
  ext i j; fin_cases i <;> fin_cases j <;> simp [U, matA]

end Binary

end D93

section Binary93

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

open D93

/-- **93:11, isotropic case** (O'Meara 1963, p. 255): a binary unimodular lattice $L$ with $\mathfrak nL \subseteq
2\mathfrak o$ on an isotropic vector is $L \cong A(0, 0)$. (O'Meara argues: $L$ is $2\mathfrak o$-maximal by 82:19,
so $L \cong A(0,0)$ by 82:22. Here this is proved directly, without assuming $FL = V$ or $\dim V = 2$: if $x \in L$ is
a maximal isotropic vector then $B(x, L) = \mathfrak o$ by 82:17, so there is $z \in L$ with $B(x, z) = 1$, and
$z - \tfrac12 Q(z) x \in L$ because $Q(z) \in \mathfrak nL \subseteq 2\mathfrak o$.) -/
@[kb "omeara1963" "§93B, 93:11, p. 255 (isotropic case: L ≅ A(0,0))"]
theorem hasMatrixA_zero_zero_of_isotropic {L : Submodule R V} (hfg : L.FG) (hL : IsUnimodular Q L)
    (hrk : finrank R L = 2) (hn : normIdeal Q L ≤ R ∙ (2 : F)) (hiso : ∃ v ∈ L, v ≠ 0 ∧ Q v = 0) :
    HasMatrixA Q L 0 0 := by
  obtain ⟨v, hvL, hv0, hQv⟩ := hiso
  obtain ⟨x, hxm, t, ht, hvt⟩ := exists_isMaxVec_smul (F := F) hfg hv0 (subset_span hvL)
  have hQx : Q x = 0 := by
    have h1 : Q v = t ^ 2 * Q x := by rw [hvt, Q_smul]
    rw [hQv] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero 2 ht)
  obtain ⟨z, hz, hzs⟩ := exists_bil_unit_of_isMaxVec Q hfg (α := 1)
    (by rw [← Submodule.one_eq_span]; exact hL) hxm
  rw [← Submodule.one_eq_span] at hzs
  obtain ⟨e, he, hbe⟩ := u93_unit_of_span_eq_one hzs
  obtain ⟨f, hf⟩ := he.exists_left_inv
  have hz1 : f • z ∈ L := L.smul_mem f hz
  have hxz1 : bil Q x (f • z) = 1 := by
    rw [bil_rsmul_right, hbe, ← map_mul, hf, map_one]
  obtain ⟨q, hq⟩ := mem_span_singleton.1 (hn (Q_mem_normIdeal Q hz1))
  have hz2 : f • z + (-q) • x ∈ L := L.add_mem hz1 (L.smul_mem _ hxm.1)
  refine hasMatrixA_of_vecs Q hfg hL hrk hxm.1 hz2 (by rw [hQx, map_zero]) ?_ ?_ (by simp)
  · rw [Q_add Q (f • z) ((-q) • x), Q_rsmul Q (-q) x, bil_rsmul_right Q (-q) (f • z) x,
      bil_comm Q (f • z) x, hxz1, hQx, ← hq, Algebra.smul_def, map_neg, map_zero]
    ring
  · rw [bil_add_right Q x (f • z) ((-q) • x), bil_rsmul_right Q (-q) x x, hxz1, bil_self, hQx]; simp

end Binary93

section Aniso93

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

open D93

/-- **93:11, anisotropic case** (O'Meara 1963, pp. 255–256): let $\Delta = 1 + 4\rho$ be a non-square (e.g. the unit of
quadratic defect $4\mathfrak o$ of §93, p. 251). A binary unimodular lattice $L$ with $\mathfrak nL \subseteq 2\mathfrak o$
on an anisotropic space is $L \cong A(2, 2\rho)$.

*Proof* (elementary, replacing O'Meara's Hasse symbol computation and 91:2). By 93:10, $L$ has a base $x, y$ with
$Q(x) = 2\varepsilon$ ($\varepsilon$ a unit), $B(x, y) = 1$, $Q(y) = 2\beta'$. Anisotropy of $L$ (Hensel) gives that
$\beta'$ is a unit; choose a unit $\mu$ with $\beta'\mu^2 \equiv 1 \bmod \mathfrak p$ (the residue field is perfect),
and by Hensel a root $s$ of $\varepsilon s^2 + \mu s + (\beta'\mu^2 - 1)$, so that $e = sx + \mu y$ has $Q(e) = 2$;
with $f_0$ a multiple of $x$ with $B(e, f_0) = 1$ we get $L \cong A(2, 2\beta'')$. Replacing $f_0$ by
$(1 + 2\lambda)^{-1}(f_0 + \lambda e)$ changes $\beta''$ to $\beta''$ with $\beta'' + \lambda + \lambda^2$ divided by
$(1 + 2\lambda)^2$; this equals $\rho$ iff $(1 - 4\rho)(\lambda^2 + \lambda) + (\beta'' - \rho) = 0$. Over the residue
field the additive map $\lambda \mapsto \lambda^2 + \lambda$ has index $2$ in the image (kernel $\{0, 1\}$), and neither
$\beta''$ (anisotropy of $L$) nor $\rho$ (non-squareness of $\Delta$, since $(2\lambda + 1)^2 = 1 + 4\rho$ if
$\lambda^2 + \lambda = \rho$) is in the image; so $\beta'' - \rho$ is, and Hensel's lemma lifts a root to $R$.

*Hypotheses.* $\Delta$ non-square in $F$ suffices; the book's $\rho$ unit is not needed (it follows). -/
@[kb "omeara1963" "§93B, 93:11, pp. 255–256 (anisotropic case: L ≅ A(2, 2ρ))"]
theorem hasMatrixA_two_of_anisotropic (h2p : ¬ IsUnit (2 : R)) {ρ : R}
    (hΔ : ¬ IsSquare (algebraMap R F (1 + 4 * ρ))) {L : Submodule R V} (hfg : L.FG)
    (hL : IsUnimodular Q L) (hrk : finrank R L = 2) (hn : normIdeal Q L ≤ R ∙ (2 : F))
    (hani : ∀ v ∈ L, Q v = 0 → v = 0) : HasMatrixA Q L 2 (2 * ρ) := by
  have hinj := IsFractionRing.injective R F
  have h2m : (2 : R) ∈ maximalIdeal R := (mem_maximalIdeal _).mpr h2p
  have h4m : (4 : R) ∈ maximalIdeal R := by
    rw [show (4 : R) = 2 * 2 by norm_num]; exact Ideal.mul_mem_left _ _ h2m
  have nonunit : ∀ {a : R}, a ∈ maximalIdeal R → ¬ IsUnit a := fun h hu => (mem_maximalIdeal _).mp h hu
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have hs1 : scale Q L = 1 := hL.2.1
  have h1s : (1 : F) ∈ scale Q L := by rw [hs1]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  -- a norm generator of `L`
  obtain ⟨x, hxL, hxN⟩ := exists_normIdeal_eq Q hfg
  have h2N : (2 : F) ∈ normIdeal Q L := by simpa using two_mul_mem_normIdeal Q h1s
  have hNeq : normIdeal Q L = R ∙ (2 : F) := le_antisymm hn ((span_singleton_le_iff_mem _ _).2 h2N)
  obtain ⟨ε, hε⟩ := mem_span_singleton.1 (hNeq ▸ Q_mem_normIdeal Q hxL)
  have hQx : Q x = 2 * algebraMap R F ε := by rw [← hε, Algebra.smul_def]; ring
  have hεu : IsUnit ε := by
    have h2' : (2 : F) ∈ R ∙ Q x := by rw [← hxN, hNeq]; exact mem_span_singleton_self _
    obtain ⟨s, hs⟩ := mem_span_singleton.1 h2'
    rw [Algebra.smul_def, hQx] at hs
    have hsε : s * ε = 1 := hinj (by
      rw [map_mul, map_one]; apply mul_left_cancel₀ h2F; linear_combination hs)
    exact isUnit_iff_exists_inv.2 ⟨s, by rw [mul_comm]; exact hsε⟩
  obtain ⟨β, -, -, b, hb0, hgram⟩ := exists_hasMatrixA Q h2p hfg hL hrk hxL (α := 2 * ε)
    (by rw [hQx, map_mul, map_ofNat]) ⟨Q_mem_normGroup Q hxL, hxN.symm⟩
  have hXY : bil Q x (b 1 : V) = 1 := by
    have := congrFun (congrFun hgram 0) 1
    simpa [gram, matA, hb0] using this
  obtain ⟨β', hβ'⟩ := mem_span_singleton.1 (hNeq ▸ Q_mem_normIdeal Q (b 1).2)
  have hQY : Q (b 1 : V) = 2 * algebraMap R F β' := by rw [← hβ', Algebra.smul_def]; ring
  obtain ⟨Y, hYL, hQY, hXY⟩ : ∃ Y ∈ L, Q Y = 2 * algebraMap R F β' ∧ bil Q x Y = 1 :=
    ⟨(b 1 : V), (b 1).2, hQY, hXY⟩
  -- anisotropy in coordinates
  have A1 : ∀ u v : R, ε * u ^ 2 + u * v + β' * v ^ 2 = 0 → u = 0 ∧ v = 0 := by
    intro u v huv
    have hw : u • x + v • Y ∈ L := L.add_mem (L.smul_mem u hxL) (L.smul_mem v hYL)
    have hQw : Q (u • x + v • Y) = 0 := by
      rw [Q_add, Q_rsmul, Q_rsmul, bil_rsmul_left, bil_rsmul_right, hQx, hQY, hXY]
      have : algebraMap R F (ε * u ^ 2 + u * v + β' * v ^ 2) = 0 := by rw [huv, map_zero]
      simp only [map_add, map_mul, map_pow] at this
      linear_combination 2 * this
    have h0 := hani _ hw hQw
    have e1 : bil Q (u • x + v • Y) x = 0 := by rw [h0]; simp [bil]
    have e2 : bil Q (u • x + v • Y) Y = 0 := by rw [h0]; simp [bil]
    rw [bil_add_left, bil_rsmul_left, bil_rsmul_left, bil_self, hQx, bil_comm Q Y x, hXY] at e1
    rw [bil_add_left, bil_rsmul_left, bil_rsmul_left, hXY, bil_self, hQY] at e2
    have e1' : 2 * ε * u + v = 0 := hinj (by
      simp only [map_add, map_mul, map_zero, map_ofNat]; linear_combination e1)
    have e2' : u + 2 * β' * v = 0 := hinj (by
      simp only [map_add, map_mul, map_zero, map_ofNat]; linear_combination e2)
    have hunit : IsUnit (1 - 4 * ε * β') := by
      have h4n : ¬ IsUnit (4 * ε * β') :=
        nonunit (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h4m))
      have := (u93_isUnit_sub_of_nonunit h4n isUnit_one).neg
      simpa [neg_sub] using this
    have hu0 : u = 0 := by
      have : u * (1 - 4 * ε * β') = 0 := by linear_combination e2' - 2 * β' * e1'
      exact (mul_eq_zero.1 this).resolve_right hunit.ne_zero
    refine ⟨hu0, ?_⟩
    rw [hu0] at e1'; simpa using e1'
  -- `β'` is a unit
  have hβ'u : IsUnit β' := by
    by_contra hβ'n
    obtain ⟨r, hr, -⟩ := hensel_quad (a := ε) (b := 1) (c := β') (r₀ := 0) hεu
      (by simpa using (mem_maximalIdeal _).mpr hβ'n) (by simp)
    have := (A1 r 1 (by linear_combination hr)).2
    exact one_ne_zero this
  -- a unit `μ` with `β' μ² ≡ 1`
  obtain ⟨β'', hβ''⟩ := hβ'u.exists_right_inv
  obtain ⟨μ, hμ⟩ := exists_sq_mod h2p β''
  have hμu : IsUnit μ := by
    by_contra hμn
    have h1 : μ ^ 2 ∈ maximalIdeal R := Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).mpr hμn) 2 (by norm_num)
    have h2 : β'' ∈ maximalIdeal R := by
      have := add_mem hμ h1
      simpa using this
    exact nonunit h2 (isUnit_iff_exists_inv.2 ⟨β', by rw [mul_comm]; exact hβ''⟩)
  have hμ1 : β' * μ ^ 2 - 1 ∈ maximalIdeal R := by
    have h3 : β' * μ ^ 2 - 1 = -(β' * (β'' - μ ^ 2)) := by linear_combination hβ''
    rw [h3]; exact neg_mem (Ideal.mul_mem_left _ β' hμ)
  obtain ⟨s, hs, -⟩ := hensel_quad (a := ε) (b := μ) (c := β' * μ ^ 2 - 1) (r₀ := 0) hεu
    (by simpa using hμ1) (by simpa using hμu)
  -- the vector `e` with `Q e = 2`
  set e : V := s • x + μ • Y with he
  have heL : e ∈ L := L.add_mem (L.smul_mem s hxL) (L.smul_mem μ hYL)
  have hQe : Q e = 2 := by
    rw [he, Q_add, Q_rsmul, Q_rsmul, bil_rsmul_left, bil_rsmul_right, hQx, hQY, hXY]
    have : algebraMap R F (ε * s ^ 2 + μ * s + (β' * μ ^ 2 - 1)) = 0 := by rw [hs, map_zero]
    simp only [map_add, map_mul, map_pow, map_sub, map_one] at this
    linear_combination 2 * this
  -- `B(e, x)` is a unit
  have hBex : bil Q e x = algebraMap R F (2 * ε * s + μ) := by
    rw [he, bil_add_left, bil_rsmul_left, bil_rsmul_left, bil_self, hQx, bil_comm Q Y x, hXY]
    simp only [map_add, map_mul, map_ofNat]; ring
  have hwu : IsUnit (2 * ε * s + μ) :=
    u93_isUnit_add_of_nonunit (nonunit (Ideal.mul_mem_right s _ (Ideal.mul_mem_right ε _ h2m))) hμu
  obtain ⟨w', hw'⟩ := hwu.exists_left_inv
  have hw'F : algebraMap R F w' * algebraMap R F (2 * ε * s + μ) = 1 := by rw [← map_mul, hw', map_one]
  set f0 : V := w' • x with hf0
  have hf0L : f0 ∈ L := L.smul_mem w' hxL
  have hef0 : bil Q e f0 = 1 := by rw [hf0, bil_rsmul_right, hBex, hw'F]
  set β2 : R := w' ^ 2 * ε with hβ2
  have hQf0 : Q f0 = 2 * algebraMap R F β2 := by
    rw [hf0, Q_rsmul, hQx, hβ2]; simp only [map_mul, map_pow]; ring
  have hf0e : bil Q f0 e = 1 := by rw [bil_comm]; exact hef0
  -- the residue field
  have h2z : (2 : ResidueField R) = 0 := by
    have := (residue_eq_zero_iff (2 : R)).2 h2m
    rwa [map_ofNat] at this
  have h4z : (4 : ResidueField R) = 0 := by
    have := (residue_eq_zero_iff (4 : R)).2 h4m
    rwa [map_ofNat] at this
  -- `β2` is not of the form `x² + x` modulo `𝔭`
  have P1 : ¬ ∃ xb : ResidueField R, xb ^ 2 + xb = -residue R β2 := by
    rintro ⟨xb, hxb⟩
    obtain ⟨l0, rfl⟩ := residue_surjective xb
    have h0 : 1 * l0 ^ 2 + 1 * l0 + β2 ∈ maximalIdeal R := (residue_eq_zero_iff _).1 (by
      simp only [map_add, map_mul, map_pow, map_one]; linear_combination hxb)
    obtain ⟨l, hl, -⟩ := hensel_quad (a := 1) (b := 1) (c := β2) (r₀ := l0) isUnit_one h0
      (u93_isUnit_add_of_nonunit (nonunit (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h2m))) isUnit_one)
    have hz : l • e + f0 ∈ L := L.add_mem (L.smul_mem l heL) hf0L
    have hQz : Q (l • e + f0) = 0 := by
      rw [Q_add, Q_rsmul, bil_rsmul_left, hef0, hQe, hQf0]
      have : algebraMap R F (1 * l ^ 2 + 1 * l + β2) = 0 := by rw [hl, map_zero]
      simp only [map_add, map_mul, map_pow, map_one] at this
      linear_combination 2 * this
    have h0z := hani _ hz hQz
    have hb : bil Q (l • e + f0) e = algebraMap R F (2 * l + 1) := by
      rw [bil_add_left, bil_rsmul_left, bil_self, hQe, hf0e]
      simp only [map_add, map_mul, map_ofNat, map_one]; ring
    rw [h0z] at hb
    have hu1 : IsUnit (2 * l + 1) :=
      u93_isUnit_add_of_nonunit (nonunit (Ideal.mul_mem_right _ _ h2m)) isUnit_one
    have : algebraMap R F (2 * l + 1) = 0 := by rw [← hb]; simp [bil]
    exact hu1.ne_zero (hinj (by rw [this, map_zero]))
  -- `ρ` is not of the form `x² + x` modulo `𝔭`
  have P2 : ¬ ∃ xb : ResidueField R, xb ^ 2 + xb = residue R ρ := by
    rintro ⟨xb, hxb⟩
    obtain ⟨l0, rfl⟩ := residue_surjective xb
    have h0 : 1 * l0 ^ 2 + 1 * l0 + (-ρ) ∈ maximalIdeal R := (residue_eq_zero_iff _).1 (by
      simp only [map_add, map_mul, map_pow, map_one, map_neg]; linear_combination hxb)
    obtain ⟨r, hr, -⟩ := hensel_quad (a := 1) (b := 1) (c := -ρ) (r₀ := l0) isUnit_one h0
      (u93_isUnit_add_of_nonunit (nonunit (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h2m))) isUnit_one)
    refine hΔ ⟨algebraMap R F (2 * r + 1), ?_⟩
    rw [← map_mul]; congr 1
    linear_combination (-4) * hr
  obtain ⟨xb, hxb⟩ := artinSchreier_add h2z P1 P2
  obtain ⟨l0, rfl⟩ := residue_surjective xb
  have hau : IsUnit (1 - 4 * ρ) := by
    have := (u93_isUnit_sub_of_nonunit (nonunit (Ideal.mul_mem_right ρ _ h4m)) isUnit_one).neg
    simpa [neg_sub] using this
  have h0 : (1 - 4 * ρ) * l0 ^ 2 + (1 - 4 * ρ) * l0 + (β2 - ρ) ∈ maximalIdeal R := (residue_eq_zero_iff _).1 (by
    simp only [map_add, map_mul, map_pow, map_one, map_sub, map_ofNat, h4z]
    linear_combination hxb)
  obtain ⟨l, hl, -⟩ := hensel_quad (a := 1 - 4 * ρ) (b := 1 - 4 * ρ) (c := β2 - ρ) (r₀ := l0) hau h0 (by
    have : 2 * (1 - 4 * ρ) * l0 + (1 - 4 * ρ) = (1 - 4 * ρ) * (2 * l0 + 1) := by ring
    rw [this]
    exact hau.mul (u93_isUnit_add_of_nonunit (nonunit (Ideal.mul_mem_right _ _ h2m)) isUnit_one))
  have hw1u : IsUnit (2 * l + 1) :=
    u93_isUnit_add_of_nonunit (nonunit (Ideal.mul_mem_right _ _ h2m)) isUnit_one
  obtain ⟨w1, hw1⟩ := hw1u.exists_left_inv
  have hw1F : algebraMap R F w1 * algebraMap R F (2 * l + 1) = 1 := by rw [← map_mul, hw1, map_one]
  set f1 : V := w1 • (f0 + l • e) with hf1
  have hf1L : f1 ∈ L := L.smul_mem w1 (L.add_mem hf0L (L.smul_mem l heL))
  have hef1 : bil Q e f1 = 1 := by
    rw [hf1, bil_rsmul_right Q w1 e (f0 + l • e), bil_add_right Q e f0 (l • e), bil_rsmul_right Q l e e, hef0,
      bil_self, hQe]
    simp only [map_add, map_mul, map_ofNat, map_one] at hw1F ⊢
    linear_combination hw1F
  have hkey : w1 ^ 2 * (β2 + l + l ^ 2) = ρ := by
    have h : β2 + l + l ^ 2 = ρ * (2 * l + 1) ^ 2 := by linear_combination hl
    rw [h]; linear_combination (ρ * (w1 * (2 * l + 1) + 1)) * hw1
  have hQf1 : Q f1 = algebraMap R F (2 * ρ) := by
    rw [hf1, Q_rsmul Q w1 (f0 + l • e), Q_add Q f0 (l • e), Q_rsmul Q l e, bil_rsmul_right Q l f0 e, hf0e,
      hQe, hQf0, ← hkey]
    simp only [map_add, map_mul, map_pow, map_ofNat]; ring
  refine hasMatrixA_of_vecs Q hfg hL hrk heL hf1L (by rw [hQe, map_ofNat]) hQf1 hef1 ?_
  rw [add_comm]
  exact u93_isUnit_add_of_nonunit (nonunit (Ideal.mul_mem_right (2 * ρ) _ h2m)) isUnit_one.neg

/-- **Example 93:11** (O'Meara 1963, pp. 255–256): let $L$ be a binary unimodular lattice with $\mathfrak nL \subseteq
2\mathfrak o$ over a dyadic local field. Then $L \cong A(0, 0)$ or $L \cong A(2, 2\rho)$, where $\Delta = 1 + 4\rho$ is
the fixed unit of quadratic defect $4\mathfrak o$ (§93, p. 251).

*Form of the hypothesis on $\rho$.* The statement assumes only that $1 + 4\rho$ is not a square in $F$ (this is what
the proof uses; it holds for the unit $\Delta = 1 + 4\rho$ of defect $4\mathfrak o$, see
`hasMatrixA_of_quadDefect`), and not that $\rho$ is a unit (this follows: for $\rho \in \mathfrak p$, $1 + 4\rho$ is a
square by the Local Square Theorem). The case split is: $L$ isotropic gives $A(0,0)$
(`hasMatrixA_zero_zero_of_isotropic`), $L$ anisotropic gives $A(2, 2\rho)$ (`hasMatrixA_two_of_anisotropic`). Since
$\mathfrak nL \supseteq 2\,\mathfrak sL = 2\mathfrak o$ for unimodular $L$, the hypothesis $\mathfrak nL \subseteq 2\mathfrak o$
means $\mathfrak nL = 2\mathfrak o$. -/
@[kb "omeara1963" "§93B, 93:11, pp. 255–256"]
theorem hasMatrixA_of_normIdeal_le_two (h2p : ¬ IsUnit (2 : R)) {ρ : R}
    (hΔ : ¬ IsSquare (algebraMap R F (1 + 4 * ρ))) {L : Submodule R V} (hfg : L.FG)
    (hL : IsUnimodular Q L) (hrk : finrank R L = 2) (hn : normIdeal Q L ≤ R ∙ (2 : F)) :
    HasMatrixA Q L 0 0 ∨ HasMatrixA Q L 2 (2 * ρ) := by
  by_cases hiso : ∃ v ∈ L, v ≠ 0 ∧ Q v = 0
  · exact Or.inl (hasMatrixA_zero_zero_of_isotropic Q hfg hL hrk hn hiso)
  · refine Or.inr (hasMatrixA_two_of_anisotropic Q h2p hΔ hfg hL hrk hn fun v hv hQv => ?_)
    by_contra hv0
    exact hiso ⟨v, hv, hv0, hQv⟩

/-- **Example 93:11**, with the library's form of the hypothesis on $\Delta$: $\rho \in \mathfrak o$ with the quadratic
defect of $1 + 4\rho$ equal to $4\mathfrak o$ (`quadDefect`, §63A; such $\rho$ exists by `exists_quadDefect_dyadic`).
Then $L \cong A(0,0)$ or $L \cong A(2, 2\rho)$. -/
theorem hasMatrixA_of_quadDefect (h2p : ¬ IsUnit (2 : R)) {ρ : R}
    (hd : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)}) {L : Submodule R V} (hfg : L.FG)
    (hL : IsUnimodular Q L) (hrk : finrank R L = 2) (hn : normIdeal Q L ≤ R ∙ (2 : F)) :
    HasMatrixA Q L 0 0 ∨ HasMatrixA Q L 2 (2 * ρ) := by
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have h2 : (2 : R) ≠ 0 := fun h => h2F (by
    have := congrArg (algebraMap R F) h
    rwa [map_ofNat, map_zero] at this)
  refine hasMatrixA_of_normIdeal_le_two Q h2p (fun hsq => ?_) hfg hL hrk hn
  have h0 := (isSquare_iff_quadDefect_eq_bot h2 _).1 hsq
  rw [hd, span_singleton_eq_bot] at h0
  exact h2F (mul_self_eq_zero.1 (by rw [← h0]; norm_num))

end Aniso93

/-! ### Hyperbolic spaces -/

section Hyperbolic

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-- **Hyperbolic space** (O'Meara 1963, §93A, 93:3, p. 252: "a hyperbolic space $V$"): a quadratic space which is an
orthogonal sum of hyperbolic planes, i.e. isometric to $\mathbb H^m$ = `QuadraticForm.hyperbolicSpace F m` for some
$m \ge 0$ (so $\dim V = 2m$; the zero space is hyperbolic). -/
@[kb "omeara1963" "§93A, 93:3, p. 252 (hyperbolic space V)"]
def IsHyperbolicSpace (Q : QuadraticForm F V) : Prop :=
  ∃ m : ℕ, Nonempty (Q.IsometryEquiv (QuadraticForm.hyperbolicSpace F m))

end Hyperbolic

namespace D93

section Hyp

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-- A hyperbolic space $V$ ($\dim V = 2m$) has a totally isotropic subspace $T$ of dimension $m$. -/
theorem exists_isotropic_subspace_of_hyperbolic [FiniteDimensional F V] {Q : QuadraticForm F V}
    (h : IsHyperbolicSpace Q) :
    ∃ T : Submodule F V, (∀ t ∈ T, Q t = 0) ∧ finrank F V ≤ 2 * finrank F T := by
  obtain ⟨m, ⟨e⟩⟩ := h
  let Φ : (Fin m → F) →ₗ[F] (Fin m → F × F) :=
    LinearMap.pi fun i => (LinearMap.inl F F F).comp (LinearMap.proj i)
  have hΦ : Function.Injective Φ := by
    intro a b hab
    funext i
    have := congrFun hab i
    simpa [Φ] using congrArg Prod.fst this
  refine ⟨(LinearMap.range Φ).map e.toLinearEquiv.symm.toLinearMap, ?_, ?_⟩
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    have := e.map_app' (e.toLinearEquiv.symm (Φ a))
    simp only [LinearEquiv.coe_coe]
    rw [← this]
    simp [QuadraticForm.hyperbolicSpace_apply, Φ]
  · have h1 : finrank F V = finrank F (Fin m → F × F) := e.toLinearEquiv.finrank_eq
    have h2 : finrank F ((LinearMap.range Φ).map e.toLinearEquiv.symm.toLinearMap) = m := by
      rw [LinearEquiv.finrank_map_eq (e.toLinearEquiv.symm), LinearMap.finrank_range_of_inj hΦ]
      simp
    rw [h2, h1]
    simp [Module.finrank_pi_fintype, Module.finrank_prod, mul_comm]

/-- A hyperbolic space is nondegenerate: $B(v, V) = 0$ forces $v = 0$. -/
theorem bil_eq_zero_of_hyperbolic [Invertible (2 : F)] {Q : QuadraticForm F V} (h : IsHyperbolicSpace Q)
    {v : V} (hv : ∀ w, QuadraticMap.associated Q v w = 0) : v = 0 := by
  obtain ⟨m, ⟨e⟩⟩ := h
  have hpol : ∀ w, polar Q v w = 0 := by
    intro w
    have h0 : bil Q v w = 0 := hv w
    have := Q_add Q v w
    rw [h0] at this
    simp only [polar]
    linear_combination this
  have hv0 : e v = 0 := by
    refine (QuadraticForm.nondegenerate_polarBilin_iff _).1 (QuadraticForm.nondegenerate_hyperbolicSpace F m)
      (e v) fun u => ?_
    obtain ⟨w, rfl⟩ := e.toLinearEquiv.surjective u
    have h1 := hpol w
    simp only [polar] at h1 ⊢
    have e1 : QuadraticForm.hyperbolicSpace F m (e.toLinearEquiv (v + w)) = Q (v + w) := e.map_app' (v + w)
    have e2 : QuadraticForm.hyperbolicSpace F m (e.toLinearEquiv v) = Q v := e.map_app' v
    have e3 : QuadraticForm.hyperbolicSpace F m (e.toLinearEquiv w) = Q w := e.map_app' w
    rw [map_add] at e1
    show QuadraticForm.hyperbolicSpace F m (e.toLinearEquiv v + e.toLinearEquiv w) -
      QuadraticForm.hyperbolicSpace F m (e.toLinearEquiv v) - QuadraticForm.hyperbolicSpace F m (e.toLinearEquiv w) = 0
    rw [e1, e2, e3]
    exact h1
  exact e.toLinearEquiv.injective (hv0.trans (map_zero e.toLinearEquiv).symm)

end Hyp

section Max

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- A non-empty family of submodules of $V$ contained in a finitely generated submodule $N$ has a maximal member
($R$ Noetherian). -/
theorem exists_maximal_bounded (S : Set (Submodule R V)) (hS : S.Nonempty) {N : Submodule R V}
    (hN : N.FG) (hle : ∀ I ∈ S, I ≤ N) : ∃ I₀ ∈ S, ∀ I ∈ S, I₀ ≤ I → I = I₀ := by
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  let S' : Set (Submodule R N) := {J | J.map N.subtype ∈ S}
  have hS' : S'.Nonempty := by
    obtain ⟨I, hI⟩ := hS
    refine ⟨I.comap N.subtype, ?_⟩
    show (I.comap N.subtype).map N.subtype ∈ S
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hle I hI)]
    exact hI
  obtain ⟨J₀, hJ₀, hmax⟩ :=
    (set_has_maximal_iff_noetherian (R := R) (M := N)).mpr inferInstance S' hS'
  refine ⟨J₀.map N.subtype, hJ₀, fun I hI hle' => ?_⟩
  have hmem : I.comap N.subtype ∈ S' := by
    show (I.comap N.subtype).map N.subtype ∈ S
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hle I hI)]
    exact hI
  have h1 : J₀ ≤ I.comap N.subtype := Submodule.map_le_iff_le_comap.mp hle'
  have heq : J₀ = I.comap N.subtype := by
    by_contra hne
    exact hmax _ hmem (lt_of_le_of_ne h1 hne)
  rw [heq, Submodule.map_comap_subtype, inf_eq_right.mpr (hle I hI)]

/-- **Maximality for the family of $\mathfrak{o}$-scaled lattices with norm group in $G$**: $K$ is maximal among
the finitely generated lattices $M \supseteq K$ inside $FK$ with $\mathfrak s M \subseteq \mathfrak o$ and
$\mathfrak g M \subseteq G$. -/
def MaxFor (G : AddSubgroup F) (K : Submodule R V) : Prop :=
  ∀ M : Submodule R V, M.FG → K ≤ M → (∀ m ∈ M, m ∈ span F (K : Set V)) → scale Q M ≤ 1 →
    normGroup Q M ≤ G → M = K

/-- **The key step of 93:3** (O'Meara 1963, p. 253): if $K$ is maximal (`MaxFor`), then every isotropic $z \in FK$ with
$B(z, K) \subseteq \mathfrak o$ lies in $K$. (O'Meara: $K' = \mathfrak o z + K$ has $\mathfrak sK' = \mathfrak o$ and
$\mathfrak gK' = \mathfrak gK$, so $K' = K$.) Here $G \supseteq 2\mathfrak o$ is the group $\mathfrak gL$. -/
theorem mem_of_maxFor_isotropic {G : AddSubgroup F} (hG2 : ∀ r : R, 2 * algebraMap R F r ∈ G)
    {K : Submodule R V} (hKfg : K.FG) (hKs : scale Q K ≤ 1) (hKG : normGroup Q K ≤ G)
    (hmax : MaxFor Q G K) {z : V} (hz : z ∈ span F (K : Set V)) (hQz : Q z = 0)
    (hB : ∀ k ∈ K, bil Q z k ∈ (1 : Submodule R F)) : z ∈ K := by
  set M : Submodule R V := K ⊔ R ∙ z with hM
  have hMfg : M.FG := hKfg.sup (fg_span_singleton z)
  have hmem : ∀ m ∈ M, ∃ k ∈ K, ∃ a : R, m = k + a • z := by
    intro m hm
    obtain ⟨k, hk, y, hy, rfl⟩ := mem_sup.1 hm
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hy
    exact ⟨k, hk, a, rfl⟩
  have hbilzk : ∀ k ∈ K, ∃ r : R, algebraMap R F r = bil Q z k := fun k hk => Submodule.mem_one.1 (hB k hk)
  have hbil : ∀ m ∈ M, ∀ m' ∈ M, bil Q m m' ∈ (1 : Submodule R F) := by
    intro m hm m' hm'
    obtain ⟨k, hk, a, rfl⟩ := hmem m hm
    obtain ⟨k', hk', a', rfl⟩ := hmem m' hm'
    obtain ⟨r1, h1⟩ := hbilzk k hk
    obtain ⟨r2, h2⟩ := hbilzk k' hk'
    obtain ⟨r0, h0⟩ := Submodule.mem_one.1 (hKs (bil_mem_scale Q hk hk'))
    refine Submodule.mem_one.2 ⟨r0 + a' * r1 + a * r2, ?_⟩
    have : bil Q (k + a • z) (k' + a' • z) =
        bil Q k k' + algebraMap R F a' * bil Q z k + algebraMap R F a * bil Q z k' := by
      simp only [bil_add_left, bil_add_right, bil_rsmul_left, bil_rsmul_right, bil_self, hQz]
      rw [bil_comm Q k z]; ring
    rw [this, ← h0, ← h1, ← h2]
    simp only [map_add, map_mul]
  have hMs : scale Q M ≤ 1 := by
    rw [scale, span_le]
    rintro _ ⟨m, hm, m', hm', rfl⟩
    exact hbil m hm m' hm'
  have hMG : normGroup Q M ≤ G := by
    rintro _ ⟨m, hm, c, hc, rfl⟩
    obtain ⟨k, hk, a, rfl⟩ := hmem m hm
    obtain ⟨r1, h1⟩ := hbilzk k hk
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hMs hc)
    have : Q (k + a • z) + 2 * c = Q k + 2 * algebraMap R F (a * r1 + r) := by
      rw [Q_add, Q_rsmul, bil_rsmul_right, hQz, bil_comm Q k z, ← h1, ← hr]
      simp only [map_add, map_mul]; ring
    rw [this]
    exact G.add_mem (hKG (Q_mem_normGroup Q hk)) (hG2 _)
  have hspan : ∀ m ∈ M, m ∈ span F (K : Set V) := by
    intro m hm
    obtain ⟨k, hk, a, rfl⟩ := hmem m hm
    exact add_mem (subset_span hk) ((span F (K : Set V)).smul_of_tower_mem a hz)
  have hMK : M = K := hmax M hMfg le_sup_left hspan hMs hMG
  rw [← hMK]
  exact mem_sup_right (mem_span_singleton_self z)

/-- **A maximal $K$ has $B(x, K) = \mathfrak o$ for a maximal isotropic vector $x$** (O'Meara 1963, p. 253). -/
theorem exists_unit_bil_of_maxFor {G : AddSubgroup F} (hG2 : ∀ r : R, 2 * algebraMap R F r ∈ G)
    {K : Submodule R V} (hKfg : K.FG) (hKs : scale Q K ≤ 1) (hKG : normGroup Q K ≤ G)
    (hmax : MaxFor Q G K) {x : V} (hx : IsMaxVec F K x) (hQx : Q x = 0) :
    ∃ k ∈ K, ∃ u : R, IsUnit u ∧ bil Q x k = algebraMap R F u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπF : algebraMap R F π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero
  have hz : (algebraMap R F π)⁻¹ • x ∈ span F (K : Set V) := Submodule.smul_mem _ _ (subset_span hx.1)
  have hQz : Q ((algebraMap R F π)⁻¹ • x) = 0 := by rw [Q_smul, hQx, mul_zero]
  have hB : ∀ k ∈ K, bil Q ((algebraMap R F π)⁻¹ • x) k ∈ (1 : Submodule R F) := by
    intro k hk
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hKs (bil_mem_scale Q hx.1 hk))
    have hrn : ¬ IsUnit r := fun hu => hcon k hk r hu hr.symm
    have hm : r ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hrn
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.mem_span_singleton] at hm
    obtain ⟨s, rfl⟩ := hm
    refine Submodule.mem_one.2 ⟨s, ?_⟩
    rw [bil_smul_left, ← hr, map_mul]
    field_simp
  have hzK := mem_of_maxFor_isotropic Q hG2 hKfg hKs hKG hmax hz hQz hB
  obtain ⟨r, hr⟩ := hx.2 _ hzK
  have : π * r = 1 := IsFractionRing.injective R F (by
    rw [map_mul, map_one, hr]; field_simp)
  exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨r, this⟩)

/-- **Splitting off a unimodular binary lattice** (O'Meara 1963, p. 253): if $x, y \in K$, $\mathfrak sK \subseteq
\mathfrak o$, $Q(x) = 0$ and $B(x, y) = 1$, then $\mathfrak ox + \mathfrak oy$ is a unimodular binary sublattice
which splits $K$ (82:15). -/
theorem exists_split_pair {K : Submodule R V} (hKs : scale Q K ≤ 1) {x y : V} (hx : x ∈ K) (hy : y ∈ K)
    (hQx : Q x = 0) (hxy : bil Q x y = 1) :
    ∃ J K' : Submodule R V, IsOrthSum Q K J K' ∧ IsUnimodular Q J ∧ finrank R J = 2 ∧ x ∈ J ∧ y ∈ J ∧
      ∀ j ∈ J, ∃ a b : R, j = a • x + b • y := by
  obtain ⟨q, hq⟩ := Submodule.mem_one.1 (hKs (bil_mem_scale Q hy hy))
  have hq' : Q y = algebraMap R F q := by rw [← bil_self]; exact hq.symm
  let v : Fin 2 → V := ![x, y]
  let U : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, q]
  have hU : IsUnit U.det := by simp [U, Matrix.det_fin_two_of]
  have hG : gram Q v = (1 : F) • U.map (algebraMap R F) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [v, U, gram, hQx, hq', hxy, bil_comm Q y x, bil_self]
  obtain ⟨hmod, hrk⟩ := isModular_span_of_gram Q one_ne_zero hU hG
  have hJK : span R (Set.range v) ≤ K := by
    rw [span_le]; rintro _ ⟨i, rfl⟩; fin_cases i
    · exact hx
    · exact hy
  have hsc : scale Q K ≤ R ∙ (1 : F) := by rw [← Submodule.one_eq_span]; exact hKs
  obtain ⟨K', hK'⟩ := (splits_iff_of_isModular Q hJK hmod (fg_span (Set.finite_range v))).2
    (fun a ha b hb => hsc (bil_mem_scale Q (hJK ha) hb))
  refine ⟨_, K', hK', ?_, by simpa using hrk, subset_span ⟨0, by simp [v]⟩, subset_span ⟨1, by simp [v]⟩,
    fun j hj => ?_⟩
  · show IsModular Q 1 _
    rwa [Submodule.one_eq_span]
  · obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun R).1 hj
    exact ⟨c 0, c 1, by simp [Fin.sum_univ_two, v]⟩

omit [IsFractionRing R F] [Invertible (2 : F)] in
/-- If $T$ is a subspace of finite-dimensional $V$ and $\varphi$ a linear form, then $T \cap \ker\varphi$ has
codimension at most $1$ in $T$. -/
theorem finrank_le_finrank_inf_ker_add_one [FiniteDimensional F V] (T : Submodule F V) (φ : V →ₗ[F] F) :
    finrank F T ≤ finrank F (T ⊓ LinearMap.ker φ : Submodule F V) + 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : finrank F (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq T (LinearMap.ker φ)
  have h4 : finrank F (T ⊔ LinearMap.ker φ : Submodule F V) ≤ finrank F V := Submodule.finrank_le _
  omega

variable [FiniteDimensional F V]

/-- **The induction of 93:3** (O'Meara 1963, p. 253): let $K$ be maximal (`MaxFor`) in $FK$ with $\mathfrak sK \subseteq
\mathfrak o$ and $\mathfrak gK \subseteq G$, where $G \supseteq 2\mathfrak o$, and suppose $FK$ contains a totally
isotropic subspace $T$ with $\operatorname{rank}K \le 2\dim T$ (i.e. $FK$ is hyperbolic). Then $K = 0$ or $K$ is
unimodular. (Induction on the rank: split $\mathfrak ox + \mathfrak oy$ off, $x \in T$ a maximal isotropic vector,
$B(x, y) = 1$; the complement $K'$ is maximal in $FK'$ and $T \cap y^\perp$ is totally isotropic of dimension
$\ge \dim T - 1$ in $FK'$.) -/
theorem unimodular_of_maxFor {G : AddSubgroup F} (hG2 : ∀ r : R, 2 * algebraMap R F r ∈ G) :
    ∀ (n : ℕ) (K : Submodule R V), finrank R K = n → K.FG → scale Q K ≤ 1 → normGroup Q K ≤ G →
      MaxFor Q G K → (∃ T : Submodule F V, (∀ t ∈ T, Q t = 0) ∧ (∀ t ∈ T, t ∈ span F (K : Set V)) ∧
        n ≤ 2 * finrank F T) → K = ⊥ ∨ IsUnimodular Q K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hrk hKfg hKs hKG hmax ⟨T, hTiso, hTK, hTdim⟩
  by_cases hK0 : K = ⊥
  · exact Or.inl hK0
  right
  have hn1 : 1 ≤ n := hrk ▸ one_le_finrank_of_ne_bot (F := F) hK0
  have hT0 : T ≠ ⊥ := by
    rintro rfl
    simp at hTdim; omega
  obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
  obtain ⟨x, hxm, c, hc0, hxt⟩ := exists_isMaxVec_smul hKfg ht0 (hTK t htT)
  have hxT : x ∈ T := by
    have : x = c⁻¹ • t := by rw [hxt, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]; exact T.smul_mem _ htT
  have hQx : Q x = 0 := hTiso x hxT
  obtain ⟨k, hk, u, hu, hxk⟩ := exists_unit_bil_of_maxFor Q hG2 hKfg hKs hKG hmax hxm hQx
  obtain ⟨u', hu'⟩ := hu.exists_left_inv
  have hyK : u' • k ∈ K := K.smul_mem u' hk
  have hxy : bil Q x (u' • k) = 1 := by rw [bil_rsmul_right, hxk, ← map_mul, hu', map_one]
  obtain ⟨J, K', hsplit, hJ, hJrk, hxJ, hyJ, hJspan⟩ := exists_split_pair Q hKs hxm.1 hyK hQx hxy
  set y := u' • k with hy
  have hJle : J ≤ K := hsplit.sup_eq ▸ le_sup_left
  have hK'le : K' ≤ K := hsplit.sup_eq ▸ le_sup_right
  have hJfg : J.FG := FG.of_le hKfg hJle
  have hK'fg : K'.FG := FG.of_le hKfg hK'le
  have hrank : n = 2 + finrank R K' := by rw [← hrk, isOrthSum_finrank Q hsplit hKfg, hJrk]
  have hreg : IsRegular Q J := IsModular.isRegular Q hJ hJfg
  have hJ0 : J ≠ ⊥ := by
    rintro rfl; simp at hJrk
  have horthspan : ∀ j ∈ J, ∀ w ∈ span F (K' : Set V), bil Q j w = 0 := fun j hj w hw =>
    bil_zero_of_mem_span_F Q (fun z hz => hsplit.orth j hj z hz) hw
  -- maximality of `K'`
  have hmax' : MaxFor Q G K' := by
    intro M' hM'fg hK'M' hM'span hM's hM'G
    have horth : ∀ a ∈ J, ∀ b ∈ M', bil Q a b = 0 := fun a ha b hb => horthspan a ha b (hM'span b hb)
    have hM : J ⊔ M' = K := by
      apply hmax (J ⊔ M') (hJfg.sup hM'fg)
      · rw [← hsplit.sup_eq]; exact sup_le_sup_left hK'M' J
      · intro m hm
        obtain ⟨j, hj, m', hm', rfl⟩ := mem_sup.1 hm
        exact add_mem (subset_span (hJle hj))
          (span_mono (SetLike.coe_subset_coe.2 hK'le) (hM'span m' hm'))
      · rw [scale_sup_of_orth Q horth]; exact sup_le ((scale_mono Q hJle).trans hKs) hM's
      · rw [normGroup_sup_of_orth Q horth]; exact sup_le ((normGroup_mono Q hJle).trans hKG) hM'G
    apply le_antisymm _ hK'M'
    intro m' hm'
    have : m' ∈ J ⊔ K' := by rw [hsplit.sup_eq, ← hM]; exact mem_sup_right hm'
    obtain ⟨j, hj, k', hk', hjk⟩ := mem_sup.1 this
    have hj0 : j = 0 := by
      refine hreg j hj fun j'' hj'' => ?_
      have hjspan : j ∈ span F (K' : Set V) := by
        have : j = m' - k' := by rw [eq_sub_iff_add_eq]; exact hjk
        rw [this]; exact sub_mem (hM'span m' hm') (subset_span hk')
      rw [bil_comm]; exact horthspan j'' hj'' j hjspan
    rw [hj0, zero_add] at hjk
    rw [← hjk]; exact hk'
  -- the totally isotropic subspace of `FK'`
  set φ : V →ₗ[F] F := QuadraticMap.associated Q y with hφ
  have hxT_orth : ∀ t ∈ T, bil Q x t = 0 := by
    intro t ht
    have h1 := Q_add Q x t
    rw [hTiso _ (T.add_mem hxT ht), hQx, hTiso t ht] at h1
    have h2F : (2 : F) ≠ 0 := two_ne_zero
    have : 2 * bil Q x t = 0 := by linear_combination (-1 : F) * h1
    exact (mul_eq_zero.1 this).resolve_left h2F
  have hT'span : ∀ t ∈ T ⊓ LinearMap.ker φ, t ∈ span F (K' : Set V) := by
    intro t ht
    obtain ⟨d, hd0, hd⟩ := exists_smul_mem_of_mem_span (F := F) (S := K) (hTK t ht.1)
    obtain ⟨j, hj, k', hk', hjk⟩ := mem_sup.1 (hsplit.sup_eq ▸ hd : d • t ∈ J ⊔ K')
    have hj_eq : j = d • t - k' := eq_sub_of_add_eq hjk
    have hjx : bil Q j x = 0 := by
      rw [hj_eq, bil_sub_left, bil_rsmul_left, bil_comm Q t x, hxT_orth t ht.1, mul_zero,
        bil_comm Q k' x, hsplit.orth x hxJ k' hk', sub_zero]
    have hjy : bil Q j y = 0 := by
      have hty : bil Q t y = 0 := by
        rw [bil_comm]; exact LinearMap.mem_ker.1 ht.2
      rw [hj_eq, bil_sub_left, bil_rsmul_left, hty, mul_zero, bil_comm Q k' y,
        hsplit.orth y hyJ k' hk', sub_zero]
    have hj0 : j = 0 := by
      refine hreg j hj fun j'' hj'' => ?_
      obtain ⟨a, b, rfl⟩ := hJspan j'' hj''
      rw [bil_add_right, bil_rsmul_right, bil_rsmul_right, hjx, hjy]; simp
    rw [hj0, zero_add] at hjk
    have hdF : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hd0
    have : t = (algebraMap R F d)⁻¹ • k' := by
      rw [hjk, ← algebraMap_smul F d t, smul_smul, inv_mul_cancel₀ hdF, one_smul]
    rw [this]
    exact (span F (K' : Set V)).smul_mem _ (subset_span hk')
  have hdim : finrank R K' ≤ 2 * finrank F (T ⊓ LinearMap.ker φ : Submodule F V) := by
    have := finrank_le_finrank_inf_ker_add_one T φ
    omega
  have hK'rk : finrank R K' < n := by omega
  by_cases hK'0 : K' = ⊥
  · have : K = J := by rw [← hsplit.sup_eq, hK'0, sup_bot_eq]
    rw [this]; exact hJ
  · rcases ih (finrank R K') hK'rk K' rfl hK'fg ((scale_mono Q hK'le).trans hKs)
      ((normGroup_mono Q hK'le).trans hKG) hmax'
      ⟨T ⊓ LinearMap.ker φ, fun t ht => hTiso t ht.1, hT'span, hdim⟩ with h | h
    · exact absurd h hK'0
    · exact (Dedekind.isModular_iff_of_isOrthSum Q hsplit hJfg hK'fg hJ0 hK'0).2 ⟨hJ, h⟩

end Max

end D93

section Main3

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open D93

/-- **Proposition 93:3** (O'Meara 1963, pp. 252–253): let $L$ be a lattice of scale $\mathfrak o$ on a hyperbolic space
$V$ over a local field. Then there is a unimodular lattice $K$ on $V$ with $L \subseteq K$ and $\mathfrak gK = \mathfrak gL$.

*Proof* (O'Meara's). Lattices $K \supseteq L$ with $\mathfrak sK \subseteq \mathfrak o$ lie in the f.g. module $L^\#$, so
(ACC) there is one, $K$, which is maximal with $\mathfrak gK \subseteq \mathfrak gL$ (hence $\mathfrak gK = \mathfrak gL$ and
$\mathfrak sK = \mathfrak o$). An isotropic $z \in V$ with $B(z, K) \subseteq \mathfrak o$ lies in $K$ (`mem_of_maxFor_isotropic`),
so every maximal isotropic vector $x$ of $K$ has $B(x, K) = \mathfrak o$ (`exists_unit_bil_of_maxFor`), $K =
(\mathfrak ox + \mathfrak oy) \perp K'$ with $\mathfrak ox + \mathfrak oy$ unimodular, $K'$ is again maximal in $FK'$, and
$FK'$ is again hyperbolic. This is `D93.unimodular_of_maxFor`, an induction on the rank in which "hyperbolic" is
carried as: $FK$ contains a totally isotropic subspace $T$ with $\dim FK \le 2\dim T$ (for a hyperbolic space, $T$ is
the span of the first coordinates; the complement's $T \cap y^\perp$ replaces Witt's theorem).

*Hypotheses.* Only that $R$ is a discrete valuation ring with fraction field $F$, $2 \in F^\times$ and $V$ is
finite-dimensional: the Henselian property, the finite residue field and the dyadic hypothesis of §93 are not needed.
"Hyperbolic space" is `IsHyperbolicSpace` (isometric to `QuadraticForm.hyperbolicSpace F m`). -/
@[kb "omeara1963" "§93A, 93:3, pp. 252–253"]
theorem exists_isUnimodular_of_isHyperbolicSpace (hH : IsHyperbolicSpace Q) {L : Submodule R V}
    (hL : L.IsLattice F) (hs : scale Q L = 1) :
    ∃ K : Submodule R V, K.IsLattice F ∧ L ≤ K ∧ IsUnimodular Q K ∧ normGroup Q K = normGroup Q L := by
  have hLreg : IsRegular Q L := by
    intro x hx hx0
    refine bil_eq_zero_of_hyperbolic hH fun w => ?_
    exact bil_zero_of_mem_span_F Q hx0 (by rw [hL.span_eq_top]; trivial)
  set G := normGroup Q L with hG
  have hG2 : ∀ r : R, 2 * algebraMap R F r ∈ G := fun r =>
    two_mul_mem_normGroup Q (by rw [hs]; exact Submodule.mem_one.2 ⟨r, rfl⟩)
  have hDfg : (dual Q L).FG := dual_fg Q hL.fg hLreg
  let S : Set (Submodule R V) := {M | L ≤ M ∧ scale Q M ≤ 1 ∧ normGroup Q M ≤ G}
  have hLS : L ∈ S := ⟨le_rfl, hs.le, le_rfl⟩
  have hle : ∀ M ∈ S, M ≤ dual Q L := by
    intro M hM m hm
    exact ⟨by rw [hL.span_eq_top]; trivial, fun y hy => hM.2.1 (bil_mem_scale Q hm (hM.1 hy))⟩
  obtain ⟨K, hKS, hKmax⟩ := exists_maximal_bounded S ⟨L, hLS⟩ hDfg hle
  have hKfg : K.FG := FG.of_le hDfg (hle K hKS)
  have hKlat : K.IsLattice F := ⟨hKfg, eq_top_iff.2 (by
    rw [← hL.span_eq_top]; exact span_mono (SetLike.coe_subset_coe.2 hKS.1))⟩
  have hmax : MaxFor Q G K := fun M _ hKM _ hMs hMG => hKmax M ⟨hKS.1.trans hKM, hMs, hMG⟩ hKM
  obtain ⟨T, hTiso, hTdim⟩ := exists_isotropic_subspace_of_hyperbolic hH
  have hrk : finrank R K = finrank F V := by
    rw [finrank_eq_finrank_span (F := F) K, hKlat.span_eq_top, finrank_top]
  rcases unimodular_of_maxFor Q hG2 (finrank R K) K rfl hKfg hKS.2.1 hKS.2.2 hmax
    ⟨T, hTiso, fun t _ => by rw [hKlat.span_eq_top]; trivial, by rw [hrk]; exact hTdim⟩ with h | h
  · exfalso
    have h1 : (1 : F) ∈ scale Q K := scale_mono Q hKS.1 (by
      rw [hs]; exact Submodule.mem_one.2 ⟨1, map_one _⟩)
    rw [h, scale_bot] at h1
    exact one_ne_zero ((Submodule.mem_bot R).1 h1)
  · exact ⟨K, hKlat, hKS.1, h, le_antisymm hKS.2.2 (normGroup_mono Q hKS.1)⟩

end Main3

end QuadFormsKB.OMeara
